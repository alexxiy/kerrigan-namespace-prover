use sp1_sdk::{include_elf, Elf, ProverClient, SP1Stdin, Prover, ProveRequest, HashableKey, ProvingKey};
use sp1_sdk::env::EnvProver;
use serde::Serialize;
use std::fs;
use std::path::{Path, PathBuf};
use clap::Parser;
use anyhow::{bail, Context, Result};
use alloy_sol_types::{sol, SolType};
use tracing::{info, warn, error};
use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt};

// The batch wire format lives in `kns-core` so the host and the guest cannot drift
// apart. It used to be duplicated here under a "MUST MATCH GUEST EXACTLY" comment.
use kns_core::BatchPayload;

// ABI structure for decoding SP1 outputs
sol! {
    struct BatchResultABI {
        bytes32 old_root;
        bytes32 new_root;
        uint32 end_block_height;
    }
}

/// Byte length of an ABI-encoded `BatchResultABI`: three static 32-byte head words
/// (`bytes32`, `bytes32`, `uint32`).
const EXPECTED_PUBLIC_VALUES_LEN: usize = 96;

// Used to generate the {batch_id}_result.json file
#[derive(Serialize)]
pub struct FinalResultJson {
    pub old_root: String,
    pub new_root: String,
    pub end_block_height: u32,
}

// 1. Define the CLI Arguments
#[derive(Parser, Debug)]
#[command(author, version, about = "SP1 Prover Script for KNS")]
struct Args {
    #[arg(long)]
    batch_dir: String,

    #[arg(long)]
    batch_id: String,

    /// Execute the guest program in the zkVM and report its cycle count without
    /// generating a proof. Writes no output files. Use this to validate a batch
    /// cheaply before paying for proving.
    #[arg(long)]
    execute: bool,

    /// Permit the `mock` and `light` prover modes, which cannot produce an
    /// on-chain-verifiable proof. Even with this flag, `{batch_id}_result.json` is
    /// withheld so the sequencer never submits an unusable proof.
    #[arg(long)]
    allow_mock: bool,
}

/// Exit codes:
/// * `0` — success.
/// * `1` — run failed; `{batch_id}_error.txt` contains the reason.
/// * `2` — bad invocation; no error file is written because `--batch-dir` /
///   `--batch-id` are themselves what failed to parse. Details go to stderr.
#[tokio::main]
async fn main() {
    // 1. Parse arguments before anything else.
    //
    // This cannot write an error file: the destination is derived from the very
    // arguments that failed to parse. Use the distinct exit code 2 so the calling
    // backend can tell "you invoked me wrong" (stderr only) apart from "the batch
    // failed" (exit 1, error file written).
    let args = match Args::try_parse() {
        Ok(args) => args,
        Err(e) => {
            use clap::error::ErrorKind;
            let code = match e.kind() {
                ErrorKind::DisplayHelp
                | ErrorKind::DisplayVersion
                | ErrorKind::DisplayHelpOnMissingArgumentOrSubcommand => 0,
                _ => 2,
            };
            // Routes help/version to stdout and real errors to stderr.
            let _ = e.print();
            std::process::exit(code);
        }
    };

    let batch_dir = PathBuf::from(&args.batch_dir);

    let error_file_path = batch_dir.join(format!("{}_error.txt", args.batch_id));

    // 2. Clear any existing error file from a previous failed run
    if error_file_path.exists() {
        let _ = fs::remove_file(&error_file_path);
    }

    // 3. Configure robust logging (Writes to both Console AND debug.log)
    let log_filename = format!("{}_debug.log", args.batch_id);
    let log_file_path = batch_dir.join(&log_filename);

    // The appender opens in append mode, so a rerun of the same batch id would stack
    // onto the previous attempt's log. Truncate first: it keeps the log bounded, and
    // it means `scrape_guest_assertion` can only ever see the current run.
    if log_file_path.exists() {
        let _ = fs::remove_file(&log_file_path);
    }

    let file_appender = tracing_appender::rolling::never(&batch_dir, &log_filename);

    tracing_subscriber::registry()
        .with(fmt::layer().with_writer(file_appender).with_ansi(false)) // No colors in log file
        .with(fmt::layer().with_writer(std::io::stdout))                // Standard console output
        .init();

    // 4. Run the prover inside a safe Result block
    if let Err(e) = run_prover(&args, &batch_dir).await {
        // If an error bubbles up, log it and write the error.txt file
        let mut error_msg = format!("CRITICAL ERROR:\n{:#}\n", e);

        // Append the guest's own assertion text when the failure came from inside the
        // zkVM, so the error file names the offending transaction rather than just
        // reporting an empty public-values buffer.
        if let Some(guest_msg) = scrape_guest_assertion(&log_file_path) {
            error_msg.push_str(&format!("\nGUEST ASSERTION:\n{}\n", guest_msg));
        }

        error!("{}", error_msg);

        if let Err(write_err) = fs::write(&error_file_path, &error_msg) {
            eprintln!("Failed to write error.txt file: {}", write_err);
        }

        std::process::exit(1); // Exit with a failure code for your PHP backend to detect
    }

    info!("Proving process completed successfully for Batch {}", args.batch_id);
}

/// Recovers the guest program's own `CRITICAL:` assertion text from the run log.
///
/// The zkVM executor runs the guest in a child process and forwards its stderr as
/// DEBUG-level tracing events, so the assertion message reaches the log file but is
/// never handed back to us as a value. Scraping it here is what lets
/// `{batch_id}_error.txt` name the offending transaction. Returns `None` if nothing
/// matched, in which case the caller keeps its own generic message.
fn scrape_guest_assertion(log_file_path: &PathBuf) -> Option<String> {
    let log = fs::read_to_string(log_file_path).ok()?;

    let mut found: Vec<&str> = Vec::new();
    for line in log.lines() {
        if let Some(idx) = line.find("CRITICAL: ") {
            let msg = line[idx..].trim_end();
            // The executor echoes guest stderr more than once; keep it to one copy.
            if !found.contains(&msg) {
                found.push(msg);
            }
        }
    }

    if found.is_empty() {
        None
    } else {
        Some(found.join("\n"))
    }
}

/// Decodes the guest's committed public values into [`BatchResultABI`].
///
/// The length is checked first because a guest that aborts on a failed assertion
/// commits nothing at all. Handing an empty buffer straight to `abi_decode` yields
/// only "buffer overrun while deserializing", which hides the real cause — the
/// guest's own CRITICAL message.
fn decode_batch_result(bytes: &[u8]) -> Result<BatchResultABI> {
    if bytes.len() != EXPECTED_PUBLIC_VALUES_LEN {
        bail!(
            "Expected {} bytes of public values but got {}. A length of 0 means the \
             guest program aborted before committing its result — look for the \
             'CRITICAL:' assertion message earlier in this log to find the offending \
             transaction.",
            EXPECTED_PUBLIC_VALUES_LEN,
            bytes.len()
        );
    }

    BatchResultABI::abi_decode(bytes).context("Failed to decode ABI from public values")
}

// The core logic, but now using `?` operators to safely bubble errors up
async fn run_prover(args: &Args, batch_dir: &Path) -> Result<()> {
    // Dynamically build all necessary file paths
    let input_json_path = batch_dir.join(format!("{}_batch.json", args.batch_id));
    let proof_bin_path = batch_dir.join(format!("{}_proof.bin", args.batch_id));
    let public_values_path = batch_dir.join(format!("{}_public_values.bin", args.batch_id));
    let result_json_path = batch_dir.join(format!("{}_result.json", args.batch_id));

    info!("Starting prover for Batch ID: {}", args.batch_id);

    // Read and parse input
    info!("Loading payload from: {}", input_json_path.display());
    let json_data = fs::read_to_string(&input_json_path)
        .with_context(|| format!("Missing input file: {}", input_json_path.display()))?;

    let payload: BatchPayload = serde_json::from_str(&json_data)
        .context("Failed to parse JSON into BatchPayload structure")?;

    info!("Batch contains {} transaction(s)", payload.transactions.len());

    let mut stdin = SP1Stdin::new();
    stdin.write(&payload);

    // Initialize SP1
    info!("Initializing SP1 Prover Client");
    let client = ProverClient::from_env().await;
    let elf: Elf = include_elf!("kns-program");

    // Mirrors sp1-sdk's own default when SP1_PROVER is unset.
    let prover_mode = std::env::var("SP1_PROVER").unwrap_or_else(|_| "cpu".to_string());
    info!("Prover mode: {}", prover_mode);

    // The mock and light provers return Ok from `prove()` without producing a proof
    // the on-chain SP1 verifier would accept. Without this guard the script happily
    // writes result.json, the sequencer submits it, and the transaction reverts
    // after paying gas.
    let unprovable_mode = matches!(client, EnvProver::Mock(_) | EnvProver::Light(_));
    if unprovable_mode && !args.allow_mock {
        bail!(
            "Prover mode '{}' cannot produce an on-chain-verifiable proof. Set \
             SP1_PROVER to 'cpu', 'cuda' or 'network', or pass --allow-mock to \
             override for local testing.",
            prover_mode
        );
    }

    // PREFLIGHT: execute the guest without proving.
    //
    // Two reasons this runs first. It surfaces a failed guest assertion as an actual
    // Err carrying the guest's own CRITICAL message, instead of letting a prover
    // report success over an aborted run. And it reports the cycle count, which is
    // what proving time and cost scale with.
    info!("Preflight: executing guest program (no proof generated)...");
    let (exec_public_values, report) = client
        .execute(elf.clone(), stdin.clone())
        .await
        .context(
            "Guest program execution failed. The guest's 'CRITICAL:' assertion message \
             above names the offending transaction",
        )?;

    // NOTE: `execute()` returns Ok even when the guest ABORTS on a failed assertion —
    // it yields an empty public-values buffer alongside a perfectly normal cycle
    // count. The length check inside `decode_batch_result` is therefore the
    // authoritative success gate here, not the `?` above. Do not log success before
    // it has run.
    let preflight = decode_batch_result(exec_public_values.as_slice())
        .context("Preflight execution failed")?;

    let cycles = report.total_instruction_count();
    let tx_count = payload.transactions.len().max(1) as u64;
    info!(
        "Preflight OK — {} cycles for {} tx ({} cycles/tx)",
        cycles,
        payload.transactions.len(),
        cycles / tx_count
    );

    info!("Preflight Old Root: 0x{}", hex::encode(preflight.old_root));
    info!("Preflight New Root: 0x{}", hex::encode(preflight.new_root));

    if args.execute {
        info!("--execute specified: skipping proof generation, no output files written.");
        return Ok(());
    }

    info!("Setting up keys...");
    let pk = client.setup(elf).await.context("Failed to setup proving keys")?;

    info!("Program Verification Key (vkey): {}", pk.verifying_key().bytes32());

    info!("Generating SNARK Proof (This will take a while)...");
    let proof = client.prove(&pk, stdin).groth16().await.context("Prover execution failed!")?;

    // Decode public values
    info!("Proof generated successfully. Decoding ABI...");
    let result_bytes = proof.public_values.as_slice();

    let result_abi = decode_batch_result(result_bytes)?;

    // Verify locally before writing anything the sequencer might submit on-chain.
    info!("Verifying proof locally...");
    client
        .verify(&proof, pk.verifying_key(), None)
        .context("Locally generated proof FAILED verification — refusing to write outputs")?;
    info!("Proof verified locally.");

    info!("Batch Ended at Block: {}", result_abi.end_block_height);
    info!("Old Root: 0x{}", hex::encode(result_abi.old_root));
    info!("New Root: 0x{}", hex::encode(result_abi.new_root));

    // Save outputs
    info!("Saving proof components to disk...");
    fs::write(&proof_bin_path, proof.bytes()).context("Failed to write proof.bin")?;
    fs::write(&public_values_path, result_bytes).context("Failed to write public_values.bin")?;

    // Create the final structured JSON result for your PHP/Sequencer script
    let final_result = FinalResultJson {
        old_root: format!("0x{}", hex::encode(result_abi.old_root)),
        new_root: format!("0x{}", hex::encode(result_abi.new_root)),
        end_block_height: result_abi.end_block_height,
    };

    let final_result_json = serde_json::to_string_pretty(&final_result)
        .context("Failed to serialize final result to JSON")?;

    // result.json is the sequencer's "ready to submit" signal, so it is withheld for
    // prover modes whose output would revert on-chain.
    if unprovable_mode {
        warn!(
            "Prover mode '{}' produced a non-verifiable proof. Wrote proof artifacts \
             for inspection but WITHHOLDING {} so the sequencer will not submit it.",
            prover_mode,
            result_json_path.display()
        );
    } else {
        fs::write(&result_json_path, final_result_json).context("Failed to write result.json")?;
    }

    Ok(())
}

//! Builds a batch containing a second LST on an already-listed domain, to establish
//! whether the circuit accepts it.
//!
//! The registrar's PHP validation has no rule against re-listing: `parseCommand` blocks
//! UPD/CHG on a listed domain and ULT/BUY on an unlisted one, but nothing stops a second
//! LST. `batchProcessor` then sets `old_price` from the domain's current price, so the
//! batch carries `old_price > 0` for an LST. This produces exactly that batch so the
//! consequence can be observed instead of argued about.
//!
//! ```bash
//! cargo run --release --bin gen_relist_probe -- --batch-dir /tmp/probe --batch-id 9
//! cargo run --release --bin kns-script -- --batch-dir /tmp/probe --batch-id 9 --execute
//! ```

use std::fs;

use anyhow::{Context, Result};
use clap::Parser;
use ed25519_dalek::{Signer, SigningKey};

use kns_core::tree::ReferenceTree;
use kns_core::{signing_message, BatchPayload, LeafRecord, Op, Transaction};

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

#[derive(Parser, Debug)]
struct Args {
    #[arg(long)]
    batch_dir: String,
    #[arg(long, default_value = "9")]
    batch_id: String,
}

fn key(seed: u8) -> SigningKey {
    SigningKey::from_bytes(&[seed; 32])
}

fn unified_address(seed: u8) -> Result<String> {
    let mut payload = [0u8; kns_core::SAPLING_PAYLOAD_LEN];
    for (i, b) in payload.iter_mut().enumerate() {
        *b = seed.wrapping_mul(31).wrapping_add(i as u8);
    }
    let data = bech32::ToBase32::to_base32(&payload);
    let addr = bech32::encode(kns_core::EXPECTED_HRP, data, bech32::Variant::Bech32m)
        .context("failed to bech32m-encode the Sapling payload")?;
    anyhow::ensure!(kns_core::is_address_valid(&addr), "generated address is not accepted");
    Ok(addr)
}

fn main() -> Result<()> {
    let args = Args::parse();
    let owner = key(0x41);
    let pk: [u8; 32] = owner.verifying_key().to_bytes();
    let addr = unified_address(0x41)?;
    let domain = "relist.krgn";

    let mut tree = ReferenceTree::new();
    let old_root = tree.root();
    let mut txs = Vec::new();

    let step = |tree: &mut ReferenceTree,
                    op: Op,
                    price: u64,
                    old_price: u64,
                    nonce: u64,
                    old_nonce: u64,
                    txs: &mut Vec<Transaction>|
     -> Result<()> {
        let proof = tree.proof(domain);
        let msg = signing_message(op, domain, &addr, &pk, price, nonce);
        let sig = owner.sign(&msg).to_bytes().to_vec();
        txs.push(Transaction {
            tx_id: format!("probe-{}", txs.len()),
            op: String::from_utf8(op.as_bytes().to_vec()).unwrap(),
            domain_name: domain.to_string(),
            old_target_address: addr.clone(),
            target_address: addr.clone(),
            old_pubkey: if op == Op::Reg { [0u8; 32] } else { pk },
            pubkey: pk,
            price,
            old_price,
            nonce,
            old_nonce,
            signature: sig,
            proof,
        });
        tree.insert(
            LeafRecord {
                domain: domain.to_string(),
                pubkey: pk,
                target_address: addr.clone(),
                price,
                nonce,
            },
        );
        Ok(())
    };

    // REG -> LST(100) -> LST(200). The third step is the one under test: it carries
    // old_price = 100, which the circuit's `Op::Lst` arm asserts must be 0.
    step(&mut tree, Op::Reg, 0, 0, 1_780_000_001, 0, &mut txs)?;
    step(&mut tree, Op::Lst, 100_000_000, 0, 1_780_000_002, 1_780_000_001, &mut txs)?;
    step(&mut tree, Op::Lst, 200_000_000, 100_000_000, 1_780_000_003, 1_780_000_002, &mut txs)?;

    let payload = BatchPayload {
        old_root,
        end_block_height: 3_500_000,
        transactions: txs,
    };

    fs::create_dir_all(&args.batch_dir)?;
    let path = format!("{}/{}_batch.json", args.batch_dir, args.batch_id);
    fs::write(&path, serde_json::to_string_pretty(&payload)?)?;
    println!("wrote {path}");
    println!("  REG -> LST(1.0) -> LST(2.0) on {domain}");
    println!("  third tx carries old_price=100000000 for an LST");
    println!("  expected final root (reference tree): 0x{}", hex(&tree.root()));
    let rec = tree.record(domain).expect("domain present");
    println!("  expected final price: {} (the LAST listing wins)", rec.price);
    Ok(())
}

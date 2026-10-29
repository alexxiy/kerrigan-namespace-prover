//! Generates a valid `{batch_id}_batch.json` for the prover.
//!
//! Produces real Ed25519 keys, real signatures over `kns-core`'s message format,
//! well-formed mainnet Kerrigan Sapling addresses, and proofs taken from a canonical
//! compact SMT.
//!
//! Everything is derived deterministically from fixed seeds, so re-running produces
//! a byte-identical batch — a fixture that changes on every run is useless for
//! spotting a regression.
//!
//! The tree is `kns_core::tree::ReferenceTree` rather than a live rr-proxy daemon,
//! so this needs no running service. Both build the same canonical tree; the daemon
//! is tested against the same `verify_and_apply` this batch is proven with.
//!
//! ```bash
//! cargo run --release --bin gen_fixture -- --batch-dir /tmp --batch-id 1
//! cargo run --release --bin kns-script -- --batch-dir /tmp --batch-id 1 --execute
//! ```

use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Parser;
use ed25519_dalek::{Signer, SigningKey};

use kns_core::tree::ReferenceTree;
use kns_core::{signing_message, BatchPayload, LeafRecord, Op, Transaction};

#[derive(Parser, Debug)]
#[command(author, version, about = "Generates a valid KNS prover fixture batch")]
struct Args {
    #[arg(long)]
    batch_dir: String,

    #[arg(long, default_value = "1")]
    batch_id: String,

    /// Block height recorded in the batch header.
    #[arg(long, default_value_t = DEFAULT_END_BLOCK_HEIGHT)]
    end_block_height: u32,
}

const DEFAULT_END_BLOCK_HEIGHT: u32 = 160_000;

/// A deterministic Ed25519 key. Seeds are fixed so the fixture is reproducible.
fn key(seed: u8) -> SigningKey {
    SigningKey::from_bytes(&[seed; 32])
}

/// A deterministic, well-formed Kerrigan Sapling address for the network this build targets.
///
/// The 43-byte payload (11-byte diversifier + 32-byte `pk_d`) is derived from the seed
/// rather than being a spendable address, and that is sufficient *here* in a way it was
/// not for the Zcash original: on Kerrigan both sides of the boundary validate an address
/// structurally — bech32m prefix, character length, decoded payload size — and neither the
/// circuit nor the registrar's ingest check decodes `pk_d` as a Jubjub point. A fixture
/// built this way is therefore accepted or rejected identically by both, which is exactly
/// the property these fixtures exist to test.
///
/// If KNS ever adds a curve-point check at ingest, this must derive a real Sapling
/// address instead, or the fixture would pass the circuit and fail the indexer.
fn sapling_address(seed: u8) -> Result<String> {
    let mut payload = [0u8; kns_core::SAPLING_PAYLOAD_LEN];
    // Distinct, non-repeating bytes per seed so two seeds never collide and the payload
    // is obviously synthetic rather than looking like a real key.
    for (i, b) in payload.iter_mut().enumerate() {
        *b = seed.wrapping_mul(31).wrapping_add(i as u8);
    }

    let data = bech32::ToBase32::to_base32(&payload);
    let addr = bech32::encode(kns_core::EXPECTED_HRP, data, bech32::Variant::Bech32m)
        .context("failed to bech32m-encode the Sapling payload")?;

    // Cheap self-check: the generator and the validator must agree, or every fixture
    // would be rejected for a reason that has nothing to do with the logic under test.
    anyhow::ensure!(
        kns_core::is_address_valid(&addr),
        "generated address {addr} is not accepted by kns-core"
    );
    Ok(addr)
}

/// The in-flight state of one domain, mirroring what the registrar's database holds.
#[derive(Clone)]
struct DomainState {
    owner: SigningKey,
    target_address: String,
    price: u64,
    nonce: u64,
}

struct Builder {
    tree: ReferenceTree,
    transactions: Vec<Transaction>,
    old_root: [u8; 32],
    nonce: u64,
}

impl Builder {
    fn new() -> Self {
        let tree = ReferenceTree::new();
        Self {
            old_root: tree.root(),
            tree,
            transactions: Vec::new(),
            // Unix seconds, matching the front-end (Math.floor(Date.now() / 1000)).
            // The circuit only requires a strictly increasing sequence, but the fixture
            // should look like production data rather than inventing its own units.
            nonce: 1_780_000_000,
        }
    }

    fn next_nonce(&mut self) -> u64 {
        self.nonce += 1;
        self.nonce
    }

    /// Appends one transaction, taking its proof from the tree *before* applying the
    /// state change — which is exactly the order batchProcessor uses, and the order
    /// the circuit's root chaining requires.
    ///
    /// Returns the state actually written to the tree, which callers must use as the
    /// `before` of the next operation on that domain. It is not always `after`: see
    /// the price note below.
    #[allow(clippy::too_many_arguments)]
    fn push(
        &mut self,
        op: Op,
        domain: &str,
        signer: &SigningKey,
        before: Option<&DomainState>,
        after: DomainState,
    ) -> Result<DomainState> {
        let proof = self.tree.proof(domain);

        let pubkey = after.owner.verifying_key().to_bytes();
        let message = signing_message(
            op,
            domain,
            &after.target_address,
            &pubkey,
            after.price,
            after.nonce,
        );
        let signature = signer.sign(&message).to_bytes().to_vec();

        let (old_pubkey, old_target_address, old_price, old_nonce) = match before {
            Some(s) => (
                s.owner.verifying_key().to_bytes(),
                s.target_address.clone(),
                s.price,
                s.nonce,
            ),
            None => ([0u8; 32], String::new(), 0, 0),
        };

        self.transactions.push(Transaction {
            tx_id: format!("{:064x}", self.transactions.len() + 1),
            op: String::from_utf8(op.as_bytes().to_vec()).unwrap(),
            domain_name: domain.to_string(),
            old_target_address,
            target_address: after.target_address.clone(),
            old_pubkey,
            pubkey,
            price: after.price,
            old_price,
            nonce: after.nonce,
            old_nonce,
            signature,
            proof,
        });

        // The price the CIRCUIT writes into the resulting leaf, which is not always
        // the price on the transaction. Only LST carries a price into the leaf; every
        // other operation stores zero. BUY is the case that bites: the invariant
        // requires `price == old_price`, so the transaction carries the listed price,
        // but the new leaf clears it. Inserting `after.price` here instead would make
        // this tree diverge from the circuit's, and every later transaction in the
        // batch would fail its Merkle check.
        let stored_price = if op.binds_price() { after.price } else { 0 };

        self.tree.insert(LeafRecord {
            domain: domain.to_string(),
            pubkey,
            target_address: after.target_address.clone(),
            price: stored_price,
            nonce: after.nonce,
        });

        Ok(DomainState {
            price: stored_price,
            ..after
        })
    }
}

/// Builds the batch. Separated from `main` so tests can exercise it without
/// touching the filesystem.
fn build_batch() -> Result<(BatchPayload, [u8; 32])> {
    let alice = key(0x11);
    let bob = key(0x22);
    let carol = key(0x33);

    let addr_a = sapling_address(0x01)?;
    let addr_b = sapling_address(0x02)?;
    let addr_c = sapling_address(0x03)?;

    let mut b = Builder::new();

    // Each push returns the state the circuit actually stored, which is what the next
    // operation on that domain must treat as its "old" state.

    // REG: alice registers into an empty tree — a Vacant terminal at depth 0.
    let n = b.next_nonce();
    let alice1 = b.push(
        Op::Reg,
        "alice.krgn",
        &alice,
        None,
        DomainState { owner: alice.clone(), target_address: addr_a.clone(), price: 0, nonce: n },
    )?;

    // REG: a second domain lands on alice's slot and forces a split.
    let n = b.next_nonce();
    let bob1 = b.push(
        Op::Reg,
        "bob.krgn",
        &bob,
        None,
        DomainState { owner: bob.clone(), target_address: addr_b.clone(), price: 0, nonce: n },
    )?;

    // UPD: alice repoints her domain. The invariant requires the address to change.
    let n = b.next_nonce();
    let alice2 = b.push(
        Op::Upd,
        "alice.krgn",
        &alice,
        Some(&alice1),
        DomainState { target_address: addr_c.clone(), nonce: n, ..alice1.clone() },
    )?;

    // LST: alice lists for sale. Signed by the owner, and the only operation whose
    // price reaches the leaf.
    let n = b.next_nonce();
    let listed_price = 150_000_000u64;
    let alice3 = b.push(
        Op::Lst,
        "alice.krgn",
        &alice,
        Some(&alice2),
        DomainState { price: listed_price, nonce: n, ..alice2.clone() },
    )?;

    // BUY: carol buys at the listed price. Signed by the BUYER alone — the seller's
    // consent is the LST above, whose price the circuit checks via old_price. The
    // transaction carries `listed_price`; the resulting leaf stores 0.
    let n = b.next_nonce();
    let _alice4 = b.push(
        Op::Buy,
        "alice.krgn",
        &carol,
        Some(&alice3),
        DomainState {
            owner: carol.clone(),
            target_address: addr_a.clone(),
            price: listed_price,
            nonce: n,
        },
    )?;

    // LST then ULT on bob's domain, to exercise unlisting.
    let n = b.next_nonce();
    let bob2 = b.push(
        Op::Lst,
        "bob.krgn",
        &bob,
        Some(&bob1),
        DomainState { price: 90_000_000, nonce: n, ..bob1.clone() },
    )?;

    let n = b.next_nonce();
    let bob3 = b.push(
        Op::Ult,
        "bob.krgn",
        &bob,
        Some(&bob2),
        DomainState { price: 0, nonce: n, ..bob2.clone() },
    )?;

    // CHG: bob hands ownership to alice. Signed by the CURRENT owner.
    let n = b.next_nonce();
    let _bob4 = b.push(
        Op::Chg,
        "bob.krgn",
        &bob,
        Some(&bob3),
        DomainState { owner: alice.clone(), nonce: n, ..bob3.clone() },
    )?;

    let payload = BatchPayload {
        old_root: b.old_root,
        end_block_height: DEFAULT_END_BLOCK_HEIGHT,
        transactions: b.transactions,
    };

    Ok((payload, b.tree.root()))
}

fn main() -> Result<()> {
    let args = Args::parse();
    let batch_dir = PathBuf::from(&args.batch_dir);
    fs::create_dir_all(&batch_dir)
        .with_context(|| format!("cannot create {}", batch_dir.display()))?;

    let (mut payload, final_root) = build_batch()?;
    payload.end_block_height = args.end_block_height;

    let path = batch_dir.join(format!("{}_batch.json", args.batch_id));
    fs::write(&path, serde_json::to_string_pretty(&payload)?)
        .with_context(|| format!("cannot write {}", path.display()))?;

    println!("wrote {}", path.display());
    println!("  transactions : {}", payload.transactions.len());
    println!("  old_root     : 0x{}", hex::encode(payload.old_root));
    println!("  final root   : 0x{}", hex::encode(final_root));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The guest rejects anything that is not a mainnet Sapling address, so a
    /// generator that emits a subtly wrong one produces a fixture that fails for a
    /// reason unrelated to whatever is being tested.
    #[test]
    fn generated_addresses_are_accepted_by_the_circuit() {
        for seed in [0x01u8, 0x02, 0x03] {
            let addr = sapling_address(seed).unwrap();
            assert!(
                kns_core::is_address_valid(&addr),
                "generated address is not valid for this build's network: {addr}"
            );
        }
    }

    /// Every signature in the batch must verify under the same rules the circuit
    /// applies: CHG is signed by the outgoing owner, everything else by the key named
    /// in `pubkey`.
    #[test]
    fn every_signature_in_the_batch_verifies() {
        let (payload, _) = build_batch().unwrap();
        assert!(!payload.transactions.is_empty());

        for tx in &payload.transactions {
            let op = Op::parse(&tx.op, &tx.tx_id);
            let signer_bytes = if op == Op::Chg { tx.old_pubkey } else { tx.pubkey };
            let signer = ed25519_dalek::VerifyingKey::from_bytes(&signer_bytes)
                .expect("signer key must be a valid curve point");

            let message = signing_message(
                op,
                &tx.domain_name,
                &tx.target_address,
                &tx.pubkey,
                tx.price,
                tx.nonce,
            );
            assert!(
                kns_core::is_signature_valid(&signer, &message, &tx.signature),
                "signature for {} {} does not verify",
                tx.op,
                tx.domain_name
            );
        }
    }

    /// The batch must cover every operation, or it stops being a useful fixture.
    #[test]
    fn the_batch_exercises_all_six_operations() {
        let (payload, _) = build_batch().unwrap();
        for op in ["REG", "UPD", "CHG", "LST", "ULT", "BUY"] {
            assert!(
                payload.transactions.iter().any(|t| t.op == op),
                "the fixture never exercises {op}"
            );
        }
    }
}

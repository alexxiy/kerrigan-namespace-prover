#![no_main]
sp1_zkvm::entrypoint!(main);

extern crate alloc;

use alloy_sol_types::{sol, SolValue};
use ed25519_dalek::VerifyingKey;

use kns_core::{
    hash_leaf, is_address_valid, is_blocking_record_valid, is_domain_valid, is_signature_valid,
    signing_message, verify_and_apply, BatchPayload, Hash, Op, Terminal,
};

sol! {
    struct BatchResultABI {
        bytes32 old_root;
        bytes32 new_root;
        uint32 end_block_height;
    }
}

enum EitherKey<'a> {
    New(&'a VerifyingKey),
    Old(VerifyingKey),
}

impl<'a> EitherKey<'a> {
    fn get(&self) -> &VerifyingKey {
        match self {
            EitherKey::New(key) => key,
            EitherKey::Old(key) => key,
        }
    }
}

pub fn main() {
    let payload: BatchPayload = sp1_zkvm::io::read();

    // An empty batch would commit `new_root == old_root` alongside an arbitrary
    // `end_block_height` — a perfectly valid proof whose only on-chain effect is to
    // advance the height marker the anchor contract tracks. The registrar never
    // generates one; asserting it here means the circuit does not have to rely on
    // that being true.
    assert!(
        !payload.transactions.is_empty(),
        "CRITICAL: Batch contains no transactions"
    );

    let mut current_root = payload.old_root;

    for tx in payload.transactions {
        // Parse the operation code once; every later stage matches on the enum.
        let op = Op::parse(&tx.op, &tx.tx_id);

        // Parse new pubkey once.
        //
        // This runs for every operation, including CHG where the signer is the OLD
        // key. Decoding doubles as a check that the incoming owner key is a valid
        // curve point, so a domain can never be handed to a key that could never
        // produce a verifiable signature.
        let new_pubkey = VerifyingKey::from_bytes(&tx.pubkey)
            .expect("CRITICAL: New pubkey is not a valid Ed25519 curve point");

        // 1. REPLAY PROTECTION
        assert!(
            tx.nonce > tx.old_nonce,
            "CRITICAL: Replay attack detected! Nonce {} is not greater than {}", tx.nonce, tx.old_nonce
        );

        // 2. INPUT DATA VALIDATION
        //
        // Only REG validates the domain string: it is the one operation that introduces a
        // domain into the tree. For every other operation the domain is pinned by the
        // Merkle proof — the leaf commits the domain and the path key is derived from it,
        // so a provable non-REG can only name a domain some earlier REG already validated.
        // This is the same induction `Op::binds_target_address` relies on for the address,
        // and it holds for the same reason: the genesis root is the empty tree.
        if op == Op::Reg {
            assert!(
                is_domain_valid(&tx.domain_name),
                "CRITICAL: Domain name '{}' failed validation rules", tx.domain_name
            );
        }
        // Only operations that carry an address need to validate it; for the rest the
        // leaf pins it to a previously validated value. See `Op::binds_target_address`.
        if op.binds_target_address() {
            assert!(
                is_address_valid(&tx.target_address),
                "CRITICAL: Target address '{}' is not a valid Kerrigan Sapling address", tx.target_address
            );
        }

        // 3. STRICT LOGICAL CHECKS & INVARIANT VERIFICATION
        match op {
            Op::Reg => {
                assert_eq!(tx.old_pubkey, [0u8; 32], "CRITICAL: REG old_pubkey must be empty");
                assert_ne!(tx.pubkey, [0u8; 32], "CRITICAL: REG pubkey cannot be empty");
                assert_eq!(tx.old_price, 0, "CRITICAL: REG old_price must be 0");
                // A registration has no prior state, so there is no previous nonce to be
                // greater than. Without this the `nonce > old_nonce` check above is the
                // only constraint, and a REG could start the domain at any nonce the
                // submitter liked. The registrar already sends 0 here
                // (batchProcessor.php derives it as `op === REG ? 0 : …`), so this pins
                // an existing convention as a checked invariant rather than changing it.
                assert_eq!(tx.old_nonce, 0, "CRITICAL: REG old_nonce must be 0");
                // to be strict to PHP Protocol logic
                assert_eq!(tx.price, 0, "CRITICAL: REG price must be 0");
            },
            Op::Upd => {
                assert_ne!(tx.pubkey, [0u8; 32], "CRITICAL: UPD pubkey cannot be empty");
                assert_eq!(tx.old_pubkey, tx.pubkey, "CRITICAL: UPD pubkeys must match");
                assert_ne!(tx.old_target_address, tx.target_address, "CRITICAL: UPD must change target address");
                // to be strict to PHP Protocol logic
                assert_eq!(tx.price, 0, "CRITICAL: UPD price must be 0");
                assert_eq!(tx.old_price, 0, "CRITICAL: UPD old_price must be 0");
            },
            Op::Chg => {
                assert_ne!(tx.pubkey, [0u8; 32], "CRITICAL: CHG pubkey cannot be empty");
                assert_ne!(tx.old_pubkey, [0u8; 32], "CRITICAL: CHG old_pubkey cannot be empty");
                assert_ne!(tx.old_pubkey, tx.pubkey, "CRITICAL: CHG pubkeys must not match");
                // to be strict to PHP Protocol logic
                assert_eq!(tx.price, 0, "CRITICAL: CHG price must be 0");
                assert_eq!(tx.old_price, 0, "CRITICAL: CHG old_price must be 0");
            },
            Op::Lst => {
                assert_ne!(tx.pubkey, [0u8; 32], "CRITICAL: LST pubkey cannot be empty");
                assert_eq!(tx.old_pubkey, tx.pubkey, "CRITICAL: LST pubkeys must match");
                assert!(tx.price > 0, "CRITICAL: LST price must be greater than 0");
                // `old_price` is deliberately unconstrained: re-listing an already-listed
                // domain at a new price is legitimate, and a batch may carry several
                // operations on one domain. The registrar chains them in memory (see
                // Protocol::commitDomainState), so the second LST's `old_price` is the
                // price the first one set, and the SMT proof chains the same way - the old
                // leaf pins whatever price the tree currently holds.
                //
                // Requiring old_price == 0 here would have made every such batch
                // unprovable, halting the checkpoint chain for every other transaction
                // batched alongside it. Soundness does not depend on it: the owner signs
                // the new price (Op::binds_price), the old price is pinned by the old leaf,
                // and the owner is unchanged by the assertion above.
            },
            Op::Ult => {
                assert_ne!(tx.pubkey, [0u8; 32], "CRITICAL: ULT pubkey cannot be empty");
                assert_eq!(tx.old_pubkey, tx.pubkey, "CRITICAL: ULT pubkeys must match");
                assert!(tx.old_price > 0, "CRITICAL: ULT domain must be listed");
                assert_eq!(tx.price, 0, "CRITICAL: ULT new price must be 0");
            },
            Op::Buy => {
                assert_ne!(tx.pubkey, [0u8; 32], "CRITICAL: BUY pubkey cannot be empty");
                assert_ne!(tx.old_pubkey, [0u8; 32], "CRITICAL: BUY old_pubkey cannot be empty");
                assert_ne!(tx.old_pubkey, tx.pubkey, "CRITICAL: BUY pubkeys must not match");
                assert!(tx.old_price > 0, "CRITICAL: Cannot buy unlisted domain");
                assert_eq!(tx.old_price, tx.price, "CRITICAL: Paid price does not match listed price");
            },
        }

        // 4. SIGNATURE CHECKING
        //
        // CHG is signed by the CURRENT owner (old_pubkey), because it is the outgoing
        // owner who authorises the transfer. Every other operation is signed by the
        // key named in `pubkey`.
        //
        // Note BUY is signed by the BUYER alone, by design: the seller's consent is
        // their earlier signed LST, whose price is pinned into the leaf and checked
        // by the `old_price == price` invariant above.
        let signer_pubkey = match op {
            Op::Chg => {
                let old_pubkey = VerifyingKey::from_bytes(&tx.old_pubkey)
                    .expect("CRITICAL: Old pubkey is not a valid Ed25519 curve point");
                EitherKey::Old(old_pubkey)
            },
            _ => EitherKey::New(&new_pubkey),
        };

        let message_bytes = signing_message(
            op,
            &tx.domain_name,
            &tx.target_address,
            &tx.pubkey,
            tx.price,
            tx.nonce,
        );

        assert!(
            is_signature_valid(signer_pubkey.get(), &message_bytes, &tx.signature),
            "CRITICAL: Invalid signature for TX {}", tx.tx_id
        );

        // 5. SMT LEAF TRANSITIONS
        //
        // REG has no expected old leaf: its proof must instead demonstrate that the
        // slot is vacant, or held by a different domain (in which case the tree is
        // split). `verify_and_apply` rejects an inclusion terminal for REG, which is
        // what stops an already-registered domain from being re-registered.
        let (expected_old_leaf, new_leaf): (Option<Hash>, Hash) = match op {
            Op::Reg => {
                let new_leaf = hash_leaf(&tx.domain_name, &tx.pubkey, &tx.target_address, 0, tx.nonce);
                (None, new_leaf)
            },
            Op::Upd => {
                let old_leaf = hash_leaf(&tx.domain_name, &tx.pubkey, &tx.old_target_address, 0, tx.old_nonce);
                let new_leaf = hash_leaf(&tx.domain_name, &tx.pubkey, &tx.target_address, 0, tx.nonce);
                (Some(old_leaf), new_leaf)
            },
            Op::Chg => {
                let old_leaf = hash_leaf(&tx.domain_name, &tx.old_pubkey, &tx.target_address, 0, tx.old_nonce);
                let new_leaf = hash_leaf(&tx.domain_name, &tx.pubkey, &tx.target_address, 0, tx.nonce);
                (Some(old_leaf), new_leaf)
            },
            Op::Lst => {
                let old_leaf = hash_leaf(&tx.domain_name, &tx.pubkey, &tx.target_address, tx.old_price, tx.old_nonce);
                let new_leaf = hash_leaf(&tx.domain_name, &tx.pubkey, &tx.target_address, tx.price, tx.nonce);
                (Some(old_leaf), new_leaf)
            },
            Op::Ult => {
                let old_leaf = hash_leaf(&tx.domain_name, &tx.pubkey, &tx.target_address, tx.old_price, tx.old_nonce);
                let new_leaf = hash_leaf(&tx.domain_name, &tx.pubkey, &tx.target_address, 0, tx.nonce);
                (Some(old_leaf), new_leaf)
            },
            Op::Buy => {
                let old_leaf = hash_leaf(&tx.domain_name, &tx.old_pubkey, &tx.old_target_address, tx.old_price, tx.old_nonce);
                let new_leaf = hash_leaf(&tx.domain_name, &tx.pubkey, &tx.target_address, 0, tx.nonce);
                (Some(old_leaf), new_leaf)
            },
        };

        // A blocking record is the one input here that nobody signs, and its domain decides
        // where the split puts the blocking leaf. Its preimage is checked against the leaf
        // only by hash, and the leaf hash does not delimit its fields, so the record must be
        // cut the one way a real leaf is. See `kns_core::is_blocking_record_valid`.
        if let Terminal::Blocked { record } = &tx.proof.terminal {
            assert!(
                is_blocking_record_valid(record),
                "CRITICAL: Blocking record '{}' for domain '{}' is not a valid leaf preimage",
                record.domain, tx.domain_name
            );
        }

        let (calc_root, next_root) =
            verify_and_apply(&tx.domain_name, &tx.proof, expected_old_leaf, new_leaf);

        assert_eq!(
            calc_root, current_root,
            "CRITICAL: Merkle proof verification failed for domain '{}'", tx.domain_name
        );

        current_root = next_root;
    }

    let result_abi = BatchResultABI {
        old_root: payload.old_root.into(),
        new_root: current_root.into(),
        end_block_height: payload.end_block_height,
    };

    sp1_zkvm::io::commit_slice(&result_abi.abi_encode());
}

//! Compact Sparse Merkle Tree.
//!
//! Implements `docs/compact-smt.md`. Read that document before changing anything
//! here; it is the shared contract with the rr-proxy daemon and the PHP client, and
//! `docs/reference/csmt_reference.py` is an independent implementation of it that
//! this module's golden vectors are taken from.
//!
//! A leaf sits at the shallowest depth at which it is the only key in its subtree,
//! so a proof carries ~log2(N) siblings rather than a fixed 128. Empty subtrees are
//! the single constant [`EMPTY`] at every height — there is no default-hash ladder.

use serde::{Deserialize, Serialize};

use crate::{hash_leaf, hash_node, domain_path};

/// A 32-byte SHA-256 digest.
pub type Hash = [u8; 32];

/// The hash of an empty subtree, at every height.
///
/// Unlike the dense tree this replaces, there is no per-height ladder: one constant
/// serves every depth, and the root of an empty tree is this value.
pub const EMPTY: Hash = [0u8; 32];

/// Upper bound on leaf depth, equal to the key length in bits.
///
/// This is a bound, not the exact proof length — that is [`Proof::depth`].
pub const MAX_DEPTH: usize = 128;

/// Bytes in a tree key: the first 128 bits of `SHA256(domain)`.
pub const KEY_LEN: usize = MAX_DEPTH / 8;

/// A domain's position in the tree.
pub type Key = [u8; KEY_LEN];

/// The full leaf preimage of the domain blocking a registration.
///
/// The whole record is carried, not just the key, because the circuit must derive
/// the blocking key from the same bytes that produce the blocking leaf hash. See
/// `docs/compact-smt.md` §5.3 — supplying only the key lets an attacker forge the
/// divergence bit and permanently strand the blocking domain's leaf.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct LeafRecord {
    pub domain: String,
    pub pubkey: [u8; 32],
    pub target_address: String,
    pub price: u64,
    pub nonce: u64,
}

impl LeafRecord {
    /// The leaf hash this record commits to.
    pub fn leaf(&self) -> Hash {
        hash_leaf(
            &self.domain,
            &self.pubkey,
            &self.target_address,
            self.price,
            self.nonce,
        )
    }
}

/// What sits at the end of a key's path.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub enum Terminal {
    /// The key's own leaf is here — the key is present.
    Occupied,
    /// An empty subtree is here — the key is absent.
    Vacant,
    /// A different domain's leaf is here — the key is absent, and inserting it
    /// requires splitting.
    Blocked { record: LeafRecord },
}

/// A Merkle proof: the path from a terminal at `depth` up to the root.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    /// Depth of the terminal node, `0..=MAX_DEPTH`.
    pub depth: u8,
    /// Sibling hashes, deepest first: `siblings[i]` is the sibling at depth
    /// `depth - i`. Length must equal `depth`.
    pub siblings: Vec<Hash>,
    pub terminal: Terminal,
}

/// A domain's tree key: the first 128 bits of `SHA256(domain)`.
pub fn key_of(domain: &str) -> Key {
    let digest = domain_path(domain);
    let mut key = [0u8; KEY_LEN];
    key.copy_from_slice(&digest[..KEY_LEN]);
    key
}

/// Path bit `i`, most-significant-bit first within each byte. `true` selects the
/// right child.
pub fn key_bit(key: &Key, i: usize) -> bool {
    (key[i / 8] >> (7 - (i % 8))) & 1 == 1
}

/// Whether two keys agree on their first `d` path bits.
pub fn shares_prefix(a: &Key, b: &Key, d: usize) -> bool {
    (0..d).all(|i| key_bit(a, i) == key_bit(b, i))
}

/// The first path bit at or after `from` at which two keys differ.
///
/// `None` means the keys are equal over all [`MAX_DEPTH`] bits.
pub fn first_divergence(a: &Key, b: &Key, from: usize) -> Option<usize> {
    (from..MAX_DEPTH).find(|&i| key_bit(a, i) != key_bit(b, i))
}

/// Folds `start` at depth `siblings.len()` up to the root along `key`'s path.
pub fn fold(key: &Key, start: Hash, siblings: &[Hash]) -> Hash {
    let n = siblings.len();
    let mut h = start;
    for (i, sibling) in siblings.iter().enumerate() {
        h = if key_bit(key, n - 1 - i) {
            hash_node(sibling, &h)
        } else {
            hash_node(&h, sibling)
        };
    }
    h
}

/// Verifies `proof` and applies the transition, returning
/// `(reconstructed_old_root, new_root)`.
///
/// The caller checks `reconstructed_old_root` against the state it expects, exactly
/// as with the dense tree — this function makes no assertion about it, so the same
/// code serves the guest (which asserts) and host tooling (which does not).
///
/// `old_leaf` is `Some` for an update, which requires [`Terminal::Occupied`], and
/// `None` for a registration, which requires a non-inclusion terminal. Everything
/// else panics, which makes the batch unprovable.
pub fn verify_and_apply(
    domain: &str,
    proof: &Proof,
    old_leaf: Option<Hash>,
    new_leaf: Hash,
) -> (Hash, Hash) {
    let d = proof.depth as usize;

    assert!(
        d <= MAX_DEPTH,
        "CRITICAL: Merkle proof depth {} exceeds the maximum of {}", d, MAX_DEPTH
    );
    assert_eq!(
        proof.siblings.len(), d,
        "CRITICAL: Merkle proof has {} siblings but claims depth {}",
        proof.siblings.len(), d
    );

    let key = key_of(domain);

    match &proof.terminal {
        // -- inclusion: the key is present, and its leaf is replaced in place. The
        //    key set does not change, so neither does the structure.
        Terminal::Occupied => {
            let old_leaf = old_leaf.expect(
                "CRITICAL: REG requires a non-inclusion terminal, but the domain is already registered",
            );
            (
                fold(&key, old_leaf, &proof.siblings),
                fold(&key, new_leaf, &proof.siblings),
            )
        }

        // -- registration into an empty subtree: one key in a zero-key subtree makes
        //    it a one-key subtree, so the leaf simply replaces the EMPTY.
        Terminal::Vacant => {
            assert!(
                old_leaf.is_none(),
                "CRITICAL: an update requires an Occupied terminal, but the domain is absent"
            );
            (
                fold(&key, EMPTY, &proof.siblings),
                fold(&key, new_leaf, &proof.siblings),
            )
        }

        // -- registration into a slot held by another domain: split down to the bit
        //    where the two keys diverge.
        Terminal::Blocked { record } => {
            assert!(
                old_leaf.is_none(),
                "CRITICAL: an update requires an Occupied terminal, but the domain is absent"
            );
            assert!(
                d < MAX_DEPTH,
                "CRITICAL: a blocked terminal at maximum depth implies a full key collision"
            );

            // Deriving BOTH the leaf hash and the key from this one record is what
            // binds them together; see the type's docs and spec §5.3.
            let blocking_leaf = record.leaf();
            let blocking_key = key_of(&record.domain);

            assert_ne!(
                blocking_key, key,
                "CRITICAL: blocking record is for domain '{}', which shares this key — that is an inclusion proof",
                record.domain
            );
            assert!(
                shares_prefix(&blocking_key, &key, d),
                "CRITICAL: blocking domain '{}' does not lie on this key's path at depth {}",
                record.domain, d
            );

            let old_root = fold(&key, blocking_leaf, &proof.siblings);

            let j = first_divergence(&key, &blocking_key, d).expect(
                "CRITICAL: blocking domain has an identical 128-bit key — unregisterable collision",
            );

            // At depth j the two leaves become siblings, ordered by bit j.
            let mut node = if key_bit(&key, j) {
                hash_node(&blocking_leaf, &new_leaf)
            } else {
                hash_node(&new_leaf, &blocking_leaf)
            };
            // Depths j-1 down to d: the keys still agree, so the other child is empty.
            for i in (d..j).rev() {
                node = if key_bit(&key, i) {
                    hash_node(&EMPTY, &node)
                } else {
                    hash_node(&node, &EMPTY)
                };
            }

            (old_root, fold(&key, node, &proof.siblings))
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------
//
// Golden values come from `docs/reference/csmt_reference.py`, an independent
// implementation of the spec. The `ReferenceTree` used to build proofs derives the
// root DECLARATIVELY from the key set, while `verify_and_apply` reaches it
// incrementally through the split logic — so agreement between them is evidence,
// not a tautology.

#[cfg(all(test, feature = "reference-tree"))]
mod tests {
    use super::*;
    use crate::tree::ReferenceTree;

    const PK: [u8; 32] = [1u8; 32];

    fn rec(domain: &str, nonce: u64) -> LeafRecord {
        LeafRecord {
            domain: domain.into(),
            pubkey: PK,
            target_address: "u1abc".into(),
            price: 0,
            nonce,
        }
    }

    fn hex(bytes: &[u8]) -> String {
        let mut buf = vec![0u8; bytes.len() * 2];
        crate::write_hex(&mut buf, bytes);
        String::from_utf8(buf).unwrap()
    }

    /// Registers `domain`, asserting the incremental result matches the canonical
    /// root and that the proof verified against the tree's previous root.
    fn register(tree: &mut ReferenceTree, domain: &str) -> Hash {
        let before = tree.root();
        let proof = tree.proof(domain);
        let record = rec(domain, 1);
        let (old_root, new_root) = verify_and_apply(domain, &proof, None, record.leaf());
        assert_eq!(old_root, before, "{domain}: proof did not reconstruct the old root");
        tree.insert(record);
        assert_eq!(new_root, tree.root(), "{domain}: incremental root != canonical root");
        new_root
    }

    // -- golden vectors -----------------------------------------------------

    #[test]
    fn empty_tree_root_is_the_empty_constant() {
        assert_eq!(ReferenceTree::new().root(), EMPTY);
        assert_eq!(hex(&EMPTY), "0".repeat(64));
    }

    #[test]
    fn registration_sequence_matches_reference() {
        let mut t = ReferenceTree::new();
        let expected = [
            ("alice.krgn", "339377c329cb7a64952b360fd20265bc3da7cfa1547734a5338267dd8d095f6b"),
            ("bob.krgn",   "8ec1ba5192b78fc356685468317d228a4ceadb91a532feb0465e39e673865c5e"),
            ("carol.krgn", "816cf7da2a5fa83844c6f3e88da63210b391fdf91595f0b27a761e7dca5083c1"),
            ("dave.krgn",  "6f0ac9a07d394e5156df139187950ab2a589dfc889cc6de21671f13601f0e217"),
            ("eve.krgn",   "0f529a84c77ac607ec89f17a46a4c4fb16c983431ad9d297ed914fbb77000582"),
        ];
        for (domain, want) in expected {
            assert_eq!(hex(&register(&mut t, domain)), want, "after REG {domain}");
        }
    }

    #[test]
    fn one_leaf_tree_root_is_that_leaf() {
        let mut t = ReferenceTree::new();
        let root = register(&mut t, "alice.krgn");
        assert_eq!(root, rec("alice.krgn", 1).leaf());
        assert_eq!(t.proof("alice.krgn").depth, 0, "a lone leaf sits at the root");
    }

    #[test]
    fn key_derivation_matches_reference() {
        assert_eq!(hex(&key_of("alice.krgn")), "fbf0a43deee9bf66e4bf5415259f5cf4");
        assert_eq!(hex(&key_of("bob.krgn")), "a96751d69f7583b1cd101a6ad887ff69");
        // 0xfb = 0b1111_1011, most-significant-bit first.
        let k = key_of("alice.krgn");
        let got: Vec<u8> = (0..8).map(|i| key_bit(&k, i) as u8).collect();
        assert_eq!(got, vec![1, 1, 1, 1, 1, 0, 1, 1]);
    }

    // -- structure ----------------------------------------------------------

    #[test]
    fn leaves_stay_shallow_and_all_remain_provable() {
        let mut t = ReferenceTree::new();
        let domains: Vec<String> = (0..120).map(|i| format!("d{i}.krgn")).collect();
        let mut root = EMPTY;
        for d in &domains {
            root = register(&mut t, d);
        }

        let depths: Vec<usize> = domains.iter().map(|d| t.proof(d).depth as usize).collect();
        let max = *depths.iter().max().unwrap();
        assert!(max < 32, "120 domains should stay far above depth 32, got {max}");

        for d in &domains {
            let proof = t.proof(d);
            assert_eq!(proof.terminal, Terminal::Occupied);
            let leaf = t.leaf(d).unwrap();
            let (old_root, _) = verify_and_apply(d, &proof, Some(leaf), [0xAAu8; 32]);
            assert_eq!(old_root, root, "{d} became unprovable");
        }
    }

    #[test]
    fn insertion_order_does_not_change_the_root() {
        let domains = ["alice.krgn", "bob.krgn", "carol.krgn", "dave.krgn"];
        let mut forward = ReferenceTree::new();
        for d in domains {
            forward.insert(rec(d, 1));
        }
        let mut backward = ReferenceTree::new();
        for d in domains.iter().rev() {
            backward.insert(rec(d, 1));
        }
        assert_eq!(forward.root(), backward.root());
    }

    #[test]
    fn both_split_shapes_occur_and_verify() {
        // Registering many names exercises j == d (immediate divergence) and j > d
        // (a chain of single-child internals) without having to hand-pick names.
        let mut t = ReferenceTree::new();
        let (mut vacant, mut blocked) = (0, 0);
        for i in 0..80 {
            let d = format!("s{i}.krgn");
            match t.proof(&d).terminal {
                Terminal::Vacant => vacant += 1,
                Terminal::Blocked { .. } => blocked += 1,
                Terminal::Occupied => unreachable!(),
            }
            register(&mut t, &d);
        }
        assert!(vacant > 0 && blocked > 0, "expected both terminals, got {vacant}/{blocked}");
    }

    #[test]
    fn update_in_place_keeps_depth_and_only_moves_the_new_root() {
        let mut t = ReferenceTree::new();
        for d in ["alice.krgn", "bob.krgn", "carol.krgn"] {
            register(&mut t, d);
        }
        let root = t.root();
        let proof = t.proof("alice.krgn");
        let old = t.leaf("alice.krgn").unwrap();

        let (o1, n1) = verify_and_apply("alice.krgn", &proof, Some(old), rec("alice.krgn", 2).leaf());
        let (o2, n2) = verify_and_apply("alice.krgn", &proof, Some(old), rec("alice.krgn", 3).leaf());
        assert_eq!(o1, root);
        assert_eq!(o1, o2, "old root must not depend on the new leaf");
        assert_ne!(n1, n2, "different new leaves must give different roots");

        t.insert(rec("alice.krgn", 2));
        assert_eq!(n1, t.root());
    }

    // -- adversarial (docs/compact-smt.md §7) -------------------------------

    fn populated() -> (ReferenceTree, Hash) {
        let mut t = ReferenceTree::new();
        let mut root = EMPTY;
        for i in 0..40 {
            root = register(&mut t, &format!("d{i}.krgn"));
        }
        (t, root)
    }

    /// A fresh name whose slot is held by another domain.
    fn blocked_name(t: &ReferenceTree) -> (String, Proof, LeafRecord) {
        for i in 0..500 {
            let name = format!("atk{i}.krgn");
            let proof = t.proof(&name);
            if let Terminal::Blocked { ref record } = proof.terminal {
                let record = record.clone();
                return (name, proof, record);
            }
        }
        panic!("no blocked slot found");
    }

    #[test]
    #[should_panic(expected = "does not lie on this key's path")]
    fn rejects_blocking_record_for_an_unrelated_domain() {
        // The §5.3 attack: keep the fold intact but swap the record to forge the
        // divergence bit. Changing the record changes the leaf hash, so this is
        // caught -- here by the prefix check, which fires first.
        let (t, _) = populated();
        let (name, proof, _) = blocked_name(&t);
        let forged = Proof {
            terminal: Terminal::Blocked { record: rec("zzzzzzzz.krgn", 1) },
            ..proof
        };
        verify_and_apply(&name, &forged, None, rec(&name, 1).leaf());
    }

    #[test]
    #[should_panic(expected = "CRITICAL")]
    fn rejects_blocking_record_that_hashes_elsewhere() {
        // Same domain, tampered fields: the key checks pass but the leaf hash no
        // longer matches what is in the tree, so the reconstructed root diverges.
        let (t, root) = populated();
        let (name, proof, record) = blocked_name(&t);
        let tampered = LeafRecord { price: record.price + 1, ..record };
        let forged = Proof { terminal: Terminal::Blocked { record: tampered }, ..proof };
        let (old_root, _) = verify_and_apply(&name, &forged, None, rec(&name, 1).leaf());
        assert_eq!(old_root, root, "CRITICAL: tampered record must not reconstruct the root");
    }

    #[test]
    #[should_panic(expected = "that is an inclusion proof")]
    fn rejects_blocking_record_naming_our_own_domain() {
        let (t, _) = populated();
        let (name, proof, _) = blocked_name(&t);
        let forged = Proof {
            terminal: Terminal::Blocked { record: rec(&name, 1) },
            ..proof
        };
        verify_and_apply(&name, &forged, None, rec(&name, 1).leaf());
    }

    #[test]
    #[should_panic(expected = "siblings but claims depth")]
    fn rejects_sibling_count_mismatch() {
        let (t, _) = populated();
        let mut proof = t.proof("d0.krgn");
        proof.siblings.pop();
        verify_and_apply("d0.krgn", &proof, t.leaf("d0.krgn"), [0xAAu8; 32]);
    }

    #[test]
    #[should_panic(expected = "exceeds the maximum")]
    fn rejects_depth_beyond_the_maximum() {
        let proof = Proof {
            depth: (MAX_DEPTH + 1) as u8,
            siblings: vec![EMPTY; MAX_DEPTH + 1],
            terminal: Terminal::Occupied,
        };
        verify_and_apply("d0.krgn", &proof, Some([1u8; 32]), [0xAAu8; 32]);
    }

    #[test]
    #[should_panic(expected = "already registered")]
    fn rejects_registration_onto_an_occupied_terminal() {
        let (t, _) = populated();
        verify_and_apply("d0.krgn", &t.proof("d0.krgn"), None, rec("d0.krgn", 9).leaf());
    }

    #[test]
    #[should_panic(expected = "requires an Occupied terminal")]
    fn rejects_update_against_a_vacant_terminal() {
        let (t, _) = populated();
        let name = (0..500)
            .map(|i| format!("free{i}.krgn"))
            .find(|n| t.proof(n).terminal == Terminal::Vacant)
            .expect("no vacant slot found");
        verify_and_apply(&name, &t.proof(&name), Some([1u8; 32]), [0xAAu8; 32]);
    }

    #[test]
    #[should_panic(expected = "requires an Occupied terminal")]
    fn rejects_update_against_a_blocked_terminal() {
        let (t, _) = populated();
        let (name, proof, _) = blocked_name(&t);
        verify_and_apply(&name, &proof, Some([1u8; 32]), [0xAAu8; 32]);
    }

    /// A wrong depth does not need an explicit check: it folds a different number of
    /// times and cannot reproduce the root.
    #[test]
    fn wrong_depth_cannot_reconstruct_the_root() {
        let (t, root) = populated();
        let proof = t.proof("d0.krgn");
        let leaf = t.leaf("d0.krgn").unwrap();

        let mut shallow = proof.clone();
        shallow.depth -= 1;
        shallow.siblings.remove(0);
        let (bad, _) = verify_and_apply("d0.krgn", &shallow, Some(leaf), [0xAAu8; 32]);
        assert_ne!(bad, root);

        let mut deep = proof.clone();
        deep.depth += 1;
        deep.siblings.insert(0, EMPTY);
        let (bad, _) = verify_and_apply("d0.krgn", &deep, Some(leaf), [0xAAu8; 32]);
        assert_ne!(bad, root);
    }

    #[test]
    fn vacant_terminal_cannot_be_claimed_for_a_present_key() {
        let (t, root) = populated();
        let proof = t.proof("d0.krgn");
        let forged = Proof { terminal: Terminal::Vacant, ..proof };
        let (bad, _) = verify_and_apply("d0.krgn", &forged, None, [0xAAu8; 32]);
        assert_ne!(bad, root, "an empty leaf must not reconstruct a populated root");
    }
}

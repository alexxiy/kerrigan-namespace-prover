//! An in-memory compact SMT built **declaratively** from the key set.
//!
//! This is not the production tree — the rr-proxy daemon owns that, backed by
//! RocksDB and updated incrementally. This one recomputes everything from scratch,
//! which makes it useless for a live index and ideal for two other jobs:
//!
//! * cross-checking [`crate::smt::verify_and_apply`], whose incremental split logic
//!   is a genuinely different algorithm from the canonical-form definition here, so
//!   agreement between them is real evidence rather than a tautology;
//! * generating test fixtures, which need a tree that can be built from nothing.
//!
//! Behind the `reference-tree` feature so it never reaches the guest ELF.
//!
//! The canonical form (`docs/compact-smt.md` §2.1) is: a subtree holding no keys is
//! [`EMPTY`], one key is that leaf placed at this depth, and two or more is an
//! internal node over the two halves.

use std::collections::BTreeMap;

use crate::hash_node;
use crate::smt::{key_bit, key_of, Hash, LeafRecord, Proof, Terminal, EMPTY, MAX_DEPTH};

/// A compact Sparse Merkle Tree over a set of domain records.
#[derive(Debug, Clone, Default)]
pub struct ReferenceTree {
    records: BTreeMap<String, LeafRecord>,
}

impl ReferenceTree {
    pub fn new() -> Self {
        Self {
            records: BTreeMap::new(),
        }
    }

    /// Inserts or replaces a domain's record.
    pub fn insert(&mut self, record: LeafRecord) {
        self.records.insert(record.domain.clone(), record);
    }

    pub fn contains(&self, domain: &str) -> bool {
        self.records.contains_key(domain)
    }

    pub fn record(&self, domain: &str) -> Option<&LeafRecord> {
        self.records.get(domain)
    }

    /// The leaf hash of a present domain.
    pub fn leaf(&self, domain: &str) -> Option<Hash> {
        self.records.get(domain).map(|r| r.leaf())
    }

    /// The canonical root.
    pub fn root(&self) -> Hash {
        let all: Vec<&String> = self.records.keys().collect();
        self.subtree(&all, 0)
    }

    /// Canonical form, §2.1.
    fn subtree(&self, keys: &[&String], depth: usize) -> Hash {
        match keys.len() {
            0 => EMPTY,
            1 => self.records[keys[0]].leaf(),
            _ => {
                debug_assert!(depth < MAX_DEPTH, "two distinct keys must diverge within MAX_DEPTH");
                let (right, left): (Vec<&String>, Vec<&String>) = keys
                    .iter()
                    .partition(|d| key_bit(&key_of(d), depth));
                hash_node(&self.subtree(&left, depth + 1), &self.subtree(&right, depth + 1))
            }
        }
    }

    /// Domains whose key agrees with `key` on its first `depth` bits.
    fn keys_under(&self, key: &crate::smt::Key, depth: usize) -> Vec<&String> {
        self.records
            .keys()
            .filter(|d| {
                let k = key_of(d);
                (0..depth).all(|i| key_bit(&k, i) == key_bit(key, i))
            })
            .collect()
    }

    /// A proof for `domain`, present or not.
    pub fn proof(&self, domain: &str) -> Proof {
        let key = key_of(domain);
        let mut siblings = Vec::new();
        let mut depth = 0usize;

        // Descend while this subtree still holds more than one key: that is exactly
        // the condition under which an internal node exists here.
        while self.keys_under(&key, depth).len() > 1 {
            let sibling_keys: Vec<&String> = self
                .keys_under(&key, depth)
                .into_iter()
                .filter(|d| key_bit(&key_of(d), depth) != key_bit(&key, depth))
                .collect();
            siblings.push(self.subtree(&sibling_keys, depth + 1));
            depth += 1;
        }

        let here = self.keys_under(&key, depth);
        let terminal = match here.first() {
            None => Terminal::Vacant,
            Some(d) if d.as_str() == domain => Terminal::Occupied,
            Some(d) => Terminal::Blocked {
                record: self.records[*d].clone(),
            },
        };

        siblings.reverse(); // deepest first
        Proof {
            depth: depth as u8,
            siblings,
            terminal,
        }
    }
}

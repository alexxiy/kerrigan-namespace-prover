//! Protocol logic shared by the KNS zkVM guest, the host prover runner and the
//! fixture generator.
//!
//! Everything in here defines the wire protocol: the batch structures, the exact
//! bytes that get signed, the leaf/node hash functions and the Sparse Merkle Tree
//! traversal. The host that builds the tree and produces signatures (today a PHP
//! backend) must agree with this crate byte-for-byte, so this is the single place
//! those rules are written down.

pub mod smt;
#[cfg(feature = "reference-tree")]
pub mod tree;

pub use smt::{
    fold, first_divergence, key_bit, key_of, shares_prefix, verify_and_apply, Hash, Key,
    LeafRecord, Proof, Terminal, EMPTY, KEY_LEN, MAX_DEPTH,
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[cfg(feature = "signatures")]
use ed25519_dalek::{Signature, VerifyingKey};

// ---------------------------------------------------------------------------
// Network parameterisation
// ---------------------------------------------------------------------------

/// Prefix on every signed message, carrying the protocol name and version.
///
/// Mainnet and testnet use distinct prefixes so a signature produced against a
/// staging deployment can never be replayed onto mainnet. This matters most for
/// `CHG`: that message binds only the domain, the new owner key and the nonce, so
/// without the prefix split a staging ownership transfer would be a valid mainnet
/// ownership transfer whenever the nonce ordering happened to allow it.
#[cfg(not(feature = "testnet"))]
pub const MESSAGE_PREFIX: &[u8] = b"KNS:1:";
/// See the mainnet variant for the rationale.
#[cfg(feature = "testnet")]
pub const MESSAGE_PREFIX: &[u8] = b"tKNS:1:";

/// Bech32m human-readable prefix of the Kerrigan Sapling addresses this build accepts.
///
/// Mainnet shielded addresses are `ks1…`; testnet ones are `ktestsapling1…`. The regtest
/// (`kregsapling1…`) and devnet (`kdevsapling1…`) forms are not accepted on either network.
#[cfg(not(feature = "testnet"))]
pub const EXPECTED_HRP: &str = "ks";
/// See the mainnet variant.
#[cfg(feature = "testnet")]
pub const EXPECTED_HRP: &str = "ktestsapling";

/// Decoded payload length of a Sapling payment address: 11-byte diversifier + 32-byte `pk_d`.
pub const SAPLING_PAYLOAD_LEN: usize = 43;

/// Exact character length of an acceptable address, derived rather than hardcoded.
///
/// Bech32m encodes the 43-byte payload as `ceil(43 * 8 / 5) = 69` data characters plus a
/// 6-character checksum, and adds the `1` separator, so the total is
/// `hrp.len() + 1 + 69 + 6`: 78 for `ks`, 88 for `ktestsapling`.
///
/// The length is pinned as well as the prefix and the decoded payload size because a
/// bech32 decoder will happily accept other payload lengths under the same prefix, and
/// the PHP host enforces exactly this number. Any disagreement here is a command the
/// indexer accepts but the circuit rejects, which stalls the batch.
pub const EXPECTED_ADDRESS_LEN: usize = EXPECTED_HRP.len() + 1 + 69 + 6;

/// Domain suffixes the protocol will register.
pub const ALLOWED_ZONES: [&str; 5] = ["kerrigan", "krgn", "private", "secure", "safe"];

// ---------------------------------------------------------------------------
// Hash domain separation
// ---------------------------------------------------------------------------

/// Domain-separation tags for the Sparse Merkle Tree hash functions.
///
/// A leaf preimage and an internal-node preimage are both fed to a bare SHA-256.
/// Without a tag, a preimage crafted to be exactly 64 bytes could be reinterpreted
/// as an internal node (the classic Merkle leaf/node confusion). Tagging makes the
/// two hash domains disjoint regardless of the lengths of the variable-size
/// `domain` and `target_address` fields.
///
/// NOTE: These tags are part of the wire protocol. The host that builds the tree
/// MUST apply the identical tags, including when deriving its empty-subtree
/// constant ladder, or every Merkle proof will fail to verify.
pub const LEAF_TAG: u8 = 0x00;
/// See [`LEAF_TAG`].
pub const NODE_TAG: u8 = 0x01;

// ---------------------------------------------------------------------------
// Wire types
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Transaction {
    pub tx_id: String,
    pub op: String,
    pub domain_name: String,
    pub old_target_address: String,
    pub target_address: String,
    pub old_pubkey: [u8; 32], // The previous owner
    pub pubkey: [u8; 32],     // The new/current owner
    pub price: u64,           // The requested action price
    pub old_price: u64,       // The previous price state
    pub nonce: u64,           // The current timestamp/nonce
    pub old_nonce: u64,       // The previous nonce from the DB
    pub signature: Vec<u8>,
    /// Compact-SMT proof for this domain's slot. See `docs/compact-smt.md`.
    pub proof: Proof,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct BatchPayload {
    pub old_root: [u8; 32],
    pub end_block_height: u32,
    pub transactions: Vec<Transaction>,
}

/// The set of state-transition operations the protocol accepts.
///
/// The wire format carries the operation as a 3-byte string. Parsing it into this
/// enum once per transaction avoids repeating the same string comparisons across
/// the invariant, signature-construction and SMT-transition stages.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Op {
    Reg,
    Upd,
    Chg,
    Lst,
    Ult,
    Buy,
}

impl Op {
    /// Parses the wire-format operation code. An unrecognised code panics, which
    /// makes the whole batch unprovable.
    pub fn parse(op: &str, tx_id: &str) -> Self {
        match op {
            "REG" => Op::Reg,
            "UPD" => Op::Upd,
            "CHG" => Op::Chg,
            "LST" => Op::Lst,
            "ULT" => Op::Ult,
            "BUY" => Op::Buy,
            _ => panic!("CRITICAL: Unknown operation '{}' in TX {}", op, tx_id),
        }
    }

    /// The canonical operation code as it appears inside signed messages.
    pub fn as_bytes(self) -> &'static [u8] {
        match self {
            Op::Reg => b"REG",
            Op::Upd => b"UPD",
            Op::Chg => b"CHG",
            Op::Lst => b"LST",
            Op::Ult => b"ULT",
            Op::Buy => b"BUY",
        }
    }

    /// Whether this operation carries a caller-supplied `target_address`.
    ///
    /// Two consequences, which is why they share one predicate and cannot drift:
    ///
    /// * The signed message binds the address only for these operations.
    /// * Only these operations need to *validate* the address. For CHG/LST/ULT the
    ///   leaf's address is pinned by the expected old leaf, so the only value that
    ///   can satisfy the Merkle proof is one that REG/UPD/BUY already validated on
    ///   the way in. Re-validating would repeat a bech32m decode and base-32 expansion
    ///   for a value the proof has already pinned.
    ///
    /// The validation induction holds as long as the genesis root is the empty tree
    /// (or every pre-seeded leaf was validated out-of-band).
    pub fn binds_target_address(self) -> bool {
        matches!(self, Op::Reg | Op::Upd | Op::Buy)
    }

    /// Whether the signed message binds the price. Only listing a domain does.
    pub fn binds_price(self) -> bool {
        matches!(self, Op::Lst)
    }
}

// ---------------------------------------------------------------------------
// Signed message construction
// ---------------------------------------------------------------------------

/// Builds the exact byte string a domain owner signs for `op`.
///
/// Layout, with the optional segments present only for the operations whose
/// predicate says so:
///
/// ```text
/// <PREFIX><OP>:<domain>[:<target_address>]:<pubkey_hex>[:<price>]:<nonce>
/// ```
///
/// `pubkey_hex` is the 64-character lowercase hex encoding of `pubkey`, and the
/// integers are plain decimal with no padding.
pub fn signing_message(
    op: Op,
    domain: &str,
    target_address: &str,
    pubkey: &[u8; 32],
    price: u64,
    nonce: u64,
) -> Vec<u8> {
    let mut pubkey_hex = [0u8; 64];
    write_hex(&mut pubkey_hex, pubkey);

    let mut msg =
        Vec::with_capacity(MESSAGE_PREFIX.len() + 128 + domain.len() + target_address.len());

    msg.extend_from_slice(MESSAGE_PREFIX);
    msg.extend_from_slice(op.as_bytes());
    msg.push(b':');
    msg.extend_from_slice(domain.as_bytes());
    msg.push(b':');

    if op.binds_target_address() {
        msg.extend_from_slice(target_address.as_bytes());
        msg.push(b':');
    }

    msg.extend_from_slice(&pubkey_hex);
    msg.push(b':');

    if op.binds_price() {
        push_u64_bytes(&mut msg, price);
        msg.push(b':');
    }

    push_u64_bytes(&mut msg, nonce);

    msg
}

/// Verifies an Ed25519 signature using the STRICT verification equation.
///
/// `verify_strict` is used rather than `verify` because the latter accepts
/// small-order public keys. Ed25519 has 8 small-order points, and for a public key
/// `A` of order 4 the cofactorless equation `[S]B = R + [k]A` can be satisfied for
/// an arbitrary message by grinding `R` until `k = 0 (mod 4)` — a 1-in-4 hit, i.e.
/// a universal forgery. `verify_strict` rejects small-order `A` and `R`, and also
/// removes signature malleability.
#[cfg(feature = "signatures")]
pub fn is_signature_valid(pubkey: &VerifyingKey, message: &[u8], sig_bytes: &[u8]) -> bool {
    if let Ok(signature) = Signature::from_slice(sig_bytes) {
        return pubkey.verify_strict(message, &signature).is_ok();
    }
    false
}

// ---------------------------------------------------------------------------
// Sparse Merkle Tree
// ---------------------------------------------------------------------------

/// Hashes a domain's state into its SMT leaf value.
///
/// Note the leaf commits to the domain name itself, which is what stops a leaf from
/// being relocated to a different path in the tree.
pub fn hash_leaf(
    domain: &str,
    pubkey: &[u8; 32],
    target_address: &str,
    price: u64,
    nonce: u64,
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update([LEAF_TAG]);
    hasher.update(domain.as_bytes());
    hasher.update(pubkey);
    hasher.update(target_address.as_bytes());
    hasher.update(price.to_le_bytes());
    hasher.update(nonce.to_le_bytes());
    hasher.finalize().into()
}

/// Hashes an internal SMT node from its two children.
pub fn hash_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update([NODE_TAG]);
    hasher.update(left);
    hasher.update(right);
    hasher.finalize().into()
}

/// The 256-bit hash a domain's tree path is read from. Only the first 16 bytes are
/// consumed, giving a 128-bit path.
pub fn domain_path(domain: &str) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain.as_bytes());
    hasher.finalize().into()
}

// ---------------------------------------------------------------------------
// Input validation
// ---------------------------------------------------------------------------

// (Kerrigan target addresses are plain Sapling bech32m strings, so there is no multi-receiver
// container to unpack here — see `is_address_valid` below.)

#[cfg(feature = "validation")]
pub fn is_domain_valid(domain: &str) -> bool {
    let bytes = domain.as_bytes();
    if bytes.is_empty() || bytes.len() > 64 {
        return false;
    }

    if bytes.iter().filter(|&&b| b == b'.').count() != 1 {
        return false;
    }

    if bytes[0] == b'-' || domain.contains("--") {
        return false;
    }

    let mut split = domain.splitn(3, '.');
    let prefix = match split.next() {
        Some(p) => p,
        None => return false,
    };
    let zone = match split.next() {
        Some(z) => z,
        None => return false,
    };
    if split.next().is_some() {
        return false;
    }

    if prefix.is_empty() || prefix.as_bytes().last() == Some(&b'-') {
        return false;
    }

    if !prefix
        .bytes()
        .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
    {
        return false;
    }

    ALLOWED_ZONES.contains(&zone)
}

/// Validates a Kerrigan Sapling shielded payment address for the network this build targets.
///
/// Four independent things are checked, and all four matter:
///
/// 1. **Canonical lowercase.** Bech32m permits an all-uppercase encoding of the same
///    address. Two spellings of one address would hash to two different leaves, so the
///    tree would disagree with itself; the host enforces lowercase too.
/// 2. **The exact prefix for this build** — `ks` on mainnet, `ktestsapling` on testnet. A
///    testnet address can therefore never be registered against mainnet state, and vice
///    versa. The regtest and devnet forms are rejected on both.
/// 3. **The exact character length** (`EXPECTED_ADDRESS_LEN`), matching the host.
/// 4. **The decoded payload length** — 43 bytes. Length in characters and length in
///    bytes are not equivalent conditions: bech32m pads to 5-bit groups, so a payload of
///    43 bytes and one of 43 bytes plus a few stray bits can encode to the same number
///    of characters. Checking the decoded size closes that.
///
/// What is deliberately *not* checked is whether `pk_d` is a valid Jubjub curve point.
/// That would need unaccelerated field arithmetic inside the zkVM, and it only affects
/// whether the *owner* can be paid — never the integrity of the tree. No other part checks
/// it either: the indexer and the registrar apply these same four rules. An address with no
/// Sapling key behind it is refused only when somebody tries to pay it — a sender's wallet
/// for a name pointing at it, and the registrar's payouts, which isolate a withdrawal to
/// such an address rather than let it fail the payouts batched with it.
#[cfg(feature = "validation")]
pub fn is_address_valid(address: &str) -> bool {
    if address.len() != EXPECTED_ADDRESS_LEN {
        return false;
    }

    // Reject before decoding: bech32m's checksum accepts either case, so an uppercase
    // variant would otherwise decode successfully into the same payload.
    if address.bytes().any(|b| b.is_ascii_uppercase()) {
        return false;
    }

    match bech32::decode(address) {
        Ok((hrp, data, variant)) => {
            // Kerrigan Sapling addresses are bech32m, not bech32 (unlike Zcash's and PIVX's):
            // Kerrigan Core's DecodeSaplingAddress refuses the bech32 checksum. Accepting
            // both would let one address have two valid checksums.
            if variant != bech32::Variant::Bech32m || hrp != EXPECTED_HRP {
                return false;
            }
            match bech32::convert_bits(&data, 5, 8, false) {
                Ok(bytes) => bytes.len() == SAPLING_PAYLOAD_LEN,
                Err(_) => false,
            }
        }
        Err(_) => false,
    }
}

/// Whether a `Terminal::Blocked` record can be the preimage of a leaf in the tree.
///
/// [`hash_leaf`] concatenates `domain ‖ pubkey ‖ target_address` with no length prefixes,
/// so the bytes of one leaf can be cut into more than one record. Shift the boundary
/// between the domain and the pubkey — and with it the one between the pubkey and the
/// address — and the leaf hash stays the same while `record.domain`, and so the blocking
/// key, changes. That reopens the attack the full record exists to close
/// (`docs/compact-smt.md` §5.3): the prover picks the divergence bit, strands the blocking
/// domain's leaf off its own path, and can then prove that domain absent and register it
/// again.
///
/// Every leaf in the tree carries a valid domain (REG validates it) and a target address
/// of exactly [`EXPECTED_ADDRESS_LEN`] characters (REG, UPD and BUY validate it; CHG, LST
/// and ULT carry it over). Requiring the same of the record fixes the address length,
/// hence the domain length, hence the one way to cut the preimage. Both checks are cheap;
/// the full bech32m decode is not needed for this.
#[cfg(feature = "validation")]
pub fn is_blocking_record_valid(record: &LeafRecord) -> bool {
    record.target_address.len() == EXPECTED_ADDRESS_LEN && is_domain_valid(&record.domain)
}

// ---------------------------------------------------------------------------
// Byte helpers
// ---------------------------------------------------------------------------

/// Writes `bytes` into `buf` as lowercase hex. `buf` must be at least twice as long.
pub fn write_hex(buf: &mut [u8], bytes: &[u8]) {
    const HEX_CHARS: &[u8; 16] = b"0123456789abcdef";
    for (i, &b) in bytes.iter().enumerate() {
        buf[i * 2] = HEX_CHARS[(b >> 4) as usize];
        buf[i * 2 + 1] = HEX_CHARS[(b & 0xf) as usize];
    }
}

/// Appends `val` to `buf` as unpadded decimal digits.
pub fn push_u64_bytes(buf: &mut Vec<u8>, mut val: u64) {
    if val == 0 {
        buf.push(b'0');
        return;
    }
    let mut tmp = [0u8; 20];
    let mut idx = 20;
    while val > 0 {
        idx -= 1;
        tmp[idx] = b'0' + (val % 10) as u8;
        val /= 10;
    }
    buf.extend_from_slice(&tmp[idx..]);
}

// ---------------------------------------------------------------------------
// Golden vectors
// ---------------------------------------------------------------------------
//
// These pin the wire protocol. The expected values were computed by an INDEPENDENT
// reference implementation (Python/hashlib), not by running this code, so a change
// in behaviour here fails rather than silently redefining the protocol.
//
// A host implementation (the PHP backend, a wallet) should reproduce every value in
// this module. If it cannot, the two sides disagree and proofs will not verify.

#[cfg(test)]
mod tests {
    use super::*;

    const PK: [u8; 32] = [1u8; 32];
    /// Lowercase hex of [`PK`].
    const PK_HEX: &str =
        "0101010101010101010101010101010101010101010101010101010101010101";
    const DOMAIN: &str = "alice.krgn";
    const ADDR: &str = "ks1abcdef";

    fn hex(bytes: &[u8]) -> String {
        let mut buf = vec![0u8; bytes.len() * 2];
        write_hex(&mut buf, bytes);
        String::from_utf8(buf).unwrap()
    }

    // -- Hashing ------------------------------------------------------------

    #[test]
    fn domain_path_matches_reference() {
        assert_eq!(
            hex(&domain_path(DOMAIN)),
            "fbf0a43deee9bf66e4bf5415259f5cf438fcbec39b7372b720aa82eb09572038"
        );
    }

    #[test]
    fn hash_leaf_matches_reference() {
        assert_eq!(
            hex(&hash_leaf(DOMAIN, &PK, ADDR, 0, 1)),
            "a953f6e55dd1d86b4fbf809815030103d912dc03d576b161dffdba8ca1b7381e"
        );
    }

    /// The tags exist to keep the leaf and node hash domains disjoint. Feeding the
    /// same bytes through both must not collide.
    #[test]
    fn leaf_and_node_hash_domains_are_separated() {
        let zero = [0u8; 32];
        // A leaf whose preimage is all-zero fields vs. a node of two zero children.
        let leaf = hash_leaf("", &zero, "", 0, 0);
        let node = hash_node(&zero, &zero);
        assert_ne!(leaf, node);
        assert_ne!(LEAF_TAG, NODE_TAG);
    }

    #[test]
    fn distinct_domains_take_distinct_paths() {
        assert_ne!(domain_path("alice.krgn"), domain_path("bob.krgn"));
    }

    // -- Signed messages ----------------------------------------------------

    fn msg(op: Op, price: u64) -> String {
        String::from_utf8(signing_message(op, DOMAIN, ADDR, &PK, price, 42)).unwrap()
    }

    #[cfg(not(feature = "testnet"))]
    #[test]
    fn signed_messages_match_reference() {
        assert_eq!(msg(Op::Reg, 0), format!("KNS:1:REG:{DOMAIN}:{ADDR}:{PK_HEX}:42"));
        assert_eq!(msg(Op::Upd, 0), format!("KNS:1:UPD:{DOMAIN}:{ADDR}:{PK_HEX}:42"));
        assert_eq!(msg(Op::Chg, 0), format!("KNS:1:CHG:{DOMAIN}:{PK_HEX}:42"));
        assert_eq!(
            msg(Op::Lst, 100_000_000),
            format!("KNS:1:LST:{DOMAIN}:{PK_HEX}:100000000:42")
        );
        assert_eq!(msg(Op::Ult, 0), format!("KNS:1:ULT:{DOMAIN}:{PK_HEX}:42"));
        assert_eq!(msg(Op::Buy, 0), format!("KNS:1:BUY:{DOMAIN}:{ADDR}:{PK_HEX}:42"));
    }

    /// A testnet build must not produce a message a mainnet verifier would accept.
    #[cfg(feature = "testnet")]
    #[test]
    fn testnet_messages_use_a_distinct_prefix() {
        assert_eq!(msg(Op::Chg, 0), format!("tKNS:1:CHG:{DOMAIN}:{PK_HEX}:42"));
        assert!(msg(Op::Reg, 0).starts_with("tKNS:1:"));
    }

    /// Only LST binds a price, so changing the price must not disturb any other
    /// operation's message.
    #[test]
    fn only_lst_binds_price() {
        for op in [Op::Reg, Op::Upd, Op::Chg, Op::Ult, Op::Buy] {
            assert_eq!(msg(op, 0), msg(op, 999), "{op:?} must not bind price");
        }
        assert_ne!(msg(Op::Lst, 1), msg(Op::Lst, 2));
    }

    /// The operation code is inside the signed bytes, so a signature for one
    /// operation cannot be replayed as another.
    #[test]
    fn operations_have_distinct_messages() {
        let all = [Op::Reg, Op::Upd, Op::Chg, Op::Lst, Op::Ult, Op::Buy];
        for (i, a) in all.iter().enumerate() {
            for b in &all[i + 1..] {
                assert_ne!(msg(*a, 7), msg(*b, 7), "{a:?} vs {b:?}");
            }
        }
    }

    // -- Op parsing ---------------------------------------------------------

    #[test]
    fn op_parse_round_trips() {
        for op in [Op::Reg, Op::Upd, Op::Chg, Op::Lst, Op::Ult, Op::Buy] {
            let code = core::str::from_utf8(op.as_bytes()).unwrap();
            assert_eq!(Op::parse(code, "tx"), op);
        }
    }

    #[test]
    #[should_panic(expected = "Unknown operation")]
    fn op_parse_rejects_unknown() {
        Op::parse("XXX", "tx-1");
    }

    #[test]
    #[should_panic(expected = "Unknown operation")]
    fn op_parse_is_case_sensitive() {
        Op::parse("reg", "tx-1");
    }

    // -- Domain validation --------------------------------------------------

    #[cfg(feature = "validation")]
    #[test]
    fn accepts_valid_domains() {
        for d in [
            "a.krgn", "alice.kerrigan", "my-domain.private", "x1.secure", "0.safe",
            "a-b-c.krgn",
        ] {
            assert!(is_domain_valid(d), "{d} should be valid");
        }
    }

    #[cfg(feature = "validation")]
    #[test]
    fn rejects_invalid_domains() {
        for d in [
            "",                    // empty
            "alice",               // no zone
            "alice.com",           // unknown zone
            "alice.krgn.krgn",     // two dots
            "-alice.krgn",        // leading hyphen
            "alice-.krgn",        // trailing hyphen
            "al--ice.krgn",       // double hyphen (also blocks punycode)
            ".krgn",              // empty prefix
            "Alice.krgn",         // uppercase
            "ali ce.krgn",        // space
            "ali_ce.krgn",        // underscore
            "alicé.krgn",         // non-ascii
            "alice.KRGN",          // uppercase zone
            "alice.pivx",          // another coin's zone
        ] {
            assert!(!is_domain_valid(d), "{d} should be rejected");
        }
    }

    #[cfg(feature = "validation")]
    #[test]
    fn rejects_overlong_domains() {
        let long = format!("{}.krgn", "a".repeat(60)); // 60 + 5 = 65 bytes
        assert_eq!(long.len(), 65);
        assert!(!is_domain_valid(&long));

        let max = format!("{}.krgn", "a".repeat(59)); // exactly 64
        assert_eq!(max.len(), 64);
        assert!(is_domain_valid(&max));
    }

    #[cfg(feature = "validation")]
    #[test]
    fn every_allowed_zone_is_accepted() {
        for zone in ALLOWED_ZONES {
            assert!(is_domain_valid(&format!("test.{zone}")), "zone {zone}");
        }
    }

    // -- Address validation -------------------------------------------------
    //
    // Every address below is a real, checksum-valid Kerrigan Sapling address with a 43-byte
    // payload, made by Kerrigan Core v1.4.0 (`z_getnewaddress`), so a rejection can only come
    // from the policy under test and never from a malformed vector.

    /// Valid mainnet shielded address (`ks`, 78 chars).
    #[cfg(feature = "validation")]
    const MAINNET_ADDR: &str =
        "ks1npkydsxtk0gzhahlph73ryx7hxk7ee2wgsvvur4y8jrxrr7h5w95gjjzdk98ruxlnrajzyrkjgf";
    /// Valid testnet shielded address (`ktestsapling`, 88 chars).
    #[cfg(feature = "validation")]
    const TESTNET_ADDR: &str =
        "ktestsapling1y5p5wupyfwr5679l9u8m9w3lvgs3qdnn7yal5q8hd7fmekr6wsdcxelv4ddufdjygrq92rr29lx";
    /// Valid *regtest* address (`kregsapling`, 87 chars). Checksum is fine; the protocol
    /// rejects the form itself, on both networks.
    #[cfg(feature = "validation")]
    const REGTEST_ADDR: &str =
        "kregsapling1frurahjy20rh4j3mxwvj66623xx9l5wwx6ukcmjyx8ny05hy9lun5jx934na7nruv64puptalrm";
    /// [`MAINNET_ADDR`]'s payload under a bech32 checksum instead of bech32m. The checksum
    /// itself is valid, which is exactly why the variant has to be checked.
    #[cfg(all(feature = "validation", not(feature = "testnet")))]
    const MAINNET_ADDR_BECH32: &str =
        "ks1npkydsxtk0gzhahlph73ryx7hxk7ee2wgsvvur4y8jrxrr7h5w95gjjzdk98ruxlnrajz3lx7dt";

    /// The address this build is supposed to accept, and the one it must not.
    #[cfg(feature = "validation")]
    fn network_vectors() -> (&'static str, &'static str) {
        if cfg!(feature = "testnet") {
            (TESTNET_ADDR, MAINNET_ADDR)
        } else {
            (MAINNET_ADDR, TESTNET_ADDR)
        }
    }

    #[cfg(feature = "validation")]
    #[test]
    fn accepts_a_shielded_address_for_this_network() {
        let (ours, _) = network_vectors();
        assert!(is_address_valid(ours), "{ours} should be accepted");
        assert_eq!(ours.len(), EXPECTED_ADDRESS_LEN);
        assert!(ours.starts_with(EXPECTED_HRP));
    }

    /// The whole point of the compile-time split: a staging address must be unusable
    /// against mainnet state and vice versa.
    #[cfg(feature = "validation")]
    #[test]
    fn rejects_a_shielded_address_from_the_other_network() {
        let (_, theirs) = network_vectors();
        assert!(!is_address_valid(theirs), "{theirs} is the wrong network");
    }

    /// Deliberate policy: the regtest form is not accepted on either network.
    #[cfg(feature = "validation")]
    #[test]
    fn rejects_the_regtest_address_form() {
        assert!(!is_address_valid(REGTEST_ADDR));
    }

    /// Kerrigan Core accepts only the bech32m checksum for a Sapling address. The bech32
    /// spelling of the same payload must be refused too, or one address would have two
    /// spellings, hashing to two different leaves.
    #[cfg(all(feature = "validation", not(feature = "testnet")))]
    #[test]
    fn rejects_the_bech32_checksum_of_a_valid_payload() {
        assert!(is_address_valid(MAINNET_ADDR));
        assert_eq!(MAINNET_ADDR_BECH32.len(), MAINNET_ADDR.len());
        assert!(!is_address_valid(MAINNET_ADDR_BECH32));
    }

    /// Bech32m checksums are case-insensitive, so the uppercase spelling of an accepted
    /// address decodes to the same payload. It must still be refused: two spellings of
    /// one address would hash to two different leaves.
    #[cfg(feature = "validation")]
    #[test]
    fn rejects_the_uppercase_spelling_of_a_valid_address() {
        let (ours, _) = network_vectors();
        assert!(is_address_valid(ours));
        assert!(!is_address_valid(&ours.to_uppercase()));
    }

    #[cfg(feature = "validation")]
    #[test]
    fn rejects_a_corrupted_checksum() {
        let (ours, _) = network_vectors();
        let mut bad = ours.to_string();
        // Flip the final character to a different bech32m charset member.
        let last = bad.pop().unwrap();
        bad.push(if last == 'q' { 'p' } else { 'q' });
        assert_eq!(bad.len(), ours.len(), "length must be unchanged");
        assert!(!is_address_valid(&bad), "corrupted checksum must be rejected");
    }

    #[cfg(feature = "validation")]
    #[test]
    fn rejects_malformed_and_foreign_addresses() {
        let (ours, _) = network_vectors();
        let truncated = &ours[..ours.len() - 1];
        for a in [
            "",
            "not-an-address",
            "1",
            truncated,
            // Kerrigan transparent address: not shielded, and not bech32m at all.
            "KSvgmrG5YH1yXqRx99XzXphsvkQXpjdFxK",
            // Correct shape, wrong coin: a PIVX and a Zcash Sapling address (bech32).
            "ps10ayxgy96kzhzwe0mtd53lraj4hxsu9scyh730vwxna0ul2yxw2pwxvdceu8tajd40fhvkmx3dyz",
            "zs1z7rejlpsa98s2rrrfkwmaxu53e4ue0ulcrw0h4x5g8jl04tak0d3mm47vdtahatqrlkngh9sly",
            // Right prefix, no separator or data.
            EXPECTED_HRP,
        ] {
            assert!(!is_address_valid(a), "{a:?} should be rejected");
        }
    }

    /// The derived constant must equal the hand-computed value for both builds; getting
    /// this wrong would silently accept or refuse every address.
    #[cfg(feature = "validation")]
    #[test]
    fn expected_address_length_matches_the_network() {
        if cfg!(feature = "testnet") {
            assert_eq!(EXPECTED_HRP, "ktestsapling");
            assert_eq!(EXPECTED_ADDRESS_LEN, 88);
        } else {
            assert_eq!(EXPECTED_HRP, "ks");
            assert_eq!(EXPECTED_ADDRESS_LEN, 78);
        }
    }

    // -- Blocking records ---------------------------------------------------

    /// The leaf preimage concatenates variable-length fields, so a real leaf's bytes can be
    /// re-cut into another record with the same hash but a different domain — and so a
    /// different blocking key. The guard must accept the real cut and refuse the other.
    #[cfg(feature = "validation")]
    #[test]
    fn a_recut_blocking_record_hashes_the_same_but_is_refused() {
        let (ours, _) = network_vectors();
        let mut pubkey = [7u8; 32];
        // An ASCII last byte, so the address side of the re-cut is still valid UTF-8.
        pubkey[31] = b'q';
        let real = LeafRecord {
            domain: DOMAIN.into(),
            pubkey,
            target_address: ours.into(),
            price: 0,
            nonce: 42,
        };

        // The domain's last byte moves into the pubkey, the pubkey's last into the address.
        let mut recut_pubkey = [0u8; 32];
        recut_pubkey[0] = *DOMAIN.as_bytes().last().unwrap();
        recut_pubkey[1..].copy_from_slice(&pubkey[..31]);
        let recut = LeafRecord {
            domain: DOMAIN[..DOMAIN.len() - 1].into(),
            pubkey: recut_pubkey,
            target_address: format!("q{ours}"),
            price: 0,
            nonce: 42,
        };

        assert_eq!(recut.leaf(), real.leaf(), "the re-cut must be the same preimage");
        assert_ne!(key_of(&recut.domain), key_of(&real.domain), "yet name another key");
        assert!(is_blocking_record_valid(&real));
        assert!(!is_blocking_record_valid(&recut));
    }
}

// ---------------------------------------------------------------------------
// Cross-implementation address corpus
// ---------------------------------------------------------------------------
//
// Reads a corpus of addresses with expected verdicts and checks `is_address_valid`
// against every one. The corpus and its verdicts are produced independently (see
// `docs/reference/gen_addr_corpus.py`), and the PHP indexer is checked against the same
// file — so host and guest disagreeing about which addresses are acceptable fails a test
// here instead of producing a batch the indexer queues and the prover cannot prove.
//
// Runs by default: the path is resolved through CARGO_MANIFEST_DIR against the committed
// fixture, so it needs no setup, and ADDR_CORPUS overrides it when validating a freshly
// generated corpus.
#[cfg(all(test, feature = "validation"))]
mod address_corpus {
    use super::*;

    #[test]
    fn matches_the_reference_corpus() {
        // Defaults to the fixture committed beside the generator, so the check runs with
        // no setup; ADDR_CORPUS overrides it when validating a freshly generated corpus.
        let path = std::env::var("ADDR_CORPUS").unwrap_or_else(|_| {
            concat!(env!("CARGO_MANIFEST_DIR"), "/../docs/reference/fixtures/addr_corpus.json")
                .to_string()
        });
        let raw = std::fs::read_to_string(&path).expect("corpus is readable");

        let net_key = if cfg!(feature = "testnet") { "\"testnet\"" } else { "\"mainnet\"" };
        let mut checked = 0usize;
        let mut failures = Vec::new();

        // Minimal field extraction rather than a JSON dependency: the corpus is emitted by
        // our own generator with one object per line group, so the shape is known.
        for entry in raw.split("\"addr\":").skip(1) {
            let addr = entry
                .split('"')
                .nth(1)
                .expect("addr value")
                .replace("\\\\", "\\");
            let want = entry
                .split(net_key)
                .nth(1)
                .and_then(|t| t.split(',').next())
                .map(|t| t.contains("true"))
                .expect("verdict for this network");

            let got = is_address_valid(&addr);
            if got != want {
                failures.push(format!("{addr:?}: expected {want}, got {got}"));
            }
            checked += 1;
        }

        assert!(checked > 0, "corpus produced no cases");
        assert!(
            failures.is_empty(),
            "{} of {checked} cases disagree with the reference:\n{}",
            failures.len(),
            failures.join("\n")
        );
        eprintln!("  {checked} corpus cases agree ({})", if cfg!(feature = "testnet") { "testnet" } else { "mainnet" });
    }
}

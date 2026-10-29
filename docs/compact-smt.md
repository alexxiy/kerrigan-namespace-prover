# Compact Sparse Merkle Tree — Protocol Specification

Status: **specified and validated against a reference implementation; Rust not yet
written.** This document is the shared contract between `kns-core` (which will
implement it), `kerrigan-name-rr-proxy` (which builds the tree and emits proofs), the SP1
guest circuit (which verifies them) and the PHP client (which forwards them).

Implement from this document, not from either codebase, and keep them in step.

**Before changing anything here, run the reference implementation:**

```bash
python3 docs/reference/csmt_reference.py
```

`docs/reference/csmt_reference.py` is an independent implementation of this document
(not a port of the Rust). It computes the canonical root declaratively from the key set
per §2.1 and asserts that the incremental algorithm of §4 agrees with it, so the two
cross-check. It also carries the §7 adversarial suite. Every claim below is checked
there rather than merely argued — including §5.3, whose attack it demonstrates
succeeding against an unsound verifier before showing the specified one rejects it.

Current result: 250 registrations agree with canonical form, every leaf remains
provable, mean leaf depth 9.4 (max 18) giving ~19 node hashes/tx against 256 —
**13.6× at that size** — and all 11 adversarial cases are rejected.

---

## 1. Why

The current tree is 128 levels deep and every leaf sits at depth 128, so every
transaction walks all 128 levels twice (once to verify the old root, once to derive
the new one). That is **256 node hashes ≈ 512 SHA-256 compressions per transaction**,
and it dominates proving cost.

Almost all of that work is re-deriving constants. With `N` domains, a leaf's path
diverges from every other key within ~`log₂(N)` levels of the root; below that point
every sibling is an empty-subtree constant carrying no information.

| N domains | E[leaf depth] | node hashes/tx | vs 256 | proof bytes |
|----------:|--------------:|---------------:|-------:|------------:|
| 1,000 | 11.3 | 23 | 11.3× | 361 |
| 10,000 | 14.6 | 29 | 8.8× | 468 |
| 100,000 | 17.9 | 36 | 7.1× | 574 |
| 1,000,000 | 21.3 | 43 | 6.0× | 680 |
| 10,000,000 | 24.6 | 49 | 5.2× | 787 |

Two secondary wins. Proof payloads drop from 4096 to ~500 bytes, which matters
because a measured run spent **~130k cycles/tx just deserialising** the 128×32-byte
proofs. And the daemon stops writing a 129-node spine on every update, writing
~`log₂(N)` nodes instead.

---

## 2. Definitions

**Key.** `key(domain) = SHA256(domain)[..16]` — 128 bits, unchanged. Bit `i` of the
key is bit `i` of the path, most-significant-bit first within each byte:
`key[i/8] >> (7 - i%8) & 1`. Path bit `0` selects the left child.

**Depth.** A node at depth `i` is reached by consuming path bits `key[0..i]`. The root
is at depth 0. `MAX_DEPTH = 128`.

**Node kinds and their hashes:**

| Kind | Hash |
|:---|:---|
| `Empty` | `[0u8; 32]` — a single reserved constant at every depth |
| `Leaf` | `hash_leaf(domain, pubkey, target_address, price, nonce)` (unchanged) |
| `Internal(L, R)` | `hash_node(L, R)` = `SHA256(0x01 ‖ L ‖ R)` (unchanged) |

> **The empty-subtree ladder is deleted.** There is no `E[i]` chain any more —
> `empty_subtree_roots()` goes away, along with the daemon's `default_hashes`. An
> empty subtree is `[0u8; 32]` regardless of height. The root of an empty tree is
> therefore `[0u8; 32]`, not `9c337c9f…`.

> **Domain-separation tags become load-bearing.** In the dense tree, `LEAF_TAG` /
> `NODE_TAG` were defence-in-depth: leaf/node confusion was infeasible only because
> a valid Sapling address made a 64-byte leaf preimage impossible. Here a **leaf hash
> legitimately appears at internal positions**, so the tags are the only thing
> separating "a leaf sits here" from "a subtree sits here". They are mandatory.

### 2.1 Canonical form

Every subtree is determined by the set of keys it contains:

| Keys in subtree | Representation |
|---:|:---|
| 0 | `Empty` |
| 1 | that `Leaf`, placed at this depth |
| ≥2 | `Internal(L, R)`, where `L`/`R` are the representations of the two halves |

Consequences worth stating explicitly, because they are what the tests check:

- A leaf sits at the **shallowest depth at which it is the only key in its subtree**.
- `Internal(Leaf, Empty)` and `Internal(Empty, Leaf)` are **invalid** — one key means
  the subtree *is* that leaf.
- `Internal(Empty, Empty)` is invalid — zero keys means `Empty`.
- `Internal(x, Empty)` with `x` internal **is** valid, and occurs when ≥2 keys share
  more prefix bits than the branch above them.
- A one-leaf tree has `root = that leaf's hash`, at depth 0.

The representation is a deterministic function of the key set, so **the root is
canonical**: there is exactly one valid root per set of domain records. The daemon and
the circuit cannot disagree about structure.

---

## 3. Proof format

```
Proof {
    depth:    u8,                 // d, 0..=128
    siblings: [Hash; d],          // deepest first: siblings[i] is at depth d - i
    terminal: Terminal,
}

Terminal =
  | Occupied                      // the key's own leaf is at depth d (inclusion)
  | Vacant                        // Empty is at depth d
  | Blocked { record: LeafRecord } // a DIFFERENT leaf is at depth d
```

`LeafRecord` is the **full leaf preimage** of the blocking domain:

```
LeafRecord { domain: String, pubkey: [u8;32], target_address: String, price: u64, nonce: u64 }
```

Section 5.3 explains why the full preimage is required and why supplying only the
blocking key would be unsound.

`siblings` has exactly `depth` entries. Folding from depth `d` to the root consumes
the siblings at depths `d, d-1, …, 1`, so step `i` uses `siblings[i]` and path bit
`key[d-1-i]`.

---

## 4. Verification

### 4.1 Folding (shared by every case)

```
fn fold(key, start_hash, siblings) -> Hash:
    h = start_hash
    for i in 0..siblings.len():
        bit = key_bit(key, siblings.len() - 1 - i)
        h = if bit { hash_node(siblings[i], h) } else { hash_node(h, siblings[i]) }
    return h
```

### 4.2 Inclusion — `UPD`, `CHG`, `LST`, `ULT`, `BUY`

```
require terminal == Occupied
require d <= MAX_DEPTH
old_leaf = hash_leaf(<expected old state, exactly as today>)
require fold(key, old_leaf, siblings) == current_root
new_leaf = hash_leaf(<new state, exactly as today>)
new_root = fold(key, new_leaf, siblings)
```

The key set does not change, so the structure does not change: the new leaf replaces
the old at the **same depth `d` with the same siblings**. This is exactly today's
algorithm with `d` in place of 128.

### 4.3 Registration into a vacant slot — `REG`, `Terminal::Vacant`

```
require d <= MAX_DEPTH
require fold(key, EMPTY, siblings) == current_root      // proves absence
new_leaf = hash_leaf(<new state>)
new_root = fold(key, new_leaf, siblings)
```

Inserting one key into an empty subtree makes it a one-key subtree, so the leaf is
placed at depth `d`, replacing the `Empty`. Also the empty-tree case: `d = 0`,
`siblings = []`, `current_root = EMPTY`, and `new_root = new_leaf`.

### 4.4 Registration into a blocked slot — `REG`, `Terminal::Blocked`

```
require d < MAX_DEPTH
blocking_leaf = hash_leaf(record.domain, record.pubkey, record.target_address,
                          record.price, record.nonce)          // binds record to hash
blocking_key  = key(record.domain)                             // binds record to key

require blocking_key != key                                    // else it is an inclusion
require shares_prefix(blocking_key, key, d)                     // it really is on our path
require fold(key, blocking_leaf, siblings) == current_root      // proves absence

j = first index >= d where key[j] != blocking_key[j]
require j < MAX_DEPTH                                          // no full 128-bit collision

// Split: both keys agree on bits [d, j) and diverge at bit j.
new_leaf = hash_leaf(<new state>)
node = if key_bit(key, j) { hash_node(blocking_leaf, new_leaf) }
       else               { hash_node(new_leaf, blocking_leaf) }     // depth j
for i in (d..j).rev():                                               // chain, depths j-1..d
    node = if key_bit(key, i) { hash_node(EMPTY, node) }
           else               { hash_node(node, EMPTY) }
new_root = fold(key, node, siblings)
```

`j - d` is geometrically distributed with a small mean, so the chain is short. Total
internals created: `j - d + 1`.

Because there is **no deletion in this protocol** (confirmed: domains never expire and
are never removed), leaves only ever move *deeper*. There is no un-splitting or
subtree-collapse path to implement or attack — this is the single biggest
simplification in the design.

---

## 5. Soundness

The property that must hold: **an attacker who controls the batch payload cannot
produce a `new_root` that is not the canonical root of a valid tree reachable from
`current_root` by the operation they signed for.**

### 5.1 Forged inclusion / absence

Every case ends in `fold(...) == current_root`. Folding is iterated SHA-256 over
tagged, fixed-width inputs, so producing a match for a hash not genuinely at that
position requires a collision. This also makes `d` self-authenticating: a wrong depth
folds a different number of times and yields a different root.

### 5.2 Leaf relocation

`hash_leaf` commits to the domain name, hence to the key, hence to the path. A leaf
cannot be moved to a path that does not match its own domain, because the fold is
performed along `key(domain)`'s bits.

### 5.3 The blocking-key attack — why the full preimage is required

An earlier draft of this design put only the blocking **key** (16 bytes) in
`Terminal::Blocked`. That is unsound, and it is the subtlest part of the design.

The circuit uses `blocking_key` for exactly one consequential thing: computing the
divergence bit `j`, which determines **where the blocking leaf is placed** in the new
subtree. With only a claimed key, an attacker registering `X` can present the genuine
`blocking_leaf` hash of some existing domain `Y` while *lying* about its key — any
value that shares `d` bits with `key(X)` and differs somewhere passes both checks. The
fold still reproduces `current_root`, because the fold never consults the claimed key.
But `j` is then wrong, and the circuit builds a subtree placing `Y`'s leaf at a
position that does not match `key(Y)`.

The result is a valid proof committing a root in which `Y` is unreachable: any future
inclusion proof for `Y` must fold along `key(Y)`, and `Y`'s leaf is no longer there.
**Any domain could be permanently bricked by registering a name that shares a prefix with it.**
Nor does it stop there. With `Y`'s leaf moved off `key(Y)`'s path, the slot that path
now ends in is empty, so a *non-inclusion* proof for `Y` verifies — and a `REG` of `Y`,
under any key, is provable. Stranding is the first step of a hijack, not just a denial
of service.

Carrying the full preimage closes it: the circuit recomputes `blocking_leaf` from the
record and derives `blocking_key` from the same `record.domain`, so the hash that gets
folded and the key that determines `j` are bound to one another. An attacker wanting a
favourable `j` must alter `record.domain`, which changes `blocking_leaf`, which breaks
the fold against `current_root`.

This is not a theoretical worry — `docs/reference/csmt_reference.py` carries it out. In
a 250-domain tree it registers a name blocked at depth 8, lies that the blocking key
diverges at bit 127 instead of bit 8, and the unsound verifier accepts, yielding a root
under which the blocking domain's own inclusion proof no longer verifies. The specified
verifier rejects the same attempt with *blocking key not on our path*.

Binding `record.domain` to `blocking_leaf` this way holds only if no two records hash to
the same leaf, and `hash_leaf` alone does not promise it: it concatenates `domain ‖ pubkey ‖ target_address` with no length
prefixes. Shift the boundary between the domain and the pubkey — the pubkey is fixed
width, so the boundary with the address shifts with it — and the same bytes make a
record with another `domain`, another key and the same leaf hash. Only the cuts whose
domain and address are valid UTF-8 are usable, so a given leaf offers about one or two,
each with a `2^-d` chance of sharing its first `d` bits with the leaf's own key. Summed
over the tree (Σ 2^-d over the leaves is at most 1) that leaves about one exploitable
leaf at any size — a victim of the prover's finding rather than choosing, but one that is
always there.

The circuit therefore also requires the record to be cut the way every leaf in the tree
is: a valid domain, and a target address of exactly `EXPECTED_ADDRESS_LEN` characters
(`kns_core::is_blocking_record_valid`). Every leaf satisfies both — `REG` validates the
domain, and `REG`, `UPD` and `BUY` the address, which the other operations carry over — and
a fixed address length fixes the domain length, so exactly one cut remains. The leaf
format itself is unchanged; restructuring it with length prefixes would have changed every
leaf hash and forced the tree to be rebuilt.

Cost: one extra `hash_leaf` plus one `SHA256(domain)` on `REG`-into-blocked only —
about 4 compressions against a saving of ~460.

**Rejected alternative.** Restructuring the leaf as
`hash_leaf = H(LEAF_TAG ‖ key ‖ H(BODY_TAG ‖ fields…))` would let the proof carry
`(key, body_hash)` — 48 bytes, one hash to bind. It was rejected because it adds a
hash to *every* leaf computation in *every* operation to save a few compressions on
one branch of one operation.

### 5.4 Non-canonical structures

A malicious `Terminal::Blocked` cannot smuggle in an invalid shape: the split is
*constructed* by the circuit from `key`, `blocking_key` and `j`, never supplied. The
construction yields `Internal(Leaf, Leaf)` at depth `j` and `Internal(internal, Empty)`
above it, both valid per §2.1. The circuit never accepts a caller-provided subtree.

### 5.5 Key collisions

Two domains with identical 128-bit keys cannot both be registered: §4.4 requires
`j < 128`, so the second registration is unprovable and the name is permanently
unregisterable. Finding such a pair costs ~2⁶⁴ work (birthday), and hitting a
*specific* target name costs ~2¹²⁸. A collision is a denial of service on one name,
never a theft, because the leaf commits to the domain.

---

## 6. What changes where

### `kns-core`
- Delete `empty_subtree_roots`, add `const EMPTY: Hash = [0u8; 32]`.
- Replace `smt_roots` with the four cases of §4. Suggested shape:
  `fn verify_and_apply(key, proof, old_leaf: Option<Hash>, new_leaf) -> (Hash, Hash)`
  returning `(reconstructed_old_root, new_root)` and leaving the equality assertion to
  the caller, as `smt_roots` does today.
- Add `Proof` / `Terminal` / `LeafRecord` types with serde, and `key(domain)`,
  `key_bit`, `shares_prefix`, `first_divergence`.
- `SMT_DEPTH` becomes `MAX_DEPTH`, still 128, now a bound rather than the exact length.

### SP1 guest (`program`)
- `merkle_proof: Vec<[u8;32]>` on `Transaction` becomes the `Proof` struct.
- `REG` no longer passes `[0u8; 32]` as the expected old leaf; it passes `None` and the
  terminal decides between §4.3 and §4.4.
- Everything else — nonce checks, per-op invariants, signature verification — is
  untouched.

### `kerrigan-name-rr-proxy`
- `Smt::default_hashes` and the ladder go away.
- `update` becomes an insert honouring §2.1: descend to the terminal, and on a blocked
  slot **delete the node at depth `d`** and write the split chain (the store already has
  tombstone support). Writes ~`log₂(N)` nodes instead of 129.
- `proof` returns the §3 structure, needing the terminal's record on a blocked slot.
- The `NodeKey` scheme (`[depth][packed prefix]`) is unchanged and still correct.
- Keep `agrees_with_prover_traversal` calling `kns_core` directly.

> **The daemon must now persist full leaf records, which it does not today.**
>
> This falls out of §5.3: a `Terminal::Blocked` proof carries the blocking domain's
> entire preimage, so the daemon has to be able to answer "which record occupies this
> position?" It currently stores only 32-byte hashes — `OP_SMT_UPDATE` receives the
> record fields, hashes them and discards the originals.
>
> Records cannot simply live at the leaf's node key, because a split **moves** a leaf
> deeper and the key would move with it. Keying them by domain (or by the 128-bit tree
> key, which is derived from it and fixed for the life of the domain) keeps them stable
> across splits. Storage grows by roughly one record per domain — small next to the
> ~2N node hashes, and the split already deletes and rewrites node entries, so the
> record store is the one part that stays put.

### PHP client
- `RustRocksDBProxy::PROOF_DEPTH = 128` → `MAX_PROOF_DEPTH`, and the exact-length
  assertion in `smtProof()` (`32 * (1 + 128)`) must become a structural parse:
  root, depth, terminal tag, `depth` siblings, optional record.
- `SparseMerkleTree::getProof()` / `getProofWithRoot()` return the richer shape.
- PHP still hashes nothing.

---

## 7. Test plan

All of the following already pass in `docs/reference/csmt_reference.py`; the Rust must
reproduce them, with golden vectors taken from that script so `kns-core`'s tests
cross-check rather than restate the implementation:

- Empty tree: `root == EMPTY`; `REG` at `d=0` gives `root == leaf`.
- One-leaf tree: inclusion with `d=0`, `siblings=[]`.
- Canonical form: building the same key set in different insertion orders yields one
  root (the daemon already has `update_order_does_not_affect_the_root`).
- Depth: with `N` random keys, every leaf is at the shallowest unique-prefix depth.
- Split: `j == d` (immediate divergence) and `j > d` (chain), including `j = d + 1`.

Adversarial tests, each of which **must fail verification**:

- Inclusion proof with `depth` off by one, in each direction.
- `Terminal::Vacant` for a key that is present.
- `Terminal::Blocked` whose `record` hashes to a leaf not at that position.
- **`Terminal::Blocked` whose `record.domain` does not share `d` bits with the
  registered key** — the §5.3 attack, and the single most important test here.
- `Terminal::Blocked` where `record.domain == domain` (should be inclusion).
- `Terminal::Occupied` for an absent key.
- `siblings.len() != depth`.
- `depth > 128`.
- A caller-supplied subtree in place of the constructed split (should be
  unrepresentable in the wire type — assert it at the type level if possible).

---

## 8. Migration

Pre-launch, with no registered domains, so this is a
resync rather than a migration:

1. Land `kns-core`, guest and daemon together — they share the crate, so a mismatch is
   a compile error rather than a silent root divergence.
2. Update the PHP proof parsing.
3. Wipe the databases (`OP_CLEAR`) and resync from chain data.
4. Register the new vKey in the anchor contract.

**Do this in the same window as the domain-separation tags.** Those already changed the
empty-tree root from `b4c9dacf…` to `9c337c9f…`; this change makes it `0x00…00`. There
is no reason for the intermediate value to ever be deployed, and one resync is enough
for both.

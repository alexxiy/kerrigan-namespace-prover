#!/usr/bin/env python3
"""Independent reference implementation of ../compact-smt.md.

Purpose
-------
This is deliberately NOT a port of the Rust. It is a second, independent
implementation used to:

  1. validate the specification before the Rust was written,
  2. generate golden vectors for `kns-core`'s tests, so those tests cross-check
     rather than restate the implementation they cover,
  3. demonstrate the section 5.3 attack, so the reason the non-inclusion proof
     carries a full leaf preimage is reproducible rather than merely argued.

`Tree.root()` recomputes the canonical form from the key set per section 2.1,
independently of the incremental insert path in `verify_and_apply`. Every test
asserting `verify_and_apply(...) == tree.root()` is therefore a genuine check
that the incremental algorithm agrees with the declarative definition.

Run: python3 csmt_reference.py
"""
import hashlib
import statistics

LEAF_TAG, NODE_TAG = b"\x00", b"\x01"
EMPTY = bytes(32)
MAX_DEPTH = 128


# --------------------------------------------------------------------- hashing

def hash_leaf(domain, pubkey, addr, price, nonce):
    h = hashlib.sha256()
    h.update(LEAF_TAG)
    h.update(domain.encode())
    h.update(pubkey)
    h.update(addr.encode())
    h.update(price.to_bytes(8, "little"))
    h.update(nonce.to_bytes(8, "little"))
    return h.digest()


def hash_node(left, right):
    h = hashlib.sha256()
    h.update(NODE_TAG)
    h.update(left)
    h.update(right)
    return h.digest()


def key_of(domain):
    return hashlib.sha256(domain.encode()).digest()[:16]


def bits(key):
    """Path bits, most-significant-bit first within each byte."""
    return [(key[i // 8] >> (7 - i % 8)) & 1 for i in range(MAX_DEPTH)]


def shares_prefix(a, b, d):
    return a[:d] == b[:d]


# ------------------------------------------------------------ canonical tree

class Tree:
    """Domain records: domain -> (pubkey, target_address, price, nonce)."""

    def __init__(self):
        self.rec = {}

    def leaf(self, domain):
        return hash_leaf(domain, *self.rec[domain])

    def _index(self):
        return {dom: bits(key_of(dom)) for dom in self.rec}

    def _in(self, prefix):
        d = len(prefix)
        idx = getattr(self, "_idx", None) or self._index()
        return [dom for dom, b in idx.items() if b[:d] == list(prefix)]

    def root(self, prefix=()):
        """Canonical root, derived from the key set per spec 2.1."""
        self._idx = self._index()
        return self._root(sorted(self._in(list(prefix))), list(prefix))

    def _root(self, ks, prefix):
        if len(ks) == 0:
            return EMPTY
        if len(ks) == 1:
            return self.leaf(ks[0])
        d = len(prefix)
        left = [k for k in ks if self._idx[k][d] == 0]
        right = [k for k in ks if self._idx[k][d] == 1]
        return hash_node(self._root(left, prefix + [0]), self._root(right, prefix + [1]))

    def proof(self, domain):
        """(depth, siblings deepest-first, terminal) per spec 3."""
        kb = bits(key_of(domain))
        sibs, d = [], 0
        while len(self._in(kb[:d])) > 1:
            sibs.append(self.root(tuple(kb[:d]) + (1 - kb[d],)))
            d += 1
        ks = self._in(kb[:d])
        if len(ks) == 0:
            terminal = ("Vacant", None)
        elif ks[0] == domain:
            terminal = ("Occupied", None)
        else:
            terminal = ("Blocked", ks[0])
        return d, list(reversed(sibs)), terminal


# ---------------------------------------------------------------- verifier

def fold(kb, start, sibs):
    """Spec 4.1."""
    h, n = start, len(sibs)
    for i in range(n):
        bit = kb[n - 1 - i]
        h = hash_node(sibs[i], h) if bit else hash_node(h, sibs[i])
    return h


def verify_and_apply(domain, proof, cur_root, old_leaf, new_leaf, blocking_rec=None):
    """Spec 4.2-4.4. Returns new_root or raises ValueError.

    `old_leaf` is None for REG (which requires a non-inclusion terminal).
    """
    d, sibs, (kind, _) = proof
    if len(sibs) != d:
        raise ValueError("siblings.len() != depth")
    if d > MAX_DEPTH:
        raise ValueError("depth > MAX_DEPTH")
    kb = bits(key_of(domain))

    # 4.2 inclusion
    if kind == "Occupied":
        if old_leaf is None:
            raise ValueError("REG requires a non-inclusion terminal")
        if fold(kb, old_leaf, sibs) != cur_root:
            raise ValueError("old root mismatch")
        return fold(kb, new_leaf, sibs)

    if old_leaf is not None:
        raise ValueError("update requires an Occupied terminal")

    # 4.3 vacant
    if kind == "Vacant":
        if fold(kb, EMPTY, sibs) != cur_root:
            raise ValueError("absence proof failed")
        return fold(kb, new_leaf, sibs)

    # 4.4 blocked
    if d >= MAX_DEPTH:
        raise ValueError("blocked at max depth implies a full key collision")
    bdom, bpk, baddr, bprice, bnonce = blocking_rec
    # The full preimage binds the folded hash and the key that determines j to
    # one another. See spec 5.3 -- omitting this is exploitable.
    blocking_leaf = hash_leaf(bdom, bpk, baddr, bprice, bnonce)
    bkey = key_of(bdom)
    if bkey == key_of(domain):
        raise ValueError("blocking key equals ours; that is inclusion")
    if not shares_prefix(bits(bkey), kb, d):
        raise ValueError("blocking key not on our path")
    if fold(kb, blocking_leaf, sibs) != cur_root:
        raise ValueError("absence proof failed")

    bb = bits(bkey)
    j = next((i for i in range(d, MAX_DEPTH) if kb[i] != bb[i]), None)
    if j is None:
        raise ValueError("full 128-bit key collision")

    node = hash_node(blocking_leaf, new_leaf) if kb[j] else hash_node(new_leaf, blocking_leaf)
    for i in range(j - 1, d - 1, -1):
        node = hash_node(EMPTY, node) if kb[i] else hash_node(node, EMPTY)
    return fold(kb, node, sibs)


# ---------------------------------------------------------------- validation

PK = bytes([1] * 32)


def _rec(n=1):
    return (PK, "u1abc", 0, n)


def _ok(label, cond):
    print(("  PASS  " if cond else "  FAIL  ") + label)
    assert cond, label


def _rejects(label, fn):
    try:
        fn()
    except ValueError as e:
        print(f"  PASS (rejected: {str(e)[:44]})  {label}")
        return
    raise AssertionError(f"ACCEPTED an invalid proof: {label}")


def _reg(t, root, dom):
    """Register `dom`, asserting the result matches the canonical root."""
    pr = t.proof(dom)
    kind, blocker = pr[2]
    brec = ((blocker,) + t.rec[blocker]) if kind == "Blocked" else None
    new_root = verify_and_apply(dom, pr, root, None, hash_leaf(dom, *_rec()), blocking_rec=brec)
    t.rec[dom] = _rec()
    assert new_root == t.root(), f"{dom}: incremental root != canonical root"
    return new_root, kind


def main():
    print("=== empty tree and first registration ===")
    t = Tree()
    _ok("empty tree root == EMPTY", t.root() == EMPTY)
    pr = t.proof("alice.krgn")
    _ok("depth 0, Vacant", pr[0] == 0 and pr[2][0] == "Vacant")
    root, _ = _reg(t, t.root(), "alice.krgn")
    _ok("one-leaf tree root == that leaf", root == t.leaf("alice.krgn"))

    print("=== inclusion at depth 0 ===")
    pr = t.proof("alice.krgn")
    _ok("Occupied at depth 0", pr[0] == 0 and pr[2][0] == "Occupied")
    nl = hash_leaf("alice.krgn", *_rec(2))
    nr = verify_and_apply("alice.krgn", pr, root, t.leaf("alice.krgn"), nl)
    t.rec["alice.krgn"] = _rec(2)
    _ok("update matches canonical root", nr == t.root())
    root = nr

    print("=== registration into a blocked slot (the split) ===")
    _ok("second name is Blocked", t.proof("bob.krgn")[2][0] == "Blocked")
    root, _ = _reg(t, root, "bob.krgn")
    _ok("split matches canonical root", root == t.root())

    print("=== 250 registrations, each checked against canonical form ===")
    t, root = Tree(), EMPTY
    doms = [f"d{i}.krgn" for i in range(250)]
    kinds = {"Blocked": 0, "Vacant": 0}
    for dom in doms:
        root, kind = _reg(t, root, dom)
        kinds[kind] += 1
    _ok(f"250 registrations canonical ({kinds})", True)

    for dom in doms:
        p = t.proof(dom)
        assert p[2][0] == "Occupied"
        verify_and_apply(dom, p, root, t.leaf(dom), hash_leaf(dom, *_rec(9)))
    _ok("every leaf still provable after all inserts", True)

    ds = [t.proof(d)[0] for d in doms]
    mean = statistics.mean(ds)
    print(f"    depth min={min(ds)} mean={mean:.1f} max={max(ds)} (dense tree = 128)")
    print(f"    ~{2 * mean:.0f} node hashes/tx vs 256 -> {256 / (2 * mean):.1f}x")

    print("=== spec 5.3: the blocking-key attack ===")
    cand = next(f"atk{i}.krgn" for i in range(2000) if t.proof(f"atk{i}.krgn")[2][0] == "Blocked")
    d, sibs, (_, blocker) = pr = t.proof(cand)
    brec = (blocker,) + t.rec[blocker]
    blocking_leaf, nl = t.leaf(blocker), hash_leaf(cand, *_rec())
    kb, bb = bits(key_of(cand)), bits(key_of(blocker))
    print(f"    {cand} is blocked by {blocker} at depth {d}; "
          f"true divergence j={next(i for i in range(d, 128) if kb[i] != bb[i])}")

    # An unsound verifier that trusts a caller-supplied key instead of deriving it.
    def unsound(claimed):
        if not shares_prefix(claimed, kb, d) or claimed == kb:
            raise ValueError("prefix")
        if fold(kb, blocking_leaf, sibs) != root:
            raise ValueError("absence")
        j = next(i for i in range(d, 128) if kb[i] != claimed[i])
        node = hash_node(blocking_leaf, nl) if kb[j] else hash_node(nl, blocking_leaf)
        for i in range(j - 1, d - 1, -1):
            node = hash_node(EMPTY, node) if kb[i] else hash_node(node, EMPTY)
        return fold(kb, node, sibs)

    lie = list(kb)
    lie[127] = 1 - lie[127]  # shares every bit but the last, forcing j = 127
    forged = unsound(lie)
    honest = verify_and_apply(cand, pr, root, None, nl, blocking_rec=brec)
    _ok("unsound verifier accepts the lie and yields a different root", forged != honest)

    after = Tree()
    after.rec = dict(t.rec)
    after.rec[cand] = _rec()
    pv = after.proof(blocker)
    bricked = fold(bits(key_of(blocker)), after.leaf(blocker), pv[1]) != forged
    _ok(f"consequence: {blocker} is unprovable under the forged root (bricked)", bricked)

    _rejects("5.3 attack against the specified verifier",
             lambda: verify_and_apply(cand, pr, root, None, nl,
                                      blocking_rec=("zzzz.krgn",) + t.rec[blocker]))

    print("=== remaining adversarial cases (spec 7) ===")
    victim = doms[0]
    inc, ol = t.proof(victim), t.leaf(victim)
    nlv = hash_leaf(victim, *_rec(5))
    _rejects("depth one too small",
             lambda: verify_and_apply(victim, (inc[0] - 1, inc[1][:-1], inc[2]), root, ol, nlv))
    _rejects("depth one too large",
             lambda: verify_and_apply(victim, (inc[0] + 1, inc[1] + [EMPTY], inc[2]), root, ol, nlv))
    _rejects("siblings.len() != depth",
             lambda: verify_and_apply(victim, (inc[0], inc[1][:-1], inc[2]), root, ol, nlv))
    _rejects("depth > MAX_DEPTH",
             lambda: verify_and_apply(victim, (129, [EMPTY] * 129, ("Occupied", None)), root, ol, nlv))
    _rejects("Vacant claimed for a present key",
             lambda: verify_and_apply(victim, (inc[0], inc[1], ("Vacant", None)), root, None, nlv))
    _rejects("Occupied claimed for an absent key",
             lambda: verify_and_apply(cand, (d, sibs, ("Occupied", None)), root,
                                      hash_leaf(cand, *_rec()), nl))
    _rejects("Blocked record hashing to a leaf not at that position",
             lambda: verify_and_apply(cand, pr, root, None, nl,
                                      blocking_rec=(blocker, PK, "u1DIFFERENT", 0, 1)))
    _rejects("Blocked whose record.domain is our own domain",
             lambda: verify_and_apply(cand, pr, root, None, nl, blocking_rec=(cand,) + _rec()))
    _rejects("REG using an inclusion terminal",
             lambda: verify_and_apply(victim, inc, root, None, nlv))
    _rejects("update using a non-inclusion terminal",
             lambda: verify_and_apply(cand, pr, root, hash_leaf(cand, *_rec()), nl,
                                      blocking_rec=brec))

    print("\nALL CHECKS PASSED")


if __name__ == "__main__":
    main()

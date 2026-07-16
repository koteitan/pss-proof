#!/usr/bin/env python3
"""Numeric audit for §8.2 strong monomiality (強単項性) and the proposition
命題（標準形の直系先祖による切片の簡約化の強単項性） (content.md 3283),
backing lean/8/8.2-standard-slice-Red-strongmono.lean.

Checks, in order:

1. DEFINITION checksum: fold `strong_mono` over every nonempty pair sequence
   with entries < k and length <= maxL (k=4, maxL=4 -> 69,904 sequences, same
   family as python/red_checksum.lean).  The matching Lean snippet must print
   the same checksum.
2. PROPOSITION: for a pool of REAL standard forms (diagSeq closed under oper,
   entries reach 8+ naturally), every row-0 ancestor slice
   (0,j0') <=_M (0,j1'), j0' < j1' <= Lng M - 1, satisfies
   `strong_mono(Red(seg(M, j0', j1')))`.
3. PROOF TRANSPORT invariants used by the Lean proof:
   - S := seg(M,j0',j1'), N := Red(S), k := S[0][0]-S[0][1]:
     S == IncrFirst^k(N)  (ancestor_slice_Red_IncrFirst)
   - Br(S) == [IncrFirst^k(C) for C in Br(N)]  (Br_IncrFirstN)
   - descending reverse transport is therefore sound on these instances.
4. Emits a handful of #guard vectors (Lean regression lines) on stdout.

Semantics is red_model.py (the canonical model); only le0's reachability
matrix is memoized per sequence (pure speedup, no semantic change).
"""
import sys, os
from functools import lru_cache
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm

MOD = 1_000_000_007

# ---- pure speedup: cache the row-0 reachability matrix per sequence --------
@lru_cache(maxsize=1 << 20)
def _reach0(Mt):
    return rm.reach(list(Mt), rm.nextrel0)


def _le0_cached(M, j0, j1):
    n = rm.Lng(M)
    if not (j0 < n and j1 < n):
        return False
    return _reach0(tuple(M))[j0][j1]

rm.le0 = _le0_cached  # red_model resolves le0 from module globals at call time

Lng, entry, seg = rm.Lng, rm.entry, rm.seg
diagSeq, IncrFirst, funpow, oper = rm.diagSeq, rm.IncrFirst, rm.funpow, rm.oper


def cdom(C, D):
    """Row-0 heads weakly decreasing, row-1 tie-break (article 1402-1412)."""
    if not (entry(D, 0, 0) <= entry(C, 0, 0)):
        return False
    if entry(C, 0, 0) == entry(D, 0, 0) and not (entry(D, 1, 0) <= entry(C, 1, 0)):
        return False
    return True


def descending(Q):
    return all(cdom(Q[j0], Q[j1])
               for j1 in range(len(Q)) for j0 in range(j1 + 1))


@lru_cache(maxsize=1 << 20)
def _strong_mono_t(Mt):
    M = list(Mt)
    return rm.reduced(M) and rm.monoT(M) and descending(rm.Br(M))


def strong_mono(M):
    """強単項 (article 3279): reduced & mono & Br descending."""
    return bool(M) and _strong_mono_t(tuple(M))


# ---------------------------------------------------------------- 1. checksum
def all_seqs(k, maxL):
    pool = [[]]
    for _ in range(maxL):
        pool = [M + [(a, b)] for M in pool
                for a in range(k) for b in range(k)]
        yield from pool


def checksum(k=4, maxL=4):
    acc, n = 0, 0
    for M in all_seqs(k, maxL):
        n += 1
        bit = 1 if strong_mono(M) else 2
        acc = (acc * 31 + bit) % MOD
    return n, acc


# ---------------------------------------------------------- 2/3. proposition
def standard_pool(umax=3, vmax=5, nmax=3, gens=4, lenCap=13):
    pool, seen = [], set()
    for u in range(umax + 1):
        for v in range(u, vmax + 1):
            M = diagSeq(u, v)
            t = tuple(M)
            if t not in seen:
                seen.add(t)
                pool.append(M)
    frontier = list(pool)
    for _ in range(gens):
        nxt = []
        for M in frontier:
            for n in range(1, nmax + 1):
                N = oper(M, n)
                if Lng(N) > lenCap:
                    continue
                t = tuple(N)
                if t not in seen:
                    seen.add(t)
                    pool.append(N)
                    nxt.append(N)
        frontier = nxt
    return pool


def audit_proposition(pool):
    cases = viol = 0
    trans_viol = 0
    for M in pool:
        L = Lng(M)
        for j1p in range(1, L):
            for j0p in range(j1p):
                if not rm.le0(M, j0p, j1p):
                    continue
                cases += 1
                S = seg(M, j0p, j1p)
                N = rm.Red(S)
                if not strong_mono(N):
                    viol += 1
                    print(f"PROP VIOLATION M={M} j0'={j0p} j1'={j1p} "
                          f"S={S} Red(S)={N}", flush=True)
                    continue
                k = S[0][0] - S[0][1]
                if S != funpow(IncrFirst, k, N):
                    trans_viol += 1
                    print(f"READBACK VIOLATION M={M} j0'={j0p} j1'={j1p}",
                          flush=True)
                    continue
                BrS, BrN = rm.Br(S), rm.Br(N)
                if BrS != [funpow(IncrFirst, k, C) for C in BrN]:
                    trans_viol += 1
                    print(f"BR-MAP VIOLATION M={M} j0'={j0p} j1'={j1p}",
                          flush=True)
    return cases, viol, trans_viol


def guard_vectors():
    """Concrete regression vectors for #guard lines in the Lean file."""
    vecs = [
        [(0, 0)],
        [(0, 0), (1, 1)],
        [(0, 0), (1, 1), (2, 2)],
        [(0, 0), (1, 1), (2, 1)],
        [(0, 0), (1, 1), (2, 2), (3, 1), (3, 1)],
        [(0, 0), (1, 1), (2, 2), (3, 3), (3, 2), (3, 1)],
        [(0, 0), (1, 1), (2, 2), (3, 1), (3, 2)],
        [(1, 1), (2, 2)],
        [(0, 0), (0, 2)],
    ]
    return [(M, strong_mono(M)) for M in vecs]


def main():
    pool = standard_pool()
    lens = [Lng(M) for M in pool]
    ents = [x for M in pool for p in M for x in p]
    print(f"standard pool: {len(pool)} forms, maxlen {max(lens)}, "
          f"max entry {max(ents)}", flush=True)
    cases, viol, tviol = audit_proposition(pool)
    print(f"proposition: {cases} ancestor-slice cases, "
          f"{viol} violations, {tviol} transport violations", flush=True)

    print("guard vectors (M, strong_mono):", flush=True)
    for M, b in guard_vectors():
        lit = "[" + ", ".join(f"({a}, {b2})" for (a, b2) in M) + "]"
        print(f"#guard strongMono {lit} == {str(b).lower()}", flush=True)

    n, acc = checksum()
    print(f"checksum(k=4,maxL=4): {n} seqs -> {acc}", flush=True)

    ok = viol == 0 and tviol == 0
    print("AUDIT", "OK" if ok else "FAILED", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

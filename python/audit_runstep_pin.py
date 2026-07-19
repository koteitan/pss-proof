#!/usr/bin/env python3
"""Numeric audit for MISSION TransPinRunStepD_pt (§8.2 run-step D-regime pinned form).

Checks the FULL pinned equality
    Trans N = D_{N1,0}( F  +_B  D_{N1,j0'}( bpHeadT (Trans Mp) ) )
where
    F   = bpHeadT (Trans (seg N 0 (FirstNodes N ! (LastStep N) - 1)))     [front head]
    j0' = Joints N ! (Lng(Br N) - 1)
    Mp  = seg N j0' (Lng N - 1)                                            [terminal slice]
on the D-regime run-step deep BASE domain
    VE34Reg4D N  &  VEj1p N = Lng N - 1  &  TrMax N + 2 < Lng N  &  LastStep N < Lng(Br N) - 1
matching the Lean defs (8.2-condIIIV-pin-tspin TransPinRunStepD_pt).
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax,
                       seg, oper, reduced)
import trans_model as tm
from trans_model import Trans, bpHeadT, Dpt, addBT

def LastStep(M):
    b = Br(M)
    if not b: return 0
    J1 = len(b) - 1
    h0 = entry(b[J1], 0, 0); h1 = entry(b[J1], 1, 0)
    if h0 == h1: return J1
    return min(J for J in range(len(b))
               if entry(b[J1], 0, 0) == entry(b[J], 0, 0) and entry(b[J], 1, 0) < entry(b[J], 0, 0))

def cfbx_j1p(M): return FirstNodes(M)[len(Br(M)) - 1]          # VEj1p
def reg2(M): return reduced(M) and monoT(M) and len(Br(M)) > 0
def guard(M):
    j1p = cfbx_j1p(M); return entry(M, 0, j1p) > entry(M, 1, j1p)
def reg3(M): return reg2(M) and guard(M)
def reg4(M):
    if not reg3(M): return False
    J1 = len(Br(M)) - 1; j0p = Joints(M)[J1]
    return 0 < j0p < TrMax(M)

# cdomB / descendingB matching Lean 8.2-standard-slice-Red-strongmono
def cdomB(C, D):
    if not (entry(D, 0, 0) <= entry(C, 0, 0)): return False
    if entry(C, 0, 0) == entry(D, 0, 0):
        return entry(D, 1, 0) <= entry(C, 1, 0)
    return True
def descending(Q):
    n = len(Q)
    return all(cdomB(Q[J0], Q[J1]) for J1 in range(n) for J0 in range(J1 + 1))

def reg4D(M): return reg4(M) and descending(Br(M))

def in_domain(N):
    if Lng(N) < 2: return False
    if not reg4D(N): return False
    if cfbx_j1p(N) != Lng(N) - 1: return False          # VEj1p = Lng-1  (BASE)
    if not (TrMax(N) + 2 < Lng(N)): return False         # deep
    if not (LastStep(N) < len(Br(N)) - 1): return False  # run-step
    return True

def pinned(N):
    n = Lng(N)
    J1 = len(Br(N)) - 1
    j0p = Joints(N)[J1]
    J0 = LastStep(N)
    m1 = FirstNodes(N)[J0] - 1
    F = bpHeadT(Trans(seg(N, 0, m1)))
    Mp = seg(N, j0p, n - 1)
    inner = bpHeadT(Trans(Mp))
    return Dpt(entry(N, 1, 0),
              addBT(F, Dpt(entry(N, 1, j0p), inner)))

def gen_brute(maxL):
    GRID = [(x, y) for x in range(4) for y in range(4)]
    out = set()
    for L in range(3, maxL + 1):
        for tup in itertools.product(GRID, repeat=L - 1):
            M = [(0, 0)] + list(tup)
            if reg2(M): out.add(tuple(M))
    return out

def gen_deep(seeds, cap, maxLng):
    seen = set(seeds); frontier = list(seeds)
    while frontier and len(seen) < cap:
        nxt = []
        for M in frontier:
            Ml = list(M)
            for nn in range(2, 7):
                try: R = Red(oper(Ml, nn))
                except Exception: continue
                if 2 <= Lng(R) <= maxLng and reduced(R) and monoT(R) and len(Br(R)) > 0:
                    t = tuple(R)
                    if t not in seen:
                        seen.add(t); nxt.append(t)
                        if len(seen) >= cap: break
            if len(seen) >= cap: break
        frontier = nxt
    return seen

def main():
    corpus = gen_brute(6)
    corpus |= gen_deep(list(corpus), 60000, 9)
    dom = [list(M) for M in corpus if in_domain(list(M))]
    print("corpus size      :", len(corpus))
    print("in-domain hosts  :", len(dom))
    bad = []
    for N in dom:
        if Trans(N) != pinned(N):
            bad.append(N)
    print("pinned-form FAIL :", len(bad))
    for N in bad[:8]:
        print("   CEX:", N)
        print("     Trans =", Trans(N))
        print("     pinned=", pinned(N))
    if not bad:
        print("RESULT: pinned form HOLDS on all", len(dom), "in-domain run-step hosts.")
        # emit a handful for Lean cross-check
        show = sorted(dom, key=lambda x: (Lng(x), x))[:12]
        print("sample in-domain hosts:")
        for N in show:
            print("   ", N)
    else:
        print("RESULT: pinned form REFUTED (12th refutation candidate).")

if __name__ == "__main__":
    main()

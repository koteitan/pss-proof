#!/usr/bin/env python3
"""Empirically pin the i1=1 (d0pos) fold Br decomposition for the article-faithful
route-2 d0pos proof (docs continued 32).

For standard d1pos N (idx1 N (Lng N-1)=1, has row-1 parent), M = oper(N,n), and a monoT
slice M' = seg M j0' j1' whose branch region enters the delta-fold, the article claims
(regime-dependent):  Br M' = (Br N')[0 .. J_1-1] @ [single tail component], where
N' = seg N j0' (Lng N-1), J_1 = Lng(Br N')-1, and the tail head's row-0 equals
(Br N'_{J_1})_0's row-0 (TIE) with row-1 <= it.

This script checks, over the rank-stratified standard generator:
 (D1) is the fold tail a SINGLE component (#Br M' relates to #Br N')?
 (D2) does Br M' = (Br N')[0..J_1-1] @ [tail] hold as a prefix identity?
 (D3) the head row-0 tie + row-1 weak-decrease at the junction (Br N'_{J_1} vs tail).
Classify by article regime to see which sub-case each witness falls in.
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, zeroT, Br, is_standard, fmt, le0, FirstNodes)

def gen_std(maxlen, maxval, KMAX):
    base = [[(j, j) for j in range(u, v + 1)] for u in range(maxval + 1)
            for v in range(u, maxval + 1)]
    store = {fmt(m): m for m in base}; frontier = list(base)
    for _ in range(KMAX):
        newf = []
        for M in frontier:
            for n in range(1, 4):
                Mp = oper(M, n); key = fmt(Mp)
                if Mp and len(Mp) <= maxlen and all(a <= maxval and b <= maxval for (a, b) in Mp) \
                        and key not in store:
                    store[key] = Mp; newf.append(Mp)
        frontier = newf
    return [m for m in store.values() if is_standard(m)]

def is_d1pos(N):
    j1 = Lng(N) - 1
    return j1 >= 1 and not (entry(N,0,j1)==0 and entry(N,1,j1)==0) \
           and idx1(N, j1) == 1 and hasParent(N, 1, j1)

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (7, 3, 5)
    Ns = gen_std(maxlen, maxval, KMAX)
    d1 = [N for N in Ns if is_d1pos(N)]
    print(f"#std={len(Ns)} #d1pos={len(d1)}")
    tot = d1tail_single = d2_prefix_ok = d3_tie_ok = d3_tie_pairs = 0
    bad = []
    for N in d1:
        LN = Lng(N)
        for n in (1, 2, 3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p + 1, Lng(M)):
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    if not le0(M, j0p, j1p): continue
                    BrMp = Br(Mp)
                    if len(BrMp) < 1: continue
                    # reference slice N' = seg N j0' (Lng N -1) (only when j0p < LN)
                    if j0p >= LN: continue
                    Np = seg(N, j0p, LN - 1)
                    if not monoT(Np): continue
                    BrNp = Br(Np)
                    tot += 1
                    # (D2) prefix identity Br M' = (Br N')[0..J1-1] @ [tail]
                    J1 = len(BrNp) - 1
                    if J1 >= 0 and len(BrMp) >= 1:
                        prefix_ok = (len(BrMp) >= 1 and
                                     [fmt(c) for c in BrMp[:J1]] == [fmt(c) for c in BrNp[:J1]])
                        if prefix_ok: d2_prefix_ok += 1
                        # (D3) junction head tie + row-1 drop: BrMp[J1] vs BrNp[J1]
                        if J1 < len(BrMp) and J1 < len(BrNp):
                            hM = BrMp[J1][0]; hN = BrNp[J1][0]
                            if hM[0] == hN[0]:
                                d3_tie_pairs += 1
                                if hM[1] <= hN[1]: d3_tie_ok += 1
                                else:
                                    bad.append(('D3', fmt(N), n, j0p, j1p, hM, hN))
                    # (D1) tail single: len(BrMp) - J1 == 1 (one tail beyond the prefix)
                    if len(BrMp) == max(J1, 0) + 1:
                        d1tail_single += 1
    print(f"witnesses(monoT slice, j0'<LN, monoT N'): {tot}")
    print(f"  (D1) #BrM' == J1+1 (single tail):       {d1tail_single}/{tot}")
    print(f"  (D2) prefix Br M'[..J1-1] == Br N'[..J1-1]: {d2_prefix_ok}/{tot}")
    print(f"  (D3) junction row-0 tie => row-1 drop:  {d3_tie_ok}/{d3_tie_pairs} ok")
    if bad: print("  COUNTEREXAMPLES (first 5):", bad[:5])

if __name__ == '__main__':
    main()

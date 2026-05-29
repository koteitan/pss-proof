#!/usr/bin/env python3
"""Pin the ¬brle (multi-component) d0pos structure for the article regime decomposition.

For standard d1pos N, M=oper(N,n), monoT slice M'=seg M j0' j1' with leR M 0 j0' j1',
nonempty Br, and ¬brle (TrMax!=end AND not le0 M' (TrMax+1)(Lng-1) -> Yp multiT):
check the article decomposition Br M' = (Br N')[0..J1-1] @ [tail] with N' = seg N j0' (Lng N-1)
(regime A) and report:
  - whether N' is monoT and Br N' nonempty (so IH applies),
  - prefix match: Br M'[0..len-2] == Br N'[0..len-2]?
  - junction: Br M'[-1] head row-0 == Br N'[J1] head row-0 (tie) and row-1 <= (drop)?
  - tail (last comp of Br M') is a single component (always, since it is the last P-comp).
Also count how many ¬brle witnesses have j0' < j_{-2}^N (regime A) vs >= (regime B).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, Br, is_standard, fmt, le0)

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
        if len(sys.argv) > 3 else (7, 3, 4)
    Ns = gen_std(maxlen, maxval, KMAX)
    d1 = [N for N in Ns if is_d1pos(N)]
    nb = Nprime_mono = prefix_ok = junction_ok = junction_pairs = 0
    regA = regB = 0; exs = []; bad = []
    for N in d1:
        LN = Lng(N); j1N = LN - 1
        jm2 = parent(N, 1, j1N)
        for n in (1, 2, 3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p + 1, Lng(M)):
                    if not le0(M, j0p, j1p): continue
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    t = TrMax(Mp)
                    if t == Lng(Mp) - 1: continue
                    if le0(Mp, t + 1, Lng(Mp) - 1): continue     # brle holds -> skip
                    BrMp = Br(Mp)
                    if len(BrMp) < 2: continue                    # multi only
                    nb += 1
                    if j0p < LN:
                        if j0p < jm2: regA += 1
                        else: regB += 1
                        Np = seg(N, j0p, LN - 1)
                        if monoT(Np):
                            BrNp = Br(Np)
                            if BrNp:
                                Nprime_mono += 1
                                J1 = len(BrNp) - 1
                                # prefix Br M'[0..len(BrMp)-2] vs Br N'[0..J1-1]
                                if [fmt(c) for c in BrMp[:-1]] == [fmt(c) for c in BrNp[:J1]]:
                                    prefix_ok += 1
                                else:
                                    if len(bad) < 6:
                                        bad.append(('prefix', fmt(N), n, j0p, j1p,
                                                    [fmt(c) for c in BrMp], [fmt(c) for c in BrNp]))
                                # junction: BrMp[-1] vs BrNp[J1]
                                hM = BrMp[-1][0]; hN = BrNp[J1][0]
                                if hM[0] == hN[0]:
                                    junction_pairs += 1
                                    if hM[1] <= hN[1]: junction_ok += 1
                    if len(exs) < 5:
                        exs.append((fmt(N), n, j0p, j1p, [fmt(c) for c in BrMp]))
    print(f"#d1pos={len(d1)}  ¬brle multi witnesses={nb}")
    print(f"  regime A (j0'<j_{{-2}}^N)={regA}  regime B (>=)={regB}")
    print(f"  N'=seg N j0' (LN-1) monoT w/ nonempty Br: {Nprime_mono}/{nb}")
    print(f"  prefix Br M'[:-1] == Br N'[:J1]: {prefix_ok}/{Nprime_mono}")
    print(f"  junction row-0 tie => row-1 drop: {junction_ok}/{junction_pairs}")
    if exs: print("  examples:", exs)
    if bad: print("  prefix MISMATCH (first):", bad[:3])

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""RECONCILE: is Br M' ALWAYS a single P-component for d1pos monoT slices (agent A:
5548/5548), or sometimes multi (agent B D1=180/189 + the article regime A/B)?

For each standard d1pos N (rank-stratified generator), M=oper(N,n), and EVERY monoT
slice M'=seg M j0' j1' with leR M 0 j0' j1' (the lemma's actual hypotheses) and
nonempty Br, report the distribution of #(Br M') and whether
le0 M' (TrMax M'+1)(Lng M'-1) (= the 'brle' that makes Yp monoT/singleton).
Print concrete multi-component witnesses if any.
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
    print(f"#std={len(Ns)} #d1pos={len(d1)}")
    from collections import Counter
    dist = Counter(); brle_ok = brle_no = tot = 0
    multi_ex = []; brle_fail_single = []
    for N in d1:
        M = N  # the AMBIENT is M=oper(N,.) below; here treat each std d1pos as N
    for N in d1:
        for n in (1, 2, 3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p + 1, Lng(M)):
                    if not le0(M, j0p, j1p): continue          # leR M 0 j0' j1'
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    t = TrMax(Mp)
                    if t == Lng(Mp) - 1: continue              # Br empty
                    BrMp = Br(Mp)
                    tot += 1
                    dist[len(BrMp)] += 1
                    brle = le0(Mp, t + 1, Lng(Mp) - 1)
                    if brle: brle_ok += 1
                    else: brle_no += 1
                    if len(BrMp) > 1 and len(multi_ex) < 6:
                        multi_ex.append((fmt(N), n, j0p, j1p, len(BrMp), brle, fmt(Mp)))
                    if (not brle) and len(BrMp) == 1 and len(brle_fail_single) < 4:
                        brle_fail_single.append((fmt(N), n, j0p, j1p))
    print(f"witnesses (le0 slice, monoT, nonempty Br): {tot}")
    print(f"  #Br M' distribution: {dict(sorted(dist.items()))}")
    print(f"  le0 M' (TrMax+1)(Lng-1) [brle, => Yp monoT/singleton]: {brle_ok} ok / {brle_no} NO")
    print(f"  multi-component (#Br>1) examples: {multi_ex}")
    if brle_fail_single: print(f"  brle-fail-but-single (sanity): {brle_fail_single}")

if __name__ == '__main__':
    main()

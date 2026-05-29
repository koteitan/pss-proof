#!/usr/bin/env python3
"""LINCHPIN check: is the d0pos ¬brle residual VACUOUS in its EXACT context?

The residual (m_6_8_slice_Br_descending_monoT, d0pos jlarge branch) is reached with:
  N monoT standard, M=oper(N,n) (n>=1), idx1 N (Lng N-1)=1 & hasParent N 1 (Lng N-1),
  M'=seg M j0' j1' monoT, le0 M j0' j1',  bge: Lng N-1 <= j1'   (the 'jlarge' branch;
  crossesA0 j0N<j1' is then automatic since j0N=parent N 1 (Lng N-1) < Lng N-1 <= j1').
brle := (TrMax M' = Lng M'-1) OR le0 M' (TrMax M'+1)(Lng M'-1).
Claim (agent B): in this context brle ALWAYS holds (¬brle vacuous) => brYp_single is provable.

This pins it with the EXACT bge constraint (which earlier d1pos_Br_singleton_check OMITTED),
over a DEEP rank-stratified standard generator. Also re-classify: do the earlier ¬brle multi
witnesses all have j1' < Lng N-1 (jsmall, handled by IH) so they never reach the residual?
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

def is_d1pos_mono(N):
    j1 = Lng(N) - 1
    return j1 >= 1 and monoT(N) and not (entry(N,0,j1)==0 and entry(N,1,j1)==0) \
           and idx1(N, j1) == 1 and hasParent(N, 1, j1)

def brle(Mp):
    t = TrMax(Mp)
    return t == Lng(Mp) - 1 or le0(Mp, t + 1, Lng(Mp) - 1)

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (8, 3, 5)
    Ns = gen_std(maxlen, maxval, KMAX)
    d1 = [N for N in Ns if is_d1pos_mono(N)]
    resid = nb_resid = 0           # residual context (with bge)
    nobge_nb = nobge_tot = 0       # WITHOUT bge (earlier framing)
    nb_resid_ex = []; nb_nobge_jsmall = 0
    for N in d1:
        LN = Lng(N); j0N = parent(N, 1, LN - 1)
        for n in (1, 2, 3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p + 1, Lng(M)):
                    if not le0(M, j0p, j1p): continue
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    b = brle(Mp)
                    # WITHOUT bge (earlier framing): count ¬brle
                    nobge_tot += 1
                    if not b:
                        nobge_nb += 1
                        if j1p < LN - 1: nb_nobge_jsmall += 1   # would be jsmall (j1'<Lng N-1)
                    # RESIDUAL context: add bge (Lng N-1 <= j1')
                    if j1p >= LN - 1:
                        resid += 1
                        if not b:
                            nb_resid += 1
                            if len(nb_resid_ex) < 8:
                                nb_resid_ex.append((fmt(N), n, j0p, j1p, fmt(Mp),
                                                    len(Br(Mp))))
    print(f"#d1pos-mono std = {len(d1)}")
    print(f"WITHOUT bge (all monoT slices): ¬brle = {nobge_nb}/{nobge_tot}"
          f"  (of which j1'<Lng N-1 [jsmall, IH-handled] = {nb_nobge_jsmall})")
    print(f"RESIDUAL context (bge: Lng N-1 <= j1'): ¬brle = {nb_resid}/{resid}")
    if nb_resid == 0:
        print("  => VACUOUS: brYp_single (le0 M' (TrMax+1)(Lng-1)) holds in context. d0pos CLOSES.")
    else:
        print("  => NOT vacuous! brYp_single is FALSE for:", nb_resid_ex)

if __name__ == '__main__':
    main()

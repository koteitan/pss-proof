#!/usr/bin/env python3
"""Crux of the capped confinement (TrMax M' <= c) via boundary row-1 stop.
For capped notbrle cases (formula-G, j1red=LN-1), check the boundary stop:
 the row-1 step  c -> c+1 in M'  FAILS, where
   entry M' 1 c    = entry N 1 (j1red-1) = entry N 1 (LN-2)         (last trunk node)
   entry M' 1 (c+1)= entry N 1 jm2       (block-(q+1) start, row-1 reset)
 so step fails iff  NOT (entry N 1 (LN-2) < entry N 1 jm2), i.e. entry N 1 jm2 <= entry N 1 (LN-2).
BUT confinement requires the FULL stop (no nextrel1 at the trunk's actual end).
So instead DIRECTLY verify: TrMax M' <= c  via the keystone-span route is equivalent
to: NOT (c < TrMax M').  We probe the necessary local fact:
   the row-1 value at M'-index c+1 (block restart) and at c (block end), and whether
   entry M' 1 (c+1) <= entry M' 1 c  (the row-1 NON-increase across the block boundary).
This single inequality drives the stop.  Also: does it hold for ALL j1' (not just at c+1)?
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, is_standard, fmt, le0)
from d1pos_j0j1red_search import gen_std, is_d1pos_mono, brle

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (11, 5, 6)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    cap=0
    b_ineq=0; b_fail=[]      # entry N 1 jm2 <= entry N 1 (LN-2)
    mb_ineq=0; mb_fail=[]    # entry M' 1 (c+1) <= entry M' 1 c  (at the boundary, when c+1<Lng M')
    for N in Ns:
        LN = Lng(N); jm2 = parent(N, 1, LN-1); w = LN-1-jm2
        if w<=0: continue
        for n in (1,2,3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p+1, Lng(M)):
                    if j1p < LN-1: continue
                    if not le0(M, j0p, j1p): continue
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    if brle(Mp): continue
                    j0red=jm2+(j0p-jm2)%w if j0p>=jm2 else j0p
                    j1red=min(j0red+(j1p-j0p),LN-1)
                    if not (j0red<j1red<=LN-1): continue
                    capped = (j1red != j0red+(j1p-j0p))
                    if not capped: continue
                    cap+=1
                    c=j1red-1-j0red
                    # boundary N-side: jm2 vs LN-2
                    if entry(N,1,jm2) <= entry(N,1,LN-2): b_ineq+=1
                    elif len(b_fail)<8: b_fail.append((fmt(N),'jm2',jm2,'e1jm2',entry(N,1,jm2),'e1LN-2',entry(N,1,LN-2)))
                    # M'-side: if c+1 < Lng Mp, check row-1 non-increase across boundary
                    if c+1 < Lng(Mp):
                        if entry(Mp,1,c+1) <= entry(Mp,1,c): mb_ineq+=1
                        elif len(mb_fail)<8: mb_fail.append((fmt(N),n,j0p,j1p,'c',c,'e1c1',entry(Mp,1,c+1),'e1c',entry(Mp,1,c)))
    print(f"#capped notbrle={cap} KMAX={KMAX}")
    print(f"  N-side  entry N 1 jm2 <= entry N 1 (LN-2): {b_ineq}/{cap}")
    for f in b_fail: print("    Nfail",f)
    nb=sum(1 for _ in [0])
    print(f"  M'-side entry M' 1 (c+1) <= entry M' 1 c (boundary row-1 non-increase): {mb_ineq}")
    for f in mb_fail: print("    Mfail",f)

if __name__=='__main__': main()

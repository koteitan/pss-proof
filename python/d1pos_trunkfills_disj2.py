#!/usr/bin/env python3
"""Does disj2 (le0 Mp (TrMax Mp+1)(Lng Mp -1)) hold on ALL trunkfills cases?
And separately disj1.  Tabulate the disjunct that fires.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, is_standard, fmt, le0)
from d1pos_j0j1red_search import gen_std, is_d1pos_mono, brle

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (11, 5, 6)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot=0; d1=0; d2=0; both=0; neither=[]
    # is TrMax Mp+1 <= Lng Mp -1 (room for disj2)?
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
                    j0red=jm2+(j0p-jm2)%w if j0p>=jm2 else j0p
                    j1red=min(j0red+(j1p-j0p),LN-1)
                    if not (j0red<j1red<=LN-1): continue
                    Np=seg(N,j0red,j1red)
                    if TrMax(Np)!=Lng(Np)-1: continue
                    tot+=1
                    TrMp=TrMax(Mp); LMp1=Lng(Mp)-1
                    a = (TrMp==LMp1)
                    b = le0(Mp,TrMp+1,LMp1)
                    if a: d1+=1
                    if b: d2+=1
                    if a and b: both+=1
                    if not (a or b) and len(neither)<8:
                        neither.append((fmt(N),n,j0p,j1p,'TrMp',TrMp,'LMp1',LMp1))
    print(f"#trunkfills cases={tot} KMAX={KMAX}")
    print(f"  disj1 (TrMp==LMp-1): {d1}/{tot}")
    print(f"  disj2 (le0 Mp (TrMp+1)(LMp-1)): {d2}/{tot}")
    print(f"  both: {both}")
    print(f"  NEITHER: {len(neither)}")
    for f in neither: print("    NEITHER",f)

if __name__=='__main__': main()

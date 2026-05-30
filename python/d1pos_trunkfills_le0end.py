#!/usr/bin/env python3
"""In trunkfills cases, probe intrinsic M'-characterizations:
  (A) le0 Mp 0 (Lng Mp -1)  -- whole M' is one row-0 chain end-to-end
  (B) for disj2 cases: le0 Mp (TrMp+1)(LMp-1).
Also: is brle(Mp) <=> le0 Mp 0 (Lng Mp-1) on trunkfills?  And is it
equivalent on ALL in-domain cases (the real discriminator)?
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
    tf=0; tf_le0end=0; tf_fail=[]
    # whole-domain: is le0end == trunkfills? (discriminator hypothesis)
    dom=0; eq=0; neq=[]
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
                    trunkfills = (TrMax(Np)==Lng(Np)-1)
                    le0end = le0(Mp,0,Lng(Mp)-1)
                    dom+=1
                    if le0end==trunkfills: eq+=1
                    elif len(neq)<10: neq.append((fmt(N),n,j0p,j1p,'tf',trunkfills,'le0end',le0end,'TrNp',TrMax(Np),'LNp1',Lng(Np)-1))
                    if trunkfills:
                        tf+=1
                        if le0end: tf_le0end+=1
                        elif len(tf_fail)<8: tf_fail.append((fmt(N),n,j0p,j1p))
    print(f"KMAX={KMAX} domain={dom}")
    print(f"  trunkfills cases={tf}; of these le0 Mp 0 (LMp-1): {tf_le0end}/{tf}")
    for f in tf_fail: print("   TF-noLE0END",f)
    print(f"  (whole domain) le0end == trunkfills : {eq}/{dom}")
    for f in neq: print("   NEQ",f)

if __name__=='__main__': main()

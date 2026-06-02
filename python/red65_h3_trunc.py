#!/usr/bin/env python3
"""H3: does truncation ever occur, and is the claim still TRUE when S is monoT?"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import Lng, entry, seg, leR, monoT, fmt
from d1pos_j0j1red_search import gen_std

def rebase(N, m10):
    e0=entry(N,0,m10); e1=entry(N,1,m10); S=seg(N,m10,Lng(N)-1)
    return [(p[0]-e0+e1,p[1]) for p in S]

if __name__=="__main__":
    maxlen,maxval,KMAX=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (12,6,6)
    Ms=gen_std(maxlen,maxval,KMAX)
    trunc_cases=0; total_slices=0; monoS_slices=0
    Tm=Fm=0; cexm=[]
    for N in Ms:
        ln=Lng(N)
        for m10 in range(0,ln):
            total_slices+=1
            S=seg(N,m10,ln-1); e0=entry(N,0,m10)
            if any(entry(S,0,j)<e0 for j in range(Lng(S))): trunc_cases+=1
            if monoT(S):
                monoS_slices+=1
                RM=rebase(N,m10); w=ln-m10
                for i in (0,1):
                    for a in range(w):
                        for b in range(w):
                            lhs=leR(RM,i,a,b); rhs=leR(N,i,a+m10,b+m10)
                            if lhs==rhs: Tm+=1
                            else:
                                Fm+=1
                                if len(cexm)<6: cexm.append((fmt(N),m10,i,a,b,lhs,rhs))
    print(f"total_slices={total_slices} truncating_slices={trunc_cases} monoT_slices={monoS_slices}")
    print(f"[monoT(S) restricted] TRUE={Tm} FALSE={Fm}")
    for c in cexm: print("  CEX",c)

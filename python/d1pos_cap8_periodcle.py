#!/usr/bin/env python3
"""Verify periodic-BOUNDARY cleMB: for residual ¬brle periodic (j0'>=LN-1) with the
min-cap ACTIVE (j1red=LN-1 < j0red+(j1'-j0')), the anchor c = IdxSum(P S)!(len-1) of
S = seg M (j0'+TrMax M'+1) j1' satisfies c <= Lng(seg N AN j1red)-1. Rank-strat, BOTH counts."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))+"/../python")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, Br, is_standard, fmt, le0, IdxSum)
def gen_std(maxlen, maxval, KMAX):
    base = [[(j, j) for j in range(u, v + 1)] for u in range(maxval + 1) for v in range(u, maxval + 1)]
    store = {fmt(m): m for m in base}; frontier = list(base)
    for _ in range(KMAX):
        newf = []
        for M in frontier:
            for n in range(1, 4):
                Mp = oper(M, n); key = fmt(Mp)
                if Mp and len(Mp) <= maxlen and all(a<=maxval and b<=maxval for (a,b) in Mp) and key not in store:
                    store[key]=Mp; newf.append(Mp)
        frontier=newf
    return [m for m in store.values() if is_standard(m)]
def is_d1pos(N):
    j1=Lng(N)-1
    return j1>=1 and not (entry(N,0,j1)==0 and entry(N,1,j1)==0) and idx1(N,j1)==1 and hasParent(N,1,j1)
def brle_seg(X,a,b):
    Xp=seg(X,a,b); t=TrMax(Xp); L=Lng(Xp)
    return (t==L-1) or le0(Xp,t+1,L-1)
def main():
    maxlen,maxval=(int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (9,4)
    KMAXm=int(sys.argv[3]) if len(sys.argv)>3 else 7
    for KMAX in range(4,KMAXm+1):
        Ns=[N for N in gen_std(maxlen,maxval,KMAX) if is_d1pos(N)]
        bnd=0; ok=0; bad=0; interior=0
        for N in Ns:
            LN=Lng(N); j1N=LN-1; jm2=parent(N,1,j1N); w=j1N-jm2
            if w<=0: continue
            for n in range(1,4):
                M=oper(N,n)
                if not M: continue
                LM=Lng(M)
                for j0 in range(LM):
                    for j1 in range(j0+1,LM):
                        Mp=seg(M,j0,j1)
                        if not monoT(Mp) or not le0(M,j0,j1) or not (j1N<=j1): continue
                        if brle_seg(M,j0,j1): continue
                        if not (j0>=j1N): continue  # periodic
                        q0=(j0-jm2)//w; s0=(j0-jm2)%w
                        j0red=jm2+s0; j1red=min(j0red+(j1-j0), j1N)
                        if not (j1N < j0red+(j1-j0)): continue  # cap active (boundary)
                        bnd+=1
                        A=j0+TrMax(Mp)+1
                        S=seg(M,A,j1)
                        if len(P(S))<=1: continue
                        c=IdxSum(P(S))[len(P(S))-1]
                        AN=j0red+TrMax(seg(N,j0red,j1red))+1
                        Snside=seg(N,AN,j1red)
                        m=Lng(Snside)-1
                        if c<=m: ok+=1
                        else: bad+=1
        print(f"KMAX={KMAX}: periodic-boundary={bnd}  c<=m OK={ok}  BAD={bad}")
main()

#!/usr/bin/env python3
"""Verify the low-branch (j0'<LN-1) chain: notbrleNp (with j0red=j0', j1red=LN-1)
holds in residual ¬brle cases, and A<LN-1 follows (since A==LN-1 => brleNp).
Also verify regime dispatch facts: multiNp, le0Np for the low cells. Rank-strat, BOTH counts."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))+"/../python")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, Br, is_standard, fmt, le0)
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
def brle_seg(N,a,b):
    Np=seg(N,a,b); t=TrMax(Np); L=Lng(Np)
    return (t==L-1) or le0(Np,t+1,L-1)
def main():
    maxlen,maxval=(int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (9,4)
    KMAXm=int(sys.argv[3]) if len(sys.argv)>3 else 7
    for KMAX in range(4,KMAXm+1):
        Ns=[N for N in gen_std(maxlen,maxval,KMAX) if is_d1pos(N)]
        low=0; notbrleNp_T=0; notbrleNp_F=0; AltN_T=0; AltN_F=0; multiNp_T=0; multiNp_F=0; le0Np_T=0; le0Np_F=0
        for N in Ns:
            LN=Lng(N); j1N=LN-1
            for n in range(1,4):
                M=oper(N,n)
                if not M: continue
                LM=Lng(M)
                for j0 in range(LM):
                    for j1 in range(j0+1,LM):
                        Mp=seg(M,j0,j1)
                        if not monoT(Mp) or not le0(M,j0,j1) or not (j1N<=j1): continue
                        if brle_seg(M,j0,j1): continue
                        if not (j0<j1N): continue  # low branch
                        low+=1
                        A=j0+TrMax(Mp)+1
                        if A<j1N: AltN_T+=1
                        else: AltN_F+=1
                        # notbrleNp at j0red=j0, j1red=LN-1
                        nb = not brle_seg(N,j0,j1N)
                        if nb: notbrleNp_T+=1
                        else: notbrleNp_F+=1
                        # multiNp = 1<len(P(seg N (j0+TrMax(seg N j0 j1N)+1) j1N))
                        AN=j0+TrMax(seg(N,j0,j1N))+1
                        SN=seg(N,AN,j1N)
                        if len(P(SN))>1: multiNp_T+=1
                        else: multiNp_F+=1
                        if le0(N,j0,j1N): le0Np_T+=1
                        else: le0Np_F+=1
        print(f"KMAX={KMAX}: low={low}  notbrleNp T/F={notbrleNp_T}/{notbrleNp_F}  AltN(A<LN-1) T/F={AltN_T}/{AltN_F}  multiNp T/F={multiNp_T}/{multiNp_F}  le0Np T/F={le0Np_T}/{le0Np_F}")
main()

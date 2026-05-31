#!/usr/bin/env python3
"""Hunt for residual ¬brle d1pos cases with j0'<LN-1 and A=j0'+TrMax(M')+1 >= LN-1.
Rank-stratified by KMAX. If NONE found, A<LN-1 is forced when j0'<LN-1."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))+"/../python")
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
                if Mp and len(Mp) <= maxlen and all(a <= maxval and b <= maxval for (a, b) in Mp) and key not in store:
                    store[key] = Mp; newf.append(Mp)
        frontier = newf
    return [m for m in store.values() if is_standard(m)]
def is_d1pos(N):
    j1 = Lng(N) - 1
    return j1 >= 1 and not (entry(N,0,j1)==0 and entry(N,1,j1)==0) and idx1(N,j1)==1 and hasParent(N,1,j1)
def main():
    for KMAX in range(2, int(sys.argv[3])+1 if len(sys.argv)>3 else 9):
        maxlen, maxval = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv)>2 else (10,4)
        Ns=[N for N in gen_std(maxlen,maxval,KMAX) if is_d1pos(N)]
        tot=Aeq=Agt=0
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
                        t=TrMax(Mp); LMp=Lng(Mp)
                        if (t==LMp-1) or le0(Mp,t+1,LMp-1): continue
                        tot+=1; A=j0+t+1
                        if j0<j1N:
                            if A==j1N: Aeq+=1
                            elif A>j1N: Agt+=1
        print(f"KMAX={KMAX} len<={maxlen} val<={maxval}: residual={tot}  (j0<LN-1 & A==LN-1)={Aeq}  (A>LN-1)={Agt}")
main()

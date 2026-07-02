#!/usr/bin/env python3
"""Pin EXACTLY: for le0-pred j' of y (c<j', le0 N j' y), what is (qp vs q)?
Since le0 needs j'<=y (forward reach), and c<j', and j'=j0+qp*w+sp:
  c=pM+q*w=j0+q*w+spM (spM=pM-j0), y=j0+q*w+s.
  c<j' & j'<=y  =>  qp=q (SAME block q) and spM<sp<=s.
So ALL predecessors are SAME-BLOCK q! Then oper_d1pos_le0_base_back applies directly.
Verify: every le0-pred j' (c<j', le0 N j' y) has qp==q."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, idx1, hasParent, parent, oper)
from _valley_check import reach_matrix, closure, fmt

def main():
    allM=closure(4,12)
    cSame=0; cDiff=0; bad=[]
    cBack_ok=0; cBack_bad=0
    for M in allM:
        M=list(map(tuple,M)); L=Lng(M)
        if L<=1: continue
        j1=L-1
        if entry(M,0,j1)==0 and entry(M,1,j1)==0: continue
        if idx1(M,j1)!=1 or not hasParent(M,1,j1): continue
        j0=parent(M,1,j1)
        if j0 is None or not(j0<j1): continue
        w=j1-j0
        if w<=0: continue
        Rm=reach_matrix(M)
        for n in range(2,4):
            N=oper(M,n); LN=Lng(N)
            if LN!=j0+n*w: continue
            Rn=reach_matrix(N)
            for s in range(1,w):
                u=j0+s
                if not hasParent(M,1,u): continue
                pM=parent(M,1,u)
                if pM is None or pM<j0: continue
                spM=pM-j0
                for q in range(n):
                    y=j0+q*w+s; c=pM+q*w
                    if y>=LN: continue
                    for jp in range(c+1,LN):
                        if not Rn[jp][y]: continue
                        d=jp-j0; qp=d//w; sp=d%w
                        if j0+qp*w+sp!=jp: continue
                        if qp==q:
                            cSame+=1
                            # base_back: le0 N j' y (both block q) => le0 M (j0+sp) (j0+s)
                            if j0+sp<L and u<L and Rm[j0+sp][u]: cBack_ok+=1
                            else: cBack_bad+=1
                        else:
                            cDiff+=1
                            if len(bad)<20: bad.append((fmt(M),n,q,s,jp,qp,sp))
    print("predecessors SAME block (qp==q):", cSame, " DIFFERENT block:", cDiff)
    print("base_back reflection le0 M (j0+sp) u ok/bad:", cBack_ok, cBack_bad)
    print("--- diff-block examples ---")
    for e in bad: print(e)

if __name__=="__main__":
    main()

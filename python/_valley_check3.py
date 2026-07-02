#!/usr/bin/env python3
"""Check the M-side discharge boundary: for le0-pred j'=j0+qp*w+sp of y (c<j', le0 N j' y):
  - is j0+sp > pM always? (then M valley clause directly gives entry1(j0+sp)>=entry1 u)
  - or are there cases j0+sp <= pM (need different arg)?
Also: does c<j' force the block index qp to satisfy qp>=q? (then sp can be small but
block later). And confirm: c<j' <=> (qp,sp) lexicographically after (q, sp_of_pM)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, idx1, hasParent, parent, oper)
from _valley_check import reach_matrix, closure, fmt

def main():
    allM=closure(4,12)
    cGT=0; cLE=0; bad=[]
    # for j0+sp<=pM cases, record whether entry M1(j0+sp)>=entry M1 u still holds
    cLE_ok=0; cLE_bad=0
    # block relationship
    cqpge=0; cqplt=0
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
                        if qp>=q: cqpge+=1
                        else: cqplt+=1
                        if j0+sp>pM: cGT+=1
                        else:
                            cLE+=1
                            if entry(M,1,j0+sp)>=entry(M,1,u): cLE_ok+=1
                            else:
                                cLE_bad+=1
                                if len(bad)<20: bad.append((fmt(M),n,q,s,jp,qp,sp,spM))
    print("j0+sp > pM:", cGT, " | j0+sp <= pM:", cLE)
    print("  among <=pM: entry ineq ok/bad:", cLE_ok, cLE_bad)
    print("qp>=q:", cqpge, " qp<q:", cqplt)
    print("--- bad ---")
    for e in bad: print(e)

if __name__=="__main__":
    main()

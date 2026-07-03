#!/usr/bin/env python3
"""Deeper: for le0-predecessor j'=j0+qp*w+sp of y (c<j', le0 N j' y), check:
 (A) offset sp satisfies sp<=s? (or rather the M-side le0 (j0+sp) u holds)
 (B) le0 M (j0+sp) u  (so M valley clause: pM<j' & le0 M j' u => entry1 j'>=entry1 u applies)
 (C) does pM < (j0+sp) hold? (needed: M valley wants predecessor > pM, but entry monotone)
 (D) the FULL valley via M-side: entry M 1 (j0+sp) >= entry M 1 u  when le0 M (j0+sp) u.
We separate: when le0 M (j0+sp) u is TRUE vs the entry inequality."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, nextrel0, idx1, hasParent, parent, oper, diagSeq, IncrFirst)
from _valley_check import reach_matrix, closure, fmt

def main():
    allM=closure(4,12)
    print("closure:", len(allM))
    cA=cAbad=0   # le0 M (j0+sp) u holds whenever le0 N j' y (j'>c)
    cD=cDbad=0   # when le0 M (j0+sp) u, entry M1(j0+sp) >= entry M1 u
    cSP=0; cSPgt=0  # sp<=s vs sp>s
    cNoLe0=0     # le0 N j' y but NOT le0 M (j0+sp) u
    bad=[]
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
                for q in range(n):
                    y=j0+q*w+s; c=pM+q*w
                    if y>=LN: continue
                    for jp in range(c+1,LN):
                        if not Rn[jp][y]: continue
                        d=jp-j0; qp=d//w; sp=d%w
                        if j0+qp*w+sp!=jp: continue
                        if sp<=s: cSP+=1
                        else: cSPgt+=1
                        # (A) le0 M (j0+sp) u
                        if j0+sp<L and u<L and Rm[j0+sp][u]:
                            cA+=1
                            # (D)
                            if entry(M,1,j0+sp)>=entry(M,1,u): cD+=1
                            else:
                                cDbad+=1
                                if len(bad)<20: bad.append(("D",fmt(M),n,q,s,jp,qp,sp))
                        else:
                            cNoLe0+=1
                            # When no M-side le0, do we still have the entry ineq?
                            if entry(M,1,j0+sp)>=entry(M,1,u): cA+=0
                            else:
                                cAbad+=1
                                if len(bad)<20: bad.append(("NOLE0_FAIL",fmt(M),n,q,s,jp,qp,sp,entry(M,1,j0+sp),entry(M,1,u)))
    print("sp<=s :", cSP, " sp>s :", cSPgt)
    print("le0 M (j0+sp) u holds:", cA, " | NOT-holds:", cNoLe0)
    print("when le0 M holds, entry ineq (D) ok/bad:", cD, cDbad)
    print("when NO le0 M, entry ineq still ok unless listed; bad:", cAbad)
    print("--- bad ---")
    for e in bad: print(e)

if __name__=="__main__":
    main()

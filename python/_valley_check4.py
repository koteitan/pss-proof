#!/usr/bin/env python3
"""Can the valley be discharged WITHOUT cross-block le0 reflection?
Candidate: entry N 1 j' >= entry N 1 y reduces (via periodic readback) to
  entry M 1 (j0+sp) >= entry M 1 (j0+s)   [u=j0+s], with sp = offset of j'.
And empirically le0 N j' y forces sp<=s and j0+sp>pM.

ALT route: is the M-side fact "for sp with pM<j0+sp and sp<=s: entry M1(j0+sp)>=entry M1 u"
derivable WITHOUT le0, i.e., just from M valley applied to le0 M (j0+sp) u?  We need le0 M (j0+sp) u.
Check: is le0 M (j0+sp) u guaranteed by sp<=s alone (within-block reachability j0+sp -> u in M)?
i.e. (nextrel0 M)* (j0+sp) (j0+s) for pM<j0+sp<=... <j0+s.  Verify le0 M (j0+sp) u <-> True
whenever 0<=sp<=s and... (the within-block monotone chain)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, idx1, hasParent, parent, oper)
from _valley_check import reach_matrix, closure, fmt

def main():
    allM=closure(4,12)
    # Q1: for ALL offsets sp with pM<j0+sp<=u(=j0+s) and le0 M (j0+sp) u? always?
    cTotal=0; cLe0=0; cNoLe0=0
    # Q2: simpler structural fact -- is le0 M (j0+sp) (j0+s) <=> le0 M (j0+sp') ... determined by base chain?
    # we test: for pM < j0+sp <= u, le0 M (j0+sp) u holds.
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
        for s in range(1,w):
            u=j0+s
            if not hasParent(M,1,u): continue
            pM=parent(M,1,u)
            if pM is None or pM<j0: continue
            # all sp with pM<j0+sp<=u
            for sp in range(s+1):
                node=j0+sp
                if not(pM<node<=u): continue
                cTotal+=1
                if node<L and u<L and Rm[node][u]:
                    cLe0+=1
                else:
                    cNoLe0+=1
                    if len(bad)<20: bad.append((fmt(M),s,sp,pM-j0))
    print("nodes pM<j0+sp<=u total:", cTotal, " le0 M node u:", cLe0, " NO le0:", cNoLe0)
    print("--- bad (no le0 within (pM,u]) ---")
    for e in bad: print(e)

if __name__=="__main__":
    main()

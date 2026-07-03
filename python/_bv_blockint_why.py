#!/usr/bin/env python3
"""Why entry M 1 (j0+ss) >= entry M 1 j0 for block-interior preds (ss>0, jp in block qq<=q)?
Candidate reasons:
 (a) le0 M j0 (j0+ss) (forward within-block row-0 reach) + M-valley of nextrel1 M pj j0
     does NOT directly apply (valley is about predecessors of j0).
 (b) Actually jp=j0+qq*w+ss is a le0(N)-predecessor of z=j0+q*w. Reflect: is le0 N jp z
     => something. jp in block qq, z in block q, qq<=q. The reflection: entry N 1 jp = entry M 1(j0+ss).
     We want >= entry M 1 j0.
 Test: is it because le0 N (j0+qq*w) jp ... no.
 Simpler: maybe the real reflected M-fact is le0 M (j0+ss') j0 for the prefix-only part, and
 block-interior actually reflect to a prefix M-column via... no, j0+ss>j0.
 Let me check: does le0 M (j0+ss) (j0+w=j1) hold? i.e. is j0+ss on the way up to j1 (the ramp)?
 And entry M 1 j0 <= entry M 1 (j0+ss) because the row-1 is monotone on [j0,j1]? Check row1 mono on block."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,le0,nextrel1,idx1,hasParent,parent,oper,diagSeq)
from _boundary_valley_B import gen_closure

def check(depth,umax,vmax,maxlen,maxn):
    base=gen_closure(depth,umax,vmax,maxlen,maxn)
    # for each M (d1pos boundary), check structural facts on M-side [j0,j1]:
    row1_mono_ok=0; row1_mono_no=0  # entry M 1 (j0+t) >= entry M 1 j0 for all 0<=t<=w?
    le0_j0_ok=0; le0_j0_no=0        # le0 M j0 (j0+t)?
    fails=[]
    for M in base:
        nm=Lng(M)
        if nm<2: continue
        j1M=nm-1
        if not hasParent(M,1,j1M): continue
        j0=parent(M,1,j1M)
        if j0 is None or not(j0<j1M): continue
        if entry(M,0,j1M)==0 and entry(M,1,j1M)==0: continue
        if idx1(M,j1M)!=1: continue
        if not hasParent(M,1,j0): continue
        pj=parent(M,1,j0)
        if pj is None or not(pj<j0): continue
        w=j1M-j0
        for t in range(0,w+1):
            if entry(M,1,j0+t)>=entry(M,1,j0): row1_mono_ok+=1
            else: row1_mono_no+=1; fails.append(("row1",tuple(map(tuple,M)),t,entry(M,1,j0+t),entry(M,1,j0)))
            if le0(M,j0,j0+t): le0_j0_ok+=1
            else: le0_j0_no+=1
    return row1_mono_ok,row1_mono_no,le0_j0_ok,le0_j0_no,fails

if __name__=='__main__':
    a,b,c,d,f=check(3,2,4,11,3)
    print("row1 entry M 1 (j0+t)>=entry M 1 j0 on [j0,j1]: ok=%d no=%d"%(a,b))
    print("le0 M j0 (j0+t) on [j0,j1]: ok=%d no=%d"%(c,d))
    for x in f[:8]: print("  ",x)

#!/usr/bin/env python3
"""TASK 2: the boundary valley clause of oper_parent1_readback_boundary.
N=M[n]. block-start z = j0+q*w (s=0).  pj = parent M 1 j0 (in prefix).
Valley clause to prove:  for all j' with pj<j' and le0 N j' z:
    entry N 1 z <= entry N 1 j'.
We need to show this from M-side facts. The predecessors j' are cross-block.
Test the reflection: le0 N j' z (j' a predecessor of block-start z) reflects to
an M-side le0, and M's row-1 maximality at j0 gives the bound.

Key question: classify j' predecessors and check whether
   entry N 1 j' >= entry N 1 z  (= entry M 1 j0)
always holds, and via WHICH M-side fact (which column does j' read back to)."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,le0,nextrel1,idx1,hasParent,parent,oper,diagSeq)

def gen_closure(depth,umax,vmax,maxlen,max_n):
    seen=set(); frontier=[]
    for u in range(0,umax+1):
        for v in range(u,vmax+1):
            d=tuple(map(tuple,diagSeq(u,v)))
            if d not in seen and len(d)<=maxlen:
                seen.add(d); frontier.append([list(x) for x in d])
    allM=list(frontier)
    for _ in range(depth):
        newf=[]
        for M in frontier:
            for n in range(1,max_n+1):
                N=oper([tuple(x) for x in M],n); t=tuple(map(tuple,N))
                if t not in seen and 1<len(t)<=maxlen:
                    seen.add(t); newf.append([list(x) for x in N]); allM.append([list(x) for x in N])
        frontier=newf
        if not frontier: break
    return allM

def check(depth,umax,vmax,maxlen,maxn):
    base=gen_closure(depth,umax,vmax,maxlen,maxn)
    valley_tot=0; valley_fail=[]
    # classify predecessors j' by region:
    prefix_pred=0; block_pred=0; samestart=0
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
        for n in range(1,maxn+1):
            N=oper([tuple(x) for x in M],n)
            if Lng(N)<2: continue
            for q in range(0,n):
                z=j0+q*w
                if z>=Lng(N): continue
                ez=entry(N,1,z)
                for jp in range(0,Lng(N)):
                    if not(pj<jp): continue
                    if not le0(N,jp,z): continue
                    valley_tot+=1
                    ejp=entry(N,1,jp)
                    if not(ejp>=ez):
                        valley_fail.append((tuple(map(tuple,M)),n,q,z,jp,ez,ejp))
                    # region of jp
                    if jp<j0: prefix_pred+=1
                    else:
                        qq=(jp-j0)//w; ss=(jp-j0)-qq*w
                        if ss==0: samestart+=1
                        else: block_pred+=1
    return valley_tot,valley_fail,prefix_pred,block_pred,samestart

if __name__=='__main__':
    for cfg in [(3,2,4,11,3)]:
        vt,vf,pp,bp,ss=check(*cfg)
        print(f"cfg{cfg}: boundary-valley cases={vt} fails={len(vf)}")
        print(f"   pred regions: prefix={pp} block-interior={bp} block-start={ss}")
        for f in vf[:8]: print("   VFAIL",f)

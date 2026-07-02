#!/usr/bin/env python3
"""The z<j0M (prefix) interior-gated case: how does Ez_N(z) relate to M?
N=M[n]. z<j0M is in N's prefix (reads M verbatim for cols<j0M).
j1N is in tiling. Ez_N(z): entry N 0 j1N = entry N 0 z + (j1N - z).
Since entry N 0 z = entry M 0 z (prefix), and entry N 0 j1N = (tiling endpoint),
test whether Ez_N(z) <=> [Ez_M(z) on M's OWN endpoint j1M]  combined with the
block-count carry. Specifically does the prefix z's row-1 parent pz read back to
an M-side parent (also a prefix node), giving M-side gating + M-side Ez?"""
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
    # for prefix interior-gated z (z<j0M), record:
    #  (a) does z have an M-side row-1 parent equal to pz (prefix readback)?
    #  (b) is z interior-gated IN M too (pz_M>j0M? no -- M's j0 is j0M; but z<j0M so pz<z<j0M < j0M? )
    #  Actually in M, the endpoint is j1M; z<j0M is interior of M as well.
    #  Test: Ez_N(z) computed; and the M-relative statement.
    tot=0; samepar=0; mism=[]
    EzN_true=0
    for M in base:
        nm=Lng(M)
        if nm<2: continue
        j1M=nm-1
        if not hasParent(M,1,j1M): continue
        j0M=parent(M,1,j1M)
        if j0M is None or not(j0M<j1M): continue
        if entry(M,0,j1M)==0 and entry(M,1,j1M)==0: continue
        if idx1(M,j1M)!=1: continue
        w=j1M-j0M
        for n in range(1,maxn+1):
            N=oper([tuple(x) for x in M],n)
            if Lng(N)<2: continue
            jN=Lng(N)-1
            if not hasParent(N,1,jN): continue
            j0N=parent(N,1,jN)
            if j0N is None: continue
            for z in range(j0N+1,jN):
                if z>=j0M: continue
                if not hasParent(N,1,z): continue
                pz=parent(N,1,z)
                if pz is None or not(pz>j0N): continue
                tot+=1
                EzN=(entry(N,0,jN)==entry(N,0,z)+(jN-z))
                if EzN: EzN_true+=1
                # M-side row-1 parent of z (z<j0M, prefix)
                pzM=parent(M,1,z) if hasParent(M,1,z) else None
                if pzM==pz: samepar+=1
                else: mism.append((tuple(map(tuple,M)),n,z,pz,pzM,j0N,j0M))
    return tot,samepar,EzN_true,mism

if __name__=='__main__':
    for cfg in [(3,2,4,11,3),(4,2,4,13,3)]:
        tot,sp,ezt,mism=check(*cfg)
        print(f"cfg{cfg}: prefix-gated z<j0M cases={tot}  EzN_true={ezt}  pz==pzM(prefix readback)={sp}")
        for m in mism[:6]: print("   PARMISM",m)

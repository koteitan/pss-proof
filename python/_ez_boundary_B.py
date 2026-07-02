#!/usr/bin/env python3
"""Do interior gated nodes (pz>j0N) ever land on a block boundary (s=0)?
And what is j0N in terms of M?  Determines whether TASK1 needs the boundary valley."""
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
    s0=0; sgt0=0; j0N_eq_j0M=0; j0N_other=0; bdyfail=[]
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
            if j0N==j0M: j0N_eq_j0M+=1
            else: j0N_other+=1
            for z in range(j0N+1,jN):
                if not hasParent(N,1,z): continue
                pz=parent(N,1,z)
                if pz is None or not(pz>j0N): continue
                if z<j0M:
                    bdyfail.append(("z<j0M",tuple(map(tuple,M)),n,z,j0M))
                    continue
                q=(z-j0M)//w; s=(z-j0M)-q*w
                if s==0: s0+=1
                else: sgt0+=1
    return s0,sgt0,j0N_eq_j0M,j0N_other,bdyfail

if __name__=='__main__':
    for cfg in [(3,2,4,11,3),(4,2,4,13,3)]:
        s0,sgt0,a,b,bf=check(*cfg)
        print(f"cfg{cfg}: interior-gated on s=0(boundary)={s0}  s>0(interior)={sgt0}")
        print(f"         j0N==j0M:{a}  j0N!=j0M:{b}  z<j0M-cases:{len(bf)}")
        for f in bf[:4]: print("   ",f)

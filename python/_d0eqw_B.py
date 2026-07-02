#!/usr/bin/env python3
"""Is d0==w FORCED for any M in ST_PS with i1=1 parent j0 of j1M?
i.e. entry M0 j1M - entry M0 j0 == j1M - j0  (the M-side block is a +1 ramp).
If YES universally, then the in-block Ez lift needs NO recursion -- it's a flat fact.
Test on the broad closure (ALL M, not just gated)."""
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
    tot=0; fail=[]
    for M in base:
        nm=Lng(M)
        if nm<2: continue
        j1M=nm-1
        if not hasParent(M,1,j1M): continue
        j0=parent(M,1,j1M)
        if j0 is None or not(j0<j1M): continue
        if entry(M,0,j1M)==0 and entry(M,1,j1M)==0: continue
        if idx1(M,j1M)!=1: continue
        w=j1M-j0
        d0=entry(M,0,j1M)-entry(M,0,j0)
        tot+=1
        if d0!=w: fail.append((tuple(map(tuple,M)),j0,j1M,d0,w))
    return tot,fail

if __name__=='__main__':
    for cfg in [(5,3,6,14,4),(5,2,5,16,5),(6,3,6,16,3)]:
        tot,fail=check(*cfg)
        print(f"cfg{cfg}: M with i1=1 parent : {tot} cases, d0!=w fails={len(fail)}")
        for f in fail[:8]: print("   FAIL",f)

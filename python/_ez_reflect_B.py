#!/usr/bin/env python3
"""Verify the oper-step reflection structure for Ez induction (TASK B).

For N = M[n] (M in broad ST_PS closure, n>=1), take an interior row-1 node z of N:
  j0N = parent N 1 (LngN-1),  j0N < z < LngN-1,  hasParent N 1 z,  parent N 1 z > j0N.
Decompose z in the oper tiling of M.  Check:
 (A) Ez_N(z) :  entry N 0 (j1N) = entry N 0 z + (j1N - z)
 (B) the reflection: does Ez_N(z) coincide with an M-side fact?

KEY ALTERNATIVE: maybe Ez is EASIER as a *direct* row-0 ramp claim, independent of
the row-1 ancestor.  Let's also test: for ANY interior z with j0N<z<j1N and the
row-0 +1 ramp on [z,j1N], i.e. is the +1 ramp exactly the set of z that are on the
row-0 trunk reaching j1N (le0 N z j1N)?  We test whether
  (parent N 1 z > j0N) ==> le0 N z (j1N)   [the gating that the task says is local]
"""
import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,le0,le1,nextrel1,idx1,hasParent,parent,oper,diagSeq)

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

def check(allM):
    # claim G: (interior z, parent N 1 z > j0) ==> le0 N z j1
    gtot=0; gfail=[]
    # claim Gamma: (interior z, parent N 1 z > j0) ==> Ez
    etot=0; efail=[]
    # claim H: le0 N z j1 ==> Ez (the row-0 ramp from reach) -- already a GREEN brick path
    htot=0; hfail=[]
    for M in allM:
        n=Lng(M)
        if n<2: continue
        j1=n-1
        if not hasParent(M,1,j1): continue
        j0=parent(M,1,j1)
        if j0 is None or not(j0<j1): continue
        for z in range(j0+1,j1):
            if not hasParent(M,1,z): continue
            pz=parent(M,1,z)
            if pz is None or not(pz>j0): continue
            gtot+=1
            r=le0(M,z,j1)
            if not r: gfail.append((tuple(map(tuple,M)),z,j0,pz))
            etot+=1
            Ez=(entry(M,0,j1)==entry(M,0,z)+(j1-z))
            if not Ez: efail.append((tuple(map(tuple,M)),z,j0,pz))
    return (gtot,gfail),(etot,efail)

if __name__=='__main__':
    for cfg in [(5,3,6,14,4),(6,3,6,16,3),(5,2,5,16,5)]:
        allM=gen_closure(*cfg)
        (gt,gf),(et,ef)=check(allM)
        print(f"cfg{cfg}: closure={len(allM)}")
        print(f"   G:(pz>j0)=>le0 z j1 : {gt} cases, {len(gf)} fails")
        for f in gf[:4]: print("     Gfail",f)
        print(f"   Ez:(pz>j0)=>Ez      : {et} cases, {len(ef)} fails")
        for f in ef[:4]: print("     Efail",f)

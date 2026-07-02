#!/usr/bin/env python3
"""Verify the IN-BLOCK Ez lift arithmetic precisely (s>0), for a standalone brick.

N=M[n], j1M=LngM-1, j0=parent M 1 j1M, w=j1M-j0, d0=entry M0 j1M - entry M0 j0.
The endpoint of N: j1N = LngN-1 = j0 + n*w - 1  (the last column).
An in-block z = j0 + q*w + s with 0<s<w, q<n.

Row-0 readback (oper_gen_block_entry0): entry N 0 (j0+q*w+s) = entry M0 (j0+s) + q*d0.
The endpoint j1N = j0+n*w-1 = j0+(n-1)*w + (w-1). So endpoint is block q=n-1, s=w-1.
entry N 0 j1N = entry M0 (j0+(w-1)) + (n-1)*d0 = entry M0 (j1M-1) + (n-1)*d0.

Ez_N(z): entry N0 j1N = entry N0 z + (j1N - z).
 LHS = entry M0(j1M-1) + (n-1)*d0
 entry N0 z = entry M0(j0+s) + q*d0
 j1N - z = (j0+n*w-1) - (j0+q*w+s) = (n-1-q)*w + (w-1-s)
So Ez_N(z) <=>
 entry M0(j1M-1)+(n-1)*d0 = entry M0(j0+s)+q*d0 + (n-1-q)*w + (w-1-s)
 <=> entry M0(j1M-1) - entry M0(j0+s) + (n-1-q)*d0 = (n-1-q)*w + (w-1-s)
Hmm d0 = entry M0 j1M - entry M0 j0. And the M-side +1 ramp on [j0+s, j1M] would give
 entry M0 j1M = entry M0(j0+s) + (j1M - (j0+s)) = entry M0(j0+s) + (w-s).
That's EzM at the reflected child zp=j0+s.
We test: does EzN(z)  <=>  [EzM(zp) AND the M-side +1 ramp also gives entry M0(j1M-1)=entry M0 j1M -1]?
i.e. is it sufficient that the WHOLE M-tail [j0, j1M] is a +1 ramp (d0=w)?
"""
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
    # For in-block gated z (s>0), test the hypothesis:
    #   EzN(z) <=> d0==w  (the whole M block [j0,j1M] is a +1 ramp)
    tot=0; mism=[]; d0eqw_count=0
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
        for n in range(1,maxn+1):
            N=oper([tuple(x) for x in M],n)
            if Lng(N)<2: continue
            jN=Lng(N)-1
            if not hasParent(N,1,jN): continue
            j0N=parent(N,1,jN)
            if j0N is None: continue
            for z in range(j0N+1,jN):
                if z<j0: continue
                q=(z-j0)//w; s=(z-j0)-q*w
                if s==0: continue
                if not hasParent(N,1,z): continue
                pz=parent(N,1,z)
                if pz is None or not(pz>j0N): continue
                tot+=1
                EzN=(entry(N,0,jN)==entry(N,0,z)+(jN-z))
                hyp=(d0==w)
                if EzN!=hyp: mism.append((tuple(map(tuple,M)),n,z,q,s,d0,w,EzN))
                if d0==w: d0eqw_count+=1
    return tot,mism,d0eqw_count

if __name__=='__main__':
    for cfg in [(3,2,4,11,3),(4,2,4,13,3)]:
        tot,mism,c=check(*cfg)
        print(f"cfg{cfg}: in-block gated z(s>0) cases={tot}  d0==w count={c}  EzN<->(d0==w) mism={len(mism)}")
        for m in mism[:8]: print("   MISM",m)

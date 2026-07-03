#!/usr/bin/env python3
"""The oper-step reflection for Ez induction.

N = M[n].  Let j1M=LngM-1, j0M=parent M 1 j1M, w=j1M-j0M.
Interior row-1 node z of N with j0N<z<j1N=LngN-1, pz=parent N 1 z > j0N.

The oper tiling: N's columns j0N..j1N are n tiled copies of M's block [j0M,j1M).
We want to show: Ez_N(z) follows from M-side facts.

Strategy verification: the readback (oper_parent1_readback) gives
   parent N 1 (j0M + q*w + s) = parent M 1 (j0M+s) + q*w   (for s in 0..w-1).
So z = j0M + q*w + s (block q, offset s, 0<s<w), and pz reflects to pM=parent M 1 (j0M+s).
pz>j0N  <=>  pM+q*w > j0M  ... but j0N=parent N 1 j1N. What is j0N?

Let's empirically RELATE Ez_N(z) to Ez_M(z') where z' = j0M+s (the M-side child).
Test: Ez_N at z=(j0M+q*w+s)  iff  Ez_M at (j0M+s) AND the +1 carry across blocks.

Actually Ez_N(z): entry N 0 j1N = entry N 0 z + (j1N - z).
The row-0 readback (oper_gen_block_entry0, d0): on block q, entry N 0 (j0M+q*w+s)
  = entry M 0 (j0M+s) + q*d0, where d0 = entry M 0 j1M - entry M 0 j0M (i1=1 case).
The endpoint j1N = j0M + (n-1)*w + (w-1)+? Actually structure depends. Let's just
measure what j0N, j1N look like and whether the tail of N is a +1 ramp from z.
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

def reflect(depth,umax,vmax,maxlen,maxn):
    # build base set then take oper steps explicitly so we KNOW M and n
    base=gen_closure(depth,umax,vmax,maxlen,maxn)
    # claim R: for N=M[n], interior z=(j0M+q*w+s), pz>j0N
    #   Ez_N(z) <=> (s==... ) measure how z' = j0M+s relates to M's endpoint ramp
    rtot=0; rfail=[]
    # claim: the M-side reflected node z'=j0M+s satisfies: is z' on M's +1 ramp to j1M?
    #   i.e. entry M 0 j1M = entry M 0 (j0M+s) + (j1M-(j0M+s))  == Ez_M at (j0M+s)
    # AND across-block the +1 chains. Test combined:
    mtot=0; mfail=[]
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
                if not hasParent(N,1,z): continue
                pz=parent(N,1,z)
                if pz is None or not(pz>j0N): continue
                # decompose z relative to tiling: z>=j0M
                if z<j0M: continue
                q=(z-j0M)//w; s=(z-j0M)-q*w
                if s==0: continue   # boundary handled separately
                rtot+=1
                EzN=(entry(N,0,jN)==entry(N,0,z)+(jN-z))
                # M-side: is the reflected child j0M+s on M's +1 ramp to j1M with pz_M>j0M?
                zp=j0M+s
                EzM=(entry(M,0,j1M)==entry(M,0,zp)+(j1M-zp))
                pzM = parent(M,1,zp) if hasParent(M,1,zp) else None
                gateM = (pzM is not None and pzM>j0M)
                # Reflection claim: EzN holds  AND  (EzN <-> q==n-1 component? )
                # record mismatch between EzN and EzM (the IH-target)
                if EzN!=EzM:
                    rfail.append((tuple(map(tuple,M)),n,z,q,s,j0N,jN,pz,EzN,EzM,gateM))
                # also: does pz>j0N reflect to gateM (M-side strict ancestor)?
                mtot+=1
                if EzN and not gateM:
                    mfail.append(("gate",tuple(map(tuple,M)),n,z,q,s,pz,j0N))
    return (rtot,rfail),(mtot,mfail)

if __name__=='__main__':
    for cfg in [(3,2,4,11,3)]:
        (rt,rf),(mt,mf)=reflect(*cfg)
        print(f"cfg{cfg}:")
        print(f"  EzN <-> EzM(reflected child) : {rt} cases, {len(rf)} mismatch")
        for f in rf[:6]: print("    MISMATCH",f)
        print(f"  EzN => gateM(pzM>j0M)        : {mt} cases, {len(mf)} fails")
        for f in mf[:6]: print("    GATEFAIL",f)

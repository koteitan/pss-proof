#!/usr/bin/env python3
"""Check the reflection mechanism for each predecessor region.
For jp a le0-predecessor of z=j0+q*w with pj<jp:
 - prefix (jp<j0): entry N 1 jp = entry M 1 jp (verbatim). Need entry M 1 jp >= entry M 1 j0.
   Claim: le0 N jp z reflects to le0 M jp j0, and pj<jp gives M-valley => entry M 1 j0 <= entry M 1 jp. GOOD.
 - block jp=j0+qq*w+ss (ss>0, qq<=q): entry N 1 jp = entry M 1 (j0+ss) (periodic, d1=0).
   Need entry M 1 (j0+ss) >= entry M 1 j0. Reflect to le0 M (j0+ss) j0?? but j0+ss>j0. Hmm.
 - block-start jp=j0+qq*w (ss=0): entry N 1 jp = entry M 1 j0 = entry N 1 z. Equality. GOOD trivially.
Let's verify each branch's reflection target and the M-side fact used."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,le0,nextrel1,idx1,hasParent,parent,oper,diagSeq)
from _boundary_valley_B import gen_closure

def check(depth,umax,vmax,maxlen,maxn):
    base=gen_closure(depth,umax,vmax,maxlen,maxn)
    # For block-interior preds, check M-side: is le0 M (j0+ss) j0?  (would be backwards).
    # Instead check: does entry M 1 (j0+ss) >= entry M 1 j0 hold, and is le0 M jp_reflected j0?
    fail_prefix=[]; fail_blockint=[];
    # also check: for prefix preds, le0 M jp j0 holds?
    prefix_le0M_ok=0; prefix_le0M_no=0
    blockint_ge_ok=0; blockint_ge_no=0
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
                    if jp<j0:
                        # prefix: check le0 M jp j0
                        if le0(M,jp,j0): prefix_le0M_ok+=1
                        else:
                            prefix_le0M_no+=1; fail_prefix.append((n,q,jp,j0))
                    else:
                        qq=(jp-j0)//w; ss=(jp-j0)-qq*w
                        if ss==0: continue
                        # block interior: entry M 1 (j0+ss) >= entry M 1 j0 ?
                        if entry(M,1,j0+ss)>=entry(M,1,j0): blockint_ge_ok+=1
                        else:
                            blockint_ge_no+=1; fail_blockint.append((n,q,jp,ss,entry(M,1,j0+ss),entry(M,1,j0)))
    return (prefix_le0M_ok,prefix_le0M_no,fail_prefix,
            blockint_ge_ok,blockint_ge_no,fail_blockint)

if __name__=='__main__':
    r=check(3,2,4,11,3)
    print("prefix le0 M jp j0:  ok=%d no=%d"%(r[0],r[1]))
    for f in r[2][:8]: print("  PFAIL",f)
    print("blockint entry M 1 (j0+ss)>=entry M 1 j0: ok=%d no=%d"%(r[3],r[4]))
    for f in r[5][:8]: print("  BFAIL",f)

#!/usr/bin/env python3
"""For prefix preds jp<j0 of z=j0+q*w: check le0 N jp z holds AND le0 N jp j0 holds.
By row-0 confinement, a predecessor of block-start z=j0+q*w that lies in prefix must
reach z through j0. Check: le0 N jp z => le0 N jp j0 (since j0 is on the path? j0<=z and j0
is block-start 0). Actually le0 N jp z and jp<j0<=z: is le0 N jp j0?
Then le0 N jp j0 = le0 M jp j0 (prefix agreement, both <=j0)."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,le0,nextrel1,idx1,hasParent,parent,oper,diagSeq)
from _boundary_valley_B import gen_closure

def check(depth,umax,vmax,maxlen,maxn):
    base=gen_closure(depth,umax,vmax,maxlen,maxn)
    jpj0_ok=0; jpj0_no=0; fails=[]
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
                for jp in range(0,j0):  # prefix
                    if not(pj<jp): continue
                    if not le0(N,jp,z): continue
                    # claim le0 N jp j0
                    if le0(N,jp,j0): jpj0_ok+=1
                    else: jpj0_no+=1; fails.append((n,q,jp,j0,z))
    return jpj0_ok,jpj0_no,fails

if __name__=='__main__':
    a,b,f=check(3,2,4,11,3)
    print("prefix pred: le0 N jp j0 (given le0 N jp z): ok=%d no=%d"%(a,b))
    for x in f[:8]: print("  ",x)

#!/usr/bin/env python3
"""Check whether for block-interior reflect we can use le1_ances_aux on chain nextrel1 M j0 j1:
needs le0 M (j0+ss) j1 (i.e. j0+ss is on the row-0 ramp up to j1)."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,le0,nextrel1,idx1,hasParent,parent,oper,diagSeq)
from _boundary_valley_B import gen_closure

def check(depth,umax,vmax,maxlen,maxn):
    base=gen_closure(depth,umax,vmax,maxlen,maxn)
    le0_t_j1_ok=0; le0_t_j1_no=0
    nr1j0j1_ok=0; nr1j0j1_no=0
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
        if nextrel1(M,j0,j1M): nr1j0j1_ok+=1
        else: nr1j0j1_no+=1
        for t in range(0,w+1):
            if le0(M,j0+t,j1M): le0_t_j1_ok+=1
            else: le0_t_j1_no+=1
    return le0_t_j1_ok,le0_t_j1_no,nr1j0j1_ok,nr1j0j1_no

if __name__=='__main__':
    a,b,c,d=check(3,2,4,11,3)
    print("le0 M (j0+t) j1 on [j0,j1]: ok=%d no=%d"%(a,b))
    print("nextrel1 M j0 j1: ok=%d no=%d"%(c,d))

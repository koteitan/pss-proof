#!/usr/bin/env python3
"""Empirical check of Ez and the oper-step reflection for TASK B.

Ez: entry N 0 (Lng N-1) = entry N 0 z + ((Lng N-1) - z)   at interior row-1 node z
with hasParent N 1 z and parent N 1 z > j0 = parent N 1 (Lng N-1).

We build a BROAD ST_PS closure: diag(u,v) bases + oper closure depth>=5.
NOT is_standard. maxlen 14-16.
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng, entry, le0, le1, nextrel1, idx1, hasParent, parent,
                       oper, diagSeq)

def gen_closure(depth, umax, vmax, maxlen, max_n):
    seen=set()
    frontier=[]
    for u in range(0, umax+1):
        for v in range(u, vmax+1):
            d=tuple(map(tuple, diagSeq(u,v)))
            if d not in seen and len(d)<=maxlen:
                seen.add(d); frontier.append([list(x) for x in d])
    allM=list(frontier)
    for _ in range(depth):
        newf=[]
        for M in frontier:
            for n in range(1, max_n+1):
                N=oper([tuple(x) for x in M], n)
                if N is None: continue
                t=tuple(map(tuple,N))
                if t not in seen and 1<len(t)<=maxlen:
                    seen.add(t); newf.append([list(x) for x in N]); allM.append([list(x) for x in N])
        frontier=newf
        if not frontier: break
    return allM

def check_Ez(allM):
    fails=[]; total=0
    for M in allM:
        n=Lng(M)
        if n<2: continue
        j1=n-1
        if not hasParent(M,1,j1): continue
        j0=parent(M,1,j1)
        if j0 is None or not (j0 < j1): continue
        # interior z: j0 < z < j1, hasParent N 1 z, parent N 1 z > j0
        for z in range(j0+1, j1):
            if not hasParent(M,1,z): continue
            pz=parent(M,1,z)
            if pz is None or not (pz > j0): continue
            total+=1
            lhs=entry(M,0,j1); rhs=entry(M,0,z)+(j1-z)
            if lhs!=rhs:
                fails.append((tuple(map(tuple,M)),z,j0,pz,lhs,rhs))
    return total, fails

if __name__=='__main__':
    for (depth,umax,vmax,maxlen,maxn) in [(5,3,6,14,4),(6,3,6,16,3),(5,2,5,16,5)]:
        allM=gen_closure(depth,umax,vmax,maxlen,maxn)
        total,fails=check_Ez(allM)
        print(f"cfg depth={depth} umax={umax} vmax={vmax} maxlen={maxlen} maxn={maxn}: "
              f"closure={len(allM)} Ez-cases={total} fails={len(fails)}")
        for f in fails[:6]:
            print("  FAIL:", f)

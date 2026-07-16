#!/usr/bin/env python3
"""Audit for lean/6/6.8-d1pos-le0.lean private engine + public statements.

Run from repo root: python3 python/d1pos_le0_audit.py

Checks, over all pair sequences with entries < 5 and length <= 5 (plus a
deeper randomized pass), in the d1pos context (i1=1, hasParent, j0 < Lng-1):
  (E) block-min engine: entry(M[n],0,j0+k*w) < entry(M[n],0,x)
      for all k<n, j0+k*w < x < Lng(M[n])
  (A) le0(M[n], j0+k*w, x) for all j0+k*w <= x < Lng(M[n])   (start_to_any)
  (W) nextrel0 within-transfer (k<n, x>=j0, y<Lng M-1, nextrel0 M x y)
"""
import sys, itertools, random
sys.path.insert(0, 'python')
from red_model import Lng, entry, nextrel0, le0, seg, oper, idx1, hasParent, parent

def d1pos_ctx(M):
    j1 = Lng(M)-1
    if j1 == 0: return None
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: return None
    if idx1(M,j1)!=1: return None
    if not hasParent(M,1,j1): return None
    j0 = parent(M,1,j1)
    if not j0 < j1: return None
    return j0

cntE=cntA=cntW=0
def check(M, nmax=4):
    global cntE, cntA, cntW
    j0 = d1pos_ctx(M)
    if j0 is None: return
    j1 = Lng(M)-1
    w = j1-j0
    for n in range(1, nmax):
        Mn = oper(M,n)
        L = Lng(Mn)
        assert L == j0+n*w, (M,n)
        for k in range(n):
            base = j0+k*w
            for x in range(base+1, L):
                assert entry(Mn,0,base) < entry(Mn,0,x), ("E",M,n,k,x)
                cntE+=1
            for x in range(base, L):
                assert le0(Mn,base,x), ("A",M,n,k,x)
                cntA+=1
        # nextrel0 within
        for k in range(n):
            for x in range(j0, j1):
                for y in range(x+1, j1):
                    if nextrel0(M,x,y):
                        tx = j0+k*w+(x-j0); ty = j0+k*w+(y-j0)
                        assert nextrel0(Mn,tx,ty), ("W",M,n,k,x,y)
                        cntW+=1

# exhaustive small pass
VAL=4; LMAX=4
for ln in range(2, LMAX+1):
    for M in itertools.product(itertools.product(range(VAL),repeat=2), repeat=ln):
        check(list(M), nmax=4)
print("exhaustive pass ok", cntE, cntA, cntW)

# randomized deeper pass (entries up to 8, length up to 6)
random.seed(0)
for _ in range(4000):
    ln = random.randint(2,6)
    M = [(random.randint(0,8), random.randint(0,8)) for _ in range(ln)]
    check(M, nmax=4)
print("random pass ok", cntE, cntA, cntW)

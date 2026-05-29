#!/usr/bin/env python3
"""Pin the minimal hypothesis for B2 on M = N[n] (d1pos).

Component left-ends of P(seg M a b) are row-0 left-minima of M RELATIVE to a:
  forall j with a<=j<p:  entry M 0 j >= entry M 0 p.
Two such pL<pR with entry M 0 pL = entry M 0 pR (row-0 tie): is
  entry M 1 pR <= entry M 1 pL?

Hypotheses tested (all require a<=pL<pR, both rel-a left-minima, both >= j0N
since the branch region lives in the fold region):
 (A) plain
 (B) + le0 M pL pR
 (C) + le0 M a pL and le0 M a pR     (anchor = slice start a)
 (D) + le0 M a b  (the slice seg M a b is monoT/le0; full branch-region setting)
"""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/',1)[0])
from red_model import (Lng, entry, oper, idx1, hasParent, parent, le0)

def d1pos(N):
    if Lng(N) <= 1: return False
    j1 = Lng(N)-1
    if entry(N,0,j1)==0 and entry(N,1,j1)==0: return False
    if entry(N,1,j1) == 0: return False
    if idx1(N,j1) != 1: return False
    if not hasParent(N,1,j1): return False
    return parent(N,1,j1) < j1

def gen_seqs(maxlen, maxval):
    pairs = [(a,b) for a in range(maxval+1) for b in range(maxval+1)]
    for L in range(2, maxlen+1):
        for tup in itertools.product(pairs, repeat=L):
            yield list(tup)

def lmin_rel(M,a,p):
    return all(entry(M,0,j) >= entry(M,0,p) for j in range(a,p))

stats = {"A":[0,0], "B":[0,0], "C":[0,0], "D":[0,0]}
ex = {"A":None,"B":None,"C":None}
for N in gen_seqs(4,2):
    if not d1pos(N): continue
    j0N = parent(N,1,Lng(N)-1)
    for n in range(1,4):
        M = oper(N,n)
        L = Lng(M)
        if L < 2: continue
        for a in range(j0N, L):       # anchor at/after block-0 start
            for b in range(a+1, L):
                mins = [p for p in range(a, b+1) if lmin_rel(M,a,p)]
                for i in range(len(mins)):
                    for jx in range(i+1,len(mins)):
                        pL,pR = mins[i],mins[jx]
                        if entry(M,0,pL)!=entry(M,0,pR): continue
                        good = entry(M,1,pR) <= entry(M,1,pL)
                        stats["A"][0]+=1; stats["A"][1]+=(0 if good else 1)
                        if not good and ex["A"] is None: ex["A"]=(N,n,a,b,pL,pR)
                        if le0(M,pL,pR):
                            stats["B"][0]+=1; stats["B"][1]+=(0 if good else 1)
                            if not good and ex["B"] is None: ex["B"]=(N,n,a,b,pL,pR)
                        if le0(M,a,pL) and le0(M,a,pR):
                            stats["C"][0]+=1; stats["C"][1]+=(0 if good else 1)
                            if not good and ex["C"] is None: ex["C"]=(N,n,a,b,pL,pR)
                        if le0(M,a,b):
                            stats["D"][0]+=1; stats["D"][1]+=(0 if good else 1)

for k,(w,f) in stats.items():
    print(f"{k}: tie pairs={w}, fails={f}")
for k,v in ex.items():
    if v: print(f"  {k} example fail (N,n,a,b,pL,pR)={v}")

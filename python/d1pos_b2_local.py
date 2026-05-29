#!/usr/bin/env python3
"""Re-verify the B2b structural discovery for the §6.8 d0pos (i1=1) row-1 tie-break.

Findings to confirm (over row-0 tie pairs of consecutive P-components of the
branch region Yp = P(seg M' (TrMax M'+1) (Lng M'-1)), M' a monoT slice of
M = oper(N,n), N standard d1pos):
  (S-adj)  consecutive tie components are M-adjacent: pR == pL+1
  (S-sgl)  the LEFT tie component is a singleton: Lng = 1
  (M-loc)  THE real B2 target, M-local:  for adjacent p,p+1 that are a P-cut
           boundary with the left a singleton and entry M' 0 (..) tied,
           entry 1 (right) <= entry 1 (left).
  (N-loc)  the irreducible core, N-local adjacent-tie:
           in standard N, adjacent cells j,j+1 with entry N 0 j == entry N 0 (j+1)
           ==> entry N 1 (j+1) <= entry N 1 j.
Also test whether (N-loc) reduces to anything cheap (nextrel0 parent, monoT).
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent,
                       parent, monoT, zeroT, is_standard, nextrel0, le0, fmt)

def gen_seqs(maxlen, maxval):
    for L in range(2, maxlen+1):
        for cells in itertools.product(
                [(a,b) for a in range(maxval+1) for b in range(maxval+1)], repeat=L):
            yield list(cells)

def is_d1pos(N):
    j1 = Lng(N)-1
    if j1 < 1: return False
    if entry(N,0,j1)==0 and entry(N,1,j1)==0: return False
    if idx1(N,j1)!=1: return False
    return hasParent(N,1,j1)

def monoT_slices(M):
    n=Lng(M)
    for a in range(n):
        for b in range(a+1, n):
            s=seg(M,a,b)
            if monoT(s): yield a,b,s

def check():
    stats=dict(witnesses=0, tiepairs=0, adj_fail=0, sgl_fail=0, mloc_fail=0)
    nloc=dict(pairs=0, fail=0, parent_ok=0, notparent=0)
    for N in gen_seqs(5,2):
        if not is_d1pos(N): continue
        if not is_standard(N): continue
        for n in (1,2,3):
            M=oper(N,n)
            if Lng(M)<2: continue
            for a,b,Mp in monoT_slices(M):
                t=TrMax(Mp)
                if t==Lng(Mp)-1: continue           # Br empty
                Yp=seg(Mp, t+1, Lng(Mp)-1)
                comps=P(Yp)
                if len(comps)<2: continue
                stats['witnesses']+=1
                # P-cut left-ends within Yp (absolute index in Yp)
                offs=[0]
                for c in comps: offs.append(offs[-1]+Lng(c))
                for J in range(1,len(comps)):
                    cL, cR = comps[J-1], comps[J]
                    if entry(cR,0,0)!=entry(cL,0,0): continue   # only ties
                    stats['tiepairs']+=1
                    pL, pR = offs[J-1], offs[J]                  # left-ends in Yp
                    if pR!=pL+1: stats['adj_fail']+=1
                    if Lng(cL)!=1: stats['sgl_fail']+=1
                    if not (entry(cR,1,0)<=entry(cL,1,0)): stats['mloc_fail']+=1
    # N-local adjacent-tie sweep (independent, deeper)
    for N in gen_seqs(6,2):
        if not is_standard(N): continue
        for j in range(Lng(N)-1):
            if entry(N,0,j)!=entry(N,0,j+1): continue
            nloc['pairs']+=1
            if not (entry(N,1,j+1)<=entry(N,1,j)): nloc['fail']+=1
            # is j+1's row-0 a nextrel0-child whose parent is j? (cheap-route probe)
            par=parent(N,0,j+1)
            if par==j: nloc['parent_ok']+=1
            else: nloc['notparent']+=1
    return stats, nloc

if __name__=='__main__':
    s,nl=check()
    print("=== d1pos B2 structural (monoT slices of oper(N,n), N standard d1pos, len<=5/val<=2, n<=3) ===")
    print(f"witnesses(slices w/ >=2 comps): {s['witnesses']}")
    print(f"tie pairs: {s['tiepairs']}")
    print(f"  (S-adj) pR!=pL+1 failures: {s['adj_fail']}")
    print(f"  (S-sgl) left Lng!=1 failures: {s['sgl_fail']}")
    print(f"  (M-loc) entry1 R> L failures: {s['mloc_fail']}")
    print("=== N-local adjacent row-0 tie (N standard, len<=6/val<=2) ===")
    print(f"adjacent tie pairs: {nl['pairs']}")
    print(f"  (N-loc) entry1 j+1 > j failures: {nl['fail']}")
    print(f"  parent(N,0,j+1)==j (nextrel0 child of j): {nl['parent_ok']}")
    print(f"  parent != j: {nl['notparent']}")

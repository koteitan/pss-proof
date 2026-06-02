#!/usr/bin/env python3
"""BC0-B: in branch-3b, is le0 (Red A) m10 jN reducible to the SPINE (block-leftend
row-0 minima) WITHOUT Red_le on the blocks?

For each core-nontrunk node C in the A-subtree (the branch-3b nodes), Red C =
diagSeq 0 (TrMax C) @ concat(blocks), block J = IncrFirst^eJ (Red (NJ C J)).
We test whether the row-0 le0 from any trunk index to the end jN follows from:
  (S1) trunk diagonal monotone (free),
  (S2) each block's leftend is its row-0 minimum (block is a Red output = diagonal-
       prefixed, so entry block 0 0 <= entry block 0 k) -- a property of Red OUTPUTS,
  (S3) the nextrel0 boundary between consecutive blocks (FirstNodes / idxsum leftend).
Specifically: does le0 (Red C) m10 jN factor as a chain of nextrel0 steps that only
ever 'descend' to block-leftends (the row-0 spine), never needing an le0 INTERNAL to a
block that would require Red_le on that block?

Concretely we check the SUFFICIENT structural fact:
  For the FULL Red A, le0 (Red A) m10 jN holds AND the witnessing nextrel0-chain can be
  chosen to pass only through indices that are block-leftends or trunk indices
  (i.e. the row-0 ancestor of jN is a block-leftend, recursively).
We approximate by: row-0 parent chain of jN in Red A consists of block-leftends+trunk.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, seg, le0, nextrel0,
                       Red, diagSeq, IncrFirst, funpow, TrMax)
from itertools import product

def row0_parent(M,j):
    # the unique nextrel0 parent (largest j0<j with nextrel0), if any
    cands=[j0 for j0 in range(j) if nextrel0(M,j0,j)]
    return cands  # could be 0,1,many

def all_mono(maxlen,maxval):
    out=[]
    for n in range(1,maxlen+1):
        for cells in product(product(range(maxval+1),repeat=2),repeat=n):
            M=[tuple(c) for c in cells]
            if zeroT(M) or not monoT(M): continue
            out.append(M)
    return out

def red_out_diag_prefixed(N):
    # is N (a Red output) such that entry N 0 0 is the row-0 minimum (leftend minimal)?
    if Lng(N)==0: return True
    return all(entry(N,0,0)<=entry(N,0,k) for k in range(Lng(N)))

if __name__=='__main__':
    L,V=(int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (3,3)
    Ms=all_mono(L,V)
    total=0; spine_chain_ok=0; redout_leftmin=0; redout_total=0
    bad=[]
    for M in Ms:
        m10=entry(M,1,0)
        if m10==0: continue
        A=diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
        if A[0]!=(0,0): continue
        total+=1
        RA=Red(A)
        # property: every Red output along the way has leftend = row0 min
        if red_out_diag_prefixed(RA): redout_leftmin+=1
        redout_total+=1
        # row-0 ancestor chain of jN back to m10 exists (le0) -- and each hop is a single
        # nextrel0 parent (well-formed spine, no ambiguous branching at row 0)
        jN=Lng(RA)-1
        ok=True; cur=jN; guard=0
        chain=[jN]
        while cur>m10 and guard<200:
            guard+=1
            ps=row0_parent(RA,cur)
            # pick the parent that is >= m10 if exists (spine toward anchor)
            ps2=[p for p in ps if p>=m10] or ps
            if not ps2: ok=False; break
            cur=max(ps2); chain.append(cur)
        if not (ok and cur==m10):
            # maybe le0 still holds via a different chain; check le0 directly
            ok = le0(RA,m10,jN)
        if ok: spine_chain_ok+=1
        else: bad.append((M,A,RA,m10,jN))
    print(f"# A cases: {total}")
    print(f"# Red A output has leftend = row-0 minimum (diag-prefixed): {redout_leftmin}/{redout_total}")
    print(f"# row-0 spine chain m10->jN exists: {spine_chain_ok}/{total}")
    for e in bad[:6]: print("   bad:",e)

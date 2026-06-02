#!/usr/bin/env python3
"""BC0-B: trace which Red branches fire in the recursion subtree of A=coreReduce M.

DECISIVE QUESTION for the route: when we unfold Red A (A mono+core), does the proof
FORCE a descent that hits dead-branch[20] (branch-5 'else M', m10>0 noncore with
seg N not PT_PS)?  If the subtree of A NEVER enters branch-5-else AND never even
enters a branch-5/branch-4 noncore node, then Red A is determined by the TRUNK/SPINE
(branches 3a/3b core, recursing only into NJ core blocks), and the proof can go via
the spine alone -> circle BROKEN.

We instrument Red to record, over the WHOLE recursion subtree of A:
  - b3a (core trunk diagSeq), b3b (core nontrunk diagSeq + NJ blocks),
  - b4 (noncore m10=0 shift), b5then (noncore m10>0 productive),
    b5else (noncore m10>0 DEAD-BRANCH[20]: returns M),
  - b1 (zeroT), b2 (multiT).
We report, per A, the multiset of branches in its subtree, and whether b5else ever fires.
The key spine claim: are the recursive children of A all CORE (m00=0 ∧ m10=0)?
i.e. does A's subtree stay in branches {b1,b2,b3a,b3b} only (never b4/b5)?
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, seg, le0, le1,
                       diagSeq, IncrFirst, funpow, TrMax, P, Br, FirstNodes,
                       Joints, THE_nextR)
from itertools import product

def Red_branches(M, tally, depth=0):
    if depth>300: raise RuntimeError("deep")
    if zeroT(M): tally['b1']+=1; return [(0,0)]
    if multiT(M):
        tally['b2']+=1
        out=[]
        for blk in P(M): out+=Red_branches(blk,tally,depth+1)
        return out
    j1=Lng(M)-1; j1p=TrMax(M); m00=entry(M,0,0); m10=entry(M,1,0)
    if m00==0 and m10==0:
        if j1p==j1:
            tally['b3a']+=1
            return diagSeq(m10,m10+j1)
        tally['b3b']+=1
        out=diagSeq(0,j1p); b=Br(M); fn=FirstNodes(M); jn=Joints(M)
        for J in range(len(b)):
            br10=entry(b[J],1,0)
            if br10==0: np=0
            else:
                par=THE_nextR(M,1,fn[J]); np=par+1
            eJ=jn[J]+1-np
            NJ=[(m00+jn[J]+1, m10+np)]+b[J][1:]
            out+=funpow(IncrFirst,eJ,Red_branches(NJ,tally,depth+1))
        return out
    else:
        if m10==0:
            tally['b4']+=1
            core=[(entry(M,0,j)-m00, entry(M,1,j)) for j in range(j1+1)]
            return Red_branches(core,tally,depth+1)
        else:
            N=Red_branches(diagSeq(0,m10-1)+funpow(IncrFirst,m10,M),tally,depth+1)
            jN=Lng(N)-1; sg=seg(N,m10,jN)
            if m10<=jN and len(sg)>0 and monoT(sg):
                tally['b5then']+=1
                return [(entry(N,0,j)-entry(N,0,m10)+entry(N,1,m10), entry(N,1,j)) for j in range(m10,jN+1)]
            else:
                tally['b5else']+=1
                return M

def all_mono(maxlen,maxval):
    out=[]
    for n in range(1,maxlen+1):
        for cells in product(product(range(maxval+1),repeat=2),repeat=n):
            M=[tuple(c) for c in cells]
            if zeroT(M) or not monoT(M): continue
            out.append(M)
    return out

if __name__=='__main__':
    L,V=(int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (4,3)
    Ms=all_mono(L,V)
    agg={k:0 for k in ['b1','b2','b3a','b3b','b4','b5then','b5else']}
    total=0; A_subtree_has_b5else=0; A_subtree_has_b4=0; A_subtree_has_b5=0
    A_subtree_has_b2=0
    examples_b5=[]
    for M in Ms:
        m10=entry(M,1,0)
        if m10==0: continue
        A=diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
        if A[0]!=(0,0): continue
        total+=1
        t={k:0 for k in agg}
        Red_branches(A,t)
        for k in agg: agg[k]+=t[k]
        if t['b5else']>0:
            A_subtree_has_b5else+=1
            if len(examples_b5)<5: examples_b5.append((M,A,dict(t)))
        if t['b4']>0: A_subtree_has_b4+=1
        if t['b5then']+t['b5else']>0: A_subtree_has_b5+=1
        if t['b2']>0: A_subtree_has_b2+=1
    print(f"# A=coreReduce M cases (m10>0, A0=(0,0)): {total}")
    print(f"# aggregate branch counts over ALL A-subtrees: {agg}")
    print(f"# A-subtrees that EVER hit dead-branch[20] (b5else): {A_subtree_has_b5else}/{total}")
    print(f"# A-subtrees that EVER hit branch-4 (noncore m10=0):  {A_subtree_has_b4}/{total}")
    print(f"# A-subtrees that EVER hit branch-5 (noncore m10>0):  {A_subtree_has_b5}/{total}")
    print(f"# A-subtrees that EVER hit branch-2 (multiT):         {A_subtree_has_b2}/{total}")
    print(f"# => SPINE-ONLY (only b1/b2/b3a/b3b, NO b4/b5): {total-A_subtree_has_b5-A_subtree_has_b4}/{total}")
    for e in examples_b5: print("  b5else example:",e)

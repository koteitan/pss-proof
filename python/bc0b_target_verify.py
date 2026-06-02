#!/usr/bin/env python3
"""BC0-B target empirical verification.

THE TARGET (alpha BC0 fragment, row-0 forward single-anchor):
  For M in PT_PS (mono), m10 = entry M 1 0 > 0,
    A := diagSeq 0 (m10-1) @ (IncrFirst^^m10) M   (= coreReduce M, the branch-5 arg)
    jA := Lng A - 1,  N := Red A,  jN := Lng N - 1
  GIVEN  le0 A m10 jA   (the anchor)
  SHOW   le0 (Red A) m10 jN.

Also test the cleaner standalone form:
  redle_le0_anchor_fwd:  for any mono ANCHORED B with le0 B a (Lng B-1) [the trunk anchor],
    le0 B a b ==> le0 (Red B) a b   on the trunk endpoint b = Lng B-1, a = the anchor index.

We enumerate all T_PS mono M (M0=(0,0)), build A, and check:
  (1) the anchor le0 A m10 jA  (should always hold since A is mono+core: A0=(0,0))
  (2) le0 (Red A) m10 jN
  (3) report BOTH counts (consequent-true / antecedent-true) and whether antecedent=>consequent.

Also: does the proof FORCE descent into the NJ sub-recursion? We instrument Red to
record whether the branch-5 'else M' dead-branch[20] fires (m10>0 noncore with seg not PT_PS),
and whether any NJ branch fires with m10>0 in the recursive subtree of A.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, seg, le0, le1,
                       Red, diagSeq, IncrFirst, funpow, TrMax)
from itertools import product

def all_mono(maxlen, maxval):
    # M in PT_PS = mono (NOT necessarily M0=(0,0): the alpha-route M is the ORIGINAL
    # noncore mono with m10>0).  A=coreReduce M will start at (0,0) by construction.
    out=[]
    for n in range(1,maxlen+1):
        for cells in product(product(range(maxval+1),repeat=2),repeat=n):
            M=[tuple(c) for c in cells]
            if zeroT(M): continue
            if not monoT(M): continue
            out.append(M)
    return out

def coreReduce_arg(M):
    m10=entry(M,1,0)
    return diagSeq(0,m10-1) + funpow(IncrFirst,m10,M)

if __name__=='__main__':
    L,V=(int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (5,3)
    Ms=all_mono(L,V)
    print(f"# mono M (len<=%d val<=%d, M0=(0,0)): {len(Ms)}"%(L,V))
    cons=0   # le0(Red A) m10 jN  holds
    ante=0   # le0 A m10 jA holds (anchor)
    both=0   # ante AND cons
    impl_fail=0  # ante TRUE but cons FALSE  (counterexamples to forward)
    total=0
    anchor_always=True
    fails=[]
    A_mono_count=0
    for M in Ms:
        m10=entry(M,1,0)
        if m10==0: continue   # branch-5 needs m10>0
        A=coreReduce_arg(M)
        if A[0]!=(0,0): continue
        jA=Lng(A)-1
        total+=1
        if monoT(A): A_mono_count+=1
        anc = le0(A,m10,jA)
        RA = Red(A)
        jN = Lng(RA)-1
        con = le0(RA,m10,jN)
        if anc: ante+=1
        if con: cons+=1
        if anc and con: both+=1
        if anc and not con:
            impl_fail+=1
            fails.append((M,A,m10,jA,jN))
        if not anc:
            anchor_always=False
    print(f"# (M with m10>0, A0=(0,0)) cases: {total}")
    print(f"  A is mono: {A_mono_count}/{total}")
    print(f"  anchor le0 A m10 jA            holds: {ante}/{total}  (always={anchor_always})")
    print(f"  consequent le0 (Red A) m10 jN holds: {cons}/{total}")
    print(f"  BOTH (ante & cons):                  {both}/{total}")
    print(f"  IMPLICATION FAILURES (ante & ~cons): {impl_fail}")
    for e in fails[:8]:
        print("   FAIL", e)

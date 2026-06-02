#!/usr/bin/env python3
"""BC0-B: is the anchor index m10 inside the TRUNK prefix of Red A?

Target: le0 (Red A) m10 jN, jN=Lng(Red A)-1.  In Red A = diagSeq 0 (TrMax(Red A)) @ blocks,
the anchor m10 is on the diagonal-trunk prefix iff m10 <= TrMax(Red A).  If so, le0 from
m10 along the trunk to jN reduces to trunk monotonicity (row-0 spine), and the row-1
NJ-block difficulty (BC1) is IRRELEVANT to the row-0 forward target.

Also report: entry(Red A) 0 m10 vs m10 (is the trunk value exactly m10? = diagonal).
And whether le0 (Red A) m10 (TrMax) and le0 (Red A) TrMax jN both hold (trunk + spine join).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, seg, le0,
                       Red, diagSeq, IncrFirst, funpow, TrMax)
from itertools import product

def all_mono(maxlen,maxval):
    out=[]
    for n in range(1,maxlen+1):
        for cells in product(product(range(maxval+1),repeat=2),repeat=n):
            M=[tuple(c) for c in cells]
            if zeroT(M) or not monoT(M): continue
            out.append(M)
    return out

if __name__=='__main__':
    L,V=(int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (3,3)
    Ms=all_mono(L,V)
    total=0; in_trunk=0; diag_val=0; le0_full=0
    trunk_then_spine=0
    notintrunk=[]
    for M in Ms:
        m10=entry(M,1,0)
        if m10==0: continue
        A=diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
        if A[0]!=(0,0): continue
        total+=1
        RA=Red(A); jN=Lng(RA)-1; tr=TrMax(RA)
        if m10<=tr:
            in_trunk+=1
            if entry(RA,0,m10)==m10: diag_val+=1
        else:
            notintrunk.append((M,A,RA,m10,tr,jN))
        if le0(RA,m10,jN): le0_full+=1
        # trunk-then-spine: le0 along trunk m10->tr, then tr->jN
        if le0(RA,m10,tr) and (tr==jN or le0(RA,tr,jN)):
            trunk_then_spine+=1
    print(f"# A cases: {total}")
    print(f"# anchor m10 <= TrMax(Red A) (on trunk prefix): {in_trunk}/{total}")
    print(f"#   of those, entry(Red A) 0 m10 == m10 (diagonal value): {diag_val}/{in_trunk}")
    print(f"# le0 (Red A) m10 jN holds: {le0_full}/{total}")
    print(f"# trunk-then-spine decomposition holds: {trunk_then_spine}/{total}")
    print(f"# anchor NOT in trunk: {len(notintrunk)}")
    for e in notintrunk[:6]: print("   notintrunk:",e)

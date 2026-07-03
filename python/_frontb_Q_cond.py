#!/usr/bin/env python3
"""Does Q = diagSeq 0 (m10-1) + M satisfy RedCondA & RedCondB?
M monoT, m10>0, RedCondA M, RedCondB M (NOT assuming Red M = M).
Also: under these (no Red M=M assumption), what is Red M? is it = M anyway?
The keystone backward says: M monoT, A&B  ==>  Red M = M.  We want to reduce
to a CORE-shaped A&B sequence.  Test if Q is core & satisfies A&B."""
import sys, itertools
sys.path.insert(0, __import__('os').path.dirname(__file__))
from red_model import (Lng, entry, monoT, Red, diagSeq, IncrFirst, funpow, seg,
                       hasParent, parent)

def RedCondA(M):
    for i in (0,1):
        for j in range(Lng(M)):
            if hasParent(M,i,j) and entry(M,i,parent(M,i,j))+1 != entry(M,i,j): return False
    return True
def RedCondB(M):
    for j in range(Lng(M)):
        if (not hasParent(M,0,j)) and entry(M,0,j) != entry(M,1,j): return False
    return True

def enum(maxlen, val):
    for n in range(1, maxlen+1):
        cells = [(a,b) for a in range(val+1) for b in range(val+1)]
        for M in itertools.product(cells, repeat=n):
            yield list(M)

def main():
    maxlen, val = 4, 4
    cand=0; qcore_fail=0; qa_fail=0; qb_fail=0; redM_ne=0; redQ_ne=0; ex=[]
    for M in enum(maxlen, val):
        if not monoT(M): continue
        m10 = entry(M,1,0)
        if m10 == 0: continue
        if not (RedCondA(M) and RedCondB(M)): continue   # NOTE: NOT assuming Red M = M
        cand+=1
        Q = diagSeq(0,m10-1)+M
        if not (entry(Q,0,0)==0 and entry(Q,1,0)==0): qcore_fail+=1
        if not RedCondA(Q):
            qa_fail+=1
            if len(ex)<5: ex.append(("RedCondA Q fail", M, Q))
        if not RedCondB(Q):
            qb_fail+=1
            if len(ex)<5: ex.append(("RedCondB Q fail", M, Q))
        if Red(M)!=M: redM_ne+=1
        if Red(Q)!=Q: redQ_ne+=1
    print(f"candidates(monoT,m10>0,A&B on M)={cand}")
    print(f"  Q not core        : {qcore_fail}")
    print(f"  RedCondA Q fail    : {qa_fail}")
    print(f"  RedCondB Q fail    : {qb_fail}")
    print(f"  Red M != M (target): {redM_ne}")
    print(f"  Red Q != Q         : {redQ_ne}")
    for e in ex: print("   ", e)

if __name__=='__main__':
    main()

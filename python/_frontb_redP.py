#!/usr/bin/env python3
"""Is Red P = P for P = diagSeq 0 (m10-1) + IncrFirst^m10 M (M monoT, m10>0, A&B)?
Even though RedCondA P fails. Also check: is P reduced? does core-hyp apply?"""
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
    cand=0; redP_fail=0; redP_ok=0; ex=[]
    for M in enum(maxlen, val):
        if not monoT(M): continue
        m10 = entry(M,1,0)
        if m10 == 0: continue
        if not (RedCondA(M) and RedCondB(M)): continue
        if Red(M)!=M: continue
        cand+=1
        P = diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
        if Red(P)==P: redP_ok+=1
        else:
            redP_fail+=1
            if len(ex)<5: ex.append((M, P, Red(P)))
    print(f"candidates={cand}: Red P = P ok={redP_ok} fail={redP_fail}")
    for e in ex: print("   ", e)

if __name__=='__main__':
    main()

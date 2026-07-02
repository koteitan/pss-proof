#!/usr/bin/env python3
"""Use the ACTUAL N = Red(coreReduce M) = Red P. Check the m10>0 branch reconstructs M.
Also: is N core (entry N 0 0=0, N 1 0=0)? reduced (Red N=N)? Does seg N m10 jN in PT_PS?
And how does N relate to M? (N = diagSeq 0 (m10-1)+M ? or = coreReduce ... ?)
"""
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
    cand=0; recon_fail=0; ncore_fail=0; nred_fail=0; rel_fail=0; ex=[]
    for M in enum(maxlen, val):
        if not monoT(M): continue
        m10 = entry(M,1,0)
        if m10 == 0: continue
        if not (RedCondA(M) and RedCondB(M)): continue
        if Red(M)!=M: continue
        cand+=1
        P = diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
        N = Red(P)
        jN = Lng(N)-1
        # core?
        if not (entry(N,0,0)==0 and entry(N,1,0)==0): ncore_fail+=1
        # reduced?
        if Red(N)!=N: nred_fail+=1
        # reconstruct
        sg = seg(N,m10,jN)
        ok = (m10<=jN) and len(sg)>0 and monoT(sg)
        if not ok:
            recon_fail+=1
            if len(ex)<5: ex.append(("guard fail", M, N)); continue
        recon = [(entry(N,0,j)-entry(N,0,m10)+entry(N,1,m10), entry(N,1,j)) for j in range(m10,jN+1)]
        if recon != M:
            recon_fail+=1
            if len(ex)<5: ex.append(("recon!=M", M, N, recon))
        # relationship: is N = diagSeq 0 (m10-1) + M ?
        guessN = diagSeq(0,m10-1)+M
        if N != guessN:
            rel_fail+=1
            if len(ex)<8 and rel_fail<=4: ex.append(("N != diagSeq+M", M, "N=",N, "guess=",guessN))
    print(f"candidates={cand}")
    print(f"  N not core         : {ncore_fail}")
    print(f"  N not reduced      : {nred_fail}")
    print(f"  reconstruction fail: {recon_fail}")
    print(f"  N != diagSeq 0(m10-1)+M : {rel_fail}")
    for e in ex: print("   ", e)

if __name__=='__main__':
    main()

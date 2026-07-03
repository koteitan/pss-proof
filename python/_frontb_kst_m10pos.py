#!/usr/bin/env python3
"""Empirical check for Front B keystone backward, monoT m10>0 reduction.

Claims to verify on monoT M (in T_PS), m10=entry M 1 0 > 0, RedCondA M, RedCondB M:
  (0) Red M = M  (the target).
  (1) P = diagSeq 0 (m10-1) + IncrFirst^m10 M is core: entry P 0 0 = entry P 1 0 = 0.
  (2) RedCondA P and RedCondB P.
  (3) Assuming core-hypothesis (Red P = P), the Red M m10>0 branch reconstructs M:
        N = Red P = P (if core holds), jN = Lng N - 1, m10<=jN, seg N m10 jN in PT_PS,
        and map(...) over [m10..<Suc jN] = M.
"""
import sys, itertools
sys.path.insert(0, __import__('os').path.dirname(__file__))
from red_model import (Lng, entry, monoT, zeroT, multiT, Red, diagSeq, IncrFirst,
                       funpow, seg, hasParent, parent, le0, TrMax)

def RedCondA(M):
    for i in (0,1):
        for j in range(Lng(M)):
            if hasParent(M,i,j):
                if entry(M,i,parent(M,i,j))+1 != entry(M,i,j): return False
    return True
def RedCondB(M):
    for j in range(Lng(M)):
        if (not hasParent(M,0,j)) and j<=Lng(M)-1:
            if entry(M,0,j) != entry(M,1,j): return False
    return True
def in_PT_PS(M):
    return len(M)>0 and monoT(M)

def enum(maxlen, val):
    for n in range(1, maxlen+1):
        cells = [(a,b) for a in range(val+1) for b in range(val+1)]
        for M in itertools.product(cells, repeat=n):
            yield list(M)

def main():
    maxlen, val = 4, 4
    tot=cand=0
    f0=f1=f2a=f2b=f3=0
    ex=[]
    for M in enum(maxlen, val):
        tot+=1
        if not monoT(M): continue
        m10 = entry(M,1,0)
        if m10 == 0: continue
        if not (RedCondA(M) and RedCondB(M)): continue
        cand+=1
        # (0) target
        if Red(M) != M:
            f0+=1
            if len(ex)<5: ex.append(("Red M != M", M))
            continue
        # (1) P core
        P = diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
        if not (entry(P,0,0)==0 and entry(P,1,0)==0):
            f1+=1
            if len(ex)<5: ex.append(("P not core", M, P))
        # (2) condA/B on P
        if not RedCondA(P):
            f2a+=1
            if len(ex)<5: ex.append(("RedCondA P fail", M, P))
        if not RedCondB(P):
            f2b+=1
            if len(ex)<5: ex.append(("RedCondB P fail", M, P))
        # (3) reconstruction assuming Red P = P (i.e. N = P)
        N = P  # core hypothesis: Red P = P
        jN = Lng(N)-1
        sg = seg(N,m10,jN)
        ok = (m10<=jN) and in_PT_PS(sg)
        if not ok:
            f3+=1
            if len(ex)<5: ex.append(("guard fail with N=P", M, N))
            continue
        recon = [(entry(N,0,j)-entry(N,0,m10)+entry(N,1,m10), entry(N,1,j)) for j in range(m10,jN+1)]
        if recon != M:
            f3+=1
            if len(ex)<5: ex.append(("recon != M", M, recon))
    print(f"maxlen={maxlen} val={val}: total={tot} candidates(monoT,m10>0,A&B)={cand}")
    print(f"  (0) Red M != M        : {f0}")
    print(f"  (1) P not core        : {f1}")
    print(f"  (2a) RedCondA P fail   : {f2a}")
    print(f"  (2b) RedCondB P fail   : {f2b}")
    print(f"  (3) recon/guard fail   : {f3}")
    for e in ex: print("   ", e)

if __name__=='__main__':
    main()

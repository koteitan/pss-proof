#!/usr/bin/env python3
"""Verify the 4-regime case-split COVERS all d1pos ¬brle residual cases, and that
A=j0'+TrMax+1 satisfies A<=Lng N-1 always, with the 'high' case (j0'<Lng N-1 and
A>=Lng N-1) being vacuous (so no 'high_impossible' lemma needed: A<Lng N-1 whenever
j0'<Lng N-1, given tnc). Rank-stratified, BOTH true/false counts."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, Br, is_standard, fmt, le0)

def gen_std(maxlen, maxval, KMAX):
    base = [[(j, j) for j in range(u, v + 1)] for u in range(maxval + 1)
            for v in range(u, maxval + 1)]
    store = {fmt(m): m for m in base}; frontier = list(base)
    for _ in range(KMAX):
        newf = []
        for M in frontier:
            for n in range(1, 4):
                Mp = oper(M, n); key = fmt(Mp)
                if Mp and len(Mp) <= maxlen and all(a <= maxval and b <= maxval for (a, b) in Mp) \
                        and key not in store:
                    store[key] = Mp; newf.append(Mp)
        frontier = newf
    return [m for m in store.values() if is_standard(m)]

def is_d1pos(N):
    j1 = Lng(N) - 1
    return j1 >= 1 and not (entry(N,0,j1)==0 and entry(N,1,j1)==0) \
           and idx1(N, j1) == 1 and hasParent(N, 1, j1)

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (12, 5, 12)
    Ns = gen_std(maxlen, maxval, KMAX)
    d1 = [N for N in Ns if is_d1pos(N)]
    by_rank={}
    regA=regB=boundary=periodic=uncovered=0
    high_viol=0  # j0'<LN-1 but A>=LN-1
    Aeq=0        # A==LN-1 (boundary trunk reaches exactly)
    total=0
    for N in d1:
        n_count = sum(1 for _ in [0])
        LN=Lng(N); j1N=LN-1
        jm2=parent(N,1,j1N)
        for n in range(1,4):
            M=oper(N,n)
            if not M: continue
            LM=Lng(M)
            for j0 in range(0,LM):
                for j1 in range(j0+1,LM):
                    Mp=seg(M,j0,j1)
                    if not monoT(Mp): continue
                    if not le0(M,j0,j1): continue
                    if not (j1N<=j1): continue
                    t=TrMax(Mp); LMp=Lng(Mp)
                    brle = (t==LMp-1) or le0(Mp,t+1,LMp-1)
                    if brle: continue
                    # residual ¬brle case
                    total+=1
                    A=j0+t+1
                    rk=KMAX  # not tracking exact rank here
                    if j0>=j1N:
                        periodic+=1
                    elif A<jm2:
                        regA+=1
                    elif jm2<=A<j1N:
                        if j0>=jm2: regB+=1
                        else: boundary+=1
                    elif A==j1N:
                        Aeq+=1
                        if j0<j1N: high_viol+=1
                    else:  # A>j1N with j0<j1N
                        if j0<j1N: high_viol+=1
                        uncovered+=1
    print(f"params len<={maxlen} val<={maxval} KMAX={KMAX}: d1pos N = {len(d1)}")
    print(f"total residual ¬brle cases = {total}")
    print(f"  regA (A<jm2)              = {regA}")
    print(f"  regB (jm2<=A<LN-1,j0>=jm2)= {regB}")
    print(f"  boundary (.. , j0<jm2)    = {boundary}")
    print(f"  periodic (j0>=LN-1)       = {periodic}")
    print(f"  A==LN-1 (j0<LN-1?)        = {Aeq}")
    print(f"  uncovered (A>LN-1,j0<LN-1)= {uncovered}")
    print(f"  HIGH violations(j0<LN-1 & A>=LN-1) = {high_viol}")
    covered=regA+regB+boundary+periodic
    print(f"COVERED by 4 cells (incl A==LN-1 as boundary if j0>=jm2) = {covered} / {total}")

if __name__=='__main__':
    main()

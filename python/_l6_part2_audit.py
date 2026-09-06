#!/usr/bin/env python3
"""Numeric check of §8.4 lemma part (2) / L6TransSliceClosed_p2:
  Trans( op1^[w'](M[n+1]) )  ==  operB( Trans M , numBT (n-1) )
with w' = (Lng M - 1) - 1 - parent M 1 (Lng M - 1), op1 N = oper N 1,
over mono ST_PS hosts M with hasParent M 1 (Lng M-1), 1 < Lng M-1, condIII or condIV.
Also checks the L-slice concrete form s84x_L M n = op1^[w'](M[n+1])."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, monoT, seg, parent, hasParent, oper)
import red_model as rm
from _r15_vx_lib import (Trans, operB, numBT, gen_pool, mono_hosts, guarded, SKIP, Tally, fmt)
from trans_model import condIII, condV

def condIV(M):
    from _r15_vx_lib import condIV as c4
    return c4(M)

def s84x_jm2(M): return parent(M, 1, Lng(M)-1)

def op1pow(M, w):
    N = list(M)
    for _ in range(w):
        N = oper(N, 1)
    return N

def s84x_L(M, n):
    # oper M n ++ [(M0,jm2 + n*(M0,j1 - M0,jm2), M1,jm2)]
    jm2 = s84x_jm2(M); j1 = Lng(M)-1
    col = (entry(M,0,jm2) + n*(entry(M,0,j1) - entry(M,0,jm2)), entry(M,1,jm2))
    return list(oper(M,n)) + [col]

def main():
    pool = gen_pool(maxlen=8, maxn=3, maxseed=2, cap=800, oper_budget=3)
    hosts = mono_hosts(pool)
    T = Tally()
    ntest = 0
    for M in hosts:
        M = list(M)
        L = Lng(M)
        if not (1 < L - 1): continue
        if not hasParent(M, 1, L-1): continue
        c3 = guarded(condIII, M, budget=5)
        c4 = guarded(condIV, M, budget=5)
        if c3 is SKIP or c4 is SKIP: continue
        if not (c3 or c4): continue
        jm2 = s84x_jm2(M)
        w = (L - 1) - 1 - jm2
        for n in range(1, 5):
            # main claim: Trans(op1^w (M[n+1])) == operB(Trans M, numBT(n-1))
            lhs_host = guarded(op1pow, M, w, budget=8) if False else None
            Mn1 = guarded(oper, M, n+1, budget=8)
            if Mn1 is SKIP: continue
            Lslice = guarded(op1pow, Mn1, w, budget=8)
            if Lslice is SKIP: continue
            TL = guarded(Trans, Lslice, budget=8)
            TM = guarded(Trans, M, budget=8)
            if TL is SKIP or TM is SKIP: continue
            rhs = guarded(operB, TM, numBT(n-1), budget=8)
            if rhs is SKIP: continue
            T.add('part2: Trans(L-slice)==operB(TransM,n-1)', TL == rhs, (M, n))
            # bridge: s84x_L M n == op1^w (M[n+1])
            SL = s84x_L(M, n)
            T.add('op1pow: s84x_L M n == op1^w(M[n+1])', list(SL) == list(Lslice), (M, n))
            ntest += 1
    print(f"tested instances: {ntest}")
    print(T.report('§8.4 part(2) / L6 numeric audit:'))

if __name__ == '__main__':
    main()

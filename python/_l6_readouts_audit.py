#!/usr/bin/env python3
"""Numeric check of the §8.4 L6 base-readout canonical values that
`8.4-l6-readouts-close.lean` reduces `L6BaseReadoutsResidual` to
(the sharp `L6BaseCoreResidual`):

  (3') Trans(s84x_L M 1) == operB(Trans M, numBT 0)              [BT identity]
  (Lp-head) Trans(s84x_Lp M) is a single principal D_v(.) with
            v == entry M 1 (s84x_jm2 M)   (= M_{1,j-2})          [pins ub == leaf(2)]

Over mono ST_PS hosts M with hasParent M 1 (Lng M-1), 1 < Lng M-1, condIII or condIV.
Leaf (3') is exactly part(2) at n=1; the Lp-head fact is what forces leaf (2) ub_eq
(head of Trans(Lp) matches Dprin ub (ins BZero) head => ub = M_{1,j-2})."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, seg, parent, hasParent, oper)
from _r15_vx_lib import (Trans, operB, numBT, gen_pool, mono_hosts, guarded, SKIP, Tally)
from trans_model import condIII, bpHeadV

def condIV(M):
    from _r15_vx_lib import condIV as c4
    return c4(M)

def s84x_jm2(M): return parent(M, 1, Lng(M)-1)

def s84x_L(M, n):
    jm2 = s84x_jm2(M); j1 = Lng(M)-1
    col = (entry(M,0,jm2) + n*(entry(M,0,j1) - entry(M,0,jm2)), entry(M,1,jm2))
    return list(oper(M,n)) + [col]

def s84x_Lp(M):
    jm2 = s84x_jm2(M); L = Lng(M)
    return list(seg(M, jm2, L-2)) + [(entry(M,0,L-1), entry(M,1,jm2))]

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
        # leaf (3'): Trans(s84x_L M 1) == operB(Trans M, numBT 0)
        L1 = guarded(s84x_L, M, 1, budget=8)
        TL1 = guarded(Trans, L1, budget=8) if L1 is not SKIP else SKIP
        TM = guarded(Trans, M, budget=8)
        if TL1 is SKIP or TM is SKIP: continue
        rhs = guarded(operB, TM, numBT(0), budget=8)
        if rhs is SKIP: continue
        T.add("(3') Trans(L1)==operB(TransM,numBT 0)", TL1 == rhs, (M,))
        # Lp-head: Trans(s84x_Lp M) single principal with head-value M_{1,j-2}
        Lp = s84x_Lp(M)
        TLp = guarded(Trans, Lp, budget=8)
        if TLp is SKIP: continue
        single = (TLp[0] == 'T' and len(TLp[1]) == 1)
        headv = bpHeadV(TLp)
        T.add("(Lp) Trans(Lp) single-principal", single, (M,))
        T.add("(Lp/ub) head(Trans(Lp)) == M_{1,j-2}", headv == entry(M,1,jm2), (M,))
        ntest += 1
    print(f"tested instances: {ntest}")
    print(T.report('§8.4 L6 base-readout canonical audit:'))

if __name__ == '__main__':
    main()

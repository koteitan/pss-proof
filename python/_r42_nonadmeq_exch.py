#!/usr/bin/env python3
"""r42: find NON-admeq condIV ST_PS hosts (rare) via the r32 generator with
widened diagonal seeds, then run the FULL exchange triple (3 conjuncts) on them
for n=1,2,3.  Report count + pass-fraction + minimal CEX if any conjunct fails.
Also structurally characterize the non-admeq regime.
"""
import sys, os, time, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r28_c4dx_producer as V
from red_model import (Lng, entry, monoT, zeroT, hasParent, parent, seg, Br,
                       fmt, reduced, oper)
from trans_model import Adm, adm, Pred
from _r15_vx_lib import (Trans, Mark, operB, numBT, lessBT, leBT, guarded, SKIP)

def pr(*a): print(*a, flush=True)

def s84x_jm2(M): return parent(M, 1, Lng(M) - 1)
def transJ0(M): return parent(M, 0, Lng(M) - 1)
def s84x_jm3(M): return Adm(M, s84x_jm2(M))
def transJm1(M): return Adm(M, transJ0(M))

def gt(f, *a, budget=25): return guarded(f, *a, budget=budget)

def main():
    t0 = time.time()
    pool = []
    # r32 seed tuples, WIDENED (larger um/vx to reach more non-admeq hosts)
    for seed, mlen, cap, ns, um, vx in (
            (11, 14, 4000, (1, 2, 3), 5, 10),
            (23, 14, 4000, (1, 2), 6, 11),
            (37, 15, 4000, (1, 2, 3), 6, 12),
            (5, 15, 4000, (1, 2), 6, 12),
            (7, 16, 4000, (1, 2, 3), 7, 12),
            (13, 16, 4000, (1, 2), 7, 13),
            (17, 17, 4000, (1, 2, 3), 7, 13),
            (29, 17, 4000, (1, 2), 8, 14),
            (3, 18, 4000, (1, 2, 3), 8, 14),
            (41, 18, 4000, (1, 2), 8, 15)):
        pool += V.gen_oper(mlen, cap, seed, ns, um, vx)
    pr(f'pool {len(pool)}  gen_t={time.time()-t0:.0f}s')

    admeq_n = 0; nonadmeq = []
    seenN = set()
    hosts = 0
    for M in pool:
        L = Lng(M); j1 = L - 1
        if not (1 < j1) or not monoT(M) or zeroT(M): continue
        if not hasParent(M, 1, j1): continue
        if not reduced(M): continue
        if not V.condIV(M): continue
        jm2 = s84x_jm2(M); jm3 = s84x_jm3(M); jm1 = transJm1(M)
        if jm2 is None: continue
        hosts += 1
        if jm3 == jm1:
            admeq_n += 1
        else:
            t = tuple(M)
            if t not in seenN:
                seenN.add(t); nonadmeq.append(M)
    pr(f'condIV hosts {hosts}  admeq {admeq_n}  nonadmeq(unique) {len(nonadmeq)}'
       f'  t={time.time()-t0:.0f}s')

    # structural characterization
    dir_gt = dir_lt = 0
    pr('--- nonadmeq hosts (structure) ---')
    for M in sorted(nonadmeq, key=lambda x: Lng(x)):
        jm2 = s84x_jm2(M); jm3 = s84x_jm3(M); jm1 = transJm1(M); j0 = transJ0(M)
        L = Lng(M); v1 = entry(M, 1, L-1)
        if jm3 > jm1: dir_gt += 1
        else: dir_lt += 1
        # is the N-slice single-column?  N = seg M jm3 (L-1); Np = seg M jm2 (L-1)
        Nslice = seg(M, jm3, L-1); Npslice = seg(M, jm2, L-1)
        pr(f'  M={fmt(M)} L={L} v1={v1}')
        pr(f'     jm2={jm2}(row1par) j0={j0}(row0par) jm3=Adm(jm2)={jm3} jm1=Adm(j0)={jm1}'
           f'  admJm2={adm(M,jm2)} admJ0={adm(M,j0)}')
        pr(f'     entrys: e1[jm2]={entry(M,1,jm2)} e1[jm3]={entry(M,1,jm3)} '
           f'e1[jm1]={entry(M,1,jm1)} e1[j0]={entry(M,1,j0)}')
        pr(f'     Nslice(jm3..)={fmt(Nslice)} Lng={Lng(Nslice)}')
        pr(f'     Npslice(jm2..)={fmt(Npslice)} Lng={Lng(Npslice)}')
    pr(f'direction: jm3>jm1={dir_gt}  jm3<jm1={dir_lt}')

    # FULL exchange triple, n=1,2,3
    pr('--- exchange triple on nonadmeq hosts ---')
    C1=[0,0]; C2=[0,0]; C3=[0,0]; cex={1:None,2:None,3:None}; skipped=0
    for M in nonadmeq:
        TM = gt(Trans, M, budget=30)
        if TM is SKIP: skipped += 1; continue
        for n in (1, 2, 3):
            Mn = gt(oper, M, n, budget=15); Mn1 = gt(oper, M, n+1, budget=15)
            if Mn is SKIP or Mn1 is SKIP: skipped+=1; continue
            TMn = gt(Trans, Mn, budget=30); TMn1 = gt(Trans, Mn1, budget=30)
            if TMn is SKIP or TMn1 is SKIP: skipped+=1; continue
            opN = gt(operB, TM, numBT(n), budget=15)
            opNm1 = gt(operB, TM, numBT(n-1), budget=15)
            if opN is SKIP or opNm1 is SKIP: skipped+=1; continue
            c1 = lessBT(TMn, opN); c2 = lessBT(TMn, TM); c3 = lessBT(opNm1, TMn1)
            C1[0]+=c1; C1[1]+=1; C2[0]+=c2; C2[1]+=1; C3[0]+=c3; C3[1]+=1
            if not c1 and cex[1] is None: cex[1]=(fmt(M),n)
            if not c2 and cex[2] is None: cex[2]=(fmt(M),n)
            if not c3 and cex[3] is None: cex[3]=(fmt(M),n)
    pr(f'CONJ1 lessBT(Trans M[n], operB(Trans M, numBT n))    : {C1[0]}/{C1[1]}')
    pr(f'CONJ2 lessBT(Trans M[n], Trans M)                    : {C2[0]}/{C2[1]}')
    pr(f'CONJ3 lessBT(operB(Trans M, numBT(n-1)), Trans M[n+1]): {C3[0]}/{C3[1]}')
    pr(f'CEX c1 {cex[1]}  c2 {cex[2]}  c3 {cex[3]}  skipped {skipped}')
    pr(f'total {time.time()-t0:.0f}s')

if __name__ == '__main__':
    main()

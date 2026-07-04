#!/usr/bin/env python3
"""Characterize the admeq gate for condIV: Adm M (s84x_jm2 M) == transJm1 M,
i.e. Adm M (parent M 1 (Lng-1)) == Adm M (parent M 0 (Lng-1)).
Measure over condIV standard hosts (with the rng side-cond that c4wx uses)."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r28_c4dx_producer as V
from red_model import (Lng, entry, monoT, zeroT, hasParent, parent, seg, Br,
                       fmt, reduced, is_standard)
from trans_model import Adm, adm

def pr(*a): print(*a, flush=True)

def main():
    t0 = time.time()
    admeq_all = [0, 0]; admeq_std = [0, 0]; admeq_rng = [0, 0]
    cex = []
    hosts = 0; std = 0; HOSTCAP = 3000
    pool = []
    for seed, mlen, cap, ns, um, vx in (
            (11, 11, 2000, (1, 2, 3), 3, 7),
            (23, 12, 2000, (1, 2), 4, 8),
            (37, 12, 2000, (1, 2, 3), 5, 8),
            (5, 13, 2000, (1, 2), 3, 9),
            (7, 13, 2000, (1, 2, 3), 4, 9),
            (13, 14, 2500, (1, 2), 3, 10),
            (17, 15, 2500, (1, 2, 3), 5, 10),
            (29, 15, 2500, (1, 2), 4, 11)):
        pool += V.gen_oper(mlen, cap, seed, ns, um, vx)
    pr(f'pool {len(pool)} gen_t={time.time()-t0:.0f}s')
    for M in pool:
        if hosts >= HOSTCAP: break
        L = Lng(M); j1 = L - 1
        if j1 <= 2 or not monoT(M) or zeroT(M) or not hasParent(M, 1, j1): continue
        if not V.condIV(M): continue
        if not reduced(M): continue
        hosts += 1
        jm2 = V.s84x_jm2(M); jm3 = V.s84x_jm3(M); jm1 = V.transJm1(M)
        ae = (jm3 == jm1)
        admeq_all[0] += ae; admeq_all[1] += 1
        rngok = (jm2 + 1 < L - 1)
        if rngok:
            admeq_rng[0] += ae; admeq_rng[1] += 1
            if not ae and len(cex) < 6:
                cex.append((fmt(M), 'jm2', jm2, 'jm3', jm3, 'jm1', jm1,
                            'j0', V.transJ0(M)))
        try:
            if is_standard(M):
                std += 1
                admeq_std[0] += ae; admeq_std[1] += 1
        except Exception:
            pass
    pr(f'condIV hosts {hosts}  standard {std}  t={time.time()-t0:.0f}s')
    pr(f'ADMEQ_all  {admeq_all}')
    pr(f'ADMEQ_std  {admeq_std}   (is_standard filtered)')
    pr(f'ADMEQ_rng  {admeq_rng}   (rng side-cond jm2+1<Lng-1, what c4wx needs)')
    pr(f'cex_admeq_fail (rng) {cex}')
    pr(f'total {time.time()-t0:.0f}s')

if __name__ == '__main__':
    main()

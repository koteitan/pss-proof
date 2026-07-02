#!/usr/bin/env python3
"""r15-S4d follow-up: validate the FULL L6 statement (and P1/BASE/DEC2 bricks)
on condition-IV instances, esp. the newly found condIV & jm3<jm1 regime
(NOT vacuous: 3 instances found by _r15_s4d_validate.py seed 202; the round-14
vacuity hypothesis from run E is REFUTED).

Mining strategy that worked: ns=(1,2) only, deeper maxLng, wider diagSeq seeds.
"""
import sys, signal, time
from collections import defaultdict
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
import _r15_s4d_validate as V
from _r15_s4d_validate import (gen_pool, Stat, check_L6, check_L5, check_P1,
                               check_BASE, check_IVMINE, setup, TimeoutErr)
from red_model import Lng, parent, hasParent, monoT
from trans_model import Adm, adm, condIII, condVI
import signal

def main():
    t0 = time.time()
    S = defaultdict(Stat)
    R = {'n': 0, 'jm2adm': 0, 'jm3eqjm1': 0, 'gapadm': 0,
         'gapw': defaultdict(int), 'CEX': []}
    nIV = nIVL6 = timeouts = 0
    for seed, mlen, cap, ns, um, vx, bud in (
            (202, 16, 12000, (1,2), 2, 7, 400),
            (303, 18, 12000, (1,2), 2, 8, 400),
            (404, 17, 15000, (1,2,3), 3, 7, 400)):
        pool = gen_pool(max_len=mlen, cap=cap, seed=seed, ns=ns, umax=um, vextra=vx)
        tseg = time.time()
        for M in pool:
            if time.time() - tseg > bud: break
            j1 = Lng(M)-1
            if j1 <= 1 or not monoT(M) or not hasParent(M, 1, j1): continue
            if not V.condIV(M): continue
            j0 = parent(M, 0, j1)
            jm2 = parent(M, 1, j1)
            jm1 = Adm(M, j0)
            nIV += 1
            signal.alarm(15)
            try:
                check_IVMINE(M, R)
                check_P1(M, S)
                if (not condVI(M)) and Adm(M, jm2) == jm1 and (jm2 < j0 or adm(M, j0)):
                    check_L5(M, S)
                    check_BASE(M, S)
                if Adm(M, jm2) < jm1:
                    nIVL6 += 1
                    check_L6(M, S)
            except TimeoutErr:
                timeouts += 1
            except RecursionError:
                timeouts += 1
            finally:
                signal.alarm(0)
        print(f'[seed {seed}] pool {len(pool)} IV so far {nIV} IV-L6 {nIVL6} '
              f'timeouts {timeouts} ({time.time()-tseg:.0f}s)')
    print()
    for k in sorted(S):
        st = S[k]
        print(f'{k:12s} {st}', 'CEX:' if st.bad else '', st.cex[:2] if st.bad else '')
    print()
    print('IVMINE: n=%d jm2adm=%d jm3eqjm1=%d gapadm=%d' %
          (R['n'], R['jm2adm'], R['jm3eqjm1'], R['gapadm']))
    print('  gap widths:', dict(R['gapw']))
    print('  condIV & jm3<jm1 instances:', len(R['CEX']))
    for c in R['CEX'][:8]: print('   ', c)
    print('elapsed %.1fs' % (time.time()-t0))

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
r"""r28-CONDIV13 companion: validate the HB residual of the assembled condIV
exchange (c4dx_condIV_exchange_assembled):

  HB: every monomial component of t2 = transT2 M is >= D_{M_{1,j1}} 0  (leBT)

on GENUINE condIV hosts (the condIV analogue of the deferred part (3) of
条件(V)の下での Joints/FirstNodes/t2 の基本性質).  Also record the admeq/reg
gates so the residual's truth is checked exactly on the assembled lemma's
regime.  Reuses the r28 producer validator's generators and order model."""
import sys, os, time, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r28_c4dx_producer as V
from red_model import Lng, entry, monoT, zeroT, hasParent, fmt
from trans_model import ZB, Dpt, PB

def pr(*a): print(*a, flush=True)

def leBT(a, b): return a == b or V.lessBT(a, b)

def main():
    t0 = time.time()
    R = {'hosts': 0, 'gated': 0, 'to': 0}
    hb_all = V.St(); hb_gated = V.St(); hb_deep = V.St()
    pools = []
    for seed, mlen, cap, ns, um, vx in (
            (202, 16, 4000, (1, 2), 2, 7),
            (303, 18, 4000, (1, 2), 2, 8),
            (505, 20, 5000, (1, 2), 3, 9),
            (707, 22, 6000, (1, 2), 4, 9)):
        pools.append(('oper s%d' % seed, V.gen_oper(mlen, cap, seed, ns, um, vx)))
    for seed, mlen, cap in ((41, 9, 600), (43, 10, 500), (47, 11, 400)):
        pools.append(('straddle s%d' % seed, V.gen_straddle(mlen, cap, seed)))
    for tag, pool in pools:
        nh = 0; t1 = time.time()
        for M in pool:
            if time.time() - t1 > 90: break
            j1 = Lng(M) - 1
            if j1 <= 1 or not monoT(M) or zeroT(M) or not hasParent(M, 1, j1):
                continue
            if not V.reduced(M) or not V.condIV(M): continue
            nh += 1
            signal.alarm(25)
            try:
                v1 = entry(M, 1, j1)
                t2 = V.transT2(M)
                jm3 = V.s84x_jm3(M); jm1 = V.transJm1(M)
                jp = V.transJ0(M)
                admeq = (jm3 == jm1)
                reg = (V.s84x_jm2(M) < jp) or V.adm(M, jp)
                ok = all(leBT(Dpt(v1, ZB), c) for c in PB(t2))
                R['hosts'] += 1
                hb_all.rec(ok, (fmt(M),))
                if admeq and reg:
                    R['gated'] += 1
                    hb_gated.rec(ok, (fmt(M),))
                if Lng(M) >= 9: hb_deep.rec(ok, (fmt(M),))
            except (V.TO, RecursionError, ValueError, IndexError):
                R['to'] += 1
            finally:
                signal.alarm(0)
        pr(f'[{tag}] pool={len(pool)} condIV={nh} ({time.time() - t1:.0f}s)')
    pr(f'hosts={R["hosts"]} gated={R["gated"]} timeouts={R["to"]}')
    pr(f'HB all   {hb_all}  CEX {hb_all.cex[:4]}')
    pr(f'HB gated {hb_gated}  CEX {hb_gated.cex[:4]}')
    pr(f'HB deep  {hb_deep}  CEX {hb_deep.cex[:4]}')
    pr(f'total {time.time() - t0:.0f}s')

if __name__ == '__main__':
    main()

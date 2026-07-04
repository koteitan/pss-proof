#!/usr/bin/env python3
r"""r30-CONDIVHB: deep validation of the condIV t2-component lower bound (HB)
and the SLICE GEOMETRY the proof route needs.

HB (target):  forall c in PB(transT2 M).  leBT (D_{M_{1,j1}} 0) c

Route to validate (mirror of atx_condV_nadm_t2_components, using the GENERAL
m_8_4_rightmost_nonadm_ancestor with m0=j0, m1=j1 instead of the condV special):
  N   = seg M jm1 j1,   jm1 = transJm1 M = Adm M j0,  j0 = parent M 0 j1
  RN  = Red N in DT_PS
  slice facts:
    BRNE     : Br RN != []
    FNLAST   : FirstNodes RN ! last  == j1 - jm1
    DIAG     : entry RN 0 (j1-jm1) == entry RN 1 (j1-jm1)      (2nd disjunct)
    JLAST    : Joints RN ! last == j0 - jm1
    NOTNX1   : not nextR M 1 (j1-1) j1
    LVL      : entry RN 1 (j1-jm1) == entry M 1 j1  (bound is at M_{1,j1})
  pin:
    PIN      : flat(Trans N) == flat(transC2 M)
  condIV inequality (for the leftDj0 last-component case):
    JPGE     : entry M 1 j0 >= entry M 1 j1
  leftDj0 bookkeeping:
    LEFT     : fraction of hosts with leftDj0 True (diagnostic)
Deep: pool caps up to 40000, Lng up to 15, oper-orbit + brute straddle.
"""
import sys, os, time, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r28_c4dx_producer as V
from red_model import (Lng, entry, monoT, zeroT, hasParent, parent, seg,
                       Br, FirstNodes, Joints, nextR, fmt)
from trans_model import (Adm, ZB, Dpt, PB, bpHeadV, bpHeadT, flatBT, _c2, Pred)

def pr(*a): print(*a, flush=True)
def leBT(a, b): return a == b or V.lessBT(a, b)

class St:
    def __init__(s): s.ok = 0; s.bad = 0; s.cex = []
    def rec(s, g, i):
        if g: s.ok += 1
        else:
            s.bad += 1
            if len(s.cex) < 6: s.cex.append(i)
    def __str__(s): return f"{s.ok}/{s.ok+s.bad}"

KEYS = ('HB','BRNE','FNLAST','DIAG','JLAST','NOTNX1','LVL','PIN','JPGE','HBstrong')

def check(M, R, deep):
    j1 = Lng(M) - 1
    v1 = entry(M, 1, j1)
    j0 = parent(M, 0, j1)
    if j0 is None: return
    jm1 = V.transJm1(M)                # Adm M j0
    t2 = V.transT2(M)
    Rn = V.Red(seg(M, jm1, j1))
    R['hosts'] += 1
    if deep: R['deep'] += 1
    def rec(k, ok):
        R[k].rec(ok, (fmt(M),))
        if deep: R[k+'_d'].rec(ok, (fmt(M),))
    # HB target
    hb = all(leBT(Dpt(v1, ZB), c) for c in PB(t2))
    rec('HB', hb)
    # stronger bound at j0-level (condIV M_{1,j0} >= M_{1,j1})
    vj0 = entry(M, 1, j0)
    hbs = all(leBT(Dpt(vj0, ZB), c) for c in PB(t2))
    rec('HBstrong', hbs)
    # slice geometry
    brn = Br(Rn)
    rec('BRNE', len(brn) >= 1)
    if len(brn) >= 1:
        last = Lng(brn) - 1 if isinstance(brn, list) else len(brn) - 1
        fn = FirstNodes(Rn); jj = Joints(Rn)
        rec('FNLAST', fn[last] == j1 - jm1)
        rec('DIAG', entry(Rn, 0, j1 - jm1) == entry(Rn, 1, j1 - jm1))
        rec('JLAST', jj[last] == j0 - jm1)
        rec('LVL', entry(Rn, 1, j1 - jm1) == v1)
    rec('NOTNX1', not nextR(M, 1, j1 - 1, j1))
    rec('JPGE', vj0 >= v1)
    # pin
    jm1c = V.transJm1(M)
    c2 = _c2(M, j1, j0, bpHeadV(V.Mark(Pred(M), jm1c)), t2)
    pin = flatBT(V.Trans(seg(M, jm1, j1))) == flatBT(c2)
    rec('PIN', pin)

def main():
    t0 = time.time()
    R = {'hosts': 0, 'deep': 0, 'to': 0}
    for k in KEYS: R[k] = St(); R[k+'_d'] = St()
    pools = []
    for seed, mlen, cap, ns, um, vx in (
            (11, 15, 30000, (1, 2, 3), 3, 9),
            (23, 15, 30000, (1, 2), 4, 10),
            (37, 16, 30000, (1, 2, 3), 5, 10)):
        pools.append(('oper s%d' % seed, V.gen_oper(mlen, cap, seed, ns, um, vx)))
    for seed, mlen, cap in ((41, 13, 40000), (43, 14, 40000), (47, 15, 40000)):
        pools.append(('straddle s%d' % seed, V.gen_straddle(mlen, cap, seed)))
    for tag, pool in pools:
        nh = 0; t1 = time.time()
        for M in pool:
            if time.time() - t1 > 150: break
            j1 = Lng(M) - 1
            if j1 <= 1 or not monoT(M) or zeroT(M) or not hasParent(M, 1, j1):
                continue
            if not V.reduced(M) or not V.condIV(M): continue
            nh += 1
            signal.alarm(25)
            try: check(M, R, Lng(M) >= 10)
            except (V.TO, RecursionError, ValueError, IndexError):
                R['to'] += 1
            finally: signal.alarm(0)
        pr(f'[{tag}] pool={len(pool)} condIV={nh} ({time.time()-t1:.0f}s)')
    pr(f'hosts={R["hosts"]} deep(Lng>=10)={R["deep"]} timeouts={R["to"]}')
    for k in KEYS:
        pr(f'{k:9s} all {str(R[k]):>10s}   deep {str(R[k+"_d"]):>10s}   '
           f'CEX {R[k].cex[:3]}')
    pr(f'total {time.time()-t0:.0f}s')

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""r71: DEEP-STRESS the bottom guard BG (the r71 census residual) and break down
its NON-VACUOUS exercises.

BG:  for every t in S = {body} u GBT v1 body  whose principal list starts with the
     bottom prefix psR (ox8_rsub body dR = Trm (psR @ [D_v1 0])), the principal x
     at the hole-aligned index |psR| satisfies
         lessBP x (D_v1 0)  -->  lessBP x (D_ub X0)     (X0 = D_ub 0, ub = v1-1)
     i.e.  head x < v1  -->  head x < ub  or  (head x = ub and body x < X0).

DANGEROUS x  ==  head x = ub  and  NOT (body x < X0).   BG = "no DANGEROUS x at
the hole-aligned index".  We count:
  EX      : non-vacuous exercises (head x < v1 at the hole-aligned index)
  EX_lt   : ... of which head x < ub  (safe by HEAD alone)
  EX_eq   : ... of which head x = ub  (safe only by the BODY comparison)
  FAIL    : DANGEROUS ones               <- must be 0
Also re-checks KK itself, and the "walk reaches the hole" count.
"""
import sys, time, signal, random
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4c/python')
from red_model import (Lng, entry, monoT, diagSeq, oper, seg, parent,
                       hasParent, Adm)
from trans_model import Trans, Pred, adm
import buchholz as bu

ZB = ('T', [])
def D(v, t): return ('D', v, t)
def T(ps): return ('T', ps)
def bucOf(t): return [('D', p[1], bucOf(p[2])) for p in t[1]]
def lt(a, b): return bu.lt_term(bucOf(a), bucOf(b))
def ltP(p, q): return bu.lt_princ(('D', p[1], bucOf(p[2])), ('D', q[1], bucOf(q[2])))

class TO(Exception): pass
def _h(s, f): raise TO()
signal.signal(signal.SIGALRM, _h)
def safe(f, *a, budget=6):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TO, RecursionError, AssertionError, ValueError, IndexError,
            KeyError, RuntimeError):
        signal.alarm(0); return None

def gen(maxlen, tmax, nmax, seeds):
    seen = set(); t0 = time.time()
    starts = [diagSeq(u, u + d) for u in range(0, 7) for d in range(1, 9)]
    dq = deque()
    for s in starts:
        k = tuple(s)
        if k not in seen: seen.add(k); dq.append(s); yield s
    tb = t0 + tmax * 0.40
    while dq and time.time() < tb:
        M = dq.popleft()
        for nn in range(1, nmax + 1):
            M2 = safe(oper, M, nn, budget=3)
            if M2 is None or M2 == M or Lng(M2) > maxlen: continue
            k = tuple(M2)
            if k not in seen: seen.add(k); dq.append(M2); yield M2
    for sd in seeds:
        rng = random.Random(sd)
        for s in starts:
            if time.time() - t0 > tmax: return
            M = list(s)
            for _ in range(600):
                if time.time() - t0 > tmax: return
                nn = rng.randrange(1, nmax + 1)
                M2 = safe(oper, M, nn, budget=3)
                if M2 is None or M2 == M or Lng(M2) > maxlen:
                    M2 = safe(oper, M, 1, budget=3)
                    if M2 is None or M2 == M or Lng(M2) > maxlen: break
                M = M2; k = tuple(M)
                if k not in seen: seen.add(k); yield M

def condIII(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp) >= entry(M,1,j1) and adm(M, jp)
def condIV(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp) >= entry(M,1,j1) and not adm(M, jp)
def hole_depth(t, v1):
    d = 0
    while True:
        ps = t[1]
        if not ps: return None
        last = ps[-1]
        if last[1] == v1 and last[2] == ZB: return d
        t = last[2]; d += 1
        if d > 300: return None
def rsub(t, k):
    for _ in range(k):
        if not t[1]: return None
        t = t[1][-1][2]
    return t
def surger(t, q):
    ps = t[1]; last = ps[-1]
    if last[2] == ZB: return T(ps[:-1] + [q])
    return T(ps[:-1] + [D(last[1], surger(last[2], q))])
def gset(t, v1, acc):
    acc.append(t)
    for p in t[1]:
        if p[1] >= v1: gset(p[2], v1, acc)
    return acc

def main():
    tmax   = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    nmax   = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    S = dict(hosts=0, levels=0, KK=0, KK_fail=0, EX=0, EX_lt=0, EX_eq=0,
             FAIL=0, hostEX=0, v1_1=0, v1_ge2=0)
    seen_ex = []
    t0 = time.time()
    for M in gen(maxlen, tmax, nmax, [11, 22, 33, 44, 55, 66, 77, 88, 99]):
        if time.time() - t0 > tmax: break
        j1 = Lng(M) - 1
        if not monoT(M) or not (1 < j1) or not hasParent(M, 1, j1): continue
        if not (condIII(M) or condIV(M)): continue
        p1 = safe(parent, M, 1, j1, budget=2); p0 = safe(parent, M, 0, j1, budget=2)
        if p1 is None or p0 is None: continue
        jm3 = safe(Adm, M, p1, budget=3); jm1 = safe(Adm, M, p0, budget=3)
        if jm3 is None or jm1 is None or not (jm3 < jm1): continue
        N = seg(M, jm3, j1)
        TN = safe(Trans, N, budget=12)
        if TN is None or not TN[1]: continue
        BODY = TN[1][0][2]
        v1 = entry(M, 1, j1)
        if v1 == 0: continue
        ub = v1 - 1
        dR = hole_depth(BODY, v1)
        if dR is None: continue
        S['hosts'] += 1
        S['v1_1' if v1 == 1 else 'v1_ge2'] += 1
        X0 = T([D(ub, ZB)]); X1 = surger(BODY, D(ub, X0))
        psR = rsub(BODY, dR)[1][:-1]; m = len(psR)
        # ---- KK re-check
        for k in range(1, dR + 1):
            Zk = rsub(BODY, k)
            if Zk is None: continue
            S['levels'] += 1
            S['KK' if lt(Zk, X1) else 'KK_fail'] += 1
        # ---- BG on the closed set
        hostex = 0
        for t in gset(BODY, v1, []):
            xs = t[1]
            if len(xs) <= m or xs[:m] != psR: continue
            x = xs[m]
            if not (x[1] < v1): continue          # guard not exercised
            S['EX'] += 1; hostex += 1
            if x[1] < ub:
                S['EX_lt'] += 1
            else:                                  # x[1] == ub
                S['EX_eq'] += 1
                if not lt(x[2], X0):
                    S['FAIL'] += 1
                    if len(seen_ex) < 5:
                        seen_ex.append(('FAIL', list(M), v1, m, bucOf(t)))
            if len(seen_ex) < 5 and x[1] == ub:
                seen_ex.append(('eq', list(M), v1, m, bucOf(T([x]))))
        if hostex: S['hostEX'] += 1
    el = time.time() - t0
    print(f'=== r71 BG deep  maxlen={maxlen} nmax={nmax} elapsed={el:.0f}s ===')
    for k in ('hosts','v1_1','v1_ge2','levels','KK','KK_fail'):
        print(f'  {k:10s} {S[k]}')
    print('  --- BOTTOM GUARD BG (non-vacuity breakdown):')
    for k in ('EX','EX_lt','EX_eq','FAIL','hostEX'):
        print(f'  {k:10s} {S[k]}')
    print('--- samples:')
    for x in seen_ex: print('   ', x)

main()

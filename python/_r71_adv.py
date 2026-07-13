#!/usr/bin/env python3
"""r71 ADVERSARIAL hunt for a counterexample to the bottom guard BG.

DANGEROUS x  ==  head x = ub  and  NOT lessBT (body x) (D_ub 0)      (ub = v1-1)
  -- exactly the principals that are  < D_v1 0  but NOT  < D_ub (D_ub 0).
  (The r70 counterexample principal D_0(D_0 0) is of this kind.)

BG fails  iff some t in S = {body} u GBT v1 body  has a DANGEROUS principal at
the HOLE-ALIGNED index m = |psR|, with its first m principals equal to psR
(psR = ox8_rsub body dR's list minus its last principal = the hole).

Reported:
  DANG_any    : (t, i) pairs in S carrying a DANGEROUS principal ANYWHERE
  DANG_hosts  : hosts with at least one such
  DANG_at_m   : ... of which the index i EQUALS m   (prefix not yet checked)
  BG_EX       : NON-VACUOUS exercises of BG (prefix matched, head < v1 at m)
  BG_FAIL     : BG counterexamples                                <- must be 0
  m_dist      : distribution of the hole-aligned index m
"""
import sys, time, signal, random
from collections import deque, Counter
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

def gen(maxlen, tmax, nmax, seeds, umax, dmax):
    seen = set(); t0 = time.time()
    starts = [diagSeq(u, u + d) for u in range(0, umax) for d in range(1, dmax)]
    dq = deque()
    for s in starts:
        k = tuple(s)
        if k not in seen: seen.add(k); dq.append(s); yield s
    tb = t0 + tmax * 0.5
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
            for _ in range(500):
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
def gset(t, v1, acc):
    acc.append(t)
    for p in t[1]:
        if p[1] >= v1: gset(p[2], v1, acc)
    return acc
def subs(t, acc):
    acc.append(t)
    for p in t[1]: subs(p[2], acc)
    return acc

def main():
    tmax   = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    nmax   = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    umax   = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    dmax   = int(sys.argv[5]) if len(sys.argv) > 5 else 8
    S = dict(hosts=0, DANG_any=0, DANG_hosts=0, DANG_at_m=0,
             BG_EX=0, BG_FAIL=0, KK=0, KK_fail=0,
             DANGsub_any=0, DANGsub_hosts=0)
    mdist = Counter(); cex = []
    t0 = time.time()
    for M in gen(maxlen, tmax, nmax, [1,2,3,4,5,6,7,8], umax, dmax):
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
        X0 = T([D(ub, ZB)])
        def dangerous(x): return x[1] == ub and not lt(x[2], X0)
        psR = rsub(BODY, dR)[1][:-1]; m = len(psR)
        mdist[m] += 1
        hd = 0; hds = 0
        for t in gset(BODY, v1, []):
            xs = t[1]
            for i, x in enumerate(xs):
                if dangerous(x):
                    S['DANG_any'] += 1; hd = 1
                    if i == m: S['DANG_at_m'] += 1
            if len(xs) > m and xs[:m] == psR and xs[m][1] < v1:
                S['BG_EX'] += 1
                if dangerous(xs[m]):
                    S['BG_FAIL'] += 1
                    if len(cex) < 4:
                        cex.append((list(M), v1, m, bucOf(t)))
        for t in subs(BODY, []):
            for x in t[1]:
                if dangerous(x): S['DANGsub_any'] += 1; hds = 1
        S['DANG_hosts'] += hd; S['DANGsub_hosts'] += hds
    el = time.time() - t0
    print(f'=== r71 ADV  maxlen={maxlen} nmax={nmax} u<{umax} d<{dmax} '
          f'elapsed={el:.0f}s ===')
    for k in ('hosts','DANG_any','DANG_hosts','DANG_at_m','BG_EX','BG_FAIL',
              'DANGsub_any','DANGsub_hosts'):
        print(f'  {k:14s} {S[k]}')
    print('  m_dist (hole-aligned index):', dict(sorted(mdist.items())))
    print('--- BG COUNTEREXAMPLES:')
    for x in cex: print('   ', x)

main()

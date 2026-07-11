#!/usr/bin/env python3
"""r70: the REPLACEMENT route for the refuted OKH.

ox9_engine consumes ox9_ok ONLY to feed ox9_MAIN, whose only output is
    leLA :  leBT (ox8_rsub A1 (Suc k)) X1 .
So the engine can take that conclusion DIRECTLY as its hypothesis:

  KEY(k) :  lessBT (ox8_rsub A1 k) X1            (1 <= k <= dR)

and KEY factors through two clean facts:

  MONO(k):  lessBT (ox8_rsub A1 k) (ox8_rsub body k)     [surgery lowers: pA < D_v1 0]
  KK(k)  :  lessBT (ox8_rsub body k) X1                  [the UNSURGERED spine sub-body
                                                          is still below the LOWERED body]

This script stress-tests KEY / MONO / KK on the deep pure-ST_PS census corpus,
including the hosts that REFUTE ox9_ok.
"""
import sys, time, signal, random
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
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

def gen(maxlen, tmax, nmax, seeds):
    seen = set(); t0 = time.time()
    starts = [diagSeq(u, u + d) for u in range(0, 6) for d in range(1, 8)]
    dq = deque()
    for s in starts:
        k = tuple(s)
        if k not in seen: seen.add(k); dq.append(s); yield s
    tb = t0 + tmax * 0.45
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
            for _ in range(400):
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
        if d > 200: return None
def surger(t, q):
    ps = t[1]; last = ps[-1]
    if last[2] == ZB: return T(ps[:-1] + [q])
    return T(ps[:-1] + [D(last[1], surger(last[2], q))])
def rsub(t, k):
    for _ in range(k):
        if not t[1]: return None
        t = t[1][-1][2]
    return t
def okpred(t, v1, X0):
    for p in t[1]:
        if not (v1 <= p[1] or lt(p[2], X0)): return False
        if not okpred(p[2], v1, X0): return False
    return True

def main():
    tmax   = int(sys.argv[1]) if len(sys.argv) > 1 else 420
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    nmax   = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    S = dict(hosts=0, okfail_hosts=0, levels=0,
             KEY=0, KEY_fail=0, MONO=0, MONO_fail=0, KK=0, KK_fail=0,
             X1lt=0, X1lt_fail=0, maxlen_seen=0, maxdR=0)
    cex = []
    t0 = time.time()
    for M in gen(maxlen, tmax, nmax, [11, 22, 33, 44, 55, 66, 77]):
        if time.time() - t0 > tmax: break
        j1 = Lng(M) - 1
        if not monoT(M) or not (1 < j1) or not hasParent(M, 1, j1): continue
        if not (condIII(M) or condIV(M)): continue
        p1 = safe(parent, M, 1, j1, budget=2); p0 = safe(parent, M, 0, j1, budget=2)
        if p1 is None or p0 is None: continue
        jm3 = safe(Adm, M, p1, budget=3); jm1 = safe(Adm, M, p0, budget=3)
        if jm3 is None or jm1 is None or not (jm3 < jm1): continue
        N = seg(M, jm3, j1)
        TN = safe(Trans, N, budget=10); TPN = safe(Trans, Pred(N), budget=10)
        if TN is None or TPN is None or not TN[1] or not TPN[1]: continue
        BODY = TN[1][0][2]; A0 = TPN[1][0][2]
        v1 = entry(M, 1, j1)
        if v1 == 0: continue
        ub = v1 - 1
        dR = hole_depth(BODY, v1)
        if dR is None: continue
        S['hosts'] += 1
        S['maxlen_seen'] = max(S['maxlen_seen'], Lng(M))
        S['maxdR'] = max(S['maxdR'], dR)
        X0 = T([D(ub, ZB)])
        if not okpred(BODY, v1, X0): S['okfail_hosts'] += 1
        X1 = surger(BODY, D(ub, X0)); A1 = surger(BODY, D(ub, A0))
        if lt(X1, BODY): S['X1lt'] += 1
        else: S['X1lt_fail'] += 1
        for k in range(1, dR + 1):
            tA = rsub(A1, k); tB = rsub(BODY, k)
            if tA is None or tB is None: continue
            S['levels'] += 1
            key = lt(tA, X1); mono = lt(tA, tB); kk = lt(tB, X1)
            S['KEY' if key else 'KEY_fail'] += 1
            S['MONO' if mono else 'MONO_fail'] += 1
            S['KK' if kk else 'KK_fail'] += 1
            if not (key and mono and kk) and len(cex) < 4:
                cex.append((list(M), v1, k, key, mono, kk,
                            bucOf(BODY), bucOf(X1)))
    print(f'=== r70 KEY route  maxlen={maxlen} nmax={nmax} '
          f'elapsed={time.time()-t0:.0f}s ===')
    for k in sorted(S): print(f'  {k:13s} {S[k]}')
    print('--- CEX (KEY/MONO/KK):')
    for x in cex: print('   ', x)

main()

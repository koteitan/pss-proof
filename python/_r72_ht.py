#!/usr/bin/env python3
"""r72 front A: the HEIGHT route to KK.

ox11_safe e p q Z W is VACUOUS as soon as Z cannot descend e levels.
  htBT Z <= e  ==>  ox11_safe e p q Z W          (pure induction, NO guard)
  htBT (rsub t k) <= htBT t - k                  (pure induction)
so KK needs only        htBT body <= dR + 1
("the right spine down to the hole is a MAXIMAL-DEPTH path of body").
Measure it.  Also measure the per-k form  htBT (rsub body k) <= dR.
"""
import sys, time, signal, random
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4c/python')
from red_model import (Lng, entry, monoT, diagSeq, oper, seg, parent, hasParent, Adm)
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
def ht(t):
    if not t[1]: return 0
    return 1 + max(ht(p[2]) for p in t[1])
def surger(t, q):
    ps = t[1]; last = ps[-1]
    if last[2] == ZB: return T(ps[:-1] + [q])
    return T(ps[:-1] + [D(last[1], surger(last[2], q))])

def main():
    tmax   = int(sys.argv[1]) if len(sys.argv) > 1 else 420
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    nmax   = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    S = dict(hosts=0, H_ok=0, H_bad=0, lev=0, K_ok=0, K_bad=0, KK=0, KKfail=0)
    bad = []
    t0 = time.time()
    for M in gen(maxlen, tmax, nmax, [11,22,33,44,55,66,77,88,99]):
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
        H = ht(BODY)
        if H <= dR + 1: S['H_ok'] += 1
        else:
            S['H_bad'] += 1
            if len(bad) < 6: bad.append(('H', list(M), v1, dR, H, bucOf(BODY)))
        X0 = T([D(ub, ZB)]); X1 = surger(BODY, D(ub, X0))
        for k in range(1, dR + 1):
            Zk = rsub(BODY, k)
            if Zk is None: continue
            S['lev'] += 1
            if ht(Zk) <= dR: S['K_ok'] += 1
            else:
                S['K_bad'] += 1
                if len(bad) < 12: bad.append(('K', list(M), v1, dR, k, ht(Zk), bucOf(BODY)))
            S['KK' if lt(Zk, X1) else 'KKfail'] += 1
    el = time.time() - t0
    print(f'=== r72 HEIGHT  maxlen={maxlen} nmax={nmax} elapsed={el:.0f}s ===')
    for k in ('hosts','H_ok','H_bad','lev','K_ok','K_bad','KK','KKfail'):
        print(f'  {k:8s} {S[k]}')
    print('--- violations:')
    for b in bad: print('   ', b)

main()

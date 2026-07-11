#!/usr/bin/env python3
"""r69 STEP-0d: ox9_hge ('all heads of BODY >= v1') is FALSE (2/425 deep hosts).
Test the CORRECT weakening actually used by the transport:

  ox9_ok v1 ub t  ==  every principal D_c XB anywhere in t satisfies
                        v1 <= c   OR   lessBT XB (D_ub 0)
                      (the second disjunct is exactly what the base case of
                       ox9_TT needs:  lessBP (D_c XB) (D_ub (D_ub 0))  when c<=ub)

Also test the stronger-but-simpler variant
  ox9_leaf: every principal D_c XB with c < v1 has XB = 0.
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

UNITS = [
 [(1,1),(2,1)], [(1,1),(2,2),(2,1)], [(1,1),(2,2),(3,1),(4,2)],
 [(1,1),(2,2),(3,1),(4,2),(4,2)], [(1,1),(2,2),(3,3),(4,1),(5,2)],
 [(1,1),(2,1),(3,1)], [(1,1),(2,2),(2,1),(3,1)], [(1,1),(2,2),(3,2)],
 [(1,1),(2,2),(3,1),(4,3)],
]
SEED_HOSTS = [
 [(0,0),(1,1),(2,2),(3,1),(4,2),(4,2)],
 [(0,0),(1,1),(2,2),(3,1),(4,0),(5,1),(6,2),(7,0),(6,2)],
]
def gen(maxlen, tmax, seeds):
    seen = set(); t0 = time.time()
    starts = [diagSeq(u, u+d) for u in range(0, 7) for d in range(1, 7)]
    starts += [list(x) for x in SEED_HOSTS]
    for U in UNITS:
        for k in (2, 3, 4):
            s = [(0,0)] + U * k
            if Lng(s) <= maxlen: starts.append(s)
    dq = deque()
    for s in starts:
        k = tuple(s)
        if k not in seen: seen.add(k); dq.append(s); yield s
    tb = t0 + tmax * 0.5
    while dq and time.time() < tb:
        M = dq.popleft()
        for nn in range(1, 4):
            M2 = safe(oper, M, nn, budget=2)
            if M2 is None or M2 == M or Lng(M2) > maxlen: continue
            k = tuple(M2)
            if k not in seen: seen.add(k); dq.append(M2); yield M2
    for sd in seeds:
        if time.time() - t0 > tmax: return
        rng = random.Random(sd)
        for s in starts:
            M = list(s)
            for _ in range(120):
                if time.time() - t0 > tmax: return
                nn = rng.randrange(1, 4)
                M2 = safe(oper, M, nn, budget=2)
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
        if d > 80: return None

def surger(t, q):
    ps = t[1]; last = ps[-1]
    if last[2] == ZB: return T(ps[:-1] + [q])
    return T(ps[:-1] + [D(last[1], surger(last[2], q))])

def rsub(t, k):
    for _ in range(k):
        if not t[1]: return None
        t = t[1][-1][2]
    return t

def ok(t, v1, ub, X0):
    """ox9_ok: every principal D_c XB: v1<=c or lessBT XB (D_ub 0)"""
    for p in t[1]:
        c, XB = p[1], p[2]
        if not (v1 <= c or lt(XB, X0)):
            return False
        if not ok(XB, v1, ub, X0):
            return False
    return True

def leafcond(t, v1):
    for p in t[1]:
        c, XB = p[1], p[2]
        if c < v1 and XB != ZB: return False
        if not leafcond(XB, v1): return False
    return True

def hge(t, v1):
    for p in t[1]:
        if p[1] < v1: return False
        if not hge(p[2], v1): return False
    return True

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    S = dict(hosts=0, ok=0, ok_fail=0, leaf=0, leaf_fail=0, hge=0, hge_fail=0,
             gt=0, gt_fail=0, levels=0)
    cex_ok, cex_leaf = [], []
    t0 = time.time()
    for M in gen(maxlen, tmax, seeds=[11, 22, 33, 44, 55]):
        if time.time() - t0 > tmax: break
        j1 = Lng(M) - 1
        if not monoT(M) or not (1 < j1) or not hasParent(M, 1, j1): continue
        if not (condIII(M) or condIV(M)): continue
        jm3 = safe(Adm, M, safe(parent, M, 1, j1, budget=2), budget=2)
        jm1 = safe(Adm, M, safe(parent, M, 0, j1, budget=2), budget=2)
        if jm3 is None or jm1 is None or not (jm3 < jm1): continue
        N = seg(M, jm3, j1)
        TN = safe(Trans, N, budget=8); TPN = safe(Trans, Pred(N), budget=8)
        if TN is None or TPN is None or not TN[1] or not TPN[1]: continue
        BODY = TN[1][0][2]; A0 = TPN[1][0][2]
        v1 = entry(M, 1, j1)
        if v1 == 0: continue
        ub = v1 - 1
        d = hole_depth(BODY, v1)
        if d is None: continue
        S['hosts'] += 1
        X0 = T([D(ub, ZB)])
        if ok(BODY, v1, ub, X0): S['ok'] += 1
        else:
            S['ok_fail'] += 1
            if len(cex_ok) < 4: cex_ok.append((M, v1, ub, bucOf(BODY)))
        if leafcond(BODY, v1): S['leaf'] += 1
        else:
            S['leaf_fail'] += 1
            if len(cex_leaf) < 3: cex_leaf.append((M, v1, bucOf(BODY)))
        if hge(BODY, v1): S['hge'] += 1
        else: S['hge_fail'] += 1
        X1 = surger(BODY, D(ub, X0))
        A1 = surger(BODY, D(ub, A0))
        for k in range(1, d+2):
            tA = rsub(A1, k)
            if tA is None: continue
            S['levels'] += 1
            S['gt'] += 1
            if not lt(tA, X1): S['gt_fail'] += 1
    print('=== r69 STEP-0d (ox9_ok vs ox9_hge vs leaf) ===')
    for k in sorted(S): print(f'  {k:10s} {S[k]}')
    print('--- ox9_ok CEX:')
    for x in cex_ok: print('   ', x)
    print('--- leaf CEX:')
    for x in cex_leaf: print('   ', x[0], 'v1=', x[1])

main()

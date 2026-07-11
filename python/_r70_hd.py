#!/usr/bin/env python3
"""r70: is KK decided at INDEX 0?   HD(k):  rsub body k = 0  or  hd(rsub body k) < hd(X1).
HD ==> KK in one line (lessBT (Trm(x#xs)) (Trm(y#ys)) <== lessBP x y).
Also measures the walk: at which (level, index) is  lessBT (rsub body k) X1  decided,
and whether the right operand's HOLE is ever reached.
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

def hd_ok(tB, X1):
    """HD: tB = 0  or  hd tB < hd X1"""
    if not tB[1]: return True
    if not X1[1]: return False
    return ltP(tB[1][0], X1[1][0])

def walk_depth(L, R, hole_lvl, lvl=0):
    """walk lessBT L R; return (verdict, level at which it is decided,
       whether the right's hole principal was compared)"""
    xs, ys = L[1], R[1]
    i = 0
    while True:
        if i >= len(xs): return (i < len(ys), lvl, False)
        if i >= len(ys): return (False, lvl, False)
        x, y = xs[i], ys[i]
        if x == y:
            i += 1; continue
        # compare principals
        if x[1] != y[1]:
            hit = (lvl == hole_lvl and i == len(ys) - 1)
            return (x[1] < y[1], lvl, hit)
        # heads tie -> descend into bodies
        hit = (lvl == hole_lvl and i == len(ys) - 1)
        if hit:
            return (lt(x[2], y[2]), lvl, True)
        v, dl, h = walk_depth(x[2], y[2], hole_lvl, lvl + 1)
        return (v, dl, h)

def main():
    tmax   = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    nmax   = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    S = dict(hosts=0, levels=0, HD=0, HD_fail=0, KK=0, KK_fail=0,
             hole_hit=0, dec_lvl0=0)
    cex = []
    t0 = time.time()
    for M in gen(maxlen, tmax, nmax, [11, 22, 33, 44, 55]):
        if time.time() - t0 > tmax: break
        j1 = Lng(M) - 1
        if not monoT(M) or not (1 < j1) or not hasParent(M, 1, j1): continue
        if not (condIII(M) or condIV(M)): continue
        p1 = safe(parent, M, 1, j1, budget=2); p0 = safe(parent, M, 0, j1, budget=2)
        if p1 is None or p0 is None: continue
        jm3 = safe(Adm, M, p1, budget=3); jm1 = safe(Adm, M, p0, budget=3)
        if jm3 is None or jm1 is None or not (jm3 < jm1): continue
        N = seg(M, jm3, j1)
        TN = safe(Trans, N, budget=10)
        if TN is None or not TN[1]: continue
        BODY = TN[1][0][2]
        v1 = entry(M, 1, j1)
        if v1 == 0: continue
        ub = v1 - 1
        dR = hole_depth(BODY, v1)
        if dR is None: continue
        S['hosts'] += 1
        X0 = T([D(ub, ZB)])
        X1 = surger(BODY, D(ub, X0))
        for k in range(1, dR + 1):
            tB = rsub(BODY, k)
            if tB is None: continue
            S['levels'] += 1
            h = hd_ok(tB, X1); kk = lt(tB, X1)
            S['HD' if h else 'HD_fail'] += 1
            S['KK' if kk else 'KK_fail'] += 1
            verdict, dl, hit = walk_depth(tB, X1, dR)
            if hit: S['hole_hit'] += 1
            if dl == 0: S['dec_lvl0'] += 1
            if not h and len(cex) < 3:
                cex.append((list(M), v1, k, kk, bucOf(tB), bucOf(X1)))
    print(f'=== r70 HD (index-0 decision) maxlen={maxlen} '
          f'elapsed={time.time()-t0:.0f}s ===')
    for k in sorted(S): print(f'  {k:10s} {S[k]}')
    print('--- HD CEX:')
    for x in cex: print('   ', x)

main()

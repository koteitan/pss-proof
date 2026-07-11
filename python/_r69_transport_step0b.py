#!/usr/bin/env python3
"""r69 TRANSPORT STEP-0b: run the PROPOSED PROOF as a decision procedure and
find its exact failure branch (if any).

Proof strategy (only provable facts used):
  F1 every right-spine head of BODY (levels 0..d-1) >= v1
  F2 descP (OT) everywhere
  F3 ub < v1;  F4 surgery strictly lowers (scbext_lessBT)

prove(L,R,hL,hR):  hL/hR = hole depth or None.
  BOTH hole   -> lock-step:  hL=0 => head v1 vs spine head>=v1 => OK
                 heads differ => OK ; heads equal => recurse bodies
                 (width mismatch at the compare index handled below)
  LEFT hole only  -> OK  (surgery lowers left; transitivity)
  RIGHT hole only -> P: walk; at hole index compare head c vs w
                     e>=1: c<w OK ; c=w recurse ; c>w or equal => vacuous
                     e=0 : c<ub OK ; c=ub => *** DANGER ***
  NEITHER -> OK
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
def ltP(p, q):  # lessBP
    return p[1] < q[1] or (p[1] == q[1] and lt(p[2], q[2]))

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
            for _ in range(90):
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
        if d > 60: return None

def surger(t, q):
    ps = t[1]; last = ps[-1]
    if last[2] == ZB: return T(ps[:-1] + [q])
    return T(ps[:-1] + [D(last[1], surger(last[2], q))])

def rsub(t, k):
    for _ in range(k):
        if not t[1]: return None
        t = t[1][-1][2]
    return t

STAT = {}
def bump(k): STAT[k] = STAT.get(k, 0) + 1

def prove(L, R, hL, hR, v1, ub, depth=0):
    """returns 'OK' or a DANGER tag."""
    if depth > 40: return 'DEPTH'
    xs, ys = L[1], R[1]
    nL, nR = len(xs), len(ys)
    for i in range(min(nL, nR)):
        holeL = (hL is not None and i == nL-1)
        holeR = (hR is not None and i == nR-1)
        a, b = xs[i], ys[i]
        if not holeL and not holeR:
            if a == b: continue
            bump('A'); return 'OK'
        if holeL and not holeR:
            bump('B'); return 'OK'
        if not holeL and holeR:
            # case (C)/(P): right operand's hole-carrying principal
            bump('C')
            if not ltP(a, b):
                bump('C_vacuous'); return 'OK'   # lessBT L R false at i
            c = a[1]
            if hR >= 1:
                w = b[1]
                if c < w: bump('C_headlt'); return 'OK'
                if c == w:
                    bump('C_headeq_recurse')
                    return prove(a[2], b[2], None, hR-1, v1, ub, depth+1)
                bump('C_impossible'); return 'OK'
            else:
                # hR == 0: b = D_v1 0 ; b' = D_ub Q  (ub = v1-1)
                bump('C_bottom')
                if c < ub: bump('C_bottom_safe'); return 'OK'
                if c == ub: bump('C_bottom_DANGER'); return 'DANGER_ub'
                bump('C_bottom_vac'); return 'OK'
        # both hole-carrying
        if hL == 0:
            bump('D0'); return 'OK'      # left head v1 < / <= right spine head
        if hR == 0:
            bump('D0R_UNEXPECTED'); return 'DANGER_dLdR'
        if a[1] != b[1]:
            bump('Dhead'); return 'OK'
        bump('Drec')
        return prove(a[2], b[2], hL-1, hR-1, v1, ub, depth+1)
    bump('EXH'); return 'OK'

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    S = dict(hosts=0, levels=0, ok=0, danger=0, gtfail=0)
    dangers = []
    t0 = time.time()
    for M in gen(maxlen, tmax, seeds=[11, 22, 33, 44]):
        if time.time() - t0 > tmax: break
        j1 = Lng(M) - 1
        if not monoT(M) or not (1 < j1) or not hasParent(M, 1, j1): continue
        if not (condIII(M) or condIV(M)): continue
        jm3 = safe(Adm, M, safe(parent, M, 1, j1, budget=2), budget=2)
        jm1 = safe(Adm, M, safe(parent, M, 0, j1, budget=2), budget=2)
        if jm3 is None or jm1 is None or not (jm3 < jm1): continue
        N = seg(M, jm3, j1)
        TN = safe(Trans, N, budget=6); TPN = safe(Trans, Pred(N), budget=6)
        if TN is None or TPN is None or not TN[1] or not TPN[1]: continue
        BODY = TN[1][0][2]; A0 = TPN[1][0][2]
        v1 = entry(M, 1, j1)
        if v1 == 0: continue
        ub = v1 - 1
        d = hole_depth(BODY, v1)
        if d is None: continue
        S['hosts'] += 1
        X0 = T([D(ub, ZB)])
        X1 = surger(BODY, D(ub, X0))
        A1 = surger(BODY, D(ub, A0))
        for k in range(1, d+2):
            tB = rsub(BODY, k); tA = rsub(A1, k)
            if tB is None or tA is None: continue
            S['levels'] += 1
            hL = hole_depth(tB, v1)
            r = prove(tB, BODY, hL, d, v1, ub)
            if r == 'OK': S['ok'] += 1
            else:
                S['danger'] += 1
                if len(dangers) < 6:
                    dangers.append((M, k, r, v1, ub, bucOf(tB), bucOf(BODY)))
            if not lt(tA, X1): S['gtfail'] += 1
    print('=== r69 TRANSPORT STEP-0b (proof as decision procedure) ===')
    for k in sorted(S): print(f'  {k:10s} {S[k]}')
    print('  branch counters:', dict(sorted(STAT.items())))
    print('--- DANGER instances:')
    for x in dangers: print('   ', x)

main()

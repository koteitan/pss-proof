#!/usr/bin/env python3
"""r69 TRANSPORT STEP-0: pin the EXACT structural side-condition the surgery
transport needs.

Census hosts M: standard ST_PS (oper-closure corpus), monoT (PT_PS),
hasParent M 1 (Lng M-1), 1 < Lng M - 1, condIII or condIV,
ltJ: s84x_jm3 M < transJm1 M.

  BODY = bpHeadT (Trans (s84x_N M)),  v1 = M[1, Lng-1],  ub = v1 - 1
  hole = D_v1 0 = deepest-right principal of BODY (at right-spine depth d)
  X1   = BODY[hole := D_ub (D_ub 0)]
  A1   = BODY[hole := D_ub A0],  A0 = bpHeadT (Trans (Pred (s84x_N M)))
  tB_k = ox8_rsub BODY k,  tA_k = ox8_rsub A1 k    (k = 1..d+1)

CHECKS
 (1) widths of BODY's right-spine levels 0..d   -> chain?  non-increasing?
 (2) the LEX-WALK case trace of (tB_k, BODY): does case (C) [left principal
     hole-FREE while right principal is hole-CARRYING at a matched index]
     ever arise?  (C) is the only branch where the surgery can flip '<'.
 (3) ground truth: lessBT tA_k X1  (the SETLE1 residual) and lessBT tB_k BODY.
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
    """right-spine depth of the deepest-right principal D_v1 0, or None."""
    d = 0
    while True:
        ps = t[1]
        if not ps: return None
        last = ps[-1]
        if last[1] == v1 and last[2] == ZB: return d
        t = last[2]; d += 1
        if d > 60: return None

def surger(t, q):
    """replace the deepest-right principal of t by the principal q."""
    ps = t[1]
    last = ps[-1]
    if last[2] == ZB:
        return T(ps[:-1] + [q])
    return T(ps[:-1] + [D(last[1], surger(last[2], q))])

def rsub(t, k):
    for _ in range(k):
        if not t[1]: return None
        t = t[1][-1][2]
    return t

def widths(t, d):
    ws = []
    for j in range(d+1):
        r = rsub(t, j)
        if r is None: return None
        ws.append(len(r[1]))
    return ws

def walk(L, R, hL, hR, trace):
    """lex-walk of lessBT L R with hole-depth annotations (None = hole-free).
    returns the terminal case tag."""
    xs, ys = L[1], R[1]
    nL, nR = len(xs), len(ys)
    for i in range(min(nL, nR)):
        holeL = (hL is not None and i == nL-1)
        holeR = (hR is not None and i == nR-1)
        a, b = xs[i], ys[i]
        if not holeL and not holeR:
            if a == b: continue
            trace.append('A'); return 'A'
        if holeL and not holeR:
            trace.append('B'); return 'B'
        if not holeL and holeR:
            trace.append('C'); return 'C'
        if hL == 0:
            trace.append('D0'); return 'D0'
        if hR == 0:
            trace.append('D0R'); return 'D0R'
        if a[1] != b[1]:
            trace.append('Dhead'); return 'Dhead'
        trace.append('D')
        return walk(a[2], b[2], hL-1, hR-1, trace)
    trace.append('EXH'); return 'EXH'

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    S = dict(pool=0, hosts=0, levels=0, chain_all=0, chain_above=0,
             noninc=0, notnoninc=0, holewide=0,
             gt_tA=0, gt_tA_fail=0, gt_tB=0, gt_tB_fail=0)
    tags = {}
    cex_C, cex_noninc, cex_wide = [], [], []
    t0 = time.time()
    for M in gen(maxlen, tmax, seeds=[11, 22, 33]):
        if time.time() - t0 > tmax: break
        S['pool'] += 1
        j1 = Lng(M) - 1
        if not monoT(M) or not (1 < j1): continue
        if not hasParent(M, 1, j1): continue
        if not (condIII(M) or condIV(M)): continue
        jm3 = safe(Adm, M, safe(parent, M, 1, j1, budget=2), budget=2)
        jm1 = safe(Adm, M, safe(parent, M, 0, j1, budget=2), budget=2)
        if jm3 is None or jm1 is None or not (jm3 < jm1): continue
        N = seg(M, jm3, j1)
        TN = safe(Trans, N, budget=6)
        TPN = safe(Trans, Pred(N), budget=6)
        if TN is None or TPN is None or not TN[1] or not TPN[1]: continue
        BODY = TN[1][0][2]
        A0 = TPN[1][0][2]
        v1 = entry(M, 1, j1); ub = v1 - 1
        if v1 == 0: continue
        d = hole_depth(BODY, v1)
        if d is None: continue
        S['hosts'] += 1
        ws = widths(BODY, d)
        if ws is None: continue
        if all(w == 1 for w in ws): S['chain_all'] += 1
        if all(w == 1 for w in ws[:-1]): S['chain_above'] += 1
        if ws[-1] > 1: S['holewide'] += 1
        if all(ws[i+1] <= ws[i] for i in range(len(ws)-1)): S['noninc'] += 1
        else:
            S['notnoninc'] += 1
            if len(cex_noninc) < 4: cex_noninc.append((M, ws))
        if ws[-1] > 1 and len(cex_wide) < 4: cex_wide.append((M, ws))
        X0 = T([D(ub, ZB)])
        X1 = surger(BODY, D(ub, X0))
        A1 = surger(BODY, D(ub, A0))
        for k in range(1, d+2):
            tB = rsub(BODY, k); tA = rsub(A1, k)
            if tB is None or tA is None: continue
            S['levels'] += 1
            hL = hole_depth(tB, v1)
            trace = []
            tag = walk(tB, BODY, hL, d, trace)
            tags[tag] = tags.get(tag, 0) + 1
            if tag == 'C' and len(cex_C) < 5:
                cex_C.append((M, k, ws, trace))
            ok_tB = lt(tB, BODY); ok_tA = lt(tA, X1)
            S['gt_tB'] += 1
            if not ok_tB: S['gt_tB_fail'] += 1
            S['gt_tA'] += 1
            if not ok_tA:
                S['gt_tA_fail'] += 1
    print('=== r69 TRANSPORT STEP-0 ===')
    for k in sorted(S): print(f'  {k:14s} {S[k]}')
    print('  terminal tags:', tags)
    print('--- widths CEX (hole level wide):')
    for M, ws in cex_wide: print('   ', M, ws)
    print('--- widths CEX (not non-increasing):')
    for M, ws in cex_noninc: print('   ', M, ws)
    print('--- case-(C) CEX:')
    for M, k, ws, tr in cex_C: print('   ', M, 'k=', k, 'widths=', ws, 'trace=', tr)

main()

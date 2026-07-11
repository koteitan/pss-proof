#!/usr/bin/env python3
"""r69 STEP-0c: the residual danger of the P-lemma is 'the left tree has a
principal with head exactly ub at the hole index'.  Test the cleanest killers:

 (S1) ub  not in allheads(BODY)                  -> P unconditional on subtrees
 (S2) ub  not in allheads(tB) for every spine sub-body tB (k>=1)
 (S3) every head of BODY is  != ub  OR  >= v1     (same as S1 basically)
 (S4) EXHAUSTIVE P-danger scan: for EVERY subtree L of BODY (hole-free part)
      and EVERY spine level R_j (hole depth e = d-j), does the danger fire?
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
    d = 0
    while True:
        ps = t[1]
        if not ps: return None
        last = ps[-1]
        if last[1] == v1 and last[2] == ZB: return d
        t = last[2]; d += 1
        if d > 60: return None

def rsub(t, k):
    for _ in range(k):
        if not t[1]: return None
        t = t[1][-1][2]
    return t

def allheads(t, acc):
    for p in t[1]:
        acc.add(p[1]); allheads(p[2], acc)
    return acc

def subtrees(t, acc):
    acc.append(t)
    for p in t[1]:
        subtrees(p[2], acc)
    return acc

def surger(t, q):
    ps = t[1]; last = ps[-1]
    if last[2] == ZB: return T(ps[:-1] + [q])
    return T(ps[:-1] + [D(last[1], surger(last[2], q))])

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 180
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 15
    S = dict(hosts=0, S1_ok=0, S1_fail=0, S4_pairs=0, S4_danger=0,
             ubheads_lt_v1=0)
    cex1, cex4 = [], []
    t0 = time.time()
    for M in gen(maxlen, tmax, seeds=[11, 22]):
        if time.time() - t0 > tmax: break
        j1 = Lng(M) - 1
        if not monoT(M) or not (1 < j1) or not hasParent(M, 1, j1): continue
        if not (condIII(M) or condIV(M)): continue
        jm3 = safe(Adm, M, safe(parent, M, 1, j1, budget=2), budget=2)
        jm1 = safe(Adm, M, safe(parent, M, 0, j1, budget=2), budget=2)
        if jm3 is None or jm1 is None or not (jm3 < jm1): continue
        N = seg(M, jm3, j1)
        TN = safe(Trans, N, budget=6)
        if TN is None or not TN[1]: continue
        BODY = TN[1][0][2]
        v1 = entry(M, 1, j1)
        if v1 == 0: continue
        ub = v1 - 1
        d = hole_depth(BODY, v1)
        if d is None: continue
        S['hosts'] += 1
        hs = allheads(BODY, set())
        if ub in hs:
            S['S1_fail'] += 1
            if len(cex1) < 5: cex1.append((M, v1, ub, sorted(hs), bucOf(BODY)))
        else:
            S['S1_ok'] += 1
        if any(h < v1 for h in hs): S['ubheads_lt_v1'] += 1
        # S4: exhaustive P-danger scan over ALL subtrees L of BODY and all
        # spine levels R_j (hole depth e = d-j).  Danger = the bottom (e=0)
        # compare index reaches a left principal with head == ub.
        Rd = rsub(BODY, d)          # the hole level, ys @ [D_v1 0]
        ys = Rd[1][:-1]
        for L in subtrees(BODY, []):
            xs = L[1]
            S['S4_pairs'] += 1
            if len(xs) <= len(ys): continue
            if any(xs[i] != ys[i] for i in range(len(ys))): continue
            c = xs[len(ys)][1]
            if c == ub:
                S['S4_danger'] += 1
                if len(cex4) < 5: cex4.append((M, v1, ub, bucOf(L), bucOf(Rd)))
    print('=== r69 STEP-0c ===')
    for k in sorted(S): print(f'  {k:14s} {S[k]}')
    print('--- S1 CEX (ub IS a head of BODY):')
    for x in cex1: print('   ', x[0], 'v1=', x[1], 'ub=', x[2], 'heads=', x[3])
    print('--- S4 CEX (bottom danger, over ALL subtrees):')
    for x in cex4: print('   ', x)

main()

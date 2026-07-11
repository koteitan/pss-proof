#!/usr/bin/env python3
"""r70 STEP-0: deep stress-test of the LAST census residual OKH.

  OKH:  ox9_ok v1 ub (bpHeadT (Trans (s84x_N P)))
  ox9_ok v ub t  ==  every principal D_c XB anywhere in t satisfies
                       v <= c   OR   lessBT XB (D_ub 0)
  leafcond t v1  ==  every principal D_c XB anywhere in t with c < v1 has XB = 0
  (hge ==> leafcond ==> ok;  hge is REFUTED (r69))

CRITICAL (r70): leafcond/ok are VACUOUSLY true on any host whose body has no head
< v1 (i.e. where hge holds).  So we report the NON-VACUOUS count separately:
  smallhosts = hosts whose body carries at least one head < v1.
Only those actually test leafcond.  Corpus is PURE ST_PS (diagSeq + oper closure)
so no synthetic non-standard host can produce a bogus verdict.

usage: _r70_okh_step0.py [tmax_sec] [maxlen] [nmax]
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


# ---------------------------------------------------------------- corpus
def gen(maxlen, tmax, nmax, seeds):
    """PURE ST_PS: every yielded M is diagSeq(u,v) or an oper-iterate thereof."""
    seen = set(); t0 = time.time()
    starts = [diagSeq(u, u + d) for u in range(0, 6) for d in range(1, 8)]
    dq = deque()
    for s in starts:
        k = tuple(s)
        if k not in seen: seen.add(k); dq.append(s); yield s
    # BFS layer (bounded time slice)
    tb = t0 + tmax * 0.45
    while dq and time.time() < tb:
        M = dq.popleft()
        for nn in range(1, nmax + 1):
            M2 = safe(oper, M, nn, budget=3)
            if M2 is None or M2 == M or Lng(M2) > maxlen: continue
            k = tuple(M2)
            if k not in seen:
                seen.add(k); dq.append(M2); yield M2
    # deep random walks (reach long/deep hosts the BFS frontier never reaches)
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
                    # try to keep walking with a smaller n rather than dying
                    M2 = safe(oper, M, 1, budget=3)
                    if M2 is None or M2 == M or Lng(M2) > maxlen: break
                M = M2; k = tuple(M)
                if k not in seen:
                    seen.add(k); yield M


def condIII(M):
    j1 = Lng(M) - 1; jp = parent(M, 0, j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp) >= entry(M,1,j1) and adm(M, jp)
def condIV(M):
    j1 = Lng(M) - 1; jp = parent(M, 0, j1)
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

def smallheads(t, v1, acc):
    """collect (head, body) for every principal anywhere in t with head < v1"""
    for p in t[1]:
        if p[1] < v1: acc.append((p[1], p[2]))
        smallheads(p[2], v1, acc)
    return acc

def ok(t, v1, X0):
    for p in t[1]:
        if not (v1 <= p[1] or lt(p[2], X0)): return False
        if not ok(p[2], v1, X0): return False
    return True

def leafcond(t, v1):
    for p in t[1]:
        if p[1] < v1 and p[2] != ZB: return False
        if not leafcond(p[2], v1): return False
    return True

def surger(t, q):
    ps = t[1]; last = ps[-1]
    if last[2] == ZB: return T(ps[:-1] + [q])
    return T(ps[:-1] + [D(last[1], surger(last[2], q))])
def rsub(t, k):
    for _ in range(k):
        if not t[1]: return None
        t = t[1][-1][2]
    return t


def main():
    tmax   = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    nmax   = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    S = dict(hosts=0, small_hosts=0, ok=0, ok_fail=0, leaf=0, leaf_fail=0,
             hge=0, hge_fail=0, tgt=0, tgt_fail=0, levels=0, maxlenseen=0,
             small_principals=0)
    cex_ok, cex_leaf = [], []
    t0 = time.time()
    for M in gen(maxlen, tmax, nmax, seeds=[11, 22, 33, 44, 55, 66, 77]):
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
        d = hole_depth(BODY, v1)
        if d is None: continue
        S['hosts'] += 1
        S['maxlenseen'] = max(S['maxlenseen'], Lng(M))
        X0 = T([D(ub, ZB)])
        sh = smallheads(BODY, v1, [])
        if sh:
            S['small_hosts'] += 1
            S['small_principals'] += len(sh)
        if ok(BODY, v1, X0): S['ok'] += 1
        else:
            S['ok_fail'] += 1
            if len(cex_ok) < 4: cex_ok.append((list(M), v1, ub, bucOf(BODY)))
        if leafcond(BODY, v1): S['leaf'] += 1
        else:
            S['leaf_fail'] += 1
            if len(cex_leaf) < 4:
                cex_leaf.append((list(M), v1, bucOf(BODY),
                                 [(h, bucOf(b)) for h, b in sh]))
        if all(h >= v1 for h, _ in sh) and not sh: S['hge'] += 1
        elif not sh: S['hge'] += 1
        else: S['hge_fail'] += 1
        # the actual downstream target (transport), as a sanity cross-check
        X1 = surger(BODY, D(ub, X0)); A1 = surger(BODY, D(ub, A0))
        for k in range(1, d + 2):
            tA = rsub(A1, k)
            if tA is None: continue
            S['levels'] += 1
            if lt(tA, X1): S['tgt'] += 1
            else: S['tgt_fail'] += 1
    print(f'=== r70 STEP-0  maxlen={maxlen} nmax={nmax} tmax={tmax}s '
          f'elapsed={time.time()-t0:.0f}s ===')
    for k in sorted(S): print(f'  {k:17s} {S[k]}')
    nz = S['small_hosts']
    print(f'  >> NON-VACUOUS leafcond tests (hosts with a head < v1): {nz}'
          f'  ({S["small_principals"]} small principals)')
    print('--- ox9_ok CEX:')
    for x in cex_ok: print('   ', x)
    print('--- leafcond CEX:')
    for x in cex_leaf: print('   M=', x[0], ' v1=', x[1], '\n      body=', x[2],
                             '\n      smallheads=', x[3])

main()

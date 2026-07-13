#!/usr/bin/env python3
"""r71 KK front.  The POSITIONAL analysis of the census walk.

KK(k):  lessBT (rsub body k) X1,   X1 = body[hole  D_v1 0  |->  D_ub (D_ub 0)],
        hole = LAST principal of  rsub body dR  (the deepest right-spine level).

A principal x = D_a s is DANGEROUS iff
        lessBP x (D_v1 0)  holds  but  lessBP x (D_ub (D_ub 0))  does NOT,
i.e.    a = ub  and  NOT lessBT s (D_ub 0).      (a < v1  ==>  a <= ub.)
Only a DANGEROUS principal sitting at a HOLE-ALIGNED position can break the
transport (ox10_lexP).  This script measures, per census host and per peel
level k:

  WALK   : does the walk of (rsub body k) against body ever meet a DANGEROUS
           principal at a hole-aligned position?          (the TRUE residual)
  HOLE   : does the walk reach the bottom hole slot at all?
  DEC    : level/case at which the walk is decided (A / B / C-chain).
  BG_G   : does the bottom guard hold on the whole closed set
           S = {body} u GBT v1 body   (a PROVABLE closure)?   + non-vacuity
  BG_SUB : same on ALL subterms of body.
  FH     : "first principal of every t in S has head >= v1"  (+ non-vacuity)
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

# ---------------------------------------------------------------- danger
def dangerous(x, v1, ub, X0):
    """x can be compared < D_v1 0 but NOT < D_ub X0"""
    a, s = x[1], x[2]
    if not (a < v1): return False           # not < D_v1 0 at all
    # lessBP x (D_ub X0)  =  a < ub  or  (a == ub and s < X0)
    if a < ub: return False
    if a == ub and lt(s, X0): return False
    return True

# ---------------------------------------------------------------- walk
def walk(Z, W, j, dR, v1, ub, X0, st):
    """walk lessBT Z W with W = W_j on the hole path.  Returns a tag:
       'A'  decided strictly left of the hole-aligned index (SAFE)
       'Ap' Z's list is a prefix of W's, len <= m  (SAFE)
       'B'  decided AT the hole-aligned index by a strictly smaller head (SAFE, j<dR)
       'HOLE-SAFE'  reached the bottom slot, principal NOT dangerous
       'HOLE-BAD'   reached the bottom slot, principal DANGEROUS   (KK BREAKS)
       'FALSE' the walk says NOT less (should never happen: contradicts the
               proven ox8_body_rspine_lessBT)
    """
    xs, ys = Z[1], W[1]
    m = len(ys) - 1                       # hole-aligned index at this level
    for i in range(m):
        if i >= len(xs):
            st['maxlvl'] = max(st['maxlvl'], j)
            return 'Ap'                   # xs proper prefix of ps -> SAFE
        if xs[i] == ys[i]: continue
        st['maxlvl'] = max(st['maxlvl'], j)
        return 'A'                        # decided strictly left of the hole
    # first m principals of Z equal ps_j
    st['maxlvl'] = max(st['maxlvl'], j)
    if len(xs) <= m:
        return 'Ap'                       # xs == ps_j exactly (len m) -> SAFE
    x = xs[m]; y = ys[m]                  # y = last principal of W_j
    if j == dR:
        st['hole'] += 1
        if dangerous(x, v1, ub, X0):
            return 'HOLE-BAD'
        # verdict must still be "less" for KK's premise to be usable
        return 'HOLE-SAFE' if ltP(x, y) else 'FALSE'
    # j < dR : y = D_{w_j} W_{j+1}
    if x[1] < y[1]: return 'B'
    if x[1] > y[1]: return 'FALSE'
    return walk(x[2], y[2], j + 1, dR, v1, ub, X0, st)   # case C: descend

# ---------------------------------------------------------------- sets
def subterms(t, acc):
    acc.append(t)
    for p in t[1]: subterms(p[2], acc)
    return acc
def gset(t, v1, acc):
    """{t} u GBT v1 t   (closed under bodies of principals with head >= v1)"""
    acc.append(t)
    for p in t[1]:
        if p[1] >= v1: gset(p[2], v1, acc)
    return acc

def bottom_guard(S, psR, v1, ub, X0, st, key):
    """for every t in S with list = psR @ x # rest : x must not be dangerous"""
    m = len(psR); ok = True
    for t in S:
        xs = t[1]
        if len(xs) <= m: continue
        if xs[:m] != psR: continue
        x = xs[m]
        if x[1] < v1:
            st[key + '_exercised'] += 1     # NON-VACUOUS use of the guard
            if dangerous(x, v1, ub, X0):
                st[key + '_fail'] += 1; ok = False
    return ok

def main():
    tmax   = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    nmax   = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    st = dict(hosts=0, levels=0, KK=0, KK_fail=0, hole=0, maxlvl=0,
              A=0, Ap=0, B=0, HOLESAFE=0, HOLEBAD=0, FALSE=0,
              BGG_exercised=0, BGG_fail=0, BGG_hostfail=0,
              BGS_exercised=0, BGS_fail=0, BGS_hostfail=0,
              FH_exercised=0, FH_fail=0,
              m0=0, mpos=0, dRmax=0, gap_min=99)
    cex = []; bgcex = []
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
        TN = safe(Trans, N, budget=10)
        if TN is None or not TN[1]: continue
        BODY = TN[1][0][2]
        v1 = entry(M, 1, j1)
        if v1 == 0: continue
        ub = v1 - 1
        dR = hole_depth(BODY, v1)
        if dR is None: continue
        st['hosts'] += 1
        st['dRmax'] = max(st['dRmax'], dR)
        X0 = T([D(ub, ZB)])
        X1 = surger(BODY, D(ub, X0))
        WdR = rsub(BODY, dR)
        psR = WdR[1][:-1]
        if len(psR) == 0: st['m0'] += 1
        else: st['mpos'] += 1
        # --- the closed sets
        S_G   = gset(BODY, v1, [])
        S_SUB = subterms(BODY, [])
        if not bottom_guard(S_G, psR, v1, ub, X0, st, 'BGG'):
            st['BGG_hostfail'] += 1
            if len(bgcex) < 3: bgcex.append(('BGG', list(M), v1, len(psR)))
        if not bottom_guard(S_SUB, psR, v1, ub, X0, st, 'BGS'):
            st['BGS_hostfail'] += 1
        # --- FIRST-HEAD conjecture on S_G
        for t in S_G:
            if not t[1]: continue
            st['FH_exercised'] += 1
            if t[1][0][1] < v1: st['FH_fail'] += 1
        # --- the walks
        for k in range(1, dR + 1):
            Zk = rsub(BODY, k)
            if Zk is None: continue
            st['levels'] += 1
            kk = lt(Zk, X1)
            st['KK' if kk else 'KK_fail'] += 1
            sub = dict(hole=0, maxlvl=-1)
            tag = walk(Zk, BODY, 0, dR, v1, ub, X0, sub)
            st['hole'] += sub['hole']
            st['gap_min'] = min(st['gap_min'], dR - sub['maxlvl'])
            key = {'A':'A','Ap':'Ap','B':'B','HOLE-SAFE':'HOLESAFE',
                   'HOLE-BAD':'HOLEBAD','FALSE':'FALSE'}[tag]
            st[key] += 1
            if (not kk or tag in ('HOLE-BAD','FALSE')) and len(cex) < 4:
                cex.append((list(M), v1, k, dR, tag, kk))
    el = time.time() - t0
    print(f'=== r71 WALK  maxlen={maxlen} nmax={nmax} elapsed={el:.0f}s ===')
    for k in ('hosts','levels','KK','KK_fail','dRmax','m0','mpos','gap_min'):
        print(f'  {k:16s} {st[k]}')
    print('  --- walk decision cases (per peel level):')
    for k in ('A','Ap','B','HOLESAFE','HOLEBAD','FALSE','hole'):
        print(f'  {k:16s} {st[k]}')
    print('  --- bottom guard on the CLOSED set S = {body} u GBT v1 body:')
    for k in ('BGG_exercised','BGG_fail','BGG_hostfail'):
        print(f'  {k:16s} {st[k]}')
    print('  --- bottom guard on ALL subterms:')
    for k in ('BGS_exercised','BGS_fail','BGS_hostfail'):
        print(f'  {k:16s} {st[k]}')
    print('  --- FIRST-HEAD (head of first principal >= v1) on S:')
    for k in ('FH_exercised','FH_fail'):
        print(f'  {k:16s} {st[k]}')
    print('--- CEX (KK fail / HOLE-BAD / FALSE):')
    for x in cex: print('   ', x)
    print('--- BG CEX:')
    for x in bgcex: print('   ', x)

main()

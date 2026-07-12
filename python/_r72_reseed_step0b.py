#!/usr/bin/env python3
"""r72 RESEED STEP-0: under the CORRECTED Buchholz fundamental sequence the
operB core is the 0_B-seeded tower  Y_n = ins^n(0_B)  (one level deeper),
NOT the old X_n = ins^n(D_ub 0).  Check the new census sandwich:

  ours  A1 = ins(A0)          A0 = bpHeadT(Trans(Pred(s84x_N M)))
  lo    Y1 = ins(0_B)         (core of operB(numBT(k-1)))
  hi    Y3 = ins(ins(ins 0_B))(core of operB(numBT(k+1)))

  ordlo   : leBT Y1 A1
  ordhi   : leBT A1 Y3
  Lbase   : leBT (D_ub 0) Y1                       [PROVED in Isabelle]
  setleY  : forall u. GBT u A1  <=  {Y1} u GBT u Y1     <-- THE RISKY ONE
  setleX  : forall u. GBT u A1  <=  {X1} u GBT u X1     (old, X1 = ins(D_ub 0))
  setleY2 : forall u. GBT u A1  <=  {Y2} u GBT u Y2     (fallback: lo = numBT k)
  ordlo2  : leBT Y2 A1                                  (fallback ordlo)
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
def le(a, b): return a == b or lt(a, b)

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

def GBT(u, t):
    out = []
    for p in t[1]:
        if u <= p[1]:
            out.append(p[2]); out.extend(GBT(u, p[2]))
    return out

def heads(t, acc):
    for p in t[1]:
        acc.add(p[1]); heads(p[2], acc)
    return acc

def setle(a, aLo, us):
    """forall u in us: every x in GBT u a is <= some y in {aLo} u GBT u aLo."""
    for u in us:
        rhs = [aLo] + GBT(u, aLo)
        for x in GBT(u, a):
            if not any(le(x, y) for y in rhs):
                return False, u, x
    return True, None, None

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
    if last[2] == ZB:
        return T(ps[:-1] + [q])
    return T(ps[:-1] + [D(last[1], surger(last[2], q))])

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    S = dict(pool=0, hosts=0, ltJ=0, notltJ=0, s0empty=0,
             base1Y=0, base1Y_F=0, base1X=0, base1X_F=0, Y1leX1=0, Y1leX1_F=0,
             ordlo=0, ordlo_F=0, ordhi=0, ordhi_F=0,
             lbase=0, lbase_F=0,
             setleX=0, setleX_F=0, setleY=0, setleY_F=0,
             setleY2=0, setleY2_F=0, ordlo2=0, ordlo2_F=0)
    cexY, cexY2, cexhi = [], [], []
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
        if jm3 is None or jm1 is None: continue
        N = seg(M, jm3, j1)
        TN = safe(Trans, N, budget=6)
        TPN = safe(Trans, Pred(N), budget=6)
        if TN is None or TPN is None or not TN[1] or not TPN[1]: continue
        BODY = TN[1][0][2]
        A0 = TPN[1][0][2]
        v1 = entry(M, 1, j1)
        if v1 == 0: continue
        ub = v1 - 1
        d = hole_depth(BODY, v1)
        if d is None: continue
        S['hosts'] += 1
        S['ltJ' if jm3 < jm1 else 'notltJ'] += 1
        if BODY == T([D(v1, ZB)]): S['s0empty'] += 1
        X0 = T([D(ub, ZB)])
        X1 = surger(BODY, D(ub, X0))
        A1 = surger(BODY, D(ub, A0))
        Y1 = surger(BODY, D(ub, ZB))
        Y2 = surger(BODY, D(ub, Y1))
        Y3 = surger(BODY, D(ub, Y2))
        us = sorted(heads(A1, heads(Y3, heads(X1, {0}))))
        us = [u for u in us] + [max(us) + 1]
        for tag, ok in (('base1Y', lt(A0, Y1)), ('base1X', lt(A0, X1)),
                        ('Y1leX1', le(Y1, X1)),
                        ('lbase', le(X0, Y1)),
                        ('ordlo', le(Y1, A1)),
                        ('ordlo2', le(Y2, A1)),
                        ('ordhi', le(A1, Y3))):
            S[tag if ok else tag + '_F'] += 1
            if not ok and tag in ('ordhi','base1Y') and len(cexhi) < 4:
                cexhi.append((tag, M, BODY, A0))
        for tag, aLo in (('setleX', X1), ('setleY', Y1), ('setleY2', Y2)):
            ok, u, x = setle(A1, aLo, us)
            S[tag if ok else tag + '_F'] += 1
            if not ok:
                lst = cexY if tag == 'setleY' else (cexY2 if tag == 'setleY2' else [])
                if len(lst) < 3: lst.append((M, BODY, A0, u, x))
    print('=== r72 RESEED STEP-0 ===')
    for k in sorted(S): print(f'  {k:12s} {S[k]}')
    print('--- setleY CEX (lo = Y1 = ins 0):')
    for M, B, A0, u, x in cexY: print('   M=', M, '\n     BODY=', B, '\n     A0=', A0, 'u=', u, 'x=', x)
    print('--- setleY2 CEX (lo = Y2 = ins ins 0):')
    for M, B, A0, u, x in cexY2: print('   M=', M, '\n     BODY=', B, '\n     A0=', A0, 'u=', u, 'x=', x)
    print('--- ordhi CEX:')
    for tg, M, B, A0 in cexhi: print('  ', tg, 'M=', M, 'BODY=', B, 'A0=', A0)

main()

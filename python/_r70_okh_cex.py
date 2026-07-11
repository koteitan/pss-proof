#!/usr/bin/env python3
"""r70: RIGOROUS validation of the OKH counterexample.

Generates a PURE ST_PS corpus with PROVENANCE (seed diagSeq + oper chain),
finds hosts where OKH's ox9_ok is FALSE, and for the first few prints a full
audit of every census hypothesis:
  1. P in ST_PS   -- explicit seed + oper chain, replayed and checked
  2. P in PT_PS   -- monoT (T_PS is automatic for oper-iterates)
  3. hasParent P 1 (Lng P - 1),  1 < Lng P - 1
  4. transCondIII P or transCondIV P
  5. Trans P in OT_B  (buchholz.in_OT)
  6. s84x_jm3 P < transJm1 P
  7. ox9_ok v1 ub (bpHeadT (Trans (s84x_N P)))   ===>  FALSE  (the refutation)
plus the DOWNSTREAM target (does SETLE1 itself survive?).
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
def fmt(t): return bu.fmt(bucOf(t))

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
def bad(t, v1, X0, path='body'):
    out = []
    for i, p in enumerate(t[1]):
        c, XB = p[1], p[2]
        pth = f'{path}[{i}]'
        if not (v1 <= c or lt(XB, X0)): out.append((pth, c, bucOf(XB)))
        out += bad(XB, v1, X0, pth + '.body')
    return out

# ---------------- corpus with provenance ----------------
def gen(maxlen, tmax, nmax, seeds):
    seen = set(); t0 = time.time()
    starts = [diagSeq(u, u + d) for u in range(0, 6) for d in range(1, 8)]
    dq = deque()
    for s in starts:
        k = tuple(s)
        if k not in seen:
            seen.add(k); dq.append((s, s, [])); yield s, s, []
    tb = t0 + tmax * 0.45
    while dq and time.time() < tb:
        M, sd, ch = dq.popleft()
        for nn in range(1, nmax + 1):
            M2 = safe(oper, M, nn, budget=3)
            if M2 is None or M2 == M or Lng(M2) > maxlen: continue
            k = tuple(M2)
            if k not in seen:
                seen.add(k); dq.append((M2, sd, ch + [nn])); yield M2, sd, ch + [nn]
    for s in seeds:
        rng = random.Random(s)
        for st in starts:
            if time.time() - t0 > tmax: return
            M = list(st); ch = []
            for _ in range(400):
                if time.time() - t0 > tmax: return
                nn = rng.randrange(1, nmax + 1)
                M2 = safe(oper, M, nn, budget=3)
                if M2 is None or M2 == M or Lng(M2) > maxlen:
                    nn = 1
                    M2 = safe(oper, M, 1, budget=3)
                    if M2 is None or M2 == M or Lng(M2) > maxlen: break
                M = M2; ch = ch + [nn]; k = tuple(M)
                if k not in seen:
                    seen.add(k); yield M, st, list(ch)

def report(M, seed, chain):
    j1 = Lng(M) - 1
    print('=' * 78)
    print('HOST P =', M)
    print('  Lng =', Lng(M), ' j1 =', j1)
    print('  ST_PS witness: seed diagSeq =', seed)
    print('                 oper chain   =', chain)
    X = list(seed)
    for n in chain: X = oper(X, n)
    print('                 replay == P  :', X == M)
    print('  monoT (PT_PS)              :', monoT(M))
    print('  hasParent P 1 (Lng-1)      :', hasParent(M, 1, j1))
    print('  1 < Lng-1                  :', 1 < j1)
    print('  transCondIII / transCondIV :', condIII(M), '/', condIV(M))
    jm2 = parent(M, 1, j1); jm3 = Adm(M, jm2)
    j0 = parent(M, 0, j1); jm1 = Adm(M, j0)
    print(f'  s84x_jm3={jm3}  transJm1={jm1}   jm3 < jm1 : {jm3 < jm1}')
    TP = Trans(M)
    print('  Trans P in OT_B            :', bu.in_OT(bucOf(TP)))
    N = seg(M, jm3, j1)
    print('  s84x_N P =', N)
    TN = Trans(N); TPN = Trans(Pred(N))
    BODY = TN[1][0][2]; A0 = TPN[1][0][2]
    v1 = entry(M, 1, j1); ub = v1 - 1
    X0 = T([D(ub, ZB)])
    print(f'  v1 = {v1}   ub = {ub}    X0 = D_{ub} 0 = {bucOf(X0)}')
    print('  Trans(s84x_N P)  =', fmt(TN))
    print('  BODY             =', fmt(BODY))
    print('  BODY (raw)       =', bucOf(BODY))
    print('  A0               =', fmt(A0))
    v = bad(BODY, v1, X0)
    print('  >>> ox9_ok (OKH) =', not v, '   <<<')
    for pth, c, XB in v:
        print(f'      VIOLATION {pth}: D_{c} XB, XB = {bu.fmt(XB)} = {XB}')
        print(f'         head {c} < v1 {v1}  AND  NOT (XB < X0)  '
              f'[XB == X0 ? {XB == bucOf(X0)}]')
    d = hole_depth(BODY, v1)
    print('  hole depth dR =', d)
    if d is not None:
        X1 = surger(BODY, D(ub, X0)); A1 = surger(BODY, D(ub, A0))
        tg = [(k, lt(rsub(A1, k), X1)) for k in range(1, d + 2)
              if rsub(A1, k) is not None]
        print('  DOWNSTREAM TARGET lessBT (rsub A1 k) X1:', tg)
        print('  base1: lessBT A0 X1 =', lt(A0, X1))

def main():
    tmax   = int(sys.argv[1]) if len(sys.argv) > 1 else 420
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    nmax   = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    want   = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    t0 = time.time(); found = 0; hosts = 0
    for M, sd, ch in gen(maxlen, tmax, nmax, [11, 22, 33]):
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
        BODY = TN[1][0][2]
        v1 = entry(M, 1, j1)
        if v1 == 0: continue
        X0 = T([D(v1 - 1, ZB)])
        hosts += 1
        if hole_depth(BODY, v1) is None: continue
        if bad(BODY, v1, X0):
            report(M, sd, ch); found += 1
            if found >= want: break
    print(f'\nscanned {hosts} census hosts; printed {found} OKH counterexamples')

main()

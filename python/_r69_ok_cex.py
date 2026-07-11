#!/usr/bin/env python3
"""r69: evaluate ox9_ok / ox9_hge / target on the two hosts that REFUTE ox9_hge."""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, entry, monoT, seg, parent, hasParent, Adm
from trans_model import Trans, Pred, adm
import buchholz as bu

ZB = ('T', [])
def D(v, t): return ('D', v, t)
def T(ps): return ('T', ps)
def bucOf(t): return [('D', p[1], bucOf(p[2])) for p in t[1]]
def lt(a, b): return bu.lt_term(bucOf(a), bucOf(b))

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

def hge(t, v1):
    return all(p[1] >= v1 and hge(p[2], v1) for p in t[1])

def ok(t, v1, X0):
    return all((v1 <= p[1] or lt(p[2], X0)) and ok(p[2], v1, X0) for p in t[1])

def leafcond(t, v1):
    return all((p[1] >= v1 or p[2] == ZB) and leafcond(p[2], v1) for p in t[1])

HOSTS = [
 [(0,0),(1,1),(2,2),(3,1),(4,0),(5,1),(6,2),(7,0),(6,1),(7,2),(8,0),(7,1),(8,1)],
 [(0,0),(1,1),(2,2),(3,1),(4,0),(5,1),(6,2),(7,0),(6,1),(7,2),(8,0),(7,1),(8,2),
  (8,1),(9,2),(9,1),(10,1)],
]
for M in HOSTS:
    j1 = Lng(M)-1
    jm3 = Adm(M, parent(M, 1, j1)); jm1 = Adm(M, parent(M, 0, j1))
    N = seg(M, jm3, j1)
    TN = Trans(N); TPN = Trans(Pred(N))
    BODY = TN[1][0][2]; A0 = TPN[1][0][2]
    v1 = entry(M, 1, j1); ub = v1 - 1
    d = hole_depth(BODY, v1)
    X0 = T([D(ub, ZB)])
    X1 = surger(BODY, D(ub, X0)); A1 = surger(BODY, D(ub, A0))
    tgt = all(lt(rsub(A1, k), X1) for k in range(1, d+2) if rsub(A1, k) is not None)
    print(f'M(len={Lng(M)}) v1={v1} ub={ub} d={d}')
    print(f'   body      = {bucOf(BODY)}')
    print(f'   ox9_hge   = {hge(BODY, v1)}      <-- refutes the r69-first hypothesis')
    print(f'   ox9_ok    = {ok(BODY, v1, X0)}   <-- the CORRECTED hypothesis')
    print(f'   leafcond  = {leafcond(BODY, v1)}')
    print(f'   TARGET lessBT (ox8_rsub A1 k) X1 for all k = {tgt}')

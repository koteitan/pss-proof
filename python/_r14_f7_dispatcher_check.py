#!/usr/bin/env python3
"""r14-F7: empirical validation of the §8.7 fseq_descend DISPATCHER case tree.

Target: p_8_7_fseq_descend  (M : ST_PS, n >= 1, Lng M > 1 ==> Trans(M[n]) < Trans M).
The dispatcher case tree to validate on the GENUINE regime (diagSeq seeds closed
under oper, i.e. literal ST_PS members):

  [A]  M[n] = Pred M                        -> Pred-descent (proven engine)
  [B]  M[n] != Pred M:
       - case-B facts: last entry != (0,0), hasParent M i1 j1, n >= 2
       [B-mono]  exactly one of transCondI..VI holds (exhaustive+disjoint);
                 condII/III/IV/V force j1 > 1 in case B;
                 condI  j1=1: M[n] = replicate n (u,u), Trans M = D_u(D_0 0)
                 condVI j1=1: M[n] = [(u+k,u)]_{k<n},  Trans M = D_u(D_{u+1} 0)
       [B-multi] Pcut M < Lng M - 1;  M[n] = A @ PJ[n];  P(M[n]) = P A @ P(PJ[n]);
                 PJ mono, Lng PJ > 1, PJ standard (component of standard);
                 additivity: Trans(M[n]) = Trans A +B corr, where
                   corr = D_0 0 +B Trans(PJ[n])  if  P(PJ[n])!0 = [(0,0)]
                        = Trans(PJ[n])           otherwise;
                 exceptional case: Trans PJ = Trm [DB w body], w=0 -> body != 0
  final: lessBT (Trans (M[n])) (Trans M)   [the target statement itself]
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, Pcut, monoT, zeroT, multiT, seg, diagSeq,
                       parent, hasParent, idx1, oper, Pred, fmt)
import red_model as rm
import trans_model as tm
from trans_model import Trans, ZB, Dpt, addBT, adm, condI, condIII, condV, condVI

def condII(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) == 0 and not adm(M, jp)
def condIV(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return (entry(M,1,j1) > 0 and entry(M,1,jp) >= entry(M,1,j1)
            and not adm(M, jp))

def lessBP(p, q):
    # DB u a < DB v b  <->  u < v  or  (u = v and a < b)
    return p[1] < q[1] or (p[1] == q[1] and lessBT(p[2], q[2]))
def lessBT(a, b):
    ps, qs = a[1], b[1]
    if not ps: return bool(qs)
    if not qs: return False
    return lessBP(ps[0], qs[0]) or (ps[0] == qs[0]
                                    and lessBT(('T',ps[1:]), ('T',qs[1:])))

# ---- genuine ST_PS pool: diagSeq seeds closed under oper (the ST_PS definition)
def gen_pool(maxlen=9, maxn=4, maxseed=3, cap=6000):
    seen = set(); frontier = []
    for u in range(maxseed):
        for v in range(u, u+maxseed+1):
            M = tuple(diagSeq(u, v))
            if M not in seen:
                seen.add(M); frontier.append(list(M))
    pool = list(frontier)
    while frontier and len(pool) < cap:
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in range(1, maxn+1):
                N = oper(M, n)
                if Lng(N) > maxlen: continue
                t = tuple(N)
                if t not in seen:
                    seen.add(t); nxt.append(N); pool.append(N)
                    if len(pool) >= cap: break
            if len(pool) >= cap: break
        frontier = nxt
    return pool

# ---- memoize Trans/Mark (pure functions; the model recomputes exponentially)
_tmemo, _mmemo = {}, {}
_Trans0, _Mark0 = tm.Trans, tm.Mark
def _TransM(M, depth=0):
    k = tuple(M)
    if k not in _tmemo: _tmemo[k] = _Trans0(M, depth)
    return _tmemo[k]
def _MarkM(M, m, depth=0):
    k = (tuple(M), m)
    if k not in _mmemo: _mmemo[k] = _Mark0(M, m, depth)
    return _mmemo[k]
tm.Trans, tm.Mark = _TransM, _MarkM
Trans = _TransM

import signal
class _TO(Exception): pass
def _hdl(s, f): raise _TO()
signal.signal(signal.SIGALRM, _hdl)

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--maxlen', type=int, default=8)
    ap.add_argument('--cap', type=int, default=1200)
    ap.add_argument('--maxn', type=int, default=3)
    ap.add_argument('--seeds', type=int, default=3)
    a = ap.parse_args()
    pool = [M for M in gen_pool(maxlen=a.maxlen, maxn=a.maxn,
                                maxseed=a.seeds, cap=a.cap) if Lng(M) > 1]
    NS = list(range(1, a.maxn + 1))
    stats = {k: 0 for k in
             ['A','B','mono','multi','cI','cII','cIII','cIV','cV','cVI',
              'cI_j1eq1','cVI_j1eq1','multi_exc','final']}
    fails = []
    total = 0
    skipped = 0
    for M in pool:
        j1 = Lng(M) - 1
        TM = Trans(M)
        for n in NS:
            Mn = oper(M, n)
            signal.alarm(20)
            try:
                Trans(Mn)
            except _TO:
                skipped += 1
                continue
            finally:
                signal.alarm(0)
            total += 1
            # ---- final target statement (sanity of p_8_7_fseq_descend itself)
            if not lessBT(Trans(Mn), TM):
                fails.append(('FINAL', fmt(M), n)); continue
            stats['final'] += 1
            if Mn == Pred(M):
                stats['A'] += 1; continue
            stats['B'] += 1
            # case-B facts
            if M[j1] == (0,0):
                fails.append(('B-lastzero', fmt(M), n)); continue
            i1 = idx1(M, j1)
            if not hasParent(M, i1, j1):
                fails.append(('B-noparent', fmt(M), n)); continue
            if n < 2:
                fails.append(('B-n1', fmt(M), n)); continue
            if monoT(M):
                stats['mono'] += 1
                cs = [condI(M), condII(M), condIII(M), condIV(M), condV(M), condVI(M)]
                if sum(cs) != 1:
                    fails.append(('mono-conds', fmt(M), n, cs)); continue
                ci = cs.index(True)
                stats[['cI','cII','cIII','cIV','cV','cVI'][ci]] += 1
                if ci in (1,2,3,4) and j1 <= 1:      # II,III,IV,V force j1>1
                    fails.append(('mono-j1', fmt(M), n, ci)); continue
                u = entry(M, 1, 0)
                if ci == 0 and j1 == 1:              # condI, j1=1
                    stats['cI_j1eq1'] += 1
                    if Mn != [(u,u)]*n:
                        fails.append(('cI-j1eq1-oper', fmt(M), n)); continue
                    if TM != Dpt(u, Dpt(0, ZB)):
                        fails.append(('cI-j1eq1-TM', fmt(M), n)); continue
                if ci == 5 and j1 == 1:              # condVI, j1=1
                    stats['cVI_j1eq1'] += 1
                    if Mn != [(u+k, u) for k in range(n)]:
                        fails.append(('cVI-j1eq1-oper', fmt(M), n)); continue
                    if TM != Dpt(u, Dpt(u+1, ZB)):
                        fails.append(('cVI-j1eq1-TM', fmt(M), n)); continue
                continue
            # ---- multi
            stats['multi'] += 1
            c = Pcut(M)
            if not (c < Lng(M) - 1):
                fails.append(('multi-pcut', fmt(M), n)); continue
            A, PJ = M[:c], M[c:]
            if not (monoT(PJ) and Lng(PJ) > 1):
                fails.append(('multi-PJ', fmt(M), n)); continue
            PJn = oper(PJ, n)
            if Mn != A + PJn:
                fails.append(('multi-oper', fmt(M), n)); continue
            if P(Mn) != P(A) + P(PJn):
                fails.append(('multi-P', fmt(M), n)); continue
            exc = (P(PJn)[0] == [(0,0)])
            corr = addBT(Dpt(0, ZB), Trans(PJn)) if exc else Trans(PJn)
            if Trans(Mn) != addBT(Trans(A), corr):
                fails.append(('multi-add', fmt(M), n, exc)); continue
            TPJ = Trans(PJ)
            if len(TPJ[1]) != 1:
                fails.append(('multi-TPJ-shape', fmt(M), n)); continue
            if exc:
                stats['multi_exc'] += 1
                w, body = TPJ[1][0][1], TPJ[1][0][2]
                if w == 0 and body == ZB:
                    fails.append(('multi-exc-body0', fmt(M), n)); continue
                if not lessBT(corr, TPJ):
                    fails.append(('multi-exc-lt', fmt(M), n)); continue
            else:
                if not lessBT(Trans(PJn), TPJ):
                    fails.append(('multi-comp-lt', fmt(M), n)); continue
    print(f"pool={len(pool)} (M,n) pairs={total} skipped(timeout)={skipped}")
    print(f"stats={stats}")
    print(f"FAILS={len(fails)}")
    for f in fails[:25]: print("  ", f)
    print("coverage: final descent %d/%d ; caseA=%d caseB=%d (mono=%d multi=%d)"
          % (stats['final'], total, stats['A'], stats['B'],
             stats['mono'], stats['multi']))

if __name__ == '__main__':
    main()

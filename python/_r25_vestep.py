#!/usr/bin/env python3
r"""r25-VESTEP: validate the STEP of the article's j1-TrMax induction for VE'.

STEP (route B):  cfbx_reg m N,  TrMax N + 2 < Lng N,  cfbx_reg m (Pred N),
                 cfbx_VE m (Pred N)   ==>   cfbx_VE m N.

The domain  TrMax N + 2 < Lng N  splits on cfbx_j1p:
  (a) cfbx_j1p N < Lng N - 1   (j1' < j1)   -> handled by bpax_VE_step (six_*).
  (b) cfbx_j1p N = Lng N - 1   (j1' = j1) & non-minimal (TrMax+2 < Lng).

Questions:
  Q0  Is the STEP TRUE?  (VE'(N) holds on the whole non-minimal domain)
  Q1  How many (b)-hosts exist?  (the "3 rare hosts" claim)
  Q2  On (b)-hosts, do the six_* facts hold: transJm1 N > 0, m <= transJm1 N (ancJm1),
      m <= parent N 0 (Lng N-1) (anc0), and the interior id2/id3?
      If YES on all (b)-hosts -> six_* machinery adapts, (b) is fully dischargeable.
      If NO -> (b) reduces to the SAME {id2,id3,intM,intN} residual family as the base.
  Q3  Cross-check: on (a)-hosts the six_* domain facts hold (already known).
"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, hasParent,
                       oper, seg, Br, Joints, FirstNodes, TrMax, Red, Adm,
                       fmt)
from trans_model import Trans, Mark, Pred, bpHeadT, bpHeadV, reduced, adm

_TC = {}
_T0 = tm.Trans
def _Tm(M, d=0):
    k = tuple(M)
    if k not in _TC:
        _TC[k] = _T0(M, d)
    return _TC[k]
tm.Trans = _Tm
def T(M): return tm.Trans(list(M))

def pr(*a): print(*a, flush=True)

def descending(br):
    n = len(br)
    for J0 in range(n):
        for J1 in range(J0, n):
            a0, a1 = entry(br[J0], 0, 0), entry(br[J0], 1, 0)
            b0, b1 = entry(br[J1], 0, 0), entry(br[J1], 1, 0)
            if not (a0 >= b0 and (a0 != b0 or a1 >= b1)):
                return False
    return True

def regime(M, m):
    br = Br(M)
    if not br:
        return False
    j1 = Lng(M) - 1
    J1 = len(br) - 1
    j0p = Joints(M)[J1]
    j1p = FirstNodes(M)[J1]
    if m > j1 - 1:
        return False
    if m < j0p:
        return True
    return (m == j0p and entry(M, 0, j1p) == entry(M, 1, j1p)
            and descending(br))

def host(M):
    if Lng(M) < 3 or zeroT(M) or not monoT(M):
        return False
    if not reduced(M):
        return False
    return Br(M) != []

def transJ0(M):  return parent(M, 0, Lng(M) - 1)
def transJm1(M): return Adm(M, transJ0(M))
def transC1(M):  return Mark(list(Pred(M)), transJm1(M))

def cfbx_j1p(M):
    br = Br(M); J1 = len(br) - 1
    return FirstNodes(M)[J1]

def gen_pool(maxlen, maxn, maxseed, cap):
    seen = set(); frontier = []
    for u in range(maxseed):
        for v in range(u, u + maxseed + 2):
            M = tuple(diagSeq(u, v))
            if M not in seen:
                seen.add(M); frontier.append(list(M))
    pool = list(frontier)
    while frontier and len(pool) < cap:
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in range(1, maxn + 1):
                try:
                    N = oper(M, n)
                except (ValueError, IndexError):
                    continue
                if Lng(N) > maxlen: continue
                t = tuple(N)
                if t not in seen:
                    seen.add(t); nxt.append(N); pool.append(N)
                    if len(pool) >= cap: break
            if len(pool) >= cap: break
        frontier = nxt
    return pool

def run(pool, tag, hostcap, deep_only=False, tbudget=180):
    S = {k: [0, 0, []] for k in
         ['STEPdom', 'VE_step', 'b_hosts', 'a_hosts',
          'b_transJm1pos', 'b_ancJm1', 'b_anc0', 'b_id2', 'b_VE',
          'a_ancJm1']}
    def rec(k, ok, info=None):
        S[k][0 if ok else 1] += 1
        if not ok and len(S[k][2]) < 8 and info is not None:
            S[k][2].append(info)
    hosts = [M for M in pool if host(M) and (Lng(M) >= 9 or not deep_only)]
    hosts = hosts[:hostcap]
    t0 = time.time(); nh = 0
    for M in hosts:
        if time.time() - t0 > tbudget:
            break
        nh += 1
        j1 = Lng(M) - 1
        Tr = TrMax(M)
        # non-minimal STEP domain: TrMax + 2 < Lng
        if not (Tr + 2 < Lng(M)):
            continue
        br = Br(M); J1 = len(br) - 1
        j0p = Joints(M)[J1]
        jj1p = cfbx_j1p(M)
        isB = (jj1p == j1)         # j1' = j1  -> sub-case (b)
        isA = (jj1p < j1)          # j1' < j1  -> sub-case (a)
        for m in range(0, min(j0p, j1 - 1) + 1):
            if not regime(M, m):
                continue
            rec('STEPdom', True)
            # STEP validity: does VE'(N) hold given IH VE'(Pred N)?
            try:
                Mp = seg(M, m, j1)
                ve = (bpHeadT(T(Mp)) == bpHeadT(T(M)))
                rec('VE_step', ve, (fmt(M), m, 'VE fail'))
            except (RecursionError, AssertionError, ValueError, IndexError):
                ve = None
            if isB:
                rec('b_hosts', True)
                tjm1 = transJm1(M)
                p0 = transJ0(M)
                rec('b_transJm1pos', tjm1 > 0,
                    (fmt(M), m, f'tjm1={tjm1} TrMax={Tr} p0={p0}'))
                rec('b_ancJm1', m <= tjm1,
                    (fmt(M), m, f'tjm1={tjm1} TrMax={Tr} p0={p0}'))
                rec('b_anc0', m <= p0, (fmt(M), m, f'p0={p0} TrMax={Tr}'))
                try:
                    N = Red(list(seg(M, m, j1)))
                    rec('b_id2', transC1(M) == transC1(N),
                        (fmt(M), m, 'id2 fail'))
                    if ve is not None:
                        rec('b_VE', ve, (fmt(M), m))
                except (RecursionError, AssertionError, ValueError, IndexError):
                    pass
            elif isA:
                rec('a_hosts', True)
                rec('a_ancJm1', m <= transJm1(M), (fmt(M), m))
    pr(f"[{tag}] hosts_scanned={nh}/{len(hosts)} maxLng="
       f"{max((Lng(M) for M in hosts), default=0)} ({round(time.time()-t0,1)}s)")
    for k in ['STEPdom', 'VE_step', 'a_hosts', 'a_ancJm1',
              'b_hosts', 'b_transJm1pos', 'b_ancJm1', 'b_anc0', 'b_id2', 'b_VE']:
        ok, bad, cex = S[k]
        if ok + bad:
            pr(f"   {k:16s} {ok}/{ok+bad}" + ("" if not bad else f"  CEX={cex}"))
    return S

def main():
    random.seed(25)
    t0 = time.time()
    pool = gen_pool(maxlen=7, maxn=3, maxseed=5, cap=1200)
    pr(f"WIDE pool={len(pool)} maxLng={max(Lng(M) for M in pool)} "
       f"build_s={round(time.time()-t0,1)}")
    run(pool, "WIDE", hostcap=350, tbudget=150)
    t0 = time.time()
    dpool = gen_pool(maxlen=11, maxn=2, maxseed=7, cap=2200)
    pr(f"DEEP pool={len(dpool)} maxLng={max(Lng(M) for M in dpool)} "
       f"build_s={round(time.time()-t0,1)}")
    run(dpool, "DEEP", hostcap=220, deep_only=True, tbudget=220)

if __name__ == '__main__':
    main()

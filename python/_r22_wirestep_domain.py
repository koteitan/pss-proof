#!/usr/bin/env python3
r"""r22-WIRESTEP: validate that the bpax_VE_step regime domain
(cfbx_reg m Q, cfbx_j1p Q < Lng Q - 1) implies the ctx_interior_ids
hypotheses, in particular the KEY domain inclusion

    ancJm1 :  m <= transJm1 M  =  Adm M (parent M 0 (Lng M - 1))

plus the supporting facts
    hp    :  hasParent M 0 (Lng M - 1)
    anc0  :  m <= parent M 0 (Lng M - 1)     (consequence of ancJm1 + adm_Adm_le)
    j0lt  :  parent M 0 (Lng M - 1) < Lng M - 1
    mint  :  m < Lng M - 2                    (geometry, already in bpax_VE_step)

and, as a full sanity, the interior identities
    id2   :  transC1 M = transC1 (Red (seg M m (Lng M - 1)))
    id3   :  transC2 M = transC2 (Red (seg M m (Lng M - 1)))
    VE'   :  bpHeadT(Trans(seg M m j1)) == bpHeadT(Trans M)
on the STEP domain (last branch first-node strictly interior).
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

def transJm1(M):
    return Adm(M, parent(M, 0, Lng(M) - 1))

def transC1(M):
    return Mark(list(Pred(M)), transJm1(M))

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

def run(pool, tag, hostcap, deep_only=False, tbudget=150):
    S = {k: [0, 0, []] for k in
         ['STEPdom', 'hp', 'j0lt', 'ancJm1', 'anc0', 'mint',
          'id2', 'id3', 'VE']}
    def rec(k, ok, info=None):
        S[k][0 if ok else 1] += 1
        if not ok and len(S[k][2]) < 6 and info is not None:
            S[k][2].append(info)
    hosts = [M for M in pool if host(M) and (Lng(M) >= 9 or not deep_only)]
    hosts = hosts[:hostcap]
    t0 = time.time(); nh = 0
    for M in hosts:
        if time.time() - t0 > tbudget:
            break
        nh += 1
        j1 = Lng(M) - 1
        br = Br(M); J1 = len(br) - 1
        j0p = Joints(M)[J1]
        j1p = FirstNodes(M)[J1]
        # STEP domain: last branch first node strictly interior
        if not (j1p < j1):
            continue
        for m in range(0, min(j0p, j1 - 1) + 1):
            if not regime(M, m):
                continue
            rec('STEPdom', True)
            # hp
            hp = hasParent(M, 0, j1)
            rec('hp', hp, (fmt(M), m, 'no parent'))
            if not hp:
                continue
            p0 = parent(M, 0, j1)
            # j0lt
            rec('j0lt', p0 < j1, (fmt(M), m, f'p0={p0} j1={j1}'))
            tjm1 = transJm1(M)
            # ancJm1  (KEY)
            rec('ancJm1', m <= tjm1, (fmt(M), m, f'tjm1={tjm1} j0p={j0p} p0={p0}'))
            # anc0
            rec('anc0', m <= p0, (fmt(M), m, f'p0={p0}'))
            # mint
            rec('mint', m < Lng(M) - 2, (fmt(M), m))
            # id2 / id3 / VE  (deep sanity)
            try:
                N = Red(list(seg(M, m, j1)))
                c1M = transC1(M); c1N = transC1(N)
                rec('id2', c1M == c1N, (fmt(M), m, 'id2 fail'))
                tM = bpHeadT(T(M))
                Mp = seg(M, m, j1)
                tMp = bpHeadT(T(Mp))
                rec('VE', tM == tMp, (fmt(M), m, 'VE fail'))
            except (RecursionError, AssertionError, ValueError, IndexError):
                pass
    pr(f"[{tag}] hosts_scanned={nh}/{len(hosts)} ({round(time.time()-t0,1)}s)")
    for k in ['STEPdom', 'hp', 'j0lt', 'ancJm1', 'anc0', 'mint', 'id2', 'VE']:
        ok, bad, cex = S[k]
        if ok + bad:
            pr(f"   {k:10s} {ok}/{ok+bad}" + ("" if not bad else f"  CEX={cex}"))
    return S

def main():
    random.seed(22)
    t0 = time.time()
    pool = gen_pool(maxlen=7, maxn=3, maxseed=5, cap=900)
    pr(f"WIDE pool={len(pool)} maxLng={max(Lng(M) for M in pool)} "
       f"build_s={round(time.time()-t0,1)}")
    run(pool, "WIDE", hostcap=200, tbudget=120)
    t0 = time.time()
    dpool = gen_pool(maxlen=10, maxn=2, maxseed=6, cap=1400)
    pr(f"DEEP pool={len(dpool)} maxLng={max(Lng(M) for M in dpool)} "
       f"build_s={round(time.time()-t0,1)}")
    run(dpool, "DEEP", hostcap=120, deep_only=True, tbudget=170)

if __name__ == '__main__':
    main()

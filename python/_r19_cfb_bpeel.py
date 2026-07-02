#!/usr/bin/env python3
r"""r19-CFB: validate the BACK-PEEL (Pred) induction structure for the
terminal-slice lemma VE'(M,m): bpHeadT(Trans(seg M m j1)) = bpHeadT(Trans M).

The article proves the terminal-slice lemma by an induction on Lng(M) via Pred
(content.md 3660-3945), NOT by the (dead) front-peel telescoping.  This harness
pins the exact back-peel step and checks its soundness deep (Lng>=9).

Facts checked, for regime hosts M (reduced, monoT, Br!=[], m in the hyp regime):
  (L)  Pred(seg M m j1) == seg (Pred M) m (Lng(Pred M)-1)      [pure list]
  (VE) bpHeadT(Trans(seg M m j1)) == bpHeadT(Trans M)          [the target]
  (RP) regime(Pred M, m): does the SAME m stay in the terminal-slice regime
       for Pred M?  (governs whether the induction is clean or needs the
       j1'=j1 / j1'<j1 case split)
  (IH) VE'(Pred M, m): bpHeadT(Trans(seg (Pred M) m ...)) == bpHeadT(Trans(Pred M))
  (STEP) the local back-peel: IH holds  ==>  VE holds  (soundness of induction)
"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper, seg,
                       Br, Joints, FirstNodes, TrMax, Red, fmt)
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
    """the article terminal-slice hypothesis for (M,m); needs Br M != []."""
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
         ['L', 'VE', 'VE_deep', 'RP', 'RP_j1eq', 'RP_j1lt',
          'IH', 'STEP', 'STEP_clean', 'ADM', 'MARKREFR', 'MARKREFR_deep']}
    def rec(k, ok, info=None):
        S[k][0 if ok else 1] += 1
        if not ok and len(S[k][2]) < 4 and info is not None:
            S[k][2].append(info)
    hosts = [M for M in pool if host(M) and (Lng(M) >= 9 or not deep_only)]
    hosts = hosts[:hostcap]
    t0 = time.time()
    nh = 0
    for M in hosts:
        if time.time() - t0 > tbudget:
            break
        nh += 1
        j1 = Lng(M) - 1
        br = Br(M); J1 = len(br) - 1
        j0p = Joints(M)[J1]
        j1p = FirstNodes(M)[J1]
        for m in range(0, min(j0p, j1 - 1) + 1):
            if not regime(M, m):
                continue
            Mp = seg(M, m, j1)
            # (L)
            predMp = Pred(Mp)
            PM = Pred(M)
            segPM = seg(PM, m, Lng(PM) - 1)
            rec('L', list(predMp) == list(segPM), (fmt(M), m))
            # (VE)
            try:
                tM = bpHeadT(T(M)); tMp = bpHeadT(T(Mp))
            except (RecursionError, AssertionError, ValueError, IndexError):
                continue
            ve = (tM == tMp)
            rec('VE', ve, (fmt(M), m, 'VE fail'))
            if Lng(M) >= 9:
                rec('VE_deep', ve)
            # (ADM): is m admissible for M?  (needed for (M,m) in Marked so
            #  Trans(seg M m j1) = Mark M m by m_7_4_Mark_Trans_repr)
            admMm = adm(M, m)
            rec('ADM', admMm, (fmt(M), m, 'not adm'))
            # (MARKREFR): the Mark reframing of VE'.  When (M,m) in Marked,
            #  m_7_4_Mark_Trans_repr gives Trans(seg M m j1) = Mark M m, so VE'
            #  becomes  bpHeadT(Mark M m) = bpHeadT(Trans M).  Check it directly.
            try:
                tmk = bpHeadT(Mark(list(M), m))
            except (RecursionError, AssertionError, ValueError, IndexError):
                tmk = None
            if tmk is not None:
                mr = (tmk == tM)
                rec('MARKREFR', mr, (fmt(M), m, 'markrefr fail'))
                if Lng(M) >= 9:
                    rec('MARKREFR_deep', mr)
            # (RP): does the same m stay in regime for Pred M?
            rp = regime(PM, m)
            rec('RP', rp, None)
            # split by whether j1'==j1 (last col in same branch) at M level
            if j1p == j1:
                rec('RP_j1eq', rp, None)
            else:
                rec('RP_j1lt', rp, None)
            # (IH) + (STEP): only meaningful when Pred M is a valid host & rp
            if host(PM) and rp and m <= Lng(PM) - 2:
                try:
                    tPM = bpHeadT(T(PM)); tpredMp = bpHeadT(T(segPM))
                except (RecursionError, AssertionError, ValueError, IndexError):
                    continue
                ih = (tPM == tpredMp)
                rec('IH', ih, (fmt(M), m))
                # STEP soundness: if IH holds, does VE hold?
                if ih:
                    rec('STEP', ve, (fmt(M), m, 'STEP fail'))
                # STEP_clean: is the M-tail obtained from Pred-tail by the SAME
                # transform on both sides?  i.e. does bpHeadT(Trans M) relate to
                # bpHeadT(Trans(Pred M)) identically for host and slice?
                # We check: (tM == tPM) iff (tMp == tpredMp) -- tails move together
                rec('STEP_clean', (tM == tPM) == (tMp == tpredMp), (fmt(M), m))
    pr(f"[{tag}] hosts_scanned={nh}/{len(hosts)} ({round(time.time()-t0,1)}s)")
    for k in ['L', 'VE', 'VE_deep', 'ADM', 'MARKREFR', 'MARKREFR_deep',
              'RP', 'RP_j1eq', 'RP_j1lt', 'IH', 'STEP', 'STEP_clean']:
        ok, bad, cex = S[k]
        if ok + bad:
            pr(f"   {k:12s} {ok}/{ok+bad}" + ("" if not bad else f"  CEX={cex}"))
    return S

def main():
    random.seed(19)
    t0 = time.time()
    pool = gen_pool(maxlen=7, maxn=3, maxseed=5, cap=900)
    pr(f"WIDE pool={len(pool)} maxLng={max(Lng(M) for M in pool)} "
       f"build_s={round(time.time()-t0,1)}")
    run(pool, "WIDE", hostcap=140, tbudget=110)
    t0 = time.time()
    dpool = gen_pool(maxlen=10, maxn=2, maxseed=6, cap=1200)
    pr(f"DEEP pool={len(dpool)} maxLng={max(Lng(M) for M in dpool)} "
       f"build_s={round(time.time()-t0,1)}")
    run(dpool, "DEEP", hostcap=80, deep_only=True, tbudget=150)

if __name__ == '__main__':
    main()

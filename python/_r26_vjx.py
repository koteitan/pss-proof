#!/usr/bin/env python3
r"""r26-VEJ1EQ: validate the j1'=j1 branch residuals VEj1eq/RPj1eq of the VE'
route-B induction, AND the IH-driven decomposition route.

  VEj1eq goal: cfbx_VE m Q  (bpHeadT(Trans(seg Q m (Lng Q-1)))==bpHeadT(Trans Q))
  under: cfbx_reg m Q, cfbx_j1p Q = Lng Q-1, TrMax Q + 2 < Lng Q,
         cfbx_reg m (Pred Q), cfbx_VE m (Pred Q), 0 < m.

Q = Pred Q @ [c], slice_Q = slice_PredQ @ [c],  c = last column (row1 = v1).
Test the append-sibling forms (both must hold with the SAME v1):
  (G1) bpHeadT(Trans Q)       == bpHeadT(Trans(Pred Q))       +B D[v1] 0
  (G2) bpHeadT(Trans slice_Q) == bpHeadT(Trans(slice PredQ))  +B D[v1] 0
  Then VEj1eq = G2 . IH . G1^-1.
Also test the UNCONDITIONAL host append form
  (Hh) bpHeadT(Trans(X@[c])) == bpHeadT(Trans X) +B D[c row1] 0 whenever X@[c]
       is a reduced monoT host with j1'=j1 (last col single-col last branch).
"""
import sys, os, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper, seg,
                       Br, Joints, FirstNodes, TrMax, Red, Adm, fmt)
from trans_model import Trans, Mark, Pred, bpHeadT, reduced, addBT, Dpt, ZB

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
    if not br: return False
    j1 = Lng(M) - 1
    J1 = len(br) - 1
    j0p = Joints(M)[J1]
    j1p = FirstNodes(M)[J1]
    if m > j1 - 1: return False
    if m < j0p: return True
    return (m == j0p and entry(M, 0, j1p) == entry(M, 1, j1p)
            and descending(br))

def host(M):
    if Lng(M) < 3 or zeroT(M) or not monoT(M): return False
    if not reduced(M): return False
    return Br(M) != []

def cfbx_j1p(M):
    br = Br(M); J1 = len(br) - 1
    return FirstNodes(M)[J1]

def transJ0(M):  return parent(M, 0, Lng(M) - 1)
def transJm1(M): return Adm(M, transJ0(M))

def gen_oper(maxlen, maxn, maxseed, cap):
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
                try: N = oper(M, n)
                except (ValueError, IndexError): continue
                if Lng(N) > maxlen: continue
                t = tuple(N)
                if t not in seen:
                    seen.add(t); nxt.append(N); pool.append(N)
                    if len(pool) >= cap: break
            if len(pool) >= cap: break
        frontier = nxt
    return pool

def gen_brute(maxlen, maxval, cap, percand):
    pool = []
    cols = [(a, b) for a in range(maxval + 1) for b in range(maxval + 1)]
    for L in range(3, maxlen + 1):
        cnt = 0
        for tail in itertools.product(cols, repeat=L - 1):
            cnt += 1
            if cnt > percand: break
            M = [(0, 0)] + list(tail)
            if zeroT(M) or not monoT(M): continue
            if not reduced(M): continue
            if Br(M) == []: continue
            pool.append(M)
            if len(pool) >= cap: return pool
    return pool

def check(pool, tag, tbudget, deep=False):
    S = {k: [0, 0, []] for k in
         ['bhost_rows', 'VEj1eq', 'RPj1eq', 'IH_present', 'G1', 'G2',
          'Hh_all', 'tjm1']}
    def rec(k, ok, info=None):
        S[k][0 if ok else 1] += 1
        if not ok and len(S[k][2]) < 6 and info is not None:
            S[k][2].append(info)
    hosts = [M for M in pool if host(M)]
    if deep:
        hosts = [M for M in hosts if Lng(M) >= 9]
    t0 = time.time()
    for M in hosts:
        if time.time() - t0 > tbudget:
            pr(f"[{tag}] TIME budget"); break
        j1 = Lng(M) - 1
        Tr = TrMax(M)
        if not (Tr + 2 < Lng(M)): continue
        if cfbx_j1p(M) != j1: continue
        br = Br(M); J1 = len(br) - 1
        j0p = Joints(M)[J1]
        PN = list(Pred(M))
        v1 = entry(M, 1, j1)
        # Hh: unconditional host append form
        try:
            hh = (bpHeadT(T(M)) == addBT(bpHeadT(T(PN)), Dpt(v1, ZB)))
            rec('Hh_all', hh, (fmt(M), f'v1={v1}'))
        except Exception:
            pass
        for m in range(1, min(j0p, j1 - 1) + 1):
            if not regime(M, m): continue
            rec('tjm1', True)  # counter only
            rpQ = regime(PN, m)
            rec('RPj1eq', rpQ, (fmt(M), m, 'RP fail'))
            rec('bhost_rows', True)
            try:
                sliceQ = list(seg(M, m, j1))
                slicePN = list(seg(PN, m, Lng(PN) - 1))
                bH_M  = bpHeadT(T(M))
                bH_PN = bpHeadT(T(PN))
                bH_sQ = bpHeadT(T(sliceQ))
                bH_sP = bpHeadT(T(slicePN))
                rec('IH_present', bH_sP == bH_PN, (fmt(M), m, 'IH false'))
                rec('VEj1eq', bH_sQ == bH_M, (fmt(M), m, 'VE fail'))
                rec('G1', bH_M  == addBT(bH_PN, Dpt(v1, ZB)), (fmt(M), m, 'G1 fail'))
                rec('G2', bH_sQ == addBT(bH_sP, Dpt(v1, ZB)), (fmt(M), m, 'G2 fail'))
            except (RecursionError, AssertionError, ValueError, IndexError):
                pass
    dt = round(time.time() - t0, 1)
    maxL = max((Lng(M) for M in hosts), default=0)
    pr(f"[{tag}] hosts={len(hosts)} maxLng={maxL} ({dt}s)")
    for k in ['bhost_rows', 'VEj1eq', 'RPj1eq', 'IH_present', 'G1', 'G2', 'Hh_all']:
        ok, bad, cex = S[k]
        if ok + bad:
            pr(f"   {k:14s} {ok}/{ok+bad}" + ("" if not bad else f"  CEX={cex}"))
    return S

def main():
    t0 = time.time()
    bp = gen_brute(maxlen=5, maxval=3, cap=40000, percand=2000000)
    pr(f"BRUTE5 pool={len(bp)} maxLng={max(Lng(M) for M in bp)} build={round(time.time()-t0,1)}s")
    check(bp, "BRUTE5", tbudget=200)
    t0 = time.time()
    bp2 = gen_brute(maxlen=7, maxval=2, cap=40000, percand=2000000)
    pr(f"BRUTE7 pool={len(bp2)} maxLng={max(Lng(M) for M in bp2)} build={round(time.time()-t0,1)}s")
    check(bp2, "BRUTE7", tbudget=220)
    t0 = time.time()
    dp = gen_oper(maxlen=13, maxn=2, maxseed=8, cap=3500)
    pr(f"DEEP pool={len(dp)} maxLng={max(Lng(M) for M in dp)} build={round(time.time()-t0,1)}s")
    check(dp, "DEEP", tbudget=240, deep=True)

if __name__ == '__main__':
    main()

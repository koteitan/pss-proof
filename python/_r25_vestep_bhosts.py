#!/usr/bin/env python3
r"""r25-VESTEP b-host probe: focus ONLY on the j1'=j1 non-minimal STEP sub-case.

b-host = cfbx_reg m N  &  TrMax N + 2 < Lng N  &  cfbx_j1p N = Lng N - 1.

For each b-host, split m==0 vs m>0 and test:
  RPERS   regime(Pred N, m)                    -- CRITICAL: is Pred N still regime?
  VE      bpHeadT(Trans slice)==bpHeadT(Trans N)
  tjm1pos transJm1 N > 0
  tjm1_gt_m  transJm1 N > m  (strict; needed for intN jm1posN = transJm1(slice)>0)
  m_eq_j0    m == j0'         (the boundary regime sub-case)
  c1net1_M   transC1 N != transT1 N  (proxy that intM holds: s=[] impossible)
  c1net1_slice transC1(Red slice) != transT1(Red slice) (proxy intN)
  seg_is_N   seg N m (Lng-1) == N  (trivial-VE marker, true iff m==0)
Report every b-host verbatim.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper, seg,
                       Br, Joints, FirstNodes, TrMax, Red, Adm, fmt)
from trans_model import Trans, Mark, Pred, bpHeadT, reduced

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

def transJ0(M):  return parent(M, 0, Lng(M) - 1)
def transJm1(M): return Adm(M, transJ0(M))
def transC1(M):  return Mark(list(Pred(M)), transJm1(M))
def transT1(M):  return T(Pred(M))
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

def scan(pool, tag, tbudget):
    hosts = [M for M in pool if host(M)]
    t0 = time.time()
    nb = 0
    fails = {'RPERS':0, 'VE':0, 'tjm1_gt_m_pos':0, 'c1net1_M_pos':0, 'c1net1_slice_pos':0}
    for M in hosts:
        if time.time() - t0 > tbudget:
            pr(f"[{tag}] TIME budget hit"); break
        j1 = Lng(M) - 1
        Tr = TrMax(M)
        if not (Tr + 2 < Lng(M)): continue
        if cfbx_j1p(M) != j1: continue    # want j1'=j1 (b-hosts)
        br = Br(M); J1 = len(br) - 1
        j0p = Joints(M)[J1]
        for m in range(0, min(j0p, j1 - 1) + 1):
            if not regime(M, m): continue
            nb += 1
            # RPERS
            PN = Pred(M)
            rp = regime(list(PN), m)
            # VE
            try:
                ve = (bpHeadT(T(seg(M, m, j1))) == bpHeadT(T(M)))
            except (RecursionError, AssertionError, ValueError, IndexError):
                ve = None
            tjm1 = transJm1(M)
            segN = (list(seg(M, m, j1)) == list(M))
            # interiority proxies (only meaningful for m>0 non-trivial)
            try:
                c1M = (transC1(M) != transT1(M))
            except Exception: c1M = None
            try:
                Nred = Red(list(seg(M, m, j1)))
                c1S = (transC1(Nred) != transT1(Nred))
                tjm1S = transJm1(Nred)   # should be transJm1(M)-m
            except Exception:
                c1S = None; tjm1S = None
            flag = []
            if not rp: flag.append('RP-FAIL'); fails['RPERS'] += 1
            if ve is False: flag.append('VE-FAIL'); fails['VE'] += 1
            if m > 0 and tjm1 <= m: flag.append('tjm1<=m'); fails['tjm1_gt_m_pos'] += 1
            if m > 0 and c1M is False: flag.append('c1=t1(M)'); fails['c1net1_M_pos'] += 1
            if m > 0 and not segN and c1S is False:
                flag.append('c1=t1(slice)'); fails['c1net1_slice_pos'] += 1
            pr(f"  [{tag}] M={fmt(M)} Lng={Lng(M)} TrMax={Tr} m={m} j0'={j0p} "
               f"tjm1={tjm1} tjm1S={tjm1S} RP={rp} VE={ve} segN={segN} "
               f"c1M={c1M} c1S={c1S} {' '.join(flag) if flag else 'OK'}")
    pr(f"[{tag}] b-host rows={nb}  ({round(time.time()-t0,1)}s)  fails={fails}")

def main():
    t0 = time.time()
    pool = gen_pool(maxlen=8, maxn=3, maxseed=6, cap=2500)
    pr(f"WIDE pool={len(pool)} maxLng={max(Lng(M) for M in pool)} build_s={round(time.time()-t0,1)}")
    scan(pool, "WIDE", tbudget=200)
    t0 = time.time()
    dpool = gen_pool(maxlen=12, maxn=2, maxseed=8, cap=3000)
    pr(f"DEEP pool={len(dpool)} maxLng={max(Lng(M) for M in dpool)} build_s={round(time.time()-t0,1)}")
    scan(dpool, "DEEP", tbudget=260)

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
r"""r26 VEj1eq split probe: at j1'=j1 non-minimal regime hosts with 0<m,
partition by (m < transJm1) [deepen, bpx2_BASE] vs (m >= transJm1) [collapse].
Within m>=transJm1, split transJm1==0 (Adm0) vs transJm1>0.
Also test the condI-append form for the Adm0 hosts:
  bpHeadT(Trans Q) == bpHeadT(Trans(Pred Q)) +B D[e1,j1] 0  (host)
  same for the reduced slice N = Red(seg Q m (Lng Q-1)).
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper, seg,
                       Br, Joints, FirstNodes, TrMax, Red, Adm, fmt)
from trans_model import Trans, Mark, Pred, bpHeadT, reduced, addBT, Dpt, ZB

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
    j1 = Lng(M) - 1; J1 = len(br) - 1
    j0p = Joints(M)[J1]; j1p = FirstNodes(M)[J1]
    if m > j1 - 1: return False
    if m < j0p: return True
    return (m == j0p and entry(M, 0, j1p) == entry(M, 1, j1p) and descending(br))

def host(M):
    if Lng(M) < 3 or zeroT(M) or not monoT(M): return False
    if not reduced(M): return False
    return Br(M) != []

def cfbx_j1p(M):
    br = Br(M); return FirstNodes(M)[len(br) - 1]

def transJ0(M):  return parent(M, 0, Lng(M) - 1)
def transJm1(M): return Adm(M, transJ0(M))

def gen_brute(maxlen, maxval):
    pool = []
    cols = [(a, b) for a in range(maxval + 1) for b in range(maxval + 1)]
    for L in range(3, maxlen + 1):
        for tail in itertools.product(cols, repeat=L - 1):
            M = [(0, 0)] + list(tail)
            if zeroT(M) or not monoT(M): continue
            if not reduced(M): continue
            if Br(M) == []: continue
            pool.append(M)
    return pool

def main():
    pool = gen_brute(6, 3) + gen_brute(7, 2)
    c = {'rows': 0, 'deepen(m<tjm1)': 0, 'collapse(m>=tjm1)': 0,
         'coll_adm0': 0, 'coll_tjm1pos': 0,
         'adm0_condI_host_ok': 0, 'adm0_condI_host_bad': 0,
         'adm0_condI_slice_ok': 0, 'adm0_condI_slice_bad': 0}
    exs = []
    for M in pool:
        if not host(M): continue
        j1 = Lng(M) - 1; Tr = TrMax(M)
        if not (Tr + 2 < Lng(M)): continue
        if cfbx_j1p(M) != j1: continue
        br = Br(M); J1 = len(br) - 1
        j0p = Joints(M)[J1]
        for m in range(1, min(j0p, j1 - 1) + 1):
            if not regime(M, m): continue
            c['rows'] += 1
            tj = transJm1(M)
            if m < tj:
                c['deepen(m<tjm1)'] += 1
            else:
                c['collapse(m>=tjm1)'] += 1
                if tj == 0:
                    c['coll_adm0'] += 1
                    # test condI-append form
                    v1 = entry(M, 1, j1)
                    PN = list(Pred(M))
                    hostok = (bpHeadT(Trans(M)) == addBT(bpHeadT(Trans(PN)), Dpt(v1, ZB)))
                    c['adm0_condI_host_ok' if hostok else 'adm0_condI_host_bad'] += 1
                    try:
                        N = Red(list(seg(M, m, j1)))
                        v1N = entry(N, 1, Lng(N) - 1)
                        PNn = list(Pred(N))
                        slok = (bpHeadT(Trans(N)) == addBT(bpHeadT(Trans(PNn)), Dpt(v1N, ZB)))
                        c['adm0_condI_slice_ok' if slok else 'adm0_condI_slice_bad'] += 1
                    except Exception:
                        pass
                else:
                    c['coll_tjm1pos'] += 1
                    if len(exs) < 10:
                        exs.append((fmt(M), m, f'tjm1={tj} j0p={j0p}'))
    print("counts:", c, flush=True)
    print("collapse tjm1>0 examples (the hard residual if any):", exs, flush=True)

if __name__ == '__main__':
    main()

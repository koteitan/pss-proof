#!/usr/bin/env python3
r"""r26 RPj1eq boundary probe: at j1'=j1 non-minimal regime hosts, classify the
regime m-condition of N and which regime clause Pred N satisfies.

Focus: the m=j0' boundary sub-case, and whether Joints(N)[J1-1] > Joints(N)[J1]
(strict -> Pred always satisfies the FIRST clause m<Joints; the shifted-diagonal
boundary transfer is then VACUOUS).
"""
import sys, os, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper, seg,
                       Br, Joints, FirstNodes, TrMax, Red, Adm, fmt)
from trans_model import Pred, reduced

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
    j0p = Joints(M)[J1]; j1p = FirstNodes(M)[J1]
    if m > j1 - 1: return False
    if m < j0p: return True
    return (m == j0p and entry(M, 0, j1p) == entry(M, 1, j1p)
            and descending(br))

def host(M):
    if Lng(M) < 3 or zeroT(M) or not monoT(M): return False
    if not reduced(M): return False
    return Br(M) != []

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
    cnt = {'bhost_m': 0, 'm_lt_j0p': 0, 'm_eq_j0p': 0,
           'JP_strict_gt': 0, 'JP_eq': 0, 'boundary_needs_diag': 0,
           'pred_clause1': 0, 'pred_clause2': 0, 'pred_FAIL': 0}
    exs = []
    for M in pool:
        if not host(M): continue
        j1 = Lng(M) - 1; Tr = TrMax(M)
        if not (Tr + 2 < Lng(M)): continue
        br = Br(M); J1 = len(br) - 1
        if FirstNodes(M)[J1] != j1: continue     # j1'=j1
        j0p = Joints(M)[J1]
        for m in range(1, min(j0p, j1 - 1) + 1):
            if not regime(M, m): continue
            cnt['bhost_m'] += 1
            PN = list(Pred(M))
            brP = Br(PN)
            if not brP:
                cnt['pred_FAIL'] += 1; continue
            JP1 = len(brP) - 1
            joints_P = Joints(PN)[JP1]
            joints_Nm1 = Joints(M)[J1 - 1] if J1 >= 1 else None
            if m < j0p: cnt['m_lt_j0p'] += 1
            else: cnt['m_eq_j0p'] += 1
            # compare Joints(N)[J1-1] vs Joints(N)[J1]
            if J1 >= 1:
                if joints_Nm1 > j0p: cnt['JP_strict_gt'] += 1
                elif joints_Nm1 == j0p: cnt['JP_eq'] += 1
            # which clause does Pred N satisfy?
            if m < joints_P:
                cnt['pred_clause1'] += 1
            elif regime(PN, m):
                cnt['pred_clause2'] += 1
                if m == j0p:
                    cnt['boundary_needs_diag'] += 1
                    if len(exs) < 8: exs.append((fmt(M), m, f'j0p={j0p} JP={joints_P}'))
            else:
                cnt['pred_FAIL'] += 1
                if len(exs) < 8: exs.append(('FAIL', fmt(M), m))
    print("counts:", cnt, flush=True)
    print("boundary_needs_diag examples:", exs, flush=True)

if __name__ == '__main__':
    main()

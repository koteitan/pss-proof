#!/usr/bin/env python3
r"""r22-WIRESTEP: probe the EXACT arithmetic relationship on the STEP domain
between
    j0p   = Joints M ! (Lng(Br M)-1)  = parent M 0 j1'   (last-branch joint)
    j0    = parent M 0 (Lng M-1)                          (row-0 parent of last col)
    tjm1  = Adm M j0  = transJm1 M
    adm_j0 = adm M j0
to find the cleanest lemma path for  m <= tjm1  (given m <= j0p).
Tallies which of  {j0p == tjm1, j0p <= tjm1, j0p == j0, tjm1 == j0, adm M j0}.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, hasParent,
                       oper, seg, Br, Joints, FirstNodes, TrMax, Red, Adm, adm,
                       fmt)
from trans_model import Pred, reduced

def pr(*a): print(*a, flush=True)

def host(M):
    if Lng(M) < 3 or zeroT(M) or not monoT(M): return False
    if not reduced(M): return False
    return Br(M) != []

def transJm1(M): return Adm(M, parent(M, 0, Lng(M) - 1))

def gen_pool(maxlen, maxn, maxseed, cap):
    seen = set(); frontier = []
    for u in range(maxseed):
        for v in range(u, u + maxseed + 2):
            M = tuple(diagSeq(u, v))
            if M not in seen: seen.add(M); frontier.append(list(M))
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

def main():
    tally = {k: [0,0,[]] for k in
             ['j0p_eq_tjm1','j0p_le_tjm1','j0p_eq_j0','tjm1_eq_j0','adm_j0',
              'j0p_le_j0','tjm1_le_j0']}
    def rec(k, ok, info=None):
        tally[k][0 if ok else 1] += 1
        if not ok and len(tally[k][2]) < 8 and info is not None:
            tally[k][2].append(info)
    pool = gen_pool(maxlen=8, maxn=3, maxseed=6, cap=2000)
    hosts = [M for M in pool if host(M)]
    t0 = time.time(); n = 0
    for M in hosts:
        if time.time() - t0 > 90: break
        j1 = Lng(M) - 1
        br = Br(M); J1 = len(br) - 1
        j0p = Joints(M)[J1]; j1p = FirstNodes(M)[J1]
        if not (j1p < j1): continue
        j0 = parent(M, 0, j1); tjm1 = transJm1(M); aj0 = adm(M, j0)
        n += 1
        info = (fmt(M), f'j0p={j0p} j0={j0} tjm1={tjm1} adm_j0={aj0} j1p={j1p} j1={j1}')
        rec('j0p_eq_tjm1', j0p == tjm1, info)
        rec('j0p_le_tjm1', j0p <= tjm1, info)
        rec('j0p_eq_j0', j0p == j0, info)
        rec('tjm1_eq_j0', tjm1 == j0, info)
        rec('adm_j0', aj0, info)
        rec('j0p_le_j0', j0p <= j0, info)
        rec('tjm1_le_j0', tjm1 <= j0, info)
    pr(f"hosts_step={n} ({round(time.time()-t0,1)}s)")
    for k in tally:
        ok, bad, cex = tally[k]
        pr(f"   {k:14s} {ok}/{ok+bad}" + ("" if not bad else f"  CEX(first)={cex[:3]}"))

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""r42 fast targeted hunt for NON-admeq condIV ST_PS hosts + structure + exchange.
Structure focus: relation of e1[transJm1] to v1, and jm2<j0, jm3<jm1."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, monoT, zeroT, hasParent, parent, seg, fmt,
                       reduced, oper, diagSeq)
from trans_model import Adm, adm, Pred, bpHeadT, bpHeadV
from _r15_vx_lib import (Trans, operB, numBT, lessBT, condIV, guarded, SKIP)

def pr(*a): print(*a, flush=True)
def s84x_jm2(M): return parent(M, 1, Lng(M) - 1)
def transJ0(M): return parent(M, 0, Lng(M) - 1)

def gt(f, *a, budget=20): return guarded(f, *a, budget=budget)

def main():
    t0 = time.time()
    # BFS closure, moderate length, MANY diagonal seeds
    seen = set(); frontier = []
    for u in range(9):
        for v in range(u, u + 10):
            M = tuple(diagSeq(u, v))
            if M not in seen: seen.add(M); frontier.append(list(M))
    pool = list(frontier); cap = 20000; maxlen = 16
    while frontier and len(pool) < cap:
        nx = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in (1, 2, 3):
                N = gt(oper, M, n, budget=4)
                if N is SKIP or Lng(N) > maxlen: continue
                t = tuple(N)
                if t not in seen:
                    seen.add(t); nx.append(N); pool.append(N)
                    if len(pool) >= cap: break
            if len(pool) >= cap: break
        frontier = nx
    pr(f'pool {len(pool)}  gen_t={time.time()-t0:.0f}s')

    nonad = []; adm_n = 0; nonseen = set()
    for M in pool:
        L = Lng(M); j1 = L-1
        if not (1 < j1) or not monoT(M) or zeroT(M): continue
        if not hasParent(M, 1, j1) or not reduced(M) or not condIV(M): continue
        jm2 = s84x_jm2(M); j0 = transJ0(M)
        if jm2 is None: continue
        jm3 = Adm(M, jm2); jm1 = Adm(M, j0)
        if jm3 == jm1: adm_n += 1
        else:
            t = tuple(M)
            if t not in nonseen: nonseen.add(t); nonad.append(M)
    pr(f'condIV: admeq {adm_n}  nonadmeq(unique) {len(nonad)}  t={time.time()-t0:.0f}s')

    # structure table
    e1jm1_eq_v1 = 0; e1jm1_lt = 0; e1jm1_gt = 0
    jm2lt_j0 = 0; jm3lt_jm1 = 0
    for M in nonad:
        L = Lng(M); j1 = L-1
        jm2 = s84x_jm2(M); j0 = transJ0(M); jm3 = Adm(M, jm2); jm1 = Adm(M, j0)
        v1 = entry(M,1,j1); e1jm1 = entry(M,1,jm1)
        if e1jm1 == v1: e1jm1_eq_v1 += 1
        elif e1jm1 < v1: e1jm1_lt += 1
        else: e1jm1_gt += 1
        if jm2 < j0: jm2lt_j0 += 1
        if jm3 < jm1: jm3lt_jm1 += 1
    pr(f'nonadmeq structure:  jm2<j0 {jm2lt_j0}/{len(nonad)}   jm3<jm1 {jm3lt_jm1}/{len(nonad)}')
    pr(f'  e1[transJm1] vs v1:  ==v1 {e1jm1_eq_v1}   <v1 {e1jm1_lt}   >v1 {e1jm1_gt}')
    pr('--- sample (up to 12) ---')
    for M in sorted(nonad, key=lambda x: Lng(x))[:12]:
        L = Lng(M); j1 = L-1
        jm2 = s84x_jm2(M); j0 = transJ0(M); jm3 = Adm(M, jm2); jm1 = Adm(M, j0)
        pr(f'  {fmt(M)} | v1={entry(M,1,j1)} jm2={jm2} j0={j0} jm3={jm3} jm1={jm1} '
           f'e1jm1={entry(M,1,jm1)} e1jm2={entry(M,1,jm2)} e1j0={entry(M,1,j0)}')

    # exchange triple
    C = [[0,0],[0,0],[0,0]]; cex = [None,None,None]; sk = 0
    for M in nonad:
        TM = gt(Trans, M, budget=25)
        if TM is SKIP: sk += 1; continue
        for n in (1,2,3):
            Mn = gt(oper, M, n, 12); Mn1 = gt(oper, M, n+1, 12)
            if Mn is SKIP or Mn1 is SKIP: sk += 1; continue
            TMn = gt(Trans, Mn, 25); TMn1 = gt(Trans, Mn1, 25)
            if TMn is SKIP or TMn1 is SKIP: sk += 1; continue
            oN = gt(operB, TM, numBT(n), 12); oNm1 = gt(operB, TM, numBT(n-1), 12)
            if oN is SKIP or oNm1 is SKIP: sk += 1; continue
            cc = [lessBT(TMn,oN), lessBT(TMn,TM), lessBT(oNm1,TMn1)]
            for i in range(3):
                C[i][0]+=cc[i]; C[i][1]+=1
                if not cc[i] and cex[i] is None: cex[i]=(fmt(M),n)
    pr(f'CONJ1 {C[0][0]}/{C[0][1]}  CONJ2 {C[1][0]}/{C[1][1]}  CONJ3 {C[2][0]}/{C[2][1]}  skip {sk}')
    pr(f'CEX {cex}')
    pr(f'total {time.time()-t0:.0f}s')

if __name__ == '__main__':
    main()

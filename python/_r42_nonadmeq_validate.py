#!/usr/bin/env python3
"""r42 deep-validation: the condIV exchange triple on the NON-admeq branch.

Generate condIV ST_PS hosts by oper/Pred closure from diagSeq seeds (incl u>0),
BFS intermediate length >= 14, SPLIT by admeq (Adm M jm2 == transJm1) vs not.
Report: #non-admeq condIV hosts + exchange pass-fraction (3 conjuncts).
If a conjunct is FALSE on some non-admeq host -> report minimal CEX and stop.
"""
import sys, os, time, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, monoT, zeroT, multiT, seg, diagSeq,
                       parent, hasParent, oper, fmt, P)
import red_model as rm
from _r15_vx_lib import (Trans, Mark, operB, numBT, lessBT, leBT, condIV,
                         guarded, SKIP, TO)
from trans_model import Adm, adm, Pred, reduced, bpHeadT

def pr(*a): print(*a, flush=True)

def s84x_jm2(M): return parent(M, 1, Lng(M) - 1)
def transJ0(M): return parent(M, 0, Lng(M) - 1)
def s84x_jm3(M): return Adm(M, s84x_jm2(M))
def transJm1(M): return Adm(M, transJ0(M))

# ---- BFS ST_PS pool with intermediate length >= 14 ----
def gen_pool(maxlen=18, maxn=4, seeds_u=4, seeds_v=5, cap=8000, oper_budget=6):
    seen = set(); frontier = []
    for u in range(seeds_u + 1):
        for v in range(u, u + seeds_v + 1):
            M = tuple(diagSeq(u, v))
            if M not in seen:
                seen.add(M); frontier.append(list(M))
    pool = list(frontier)
    while frontier and len(pool) < cap:
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in range(1, maxn + 1):
                N = guarded(oper, M, n, budget=oper_budget)
                if N is SKIP: continue
                if Lng(N) > maxlen: continue
                t = tuple(N)
                if t not in seen:
                    seen.add(t); nxt.append(N); pool.append(N)
                    if len(pool) >= cap: break
            if len(pool) >= cap: break
        frontier = nxt
    return pool

def gterm(f, *a, budget=25):
    return guarded(f, *a, budget=budget)

def main():
    t0 = time.time()
    pool = gen_pool()
    pr(f'pool {len(pool)}  gen_t={time.time()-t0:.0f}s')
    lens = {}
    for M in pool:
        lens[Lng(M)] = lens.get(Lng(M), 0) + 1
    pr('len-histogram', dict(sorted(lens.items())))

    # collect condIV hosts satisfying the target's structural hyps
    admeq_hosts = []; nonadmeq_hosts = []
    for M in pool:
        L = Lng(M); j1 = L - 1
        if j1 <= 2: continue                 # need 1 < Lng M - 1  (j1 = Lng-1 > 2? no: 1<j1)
        if not (1 < j1): continue
        if not monoT(M) or zeroT(M): continue
        if not hasParent(M, 1, j1): continue
        if not reduced(M): continue
        if not condIV(M): continue
        jm2 = s84x_jm2(M); jm3 = s84x_jm3(M); jm1 = transJm1(M)
        if jm2 is None: continue
        if jm3 == jm1: admeq_hosts.append(M)
        else: nonadmeq_hosts.append(M)
    pr(f'condIV hosts: admeq={len(admeq_hosts)}  nonadmeq={len(nonadmeq_hosts)}'
       f'  t={time.time()-t0:.0f}s')

    # dedup nonadmeq by tuple
    seen = set(); nd = []
    for M in nonadmeq_hosts:
        t = tuple(M)
        if t not in seen: seen.add(t); nd.append(M)
    nonadmeq_hosts = nd
    pr(f'nonadmeq unique: {len(nonadmeq_hosts)}')

    # characterize the nonadmeq structure: jm3 vs jm1 direction, and depths
    dir_gt = dir_lt = 0
    lenhist = {}
    for M in nonadmeq_hosts:
        jm3 = s84x_jm3(M); jm1 = transJm1(M)
        if jm3 > jm1: dir_gt += 1
        else: dir_lt += 1
        lenhist[Lng(M)] = lenhist.get(Lng(M), 0) + 1
    pr(f'nonadmeq direction: jm3>jm1 = {dir_gt}   jm3<jm1 = {dir_lt}')
    pr('nonadmeq len-hist', dict(sorted(lenhist.items())))

    # sample some nonadmeq hosts with full structural readout
    pr('--- sample nonadmeq hosts ---')
    for M in sorted(nonadmeq_hosts, key=lambda x: (Lng(x),))[:8]:
        jm2 = s84x_jm2(M); jm3 = s84x_jm3(M); jm1 = transJm1(M); j0 = transJ0(M)
        pr(f'  M={fmt(M)}  L={Lng(M)}  jm2={jm2} j0={j0}  jm3={jm3} jm1={jm1}'
           f'  admJm2={adm(M,jm2)} admJ0={adm(M,j0)}')

    # exchange triple on nonadmeq hosts, n = 1,2,3
    C1 = [0,0]; C2 = [0,0]; C3 = [0,0]     # [ok, tot]
    cexs = {1: None, 2: None, 3: None}
    skipped = 0
    checked = 0
    for M in nonadmeq_hosts:
        TM = gterm(Trans, M, budget=25)
        if TM is SKIP: skipped += 1; continue
        host_ok = True
        for n in (1, 2, 3):
            Mn  = gterm(oper, M, n, budget=15)
            Mn1 = gterm(oper, M, n+1, budget=15)
            if Mn is SKIP or Mn1 is SKIP: skipped += 1; continue
            TMn  = gterm(Trans, Mn, budget=25)
            TMn1 = gterm(Trans, Mn1, budget=25)
            if TMn is SKIP or TMn1 is SKIP: skipped += 1; continue
            opN   = gterm(operB, TM, numBT(n), budget=15)
            opNm1 = gterm(operB, TM, numBT(n-1), budget=15)
            if opN is SKIP or opNm1 is SKIP: skipped += 1; continue
            # conjunct 1: lessBT (Trans (M[n])) (operB (Trans M) (numBT n))
            c1 = lessBT(TMn, opN)
            # conjunct 2: lessBT (Trans (M[n])) (Trans M)
            c2 = lessBT(TMn, TM)
            # conjunct 3: lessBT (operB (Trans M) (numBT (n-1))) (Trans (M[n+1]))
            c3 = lessBT(opNm1, TMn1)
            C1[0]+=c1; C1[1]+=1; C2[0]+=c2; C2[1]+=1; C3[0]+=c3; C3[1]+=1
            if not c1 and cexs[1] is None: cexs[1] = (fmt(M), n)
            if not c2 and cexs[2] is None: cexs[2] = (fmt(M), n)
            if not c3 and cexs[3] is None: cexs[3] = (fmt(M), n)
        checked += 1
    pr(f'checked nonadmeq hosts (Trans computed): {checked}  skipped(timeout)={skipped}')
    pr(f'CONJ1 lessBT(Trans M[n], operB(Trans M, numBT n)) : {C1[0]}/{C1[1]}')
    pr(f'CONJ2 lessBT(Trans M[n], Trans M)                 : {C2[0]}/{C2[1]}')
    pr(f'CONJ3 lessBT(operB(Trans M, numBT(n-1)), Trans M[n+1]): {C3[0]}/{C3[1]}')
    pr(f'CEX conj1 {cexs[1]}  conj2 {cexs[2]}  conj3 {cexs[3]}')
    pr(f'total {time.time()-t0:.0f}s')

if __name__ == '__main__':
    main()

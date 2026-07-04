#!/usr/bin/env python3
"""Validate the condIV d3 GOAL on the TRUNK branch (the bypass target) and the
regime branch, plus diagnostic reducedness. Host-capped; cheap prefilters first."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r28_c4dx_producer as V
from red_model import (Lng, entry, monoT, zeroT, hasParent, parent, seg, Br,
                       fmt, reduced, TrMax)
from trans_model import Dpt, bpHeadT

def pr(*a): print(*a, flush=True)

def main():
    t0 = time.time()
    goal_tr = [0, 0]; goal_rg = [0, 0]
    rr_tr = [0, 0]; rr_rg = [0, 0]; trunk = [0, 0]
    cex_goal_tr = []; cex_goal_rg = []; cex_rr_rg = []
    hosts = 0; HOSTCAP = 220
    pool = []
    for seed, mlen, cap, ns, um, vx in (
            (11, 10, 1500, (1, 2, 3), 3, 7),
            (23, 11, 1500, (1, 2), 4, 8),
            (37, 11, 1500, (1, 2, 3), 5, 8),
            (5, 12, 1500, (1, 2), 3, 9)):
        pool += V.gen_oper(mlen, cap, seed, ns, um, vx)
    pr(f'pool {len(pool)} gen_t={time.time()-t0:.0f}s')
    for M in pool:
        if hosts >= HOSTCAP: break
        L = Lng(M); j1 = L - 1
        if j1 <= 2 or not monoT(M) or zeroT(M) or not hasParent(M, 1, j1):
            continue
        if not V.condIV(M):
            continue
        jm2 = V.s84x_jm2(M); jm3 = V.s84x_jm3(M)
        if not (jm2 + 1 < L - 1):
            continue
        if not reduced(M):
            continue
        hosts += 1
        c = L - 2
        X = seg(M, jm3, c)          # Pred(s84x_N M)
        rr = reduced(X)
        t = (len(Br(X)) == 0)       # trunk branch
        trunk[0] += t; trunk[1] += 1
        # d3 GOAL: Trans(Pred(s84x_Np M)) = Dpt(entry M 1 jm2)(transT2 M)
        PNp = seg(M, jm2, c)        # Pred(s84x_Np M)
        try:
            lhs = V.Trans(PNp)
            rhs = Dpt(entry(M, 1, jm2), V.transT2(M))
            goal = (lhs == rhs)
        except Exception:
            continue
        if t:
            goal_tr[0] += goal; goal_tr[1] += 1
            rr_tr[0] += rr; rr_tr[1] += 1
            if not goal and len(cex_goal_tr) < 4:
                cex_goal_tr.append((fmt(M), 'jm3', jm3, 'jm2', jm2, 'c', c))
        else:
            goal_rg[0] += goal; goal_rg[1] += 1
            rr_rg[0] += rr; rr_rg[1] += 1
            if not goal and len(cex_goal_rg) < 4:
                cex_goal_rg.append((fmt(M), 'jm3', jm3, 'jm2', jm2, 'c', c))
            if not rr and len(cex_rr_rg) < 4:
                cex_rr_rg.append((fmt(M), 'jm3', jm3, 'c', c, 'TrMax', TrMax(M)))
    pr(f'condIV_rng_hosts {hosts}  (cap {HOSTCAP})  t={time.time()-t0:.0f}s')
    pr(f'TRUNK(Br(raw)=[])   {trunk}')
    pr(f'GOAL_trunk          {goal_tr}   <- MUST be all-pass (bypass target)')
    pr(f'GOAL_regime         {goal_rg}   (sanity)')
    pr(f'RAWRED_trunk        {rr_tr}')
    pr(f'RAWRED_regime       {rr_rg}     <- residual regSP-raw satisfiability')
    pr(f'cex_GOAL_trunk      {cex_goal_tr}')
    pr(f'cex_GOAL_regime     {cex_goal_rg}')
    pr(f'cex_RAWRED_regime   {cex_rr_rg}')
    pr(f'total {time.time()-t0:.0f}s')

if __name__ == '__main__':
    main()

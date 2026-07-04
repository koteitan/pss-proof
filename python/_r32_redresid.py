#!/usr/bin/env python3
"""Validate the Red-slice d3 residual for condIV: on Br(Red(raw))!=[] branch,
is cfbx_reg (jm2-jm3) (Red(raw slice)) TRUE (= condIII's shared REGSP)?
Also confirm Br(raw)=[] <=> Br(Red(raw))=[]. Host-capped."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r28_c4dx_producer as V
from red_model import (Lng, entry, monoT, zeroT, hasParent, seg, Br, Joints,
                       FirstNodes, TrMax, fmt, reduced)

def pr(*a): print(*a, flush=True)

def descending(br):
    n = len(br)
    for a in range(n):
        for b in range(a, n):
            a0, a1 = entry(br[a], 0, 0), entry(br[a], 1, 0)
            b0, b1 = entry(br[b], 0, 0), entry(br[b], 1, 0)
            if not (a0 >= b0 and (a0 != b0 or a1 >= b1)):
                return False
    return True

def cfbx_reg(m, N):
    # faithful to cfbx_reg_def: N reduced & PT (mono, not zeroT) & Br!=[] & offset cond
    if not reduced(N): return False
    if zeroT(N) or not monoT(N): return False
    br = Br(N)
    if len(br) == 0: return False
    J1 = len(br) - 1
    jn = Joints(N); fn = FirstNodes(N)
    jJ = jn[J1]
    if m < jJ: return True
    if m == jJ:
        f = fn[J1]
        return (entry(N, 0, f) == entry(N, 1, f)) and descending(br)
    return False

def main():
    t0 = time.time()
    coincide = [0, 0]            # Br(raw)=[] <=> Br(Red raw)=[]
    regsat_red = [0, 0]         # on Br(Red)!=[]: cfbx_reg(jm2-jm3)(Red raw) TRUE?
    trunk_red = [0, 0]          # fraction with Br(Red raw)=[]
    cex = []
    hosts = 0; HOSTCAP = 1200
    pool = []
    for seed, mlen, cap, ns, um, vx in (
            (11, 11, 2000, (1, 2, 3), 3, 7),
            (23, 12, 2000, (1, 2), 4, 8),
            (37, 12, 2000, (1, 2, 3), 5, 8),
            (5, 13, 2000, (1, 2), 3, 9),
            (7, 13, 2500, (1, 2, 3), 4, 9),
            (13, 14, 2500, (1, 2), 3, 10),
            (17, 14, 2500, (1, 2, 3), 5, 10)):
        pool += V.gen_oper(mlen, cap, seed, ns, um, vx)
    pr(f'pool {len(pool)} gen_t={time.time()-t0:.0f}s')
    for M in pool:
        if hosts >= HOSTCAP: break
        L = Lng(M); j1 = L - 1
        if j1 <= 2 or not monoT(M) or zeroT(M) or not hasParent(M, 1, j1): continue
        if not V.condIV(M): continue
        jm2 = V.s84x_jm2(M); jm3 = V.s84x_jm3(M)
        if not (jm2 + 1 < L - 1): continue
        if not reduced(M): continue
        hosts += 1
        c = L - 2
        X = seg(M, jm3, c)          # Pred(s84x_N M) raw
        RX = V.Red(X)               # Red(Pred(s84x_N M))
        braw_empty = (len(Br(X)) == 0)
        bred_empty = (len(Br(RX)) == 0)
        coincide[0] += (braw_empty == bred_empty); coincide[1] += 1
        trunk_red[0] += bred_empty; trunk_red[1] += 1
        if not bred_empty:
            ok = cfbx_reg(jm2 - jm3, RX)
            regsat_red[0] += ok; regsat_red[1] += 1
            if not ok and len(cex) < 5:
                cex.append((fmt(M), 'jm3', jm3, 'jm2', jm2, 'c', c,
                            'JoinRed', Joints(RX)[len(Br(RX)) - 1] if Br(RX) else None,
                            'off', jm2 - jm3))
    pr(f'condIV_rng_hosts {hosts}  t={time.time()-t0:.0f}s')
    pr(f'COINCIDE Br(raw)=[]<=>Br(Red)=[]  {coincide}   (must be all-pass)')
    pr(f'TRUNK_red Br(Red raw)=[]          {trunk_red}')
    pr(f'REGSAT_red cfbx_reg(Red raw) on Br(Red)!=[]  {regsat_red}  <- residual (=condIII REGSP)')
    pr(f'cex_REGSAT_red {cex}')
    pr(f'total {time.time()-t0:.0f}s')

if __name__ == '__main__':
    main()

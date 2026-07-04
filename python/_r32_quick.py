#!/usr/bin/env python3
"""Fast brute enumeration of reduced condIV hosts; measure raw-slice reducedness."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r28_c4dx_producer as V
from red_model import (Lng, entry, monoT, zeroT, hasParent, parent, seg, Br, fmt,
                       TrMax, reduced)

def pr(*a): print(*a, flush=True)

def enum(maxlen, cap):
    """BFS build reduced sequences col by col starting (0,0)."""
    out = []; frontier = [[(0, 0)]]; seen = {((0, 0),)}
    while frontier and len(out) < cap:
        nf = []
        for M in frontier:
            out.append(M)
            if Lng(M) >= maxlen: continue
            pm0 = max(p[0] for p in M)
            for a in range(0, pm0 + 2):
                for b in range(0, a + 1):
                    N = M + [(a, b)]
                    t = tuple(N)
                    if t in seen: continue
                    if reduced(N):
                        seen.add(t); nf.append(N)
        frontier = nf
    return out

def main():
    t0 = time.time()
    raw_all = [0, 0]; diag = [0, 0]; trunk = [0, 0]
    rr_trunk = [0, 0]; rr_reg = [0, 0]
    cex_reg = []; cex_trunk_nonred = []
    hosts = 0
    pool = enum(9, 60000)
    pr(f'enumerated {len(pool)} reduced seqs ({time.time()-t0:.0f}s)')
    for M in pool:
        L = Lng(M); j1 = L - 1
        if j1 <= 2 or not monoT(M) or zeroT(M) or not hasParent(M, 1, j1): continue
        if not V.condIV(M): continue
        jm2 = V.s84x_jm2(M); jm3 = V.s84x_jm3(M)
        if not (jm2 + 1 < L - 1): continue
        hosts += 1
        c = L - 2; X = seg(M, jm3, c); rr = reduced(X)
        raw_all[0] += rr; raw_all[1] += 1
        diag[0] += (entry(M, 0, jm3) == entry(M, 1, jm3)); diag[1] += 1
        t = (len(Br(X)) == 0); trunk[0] += t; trunk[1] += 1
        if t:
            rr_trunk[0] += rr; rr_trunk[1] += 1
            if not rr and len(cex_trunk_nonred) < 4:
                cex_trunk_nonred.append((fmt(M), 'jm3=', jm3, 'c=', c))
        else:
            rr_reg[0] += rr; rr_reg[1] += 1
            if not rr and len(cex_reg) < 4:
                cex_reg.append((fmt(M), 'jm3=', jm3, 'c=', c, 'TrMax=', TrMax(M)))
    pr(f'condIV hosts (rng): {hosts}')
    pr(f'RAWRED_ALL   {raw_all}')
    pr(f'DIAG_jm3     {diag}')
    pr(f'TRUNK(Br=[]) {trunk}')
    pr(f'RAWRED_trunk {rr_trunk}   <- key: reducedness on trunk branch')
    pr(f'RAWRED_reg   {rr_reg}     <- key: reducedness on regime branch')
    pr('cex_reg (non-reduced raw on Br!=[]):')
    for x in cex_reg: pr('  ', x)
    pr('cex_trunk_nonred (non-reduced raw on Br=[]):')
    for x in cex_trunk_nonred: pr('  ', x)
    pr(f'total {time.time()-t0:.0f}s')

if __name__ == '__main__':
    main()

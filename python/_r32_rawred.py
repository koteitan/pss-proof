#!/usr/bin/env python3
r"""r32: FAST diagnostic for the condIV regSP-raw reducedness crux.

Over reduced condIV hosts (cheap; no Trans, no yaBMS), measure:
  RAWRED_ALL : seg M jm3 (Lng M-2) in RT_PS   (raw Pred(s84x_N) slice reduced?)
  DIAG_jm3   : entry M 0 jm3 == entry M 1 jm3  (is jm3 a diagonal node?)
  TRUNK      : Br(seg M jm3 (Lng M-2)) == []   (the branch to bypass)
  RAWRED_trunk : RAWRED on the TRUNK branch    <-- the key one for the bypass
  RAWRED_reg   : RAWRED on the regime branch
  NRED_std     : same but restricted to is_standard (sampled)
Only hosts with rng: jm2+1 < Lng M -1.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r28_c4dx_producer as V
from red_model import (Lng, entry, monoT, zeroT, hasParent, parent, seg,
                       Br, fmt, is_standard)

def pr(*a): print(*a, flush=True)

class St:
    def __init__(s): s.ok=0; s.bad=0; s.cex=[]
    def rec(s,g,i):
        if g: s.ok+=1
        else:
            s.bad+=1
            if len(s.cex)<8: s.cex.append(i)
    def __str__(s): return f"{s.ok}/{s.ok+s.bad}"

def main():
    t0=time.time()
    R={k:St() for k in ('RAWRED_ALL','DIAG_jm3','TRUNK','RAWRED_trunk','RAWRED_reg','NRED_std','RAWRED_std')}
    hosts=0; std=0
    pools=[]
    for seed,mlen,cap,ns,um,vx in (
            (11,14,40000,(1,2,3),3,9),
            (23,15,40000,(1,2),4,10),
            (37,16,40000,(1,2,3),5,10)):
        pools.append(V.gen_oper(mlen,cap,seed,ns,um,vx))
    for seed,mlen,cap in ((41,13,40000),(43,14,40000),(47,15,40000)):
        pools.append(V.gen_straddle(mlen,cap,seed))
    for pool in pools:
        t1=time.time()
        for M in pool:
            if time.time()-t1>120: break
            L=Lng(M); j1=L-1
            if j1<=2 or not monoT(M) or zeroT(M) or not hasParent(M,1,j1): continue
            if not V.reduced(M) or not V.condIV(M): continue
            jm2=V.s84x_jm2(M); jm3=V.s84x_jm3(M)
            if not (jm2+1 < L-1): continue
            hosts+=1
            c=L-2
            X=seg(M,jm3,c)
            rr=V.reduced(X)
            R['RAWRED_ALL'].rec(rr,(fmt(M),jm3,c))
            R['DIAG_jm3'].rec(entry(M,0,jm3)==entry(M,1,jm3),(fmt(M),jm3))
            trunk=(len(Br(X))==0)
            R['TRUNK'].rec(trunk,(fmt(M),))
            if trunk: R['RAWRED_trunk'].rec(rr,(fmt(M),jm3,c))
            else: R['RAWRED_reg'].rec(rr,(fmt(M),jm3,c))
            # standard sample: only check is_standard for a subset (every host, cheap enough at this count)
            if hosts % 1 == 0:
                try:
                    if is_standard(M):
                        std+=1
                        R['NRED_std'].rec(True,None)
                        R['RAWRED_std'].rec(rr,(fmt(M),jm3,c))
                except Exception:
                    pass
        pr(f'[pool {len(pool)}] hosts_so_far={hosts} std={std} ({time.time()-t1:.0f}s)')
    pr(f'hosts={hosts} std={std}')
    for k in R:
        pr(f'{k:13s} {str(R[k]):>10s}   CEX {R[k].cex[:4]}')
    pr(f'total {time.time()-t0:.0f}s')

if __name__=='__main__':
    main()

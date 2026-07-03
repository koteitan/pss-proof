#!/usr/bin/env python3
# quick sync probe: genuine hosts from small oper pool; check
#   run cap, W2nostr, and cfbx_reg 1 (Red(seg M s c)) for run columns s.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, Adm, adm,
                       oper, diagSeq, le0, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax)
from trans_model import Trans, bpHeadT

def pr(*a): print(*a, flush=True)

def Ts(M):
    try: return Trans(M)
    except Exception: return None

def transJ0(M): return parent(M, 0, Lng(M)-1)

def condV(M):
    n = Lng(M)
    if n < 2 or not hasParent(M, 0, n-1): return False
    j0 = transJ0(M)
    return (entry(M,1,n-1) > 0 and entry(M,1,j0)+1 == entry(M,1,n-1)
            and j0+1 < n-1)

def genuine(M):
    return (Lng(M) >= 4 and monoT(M) and reduced(M) and condV(M)
            and not adm(M, transJ0(M)))

def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0, len(bs)):
            a0, b0 = bs[J0][0]; a1, b1 = bs[J1][0]
            if not (a0 >= a1 and (a0 != a1 or b0 >= b1)): return False
    return True

def cfbx_reg1(S):
    if not reduced(S): return (False, 'notRT')
    if not monoT(S): return (False, 'notPT')
    b = Br(S)
    if not b: return (False, 'BrEmpty')
    jl = Joints(S)[len(b)-1]
    if jl is None: return (False, 'jointNone')
    if 1 < jl: return (True, 'lt')
    if 1 == jl:
        fn = FirstNodes(S)[len(b)-1]
        if entry(S,0,fn) == entry(S,1,fn) and descending(b): return (True, 'eq-diag-desc')
        return (False, 'eq-nodiag/nodesc')
    return (False, f'joint{jl}')

def gen_oper(maxlen, maxn, maxseed, cap, budget):
    t0=time.time(); seen=set(); frontier=[]
    for u in range(maxseed):
        for v in range(u, u+maxseed+2):
            M=tuple(diagSeq(u,v))
            if Lng(M)<=maxlen and M not in seen: seen.add(M); frontier.append(list(M))
    pool=list(frontier)
    while frontier and len(pool)<cap and time.time()-t0<budget:
        nxt=[]
        for M in frontier:
            if Lng(M)<=1: continue
            for n in range(1, maxn+1):
                N=oper(M,n)
                if Lng(N)>maxlen: continue
                t=tuple(N)
                if t not in seen: seen.add(t); nxt.append(N); pool.append(N)
            if len(pool)>=cap or time.time()-t0>budget: break
        frontier=nxt
    return pool

t0=time.time()
pool = gen_oper(maxlen=9, maxn=3, maxseed=3, cap=900, budget=40)
pr(f"pool={len(pool)} t={time.time()-t0:.0f}s")
gh=[M for M in pool if genuine(M)]
pr(f"genuine={len(gh)} t={time.time()-t0:.0f}s")
runs={}; ok=bad=0; regok=regbad=0; regwhy={}
for M in gh:
    n=Lng(M); j0=transJ0(M); jm1=Adm(M,j0); run=j0-jm1
    runs[run]=runs.get(run,0)+1
    for c in range(j0+1, n):
        Q=Ts(seg(M,j0,c)); N=Ts(seg(M,jm1,c))
        if Q is None or N is None: continue
        hold=(bpHeadT(Q)==bpHeadT(N))
        if hold: ok+=1
        else:
            bad+=1; pr(f"  W2CEX {fmt(M)} j0={j0} jm1={jm1} c={c}")
        # per-run-column reduced-slice regime guard
        for s in range(jm1, j0):
            if not le0(M,s,c):
                regwhy['NOreach']=regwhy.get('NOreach',0)+1; continue
            R=Red(seg(M,s,c))
            v,why=cfbx_reg1(R)
            key=('T:' if hold else 'F:')+why
            regwhy[key]=regwhy.get(key,0)+1
            if v: regok+=1
            else:
                regbad+=1
                if regbad<=6:
                    pr(f"  REGFAIL {fmt(M)} s={s} c={c} why={why} R={fmt(R)} hold={hold}")
pr(f"runs={runs}")
pr(f"W2nostr ok={ok} bad={bad}")
pr(f"redslice-reg ok={regok} bad={regbad} why={regwhy}")
pr(f"t={time.time()-t0:.0f}s")

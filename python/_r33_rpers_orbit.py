#!/usr/bin/env python3
# r33: RPERS-guarded via oper-orbit (standard => reduced monoT), no brute Red.
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax, diagSeq, oper, fmt)
def is_reduced(M): return Red(list(M))==list(M)
def cfbx_j1p(M): return FirstNodes(M)[len(Br(M))-1]
def reg2(M): return len(Br(M))>0 and monoT(M) and is_reduced(M)
def guard(M):
    j1p=cfbx_j1p(M); return entry(M,0,j1p)>entry(M,1,j1p)
def reg3(M): return reg2(M) and guard(M)
def Pred(M): return M[:-1] if Lng(M)>1 else M
def gen(maxlen,vcap,budget):
    t0=time.time(); seen=set(); frontier=[]
    for v in range(1,maxlen):
        d=diagSeq(0,v)
        if Lng(d)<=maxlen: frontier.append(tuple(map(tuple,d)))
    seen.update(frontier); hosts=list(frontier)
    while frontier:
        if time.time()-t0>budget: break
        nf=[]
        for M in frontier:
            Ml=[list(p) for p in M]
            for n in (1,2,3,4):
                O=oper(Ml,n)
                if Lng(O)<1 or Lng(O)>maxlen: continue
                if any(a>vcap or b>vcap for (a,b) in O): continue
                t=tuple(map(tuple,O))
                if t not in seen: seen.add(t); nf.append(t); hosts.append(t)
        frontier=nf
    return [[list(p) for p in M] for M in hosts]
hosts=gen(13,9,120)
rp_ok=rp_bad=0; jp_ok=jp_bad=0; nstep=0; cex=[]
for M in hosts:
    if not reg3(M): continue
    if cfbx_j1p(M) >= Lng(M)-1: continue
    nstep+=1
    P=Pred(M)
    if reg3(P): rp_ok+=1
    else:
        rp_bad+=1
        if len(cex)<10: cex.append((fmt(M),'reg2P' if reg2(P) else 'notreg2','g' if (len(Br(P))>0 and guard(P)) else 'ng'))
    if len(Br(P))>0 and cfbx_j1p(P)==cfbx_j1p(M): jp_ok+=1
    else: jp_bad+=1
print(f"oper-orbit hosts={len(hosts)} STEP(reg3&cfbx_j1p<Lng-1)={nstep}")
print(f"[RPERS-guarded] reg3(Pred N): ok={rp_ok} bad={rp_bad}")
print(f"[cfbx_j1p stable]: ok={jp_ok} bad={jp_bad}")
for x in cex: print("  CEX",x)

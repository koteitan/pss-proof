#!/usr/bin/env python3
# r38 quick: key structural questions on a modest but genuine corpus.
import sys, itertools, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from functools import lru_cache
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax, seg, fmt, oper,
                       reduced, parent, leR)
import trans_model as tm
from trans_model import bpHeadT

@lru_cache(maxsize=None)
def _Trans(t): return tm.Trans(list(t))
def Trans(M): return _Trans(tuple(M))
@lru_cache(maxsize=None)
def _red(t): return reduced(list(t))
@lru_cache(maxsize=None)
def _mono(t): return monoT(list(t))
def LastStep(M):
    b=Br(M)
    if not b: return 0
    J1=len(b)-1
    h0=entry(b[J1],0,0); h1=entry(b[J1],1,0)
    if h0==h1: return J1
    return min(J for J in range(len(b)) if entry(b[J1],0,0)==entry(b[J],0,0) and entry(b[J],1,0)<entry(b[J],0,0))
def cfbx_j1p(M): return FirstNodes(M)[len(Br(M))-1]
def reg2(M): return _red(tuple(M)) and _mono(tuple(M)) and len(Br(M))>0
def descending(bs): return all(entry(bs[i],0,0)>=entry(bs[i+1],0,0) for i in range(len(bs)-1))
def guard(M):
    j1p=cfbx_j1p(M); return entry(M,0,j1p) > entry(M,1,j1p)
def reg4(M):
    if not reg2(M) or not guard(M): return False
    J1=len(Br(M))-1; j0p=Joints(M)[J1]
    return 0<j0p<TrMax(M)
def reg7(M): return reg4(M) and descending(Br(M))
def Pred(M): return M[:-1] if Lng(M)>1 else M
def is_prefix(A,B): return len(A)<=len(B) and B[:len(A)]==A
def ve34(M):
    n=Lng(M); b=Br(M); J1=len(b)-1
    j0p=Joints(M)[J1]; J0=LastStep(M); m1=FirstNodes(M)[J0]-1
    Mp=seg(M,j0p,n-1); N=seg(M,0,m1)
    A=bpHeadT(Trans(N)); B=bpHeadT(Trans(Mp)); C=bpHeadT(Trans(M)); v=entry(M,1,j0p)
    ve3 = is_prefix(A[1],B[1]) and len(A[1])<len(B[1])
    ve4 = (C[1]==A[1]+[('D',v,B)])
    return ve3 and ve4

t0=time.time()
# modest corpus: brute L<=4 (GRID 4x4) + one deep-ish layer
GRID=[(x,y) for x in range(4) for y in range(4)]
seeds=set()
for L in range(3,5):
    for tup in itertools.product(GRID,repeat=L-1):
        M=[(0,0)]+list(tup)
        if reg2(M): seeds.add(tuple(M))
seen=set(seeds); frontier=list(seeds); cap=2500
while frontier and len(seen)<cap:
    nxt=[]
    for M in frontier:
        for nn in range(2,5):
            try:
                inter=oper(list(M),nn)
                if Lng(inter)>50: continue
                R=Red(inter)
            except Exception: continue
            if 2<=Lng(R)<=14 and reg2(R):
                t=tuple(R)
                if t not in seen: seen.add(t); nxt.append(t)
            if len(seen)>=cap: break
        if len(seen)>=cap: break
    frontier=nxt
corpus=seen
print(f"corpus={len(corpus)} ({round(time.time()-t0,1)}s)", flush=True)
reg7_all=[list(M) for M in corpus if reg7(list(M))]
print(f"reg7={len(reg7_all)} maxLng={max((Lng(M) for M in reg7_all),default=0)}", flush=True)

step_hosts=[M for M in reg7_all if cfbx_j1p(M)<Lng(M)-1 and reg7(Pred(M)) and len(Br(Pred(M)))>0]
print(f"STEP hosts={len(step_hosts)} (Lng>=8: {sum(1 for M in step_hosts if Lng(M)>=8)})", flush=True)

g_ok=g_bad=0; s_ok=s_bad=0; case4=case3=other=0
resid_ok=resid_bad=0; ve3ok=ve3bad=0; sig_eq=sig_ne=0; scex=[]
for M in step_hosts:
    P=Pred(M); n=Lng(M); J1=len(Br(M))-1; j0p=Joints(M)[J1]
    bN=seg(M,0,FirstNodes(M)[LastStep(M)]-1); bP=seg(P,0,FirstNodes(P)[LastStep(P)]-1)
    aN=seg(M,j0p,n-1); J1p=len(Br(P))-1; j0pP=Joints(P)[J1p]; aP=seg(P,j0pP,Lng(P)-1)
    geom=(bN==bP) and (j0p==j0pP) and (aN==aP+[M[n-1]]) and (entry(M,1,j0p)==entry(P,1,j0pP))
    if geom: g_ok+=1
    else: g_bad+=1
    vp=ve34(P); vn=ve34(M)
    if vp and vn: s_ok+=1
    elif vp and not vn:
        s_bad+=1
        if len(scex)<6: scex.append(fmt(M))
    if not (geom and vp and vn): continue
    v=entry(M,1,j0p)
    A=bpHeadT(Trans(bN)); hN=bpHeadT(Trans(aN)); hP=bpHeadT(Trans(aP))
    gN=bpHeadT(Trans(M)); gP=bpHeadT(Trans(P))
    lastP=gP[1][-1] if gP[1] else None; lastN=gN[1][-1] if gN[1] else None
    j1pi=cfbx_j1p(M)
    if lastP and lastN:
        if lastP[1]==v and lastN[1]==v: case4+=1
        elif lastP[1]==entry(M,1,j1pi) and lastN[1]==entry(M,1,j1pi): case3+=1
        else: other+=1
    tau3=lastN[2] if (lastN and lastN[1]==v) else None
    if tau3 is not None:
        if hN==tau3: resid_ok+=1
        else: resid_bad+=1
    if is_prefix(A[1],hN[1]):
        t2=hN[1][len(A[1]):]
        if len(t2)>0: ve3ok+=1
        else: ve3bad+=1
    else: ve3bad+=1
    # slice-keystone sigma1: prefix of hP before its last D_v block == A ?
    lastTP=hP[1][-1] if hP[1] else None
    if lastTP and lastTP[1]==v:
        sig1=('T',hP[1][:-1])
        if sig1==A: sig_eq+=1
        else: sig_ne+=1
print(f"[geom] ok={g_ok} bad={g_bad}", flush=True)
print(f"[STEP impl] ok={s_ok} FAIL={s_bad}", flush=True)
for c in scex: print("   STEP-CEX",c)
print(f"[keystone case N] case4={case4} case3={case3} other={other}", flush=True)
print(f"[residual hN==tau3|case4] ok={resid_ok} bad={resid_bad}", flush=True)
print(f"[VE3_N: hN=A+t2,t2!=0] ok={ve3ok} bad={ve3bad}", flush=True)
print(f"[slice sig1==A] eq={sig_eq} ne={sig_ne}", flush=True)
print(f"done ({round(time.time()-t0,1)}s)", flush=True)

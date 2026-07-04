#!/usr/bin/env python3
# r38 confirmation: STEP structure on a bounded but deep-ish corpus (chains, Lng<=12).
import sys, itertools, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from functools import lru_cache
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax, seg, fmt, oper,
                       reduced, parent, leR)
import trans_model as tm
from trans_model import bpHeadT
@lru_cache(maxsize=None)
def _T(t): return tm.Trans(list(t))
def Trans(M): return _T(tuple(M))
@lru_cache(maxsize=None)
def _r(t): return reduced(list(t))
@lru_cache(maxsize=None)
def _m(t): return monoT(list(t))
def LastStep(M):
    b=Br(M)
    if not b: return 0
    J1=len(b)-1; h0=entry(b[J1],0,0); h1=entry(b[J1],1,0)
    if h0==h1: return J1
    return min(J for J in range(len(b)) if entry(b[J1],0,0)==entry(b[J],0,0) and entry(b[J],1,0)<entry(b[J],0,0))
def cfbx_j1p(M): return FirstNodes(M)[len(Br(M))-1]
def reg2(M): return _r(tuple(M)) and _m(tuple(M)) and len(Br(M))>0
def descending(bs): return all(entry(bs[i],0,0)>=entry(bs[i+1],0,0) for i in range(len(bs)-1))
def reg4(M):
    if not reg2(M): return False
    j1p=cfbx_j1p(M)
    if not entry(M,0,j1p)>entry(M,1,j1p): return False
    J1=len(Br(M))-1; j0p=Joints(M)[J1]
    return 0<j0p<TrMax(M)
def reg7(M): return reg4(M) and descending(Br(M))
def Pred(M): return M[:-1] if Lng(M)>1 else M
def isp(A,B): return len(A)<=len(B) and B[:len(A)]==A
def ve34(M):
    n=Lng(M); b=Br(M); J1=len(b)-1
    j0p=Joints(M)[J1]; J0=LastStep(M); m1=FirstNodes(M)[J0]-1
    Mp=seg(M,j0p,n-1); N=seg(M,0,m1)
    A=bpHeadT(Trans(N)); B=bpHeadT(Trans(Mp)); C=bpHeadT(Trans(M)); v=entry(M,1,j0p)
    return isp(A[1],B[1]) and len(A[1])<len(B[1]) and (C[1]==A[1]+[('D',v,B)])

t0=time.time()
GRID=[(x,y) for x in range(3) for y in range(3)]
seeds=set()
for L in range(3,6):
    for tup in itertools.product(GRID,repeat=L-1):
        M=[(0,0)]+list(tup)
        if reg2(M): seeds.add(tuple(M))
print(f"seeds={len(seeds)} ({round(time.time()-t0,1)}s)",flush=True)
# deep chains: iterate oper(M,n) then Red, keep Lng<=12; track depth
seen=set(seeds); dep={s:0 for s in seeds}; frontier=list(seeds); layers=0
while frontier and len(seen)<8000 and layers<25:
    layers+=1; nxt=[]
    for M in frontier:
        for n in (2,3):
            try:
                inter=oper(list(M),n)
                if Lng(inter)>26: continue
                R=Red(inter)
            except Exception: continue
            if 2<=Lng(R)<=12 and reg2(R):
                t=tuple(R)
                if t not in seen:
                    seen.add(t); dep[t]=dep[M]+1; nxt.append(t)
            if len(seen)>=8000: break
        if len(seen)>=8000: break
    frontier=nxt
corpus=list(seen)
mdep=max(dep.values())
print(f"corpus={len(corpus)} layers={layers} max-deriv-depth={mdep} ({round(time.time()-t0,1)}s)",flush=True)
reg7_all=[list(M) for M in corpus if reg7(list(M))]
mdep7=max((dep[tuple(M)] for M in reg7_all),default=0)
print(f"reg7={len(reg7_all)} max-deriv-depth(reg7)={mdep7} maxLng={max((Lng(M) for M in reg7_all),default=0)}",flush=True)
step=[M for M in reg7_all if cfbx_j1p(M)<Lng(M)-1 and reg7(Pred(M)) and len(Br(Pred(M)))>0]
sdep=max((dep[tuple(M)] for M in step),default=0)
print(f"STEP hosts={len(step)} max-deriv-depth(step)={sdep} deep(depth>=8):{sum(1 for M in step if dep[tuple(M)]>=8)}",flush=True)
g=gb=s=sb=c4=c3=oth=rok=rbad=v3ok=v3bad=0; scex=[]; rcex=[]
for M in step:
    P=Pred(M); n=Lng(M); J1=len(Br(M))-1; j0p=Joints(M)[J1]
    bN=seg(M,0,FirstNodes(M)[LastStep(M)]-1); bP=seg(P,0,FirstNodes(P)[LastStep(P)]-1)
    aN=seg(M,j0p,n-1); J1p=len(Br(P))-1; j0pP=Joints(P)[J1p]; aP=seg(P,j0pP,Lng(P)-1)
    geom=(bN==bP) and (j0p==j0pP) and (aN==aP+[M[n-1]]) and (entry(M,1,j0p)==entry(P,1,j0pP))
    if geom: g+=1
    else: gb+=1
    vp=ve34(P); vn=ve34(M)
    if vp and vn: s+=1
    elif vp and not vn:
        sb+=1
        if len(scex)<6: scex.append((fmt(M),dep[tuple(M)]))
    if not(geom and vp and vn): continue
    v=entry(M,1,j0p)
    A=bpHeadT(Trans(bN)); hN=bpHeadT(Trans(aN))
    gN=bpHeadT(Trans(M)); gP=bpHeadT(Trans(P))
    lp=gP[1][-1] if gP[1] else None; ln=gN[1][-1] if gN[1] else None
    j1i=cfbx_j1p(M)
    if lp and ln:
        if lp[1]==v and ln[1]==v: c4+=1
        elif lp[1]==entry(M,1,j1i) and ln[1]==entry(M,1,j1i): c3+=1
        else: oth+=1
    tau3=ln[2] if (ln and ln[1]==v) else None
    if tau3 is not None:
        if hN==tau3: rok+=1
        else:
            rbad+=1
            if len(rcex)<4: rcex.append(fmt(M))
    if isp(A[1],hN[1]) and len(hN[1])>len(A[1]): v3ok+=1
    else: v3bad+=1
print(f"[geom lockstep] ok={g} bad={gb}",flush=True)
print(f"[STEP impl vp&vn] ok={s} FAIL(vp&!vn)={sb}",flush=True)
for c in scex: print("   STEP-CEX",c)
print(f"[keystone case N] case4(D_j0')={c4} case3(D_j1')={c3} other={oth}",flush=True)
print(f"[VE4 core hN==tau3|case4] ok={rok} bad={rbad}",flush=True)
for c in rcex: print("   RESID-CEX",c)
print(f"[VE3_N hN strictly-extends A] ok={v3ok} bad={v3bad}",flush=True)
print(f"done ({round(time.time()-t0,1)}s)",flush=True)

import sys, itertools, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from functools import lru_cache
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax, seg, fmt, oper, reduced)
import trans_model as tm
from trans_model import bpHeadT
@lru_cache(maxsize=None)
def _T(t): return tm.Trans(list(t))
def Trans(M): return _T(tuple(M))
def LastStep(M):
    b=Br(M)
    if not b: return 0
    J1=len(b)-1; h0=entry(b[J1],0,0); h1=entry(b[J1],1,0)
    if h0==h1: return J1
    return min(J for J in range(len(b)) if entry(b[J1],0,0)==entry(b[J],0,0) and entry(b[J],1,0)<entry(b[J],0,0))
def cj(M): return FirstNodes(M)[len(Br(M))-1]
def reg2(M): return reduced(M) and monoT(M) and len(Br(M))>0
def desc(bs): return all(entry(bs[i],0,0)>=entry(bs[i+1],0,0) for i in range(len(bs)-1))
def reg4(M):
    if not reg2(M): return False
    j=cj(M)
    if not entry(M,0,j)>entry(M,1,j): return False
    J1=len(Br(M))-1; j0=Joints(M)[J1]
    return 0<j0<TrMax(M)
def reg7(M): return reg4(M) and desc(Br(M))
def Pred(M): return M[:-1] if Lng(M)>1 else M
def isp(A,B): return len(A)<=len(B) and B[:len(A)]==A
def ve34(M):
    n=Lng(M); b=Br(M); J1=len(b)-1
    j0=Joints(M)[J1]; J0=LastStep(M); m1=FirstNodes(M)[J0]-1
    Mp=seg(M,j0,n-1); N=seg(M,0,m1)
    A=bpHeadT(Trans(N)); B=bpHeadT(Trans(Mp)); C=bpHeadT(Trans(M)); v=entry(M,1,j0)
    return isp(A[1],B[1]) and len(A[1])<len(B[1]) and (C[1]==A[1]+[('D',v,B)])
t0=time.time()
# brute GRID 4x4 L in 4..6 but only collect reg7 STEP hosts directly (early-exit filters first)
GRID=[(x,y) for x in range(4) for y in range(4)]
step=[]
for L in (5,6):
    for tup in itertools.product(GRID,repeat=L-1):
        M=[(0,0)]+list(tup)
        # cheap early filters before expensive reduced()
        if not (M[1]==(1,1) or M[1]==(0,0)): pass
        if not monoT(M): continue
        if not reduced(M): continue
        if len(Br(M))==0: continue
        if not reg7(M): continue
        if not (cj(M)<Lng(M)-1): continue
        P=Pred(M)
        if Lng(P)<2 or not reg2(P) or not reg7(P) or len(Br(P))==0: continue
        step.append(M)
    print(f"  after L={L}: step-hosts so far={len(step)} ({round(time.time()-t0,1)}s)",flush=True)
    if time.time()-t0>200:
        print("  time cap hit",flush=True); break
print(f"STEP-hosts={len(step)} maxLng={max((Lng(M) for M in step),default=0)}",flush=True)
g=gb=s=sb=c4=c3=oth=rok=rbad=v3ok=v3bad=0; scex=[]
for M in step:
    P=Pred(M); n=Lng(M); J1=len(Br(M))-1; j0=Joints(M)[J1]
    bN=seg(M,0,FirstNodes(M)[LastStep(M)]-1); bP=seg(P,0,FirstNodes(P)[LastStep(P)]-1)
    aN=seg(M,j0,n-1); J1p=len(Br(P))-1; j0P=Joints(P)[J1p]; aP=seg(P,j0P,Lng(P)-1)
    geom=(bN==bP) and (j0==j0P) and (aN==aP+[M[n-1]]) and (entry(M,1,j0)==entry(P,1,j0P))
    if geom: g+=1
    else: gb+=1
    vp=ve34(P); vn=ve34(M)
    if vp and vn: s+=1
    elif vp and not vn:
        sb+=1
        if len(scex)<6: scex.append(fmt(M))
    if not(geom and vp and vn): continue
    v=entry(M,1,j0); A=bpHeadT(Trans(bN)); hN=bpHeadT(Trans(aN))
    gN=bpHeadT(Trans(M)); gP=bpHeadT(Trans(P))
    lp=gP[1][-1] if gP[1] else None; ln=gN[1][-1] if gN[1] else None
    j1i=cj(M)
    if lp and ln:
        if lp[1]==v and ln[1]==v: c4+=1
        elif lp[1]==entry(M,1,j1i) and ln[1]==entry(M,1,j1i): c3+=1
        else: oth+=1
    tau3=ln[2] if (ln and ln[1]==v) else None
    if tau3 is not None:
        if hN==tau3: rok+=1
        else: rbad+=1
    if isp(A[1],hN[1]) and len(hN[1])>len(A[1]): v3ok+=1
    else: v3bad+=1
print(f"[geom lockstep] ok={g} bad={gb}",flush=True)
print(f"[STEP impl vp&vn] ok={s} FAIL(vp&!vn)={sb}",flush=True)
for c in scex: print("  STEP-CEX",c)
print(f"[keystone case for N] case4(D_j0')={c4} case3(D_j1')={c3} other={oth}",flush=True)
print(f"[VE4 core hN==tau3] ok={rok} bad={rbad}",flush=True)
print(f"[VE3_N hN extends A] ok={v3ok} bad={v3bad}",flush=True)
print(f"done ({round(time.time()-t0,1)}s)",flush=True)

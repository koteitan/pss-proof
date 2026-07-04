#!/usr/bin/env python3
# r33 VE34: confirm the corrected regime vg3x_reg3 = vg2x_reg2 & guard and that
# (i) guard <=> VE34 (reconfirm, deeper), (ii) in STEP (cfbx_j1p < Lng-1),
# vg3x_reg3(Pred N) holds (RPERS-guarded true), and cfbx_j1p(Pred N)=cfbx_j1p N.
import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax, seg, fmt)
import trans_model as tm
from trans_model import Trans, bpHeadT

def is_reduced(M): return Red(list(M))==list(M)
def LastStep(M):
    b=Br(M)
    if not b: return 0
    J1=len(b)-1
    h0=entry(b[J1],0,0); h1=entry(b[J1],1,0)
    if h0==h1: return J1
    return min(J for J in range(len(b)) if entry(b[J1],0,0)==entry(b[J],0,0) and entry(b[J],1,0)<entry(b[J],0,0))
def cfbx_j1p(M): return FirstNodes(M)[len(Br(M))-1]
def reg2(M): return is_reduced(M) and monoT(M) and len(Br(M))>0
def guard(M):
    j1p=cfbx_j1p(M); return entry(M,0,j1p) > entry(M,1,j1p)
def reg3(M): return reg2(M) and guard(M)
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

GRID=[(x,y) for x in range(4) for y in range(4)]
gTrue_ok=gTrue_bad=gFalse_ok=gFalse_bad=0
rpers_ok=rpers_bad=0; j1p_ok=j1p_bad=0
cexp=[]
for L in range(3,6):
    for tup in itertools.product(GRID,repeat=L-1):
        M=[(0,0)]+list(tup)
        if not reg2(M): continue
        b=Br(M); J1=len(b)-1; j0p=Joints(M)[J1]
        if not (0<j0p<TrMax(M)): continue
        try: ok=ve34(M)
        except Exception: continue
        if guard(M):
            if ok: gTrue_ok+=1
            else: gTrue_bad+=1
        else:
            if ok: gFalse_ok+=1
            else: gFalse_bad+=1
        # STEP persistence: cfbx_j1p < Lng-1
        if cfbx_j1p(M) < Lng(M)-1 and reg3(M):
            P=Pred(M)
            if Lng(P)>=1 and len(Br(P))>0:
                if reg3(P): rpers_ok+=1
                else:
                    rpers_bad+=1
                    if len(cexp)<8: cexp.append(('reg3P',fmt(M)))
                if cfbx_j1p(P)==cfbx_j1p(M): j1p_ok+=1
                else: j1p_bad+=1
            else:
                rpers_bad+=1
print(f"[guard <=> VE34]  guard=True: ok={gTrue_ok} bad={gTrue_bad} | guard=False: ok={gFalse_ok} bad={gFalse_bad}")
print(f"[RPERS-guarded]   reg3(N)&STEP => reg3(Pred N): ok={rpers_ok} bad={rpers_bad}")
print(f"[cfbx_j1p stable] cfbx_j1p(Pred N)=cfbx_j1p N in STEP: ok={j1p_ok} bad={j1p_bad}")
for x in cexp: print("  CEX",x)

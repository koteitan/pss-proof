#!/usr/bin/env python3
# brute-only VE34 STEP validation, L up to 6 (GRID range 4), no deep gen.
import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax, seg, fmt, reduced)
import trans_model as tm
from trans_model import Trans, bpHeadT

def LastStep(M):
    b=Br(M)
    if not b: return 0
    J1=len(b)-1
    h0=entry(b[J1],0,0); h1=entry(b[J1],1,0)
    if h0==h1: return J1
    return min(J for J in range(len(b)) if entry(b[J1],0,0)==entry(b[J],0,0) and entry(b[J],1,0)<entry(b[J],0,0))
def cfbx_j1p(M): return FirstNodes(M)[len(Br(M))-1]
def reg2(M): return reduced(M) and monoT(M) and len(Br(M))>0
def guard(M):
    j1p=cfbx_j1p(M); return entry(M,0,j1p) > entry(M,1,j1p)
def reg3(M): return reg2(M) and guard(M)
def reg4(M):
    if not reg3(M): return False
    J1=len(Br(M))-1; j0p=Joints(M)[J1]
    return 0<j0p<TrMax(M)
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
whole_ok=whole_bad=0; wcex=[]
step_ok=step_bad=0; scex=[]
geom_ok=geom_bad=0; gcex=[]
hshift_ok=hshift_bad=0
hext_ok=hext_bad=0
nreg4=0
for L in range(5,7):
    for tup in itertools.product(GRID,repeat=L-1):
        M=[(0,0)]+list(tup)
        if not reg4(M): continue
        nreg4+=1
        try: wn=ve34(M)
        except Exception: continue
        if wn: whole_ok+=1
        else:
            whole_bad+=1
            if len(wcex)<6: wcex.append(fmt(M))
        if cfbx_j1p(M) < Lng(M)-1:
            P=Pred(M)
            if Lng(P)<1 or len(Br(P))==0: continue
            if not reg4(P): continue
            # geom: bpHeadT(Trans NfxP)==bpHeadT(Trans NfxN)
            NfxN=seg(M,0,FirstNodes(M)[LastStep(M)]-1)
            NfxP=seg(P,0,FirstNodes(P)[LastStep(P)]-1)
            gN=bpHeadT(Trans(NfxN)); gP=bpHeadT(Trans(NfxP))
            if gP==gN: geom_ok+=1
            else:
                geom_bad+=1
                if len(gcex)<6: gcex.append((fmt(M),NfxN,NfxP))
            # hext: bpHeadT(Trans MpN) = bpHeadT(Trans MpP) +B e  (prefix)
            J1=len(Br(M))-1; j0p=Joints(M)[J1]
            J1p=len(Br(P))-1; j0pP=Joints(P)[J1p]
            MpN=bpHeadT(Trans(seg(M,j0p,Lng(M)-1)))
            MpP=bpHeadT(Trans(seg(P,j0pP,Lng(P)-1)))
            if is_prefix(MpP[1],MpN[1]): hext_ok+=1
            else:
                hext_bad+=1
            # hshift: bpHeadT(Trans N) = bpHeadT(Trans NfxN) +B D_v(bpHeadT(Trans MpN))
            v=entry(M,1,j0p); C=bpHeadT(Trans(M))
            if C[1]==gN[1]+[('D',v,('T',MpN[1]))]:
                hshift_ok+=1
            else:
                hshift_bad+=1
            # STEP: ve34(P) & ve34(N)
            try: vp=ve34(P); vnn=ve34(M)
            except Exception: continue
            if vp and vnn: step_ok+=1
            elif vp and not vnn:
                step_bad+=1
                if len(scex)<6: scex.append(fmt(M))
print(f"reg4 hosts={nreg4}")
print(f"[whole ve34/reg4]  ok={whole_ok} bad={whole_bad}")
for c in wcex: print("  WHOLE-CEX",c)
print(f"[geom NfxP==NfxN]  ok={geom_ok} bad={geom_bad}")
for c in gcex: print("  GEOM-CEX",c)
print(f"[hext prefix]      ok={hext_ok} bad={hext_bad}")
print(f"[hshift VE4-N]     ok={hshift_ok} bad={hshift_bad}")
print(f"[STEP vp&vn]       ok={step_ok}  STEP-FAIL={step_bad}")
for c in scex: print("  STEP-CEX",c)

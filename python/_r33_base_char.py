#!/usr/bin/env python3
# r33: characterize the GUARDED BASE residual (cfbx_j1p==Lng-1 & guard).
# Split by adm(j0'); report VE34 holds and the growth term t2 (VE3 suffix)
# vs article case1 (adm j0' => t2 = D_{M1,j1'} 0) / case2 (nadm j0').
import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax, seg, adm, fmt)
from trans_model import Trans, bpHeadT
def is_reduced(M): return Red(list(M))==list(M)
def LastStep(M):
    b=Br(M)
    if not b: return 0
    J1=len(b)-1
    if entry(b[J1],0,0)==entry(b[J1],1,0): return J1
    return min(J for J in range(len(b)) if entry(b[J1],0,0)==entry(b[J],0,0) and entry(b[J],1,0)<entry(b[J],0,0))
def is_prefix(A,B): return len(A)<=len(B) and B[:len(A)]==A
GRID=[(x,y) for x in range(4) for y in range(4)]
adm_ok=adm_bad=nadm_ok=nadm_bad=0
t2_case1=t2_other=0; ex=[]
for L in range(3,6):
    for tup in itertools.product(GRID,repeat=L-1):
        M=[(0,0)]+list(tup)
        if not (monoT(M) and is_reduced(M)): continue
        b=Br(M)
        if not b: continue
        n=Lng(M); J1=len(b)-1; j0p=Joints(M)[J1]
        if not (0<j0p<TrMax(M)): continue
        j1p=FirstNodes(M)[J1]
        if j1p != n-1: continue          # BASE
        if not (entry(M,0,j1p)>entry(M,1,j1p)): continue  # GUARD
        J0=LastStep(M); m1=FirstNodes(M)[J0]-1
        Mp=seg(M,j0p,n-1); N=seg(M,0,m1)
        A=bpHeadT(Trans(N)); B=bpHeadT(Trans(Mp)); C=bpHeadT(Trans(M)); v=entry(M,1,j0p)
        ve3 = is_prefix(A[1],B[1]) and len(A[1])<len(B[1])
        ve4 = (C[1]==A[1]+[('D',v,B)])
        ok = ve3 and ve4
        aj0 = adm(M,j0p)
        if aj0:
            if ok: adm_ok+=1
            else: adm_bad+=1
        else:
            if ok: nadm_ok+=1
            else: nadm_bad+=1
        # t2 = suffix of B beyond A
        if ve3:
            t2list=B[1][len(A[1]):]
            # case1 predicted: t2 = [('D', entry M 1 j1p, 0_B)]
            pred=[('D',entry(M,1,j1p),('T',[]))]
            if aj0 and t2list==pred: t2_case1+=1
            elif aj0:
                t2_other+=1
                if len(ex)<6: ex.append((fmt(M),'adm t2',t2list,'pred',pred))
print(f"[BASE guarded, adm j0']  VE34 ok={adm_ok} bad={adm_bad}")
print(f"[BASE guarded, nadm j0'] VE34 ok={nadm_ok} bad={nadm_bad}")
print(f"[adm case: t2 == D_(M1,j1') 0 ?] match={t2_case1} other={t2_other}")
for x in ex: print("  ",x)

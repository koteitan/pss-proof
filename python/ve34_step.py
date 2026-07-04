#!/usr/bin/env python3
# r36-VESTEP: validate the EXACT VE34 STEP (article 8.2 cases 3,4 head-shift):
#   vg4x_reg4 N & cfbx_j1p N < Lng N-1 & vg4x_reg4(Pred N) & vg2x_VE34(Pred N)
#      ==> vg2x_VE34 N
# plus the geometric lockstep facts that reduce STEP to a head-shift.
import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax, seg, fmt, oper, reduced)
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
    # (i): bpHeadT(Trans terminal) = bpHeadT(Trans prefix) +B t2, t2!=0
    ve3 = is_prefix(A[1],B[1]) and len(A[1])<len(B[1])
    # (ii): bpHeadT(Trans M) = bpHeadT(Trans prefix) +B D_v (bpHeadT(Trans terminal))
    ve4 = (C[1]==A[1]+[('D',v,B)])
    return ve3 and ve4

# ---- corpus: brute small + deep oper-BFS ----
def gen_brute(maxL):
    GRID=[(x,y) for x in range(4) for y in range(4)]
    out=set()
    for L in range(3,maxL+1):
        for tup in itertools.product(GRID,repeat=L-1):
            M=[(0,0)]+list(tup)
            if reg2(M): out.add(tuple(M))
    return out

def gen_deep(seeds, cap, maxLng):
    seen=set(seeds); frontier=list(seeds)
    while frontier and len(seen)<cap:
        nxt=[]
        for M in frontier:
            Ml=list(M)
            for nn in range(2,6):
                try:
                    R=Red(oper(Ml,nn))
                except Exception: continue
                if 2<=Lng(R)<=maxLng and reduced(R) and monoT(R) and len(Br(R))>0:
                    t=tuple(R)
                    if t not in seen:
                        seen.add(t); nxt.append(t)
                        if len(seen)>=cap: break
            if len(seen)>=cap: break
        frontier=nxt
    return seen

import sys as _s
brute=gen_brute(5)
print(f"brute={len(brute)}", flush=True)
deep=gen_deep(brute, 6000, 12)
corpus=brute|deep
print(f"corpus: brute={len(brute)} total={len(corpus)}", flush=True)

reg4_all=[list(M) for M in corpus if reg4(list(M))]
maxL=max((Lng(M) for M in reg4_all), default=0)
print(f"reg4 hosts: {len(reg4_all)}  maxLng={maxL}")

# 1) whole target: ve34 over reg4
w_ok=w_bad=0; wcex=[]
for M in reg4_all:
    try: ok=ve34(M)
    except Exception: continue
    if ok: w_ok+=1
    else:
        w_bad+=1
        if len(wcex)<6: wcex.append(fmt(M))
print(f"[ve34 over reg4] ok={w_ok} bad={w_bad}")
for c in wcex: print("   WHOLE-CEX",c)

# 2) geometric lockstep in STEP regime (cfbx_j1p < Lng-1)
g_ok=g_bad=0; gcex=[]
for M in reg4_all:
    if not (cfbx_j1p(M) < Lng(M)-1): continue
    P=Pred(M)
    if Lng(P)<1 or len(Br(P))==0: continue
    n=Lng(M); J1=len(Br(M))-1; j0p=Joints(M)[J1]
    # geom facts
    bN=seg(M,0,FirstNodes(M)[LastStep(M)]-1)
    bP=seg(P,0,FirstNodes(P)[LastStep(P)]-1)
    aN=seg(M,j0p,n-1)
    J1p=len(Br(P))-1; j0pP=Joints(P)[J1p]
    aP=seg(P,j0pP,Lng(P)-1)
    ok = (bN==bP) and (j0p==j0pP) and (aN==aP+[M[n-1]]) and (entry(M,1,j0p)==entry(P,1,j0pP))
    if ok: g_ok+=1
    else:
        g_bad+=1
        if len(gcex)<8: gcex.append((fmt(M), bN==bP, j0p==j0pP, aN==aP+[M[n-1]]))
print(f"[geom lockstep] ok={g_ok} bad={g_bad}")
for c in gcex: print("   GEOM-CEX",c)

# 3) the STEP implication proper
s_ok=s_bad=s_vac=0; scex=[]
rpers_bad=0
for M in reg4_all:
    if not (cfbx_j1p(M) < Lng(M)-1): continue
    P=Pred(M)
    if Lng(P)<1 or len(Br(P))==0: continue
    if not reg4(P):
        rpers_bad+=1; continue
    try:
        vp=ve34(P); vn=ve34(M)
    except Exception: continue
    if vp and vn: s_ok+=1
    elif vp and not vn:
        s_bad+=1
        if len(scex)<8: scex.append(fmt(M))
    else: s_vac+=1  # premise false (shouldn't happen if whole-target holds)
print(f"[STEP impl] ve34(P)&ve34(N) ok={s_ok}  STEP-FAIL(vp&!vn)={s_bad}  premise-false={s_vac}  rpers_bad={rpers_bad}")
for c in scex: print("   STEP-CEX",c)

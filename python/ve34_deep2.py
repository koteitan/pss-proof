#!/usr/bin/env python3
# targeted deep spot-check: find reg4 STEP hosts via oper from small standard
# seeds; verify STEP + residuals directly. Hard-capped (few hosts, deep Lng).
import sys, itertools, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax, seg, fmt, reduced, oper)
from trans_model import Trans, bpHeadT

def LastStep(M):
    b=Br(M); J1=len(b)-1
    if not b: return 0
    if entry(b[J1],0,0)==entry(b[J1],1,0): return J1
    return min(J for J in range(len(b)) if entry(b[J1],0,0)==entry(b[J],0,0) and entry(b[J],1,0)<entry(b[J],0,0))
def cfbx_j1p(M): return FirstNodes(M)[len(Br(M))-1]
def reg4(M):
    if not (reduced(M) and monoT(M) and len(Br(M))>0): return False
    j1p=cfbx_j1p(M)
    if not (entry(M,0,j1p) > entry(M,1,j1p)): return False
    J1=len(Br(M))-1; j0p=Joints(M)[J1]
    return 0<j0p<TrMax(M)
def Pred(M): return M[:-1] if Lng(M)>1 else M
def is_prefix(A,B): return len(A)<=len(B) and B[:len(A)]==A
def ve34(M):
    n=Lng(M); b=Br(M); J1=len(b)-1
    j0p=Joints(M)[J1]; J0=LastStep(M); m1=FirstNodes(M)[J0]-1
    Mp=seg(M,j0p,n-1); N=seg(M,0,m1)
    A=bpHeadT(Trans(N)); B=bpHeadT(Trans(Mp)); C=bpHeadT(Trans(M)); v=entry(M,1,j0p)
    return is_prefix(A[1],B[1]) and len(A[1])<len(B[1]) and (C[1]==A[1]+[('D',v,B)])

# seeds: small reduced monoT with branch structure
seeds=[]
GRID=[(x,y) for x in range(4) for y in range(4)]
for L in range(4,5):
    for tup in itertools.product(GRID,repeat=L-1):
        M=[(0,0)]+list(tup)
        if reduced(M) and monoT(M) and len(Br(M))>0:
            seeds.append(M)
print(f"seeds={len(seeds)}", flush=True)

hosts=set()
t0=time.time()
for s in seeds:
    for nn in range(2,5):
        try: R=Red(oper(s,nn))
        except Exception: continue
        if 6<=Lng(R)<=14 and reg4(R) and cfbx_j1p(R)<Lng(R)-1:
            hosts.add(tuple(R))
    if time.time()-t0>90: break
hosts=[list(h) for h in hosts]
print(f"deep reg4-STEP hosts={len(hosts)}  maxLng={max((Lng(h) for h in hosts),default=0)}", flush=True)

s_ok=s_bad=g_ok=g_bad=he_ok=he_bad=hs_ok=hs_bad=w_ok=w_bad=0; scex=[]
for M in hosts:
    P=Pred(M)
    if Lng(P)<1 or len(Br(P))==0 or not reg4(P): continue
    wn=ve34(M)
    if wn: w_ok+=1
    else: w_bad+=1
    NfxN=seg(M,0,FirstNodes(M)[LastStep(M)]-1); NfxP=seg(P,0,FirstNodes(P)[LastStep(P)]-1)
    gN=bpHeadT(Trans(NfxN)); gP=bpHeadT(Trans(NfxP))
    if gP==gN: g_ok+=1
    else: g_bad+=1
    J1=len(Br(M))-1; j0p=Joints(M)[J1]; J1p=len(Br(P))-1; j0pP=Joints(P)[J1p]
    MpN=bpHeadT(Trans(seg(M,j0p,Lng(M)-1))); MpP=bpHeadT(Trans(seg(P,j0pP,Lng(P)-1)))
    if is_prefix(MpP[1],MpN[1]): he_ok+=1
    else: he_bad+=1
    v=entry(M,1,j0p); C=bpHeadT(Trans(M))
    if C[1]==gN[1]+[('D',v,('T',MpN[1]))]: hs_ok+=1
    else: hs_bad+=1
    vp=ve34(P)
    if vp and wn: s_ok+=1
    elif vp and not wn:
        s_bad+=1
        if len(scex)<5: scex.append(fmt(M))
print(f"[deep] whole:{w_ok}/{w_bad} geom:{g_ok}/{g_bad} hext:{he_ok}/{he_bad} hshift:{hs_ok}/{hs_bad} STEP:{s_ok}/FAIL{s_bad}")
for c in scex: print("  STEP-CEX",c)

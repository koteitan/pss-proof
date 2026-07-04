#!/usr/bin/env python3
# r38-VESTEP2 (fast): DEEP validation of the VE34 STEP over vg7x_reg4 + head-shift structure.
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

def gen_deep(seeds, cap, maxLng, minInter=10, maxInter=60):
    # BFS: apply oper(M,n) (n small) then Red; keep reduced results.
    # Track derivation DEPTH (frontier layers) and how many intermediates had Lng>=10.
    seen=set(seeds); frontier=list(seeds); depth=0; inter_hits=0; deep_layer_hosts=0
    maxdepth_of={s:0 for s in seeds}
    while frontier and len(seen)<cap:
        nxt=[]; depth+=1
        for M in frontier:
            Ml=list(M); d=maxdepth_of.get(M,0)
            for nn in (2,3):
                try:
                    inter=oper(Ml,nn)
                    Li=Lng(inter)
                    if Li>=minInter: inter_hits+=1
                    if Li>maxInter: continue    # skip Red-blowup
                    R=Red(inter)
                except Exception: continue
                if 2<=Lng(R)<=maxLng and reg2(R):
                    t=tuple(R)
                    if t not in seen:
                        seen.add(t); nxt.append(t); maxdepth_of[t]=d+1
                        if d+1>=9: deep_layer_hosts+=1
                        if len(seen)>=cap: break
            if len(seen)>=cap: break
        frontier=nxt
    return seen, depth, inter_hits, deep_layer_hosts, maxdepth_of

t0=time.time()
GRID=[(x,y) for x in range(3) for y in range(3)]
brute=set()
for L in range(3,5):
    for tup in itertools.product(GRID,repeat=L-1):
        M=[(0,0)]+list(tup)
        if reg2(M): brute.add(tuple(M))
print(f"brute={len(brute)} ({round(time.time()-t0,1)}s)", flush=True)
deep,depth,ih,deeph,mdof=gen_deep(brute, 6000, 16, minInter=10, maxInter=34)
corpus=brute|deep
print(f"corpus total={len(corpus)} bfs_depth={depth} inter_len>=10_hits={ih} deriv-depth>=9_hosts={deeph} ({round(time.time()-t0,1)}s)", flush=True)

reg7_all=[list(M) for M in corpus if reg7(list(M))]
# derivation depth of reg7 STEP hosts specifically
_maxdd=max((mdof.get(tuple(M),0) for M in reg7_all), default=0)
print(f"max deriv-depth among reg7 hosts = {_maxdd}", flush=True)
maxL=max((Lng(M) for M in reg7_all), default=0)
print(f"reg7 hosts: {len(reg7_all)}  maxLng={maxL} ({round(time.time()-t0,1)}s)", flush=True)

w_ok=w_bad=0; wcex=[]
for M in reg7_all:
    try: ok=ve34(M)
    except Exception: continue
    if ok: w_ok+=1
    else:
        w_bad+=1
        if len(wcex)<6: wcex.append(fmt(M))
print(f"[ve34 over reg7] ok={w_ok} bad={w_bad}", flush=True)
for c in wcex: print("   WHOLE-CEX",c)

step_hosts=[M for M in reg7_all if cfbx_j1p(M)<Lng(M)-1 and reg7(Pred(M)) and len(Br(Pred(M)))>0]
deepstep=[M for M in step_hosts if Lng(M)>=10]
_sdd=max((mdof.get(tuple(M),0) for M in step_hosts), default=0)
_sdd10=max((mdof.get(tuple(M),0) for M in deepstep), default=0)
print(f"[STEP hosts] {len(step_hosts)}  Lng>=10: {len(deepstep)}  max-deriv-depth(step)={_sdd} (Lng>=10 subset:{_sdd10})", flush=True)

g_ok=g_bad=0; gcex=[]
s_ok=s_bad=s_vac=0; scex=[]
case_count={3:0,4:0,'other':0}
resid_ok=resid_bad=0; residcex=[]
marked_j0=0; marked_notj0=0
ve3ext_ok=ve3ext_bad=0
sigma_eq_A=0; sigma_ne_A=0
for M in step_hosts:
    P=Pred(M)
    n=Lng(M); J1=len(Br(M))-1; j0p=Joints(M)[J1]
    bN=seg(M,0,FirstNodes(M)[LastStep(M)]-1)
    bP=seg(P,0,FirstNodes(P)[LastStep(P)]-1)
    aN=seg(M,j0p,n-1)
    J1p=len(Br(P))-1; j0pP=Joints(P)[J1p]
    aP=seg(P,j0pP,Lng(P)-1)
    geom = (bN==bP) and (j0p==j0pP) and (aN==aP+[M[n-1]]) and (entry(M,1,j0p)==entry(P,1,j0pP))
    if geom: g_ok+=1
    else:
        g_bad+=1
        if len(gcex)<8: gcex.append((fmt(M), bN==bP, j0p==j0pP, aN==aP+[M[n-1]]))
    try: vp=ve34(P); vn=ve34(M)
    except Exception: continue
    if vp and vn: s_ok+=1
    elif vp and not vn:
        s_bad+=1
        if len(scex)<8: scex.append(fmt(M))
    else: s_vac+=1
    if not (geom and vp and vn): continue
    v=entry(M,1,j0p)
    A=bpHeadT(Trans(bN)); hN=bpHeadT(Trans(aN)); hP=bpHeadT(Trans(aP))
    gN=bpHeadT(Trans(M)); gP=bpHeadT(Trans(P))
    lastP=gP[1][-1] if gP[1] else None
    lastN=gN[1][-1] if gN[1] else None
    j1p_idx=cfbx_j1p(M)
    if lastP and lastN:
        if lastP[1]==v and lastN[1]==v: case_count[4]+=1
        elif lastP[1]==entry(M,1,j1p_idx) and lastN[1]==entry(M,1,j1p_idx): case_count[3]+=1
        else: case_count['other']+=1
    tau3 = lastN[2] if (lastN and lastN[1]==v) else None
    if tau3 is not None:
        if hN==tau3: resid_ok+=1
        else:
            resid_bad+=1
            if len(residcex)<6: residcex.append(fmt(M))
    if tm.adm(M,j0p) and leR(M,0,j0p,n-1): marked_j0+=1
    else: marked_notj0+=1
    if is_prefix(A[1],hN[1]) and is_prefix(A[1],hP[1]):
        t2=hN[1][len(A[1]):]; t2p=hP[1][len(A[1]):]
        if is_prefix(t2p,t2): ve3ext_ok+=1
        else: ve3ext_bad+=1
    # terminal-slice keystone on aN: Trans(Pred aN)=Trans(aP)=D_v hP, Trans aN=D_v hN.
    # sigma1 = prefix of hP before its last D_v block?  compare with A.
    lastTP=hP[1][-1] if hP[1] else None
    if lastTP and lastTP[1]==v:
        sig1=('T',hP[1][:-1])
        if sig1==A: sigma_eq_A+=1
        else: sigma_ne_A+=1

print(f"[geom lockstep] ok={g_ok} bad={g_bad}", flush=True)
for c in gcex: print("   GEOM-CEX",c)
print(f"[STEP impl] ok={s_ok}  STEP-FAIL(vp&!vn)={s_bad}  premise-false={s_vac}", flush=True)
for c in scex: print("   STEP-CEX",c)
print(f"[keystone case for N] case4(D_j0')={case_count[4]} case3(D_j1')={case_count[3]} other={case_count['other']}")
print(f"[residual hN==tau3 | case4] ok={resid_ok} bad={resid_bad}")
for c in residcex: print("   RESID-CEX",c)
print(f"[(N,j0') in Marked?] yes={marked_j0} no={marked_notj0}")
print(f"[VE3_N ext: t2' prefix of t2] ok={ve3ext_ok} bad={ve3ext_bad}")
print(f"[slice-keystone sigma1==A?] eq={sigma_eq_A} ne={sigma_ne_A}")
print(f"done ({round(time.time()-t0,1)}s)", flush=True)

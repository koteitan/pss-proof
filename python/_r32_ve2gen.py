#!/usr/bin/env python3
# r32 VEGEOM2 VE2: deep generator of genuine condIIIV DT_PS hosts via Red of
# ancestor slices of oper-expanded standard forms; validate cfbx_reg j0' (seg M 0 m1)
# (J0>0 branch) AND the direct VE2 Trans equality, AND the prefix geometry.
import sys, time, itertools, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, seg, parent, Adm, adm,
                       oper, diagSeq, le0, leR, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax)
from trans_model import Trans, bpHeadT

def pr(*a): print(*a, flush=True)
def is_reduced(M): return Red(list(M)) == list(M)

def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0, len(bs)):
            a0, b0 = bs[J0][0]; a1, b1 = bs[J1][0]
            if not (a0 >= a1 and (a0 != a1 or b0 >= b1)): return False
    return True

def in_DT_PS(M):
    return is_reduced(M) and monoT(M) and descending(Br(M))

def LastStep(M):
    b = Br(M)
    if not b: return 0
    J1 = len(b)-1
    lastb = b[J1]
    if entry(lastb,0,0) == entry(lastb,1,0): return J1
    cands = [J for J in range(len(b))
             if entry(lastb,0,0)==entry(b[J],0,0) and entry(b[J],1,0)<entry(b[J],0,0)]
    return min(cands)

def cfbx_reg(m, N):
    if Lng(N) < 1: return ('fail','empty')
    if not is_reduced(N): return ('fail','notRed')
    if not monoT(N): return ('fail','notMono')
    b = Br(N)
    if not b: return ('fail','BrEmpty')
    jl = Joints(N)[len(b)-1]
    if jl is None: return ('fail','jointNone')
    if m < jl: return ('ok','lt')
    if m == jl:
        fn = FirstNodes(N)[len(b)-1]
        if entry(N,0,fn) == entry(N,1,fn) and descending(b): return ('ok','eqdiag')
        return ('fail','eq-BAD')
    return ('fail','gt-BAD')

def condIIIV_host(M):
    if not in_DT_PS(M): return None
    b = Br(M)
    if not b: return None
    J1 = len(b)-1
    j0p = Joints(M)[J1]; j1p = FirstNodes(M)[J1]
    if j0p is None: return None
    if not (0 < j0p and j0p < TrMax(M)): return None
    if not (entry(M,0,j1p) > entry(M,1,j1p)): return None
    J0 = LastStep(M)
    m1 = FirstNodes(M)[J0] - 1
    return (j0p, j1p, J0, m1, J1)

def gen_hosts(budget, seedmax=6):
    """Yield genuine condIIIV DT_PS hosts M (deduped) via Red of ancestor slices."""
    t0=time.time()
    seen=set()
    # deep standard forms via oper
    seeds=[]
    base_list=[[(0,0),(1,1),(2,1)],[(0,0),(1,1),(2,2),(3,1)],
               [(0,0),(1,1),(2,2),(2,1)],[(0,0),(1,1),(2,2),(3,2),(3,1)],
               [(0,0),(1,1),(2,2),(3,3),(4,1)],[(0,0),(1,1),(2,2),(2,0),(2,0)]]
    for base in base_list:
        S=list(base)
        for step in range(seedmax):
            for n in (2,3,4):
                try: X=oper(S,n)
                except Exception: continue
                if Lng(X)>=3: seeds.append(X)
            try: S=oper(S,3)
            except Exception: break
            if Lng(S)<2 or Lng(S)>40: break
    pr(f"[gen] {len(seeds)} seed sequences")
    for X in seeds:
        if time.time()-t0>budget: break
        n=Lng(X)
        for a in range(n):
            for b in range(a+1,n):
                if time.time()-t0>budget: break
                if not le0(X,a,b): continue
                S=seg(X,a,b)
                try: R=Red(S)
                except Exception: continue
                key=fmt(R)
                if key in seen: continue
                seen.add(key)
                if condIIIV_host(R) is not None:
                    yield R

def main():
    t0=time.time()
    budget=int(sys.argv[1]) if len(sys.argv)>1 else 400
    hosts=0; J0zero=0; J0pos=0
    reg_ok=0; reg_fail=0; cls_ok={}; cls_fail={}
    ve2_ok=0; ve2_bad=0
    g_trmax_bad=0; g_brtake_bad=0; g_joint_bad=0; g_j0ple_bad=0; gcount=0
    fails=[]; ve2fails=[]
    maxL=0
    for M in gen_hosts(budget):
        hosts+=1
        j0p,j1p,J0,m1,J1=condIIIV_host(M)
        maxL=max(maxL,Lng(M))
        N=seg(M,0,m1); Np=seg(M,j0p,m1)
        # direct VE2 Trans equality
        try:
            v2 = (bpHeadT(Trans(Np))==bpHeadT(Trans(N)))
        except Exception as e:
            v2=None
        if v2 is True: ve2_ok+=1
        elif v2 is False:
            ve2_bad+=1
            if len(ve2fails)<8: ve2fails.append((fmt(M),f"J0={J0}"))
        # cfbx_reg
        st,cl=cfbx_reg(j0p,N)
        if J0==0: J0zero+=1
        else: J0pos+=1
        if st=='ok': reg_ok+=1; cls_ok[cl]=cls_ok.get(cl,0)+1
        else:
            reg_fail+=1; cls_fail[cl]=cls_fail.get(cl,0)+1
            if J0>0 and len(fails)<10:
                fails.append((fmt(M),f"J0={J0}",f"j0p={j0p}",f"m1={m1}",cl))
        if J0>0:
            gcount+=1
            if TrMax(N)!=TrMax(M): g_trmax_bad+=1
            if Br(N)!=Br(M)[:J0]: g_brtake_bad+=1
            JN=Joints(N); JM=Joints(M)
            if not(len(JN)>=J0 and len(JM)>=J0 and JN[J0-1]==JM[J0-1]): g_joint_bad+=1
            if not(len(JM)>=J0 and JM[J0-1] is not None and j0p<=JM[J0-1]): g_j0ple_bad+=1
    pr("="*70)
    pr(f"[hosts] total={hosts} maxLng={maxL} J0=0:{J0zero} J0>0:{J0pos} t={time.time()-t0:.0f}s")
    pr(f"[VE2 direct Trans] ok={ve2_ok} bad={ve2_bad}")
    for e in ve2fails: pr("   VE2FAIL:",e)
    pr(f"[VE2 cfbx_reg] ok={reg_ok} fail={reg_fail}")
    pr(f"   ok classes  ={cls_ok}")
    pr(f"   fail classes={cls_fail}")
    pr(f"[geom J0>0 count={gcount}] TrMaxBad={g_trmax_bad} BrTakeBad={g_brtake_bad} "
       f"JointBad={g_joint_bad} j0pleBad={g_j0ple_bad}")
    for e in fails: pr("   REGFAIL(J0>0):",e)

if __name__=='__main__':
    main()

#!/usr/bin/env python3
# r32 VEGEOM2 VE2 GEOMETRY: broad validation of the prefix-slice geometry that
# underlies cfbx_reg j0' (seg M 0 m1).  Enumerate DT_PS hosts with Br!=[] and
# last-branch guard (M0,j1'>M1,j1'), and at J0=LastStep check:
#   Br(N)=take J0 (Br M), TrMax(N)=TrMax(M), Joints(N)!=Joints(M) coincidence,
#   and cfbx_reg j0' N  (split on J0=0 / J0>0 / eqdiag).
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, seg, parent, Adm, adm,
                       oper, diagSeq, le0, leR, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax)

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

def main():
    t0=time.time()
    Lmax=int(sys.argv[1]) if len(sys.argv)>1 else 6
    vmax=int(sys.argv[2]) if len(sys.argv)>2 else 4
    budget=int(sys.argv[3]) if len(sys.argv)>3 else 500
    cells=[(a,b) for a in range(vmax) for b in range(vmax)]
    hosts=0; J0zero=0; J0pos=0; J0eqJ1=0
    reg_ok=0; reg_fail=0; cls_ok={}; cls_fail={}
    g_trmax_bad=0; g_brtake_bad=0; g_joint_bad=0; g_j0ple_bad=0; gcount=0
    fails=[]
    for L in range(3,Lmax+1):
        if time.time()-t0>budget: pr(f"[budget] stop L={L}"); break
        cnt=0
        for tup in itertools.product(cells, repeat=L-1):
            if time.time()-t0>budget: break
            M=[(0,0)]+list(tup)
            if not monoT(M): continue
            if not is_reduced(M): continue
            b=Br(M)
            if not b: continue
            if not descending(b): continue
            J1=len(b)-1
            j1p=FirstNodes(M)[J1]
            # last-branch guard: non-diagonal last branch
            if not (entry(M,0,j1p) > entry(M,1,j1p)): continue
            j0p=Joints(M)[J1]
            if j0p is None: continue
            J0=LastStep(M)
            m1=FirstNodes(M)[J0]-1
            N=seg(M,0,m1)
            hosts+=1; cnt+=1
            if J0==0: J0zero+=1
            else:
                J0pos+=1
                if J0==J1: J0eqJ1+=1
            st,cl=cfbx_reg(j0p,N)
            if st=='ok': reg_ok+=1; cls_ok[cl]=cls_ok.get(cl,0)+1
            else:
                reg_fail+=1; cls_fail[cl]=cls_fail.get(cl,0)+1
                if J0>0 and len(fails)<12:
                    fails.append((fmt(M),f"J0={J0}",f"J1={J1}",f"j0p={j0p}",f"m1={m1}",cl))
            if J0>0:
                gcount+=1
                if TrMax(N)!=TrMax(M): g_trmax_bad+=1
                if Br(N)!=b[:J0]: g_brtake_bad+=1
                JN=Joints(N); JM=Joints(M)
                if not(len(JN)>=J0 and JN[J0-1]==JM[J0-1]): g_joint_bad+=1
                if not(JM[J0-1] is not None and j0p<=JM[J0-1]): g_j0ple_bad+=1
        pr(f"[L={L}] hosts={hosts}(+{cnt}) reg_ok={reg_ok} reg_fail={reg_fail} "
           f"J0=0:{J0zero} J0>0:{J0pos}(J0=J1:{J0eqJ1}) t={time.time()-t0:.0f}s")
    pr("="*70)
    pr(f"[cfbx_reg @ LastStep] ok={reg_ok}/{hosts} fail={reg_fail}")
    pr(f"   ok classes  ={cls_ok}")
    pr(f"   fail classes={cls_fail}")
    pr(f"[split] J0=0:{J0zero} J0>0:{J0pos} (of which J0=J1:{J0eqJ1})")
    pr(f"[geom J0>0 count={gcount}] TrMaxBad={g_trmax_bad} BrTakeBad={g_brtake_bad} "
       f"JointBad={g_joint_bad} j0pleBad={g_j0ple_bad}")
    for e in fails: pr("   REGFAIL(J0>0):",e)

if __name__=='__main__':
    main()

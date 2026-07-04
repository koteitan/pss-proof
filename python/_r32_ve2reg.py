#!/usr/bin/env python3
# r32 VEGEOM2 VE2: validate cfbx_reg j0' (seg M 0 m1) (the prefix regime) on the
# GENUINE condIIIV regime, plus the supporting prefix geometry claims.
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, Adm, adm, nadm,
                       oper, diagSeq, le0, leR, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax, Pred, is_standard)

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

def T_PS(M): return len(M) >= 1

def cfbx_reg(m, N):
    """cfbx_reg m N per pss_defs: N in RT_PS & PT_PS & Br N != [] & (m<jl | (m=jl & diag & desc))"""
    if not T_PS(N): return ('fail','empty')
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
    """Return (j0p, j1p, J0, m1, J1) if M is in the genuine condIIIV regime, else None."""
    if not in_DT_PS(M): return None
    b = Br(M)
    if not b: return None
    J1 = len(b)-1
    j0p = Joints(M)[J1]
    j1p = FirstNodes(M)[J1]
    if j0p is None: return None
    if not (0 < j0p and j0p < TrMax(M)): return None
    if not (entry(M,0,j1p) > entry(M,1,j1p)): return None   # guard M0,j1' > M1,j1'
    J0 = LastStep(M)
    m1 = FirstNodes(M)[J0] - 1
    return (j0p, j1p, J0, m1, J1)

def main():
    t0 = time.time()
    Lmax = int(sys.argv[1]) if len(sys.argv)>1 else 8
    vmax = int(sys.argv[2]) if len(sys.argv)>2 else 4
    cap  = int(sys.argv[3]) if len(sys.argv)>3 else 30000
    budget = int(sys.argv[4]) if len(sys.argv)>4 else 1200
    cells = [(a,b) for a in range(vmax) for b in range(vmax)]

    hosts=0
    reg_ok=0; reg_fail=0
    cls_ok={}; cls_fail={}
    J0zero=0; J0pos=0
    # geometry sub-claims (only meaningful for J0>0)
    g_trmax=0; g_trmax_bad=0
    g_brtake=0; g_brtake_bad=0
    g_joint=0; g_joint_bad=0
    g_j0ple=0; g_j0ple_bad=0
    examples_fail=[]
    seen=0
    for L in range(3, Lmax+1):
        if time.time()-t0>budget: pr(f"[budget] stop L={L}"); break
        for tup in itertools.product(cells, repeat=L-1):
            if seen>=cap or time.time()-t0>budget: break
            M=[(0,0)]+list(tup)
            info=condIIIV_host(M)
            if info is None: continue
            seen+=1
            hosts+=1
            j0p,j1p,J0,m1,J1=info
            N=seg(M,0,m1)
            # cfbx_reg check
            st,cl=cfbx_reg(j0p,N)
            if J0==0: J0zero+=1
            else: J0pos+=1
            if st=='ok':
                reg_ok+=1; cls_ok[cl]=cls_ok.get(cl,0)+1
            else:
                reg_fail+=1; cls_fail[cl]=cls_fail.get(cl,0)+1
                if len(examples_fail)<10:
                    examples_fail.append((fmt(M),f"J0={J0}",f"j0p={j0p}",f"m1={m1}",cl,f"BrN={len(Br(N))}"))
            # geometry sub-claims (J0>0 branch)
            if J0>0:
                # TrMax(N)==TrMax(M)
                if TrMax(N)==TrMax(M): g_trmax+=1
                else: g_trmax_bad+=1
                # Br(N)==take J0 (Br M)
                if Br(N)==Br(M)[:J0]: g_brtake+=1
                else: g_brtake_bad+=1
                # Joints(N)[J0-1]==Joints(M)[J0-1]
                JN=Joints(N); JM=Joints(M)
                if len(JN)>=J0 and len(JM)>=J0 and JN[J0-1]==JM[J0-1]: g_joint+=1
                else: g_joint_bad+=1
                # j0' <= Joints(M)[J0-1]
                if len(JM)>=J0 and JM[J0-1] is not None and j0p<=JM[J0-1]: g_j0ple+=1
                else: g_j0ple_bad+=1
        pr(f"[L={L}] hosts={hosts} reg_ok={reg_ok} reg_fail={reg_fail} "
           f"J0=0:{J0zero} J0>0:{J0pos} t={time.time()-t0:.0f}s seen={seen}")
        if seen>=cap: pr(f"[cap] reached {cap}"); break
    pr("="*70)
    pr(f"[VE2 cfbx_reg] ok={reg_ok}/{hosts} fail={reg_fail}")
    pr(f"   ok classes  = {cls_ok}")
    pr(f"   fail classes= {cls_fail}")
    pr(f"[split] J0=0 (pure-trunk-prefix)={J0zero}  J0>0={J0pos}")
    pr(f"[geom J0>0] TrMax(N)=TrMax(M): {g_trmax} bad={g_trmax_bad}")
    pr(f"[geom J0>0] Br(N)=take J0 (Br M): {g_brtake} bad={g_brtake_bad}")
    pr(f"[geom J0>0] Joints(N)[J0-1]=Joints(M)[J0-1]: {g_joint} bad={g_joint_bad}")
    pr(f"[geom J0>0] j0' <= Joints(M)[J0-1]: {g_j0ple} bad={g_j0ple_bad}")
    for e in examples_fail: pr("   FAIL:", e)

if __name__=='__main__':
    main()

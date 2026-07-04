#!/usr/bin/env python3
# r31 JGEBYP: validate the three targets
#  (1) JGE  : TrMax(Red N) <= Joints(Red N)!last  on genuine condIII guard hosts
#             via single-branch(Lng(Br(Red N))=1) + parent(Red N,0,TrMax+1)=TrMax
#  (2) M0RUN: NOT(jm3<jm2) ==> nextR M 1 jm2 (jm2+1)
#  (3) REGSP bypass: on guard hosts, Br(Red(Pred N)) empty-fraction, and on the
#             empty (trunk) branch, Red(Pred N) is a diagSeq (all-trunk).
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, Adm, adm, nadm,
                       diagSeq, le0, leR, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax, Pred, is_standard, nextR, nextrel1)

def pr(*a): print(*a, flush=True)
def is_reduced(M): return Red(list(M)) == list(M)

def s84_jm2(M): return parent(M,1,Lng(M)-1)
def s84_jm3(M):
    jm2 = s84_jm2(M)
    return Adm(M, jm2)
def transJ0(M): return parent(M,0,Lng(M)-1)

def condIII(M):
    n=Lng(M)
    if n<3: return False
    if not hasParent(M,0,n-1): return False
    if not hasParent(M,1,n-1): return False
    j0=transJ0(M)
    return (entry(M,1,n-1)>0 and entry(M,1,j0)>=entry(M,1,n-1) and adm(M,j0))

def genuineIII(M):
    if Lng(M)-1<=1: return False
    if not monoT(M): return False
    if not is_reduced(M): return False
    if not hasParent(M,1,Lng(M)-1): return False
    return condIII(M)

def is_diagSeq(R):
    if len(R)==0: return False
    a=R[0][0]
    for k,(x,y) in enumerate(R):
        if x!=a+k or y!=a+k: return False
    return True

def main():
    t0=time.time()
    Lmax=int(sys.argv[1]) if len(sys.argv)>1 else 8
    vmax=int(sys.argv[2]) if len(sys.argv)>2 else 5
    require_std = (len(sys.argv)<=3) or (sys.argv[3]!='nostd')
    cells=[(a,b) for a in range(vmax) for b in range(vmax)]
    # counters
    jge_ok=jge_bad=jge_hosts=0
    sb_one=sb_multi=0                  # single-branch count of Red N
    par_ok=par_bad=0                   # parent(RN,0,TrMax+1)=TrMax
    m0_ok=m0_bad=0; m0_hosts=0         # M0RUN
    bp_empty=bp_non=0                  # Br(Red(Pred N)) empty vs not (guard hosts)
    bp_diag_ok=bp_diag_bad=0           # empty branch => diagSeq
    regsp_true=regsp_false=0           # cfbx_reg on Red(Pred N) truth (guard hosts)
    jge_ex=[]; m0_ex=[]; par_ex=[]; diag_ex=[]
    hosts=0
    budget=1500
    for L in range(3,Lmax+1):
        if time.time()-t0>budget: pr(f"[budget] stop before L={L}"); break
        for tup in itertools.product(cells,repeat=L-1):
            if time.time()-t0>budget: break
            M=[(0,0)]+list(tup)
            if not genuineIII(M): continue
            if require_std and not is_standard(M): continue
            hosts+=1
            jm2=s84_jm2(M); jm3=s84_jm3(M)
            N=seg(M,jm3,Lng(M)-1)
            RN=Red(N)
            if jm3<jm2:
                # ---- JGE ----
                jge_hosts+=1
                bR=Br(RN)
                if len(bR)==1: sb_one+=1
                else: sb_multi+=1
                tr=TrMax(RN)
                # parent(RN,0,tr+1)
                if tr+1<Lng(RN):
                    p=parent(RN,0,tr+1)
                    if p==tr: par_ok+=1
                    else:
                        par_bad+=1
                        if len(par_ex)<6: par_ex.append((fmt(M),fmt(RN),tr,p))
                jl_list=Joints(RN)
                if bR and jl_list and jl_list[-1] is not None:
                    jl=jl_list[-1]
                    if tr<=jl: jge_ok+=1
                    else:
                        jge_bad+=1
                        if len(jge_ex)<6: jge_ex.append((fmt(M),fmt(RN),tr,jl))
                # ---- REGSP bypass ----
                PN=Pred(N)   # = seg M jm3 (Lng-2)
                RPN=Red(PN)
                bRPN=Br(RPN)
                if not bRPN:
                    bp_empty+=1
                    if is_diagSeq(RPN): bp_diag_ok+=1
                    else:
                        bp_diag_bad+=1
                        if len(diag_ex)<6: diag_ex.append((fmt(M),fmt(RPN)))
                else:
                    bp_non+=1
                # cfbx_reg truth on Red(Pred N)
                d=jm2-jm3
                if bRPN:
                    jlp=Joints(RPN)[len(bRPN)-1]
                    if jlp is not None:
                        fn=FirstNodes(RPN)[len(bRPN)-1]
                        okdiag=(entry(RPN,0,fn)==entry(RPN,1,fn))
                        # descending
                        desc=True
                        for J0 in range(len(bRPN)):
                            for J1 in range(J0,len(bRPN)):
                                a0,b0=bRPN[J0][0]; a1,b1=bRPN[J1][0]
                                if not(a0>=a1 and (a0!=a1 or b0>=b1)): desc=False
                        cond=(d<jlp) or (d==jlp and okdiag and desc)
                        if is_reduced(RPN) and monoT(RPN) and cond: regsp_true+=1
                        else: regsp_false+=1
                    else: regsp_false+=1
                else:
                    regsp_false+=1  # Br empty => cfbx_reg unsatisfiable
            else:
                # ---- M0RUN (jm3==jm2) ----
                m0_hosts+=1
                if nextrel1(M,jm2,jm2+1): m0_ok+=1
                else:
                    m0_bad+=1
                    if len(m0_ex)<8: m0_ex.append((fmt(M),jm2,adm(M,jm2)))
        pr(f"[L={L}] hosts={hosts} jgeG={jge_hosts} m0={m0_hosts} t={time.time()-t0:.0f}s")
    pr("="*64)
    pr(f"HOSTS genuine condIII = {hosts}  (guard {jge_hosts}, m0-edge {m0_hosts})")
    pr(f"[1 JGE] TrMax<=Joints!last  ok={jge_ok} bad={jge_bad}")
    pr(f"        single-branch Red N: one={sb_one} multi={sb_multi}")
    pr(f"        parent(RN,0,TrMax+1)=TrMax ok={par_ok} bad={par_bad}")
    for e in jge_ex: pr("   JGE BAD:",e)
    for e in par_ex: pr("   PAR BAD:",e)
    pr(f"[2 M0RUN] nextR1 jm2 (jm2+1) ok={m0_ok} bad={m0_bad}")
    for e in m0_ex: pr("   M0 BAD:",e)
    pr(f"[3 REGSP] Br(Red(Pred N)): empty={bp_empty} nonempty={bp_non}")
    pr(f"        empty-branch is diagSeq ok={bp_diag_ok} bad={bp_diag_bad}")
    pr(f"        cfbx_reg(Red(Pred N)) TRUE={regsp_true} FALSE={regsp_false}")
    for e in diag_ex: pr("   DIAG BAD:",e)

if __name__=='__main__':
    main()

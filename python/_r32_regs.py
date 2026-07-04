#!/usr/bin/env python3
# Validate the CORRECT REGS residual (JGE is FALSE): cfbx_reg(d)(RN) and its
# MCOND core (d<Joints!last OR d=Joints!last & diag@fn_last), over broad corpus.
# Also re-confirm JGE falsity and check TrMax-run bound d<TrMax(RN).
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, monoT, seg, parent, Adm, adm, nadm,
                       diagSeq, le0, leR, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax, Pred, nextR, nextrel1, oper)
def pr(*a): print(*a, flush=True)
def s84_jm2(M): return parent(M,1,Lng(M)-1)
def s84_jm3(M): return Adm(M, s84_jm2(M))
def transJ0(M): return parent(M,0,Lng(M)-1)
def condIII(M):
    n=Lng(M)
    if n<3 or not hasParent(M,0,n-1) or not hasParent(M,1,n-1): return False
    j0=transJ0(M)
    return (entry(M,1,n-1)>0 and entry(M,1,j0)>=entry(M,1,n-1) and adm(M,j0))
def genuineIII(M):
    if Lng(M)-1<=1 or not monoT(M) or not hasParent(M,1,Lng(M)-1): return False
    return condIII(M)
def gen(maxlen,vcap,budget):
    t0=time.time(); seen=set(); frontier=[]
    for v in range(1,maxlen):
        d=diagSeq(0,v)
        if Lng(d)<=maxlen: frontier.append(tuple(map(tuple,d)))
    seen.update(frontier); hosts=list(frontier)
    while frontier:
        if time.time()-t0>budget: break
        nf=[]
        for M in frontier:
            Ml=[list(p) for p in M]
            for n in (1,2,3,4):
                O=oper(Ml,n)
                if Lng(O)<1 or Lng(O)>maxlen: continue
                if any(a>vcap or b>vcap for (a,b) in O): continue
                t=tuple(map(tuple,O))
                if t not in seen: seen.add(t); nf.append(t); hosts.append(t)
        frontier=nf
    return [[list(p) for p in M] for M in hosts]
def descending_br(bR):
    for J0 in range(len(bR)):
        for J1 in range(J0,len(bR)):
            a0,b0=bR[J0][0]; a1,b1=bR[J1][0]
            if not(a0>=a1 and (a0!=a1 or b0>=b1)): return False
    return True
def main():
    t0=time.time()
    maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 12
    vcap=int(sys.argv[2]) if len(sys.argv)>2 else 8
    budget=int(sys.argv[3]) if len(sys.argv)>3 else 600
    hosts=gen(maxlen,vcap,budget*0.55)
    pr(f"hosts={len(hosts)} t={time.time()-t0:.0f}s")
    ng=0
    regs_ok=regs_bad=0        # cfbx_reg(d)(RN) full
    mcond_ok=mcond_bad=0      # d<jl OR (d=jl & diag)
    dltjl=deqjl=dgtjl=0       # relation d vs Joints!last
    dlttr=0; dgetr=0          # d < TrMax(RN)  (crx_trmax_run)
    jge_ok=jge_bad=0          # TrMax<=Joints!last (the FALSE claim)
    ex_regs=[]; ex_dgt=[]; ex_jge=[]
    for M in hosts:
        if time.time()-t0>budget: pr("[budget]"); break
        if not genuineIII(M): continue
        jm2=s84_jm2(M); jm3=s84_jm3(M)
        if not (jm3<jm2): continue
        ng+=1
        N=seg(M,jm3,Lng(M)-1); RN=Red(N)
        b=Br(RN)
        d=jm2-jm3
        tr=TrMax(RN)
        if d<tr: dlttr+=1
        else: dgetr+=1
        if not b:
            regs_bad+=1  # Br empty => cfbx_reg false
            if len(ex_regs)<8: ex_regs.append(("BR[]",fmt(M),fmt(RN),d))
            continue
        jl=Joints(RN)[len(b)-1]; fn=FirstNodes(RN)[len(b)-1]
        if jl is None:
            regs_bad+=1; continue
        if d<jl: dltjl+=1
        elif d==jl: deqjl+=1
        else:
            dgtjl+=1
            if len(ex_dgt)<8: ex_dgt.append((fmt(M),fmt(RN),d,jl,tr))
        if tr<=jl: jge_ok+=1
        else:
            jge_bad+=1
            if len(ex_jge)<6: ex_jge.append((fmt(M),fmt(RN),tr,jl,d))
        diag=(entry(RN,0,fn)==entry(RN,1,fn))
        mcond=(d<jl) or (d==jl and diag)
        if mcond: mcond_ok+=1
        else:
            mcond_bad+=1
            if len(ex_regs)<8: ex_regs.append(("MCOND",fmt(M),fmt(RN),d,jl,diag))
        # full cfbx_reg
        from red_model import Red as _R
        cf=(_R(RN)==RN and monoT(RN) and b and mcond and descending_br(b))
        if cf: regs_ok+=1
        else:
            regs_bad+=1
            if len(ex_regs)<8: ex_regs.append(("CFBX",fmt(M),fmt(RN),d,jl))
    pr("="*60)
    pr(f"guard genuine condIII hosts = {ng}")
    pr(f"[REGS] cfbx_reg(d)(RN) full: ok={regs_ok} bad={regs_bad}")
    pr(f"[MCOND] d<jl OR (d=jl & diag): ok={mcond_ok} bad={mcond_bad}")
    pr(f"  d vs Joints!last: d<jl={dltjl} d=jl={deqjl} d>jl={dgtjl}")
    pr(f"  crx_trmax_run d<TrMax(RN): ok={dlttr} bad={dgetr}")
    pr(f"[JGE(FALSE?)] TrMax<=Joints!last: ok={jge_ok} bad={jge_bad}")
    for e in ex_dgt: pr("  d>jl:",e)
    for e in ex_jge: pr("  JGE-BAD:",e)
    for e in ex_regs: pr("  REGS-BAD:",e)
    pr(f"t={time.time()-t0:.0f}s")
if __name__=='__main__': main()

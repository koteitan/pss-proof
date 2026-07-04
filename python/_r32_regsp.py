#!/usr/bin/env python3
# Broad validation of REGSP (Br<>[] guarded): cfbx_reg(d)(Red(Pred N)) under
# Br(Red(Pred N))<>[], on genuine condIII standard hosts. Guard against a
# JGE-style silent falsity. Also report the d vs joint relation for the Pred slice.
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
def is_reduced(M): return Red(list(M))==list(M)
def main():
    t0=time.time()
    maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 12
    vcap=int(sys.argv[2]) if len(sys.argv)>2 else 8
    budget=int(sys.argv[3]) if len(sys.argv)>3 else 600
    hosts=gen(maxlen,vcap,budget*0.55)
    pr(f"hosts={len(hosts)} t={time.time()-t0:.0f}s")
    ng=0; brne=0; bremp=0
    regsp_ok=regsp_bad=0; dlt=deq=dgt=0
    ex=[]
    for M in hosts:
        if time.time()-t0>budget: pr("[budget]"); break
        if not genuineIII(M): continue
        jm2=s84_jm2(M); jm3=s84_jm3(M)
        if not (jm3<jm2): continue
        ng+=1
        N=seg(M,jm3,Lng(M)-1); PN=Pred(N); RPN=Red(PN); b=Br(RPN)
        d=jm2-jm3
        if not b: bremp+=1; continue
        brne+=1
        jl=Joints(RPN)[len(b)-1]; fn=FirstNodes(RPN)[len(b)-1]
        if jl is None: regsp_bad+=1; continue
        if d<jl: dlt+=1
        elif d==jl: deq+=1
        else:
            dgt+=1
            if len(ex)<8: ex.append(("d>jl",fmt(M),fmt(RPN),d,jl))
        diag=(entry(RPN,0,fn)==entry(RPN,1,fn))
        mcond=(d<jl) or (d==jl and diag)
        cf=(is_reduced(RPN) and monoT(RPN) and mcond and descending_br(b))
        if cf: regsp_ok+=1
        else:
            regsp_bad+=1
            if len(ex)<8: ex.append(("CFBX",fmt(M),fmt(RPN),d,jl,diag))
    pr("="*60)
    pr(f"guard genuine condIII hosts={ng}  Pred-slice Br<>[]={brne}  Br=[]={bremp}")
    pr(f"[REGSP] cfbx_reg(d)(Red(Pred N)) [Br<>[]] ok={regsp_ok} bad={regsp_bad}")
    pr(f"  d vs joint(Pred): d<jl={dlt} d=jl={deq} d>jl={dgt}")
    for e in ex: pr("  EX:",e)
    pr(f"t={time.time()-t0:.0f}s")
if __name__=='__main__': main()

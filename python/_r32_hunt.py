#!/usr/bin/env python3
# hunt guard (jm3<jm2) condIII hosts with jm3>0 or nBr>=2; verify last-joint
# admissible & >0 & ==TrMax universally.
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
def main():
    t0=time.time()
    maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 12
    vcap=int(sys.argv[2]) if len(sys.argv)>2 else 9
    budget=int(sys.argv[3]) if len(sys.argv)>3 else 600
    hosts=gen(maxlen,vcap,budget*0.5)
    pr(f"hosts={len(hosts)} t={time.time()-t0:.0f}s")
    ng=0; jm3pos=0; multi=0
    la_ok=la_bad=0; lp_ok=lp_bad=0; lt_ok=lt_bad=0
    ex_jm3pos=[]; ex_multi=[]; ex_bad=[]
    for M in hosts:
        if time.time()-t0>budget: pr("[budget]"); break
        if not genuineIII(M): continue
        jm2=s84_jm2(M); jm3=s84_jm3(M)
        if not (jm3<jm2): continue
        ng+=1
        N=seg(M,jm3,Lng(M)-1); RN=Red(N)
        b=Br(RN)
        if not b: continue
        tr=TrMax(RN); jl=Joints(RN)[len(b)-1]
        if jm3>0:
            jm3pos+=1
            if len(ex_jm3pos)<8: ex_jm3pos.append((fmt(M),jm3,jm2,fmt(RN)))
        if len(b)>=2:
            multi+=1
            if len(ex_multi)<8: ex_multi.append((fmt(M),fmt(RN),Joints(RN),tr))
        if jl is not None:
            if adm(RN,jl): la_ok+=1
            else:
                la_bad+=1
                if len(ex_bad)<8: ex_bad.append(("ADM",fmt(M),fmt(RN),jl,tr))
            if jl>0: lp_ok+=1
            else:
                lp_bad+=1
                if len(ex_bad)<8: ex_bad.append(("POS",fmt(M),fmt(RN),jl,tr))
            if jl==tr: lt_ok+=1
            else:
                lt_bad+=1
                if len(ex_bad)<8: ex_bad.append(("EQ",fmt(M),fmt(RN),jl,tr))
    pr("="*60)
    pr(f"guard hosts={ng}  jm3>0={jm3pos}  multi-branch(nBr>=2)={multi}")
    pr(f"last-joint admissible ok={la_ok} bad={la_bad}")
    pr(f"last-joint >0 ok={lp_ok} bad={lp_bad}")
    pr(f"last-joint ==TrMax ok={lt_ok} bad={lt_bad}")
    for e in ex_jm3pos: pr("  JM3POS:",e)
    for e in ex_multi: pr("  MULTI:",e)
    for e in ex_bad: pr("  BAD:",e)
    pr(f"t={time.time()-t0:.0f}s")
if __name__=='__main__': main()

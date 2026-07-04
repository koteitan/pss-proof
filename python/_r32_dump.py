#!/usr/bin/env python3
# dump full structure of the guard (jm3<jm2) and REGSP hosts
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
            for n in (1,2,3):
                O=oper(Ml,n)
                if Lng(O)<1 or Lng(O)>maxlen: continue
                if any(a>vcap or b>vcap for (a,b) in O): continue
                t=tuple(map(tuple,O))
                if t not in seen: seen.add(t); nf.append(t); hosts.append(t)
        frontier=nf
    return [[list(p) for p in M] for M in hosts]
def brdesc(RN):
    b=Br(RN); fn=FirstNodes(RN); jn=Joints(RN); tr=TrMax(RN)
    info=[]
    for J in range(len(b)):
        info.append((fn[J], jn[J], adm(RN,jn[J]) if jn[J] is not None else None))
    return tr, len(b), info
def main():
    maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 11
    vcap=int(sys.argv[2]) if len(sys.argv)>2 else 6
    hosts=gen(maxlen,vcap,200)
    pr(f"hosts={len(hosts)}")
    ng=0; nr=0
    for M in hosts:
        if not genuineIII(M): continue
        jm2=s84_jm2(M); jm3=s84_jm3(M)
        if jm3<jm2:
            ng+=1
            N=seg(M,jm3,Lng(M)-1); RN=Red(N)
            tr,nb,info=brdesc(RN)
            pr(f"--- GUARD host M={fmt(M)}")
            pr(f"    jm3={jm3} jm2={jm2} d={jm2-jm3} j0={transJ0(M)} N={fmt(N)}")
            pr(f"    RN={fmt(RN)} TrMax={tr} nBr={nb} lastcol={Lng(RN)-1}")
            pr(f"    branches(fn,joint,adm-joint)={info}")
            pr(f"    all-joints==TrMax: {all(j==tr for _,j,_ in info)}  first-attach parent0(TrMax+1)={parent(RN,0,tr+1) if tr+1<Lng(RN) else 'NA'}")
            # PRED slice for REGSP
            PN=Pred(N); RPN=Red(PN); bP=Br(RPN)
            if bP:
                nr+=1
                trP=TrMax(RPN); fnP=FirstNodes(RPN); jnP=Joints(RPN)
                pr(f"    [REGSP] Pred(N)={fmt(PN)} RPN={fmt(RPN)} TrMaxP={trP} nBrP={len(bP)}")
                pr(f"            joints_P={jnP} d={jm2-jm3} jl_P={jnP[-1]} adm-jl={adm(RPN,jnP[-1]) if jnP[-1] is not None else None}")
    pr(f"guard hosts={ng} regsp(Br<>[])={nr}")
if __name__=='__main__': main()

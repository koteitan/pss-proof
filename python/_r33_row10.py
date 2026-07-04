#!/usr/bin/env python3
# r33 VE34: validate ROW10 generalization  entry M 1 j <= entry M 0 j  for all j,
# reduced monoT M, and probe the induction sub-claims.
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, seg, parent, diagSeq, le0, le1, leR,
                       Br, FirstNodes, Joints, Red, hasParent, fmt, TrMax, oper,
                       nextrel0, nextrel1)
def pr(*a): print(*a, flush=True)
def is_reduced(M): return Red(list(M))==list(M)
def descending_br(bR):
    for J0 in range(len(bR)):
        for J1 in range(J0,len(bR)):
            a0,b0=bR[J0][0]; a1,b1=bR[J1][0]
            if not(a0>=a1 and (a0!=a1 or b0>=b1)): return False
    return True
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
    maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 14
    vcap=int(sys.argv[2]) if len(sys.argv)>2 else 9
    budget=int(sys.argv[3]) if len(sys.argv)>3 else 400
    hosts=gen(maxlen,vcap,budget)
    pr(f"oper-orbit hosts={len(hosts)} maxLng={max(Lng(M) for M in hosts)} t={time.time()-t0:.0f}s")
    # main claim over reduced monoT (oper orbit => standard => reduced monoT)
    allj_ok=allj_bad=0
    # sub-claim (a): hasParent M 1 j => hasParent M 0 j
    a_ok=a_bad=0
    # sub-claim (b): entry M 1 j > 0  =>  hasParent M 1 j    (reduced monoT)
    b_ok=b_bad=0
    # sub-claim (b'): NOT hasParent M 1 j => entry M 1 j = 0
    # classification counts of (hasP0,hasP1) at each j
    cls={}
    cex_all=[]; cex_a=[]; cex_b=[]
    nred=0
    for M in hosts:
        if not (monoT(M) and is_reduced(M)): continue
        nred+=1
        n=Lng(M)
        for j in range(n):
            r0=entry(M,0,j); r1=entry(M,1,j)
            if r1<=r0: allj_ok+=1
            else:
                allj_bad+=1
                if len(cex_all)<6: cex_all.append((fmt(M),j,r0,r1))
            hp0=hasParent(M,0,j); hp1=hasParent(M,1,j)
            cls[(hp0,hp1)]=cls.get((hp0,hp1),0)+1
            if hp1:
                if hp0: a_ok+=1
                else:
                    a_bad+=1
                    if len(cex_a)<6: cex_a.append((fmt(M),j))
            if r1>0:
                if hp1: b_ok+=1
                else:
                    b_bad+=1
                    if len(cex_b)<6: cex_b.append((fmt(M),j,r1))
    pr(f"reduced-monoT hosts checked: {nred}")
    pr(f"[MAIN] all j: entry M 1 j <= entry M 0 j : ok={allj_ok} bad={allj_bad}")
    pr(f"[a] hasParent1 j => hasParent0 j : ok={a_ok} bad={a_bad}")
    pr(f"[b] entry1 j>0 => hasParent1 j : ok={b_ok} bad={b_bad}")
    pr(f"classify (hasP0,hasP1): {cls}")
    for x in cex_all: pr("  CEX-MAIN",x)
    for x in cex_a: pr("  CEX-a",x)
    for x in cex_b: pr("  CEX-b",x)
    pr(f"total t={time.time()-t0:.0f}s")

if __name__=='__main__': main()

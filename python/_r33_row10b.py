#!/usr/bin/env python3
# r33 VE34: FAST validation of ROW10 generalization + induction sub-claims.
# Uses memoized reach and a bounded oper-orbit, plus brute L=3..6.
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, diagSeq, Red, hasParent, fmt, oper,
                       nextrel0, nextrel1, le0)
def pr(*a): print(*a, flush=True)
def is_reduced(M): return Red(list(M))==list(M)

def check(M, acc):
    n=Lng(M)
    for j in range(n):
        r0=entry(M,0,j); r1=entry(M,1,j)
        if r1<=r0: acc['allj_ok']+=1
        else:
            acc['allj_bad']+=1
            if len(acc['cex_all'])<6: acc['cex_all'].append((fmt(M),j,r0,r1))
        hp0=hasParent(M,0,j); hp1=hasParent(M,1,j)
        if hp1:
            if hp0: acc['a_ok']+=1
            else:
                acc['a_bad']+=1
                if len(acc['cex_a'])<6: acc['cex_a'].append((fmt(M),j))
        if r1>0:
            if hp1: acc['b_ok']+=1
            else:
                acc['b_bad']+=1
                if len(acc['cex_b'])<6: acc['cex_b'].append((fmt(M),j,r1))
        # sub-claim (c): both parents => entry M 1 (p1) < entry M 1 (p0)+1 style?
        # record p0,p1 values when both exist to design induction
        if hp0 and hp1:
            from red_model import parent
            p0=parent(M,0,j); p1=parent(M,1,j)
            acc['both']+=1
            # is p1 == p0 ?
            if p1==p0: acc['p1eqp0']+=1
            # is le0 M p1 p0 (p1 an ancestor of p0)?  or p1 <= p0
            if p1<=p0: acc['p1lep0']+=1

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

def main():
    t0=time.time()
    acc=dict(allj_ok=0,allj_bad=0,a_ok=0,a_bad=0,b_ok=0,b_bad=0,both=0,p1eqp0=0,p1lep0=0,
             cex_all=[],cex_a=[],cex_b=[])
    # Part 1: brute L=3..6 over small grid (thorough shallow)
    nred=0
    for L in range(3,7):
        for tup in itertools.product([(a,b) for a in range(3) for b in range(3)],repeat=L-1):
            M=[(0,0)]+list(tup)
            if not (monoT(M) and is_reduced(M)): continue
            nred+=1; check(M,acc)
    pr(f"[brute L3-6] reduced-monoT={nred} t={time.time()-t0:.0f}s")
    # Part 2: deep oper-orbit
    hosts=gen(12,8,90)
    deep=[M for M in hosts if Lng(M)>=8 and monoT(M) and is_reduced(M)]
    pr(f"[oper deep>=8] hosts={len(hosts)} deep-reduced-monoT={len(deep)} maxLng={max((Lng(M) for M in hosts),default=0)}")
    for M in deep: check(M,acc)
    pr(f"[MAIN] all j: entry M 1 j <= entry M 0 j : ok={acc['allj_ok']} bad={acc['allj_bad']}")
    pr(f"[a] hasParent1 j => hasParent0 j : ok={acc['a_ok']} bad={acc['a_bad']}")
    pr(f"[b] entry1 j>0 => hasParent1 j : ok={acc['b_ok']} bad={acc['b_bad']}")
    pr(f"[c] both parents: {acc['both']}  p1==p0: {acc['p1eqp0']}  p1<=p0: {acc['p1lep0']}")
    for x in acc['cex_all']: pr("  CEX-MAIN",x)
    for x in acc['cex_a']: pr("  CEX-a",x)
    for x in acc['cex_b']: pr("  CEX-b",x)
    pr(f"total t={time.time()-t0:.0f}s")

if __name__=='__main__': main()

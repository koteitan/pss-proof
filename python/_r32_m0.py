#!/usr/bin/env python3
# M0RUN reduction: on m0-edge (adm M jm2) genuine condIII standard hosts verify
#  (a) entry M 1 jm2 < entry M 1 (jm2+1)
#  (b) entry M 0 jm2 < entry M 0 (jm2+1)
# Also test candidate ST_PS invariants:
#  (INV0) entry M 0 strictly increasing (all adjacent)
#  (INV1a) row-1 parent step: for jm2=parent(M,1,j1), left step nextR1(jm2-1,jm2)
#          fails in m0 case, right step holds.
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
def main():
    t0=time.time()
    maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 11
    vcap=int(sys.argv[2]) if len(sys.argv)>2 else 6
    budget=int(sys.argv[3]) if len(sys.argv)>3 else 400
    hosts=gen(maxlen,vcap,budget*0.5)
    pr(f"hosts={len(hosts)} t={time.time()-t0:.0f}s")
    # INV0 over ALL standard hosts
    inv0_ok=inv0_bad=0; inv0_ex=[]
    for M in hosts:
        good=all(entry(M,0,j)<entry(M,0,j+1) for j in range(Lng(M)-1))
        if good: inv0_ok+=1
        else:
            inv0_bad+=1
            if len(inv0_ex)<8: inv0_ex.append(fmt(M))
    m0=0; a_ok=a_bad=0; b_ok=b_bad=0; left_fail=left_hold=0
    ex_a=[]; ex_b=[]; ex_m=[]
    for M in hosts:
        if not genuineIII(M): continue
        jm2=s84_jm2(M); jm3=s84_jm3(M)
        if jm3<jm2: continue  # only m0-edge
        m0+=1
        ea=entry(M,1,jm2)<entry(M,1,jm2+1)
        eb=entry(M,0,jm2)<entry(M,0,jm2+1)
        if ea: a_ok+=1
        else:
            a_bad+=1
            if len(ex_a)<10: ex_a.append((fmt(M),jm2,entry(M,1,jm2),entry(M,1,jm2+1)))
        if eb: b_ok+=1
        else:
            b_bad+=1
            if len(ex_b)<10: ex_b.append((fmt(M),jm2,entry(M,0,jm2),entry(M,0,jm2+1)))
        # left step
        if jm2>=1 and nextR(M,1,jm2-1,jm2): left_hold+=1
        else: left_fail+=1
        if len(ex_m)<4: ex_m.append((fmt(M),jm2,jm3))
    pr("="*60)
    pr(f"[INV0] entry0 strictly increasing over ALL standard: ok={inv0_ok} bad={inv0_bad}")
    for e in inv0_ex: pr("  INV0 BAD:",e)
    pr(f"m0-edge genuine condIII hosts={m0}")
    pr(f"(a) e1 jm2<e1 jm2+1: ok={a_ok} bad={a_bad}")
    for e in ex_a: pr("  A BAD:",e)
    pr(f"(b) e0 jm2<e0 jm2+1: ok={b_ok} bad={b_bad}")
    for e in ex_b: pr("  B BAD:",e)
    pr(f"left step nextR1(jm2-1,jm2): hold={left_hold} fail={left_fail}")
    for e in ex_m: pr("  M0 sample:",e)
    pr(f"t={time.time()-t0:.0f}s")
if __name__=='__main__': main()

#!/usr/bin/env python3
# Confirm the proof routes for M0RUN (a),(b):
#  (b) e0 jm2 < e0 (jm2+1): via first nextrel0 edge of le0(jm2,j1)
#  (a) e1 jm2 < e1 (jm2+1): via le0(jm2+1,j1) + row1-valley + RedCondA
# Check le0(jm2+1,j1), and whether nextrel0(jm2,jm2+1) always holds, on m0 hosts.
# Also check for GUARD hosts (crx_run_of_guard covers them, but for a uniform
# route verify (a),(b) there too).
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, monoT, seg, parent, Adm, adm, nadm,
                       diagSeq, le0, leR, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax, Pred, nextR, nextrel1, nextrel0, oper)
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
    vcap=int(sys.argv[2]) if len(sys.argv)>2 else 7
    budget=int(sys.argv[3]) if len(sys.argv)>3 else 400
    hosts=gen(maxlen,vcap,budget*0.55)
    pr(f"hosts={len(hosts)} t={time.time()-t0:.0f}s")
    m0=0; guard=0
    le0jp_m0_ok=le0jp_m0_bad=0; nr0_m0_ok=nr0_m0_bad=0
    a_m0_ok=a_m0_bad=0; b_m0_ok=b_m0_bad=0
    # uniform check on GUARD hosts too
    le0jp_g_ok=le0jp_g_bad=0; a_g_ok=a_g_bad=0; b_g_ok=b_g_bad=0
    exb=[]; exa=[]
    for M in hosts:
        if time.time()-t0>budget: break
        if not genuineIII(M): continue
        jm2=s84_jm2(M); jm3=s84_jm3(M); j1=Lng(M)-1
        if jm2+1>=Lng(M): continue
        ea=entry(M,1,jm2)<entry(M,1,jm2+1)
        eb=entry(M,0,jm2)<entry(M,0,jm2+1)
        ljp=le0(M,jm2+1,j1)
        nr0=nextrel0(M,jm2,jm2+1)
        if jm3<jm2:
            guard+=1
            if ljp: le0jp_g_ok+=1
            else: le0jp_g_bad+=1
            if ea: a_g_ok+=1
            else: a_g_bad+=1
            if eb: b_g_ok+=1
            else: b_g_bad+=1
        else:
            m0+=1
            if ljp: le0jp_m0_ok+=1
            else:
                le0jp_m0_bad+=1
                if len(exa)<8: exa.append(('LE0JP',fmt(M),jm2,j1))
            if nr0: nr0_m0_ok+=1
            else: nr0_m0_bad+=1
            if ea: a_m0_ok+=1
            else:
                a_m0_bad+=1
                if len(exa)<8: exa.append(('A',fmt(M),jm2))
            if eb: b_m0_ok+=1
            else:
                b_m0_bad+=1
                if len(exb)<8: exb.append(('B',fmt(M),jm2))
    pr("="*60)
    pr(f"m0-edge hosts={m0}  guard hosts={guard}")
    pr(f"[m0] le0(jm2+1,j1) ok={le0jp_m0_ok} bad={le0jp_m0_bad}")
    pr(f"[m0] nextrel0(jm2,jm2+1) ok={nr0_m0_ok} bad={nr0_m0_bad}")
    pr(f"[m0] (a) ok={a_m0_ok} bad={a_m0_bad}   (b) ok={b_m0_ok} bad={b_m0_bad}")
    pr(f"[guard-uniform] le0(jm2+1,j1) ok={le0jp_g_ok} bad={le0jp_g_bad}")
    pr(f"[guard-uniform] (a) ok={a_g_ok} bad={a_g_bad}   (b) ok={b_g_ok} bad={b_g_bad}")
    for e in exa: pr("  exA:",e)
    for e in exb: pr("  exB:",e)
    pr(f"t={time.time()-t0:.0f}s")
if __name__=='__main__': main()

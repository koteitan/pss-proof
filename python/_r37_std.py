#!/usr/bin/env python3
# r37 ST_PS probe.  TWO parts:
#  (A) reduced+mono brute corpus: find WGAP-false hosts, check is_standard on them
#      (expect: all WGAP-false hosts are NON-standard => ST_PS is load-bearing).
#  (B) oper-orbit ST_PS corpus (standard by construction), DEEP (Lng up to 20):
#      check WGAP and j0<=TrMax on genuine condIII/IV.
import sys, time, itertools
sys.path.insert(0, 'python')
import red_model as R
from red_model import (Lng, entry, monoT, reduced, parent, adm, oper, diagSeq,
                       le0, nextrel0, nextrel1, Br, FirstNodes, Joints,
                       hasParent, fmt, TrMax, is_standard)

def pr(*a): print(*a, flush=True)
def condIIIorIV(M):
    j1=Lng(M)-1
    if not hasParent(M,0,j1): return False
    j0=parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,j0)>=entry(M,1,j1)

def hostcheck(M):
    """return (jm2,j0,tm) if genuine condIII/IV host else None"""
    L=Lng(M); j1=L-1
    if L<3 or not (1<j1): return None
    if not monoT(M) or not reduced(M): return None
    if not hasParent(M,1,j1) or not hasParent(M,0,j1): return None
    if not condIIIorIV(M): return None
    jm2=parent(M,1,j1); j0=parent(M,0,j1)
    if not (jm2<j0): return None
    return (jm2,j0,TrMax(M))

# ---------- PART A: brute, is_standard on WGAP-false ----------
def partA(Lmax,vmax):
    t0=time.time(); cells=[(a,b) for a in range(vmax) for b in range(vmax)]
    wf_std=0; wf_nonstd=0; wf_ex=[]; jt_std=0; jt_nonstd=0; jt_ex=[]
    hosts=0; std_hosts=0; std_wgap=0; std_jt=0
    for L in range(3,Lmax+1):
        if time.time()-t0>500: pr("[A budget]",L); break
        for tup in itertools.product(cells, repeat=L-1):
            if time.time()-t0>500: break
            M=[(0,0)]+list(tup)
            hc=hostcheck(M)
            if hc is None: continue
            jm2,j0,tm=hc; hosts+=1
            e0=[entry(M,0,j) for j in range(L)]
            wgap=e0[j0]==e0[jm2]+(j0-jm2)
            jt=j0<=tm
            std=is_standard(M)
            if std:
                std_hosts+=1
                if wgap: std_wgap+=1
                if jt: std_jt+=1
            if not wgap:
                if std: wf_std+=1;  (wf_ex.append((fmt(M),'STD',jm2,j0,e0)) if len(wf_ex)<8 else None)
                else:   wf_nonstd+=1
            if not jt:
                if std: jt_std+=1;  (jt_ex.append((fmt(M),'STD',jm2,j0,tm)) if len(jt_ex)<8 else None)
                else:   jt_nonstd+=1
    pr(f"[A] hosts={hosts} std_hosts={std_hosts} std_wgap={std_wgap} std_jt(j0<=TrMax)={std_jt}")
    pr(f"[A] WGAP-false: std={wf_std} nonstd={wf_nonstd}")
    for e in wf_ex: pr("   WGAPfalse-STD",e)
    pr(f"[A] j0>TrMax:  std={jt_std} nonstd={jt_nonstd}")
    for e in jt_ex: pr("   j0>TrMax-STD",e)

# ---------- PART B: oper-orbit deep ----------
def gen_STPS(maxlen, vcap, steps, cap):
    seen=set(); frontier=[]
    for u in range(vcap):
        for v in range(u,vcap):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M); frontier.append(list(M))
    allM=list(frontier)
    for _ in range(steps):
        nf=[]
        for M in frontier:
            for n in range(1,7):
                try: Mn=oper(M,n)
                except Exception: continue
                if 1<len(Mn)<=maxlen:
                    t=tuple(Mn)
                    if t not in seen and len(seen)<cap:
                        seen.add(t); nf.append(Mn); allM.append(Mn)
        frontier=nf
        if len(seen)>=cap: break
    return allM

def partB(maxlen,vcap,steps,cap):
    hosts=0; wgap=0; jt=0; jm2t=0; deep=0; ex=[]
    for M in gen_STPS(maxlen,vcap,steps,cap):
        hc=hostcheck(M)
        if hc is None: continue
        jm2,j0,tm=hc; hosts+=1
        if Lng(M)>=10: deep+=1
        e0=[entry(M,0,j) for j in range(Lng(M))]
        if e0[j0]==e0[jm2]+(j0-jm2): wgap+=1
        else: (ex.append(('WGAPf',fmt(M),jm2,j0)) if len(ex)<8 else None)
        if j0<=tm: jt+=1
        else: (ex.append(('j0>TrMax',fmt(M),jm2,j0,tm)) if len(ex)<8 else None)
        if jm2<=tm: jm2t+=1
    pr(f"[B oper-orbit] hosts={hosts} (deep>=10: {deep}) WGAP={wgap} j0<=TrMax={jt} jm2<=TrMax={jm2t}")
    for e in ex: pr("   ",e)

if __name__=='__main__':
    mode=sys.argv[1] if len(sys.argv)>1 else 'A'
    if mode=='A': partA(int(sys.argv[2]),int(sys.argv[3]))
    else: partB(int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5]))

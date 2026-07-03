#!/usr/bin/env python3
# r28-SHARP2: intrinsic chain candidate. For standard mono N (Lng>=2):
#   CAND-IDX : RAidx(N)!1 == least k>0 with adm N k
#   CAND-VAL : RA(N)!1 == entry N 1 (least k>0 with adm N k)
# where RAidx mirrors the RightAnces recursion returning column indices.
# Also test on genuine hosts that SHARP == CAND-VAL instance (Q-form).
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import (Lng, entry, monoT, zeroT, multiT, seg, adm, oper, diagSeq,
                       parent, Adm, Pred, fmt, P)
from trans_model import reduced, condV, condVI, Trans, Mark, bpHeadT, ZB

def condI(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    return entry(M,1,j1)==0 and adm(M,jp)
def condIII(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,jp)>=entry(M,1,j1) and adm(M,jp)

def RAidx(N,depth=0):
    # mirrors RightAnces; assumes N reduced (we only call on reduced)
    if depth>100: raise RuntimeError("deep")
    assert reduced(N), "RAidx on non-reduced"
    j1=Lng(N)-1
    if j1==0:
        return [] if N[0]==(0,0) else [0]
    if monoT(N):
        if zeroT(Pred(N)): return [0,j1]
        jp=parent(N,0,j1); jm1=Adm(N,jp)
        sg=seg(N,0,jm1)
        if zeroT(sg): a=[0]
        else: a=RAidx(sg,depth+1)   # indices in seg coords == N coords (prefix)
        if condI(N) or condIII(N) or condV(N) or condVI(N):
            tail=[j1]
        else:
            tail=[jp,j1]
        return a+tail
    else:
        Pl=P(N); J1=len(Pl)-1; PJ=Pl[J1]
        if PJ==[(0,0)]: return [0]
        # indices lost (component); return None marker
        return None

def RN(t):
    xs=t[1]
    return [] if not xs else [xs[-1][1]]+RN(xs[-1][2])

def gen(ml,mn,ms,cap):
    seen=set();fr=[];pool=[]
    for u in range(ms):
        for v in range(u,u+ms+4):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M);fr.append(list(M));pool.append(list(M))
    while fr and len(pool)<cap:
        nx=[]
        for M in fr:
            if Lng(M)<=1: continue
            for n in range(1,mn+1):
                N=oper(M,n)
                if Lng(N)>ml: continue
                t=tuple(N)
                if t not in seen: seen.add(t);nx.append(N);pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        fr=nx
    return pool

def leastadm(N):
    for k in range(1,Lng(N)):
        if adm(N,k): return k
    return None

def run(ml,cap,budget,mn):
    pool=gen(ml,mn,4,cap)
    print("pool",len(pool),"mn",mn,"maxLng",ml,flush=True)
    t0=time.time()
    tot=0; okidx=0; okval=0; fidx=[]; fval=[]; deep=0
    for M in pool:
        if time.time()-t0>budget:
            print("BUDGET HIT",flush=True); break
        if not monoT(M): continue
        if Lng(M)<2: continue
        if not reduced(M): continue   # ST_PS => reduced; pool is ST_PS so must hold
        tot+=1
        if Lng(M)>=9: deep+=1
        ks=RAidx(M)
        la=leastadm(M)
        if ks is None or len(ks)<2 or la is None:
            fidx.append((fmt(M),'shape',ks,la)); fval.append((fmt(M),'shape',ks,la)); continue
        if ks[1]==la: okidx+=1
        else: fidx.append((fmt(M),ks,la))
        if entry(M,1,ks[1])==entry(M,1,la): okval+=1
        else: fval.append((fmt(M),ks,la,entry(M,1,ks[1]),entry(M,1,la)))
    print(f"standard mono N tested={tot} deep={deep}")
    print(f"  CAND-IDX ks!1==leastadm : {okidx}/{tot} fails={len(fidx)}")
    for f in fidx[:8]: print("     IDXCEX",f)
    print(f"  CAND-VAL entry(ks!1)==entry(leastadm): {okval}/{tot} fails={len(fval)}")
    for f in fval[:8]: print("     VALCEX",f)

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 13,
        int(sys.argv[2]) if len(sys.argv)>2 else 30000,
        int(sys.argv[3]) if len(sys.argv)>3 else 420,
        int(sys.argv[4]) if len(sys.argv)>4 else 9)

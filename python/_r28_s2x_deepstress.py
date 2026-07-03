#!/usr/bin/env python3
# r28-SHARP2 deep stress: atomA/atomB/SHARP on a bigger, deeper ST pool.
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import (Lng, entry, monoT, seg, adm, oper, diagSeq, parent, Adm,
                       Pred, fmt, hasParent)
from trans_model import reduced, condV, Trans, Mark, bpHeadT, ZB

def RN(t):
    xs=t[1]
    return [] if not xs else [xs[-1][1]]+RN(xs[-1][2])

def gen(ml,mn,ms,cap,budget):
    t0=time.time()
    seen=set();fr=[];pool=[]
    for u in range(ms):
        for v in range(u,u+ms+5):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M);fr.append(list(M));pool.append(list(M))
    while fr and len(pool)<cap and time.time()-t0<budget:
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

def run(ml,cap,budget,mn):
    pool=gen(ml,mn,5,cap,budget*0.4)
    print("pool",len(pool),flush=True)
    t0=time.time(); tot=0; deep=0
    failA=[];failB=[];failS=[]
    for M in pool:
        if time.time()-t0>budget:
            print("BUDGET HIT at",tot,flush=True); break
        if not (reduced(M) and monoT(M)): continue
        if Lng(M)<3: continue
        j1=Lng(M)-1
        if not hasParent(M,0,j1): continue
        jp=parent(M,0,j1)
        if not condV(M): continue
        if adm(M,jp): continue
        if Trans(Pred(M))==ZB: continue
        jm1=Adm(M,jp)
        c1=Mark(Pred(M),jm1)
        if bpHeadT(c1)==ZB: continue
        tot+=1
        if Lng(M)>=10: deep+=1
        if not adm(M,jp+1): failA.append(fmt(M))
        for c in range(jp+1,Lng(M)):
            if not hasParent(M,0,c): continue
            pj=parent(M,0,c)
            if jm1<=pj<=jp and not (pj==jp and entry(M,1,c)==entry(M,1,jp)+1):
                failB.append((fmt(M),c,pj))
        rn=RN(c1)
        if not (len(rn)>=2 and rn[1]==entry(M,1,jp+1)): failS.append(fmt(M))
    print(f"tot={tot} deep(Lng>=10)={deep}")
    print(f"atomA fails={len(failA)} atomB fails={len(failB)} SHARP fails={len(failS)}")
    for f in failA[:4]: print("  A",f)
    for f in failB[:4]: print("  B",f)
    for f in failS[:4]: print("  S",f)

if __name__=='__main__':
    run(14,60000,1200,12)

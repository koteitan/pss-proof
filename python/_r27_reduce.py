#!/usr/bin/env python3
# r27: test the TWO reductions of SHARP on ST_PS genuine hosts (deep, broad):
#  (A) RightNodes(transC1 M)!1 == entry M 1 (Lng M - 2)   [structural: a1 length 1]
#  (B) entry M 1 (Lng M - 2)   == entry M 1 (transJ0 M + 1) [row-1 arithmetic]
#  Also flag RN(c1) length != 2 and slice/Pred chain anomalies.
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import Lng, entry, monoT, seg, adm, oper, diagSeq, parent, Adm, Pred, fmt
from trans_model import reduced, condV, Trans, Mark, bpHeadT, ZB

def RN(t):
    xs=t[1]
    return [] if not xs else [xs[-1][1]]+RN(xs[-1][2])

def gen(ml,mn,ms,cap,tbudget):
    seen=set();fr=[];pool=[]
    for u in range(ms):
        for v in range(u,u+ms+4):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M);fr.append(list(M));pool.append(list(M))
    t0=time.time()
    while fr and len(pool)<cap and time.time()-t0<tbudget:
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

def run(ml,cap,budget,mn,ms):
    pool=gen(ml,mn,ms,cap,budget*0.5)
    print("pool",len(pool),"ml",ml,"mn",mn,"ms",ms,flush=True)
    t0=time.time(); tot=0; A=0; B=0; badA=[]; badB=[]; lens={}
    for M in pool:
        if time.time()-t0>budget: break
        if not (reduced(M) and monoT(M)): continue
        if Lng(M)<3: continue
        j1=Lng(M)-1; jp=parent(M,0,j1)
        if jp is None: continue
        if not condV(M): continue
        if adm(M,jp): continue
        if Trans(Pred(M))==ZB: continue
        jm1=Adm(M,jp)
        c1=Mark(Pred(M),jm1)
        if bpHeadT(c1)==ZB: continue
        rn=RN(c1)
        if len(rn)<2: continue
        tot+=1
        lens[len(rn)]=lens.get(len(rn),0)+1
        rn1=rn[1]
        eLm2=entry(M,1,Lng(M)-2); ej0p1=entry(M,1,jp+1)
        if rn1==eLm2: A+=1
        else: badA.append((fmt(M),rn1,eLm2))
        if eLm2==ej0p1: B+=1
        else: badB.append((fmt(M),eLm2,ej0p1,jp,jm1))
    print(f"tot={tot}")
    print(f"  (A) RN(c1)[1]==entry M 1 (Lng-2): {A}/{tot} badA={len(badA)}")
    for b in badA[:6]: print("     A-CEX",b)
    print(f"  (B) entry M 1 (Lng-2)==entry M 1 (j0+1): {B}/{tot} badB={len(badB)}")
    for b in badB[:6]: print("     B-CEX",b)
    print("  RN(c1) length dist:",dict(sorted(lens.items())))

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 13,
        int(sys.argv[2]) if len(sys.argv)>2 else 20000,
        int(sys.argv[3]) if len(sys.argv)>3 else 220,
        int(sys.argv[4]) if len(sys.argv)>4 else 14,
        int(sys.argv[5]) if len(sys.argv)>5 else 6)

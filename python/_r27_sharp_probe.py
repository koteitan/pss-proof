#!/usr/bin/env python3
# r27-SHARP structural probe: for genuine ST_PS non-adm condV hosts, dissect the
# terminal slice S = seg M (transJm1 M) (Lng M-2), its Trans, the RightNodes chain,
# and locate index 1 geometrically.
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import Lng, entry, monoT, seg, adm, oper, diagSeq, parent, Adm, Pred, fmt
from trans_model import reduced, condV, Trans, Mark, bpHeadT, ZB

def transJ1(M): return Lng(M)-1
def RN(t):
    xs=t[1]
    return [] if not xs else [xs[-1][1]]+RN(xs[-1][2])

def gen(ml,mn,ms,cap):
    seen=set();fr=[];pool=[]
    for u in range(ms):
        for v in range(u,u+ms+3):
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

def probe(ml,cap,budget):
    pool=gen(ml,6,3,cap)
    print("pool",len(pool),flush=True)
    t0=time.time(); n=0
    for M in pool:
        if time.time()-t0>budget: break
        if not (reduced(M) and monoT(M)): continue
        if Lng(M)<3: continue
        j1=transJ1(M); jp=parent(M,0,j1)
        if jp is None: continue
        if not condV(M): continue
        if adm(M,jp): continue
        if Trans(Pred(M))==ZB: continue
        jm1=Adm(M,jp)
        c1=Mark(Pred(M),jm1)
        if bpHeadT(c1)==ZB: continue
        rn=RN(c1)
        if len(rn)<2: continue
        # slice
        S=seg(M,jm1,Lng(M)-2)
        TS=Trans(S)
        rnS=RN(TS)
        # chain indices ks of S: RightAnces S = map (entry S 1) ks; reconstruct via
        # matching Trans structure -- but simplest: entry S 1 j for j in 0..Lng S-1.
        entS=[entry(S,1,j) for j in range(Lng(S))]
        n+=1
        if n<=25:
            print(f"M={fmt(M)} L={Lng(M)} jm1={jm1} j0={jp} j1={j1}")
            print(f"   S={fmt(S)} LngS={Lng(S)}")
            print(f"   RN(c1)={rn[:6]}  rn1={rn[1]}  entry M 1 (j0+1)={entry(M,1,jp+1)}")
            print(f"   entS(row1 of S)={entS}")
            # in M-coords: RN(c1)[1] should equal entry M 1 (jm1 + ks1). find candidate ks1
            cand=[k for k in range(Lng(S)) if entS[k]==rn[1]]
            print(f"   ks1 candidates (S-col where entS==rn1)={cand}  -> M-col={[jm1+k for k in cand]}  target M-col={jp+1}")
        if n>=25: break
    print("shown",n)

if __name__=='__main__':
    probe(int(sys.argv[1]) if len(sys.argv)>1 else 11,
          int(sys.argv[2]) if len(sys.argv)>2 else 4000,
          int(sys.argv[3]) if len(sys.argv)>3 else 120)

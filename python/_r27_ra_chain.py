#!/usr/bin/env python3
# r27: compute the RightAnces INDEX chain ks of the terminal slice S and identify
# ks!1 intrinsically. Faithful to pss_paper RightAnces recursion (indices version).
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import Lng, entry, monoT, seg, adm, oper, diagSeq, parent, Adm, Pred, fmt, zeroT, Red
from trans_model import reduced, condV, condI, condIII, condVI, Trans, Mark, bpHeadT, ZB

def transJ1(M): return Lng(M)-1

def RAidx(M):
    # returns index chain ks with RightAnces M = map (entry M 1) ks (M-relative)
    if not reduced(M):
        return RAidx(Red(M))
    j1 = Lng(M)-1
    if j1==0:
        return [] if M[0]==(0,0) else [0]
    if monoT(M):
        if zeroT(Pred(M)): return [0, j1]
        jp = parent(M,0,j1); jm1 = Adm(M,jp)
        pre = seg(M,0,jm1)
        a = [0] if zeroT(pre) else RAidx(pre)
        if condI(M) or condIII(M) or condV(M) or condVI(M):
            return a + [j1]
        else:
            return a + [jp, j1]
    # multi
    from red_model import P
    comps=P(M); J1=len(comps)-1; PJ=comps[J1]; j0=j1-Lng(PJ)+1
    if PJ==[(0,0)]: return [0]
    # RAidx(PJ) is PJ-relative; shift by j0
    return [j0+k for k in RAidx(PJ)]

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

def run(ml,cap,budget,mn):
    pool=gen(ml,mn,4,cap)
    print("pool",len(pool),flush=True)
    t0=time.time(); tot=0
    rel={}  # relation of ks1 to slice-internal landmarks
    ok_val=0; ok_ks1eq2=0
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
        S=seg(M,jm1,Lng(M)-2)
        if not (reduced(S) and monoT(S)):
            print("SLICE NOT RT/mono!", fmt(M), fmt(S)); continue
        ks=RAidx(S)
        if len(ks)<2:
            print("ks<2!", fmt(M), ks); continue
        tot+=1
        ks1=ks[1]
        # slice-internal landmarks
        LS=Lng(S)
        jpS=parent(S,0,LS-1); jm1S=Adm(S,jpS)
        # M-col of j0+1 in S-coords:
        target_scol=(jp+1)-jm1
        if ks1==target_scol: ok_ks1eq2+=1
        if entry(S,1,ks1)==entry(S,1,target_scol): ok_val+=1
        key=(ks1, target_scol, jpS, jm1S, LS-1, ks1==jpS, ks1==jpS+1, ks1==jm1S+1)
        # summarise: express ks1 relative to jpS, jm1S
        rlbl=[]
        if ks1==jpS: rlbl.append("ks1=jpS")
        if ks1==jpS+1: rlbl.append("ks1=jpS+1")
        if ks1==jm1S+1: rlbl.append("ks1=jm1S+1")
        if ks1==target_scol: rlbl.append("ks1=target")
        if ks1==2: rlbl.append("ks1=2")
        lbl=tuple(sorted(rlbl))
        rel[lbl]=rel.get(lbl,0)+1
        if tot<=12:
            print(f"M={fmt(M)} jm1={jm1} j0={jp} | S={fmt(S)} ks={ks} ks1={ks1} target_scol={target_scol} jpS={jpS} jm1S={jm1S}")
    print(f"tot={tot} ks1==target(index)={ok_ks1eq2} val-match={ok_val}")
    print("relation labels:", rel)

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 12,
        int(sys.argv[2]) if len(sys.argv)>2 else 6000,
        int(sys.argv[3]) if len(sys.argv)>3 else 180,
        int(sys.argv[4]) if len(sys.argv)>4 else 12)

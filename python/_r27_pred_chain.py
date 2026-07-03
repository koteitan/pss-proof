#!/usr/bin/env python3
# r27: Pred M is reduced mono. RightAnces(Pred M) = map (entry (Pred M) 1) ps.
# The marked column jm1 sits in ps; the element AFTER it is a1!0 = SHARP target.
# Identify ps[pos(jm1)+1] intrinsically and check == entry M 1 (j0+1) value.
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import Lng, entry, monoT, seg, adm, oper, diagSeq, parent, Adm, Pred, fmt, zeroT, Red, P
from trans_model import reduced, condV, condI, condIII, condVI, Trans, Mark, bpHeadT, ZB

def transJ1(M): return Lng(M)-1

def RAidx(M):
    if not reduced(M):
        return None  # only call on reduced
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
    comps=P(M); J1=len(comps)-1; PJ=comps[J1]; j0=j1-Lng(PJ)+1
    if PJ==[(0,0)]: return [0]
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
    okval=0; rel={}
    for M in pool:
        if time.time()-t0>budget: break
        if not (reduced(M) and monoT(M)): continue
        if Lng(M)<3: continue
        j1=transJ1(M); jp=parent(M,0,j1)
        if jp is None: continue
        if not condV(M): continue
        if adm(M,jp): continue
        jm1=Adm(M,jp)
        c1=Mark(Pred(M),jm1)
        if bpHeadT(c1)==ZB: continue
        PM=Pred(M)
        if not reduced(PM):
            print("PredM not reduced!", fmt(M)); continue
        ps=RAidx(PM)
        if jm1 not in ps:
            print("jm1 NOT in Pred chain!", fmt(M), "jm1",jm1,"ps",ps); continue
        pos=ps.index(jm1)
        if pos+1>=len(ps):
            print("jm1 is LAST in Pred chain!", fmt(M), "jm1",jm1,"ps",ps); continue
        nxt=ps[pos+1]
        tot+=1
        val_nxt=entry(PM,1,nxt); target=entry(M,1,jp+1)
        if val_nxt==target: okval+=1
        # relation of nxt to landmarks
        lbl=[]
        if nxt==jp+1: lbl.append("nxt=j0+1")
        if nxt==jp: lbl.append("nxt=j0")
        if nxt==jm1+1: lbl.append("nxt=jm1+1")
        if nxt==jm1+2: lbl.append("nxt=jm1+2")
        rel[tuple(sorted(lbl))]=rel.get(tuple(sorted(lbl)),0)+1
        if tot<=14:
            print(f"M={fmt(M)} jm1={jm1} j0={jp} j1={j1} | PredM chain ps={ps} pos={pos} nxt={nxt} val={val_nxt} target={target}")
    print(f"tot={tot} val-match={okval}")
    print("nxt relation labels:", rel)

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 12,
        int(sys.argv[2]) if len(sys.argv)>2 else 6000,
        int(sys.argv[3]) if len(sys.argv)>3 else 180,
        int(sys.argv[4]) if len(sys.argv)>4 else 12)

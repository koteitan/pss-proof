#!/usr/bin/env python3
# r26-LPH2 deep validation of the REMAINING residual SHARP on ST_PS (oper-closure):
#   SHARP : RightNodes(transC1 M)[1] == entry M 1 (transJ0 M + 1)
# plus confirm the RT_PS\ST_PS refutation of R0. ST_PS = oper closure only.
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import Lng, entry, monoT, seg, adm, oper, diagSeq, parent, Adm, Pred
from trans_model import reduced, condV, Trans, Mark, bpHeadT, ZB

def transJ1(M): return Lng(M)-1
def transJ0(M): return parent(M,0,transJ1(M))
def transJm1(M): return Adm(M, transJ0(M))
def RN(t):
    xs=t[1]
    return [] if not xs else [xs[-1][1]]+RN(xs[-1][2])

def gen(ml,mn,ms,cap):
    seen=set();fr=[]
    for u in range(ms):
        for v in range(u,u+ms+3):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M);fr.append(list(M))
    pool=list(fr)
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

def run(ml,cap,budget):
    pool=gen(ml,6,3,cap)
    print("pool",len(pool),"ml",ml,flush=True)
    t0=time.time(); tot=0; sharp=0; bad=[]
    bylen={}
    for M in pool:
        if time.time()-t0>budget: break
        if not (reduced(M) and monoT(M)): continue
        if Lng(M)<3: continue
        j1=transJ1(M); jp=parent(M,0,j1)
        if jp is None: continue
        if not condV(M): continue
        if adm(M,jp): continue
        if Trans(Pred(M))==ZB: continue
        c1=Mark(Pred(M),Adm(M,jp))
        if bpHeadT(c1)==ZB: continue
        rn=RN(c1)
        if len(rn)<2: continue
        tot+=1
        L=Lng(M); bylen.setdefault(L,[0,0])
        bylen[L][1]+=1
        lhs=rn[1]; rhs=entry(M,1,jp+1)
        if lhs==rhs: sharp+=1; bylen[L][0]+=1
        else: bad.append((M,lhs,rhs))
    print(f"ST_PS genuine hosts tot={tot}")
    print(f"  SHARP RN(c1)[1]==entry M 1 (j0+1): {sharp}/{tot}  bad={len(bad)}")
    for b in bad[:6]:
        from red_model import fmt
        print("   SHARP CEX", fmt(b[0]), b[1], b[2])
    print("  by Lng (ok/tot):", {k:tuple(v) for k,v in sorted(bylen.items())})

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 11,
        int(sys.argv[2]) if len(sys.argv)>2 else 5000,
        int(sys.argv[3]) if len(sys.argv)>3 else 200)

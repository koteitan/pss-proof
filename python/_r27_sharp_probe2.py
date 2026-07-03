#!/usr/bin/env python3
# r27-SHARP diversity probe: enumerate ST_PS genuine hosts, report RN(c1) chain
# length distribution + whether entry M 1 jm1 == 0 always, and any SHARP failure.
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

def run(ml,cap,budget,mn):
    pool=gen(ml,mn,4,cap)
    print("pool",len(pool),"mn",mn,flush=True)
    t0=time.time(); tot=0; sharp=0; bad=[]
    rnlen={}; jm1zero=0; jm1nz=[]
    shapes={}
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
        tot+=1
        rnlen[len(rn)]=rnlen.get(len(rn),0)+1
        if entry(M,1,jm1)==0: jm1zero+=1
        else: jm1nz.append((fmt(M),entry(M,1,jm1)))
        lhs=rn[1]; rhs=entry(M,1,jp+1)
        if lhs==rhs: sharp+=1
        else: bad.append((fmt(M),rn,lhs,rhs,jm1,jp,j1))
        # shape signature: row1 differences of the slice
        S=seg(M,jm1,Lng(M)-2)
        sig=tuple(entry(S,1,j) for j in range(Lng(S)))
        shapes[sig]=shapes.get(sig,0)+1
    print(f"tot={tot} sharp={sharp} bad={len(bad)}")
    print(f"  RN(c1) length dist: {dict(sorted(rnlen.items()))}")
    print(f"  entry M 1 jm1 == 0 : {jm1zero}/{tot}  nonzero examples={jm1nz[:5]}")
    for b in bad[:8]: print("  SHARP CEX", b)
    print(f"  #distinct slice row1 shapes={len(shapes)}")
    for sig,c in sorted(shapes.items(), key=lambda x:-x[1])[:12]:
        print("    shape", sig, "x", c)

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 12,
        int(sys.argv[2]) if len(sys.argv)>2 else 6000,
        int(sys.argv[3]) if len(sys.argv)>3 else 180,
        int(sys.argv[4]) if len(sys.argv)>4 else 10)

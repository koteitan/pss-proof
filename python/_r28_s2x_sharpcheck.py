#!/usr/bin/env python3
# r28-SHARP2 CRITICAL: on the BIG deep corpus, test the r27 atoms len2/redB AND the
# underlying SHARP itself (RightNodes(transC1 M)!1 == entry M 1 (j0+1)) on every
# genuine ST_PS host. If len2/redB fail but SHARP holds, the r27 atomization is
# too strong and must be re-cut.
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import Lng, entry, monoT, seg, adm, oper, diagSeq, parent, Adm, Pred, fmt
from trans_model import reduced, condV, Trans, Mark, bpHeadT, ZB

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

def run(ml,cap,budget,mn):
    pool=gen(ml,mn,4,cap)
    print("pool",len(pool),"mn",mn,"maxLng",ml,flush=True)
    t0=time.time(); tot=0; deep=0
    cnt={'len2':0,'redB':0,'sharp':0,'lastEq':0}
    fails={k:[] for k in cnt}
    for M in pool:
        if time.time()-t0>budget:
            print("BUDGET HIT",flush=True); break
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
        tot+=1; L=Lng(M)
        if L>=9: deep+=1
        rn=RN(c1)
        def chk(k,b,info):
            if b: cnt[k]+=1
            else: fails[k].append((fmt(M),info))
        chk('len2', len(rn)==2, rn)
        chk('redB', entry(M,1,L-2)==entry(M,1,jp+1), (entry(M,1,L-2),entry(M,1,jp+1),jp))
        chk('sharp', len(rn)>=2 and rn[1]==entry(M,1,jp+1), (rn,entry(M,1,jp+1),jm1,jp))
        chk('lastEq', len(rn)>=2 and rn[-1]==entry(M,1,L-2), (rn,entry(M,1,L-2)))
    print(f"tot={tot} deep={deep}")
    for k in cnt:
        print(f"  {k}: {cnt[k]}/{tot} fails={len(fails[k])}")
        for f in fails[k][:6]: print("     CEX",f)

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 13,
        int(sys.argv[2]) if len(sys.argv)>2 else 30000,
        int(sys.argv[3]) if len(sys.argv)>3 else 420,
        int(sys.argv[4]) if len(sys.argv)>4 else 9)

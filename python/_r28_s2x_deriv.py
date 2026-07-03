#!/usr/bin/env python3
# r28-SHARP2: (1) validate tail-const characterization on a BIG deep corpus;
# (2) trace oper-derivations of genuine hosts (which (M',n) steps make them).
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import Lng, entry, monoT, seg, adm, oper, diagSeq, parent, Adm, Pred, fmt
from trans_model import reduced, condV, Trans, Mark, bpHeadT, ZB

def gen(ml,mn,ms,cap):
    seen={};fr=[];pool=[]
    for u in range(ms):
        for v in range(u,u+ms+4):
            M=tuple(diagSeq(u,v))
            if M not in seen:
                seen[M]=('diag',None,None);fr.append(list(M));pool.append(list(M))
    while fr and len(pool)<cap:
        nx=[]
        for M in fr:
            if Lng(M)<=1: continue
            for n in range(1,mn+1):
                N=oper(M,n)
                if Lng(N)>ml: continue
                t=tuple(N)
                if t not in seen:
                    seen[t]=('oper',tuple(M),n);nx.append(N);pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        fr=nx
    return pool,seen

def genuine(M):
    if not (reduced(M) and monoT(M)): return None
    if Lng(M)<3: return None
    j1=Lng(M)-1; jp=parent(M,0,j1)
    if jp is None: return None
    if not condV(M): return None
    if adm(M,jp): return None
    if Trans(Pred(M))==ZB: return None
    jm1=Adm(M,jp)
    c1=Mark(Pred(M),jm1)
    if bpHeadT(c1)==ZB: return None
    return (jm1,jp,j1)

def run(ml,cap,budget,mn):
    pool,seen=gen(ml,mn,4,cap)
    print("pool",len(pool),"mn",mn,"maxLng",ml,flush=True)
    t0=time.time(); tot=0; tc_ok=0; tc_fail=[]
    e1jm1z=0; e1jm1nz=[]
    derivs={}
    deep=0
    for M in pool:
        if time.time()-t0>budget:
            print("BUDGET HIT",flush=True); break
        g=genuine(M)
        if g is None: continue
        jm1,jp,j1=g; L=Lng(M); tot+=1
        if L>=9: deep+=1
        # tail const: M!j == M!(jp+1) for jp+1<=j<=L-1
        ok=all(M[j]==M[jp+1] for j in range(jp+1,L))
        if ok: tc_ok+=1
        else: tc_fail.append((fmt(M),jp))
        if entry(M,1,jm1)==0: e1jm1z+=1
        else: e1jm1nz.append((fmt(M),entry(M,1,jm1)))
        # derivation: how was M produced?
        d=seen[tuple(M)]
        if d[0]=='oper':
            Mp=d[1]; n=d[2]
            gp=genuine(list(Mp))
            key=('pred' if n==1 else 'copy', 'parent-genuine' if gp else 'parent-not-genuine')
            derivs[key]=derivs.get(key,0)+1
        else:
            derivs[('diag',)]=derivs.get(('diag',),0)+1
    print(f"tot={tot} deep(Lng>=9)={deep}")
    print(f"tail_const: {tc_ok}/{tot} fails={len(tc_fail)}")
    for f in tc_fail[:6]: print("  TC CEX",f)
    print(f"entry M 1 jm1 == 0: {e1jm1z}/{tot} nz={e1jm1nz[:6]}")
    print("derivation kinds:",derivs)

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 13,
        int(sys.argv[2]) if len(sys.argv)>2 else 30000,
        int(sys.argv[3]) if len(sys.argv)>3 else 420,
        int(sys.argv[4]) if len(sys.argv)>4 else 9)

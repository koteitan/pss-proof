#!/usr/bin/env python3
# Decompose WRAP into W1 (single-principal, head e1 r) and W2 (body transfer).
# Also check reducedness of seg H r c and seg H (r-1) c in the WRAP domain.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, leR, adm, oper, diagSeq)
import red_model as rm
from trans_model import Trans, bpHeadT, bpHeadV, Dpt, PB

def gen_pool(maxlen, maxn, maxseed, cap):
    seen=set(); frontier=[]
    for u in range(maxseed):
        for v in range(u,u+maxseed+2):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M); frontier.append(list(M))
    pool=list(frontier)
    while frontier and len(pool)<cap:
        nxt=[]
        for M in frontier:
            if Lng(M)<=1: continue
            for n in range(1,maxn+1):
                N=oper(M,n)
                if Lng(N)>maxlen: continue
                t=tuple(N)
                if t not in seen: seen.add(t); nxt.append(N); pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        frontier=nxt
    return pool

def Ts(M):
    try: return Trans(M)
    except Exception: return None

def probe(hosts, budget=280):
    w1_ok=w1_bad=0; w2_ok=w2_bad=0
    segr_red=segr_notred=0; segr1_red=segr1_notred=0
    ex1=[]; ex2=[]
    t0=time.time()
    for H in hosts:
        if time.time()-t0>budget: break
        if not (reduced(H) and monoT(H)): continue
        n=Lng(H)
        for r in range(1,n-1):
            if adm(H,r): continue
            for c in range(r+1,n):
                sr=seg(H,r,c); sr1=seg(H,r-1,c)
                if reduced(sr): segr_red+=1
                else: segr_notred+=1
                if reduced(sr1): segr1_red+=1
                else: segr1_notred+=1
                Tr=Ts(sr); Tr1=Ts(sr1)
                if Tr is None or Tr1 is None: continue
                # W1: Tr == Dpt(e1 r)(bpHeadT Tr)  AND len PB ==1
                w1 = (Tr==Dpt(entry(H,1,r),bpHeadT(Tr)))
                if w1: w1_ok+=1
                else:
                    w1_bad+=1
                    if len(ex1)<5: ex1.append((rm.fmt(H),r,c,len(PB(Tr)),bpHeadV(Tr),entry(H,1,r),Tr))
                # W2: bpHeadT Tr == bpHeadT Tr1
                if bpHeadT(Tr)==bpHeadT(Tr1): w2_ok+=1
                else:
                    w2_bad+=1
                    if len(ex2)<5: ex2.append((rm.fmt(H),r,c))
    print(f"W1 (single-principal, head e1 r): ok={w1_ok} bad={w1_bad}")
    print(f"W2 (body transfer bpHeadT):       ok={w2_ok} bad={w2_bad}")
    print(f"seg H r c reduced:  yes={segr_red} no={segr_notred}")
    print(f"seg H (r-1) c red:  yes={segr1_red} no={segr1_notred}")
    for e in ex1: print("  W1 BAD",e)
    for e in ex2: print("  W2 BAD",e)

if __name__=='__main__':
    pool=gen_pool(11,4,4,4000)
    print("pool",len(pool))
    probe(pool)

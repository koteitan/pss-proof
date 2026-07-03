#!/usr/bin/env python3
# Broad WRAP test over reduced monoT H, general r (nonadm), general c, bucket by leR H 0 r c.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, leR, adm, oper, diagSeq)
import red_model as rm
from trans_model import Trans, bpHeadT, Dpt

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
    ok_leR=bad_leR=ok_noleR=bad_noleR=0
    ex=[]
    t0=time.time()
    for H in hosts:
        if time.time()-t0>budget: break
        if not (reduced(H) and monoT(H)): continue
        n=Lng(H)
        for r in range(1,n-1):
            if adm(H,r): continue
            for c in range(r+1,n):
                Tr=Ts(seg(H,r,c)); Tr1=Ts(seg(H,r-1,c))
                if Tr is None or Tr1 is None: continue
                want=Dpt(entry(H,1,r), bpHeadT(Tr1))
                good=(Tr==want)
                if leR(H,0,r,c):
                    if good: ok_leR+=1
                    else: bad_leR+=1
                else:
                    if good: ok_noleR+=1
                    else:
                        bad_noleR+=1
                        if len(ex)<8: ex.append((rm.fmt(H),r,c,Tr,want))
    print(f"WRAP broad: leR[ok={ok_leR} bad={bad_leR}]  NOleR[ok={ok_noleR} bad={bad_noleR}]")
    for e in ex: print("  noleR-BAD",e)

if __name__=='__main__':
    pool=gen_pool(11,4,4,4000)
    print("pool",len(pool))
    probe(pool)

#!/usr/bin/env python3
# For sr=seg H r c in WRAP domain: probe internal Trans-branch structure of sr.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, leR, adm, oper, diagSeq,
                       parent, Adm, Pred)
import red_model as rm
from trans_model import Trans, bpHeadT, bpHeadV, Dpt, PB, ZB

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
    tot=0; t1zero=0; admjm1zero=0; monoTsr=0
    jp_nonadm_in_sr=0  # is column 0 (=parent chain) ...
    t1zero_or_admzero=0
    e1r_is_transV=0
    t0=time.time()
    for H in hosts:
        if time.time()-t0>budget: break
        if not (reduced(H) and monoT(H)): continue
        n=Lng(H)
        for r in range(1,n-1):
            if adm(H,r): continue
            for c in range(r+1,n):
                sr=seg(H,r,c)
                if not reduced(sr): continue
                tot+=1
                if monoT(sr): monoTsr+=1
                # transT1 sr = Trans(Pred sr)
                Tpred=Ts(Pred(sr))
                t1z = (Tpred==ZB)
                if t1z: t1zero+=1
                # transJm1 sr = Adm sr (parent sr 0 (Lng sr -1))
                Lsr=Lng(sr)
                jp = parent(sr,0,Lsr-1)
                admjm1 = Adm(sr, jp)
                if admjm1==0: admjm1zero+=1
                if t1z or admjm1==0: t1zero_or_admzero+=1
    print(f"tot={tot} monoT(sr)={monoTsr}")
    print(f"  t1=Trans(Pred sr)=0 : {t1zero}")
    print(f"  Adm sr (parent sr 0 last)=0 : {admjm1zero}")
    print(f"  t1=0 OR Adm..=0 : {t1zero_or_admzero}  (== tot? {t1zero_or_admzero==tot})")

if __name__=='__main__':
    pool=gen_pool(11,4,4,4000)
    print("pool",len(pool))
    probe(pool)

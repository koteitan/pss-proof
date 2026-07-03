#!/usr/bin/env python3
# HYP-A: for reduced monoT M, does bpHeadT(Trans(seg M p (Lng M-1))) == bpHeadT(Mark M p)
# for ALL p (adm AND non-adm) with leR M 0 p (Lng M-1)?  If yes, Mark_nadm_const closes W2.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, leR, Adm, adm, oper, diagSeq)
import red_model as rm
from trans_model import Trans, Mark, bpHeadT

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

def T(M):
    try: return Trans(M)
    except Exception: return None
def Mk(M,m):
    try: return Mark(M,m)
    except Exception: return None

def probe(hosts,budget=120):
    hypA_ok=hypA_bad=0          # bpHeadT(Trans(seg M p end))==bpHeadT(Mark M p)
    full_ok=full_bad=0          # Trans(seg M p end)==Mark M p  (expect only adm)
    hypA_adm_bad=hypA_nadm_bad=0
    w2L_ok=w2L_bad=0            # nadm M p: bpHeadT(Trans seg p)==bpHeadT(Trans seg p+1)
    w2R_ok=w2R_bad=0            # nadm M (p+1): same
    ex=[]
    t0=time.time()
    for M in hosts:
        if time.time()-t0>budget: break
        if not (reduced(M) and monoT(M)): continue
        n=Lng(M)
        if n<3: continue
        j1=n-1
        # precompute slice bodies
        body={}
        for p in range(0,j1):
            if not leR(M,0,p,j1): continue
            tp=T(seg(M,p,j1))
            if tp is None: continue
            body[p]=bpHeadT(tp)
            mk=Mk(M,p)
            if mk is None: continue
            # HYP-A
            if bpHeadT(tp)==bpHeadT(mk): hypA_ok+=1
            else:
                hypA_bad+=1
                if adm(M,p): hypA_adm_bad+=1
                else: hypA_nadm_bad+=1
                if len(ex)<6: ex.append(('HYPA',rm.fmt(M),p,adm(M,p)))
            # full
            seg_p=seg(M,p,j1)
            if tp==mk: full_ok+=1
            else: full_bad+=1
        for p in range(0,j1-1):
            if p in body and (p+1) in body:
                eq = (body[p]==body[p+1])
                if not adm(M,p):
                    if eq: w2L_ok+=1
                    else: w2L_bad+=1
                if not adm(M,p+1):
                    if eq: w2R_ok+=1
                    else: w2R_bad+=1
    print(f"HYP-A bpHeadT(Trans seg)==bpHeadT(Mark): ok={hypA_ok} bad={hypA_bad} (adm_bad={hypA_adm_bad} nadm_bad={hypA_nadm_bad})")
    print(f"FULL Trans(seg)==Mark: ok={full_ok} bad={full_bad}")
    print(f"W2-left  (nadm at p, compare p,p+1): ok={w2L_ok} bad={w2L_bad}")
    print(f"W2-right (nadm at p+1, compare p,p+1): ok={w2R_ok} bad={w2R_bad}")
    for e in ex: print("  ",e)

if __name__=='__main__':
    pool=gen_pool(10,4,4,3000)
    print("pool",len(pool))
    probe(pool)

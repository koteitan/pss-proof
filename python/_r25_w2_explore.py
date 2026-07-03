#!/usr/bin/env python3
# W2 exploration (r25-W2): validate reductions & find clean structural invariant.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, leR, Adm, adm,
                       nadm, oper, diagSeq, marked, Red, nextR)
import red_model as rm
from trans_model import Trans, bpHeadT, bpHeadV, Dpt, PB, ZB, Mark

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

def probe(hosts, budget=260):
    # tests
    segcompose_bad=0            # seg(seg H (r-1) c) 1 k == seg H r c
    fullslice_bad=0             # seg G 0 (Lng G-1) == G
    nadmloc_bad=0               # nadm H r => nadm (seg H (r-1) c) 1
    const_ok=const_bad=0        # bpHeadT Trans seg H r c == bpHeadT Trans seg H (Adm H r) c
    admanchor_ok=admanchor_bad=0# at jm=Adm H r (adm): Trans(seg H jm c) principal, body == Mark?
    peel_adm_ok=peel_adm_bad=0  # adm H (i+1): Trans(seg H (i+1) c)==bpHeadT(Trans(seg H i c))
    peel_nadm_holds=peel_nadm_fails=0
    ex=[]
    t0=time.time()
    for H in hosts:
        if time.time()-t0>budget: break
        if not (reduced(H) and monoT(H)): continue
        n=Lng(H)
        for r in range(1,n-1):
            if adm(H,r): continue
            for c in range(r+1,n):
                G=seg(H,r-1,c)            # left-extended slice
                # seg composition
                k=Lng(G)-1
                if seg(G,1,k)!=seg(H,r,c): segcompose_bad+=1
                if seg(G,0,Lng(G)-1)!=G: fullslice_bad+=1
                # nadm locality: local column 1 of G corresponds to global r
                if not nadm(G,1): nadmloc_bad+=1
                # CONST across [Adm H r, r]
                jm=Adm(H,r)
                Trc=Ts(seg(H,r,c)); Tjm=Ts(seg(H,jm,c))
                if Trc is not None and Tjm is not None:
                    if bpHeadT(Trc)==bpHeadT(Tjm): const_ok+=1
                    else:
                        const_bad+=1
                        if len(ex)<5: ex.append(('CONST',rm.fmt(H),r,c,jm))
        # peel across each column i+1 (adm-gated)
        for i in range(0,n-1):
            for c in range(i+2,n):
                Ti=Ts(seg(H,i,c)); Ti1=Ts(seg(H,i+1,c))
                if Ti is None or Ti1 is None: continue
                peel = (Ti1==bpHeadT(Ti))
                if adm(H,i+1):
                    if peel: peel_adm_ok+=1
                    else: peel_adm_bad+=1
                else:
                    if peel: peel_nadm_holds+=1
                    else: peel_nadm_fails+=1
    print(f"seg-compose bad={segcompose_bad}  full-slice bad={fullslice_bad}")
    print(f"nadm-locality bad={nadmloc_bad}  (nadm H r => nadm (seg H (r-1) c) 1)")
    print(f"CONST bpHeadT(seg r c)==bpHeadT(seg (Adm r) c): ok={const_ok} bad={const_bad}")
    print(f"peel adm-gated: adm ok={peel_adm_ok} bad={peel_adm_bad} | nadm holds={peel_nadm_holds} fails={peel_nadm_fails}")
    for e in ex: print("  EX",e)

if __name__=='__main__':
    pool=gen_pool(11,4,4,4000)
    print("pool",len(pool))
    probe(pool)

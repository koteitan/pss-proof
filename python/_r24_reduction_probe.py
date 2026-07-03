#!/usr/bin/env python3
# Verify the WRAP->DEADM reduction is viable: over the KER regime, for each r in (jm,q]
#   (i) not adm H r, (ii) leR H 0 r c, (iii) seg H (r-1) c reduced&monoT,
#   (iv) WRAP_H: Trans(seg H r c) = Dpt(e1 r)(bpHeadT(Trans(seg H (r-1) c)))
# Also check leR H 0 r c for r in [jm,q].
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, leR, Adm, adm,
                       oper, diagSeq, marked)
import red_model as rm
from trans_model import Trans, bpHeadT, Dpt, ZB

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

def probe(hosts, deep=0, budget=300):
    nadm_bad=0; leR_bad=0; redmono_bad=0; wrap_bad=0; wrap_ok=0
    leR_jm_bad=0
    ex=[]
    t0=time.time()
    for H in hosts:
        if time.time()-t0>budget: break
        if not (reduced(H) and monoT(H)): continue
        n=Lng(H)
        if deep and n<deep: continue
        for q in range(1,n):
            jm=Adm(H,q)
            if jm==q: continue
            if not marked(H,jm): continue
            for c in range(q+1,n):
                if not leR(H,0,q,c): continue
                # leR for all r in [jm,q]
                for r in range(jm,q+1):
                    if not leR(H,0,r,c): leR_jm_bad+=1
                # steps r in (jm,q]
                for r in range(jm+1,q+1):
                    if adm(H,r): nadm_bad+=1
                    if not leR(H,0,r,c): leR_bad+=1
                    S=seg(H,r-1,c)
                    if not (reduced(S) and monoT(S)): redmono_bad+=1
                    Tr=Ts(seg(H,r,c)); Tr1=Ts(seg(H,r-1,c))
                    if Tr is None or Tr1 is None: continue
                    want=Dpt(entry(H,1,r), bpHeadT(Tr1))
                    if Tr==want: wrap_ok+=1
                    else:
                        wrap_bad+=1
                        if len(ex)<6: ex.append((rm.fmt(H),r,c,jm,q,Tr,want))
    tag=f"deep>={deep}" if deep else "all"
    print(f"[{tag}] over KER-regime steps r in (jm,q]:")
    print(f"   nadm_bad={nadm_bad} leR(r,c)_bad={leR_bad} seg(r-1,c)_notredmono={redmono_bad}")
    print(f"   leR(r,c) for r in [jm,q] bad={leR_jm_bad}")
    print(f"   WRAP_H ok={wrap_ok} bad={wrap_bad}")
    for e in ex: print("   WRAP BAD",e)

if __name__=='__main__':
    pool=gen_pool(12,4,4,5000)
    print("pool",len(pool))
    probe(pool)
    probe(pool,deep=9)

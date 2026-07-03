#!/usr/bin/env python3
# Test the LOCAL wrap:  Trans(tl S) = Dpt(entry S 1 1)(bpHeadT(Trans S))
# when column 1 of S is non-admissible.  Find exact domain.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, leR, Adm, adm,
                       oper, diagSeq, marked, le0)
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

def tl(M): return M[1:]

def probe(hosts, budget=240):
    # classify all reduced monoT S with Lng>=3 and col1 non-adm
    ok=bad=0; skip_red_tl=0
    bad_ex=[]
    # also: does it need leR S 0 1 (Lng S -1)?  count when wrap holds vs leR
    ok_leR=ok_noleR=bad_leR=bad_noleR=0
    t0=time.time()
    for S in hosts:
        if time.time()-t0>budget: break
        if not (reduced(S) and monoT(S)): continue
        n=Lng(S)
        if n<3: continue
        if adm(S,1): continue      # need col1 non-admissible
        TS=Ts(S)
        if TS is None: continue
        Ttl=Ts(tl(S))
        if Ttl is None: continue
        want=Dpt(entry(S,1,1), bpHeadT(TS))
        leRcond = leR(S,0,1,n-1)
        if Ttl==want:
            ok+=1
            if leRcond: ok_leR+=1
            else: ok_noleR+=1
        else:
            bad+=1
            if leRcond: bad_leR+=1
            else: bad_noleR+=1
            if len(bad_ex)<10:
                bad_ex.append((rm.fmt(S),leRcond,reduced(tl(S)),monoT(tl(S)),Ttl,want))
    print(f"wrap(col1 nonadm): ok={ok} bad={bad}")
    print(f"   ok  with leR01={ok_leR} without leR01={ok_noleR}")
    print(f"   bad with leR01={bad_leR} without leR01={bad_noleR}")
    for ex in bad_ex:
        S,lc,rtl,mtl,Ttl,want=ex
        print(f"   BAD S={S} leR01={lc} red(tl)={rtl} mono(tl)={mtl}\n      got ={Ttl}\n      want={want}")

if __name__=='__main__':
    pool=gen_pool(12,4,4,6000)
    print("pool",len(pool))
    probe(pool)

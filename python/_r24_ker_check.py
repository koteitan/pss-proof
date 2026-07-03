#!/usr/bin/env python3
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, leR, Adm, adm,
                       oper, diagSeq, Pred, marked)
import red_model as rm
from trans_model import Trans, bpHeadT, Dpt, ZB

def gen_pool(maxlen, maxn, maxseed, cap):
    seen = set(); frontier = []
    for u in range(maxseed):
        for v in range(u, u+maxseed+2):
            M = tuple(diagSeq(u, v))
            if M not in seen: seen.add(M); frontier.append(list(M))
    pool = list(frontier)
    while frontier and len(pool) < cap:
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in range(1, maxn+1):
                N = oper(M, n)
                if Lng(N) > maxlen: continue
                t = tuple(N)
                if t not in seen:
                    seen.add(t); nxt.append(N); pool.append(N)
                    if len(pool) >= cap: break
            if len(pool) >= cap: break
        frontier = nxt
    return pool

def Tsafe(M):
    try:
        return Trans(M)
    except (ValueError, IndexError, RecursionError, AssertionError, KeyError):
        return None

def check(hosts, tag, deep=0, budget=240):
    ker_ok=ker_bad=0; deadm_ok=deadm_bad=0; ntriv_ker=0; ntriv_deadm=0
    ker_cex=[]; deadm_cex=[]
    t0=time.time()
    for H in hosts:
        if time.time()-t0>budget: break
        if not (reduced(H) and monoT(H)): continue
        n=Lng(H)
        if deep and n<deep: continue
        for q in range(n):
            jm = Adm(H, q)
            # (H, jm) in Marked
            if not marked(H, jm): continue
            for c in range(q+1, n):
                if not leR(H,0,q,c): continue
                # slices
                sq = seg(H,q,c); sjm = seg(H,jm,c)
                Tq = Tsafe(sq); Tjm = Tsafe(sjm)
                if Tq is None or Tjm is None: continue
                # KER: bpHeadT(Trans(seg jm c)) == bpHeadT(Trans(seg q c))
                lhs = bpHeadT(Tjm); rhs = bpHeadT(Tq)
                if lhs==rhs:
                    ker_ok+=1
                    if jm!=q: ntriv_ker+=1
                else:
                    ker_bad+=1
                    if len(ker_cex)<5: ker_cex.append((H,q,c,jm,lhs,rhs))
                # DEADM (full): Trans(seg q c) == Dpt(entry H 1 q)(bpHeadT(Trans(seg jm c)))
                # only meaningful when q non-adm (else trivial identity fails generally)
                drhs = Dpt(entry(H,1,q), bpHeadT(Tjm))
                if Tq==drhs:
                    deadm_ok+=1
                    if jm!=q: ntriv_deadm+=1
                else:
                    deadm_bad+=1
                    if len(deadm_cex)<8: deadm_cex.append((H,q,c,jm,adm(H,q),Tq,drhs))
    print(f"[{tag}] KER ok={ker_ok} bad={ker_bad} (nontriv={ntriv_ker}) | DEADM ok={deadm_ok} bad={deadm_bad} (nontriv={ntriv_deadm})")
    for cx in ker_cex:
        print("  KER CEX", cx)
    for cx in deadm_cex[:8]:
        H,q,c,jm,admq,Tq,dr=cx
        print(f"  DEADM CEX H={rm.fmt(H)} q={q} c={c} jm={jm} adm(q)={admq}\n     Tq  ={Tq}\n     want={dr}")
    return ker_bad, deadm_bad

if __name__=='__main__':
    pool = gen_pool(maxlen=12, maxn=4, maxseed=4, cap=4000)
    print("pool size", len(pool))
    check(pool, "all")
    check(pool, "deep>=9", deep=9)

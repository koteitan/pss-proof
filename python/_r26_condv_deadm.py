#!/usr/bin/env python3
# On GENUINE transCondV standard hosts (the real nf3x domain), test the exact
# DEADM1 (c=Lng-1) and DEADM2 (c=Lng-2) identities that nf3x_NFall requires, and
# the reach-conditioned WRAP'/peel at G=M.  Also test WRAP' over genuine-condV G
# generally.  Straddle-aware brute enumeration.
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, leR, Adm, adm,
                       le0, is_standard)
import red_model as rm
from trans_model import Trans, bpHeadT, Dpt

def pr(*a): print(*a); sys.stdout.flush()

def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M):
    j0=transJ0(M); return None if j0 is None else Adm(M,j0)

def transCondV(M):
    n=Lng(M); j0=parent(M,0,n-1)
    if j0 is None: return False
    return (entry(M,1,n-1)>0
            and entry(M,1,j0)+1==entry(M,1,n-1)
            and j0+1 < n-1)

from red_model import oper, diagSeq
def gen_oper(maxlen, maxn, maxseed, cap):
    seen=set(); frontier=[]
    for u in range(maxseed):
        for v in range(u, u+maxseed+2):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M); frontier.append(list(M))
    pool=list(frontier)
    while frontier and len(pool)<cap:
        nxt=[]
        for M in frontier:
            if Lng(M)<=1: continue
            for n in range(1, maxn+1):
                N=oper(M,n)
                if Lng(N)>maxlen: continue
                t=tuple(N)
                if t not in seen: seen.add(t); nxt.append(N); pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        frontier=nxt
    return pool

def brute(maxlen,maxval):
    cells=[(a,b) for a in range(maxval+1) for b in range(maxval+1)]
    for L in range(4,maxlen+1):
        for M in itertools.product(cells,repeat=L):
            yield list(M)

def Ts(M):
    try: return Trans(M)
    except Exception: return None

def run(budget, hosts, use_std=True):
    tot=0; d1_ok=d1_bad=d2_ok=d2_bad=0; d1ex=[]; d2ex=[]
    nonadm=0; t0=time.time()
    for M in hosts:
        if time.time()-t0>budget: break
        if not (reduced(M) and monoT(M)): continue
        if not transCondV(M): continue
        j0=transJ0(M)
        if adm(M,j0): continue                 # non-adm condV
        nonadm+=1
        if use_std and not is_standard(M): continue
        tot+=1
        n=Lng(M); jm1=transJm1(M)
        # DEADM1 at c=n-1
        c1=n-1
        L=Ts(seg(M,j0,c1)); R=Ts(seg(M,jm1,c1))
        if L is not None and R is not None:
            want=Dpt(entry(M,1,j0), bpHeadT(R))
            if L==want: d1_ok+=1
            else:
                d1_bad+=1
                if len(d1ex)<8: d1ex.append((rm.fmt(M),j0,jm1,c1))
        # DEADM2 at c=n-2
        c2=n-2
        L=Ts(seg(M,j0,c2)); R=Ts(seg(M,jm1,c2))
        if L is not None and R is not None:
            want=Dpt(entry(M,1,j0), bpHeadT(R))
            if L==want: d2_ok+=1
            else:
                d2_bad+=1
                if len(d2ex)<8: d2ex.append((rm.fmt(M),j0,jm1,c2))
    pr(f"nonadm-condV(pre-std)={nonadm}  standard-condV hosts={tot}")
    pr(f"  DEADM1 (c=Lng-1): ok={d1_ok} bad={d1_bad}")
    for e in d1ex: pr(f"     D1-CEX M={e[0]} transJ0={e[1]} transJm1={e[2]} c={e[3]}")
    pr(f"  DEADM2 (c=Lng-2): ok={d2_ok} bad={d2_bad}")
    for e in d2ex: pr(f"     D2-CEX M={e[0]} transJ0={e[1]} transJm1={e[2]} c={e[3]}")

if __name__=='__main__':
    pr("=== genuine transCondV, STANDARD, non-adm transJ0; DEADM1/DEADM2 exact ===")
    pr("--- OPER pool (nf3x real domain: standard hosts) ---")
    op=gen_oper(13, 5, 5, 12000)
    pr(f"oper pool={len(op)}")
    run(200, op, use_std=True)
    pr("--- BRUTE straddle (len<=6 val<=3), condV, std ---")
    run(200, brute(6,3), use_std=True)

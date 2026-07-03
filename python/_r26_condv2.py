#!/usr/bin/env python3
# Bounded on-domain check: does the exact nf3x DEADM1(c=Lng-1)/DEADM2(c=Lng-2)
# identity hold on GENUINE transCondV, reduced-monoT, non-adm-transJ0 hosts?
# (standard is a subset; check is_standard only on any CEX.)
import sys, itertools, time, signal
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, Adm, adm,
                       is_standard, oper, diagSeq)
import red_model as rm
from trans_model import Trans, bpHeadT, Dpt

def pr(*a): print(*a); sys.stdout.flush()

class TO(Exception): pass
def _h(s,f): raise TO()
signal.signal(signal.SIGALRM,_h)

def Ts(M,sec=4):
    signal.alarm(sec)
    try: return Trans(M)
    except Exception: return None
    finally: signal.alarm(0)

def transCondV(M):
    n=Lng(M); j0=parent(M,0,n-1)
    if j0 is None: return False
    return (entry(M,1,n-1)>0 and entry(M,1,j0)+1==entry(M,1,n-1) and j0+1 < n-1)

def gen_oper(maxlen,maxn,maxseed,cap):
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

def brute(maxlen,maxval):
    cells=[(a,b) for a in range(maxval+1) for b in range(maxval+1)]
    for L in range(4,maxlen+1):
        for M in itertools.product(cells,repeat=L):
            yield list(M)

def run(tag,hosts,budget):
    tot=d1o=d1b=d2o=d2b=0; ex=[]; t0=time.time()
    for M in hosts:
        if time.time()-t0>budget: break
        if Lng(M)>11: continue
        if not (reduced(M) and monoT(M)): continue
        if not transCondV(M): continue
        j0=parent(M,0,Lng(M)-1)
        if adm(M,j0): continue
        tot+=1; n=Lng(M); jm1=Adm(M,j0)
        for (c,lab,inc) in ((n-1,'D1',1),(n-2,'D2',2)):
            L=Ts(seg(M,j0,c)); R=Ts(seg(M,jm1,c))
            if L is None or R is None: continue
            ok = (L==Dpt(entry(M,1,j0),bpHeadT(R)))
            if inc==1:
                if ok: d1o+=1
                else:
                    d1b+=1
                    if len(ex)<10: ex.append(('D1',rm.fmt(M),j0,jm1,c,is_standard(M)))
            else:
                if ok: d2o+=1
                else:
                    d2b+=1
                    if len(ex)<10: ex.append(('D2',rm.fmt(M),j0,jm1,c,is_standard(M)))
    pr(f"[{tag}] genuine-condV nonadm hosts={tot}  DEADM1 ok={d1o} bad={d1b}  DEADM2 ok={d2o} bad={d2b}")
    for e in ex: pr(f"    {e[0]}-CEX M={e[1]} transJ0={e[2]} transJm1={e[3]} c={e[4]} standard={e[5]}")

if __name__=='__main__':
    pr("=== on-domain nf3x DEADM (genuine transCondV, reduced monoT, non-adm transJ0) ===")
    op=gen_oper(10,5,5,5000)
    pr(f"oper pool={len(op)}")
    run("OPER",op,90)
    run("BRUTE(6,3)",brute(6,3),120)

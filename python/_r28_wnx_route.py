#!/usr/bin/env python3
# r28-W2NOSTR route verification: the EXACT Isabelle proof-route conditions
# on genuine ST_PS hosts.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, Adm, adm,
                       oper, diagSeq, le0, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax)
import trans_model as tm
from trans_model import bpHeadT

def pr(*a): print(*a, flush=True)

def Ts(M):
    try: return tm.Trans(M)
    except Exception: return None

def transJ0(M): return parent(M, 0, Lng(M)-1)

def condV(M):
    n = Lng(M)
    if n < 4 or not hasParent(M, 0, n-1): return False
    j0 = transJ0(M)
    return (entry(M,1,n-1) > 0 and entry(M,1,j0)+1 == entry(M,1,n-1)
            and j0+1 < n-1)

def genuine(M):
    return (condV(M) and not adm(M, transJ0(M)) and monoT(M)
            and Red(M) == list(M))

def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0, len(bs)):
            a0,b0 = bs[J0][0]; a1,b1 = bs[J1][0]
            if not (a0 >= a1 and (a0 != a1 or b0 >= b1)): return False
    return True

def cfbx_reg(m, S):
    if not (Red(S) == list(S) and monoT(S)): return False
    b = Br(S)
    if not b: return False
    jl = Joints(S)[len(b)-1]
    if jl is None: return False
    if m < jl: return True
    if m == jl:
        fn = FirstNodes(S)[len(b)-1]
        return entry(S,0,fn) == entry(S,1,fn) and descending(b)
    return False

def gen_oper(maxlen, maxn, maxseed, cap, budget):
    t0=time.time(); seen=set(); frontier=[]
    for u in range(maxseed):
        for v in range(u, u+maxseed+2):
            M=tuple(diagSeq(u,v))
            if Lng(M)<=maxlen and M not in seen: seen.add(M); frontier.append(list(M))
    pool=list(frontier)
    while frontier and len(pool)<cap and time.time()-t0<budget:
        nxt=[]
        for M in frontier:
            if Lng(M)<=1: continue
            for n in range(1, maxn+1):
                N=oper(M,n)
                if Lng(N)>maxlen: continue
                t=tuple(N)
                if t not in seen: seen.add(t); nxt.append(N); pool.append(N)
            if len(pool)>=cap or time.time()-t0>budget: break
        frontier=nxt
    return pool

t0=time.time()
pool = gen_oper(maxlen=12, maxn=4, maxseed=4, cap=30000, budget=150)
pr(f"pool={len(pool)} t={time.time()-t0:.0f}s")
cnt={}; bad=[]
def tick(key, ok, info=None):
    cnt[(key,ok)] = cnt.get((key,ok),0)+1
    if not ok and len(bad)<20: bad.append((key,info))
nge=0
for M in pool:
    if not genuine(M): continue
    nge+=1
    n=Lng(M); j1=n-1; j0=transJ0(M); jm1=Adm(M,j0); d=j0-jm1
    k = entry(M,0,jm1)-entry(M,1,jm1)
    # E: run arithmetic
    tick('E1', entry(M,1,j0)==entry(M,1,jm1)+d, fmt(M))
    tick('E0', entry(M,0,j0)==entry(M,0,jm1)+d, fmt(M))
    tick('Ek', entry(M,0,jm1)>=entry(M,1,jm1), fmt(M))
    # A: c = Lng-1 slice
    S = seg(M,jm1,j1); R = Red(S)
    b = Br(R); lb = len(b)
    tick('A-Brne', lb>=1, fmt(M))
    if lb>=1:
        tick('A-joint', Joints(R)[lb-1]==d, (fmt(M),Joints(R)[lb-1],d))
        tick('A-fn', FirstNodes(R)[lb-1]==Lng(R)-1, (fmt(M),FirstNodes(R)[lb-1]))
        tick('A-diag', entry(R,0,Lng(R)-1)==entry(R,1,Lng(R)-1), fmt(M))
        tick('A-desc', descending(b), fmt(M))
        tick('A-trm', 0<d<TrMax(R), (fmt(M),d,TrMax(R)))
    tick('A-reg', cfbx_reg(d,R), fmt(M))
    # B: transfer at c=j1 via VE d R
    lhs = bpHeadT(Ts(seg(R,d,Lng(R)-1))); rhs = bpHeadT(Ts(R))
    tick('B-VE', lhs==rhs, fmt(M))
    tick('B-match', bpHeadT(Ts(seg(M,j0,j1)))==lhs and bpHeadT(Ts(seg(M,jm1,j1)))==rhs, fmt(M))
    # C: R2 = Pred R
    S2 = seg(M,jm1,j1-1); R2 = Red(S2)
    PredR = R[:-1]
    tick('C-eq', R2==PredR, (fmt(M),fmt(R2),fmt(PredR)))
    # D: guard at c = Lng-2
    if TrMax(R)+2 == Lng(R):
        u = entry(R,1,0)
        tick('D-trunk', PredR==diagSeq(u,u+Lng(PredR)-1), (fmt(M),fmt(PredR)))
        tick('D-2col', d < Lng(PredR)-1, (fmt(M),d,Lng(PredR)))
    else:
        tick('D-reg', cfbx_reg(d,PredR), (fmt(M),fmt(PredR)))
    # transfer at c=Lng-2
    l2 = bpHeadT(Ts(seg(R2,d,Lng(R2)-1))); r2 = bpHeadT(Ts(R2))
    tick('D-VE', l2==r2, fmt(M))
    tick('D-match', bpHeadT(Ts(seg(M,j0,j1-1)))==l2 and bpHeadT(Ts(seg(M,jm1,j1-1)))==r2, fmt(M))
pr(f"genuine={nge} t={time.time()-t0:.0f}s")
for key in sorted(set(kk for kk,_ in cnt)):
    pr(f"  {key}: ok={cnt.get((key,True),0)} BAD={cnt.get((key,False),0)}")
for b_ in bad: pr(f"  BADCASE {b_}")
pr(f"t={time.time()-t0:.0f}s")

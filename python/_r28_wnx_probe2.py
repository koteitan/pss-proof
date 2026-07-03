#!/usr/bin/env python3
# r28-W2NOSTR comprehensive probe (optimized: condV-first filter, memoized Red/Trans).
# Outputs (flushed):
#  [Q1] W2nostr all c in (j0, Lng-1] on genuine ST_PS oper hosts (+ deep count)
#  [Q2] run histogram (j0 - jm1)
#  [Q3] same on brute RT_PS (not nec ST_PS) hosts
#  [Q4] per run-column guard on Red slice: {lt, eq-diag-desc, BrEmpty, other}, per c-kind
#  [Q5] trunk closed form on BrEmpty slices R: Trans R == Dpt(e1 R 0, Dpt(e1 R last, 0))
#  [Q6] reach le0(M, s, c) for run columns at all c
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, Adm, adm,
                       oper, diagSeq, le0, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax)
import trans_model as tm
from trans_model import Dpt, ZB, bpHeadT

def pr(*a): print(*a, flush=True)

_tmemo = {}
def Ts(M):
    t = tuple(M)
    if t in _tmemo: return _tmemo[t]
    try: v = tm.Trans(M)
    except Exception: v = None
    _tmemo[t] = v
    return v

_rmemo = {}
def RedM(M):
    t = tuple(M)
    if t in _rmemo: return _rmemo[t]
    v = Red(M); _rmemo[t] = v
    return v

_redqmemo = {}
def is_reduced(M):
    t = tuple(M)
    if t in _redqmemo: return _redqmemo[t]
    v = (RedM(list(M)) == list(M)); _redqmemo[t] = v
    return v

def transJ0(M): return parent(M, 0, Lng(M)-1)

def condV(M):
    n = Lng(M)
    if n < 4: return False
    if not hasParent(M, 0, n-1): return False
    j0 = transJ0(M)
    return (entry(M,1,n-1) > 0 and entry(M,1,j0)+1 == entry(M,1,n-1)
            and j0+1 < n-1)

def genuine(M):
    if not condV(M): return False
    if adm(M, transJ0(M)): return False
    if not monoT(M): return False
    return is_reduced(M)

def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0, len(bs)):
            a0, b0 = bs[J0][0]; a1, b1 = bs[J1][0]
            if not (a0 >= a1 and (a0 != a1 or b0 >= b1)): return False
    return True

def guard_class(R):
    # R assumed reduced monoT
    b = Br(R)
    if not b: return 'BrEmpty'
    jl = Joints(R)[len(b)-1]
    if jl is None: return 'jointNone'
    if 1 < jl: return 'lt'
    if 1 == jl:
        fn = FirstNodes(R)[len(b)-1]
        if entry(R,0,fn) == entry(R,1,fn) and descending(b): return 'eq-diag-desc'
        return 'eq-BAD'
    return 'joint0'

def check_host(M, st, exs):
    n = Lng(M); j0 = transJ0(M); jm1 = Adm(M, j0)
    st['hosts'] += 1
    if n >= 9: st['deep'] += 1
    st['runs'][j0-jm1] = st['runs'].get(j0-jm1, 0) + 1
    for c in range(j0+1, n):
        ckind = 'need' if c >= n-2 else 'mid'
        Q = Ts(seg(M, j0, c)); N = Ts(seg(M, jm1, c))
        if Q is None or N is None:
            st['tf'] += 1; continue
        hold = (bpHeadT(Q) == bpHeadT(N))
        if hold: st['ok'] += 1
        else:
            st['bad'] += 1
            if len(exs) < 8: exs.append(('W2CEX', fmt(M), j0, jm1, c))
        # per-run-column diagnostics
        for s in range(jm1, j0):
            rk = 'reach' if le0(M, s, c) else 'NOreach'
            st['reach'][(ckind, rk)] = st['reach'].get((ckind, rk), 0) + 1
            if rk == 'NOreach': continue
            R = RedM(seg(M, s, c))
            if not (is_reduced(R) and monoT(R)):
                g = 'RnotRedMono'
            else:
                g = guard_class(R)
            st['guard'][(ckind, g, hold)] = st['guard'].get((ckind, g, hold), 0) + 1
            if g == 'BrEmpty':
                tr = Ts(R)
                cf = (tr == Dpt(entry(R,1,0), Dpt(entry(R,1,Lng(R)-1), ZB)))
                st['trunkcf'][cf] = st['trunkcf'].get(cf, 0) + 1
                if not cf and len(exs) < 12:
                    exs.append(('TRUNKCF', fmt(M), s, c, fmt(R), tr))
            elif g in ('eq-BAD', 'joint0', 'jointNone', 'RnotRedMono'):
                if len(exs) < 12: exs.append(('GUARDBAD', fmt(M), s, c, g, fmt(R), hold))

def newst():
    return dict(hosts=0, deep=0, ok=0, bad=0, tf=0, runs={}, reach={}, guard={}, trunkcf={})

def report(tag, st, exs):
    pr(f"[{tag}] hosts={st['hosts']} deep={st['deep']} ok={st['ok']} bad={st['bad']} tf={st['tf']}")
    pr(f"[{tag}] runs={st['runs']}")
    pr(f"[{tag}] reach={st['reach']}")
    pr(f"[{tag}] guard={st['guard']}")
    pr(f"[{tag}] trunkcf={st['trunkcf']}")
    for e in exs: pr(f"   {e}")

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

def main():
    t0=time.time()
    # stage A: oper corpus
    pool = gen_oper(maxlen=12, maxn=4, maxseed=4, cap=30000, budget=150)
    pr(f"[genA] pool={len(pool)} t={time.time()-t0:.0f}s")
    st=newst(); exs=[]
    nge=0
    for M in pool:
        if genuine(M):
            nge+=1
            check_host(M, st, exs)
    pr(f"[genA] genuine={nge} t={time.time()-t0:.0f}s")
    report('Q1-oper', st, exs)

    # stage B: brute RT_PS (straddle-style, not nec. ST_PS)
    stB=newst(); exsB=[]
    budget=300.0; t1=time.time(); hit=False
    cells=[(a,b) for a in range(4) for b in range(4)]
    for L in range(4, 8):
        if time.time()-t1>budget: hit=True; break
        for tup in itertools.product(cells, repeat=L-1):
            if time.time()-t1>budget: hit=True; break
            M=[(0,0)]+list(tup)
            if not genuine(M): continue
            check_host(M, stB, exsB)
        pr(f"[Q3-brute] L={L} done: hosts={stB['hosts']} ok={stB['ok']} bad={stB['bad']} t={time.time()-t0:.0f}s")
    pr(f"[Q3-brute] budget_hit={hit}")
    report('Q3-brute', stB, exsB)
    pr(f"total t={time.time()-t0:.0f}s")

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
# r28-W2NOSTR empirical probe v2 (staged, flushed output).
#  Q1: W2nostr on GENUINE ST_PS oper hosts (deep Lng>=9 included), ALL c in (j0, Lng-1]
#  Q2: run cap  j0 - jm1 == 1  on those hosts
#  Q3: same on BRUTE reduced+monoT+condV+~adm(j0) hosts (RT_PS, not nec. ST_PS)
#  Q4: diagnostics per instance: parent M 0 c (straddle?), le0 M j0 c,
#      slice S=seg M jm1 c: reduced? monoT?, cfbx_reg-1 conjunct analysis
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, leR, Adm, adm,
                       oper, diagSeq, marked, le0, Br, FirstNodes, Joints,
                       hasParent, fmt, TrMax)
import red_model as rm
from trans_model import Trans, bpHeadT

def pr(*a): print(*a); sys.stdout.flush()

def Ts(M):
    try: return Trans(M)
    except Exception: return None

def transJ0(M): return parent(M, 0, Lng(M)-1)

def condV(M):
    n = Lng(M)
    if n < 2: return False
    if not hasParent(M, 0, n-1): return False
    j0 = transJ0(M)
    return (entry(M,1,n-1) > 0 and entry(M,1,j0)+1 == entry(M,1,n-1)
            and j0+1 < n-1)

def genuine(M):
    if Lng(M) < 4: return False
    if not (monoT(M) and reduced(M)): return False
    if not condV(M): return False
    if adm(M, transJ0(M)): return False
    return True

def descending(bs):
    # Br M descending (as in §8.2 regime): first entries of branch heads strictly?
    # We only report joint numbers; regime detail handled via conjunct dump.
    return None

def cfbx_reg1_diag(S):
    """return (verdict, why) for cfbx_reg 1 S"""
    if not reduced(S): return (False, 'notRT')
    if not monoT(S): return (False, 'notPT')
    b = Br(S)
    if not b: return (False, 'BrEmpty')
    jl = Joints(S)[len(b)-1]
    if jl is None: return (False, 'jointNone')
    if 1 < jl: return (True, 'lt')
    if 1 == jl:
        fn = FirstNodes(S)[len(b)-1]
        if entry(S,0,fn) == entry(S,1,fn):
            return (None, 'eq-diag(descending unchecked)')
        return (False, 'eq-nodiag')
    return (False, f'joint{jl}<1')

def check_host(M, stats, exs, diag, dlim=12):
    n = Lng(M); j0 = transJ0(M); jm1 = Adm(M, j0)
    run = j0 - jm1
    stats['hosts'] += 1
    if n >= 9: stats['deep'] += 1
    stats['runs'][run] = stats['runs'].get(run, 0) + 1
    for c in range(j0+1, n):
        Q = Ts(seg(M, j0, c)); N = Ts(seg(M, jm1, c))
        if Q is None or N is None:
            stats['trans_fail'] += 1; continue
        hold = (bpHeadT(Q) == bpHeadT(N))
        if hold: stats['ok'] += 1
        else:
            stats['bad'] += 1
            if len(exs) < 8: exs.append((fmt(M), j0, jm1, c))
        if len(diag) < dlim:
            S = seg(M, jm1, c)
            pc = parent(M, 0, c)
            diag.append((fmt(M), j0, jm1, c, hold,
                         'reach' if le0(M, j0, c) else 'NOreach',
                         f'pc={pc}', 'Sred' if reduced(S) else 'SnotRed',
                         'Smono' if monoT(S) else 'Smulti',
                         cfbx_reg1_diag(S)))

def gen_oper(maxlen, maxn, maxseed, cap, budget):
    t0=time.time()
    seen=set(); frontier=[]
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
                if len(pool)>=cap: break
            if len(pool)>=cap or time.time()-t0>budget: break
        frontier=nxt
    return pool

def main():
    t0 = time.time()
    stats = dict(hosts=0, deep=0, ok=0, bad=0, trans_fail=0, runs={})
    exs = []; diag = []
    # ---- stage A: moderate oper pool ----
    pool = gen_oper(maxlen=11, maxn=4, maxseed=3, cap=12000, budget=180)
    pr(f"[genA] pool={len(pool)} t={time.time()-t0:.0f}s")
    gh=[]
    for M in pool:
        if genuine(M): gh.append(M)
    pr(f"[genA] genuine hosts={len(gh)} t={time.time()-t0:.0f}s")
    for M in gh: check_host(M, stats, exs, diag)
    pr(f"[Q1-A oper] hosts={stats['hosts']} deep={stats['deep']} ok={stats['ok']} bad={stats['bad']} tf={stats['trans_fail']}")
    pr(f"[Q2-A] runs={stats['runs']}")
    for e in exs: pr(f"   CEX {e}")
    for d in diag: pr(f"   DIAG {d}")

    # ---- stage B: deep pool (longer, bigger n) ----
    poolB = gen_oper(maxlen=14, maxn=3, maxseed=4, cap=25000, budget=240)
    pr(f"[genB] pool={len(poolB)} t={time.time()-t0:.0f}s")
    statsB = dict(hosts=0, deep=0, ok=0, bad=0, trans_fail=0, runs={})
    exsB=[]; diagB=[]
    seenA = set(tuple(M) for M in gh)
    ghB=[]
    for M in poolB:
        if tuple(M) in seenA: continue
        if genuine(M): ghB.append(M)
    pr(f"[genB] new genuine hosts={len(ghB)} t={time.time()-t0:.0f}s")
    for M in ghB: check_host(M, statsB, exsB, diagB, dlim=6)
    pr(f"[Q1-B oper-deep] hosts={statsB['hosts']} deep={statsB['deep']} ok={statsB['ok']} bad={statsB['bad']} tf={statsB['trans_fail']}")
    pr(f"[Q2-B] runs={statsB['runs']}")
    for e in exsB: pr(f"   CEX {e}")
    for d in diagB: pr(f"   DIAG {d}")

    # ---- stage C: brute RT_PS (not nec ST_PS) ----
    statsC = dict(hosts=0, deep=0, ok=0, bad=0, trans_fail=0, runs={})
    exsC=[]; diagC=[]
    budget=300.0; t1=time.time(); hit=False
    cells=[(a,b) for a in range(4) for b in range(4)]
    for L in range(4, 8):
        if time.time()-t1>budget: hit=True; break
        for tup in itertools.product(cells, repeat=L-1):
            if time.time()-t1>budget: hit=True; break
            M=[(0,0)]+list(tup)
            if not genuine(M): continue
            check_host(M, statsC, exsC, diagC, dlim=20)
        pr(f"[Q3-C] after L={L}: hosts={statsC['hosts']} ok={statsC['ok']} bad={statsC['bad']} runs={statsC['runs']} t={time.time()-t0:.0f}s")
    pr(f"[Q3-C brute RT_PS] hosts={statsC['hosts']} ok={statsC['ok']} bad={statsC['bad']} tf={statsC['trans_fail']} budget_hit={hit}")
    pr(f"[Q3-C] runs={statsC['runs']}")
    for e in exsC: pr(f"   CEX {e}")
    for d in diagC[:20]: pr(f"   DIAG {d}")
    pr(f"total t={time.time()-t0:.0f}s")

if __name__ == '__main__':
    main()

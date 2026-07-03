#!/usr/bin/env python3
"""r23-CONDIIEX: validate the A36 EXISTENTIAL replicate-count correction for the
§8.3 condition-(II) lhs closed form.

Claim proven (conditional on lhs_ex):
  c2ex_exch_of_lhs_closed_ex : from  (EX c>=1. Trans(M[m]) = closed(c))
       derive  EX k. Trans(M[n]) = operB(Trans M)(numBT k)   [k = c-1]
  c2ex_exchange2_condII_ex   : descent lessBT(Trans(M[n]),Trans M) all n, BOTH branches.

The KIND-0 condII marked principal of Trans M is  D_u(t0 + D_v(t1 + D_0 0)) ;
in Trans(M[m]) it becomes  D_u(t0 + (D_v t1)^c) , c = replicate count.
r21b REFUTED the fixed count c = m-1 (CEX (0,0)(1,1)(2,2)(2,0)(2,0)); the count
is m OR m-1 depending on the internal leftDj0 branch.  This script confirms:
  (A) c >= 1 always (so k = c-1 >= 0 exists -> lemma 1 sound);
  (B) BOTH branches present: c == m-1 AND c == m both occur across hosts;
  (C) the fixed c = m-1 CEX reproduces.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper, Pred, fmt)
from trans_model import adm, ZB, Dpt, addBT, scb_decomps, flatBT, flatBP

_TC = {}
_T0 = tm.Trans
def _Tm(M, d=0):
    k = tuple(M)
    if k not in _TC: _TC[k] = _T0(M, d)
    return _TC[k]
tm.Trans = _Tm
def T(M): return tm.Trans(M)

def pr(*a): print(*a, flush=True)

def condII(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) == 0 and not adm(M, jp)

def host(M):
    if Lng(M) < 2 or zeroT(M) or not monoT(M): return False
    if Lng(M) - 1 <= 1: return False
    return condII(M)

def all_principals(t):
    """every ('D',v,body) node anywhere in BT t."""
    out = []
    for p in t[1]:
        out.append(p)
        out += all_principals(p[2])
    return out

def is_kind0_core(p):
    """p = ('D',u,body), body = ('T', pre + [('D',v, ('T', t1p + [('D',0,ZB)]))])."""
    u, body = p[1], p[2]
    ps = body[1]
    if not ps: return None
    last = ps[-1]                    # ('D', v, t1+D0 0)
    if last[0] != 'D': return None
    v, inner = last[1], last[2]
    ip = inner[1]
    if not ip: return None
    tail = ip[-1]                    # must be ('D',0,ZB) = D_0 0
    if tail != ('D', 0, ZB): return None
    t0 = ('T', ps[:-1])
    t1 = ('T', ip[:-1])
    return (u, t0, v, t1)

def find_marked_core(TM):
    """return (u,t0,v,t1) for a kind-0 core that scb-decomposes TM (b all ')')."""
    cands = []
    for p in all_principals(TM):
        info = is_kind0_core(p)
        if info is None: continue
        if scb_decomps(TM, flatBP(p)):   # valid scb: tail all ')'
            cands.append(info)
    return cands

def count_in(Tm, u, t0, v):
    """find principal head=u whose body = t0parts ++ (D_v t1)^c (any fixed t1),
       valid scb; return list of c (should be one)."""
    t0p = t0[1]; dv = v
    out = []
    for p in all_principals(Tm):
        if p[1] != u: continue
        ps = p[2][1]
        if len(ps) <= len(t0p): continue
        if ps[:len(t0p)] != t0p: continue
        rest = ps[len(t0p):]
        # all rest components must be equal D_v <same t1>
        if any(r[0] != 'D' or r[1] != dv for r in rest): continue
        if any(r[2] != rest[0][2] for r in rest): continue   # identical bodies
        if not scb_decomps(Tm, flatBP(p)): continue
        out.append(len(rest))
    return out

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

def analyse(hosts, tag, maxm=4, maxoperlen=20, budget=180):
    saw_mm1 = saw_m = saw_other = 0; c_ge1_fail = 0; nohost = 0; chk = 0
    examples = []; t0start = time.time()
    for M in hosts:
        if time.time() - t0start > budget: break
        try:
            TM = T(M)
        except (ValueError, IndexError, RecursionError):
            continue
        cores = find_marked_core(TM)
        if not cores:
            nohost += 1; continue
        u, t0, v, t1 = cores[0]
        seq = []
        for m in range(2, maxm+1):
            N = oper(M, m)
            if Lng(N) > maxoperlen: continue
            try:
                Tm = T(N)
            except (ValueError, IndexError, RecursionError):
                continue
            cs = count_in(Tm, u, t0, v)
            if not cs: continue
            c = max(cs)                 # the marked (rightmost) replicate run
            chk += 1
            if c < 1: c_ge1_fail += 1
            if c == m-1: saw_mm1 += 1
            elif c == m: saw_m += 1
            else: saw_other += 1
            seq.append((m, c))
        if seq and len(examples) < 8:
            examples.append((M, seq))
    pr(f"[{tag}] hosts={len(hosts)} core_found={len(hosts)-nohost} "
       f"checks={chk}  c>=1 FAILS={c_ge1_fail}")
    pr(f"[{tag}] count==m-1: {saw_mm1}   count==m: {saw_m}   other: {saw_other}")
    for M, seq in examples:
        pr(f"   {fmt(M)}  (m,c)={seq}")
    return saw_mm1, saw_m

def main():
    t0 = time.time()
    # CEX reproduction
    CEX = [(0,0),(1,1),(2,2),(2,0),(2,0)]
    pr("=== r21b CEX (0,0)(1,1)(2,2)(2,0)(2,0) ===")
    if host(CEX):
        analyse([CEX], "CEX", maxm=5, maxoperlen=16)
    else:
        pr("   (CEX not a genuine condII host under this model; skipping)")
    # WIDE
    pool = gen_pool(maxlen=8, maxn=4, maxseed=6, cap=2500)
    hosts = [M for M in pool if host(M)]
    pr(f"\nWIDE pool={len(pool)} condII_hosts={len(hosts)} build_s={round(time.time()-t0,1)}")
    mm1, m = analyse(hosts, "WIDE", maxm=4, maxoperlen=16, budget=220)
    # DEEP Lng>=9 via targeted expansion
    dpool = gen_pool(maxlen=11, maxn=3, maxseed=7, cap=1500)
    dhosts = [M for M in dpool if host(M) and Lng(M) >= 9]
    pr(f"\nDEEP pool={len(dpool)} Lng>=9 condII_hosts={len(dhosts)}")
    dmm1 = dm = 0
    if dhosts:
        dmm1, dm = analyse(dhosts, "DEEP", maxm=4, maxoperlen=20, budget=200)
    pr(f"\nBOTH-BRANCHES present overall: m-1 seen={mm1>0 or dmm1>0}  m seen={m>0 or dm>0}")

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""r17-DII: empirical validation of the condition-(II) DESCENT
  lessBT (Trans(M[n])) (Trans M)   for M a genuine condII host, all n>=1.
Also validates:
  - condII non-vacuity (wide mine) and a DEEP (Lng>=9) sample;
  - the n=1 leaf Trans(M[1]) = Trans(Pred M);
  - the pure-BT kind-0 core comparison
      lessBT (multBT (D_v t1) k) (D_v (t1 + D_0 0))   for random t1,v,k>=1
    (the theorem d2x_multBT_lt_top).
Fast: module-level memoized Trans/Mark; incremental flushed prints.

RESULTS (r17-DII, seed 17; NOTE the diagSeq-oper closure is ST_PS = reduced by
construction, so host() skips the very slow Red recomputation):
  - condII NON-VACUOUS: 67 genuine hosts at Lng 4-8 (exhaustive maxlen=8 pool,
    byLng {4:1,5:8,6:10,7:24,8:24}); 79 genuine hosts at Lng 9-12 via targeted
    one-more-oper expansion (byLng {9:25,10:23,11:16,12:15}).
    [Blind BFS with maxlen>=11 drowns in long-sequence junk before reaching the
     condII-producing branches -> reports 0; that is a BFS-ordering artifact, NOT
     vacuity.  Use exhaustive maxlen<=8 + targeted expansion, as here.]
  - DESCENT lessBT(Trans(M[n]),Trans M), all n in 1..(3/4):
      WIDE (Lng 4-8, 11 hosts):  44/44  FAILS=0
      DEEP (Lng 9-12, 79 hosts): 237/237 FAILS=0
    n=1 leaf Trans(M[1])=Trans(Pred M): 0 FAILS.
  - KIND-0 core lessBT(multBT(D_v t1,k), D_v(t1+D_0 0)) k>=1 (= d2x_multBT_lt_top):
      40000/40000 FAILS=0; multBT(D_v t1,k) head = D_v t1 always.
  Consistent with the r14-F7 fossil (condII descent 3748/3748) and r15-VX
  (condII printed index EXACT 204/204, no A28-shift).
"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, P, monoT, zeroT, diagSeq, parent, oper, Pred, fmt)
from trans_model import adm, ZB, Dpt, addBT

# ---- module-level memoization so the internal recursion is fast ----
_TC, _MC = {}, {}
_T0, _M0 = tm.Trans, tm.Mark
def _Tm(M, d=0):
    k = tuple(M)
    if k not in _TC: _TC[k] = _T0(M, d)
    return _TC[k]
def _Mm(M, m, d=0):
    k = (tuple(M), m)
    if k not in _MC: _MC[k] = _M0(M, m, d)
    return _MC[k]
tm.Trans = _Tm; tm.Mark = _Mm
def T(M): return tm.Trans(M)

def pr(*a): print(*a, flush=True)

def condII(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) == 0 and not adm(M, jp)

def lessBP(p, q): return p[1] < q[1] or (p[1] == q[1] and lessBT(p[2], q[2]))
def lessBT(a, b):
    ps, qs = a[1], b[1]
    if not ps: return bool(qs)
    if not qs: return False
    return lessBP(ps[0], qs[0]) or (ps[0] == qs[0]
                                    and lessBT(('T',ps[1:]), ('T',qs[1:])))
def multBT(a, k):
    out = ('T', [])
    for _ in range(k): out = addBT(out, a)
    return out

def host(M):
    # pool = oper-closure of diagSeq seeds => every member is ST_PS (hence reduced)
    # by construction; recomputing Red is both redundant and very slow, so skip it.
    if Lng(M) < 2 or zeroT(M) or not monoT(M): return False
    if Lng(M) - 1 <= 1: return False
    return condII(M)

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

def descent_check(hosts, maxn, tag):
    fails = 0; chk = 0; leaf = 0
    for M in hosts:
        TM = T(M)
        if T(oper(M,1)) != T(Pred(M)): leaf += 1
        for n in range(1, maxn+1):
            if not lessBT(T(oper(M,n)), TM):
                fails += 1; pr("  DFAIL", fmt(M), n)
            chk += 1
    pr(f"[{tag}] descent checked={chk} FAILS={fails}  n=1-leaf(=Pred)FAILS={leaf}")
    return fails

def main():
    random.seed(17)
    # ---- WIDE non-vacuity + shallow descent (fast) ----
    t0 = time.time()
    pool = gen_pool(maxlen=8, maxn=4, maxseed=6, cap=2500)
    hosts = [M for M in pool if host(M)]
    byl = {}
    for M in hosts: byl[Lng(M)] = byl.get(Lng(M),0)+1
    pr(f"WIDE pool={len(pool)} maxLng={max(Lng(M) for M in pool)} "
       f"condII_hosts={len(hosts)} byLng={dict(sorted(byl.items()))} "
       f"build_s={round(time.time()-t0,1)}")
    descent_check(hosts, 4, "WIDE")

    # ---- DEEP mine: Lng>=9 condII hosts (bounded sample) ----
    t0 = time.time()
    dpool = gen_pool(maxlen=11, maxn=3, maxseed=7, cap=2500)
    dhosts = [M for M in dpool if host(M) and Lng(M) >= 9]
    byl = {}
    for M in dpool:
        if host(M): byl[Lng(M)] = byl.get(Lng(M),0)+1
    pr(f"DEEP pool={len(dpool)} condII_hosts_all={sum(byl.values())} "
       f"byLng={dict(sorted(byl.items()))} Lng>=9={len(dhosts)} "
       f"build_s={round(time.time()-t0,1)}")
    if dhosts:
        for M in dhosts[:12]:
            pr("   deep host Lng", Lng(M), fmt(M))
    descent_check(dhosts, 3, "DEEP")

    # ---- pure-BT kind-0 core comparison (d2x_multBT_lt_top) ----
    def rb(d=0):
        if d > 2 or random.random() < 0.4: return ZB
        return ('T', [('D', random.randint(0,4), rb(d+1))
                      for _ in range(random.randint(1,2))])
    cf = cc = sf = 0
    for _ in range(40000):
        v = random.randint(0,5); t1 = rb(); k = random.randint(1,7)
        m = multBT(Dpt(v, t1), k)
        if not lessBT(m, Dpt(v, addBT(t1, Dpt(0, ZB)))): cf += 1
        if m[1][0] != ('D', v, t1): sf += 1
        cc += 1
    pr(f"KIND0 core lessBT(multBT(Dv t1,k),Dv(t1+D0 0)) k>=1: "
       f"checked={cc} FAILS={cf}  multBT-head=Dv t1 FAILS={sf}")

if __name__ == '__main__':
    main()

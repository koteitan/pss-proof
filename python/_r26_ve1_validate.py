#!/usr/bin/env python3
r"""r26-VE1CORE: validate VE'(1) = the m=1 special case of the terminal-slice VE'.

VE1:  S in RT_PS (reduced),  monoT S,  ~adm S 1,  1 < Lng S - 1  (i.e. Lng S >= 3)
        ==>  bpHeadT(Trans(seg S 1 (Lng S - 1))) = bpHeadT(Trans S)

Also probe the structural route hints:
  - Trans S is principal D_{entry S 1 0}(bpHeadT(Trans S)).
  - Trans(seg S 1 (Lng S-1)) is principal D_{entry S 1 1}(deep tail).
  - relation of bpHeadT(Trans S) to Mark S 1, Mark S 0, Adm S 1, parent facts.

Two corpora:
  BRUTE  = brute-force straddle: ALL length-n pair sequences over entries in
           [0..K], filtered to reduced & monoT & ~adm S 1 & Lng>=3.  (NOT
           oper-generated; W1/KER false positives came from oper-only corpora.)
  DEEP   = oper-generated hosts with Lng >= 9, filtered likewise.
"""
import sys, os, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, hasParent,
                       oper, seg, Br, Joints, FirstNodes, TrMax, Red, Adm, fmt)
from trans_model import Trans, Mark, Pred, bpHeadT, bpHeadV, reduced, adm

# memoize Trans
_TC = {}
_T0 = tm.Trans
def _Tm(M, d=0):
    k = tuple(M)
    if k not in _TC:
        _TC[k] = _T0(list(M), d)
    return _TC[k]
tm.Trans = _Tm
def T(M): return tm.Trans(list(M))

def pr(*a): print(*a, flush=True)

def is_VE1_host(S):
    if Lng(S) < 3: return False
    if zeroT(S) or not monoT(S): return False   # cheap
    if adm(S, 1): return False                   # cheap; need ~adm S 1
    if not reduced(S): return False              # local RedCondA/B, O(n^4)
    return True

def brute_hosts(n, K, cap=100000, tbudget=60):
    """length-n pair sequences with entries in [0..K] that are VE1 hosts.
    Cheap prefilter (monoT, ~adm S 1) before the reduced() call.  WLOG the
    row-0 head is 0 (translation-invariance of the whole predicate under a
    uniform row-0 shift is NOT assumed; we keep a[0] free but small)."""
    out = []
    t0 = time.time()
    rng = list(range(K + 1))
    # a monoT reduced host has row-0 nondecreasing-ish; still enumerate freely
    for pairs in itertools.product(itertools.product(rng, rng), repeat=n):
        if time.time() - t0 > tbudget: break
        S = list(pairs)
        if is_VE1_host(S):
            out.append(S)
            if len(out) >= cap: break
    return out

def gen_pool(maxlen, maxn, maxseed, cap):
    seen = set(); frontier = []
    for u in range(maxseed):
        for v in range(u, u + maxseed + 2):
            M = tuple(diagSeq(u, v))
            if M not in seen:
                seen.add(M); frontier.append(list(M))
    pool = list(frontier)
    while frontier and len(pool) < cap:
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for nn in range(1, maxn + 1):
                try:
                    N = oper(M, nn)
                except (ValueError, IndexError):
                    continue
                if Lng(N) > maxlen: continue
                t = tuple(N)
                if t not in seen:
                    seen.add(t); nxt.append(N); pool.append(N)
                    if len(pool) >= cap: break
            if len(pool) >= cap: break
        frontier = nxt
    return pool

def check(hosts, tag, tbudget=200):
    ve_ok = ve_bad = 0
    cex = []
    # structural probes
    pr_princ_S = pr_princ_pk = 0
    mark1_eq = mark1_ne = 0     # bpHeadT(Mark S 1) == bpHeadT(Trans S)?
    adm1_zero = 0               # Adm S 1 == 0 ?
    t0 = time.time(); nh = 0
    for S in hosts:
        if time.time() - t0 > tbudget: break
        nh += 1
        j1 = Lng(S) - 1
        try:
            pk = seg(S, 1, j1)
            tS = T(S); tPk = T(pk)
            ve = (bpHeadT(tS) == bpHeadT(tPk))
        except (RecursionError, AssertionError, ValueError, IndexError) as e:
            cex.append((fmt(S), 'ERR', str(e)))
            continue
        if ve: ve_ok += 1
        else:
            ve_bad += 1
            if len(cex) < 12:
                cex.append((fmt(S), 'VE1 FAIL',
                            f'Lng={Lng(S)} admS1={adm(S,1)} '
                            f'e10={entry(S,1,0)} e11={entry(S,1,1)}'))
        # structural: Trans S principal head = entry S 1 0
        if tS[1] and bpHeadV(tS) == entry(S,1,0): pr_princ_S += 1
        if tPk[1] and bpHeadV(tPk) == entry(S,1,1): pr_princ_pk += 1
        # Mark S 1 deep tail vs Trans S deep tail
        try:
            m1 = Mark(list(S), 1)
            if bpHeadT(m1) == bpHeadT(tS): mark1_eq += 1
            else: mark1_ne += 1
        except (RecursionError, AssertionError, ValueError, IndexError):
            pass
        if Adm(S, 1) == 0: adm1_zero += 1
    pr(f"[{tag}] hosts={nh} maxLng={max((Lng(S) for S in hosts[:nh]), default=0)} "
       f"({round(time.time()-t0,1)}s)")
    pr(f"   VE1            {ve_ok}/{ve_ok+ve_bad}"
       + ("" if not ve_bad else f"   CEX={cex[:12]}"))
    pr(f"   princ(TransS)  {pr_princ_S}/{nh}   princ(TransPk) {pr_princ_pk}/{nh}")
    pr(f"   Mark1_deeptail_eq_TransS {mark1_eq}/{mark1_eq+mark1_ne}")
    pr(f"   Adm_S_1==0     {adm1_zero}/{nh}")
    if cex and ve_bad == 0:
        pr(f"   (errors: {cex[:6]})")
    return ve_bad, cex

def main():
    t0 = time.time()
    # BRUTE straddle: length 3..5, entries 0..K
    allbrute = []
    for n, K in [(3,4),(3,5),(4,3),(4,4),(5,2),(5,3)]:
        hs = brute_hosts(n, K, tbudget=45)
        pr(f"brute n={n} K={K}: {len(hs)} VE1-hosts")
        allbrute += hs
    # dedup
    seen = set(); ub = []
    for S in allbrute:
        k = tuple(S)
        if k not in seen: seen.add(k); ub.append(S)
    pr(f"BRUTE total unique VE1-hosts = {len(ub)} (build {round(time.time()-t0,1)}s)")
    b_bad, _ = check(ub, "BRUTE", tbudget=300)

    # DEEP oper-generated, Lng>=9
    t0 = time.time()
    dpool = gen_pool(maxlen=13, maxn=2, maxseed=7, cap=4000)
    dhosts = [S for S in dpool if is_VE1_host(S) and Lng(S) >= 9]
    pr(f"DEEP oper hosts Lng>=9 = {len(dhosts)} (build {round(time.time()-t0,1)}s)")
    d_bad, _ = check(dhosts, "DEEP", tbudget=300)

    # DEEP2: relaxed Lng>=7 to increase count
    d2 = [S for S in dpool if is_VE1_host(S) and Lng(S) >= 7]
    pr(f"DEEP2 oper hosts Lng>=7 = {len(d2)}")
    check(d2, "DEEP7", tbudget=200)

    pr("")
    pr(f"SUMMARY: brute_fail={b_bad}  deep_fail={d_bad}")

if __name__ == '__main__':
    main()

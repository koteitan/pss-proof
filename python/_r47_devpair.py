#!/usr/bin/env python3
"""r47 STEP-0: branch standardness by ST_PS-CONSTRUCTION (the right oracle)
+ the devpair witness recipe, for the packaged residual `devpair` of
dvx_devel_of_devpair / dvx_two_slots_of_devpair.

Checks, on deep-insertion applicable hosts M drawn from the oper closure of
diagSeq seeds (so M in ST_PS BY CONSTRUCTION):

 (i)   last (Br M) itself REACHABLE in the oper closure (raw), or after an
       IncrFirst DOWN-shift (witness N0 with IncrFirst^k N0 = branch; Trans
       is IncrFirst-invariant so Trans N0 = Trans branch) -- per branch.
 (ii)  readoff: Trans(last branch) == [deposit] (r46: 43/44, corner exception).
 (iii) corner (deposit == D_0 0_B): witness (0,0)(0,0) -- reachable + Trans.
 (iv)  devpair relation on the chosen witnesses: N == NP or N == oper(NP, m)
       (the DEVELOPMENT shape needed by dvx_devel_of_devpair).
 (v)   edge census: for closure edges M = M0[n] with Br M != [], how does
       last(Br M) relate to Br(M0) / to M0 (the mechanization recipe).
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, Br, diagSeq, oper, seg, Joints,
                       IncrFirst, funpow)
from trans_model import Trans, Pred
import buchholz as bu
from collections import deque

def P(*a): print(*a, flush=True)

class TO(Exception): pass
def _h(s, f): raise TO()
signal.signal(signal.SIGALRM, _h)
def safe(f, *a, budget=3):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TO, RecursionError, AssertionError, ValueError, IndexError,
            KeyError, RuntimeError):
        signal.alarm(0); return None

def bucOf(t):
    return [('D', p[1], bucOf(p[2])) for p in t[1]]

_tr_cache = {}
def trO(M):
    k = tuple(M)
    if k not in _tr_cache:
        t = safe(Trans, M, budget=4)
        _tr_cache[k] = None if t is None else bucOf(t)
    return _tr_cache[k]

def shift_down(M, k):
    if any(a < k for (a, b) in M): return None
    return [(a - k, b) for (a, b) in M]

seen = {}          # tuple -> derivation ('diag',u,v) | (parentkey, n)
edges = []         # (key0, n, key)

def add(M, drv):
    k = tuple(M)
    if k not in seen:
        seen[k] = drv
        return True
    return False

T0 = time.time()

def bfs(maxlen, nmax, tend, q, cap):
    while q and time.time() - T0 < tend and len(seen) < cap:
        M = q.popleft()
        k0 = tuple(M)
        for nn in range(1, nmax + 1):
            M2 = safe(oper, M, nn, budget=2)
            if M2 is None or M2 == M or Lng(M2) > maxlen: continue
            if add(M2, (k0, nn)):
                edges.append((k0, nn, tuple(M2)))
                q.append(M2)

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    starts = [diagSeq(u, u + d) for u in range(0, 8) for d in range(0, 7)]
    qA = deque()
    for s in starts:
        if add(s, ('diag', s[0][0], s[-1][0])): qA.append(s)
    bfs(8, 4, tmax * 0.28, qA, 60000)      # tier A: small deep closure
    nA = len(seen)
    qB = deque(list(map(list, seen.keys())))
    bfs(14, 3, tmax * 0.42, qB, 120000)    # tier B: bigger hosts
    P('pool: tierA=%d total=%d edges=%d  t=%.0fs'
      % (nA, len(seen), len(edges), time.time() - T0))

    S = dict(applic=0,
             br_raw=0, br_shift=0, br_miss=0,
             brp_raw=0, brp_shift=0, brp_miss=0,
             read_ok=0, read_corner=0, read_fail=0,
             shiftTrans_ok=0, shiftTrans_fail=0,
             corner_wit_ok=0, corner_wit_fail=0,
             pair_eq=0, pair_dev=0, pair_fail=0,
             eqhead=0)
    ex_miss, ex_read, ex_pair, ex_shift = [], [], [], []
    corner0 = tuple([(0, 0), (0, 0)])
    corner_in_pool = corner0 in seen
    tw0 = trO([(0, 0), (0, 0)])
    P('corner witness (0,0)(0,0): in-pool=%s drv=%s Trans=%s'
      % (corner_in_pool, seen.get(corner0), tw0))

    hosts = [list(k) for k in seen.keys() if 4 <= len(k) <= 14]
    random.Random(7).shuffle(hosts)
    tend_hosts = tmax * 0.80
    for M in hosts:
        if time.time() - T0 > tend_hosts: break
        if safe(monoT, M, budget=2) is not True: continue
        B = safe(Br, M, budget=2)
        if not B or not (Lng(M) - 1 > 1): continue
        PM = Pred(M); v0 = entry(M, 1, 0)
        TM = safe(Trans, M, budget=4); TPM = safe(Trans, PM, budget=4)
        if TM is None or TPM is None: continue
        if len(TM[1]) != 1 or len(TPM[1]) != 1: continue
        if TM[1][0][1] != v0 or TPM[1][0][1] != v0: continue
        listM = bucOf(TM[1][0][2]); listPM = bucOf(TPM[1][0][2])
        if len(listM) < 2: continue
        ps = listM[:-1]
        okshape = (len(listPM) == len(listM) and listPM[:-1] == ps
                   and listPM[-1][1] == listM[-1][1]) or (listPM == ps)
        if not okshape: continue
        S['applic'] += 1
        nb = len(B)
        dep = listM[-1]; prev = listM[-2]
        if dep[1] == prev[1]: S['eqhead'] += 1
        bl = B[-1]; blp = B[-2] if nb >= 2 else None

        def reach_tag(br):
            if tuple(br) in seen: return ('raw', 0)
            mr = min(a for (a, b) in br)
            for k in range(1, mr + 1):
                s = shift_down(br, k)
                if s is not None and tuple(s) in seen: return ('shift', k)
            return None
        rt = reach_tag(bl)
        if rt is None:
            S['br_miss'] += 1
            if len(ex_miss) < 8: ex_miss.append(('last', list(M), list(bl)))
        elif rt[0] == 'raw': S['br_raw'] += 1
        else:
            S['br_shift'] += 1
            s = shift_down(bl, rt[1])
            if trO(s) == trO(bl): S['shiftTrans_ok'] += 1
            else:
                S['shiftTrans_fail'] += 1
                if len(ex_shift) < 6: ex_shift.append((list(M), list(bl), rt[1]))
        if blp is not None:
            rtp = reach_tag(blp)
            if rtp is None:
                S['brp_miss'] += 1
                if len(ex_miss) < 8: ex_miss.append(('prev', list(M), list(blp)))
            elif rtp[0] == 'raw': S['brp_raw'] += 1
            else: S['brp_shift'] += 1

        tb = trO(bl)
        corner = (dep == ('D', 0, []))
        if tb is not None and tb == [dep]:
            S['read_ok'] += 1
            N = bl
        elif corner:
            S['read_corner'] += 1
            N = [(0, 0), (0, 0)]
            if corner_in_pool and tw0 == [dep]: S['corner_wit_ok'] += 1
            else: S['corner_wit_fail'] += 1
        else:
            S['read_fail'] += 1
            N = None
            if len(ex_read) < 6: ex_read.append((list(M), list(bl), dep, tb))
        NP = None
        if blp is not None:
            tbp = trO(blp)
            if tbp is not None and tbp == [prev]: NP = blp
            elif prev == ('D', 0, []): NP = [(0, 0), (0, 0)]

        if N is not None and NP is not None:
            if N == NP: S['pair_eq'] += 1
            else:
                hit = None
                for m in range(1, 9):
                    om = safe(oper, NP, m, budget=2)
                    if om is not None and om == N: hit = m; break
                if hit is not None: S['pair_dev'] += 1
                else:
                    S['pair_fail'] += 1
                    if len(ex_pair) < 8: ex_pair.append((list(M), list(N), list(NP)))

    P('==== r47 devpair STEP-0 ====')
    for k, v in S.items(): P('  %-16s = %d' % (k, v))
    if ex_miss:
        P('\n *** branch NOT reachable in closure (raw or shifted) ***')
        for e in ex_miss: P('   ', e)
    if ex_shift:
        P('\n *** shift witness Trans MISMATCH ***')
        for e in ex_shift: P('   ', e)
    if ex_read:
        P('\n *** readoff fail (non-corner) ***')
        for e in ex_read: P('   ', e)
    if ex_pair:
        P('\n *** devpair relation FAILED on witnesses ***')
        for e in ex_pair: P('   ', e)

    # (v) edge census (time-boxed, sampled)
    C = dict(edges_br=0, copy_last=0, copy_other=0, dev_last=0,
             from_branchless=0, other=0)
    ex_other = []
    es = list(edges)
    random.Random(9).shuffle(es)
    tend_census = tmax * 0.97
    for (k0, nn, k) in es:
        if time.time() - T0 > tend_census: break
        M0 = list(k0); M = list(k)
        if Lng(M) < 3: continue
        if safe(monoT, M, budget=2) is not True: continue
        BM = safe(Br, M, budget=2)
        if not BM: continue
        C['edges_br'] += 1
        bl = BM[-1]; B0 = safe(Br, M0, budget=2)
        if not B0:
            C['from_branchless'] += 1; continue
        if bl == B0[-1]: C['copy_last'] += 1; continue
        if bl in B0: C['copy_other'] += 1; continue
        hit = None
        for m in range(1, nn + 3):
            om = safe(oper, B0[-1], m, budget=2)
            if om == bl: hit = m; break
        if hit is not None: C['dev_last'] += 1; continue
        C['other'] += 1
        if len(ex_other) < 10: ex_other.append((M0, nn, M, bl, B0))
    P('\n==== edge census: last(Br M0[n]) vs Br M0 ====')
    for k, v in C.items(): P('  %-16s = %d' % (k, v))
    if ex_other:
        P('\n *** unexplained last-branch (recipe gap) ***')
        for e in ex_other:
            P('    M0=%s [n=%d] M=%s\n      lastBr=%s Br(M0)=%s'
              % (e[0], e[1], e[2], e[3], e[4]))

if __name__ == '__main__':
    main()

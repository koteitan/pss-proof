#!/usr/bin/env python3
"""r48 STEP-0: validate the IncrFirst-normalized-branch route for devchain.

On the EXACT eqhead deep-insertion frame (as _r47_devpair2.py):
 (S) claim S: EVERY branch b of Br M is (IncrFirst^^k)(N0) with N0 standard
     (k = entry(b,0,0)-entry(b,1,0), N0 = shift_down; oracle = BFS pool built
     from ST_PS construction, so membership is EXACT, misses are inconclusive).
 (T) transport sanity: Trans(norm(b)) == Trans(b).
 (W) witness recipe: N' = norm(B[-2]) (Trans == prev principal), and
     N = N' (eqdep) or N reachable from N' by a <=3-step oper chain with
     Trans N == deposit and Lng N < Lng M (devchain shape; intermediate
     lengths unconstrained).  Also read-off diagnosis at B[-1] (depth>=2).
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import Lng, entry, monoT, Br, diagSeq, oper
from trans_model import Trans, Pred
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

def frz(p):
    return (p[0], p[1], tuple(frz(c) for c in p[2]))

_tr_cache = {}
def trO(M):
    k = tuple(M)
    if k not in _tr_cache:
        t = safe(Trans, M, budget=3)
        _tr_cache[k] = None if t is None else bucOf(t)
    return _tr_cache[k]

def norm(b):
    """IncrFirst-normalization: down-shift so first column is diagonal."""
    if not b: return None
    k = b[0][0] - b[0][1]
    if k < 0 or any(a < k for (a, _) in b): return None
    return [(a - k, c) for (a, c) in b]

seen = {}
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
                q.append(M2)

def depthOf(p):
    """nesting depth of a principal ('D', v, body)"""
    if not p[2]: return 1
    return 1 + max(depthOf(c) for c in p[2])

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 280
    starts = [diagSeq(u, u + d) for u in range(0, 8) for d in range(0, 7)]
    qA = deque()
    for s in starts:
        if add(s, ('diag', s[0][0], s[-1][0])): qA.append(s)
    bfs(8, 4, tmax * 0.14, qA, 60000)
    nA = len(seen)
    qB = deque(list(map(list, seen.keys())))
    bfs(14, 3, tmax * 0.30, qB, 120000)
    P('pool: tierA=%d total=%d  t=%.0fs' % (nA, len(seen), time.time() - T0))

    S = dict(frame=0, eqhead=0, noneq=0, br1=0,
             # claim S bookkeeping (over eqhead frame hosts)
             S_br_total=0, S_br_pool=0, S_br_miss=0, S_norm_fail=0,
             T_ok=0, T_bad=0,
             # read-off diagnosis
             ro_last_ok=0, ro_last_bad=0, ro_prev_ok=0, ro_prev_bad=0,
             # witness recipe
             eqdep=0, eqdep_wit=0, eqdep_miss=0,
             strict=0, strict_wit=0, strict_miss=0)
    exS, exRO, exW = [], [], []
    chain_stats = {}
    depdist = {}

    hosts = [list(k) for k in seen.keys() if 4 <= len(k) <= 14]
    random.Random(7).shuffle(hosts)
    tend_hosts = tmax * 0.96
    for M in hosts:
        if time.time() - T0 > tend_hosts: break
        if safe(monoT, M, budget=2) is not True: continue
        B = safe(Br, M, budget=2)
        if not B or not (Lng(M) - 1 > 1): continue
        PM = Pred(M); v0 = entry(M, 1, 0)
        TM = safe(Trans, M, budget=3); TPM = safe(Trans, PM, budget=3)
        if TM is None or TPM is None: continue
        if len(TM[1]) != 1 or len(TPM[1]) != 1: continue
        if TM[1][0][1] != v0 or TPM[1][0][1] != v0: continue
        listM = bucOf(TM[1][0][2]); listPM = bucOf(TPM[1][0][2])
        if len(listM) < 2: continue
        ps = listM[:-1]
        if not (len(listPM) >= len(ps) and listPM[:len(ps)] == ps): continue
        S['frame'] += 1
        dep = listM[-1]; prev = listM[-2]
        if dep[1] != prev[1]:
            S['noneq'] += 1; continue
        S['eqhead'] += 1
        depdist[depthOf(dep)] = depdist.get(depthOf(dep), 0) + 1
        if len(B) < 2: S['br1'] += 1

        # ---- claim S + transport, ALL branches of this host
        for b in B:
            S['S_br_total'] += 1
            nb = norm(b)
            if nb is None:
                S['S_norm_fail'] += 1
                if len(exS) < 5: exS.append(('normfail', M, b))
                continue
            if tuple(nb) in seen: S['S_br_pool'] += 1
            else:
                S['S_br_miss'] += 1
                if len(exS) < 5: exS.append(('miss', M, b, nb))
            tb, tn = trO(b), trO(nb)
            if tb is not None and tb == tn: S['T_ok'] += 1
            else:
                S['T_bad'] += 1
                if len(exS) < 5: exS.append(('transport', M, b, nb, tb, tn))

        # ---- read-off diagnosis
        tl = trO(B[-1])
        if tl == [dep]: S['ro_last_ok'] += 1
        else:
            S['ro_last_bad'] += 1
            if len(exRO) < 4: exRO.append((M, 'last', dep, tl))
        if len(B) >= 2:
            tp = trO(B[-2])
            if tp == [prev]: S['ro_prev_ok'] += 1
            else:
                S['ro_prev_bad'] += 1
                if len(exRO) < 4: exRO.append((M, 'prev', prev, tp))

        # ---- witness recipe (devchain)
        LM = Lng(M)
        # candidate N' sources: norm(B[-2]), norm(B[-1]) -- must be in pool
        cands = []
        for tag, b in (('nB-2', B[-2] if len(B) >= 2 else None),
                       ('nB-1', B[-1])):
            if b is None: continue
            nb = norm(b)
            if nb is not None and tuple(nb) in seen and Lng(nb) < LM:
                cands.append((tag, nb))
        if dep == prev:
            S['eqdep'] += 1
            hit = None
            for tag, nb in cands:
                if trO(nb) == [dep]:
                    hit = tag; break
            if hit: S['eqdep_wit'] += 1; chain_stats[hit + '/eq'] = \
                chain_stats.get(hit + '/eq', 0) + 1
            else:
                S['eqdep_miss'] += 1
                if len(exW) < 5: exW.append(('eqdep', M, dep, [c[0] for c in cands]))
        else:
            S['strict'] += 1
            hit = None
            for tag, nb in cands:
                if trO(nb) != [prev]: continue
                # BFS <=3 oper steps from nb
                frontier = [(list(nb), ())]
                for step in range(3):
                    nxt = []
                    for K, path in frontier:
                        for n in range(1, 9):
                            K2 = safe(oper, K, n, budget=2)
                            if K2 is None or K2 == K: continue
                            if Lng(K2) < LM and trO(K2) == [dep]:
                                hit = (tag, path + (n,)); break
                            if Lng(K2) <= LM + 4 and len(nxt) < 40:
                                nxt.append((K2, path + (n,)))
                        if hit: break
                    if hit: break
                    frontier = nxt
                if hit: break
            if hit:
                S['strict_wit'] += 1
                key = hit[0] + '/dev' + str(len(hit[1]))
                chain_stats[key] = chain_stats.get(key, 0) + 1
            else:
                S['strict_miss'] += 1
                if len(exW) < 5: exW.append(('strict', M, prev, dep,
                                             [c[0] for c in cands]))

    P('==== r48 STEP-0: normalized-branch devchain route ====')
    for k, v in S.items(): P('  %-12s = %d' % (k, v))
    P('  depth dist of deposit:', depdist)
    P('  recipes:', chain_stats)
    if exS:
        P(' *** claim S / transport anomalies ***')
        for e in exS: P('   ', e)
    if exRO:
        P(' *** read-off failures (depth>=2 diagnosis) ***')
        for e in exRO: P('   ', e)
    if exW:
        P(' *** witness misses ***')
        for e in exW: P('   ', e)
    P('t=%.0fs' % (time.time() - T0))

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""r48 STEP-0 run 2: classify the 18 recipe-misses.  Ladder:
  L0 corner   : dep == prev == D_0 0  (closed by dpr_devpair_corner)
  L1 nB-2     : run-1 recipe at the host itself
  L2 descent  : recurse H := norm(last(Br H)) while the body of Trans H'
                still ENDS with [.., prev, dep] (frame-descent invariant);
                retry L0/L1 at each level
  L3 index    : any pool member with Trans == prev + <=3-step chain
                (devchain TRUTH check, no recipe)
Report per-level counts + the descent invariant hit-rate + unresolved.
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

def chain_to(dep, N0, LM, steps=3, nmax=10, cap=60):
    """BFS oper chain from N0; endpoint needs Lng < LM and Trans == [dep]."""
    if trO(N0) == [dep] and Lng(N0) < LM: return ()
    frontier = [(list(N0), ())]
    for _ in range(steps):
        nxt = []
        for K, path in frontier:
            for n in range(1, nmax + 1):
                K2 = safe(oper, K, n, budget=2)
                if K2 is None or K2 == K: continue
                if Lng(K2) < LM and trO(K2) == [dep]:
                    return path + (n,)
                if Lng(K2) <= LM + 4 and len(nxt) < cap:
                    nxt.append((K2, path + (n,)))
        frontier = nxt
    return None

def recipe_at(H, dep, prev, LM):
    """L1 recipe at host H: N' = norm(Br H[-2]) with Trans == prev,
    then eq or chain to dep."""
    B = safe(Br, H, budget=2)
    if not B or len(B) < 2: return None
    nb = norm(B[-2])
    if nb is None or tuple(nb) not in seen or Lng(nb) >= LM: return None
    if trO(nb) != [prev]: return None
    if dep == prev: return ('eq',)
    c = chain_to(dep, nb, LM)
    return None if c is None else ('dev', c)

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 280
    starts = [diagSeq(u, u + d) for u in range(0, 8) for d in range(0, 7)]
    qA = deque()
    for s in starts:
        if add(s, ('diag', s[0][0], s[-1][0])): qA.append(s)
    bfs(8, 4, tmax * 0.14, qA, 60000)
    qB = deque(list(map(list, seen.keys())))
    bfs(14, 3, tmax * 0.30, qB, 120000)
    P('pool: total=%d  t=%.0fs' % (len(seen), time.time() - T0))

    # Trans index for L3
    idx = {}
    keys = sorted(seen.keys(), key=lambda k: (len(k), k))
    tend_idx = tmax * 0.5
    for k in keys:
        if time.time() - T0 > tend_idx: break
        if len(k) > 12: continue
        t = trO(list(k))
        if t is not None and len(t) == 1:
            idx.setdefault(frz(t[0]), []).append(k)
    P('index done t=%.0fs' % (time.time() - T0))

    CNT = {}
    unresolved = []
    desc_inv_ok, desc_inv_bad = 0, 0

    hosts = [list(k) for k in seen.keys() if 4 <= len(k) <= 14]
    random.Random(7).shuffle(hosts)
    tend_hosts = tmax * 0.97
    nhost = 0
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
        dep = listM[-1]; prev = listM[-2]
        if dep[1] != prev[1]: continue
        nhost += 1
        LM = Lng(M)

        tag = None
        # L0 corner
        if dep == ('D', 0, []) and prev == dep:
            tag = 'L0-corner'
        # L1 at M
        if tag is None:
            r = recipe_at(M, dep, prev, LM)
            if r is not None: tag = 'L1-' + r[0]
        # L2 recursive descent
        if tag is None:
            H = M
            for lvl in range(1, 7):
                BH = safe(Br, H, budget=2)
                if not BH: break
                H2 = norm(BH[-1])
                if H2 is None: break
                t2 = trO(H2)
                if t2 is None or len(t2) != 1: break
                body2 = t2[0][2]
                if len(body2) >= 2 and body2[-1] == dep and body2[-2] == prev:
                    desc_inv_ok += 1
                else:
                    desc_inv_bad += 1
                    break
                if tuple(H2) not in seen: break   # claim S guard (pool oracle)
                # corner / L1 at H2
                if dep == ('D', 0, []) and prev == dep:
                    tag = 'L2-corner@%d' % lvl; break
                r = recipe_at(H2, dep, prev, LM)
                if r is not None:
                    tag = 'L2-%s@%d' % (r[0], lvl); break
                H = H2
        # L3 index fallback
        if tag is None:
            for kk in idx.get(frz(prev), []):
                if len(kk) >= LM: continue
                if dep == prev: tag = 'L3-eq'; break
                c = chain_to(dep, list(kk), LM)
                if c is not None: tag = 'L3-dev'; break
        if tag is None:
            tag = 'UNRESOLVED'
            if len(unresolved) < 6:
                unresolved.append((M, prev, dep))
        CNT[tag] = CNT.get(tag, 0) + 1

    P('==== r48 run2: recipe ladder on %d eqhead frame hosts ====' % nhost)
    for k in sorted(CNT): P('  %-14s = %d' % (k, CNT[k]))
    P('  descent invariant: ok=%d bad=%d' % (desc_inv_ok, desc_inv_bad))
    if unresolved:
        P(' *** UNRESOLVED ***')
        for e in unresolved: P('   ', e)
    P('t=%.0fs' % (time.time() - T0))

if __name__ == '__main__':
    main()

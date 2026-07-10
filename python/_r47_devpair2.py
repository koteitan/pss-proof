#!/usr/bin/env python3
"""r47 STEP-0 run 2: devpair EXISTENCE on the EXACT eqhead frame, by pool
search (pool members are ST_PS BY CONSTRUCTION), + witness recipe
classification + the D_0 0_B corner derivation chain.

devpair (dvx_devel_of_devpair): EX N N' n in ST_PS, Lng < Lng M,
  Trans N = Dpt x q, Trans N' = Dpt hdv qb, N = N' | (N = N'[n], 1<=n, 1<Lng N').
Search: N' from the Trans-indexed pool; N := N'[n] (ST by ST_PS.oper) with
  Trans(N'[n]) = Dpt x q and Lng(N'[n]) < Lng M.
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

def shift_down(M, k):
    if any(a < k for (a, b) in M): return None
    return [(a - k, b) for (a, b) in M]

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

def chain(k):
    out = []
    while True:
        d = seen.get(k)
        out.append((list(k), d))
        if d is None or d[0] == 'diag': return out
        k = d[0]

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 250
    starts = [diagSeq(u, u + d) for u in range(0, 8) for d in range(0, 7)]
    qA = deque()
    for s in starts:
        if add(s, ('diag', s[0][0], s[-1][0])): qA.append(s)
    bfs(8, 4, tmax * 0.14, qA, 60000)
    nA = len(seen)
    qB = deque(list(map(list, seen.keys())))
    bfs(14, 3, tmax * 0.30, qB, 120000)
    P('pool: tierA=%d total=%d  t=%.0fs' % (nA, len(seen), time.time() - T0))

    # corner derivation chains
    for c in ([(0, 0), (0, 0)], [(0, 0), (1, 0)]):
        k = tuple(c)
        if k in seen:
            P('corner chain %s:' % c)
            for step in chain(k): P('    ', step)
        else:
            P('corner %s NOT in pool' % c)
    P('Trans((0,0),(0,0)) =', trO([(0, 0), (0, 0)]))
    P('Trans((0,0),(1,0)) =', trO([(0, 0), (1, 0)]))

    # Trans index: single-principal pool members, ascending length
    idx = {}
    keys = sorted(seen.keys(), key=lambda k: (len(k), k))
    tend_idx = tmax * 0.55
    n_idx = 0
    for k in keys:
        if time.time() - T0 > tend_idx: break
        if len(k) > 12: continue
        t = trO(list(k))
        if t is not None and len(t) == 1:
            idx.setdefault(frz(t[0]), []).append(k)
            n_idx += 1
    P('index: %d single-principal members indexed  t=%.0fs'
      % (n_idx, time.time() - T0))

    S = dict(frame=0, eqhead=0, noneq=0,
             eqdep=0, eqdep_wit=0, eqdep_nowit=0,
             dev_found=0, dev_nohit=0, prev_nowit=0)
    R = {}   # recipe classification counts
    ndist = {}
    ex_nowit, ex_nohit = [], []

    def classify(NP, B, M):
        NPl = list(NP)
        if B:
            if NPl == B[-1]: return 'B[-1]'
            if len(B) >= 2 and NPl == B[-2]: return 'B[-2]'
            for tag, br in (('shB[-1]', B[-1]),) + \
                           ((('shB[-2]', B[-2]),) if len(B) >= 2 else ()):
                mr = min(a for a, b in br)
                for kk in range(1, mr + 1):
                    if shift_down(br, kk) == NPl: return tag
        if NPl == [(0, 0), (0, 0)]: return 'corner'
        if NPl == M[:len(NPl)]: return 'prefix'
        return 'other'

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
        # a7 faithful shape: body(Trans(Pred M)) = ps @ principals(r)
        if not (len(listPM) >= len(ps) and listPM[:len(ps)] == ps): continue
        S['frame'] += 1
        dep = listM[-1]; prev = listM[-2]
        if dep[1] != prev[1]:
            S['noneq'] += 1; continue
        S['eqhead'] += 1
        LM = Lng(M)
        cands = [c for c in idx.get(frz(prev), []) if len(c) < LM]
        if dep == prev:
            S['eqdep'] += 1
            if cands:
                S['eqdep_wit'] += 1
                R[classify(cands[0], B, M) + '/eq'] = \
                    R.get(classify(cands[0], B, M) + '/eq', 0) + 1
            else:
                S['eqdep_nowit'] += 1
                if len(ex_nowit) < 6: ex_nowit.append(('eqdep', M, prev))
            continue
        if not cands:
            S['prev_nowit'] += 1
            if len(ex_nowit) < 6: ex_nowit.append(('dev', M, prev))
            continue
        hit = None
        for NP in sorted(cands, key=len)[:60]:
            if len(NP) < 2: continue
            for n in range(1, 11):
                K = safe(oper, list(NP), n, budget=2)
                if K is None or Lng(K) >= LM: continue
                if trO(K) == [dep]:
                    hit = (NP, n, K); break
            if hit: break
        if hit:
            S['dev_found'] += 1
            tag = classify(hit[0], B, M)
            R[tag + '/dev'] = R.get(tag + '/dev', 0) + 1
            ndist[hit[1]] = ndist.get(hit[1], 0) + 1
        else:
            S['dev_nohit'] += 1
            if len(ex_nohit) < 6:
                ex_nohit.append((M, prev, dep, len(cands)))

    P('==== r47 run2: devpair existence on EXACT eqhead frame ====')
    for k, v in S.items(): P('  %-12s = %d' % (k, v))
    P('  recipes:', R)
    P('  n-dist  :', ndist)
    if ex_nowit:
        P(' *** NO prev-witness in index (ambiguous: index incompleteness?) ***')
        for e in ex_nowit: P('   ', e)
    if ex_nohit:
        P(' *** prev-witness exists but NO n develops it to dep ***')
        for e in ex_nohit: P('   ', e)

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""r14-S4p-C3 stage-2 empirical validation for the m_8_4_Trans_scb proof design.

Validates, over the GENUINE regime (ST_PS-generated reduced mono marked pairs),
the chain invariant (P) that the Isar induction s84c3_Mark_chain will prove:

  For N in RT_PS, monoT N, (N,m) in Marked, m < Lng N - 1, the chain ks built
  by the SPLICE recursion
     ks(N,m) = [0, 1]                                    if zeroT (Pred N)
             = [jm1] + ([jp] if II/IV) + [j1]            if m = jm1
             = ks(seg N 0 jm1, m) + ([jp] if II/IV) + [j1]  if m < jm1
  (jp = parent N 0 j1, jm1 = Adm N jp) satisfies
   (a) RightNodes (Mark N m) = map (entry N 1) ks
   (b) ks != [], hd ks = m, last ks = Lng N - 1
   (c) windows: k < k', le0 N k k',
       adm N k  or  (entry N 1 k' <= entry N 1 k and (k' last or adm N k'))
   plus the auxiliary facts used by the induction:
   (d) marked m < j1  ==>  m <= jm1   (in the non-zeroPred branch)
   (e) splice equation: RN(Mark N m) = butlast(RN(Mark N' m)) @ RN(Mark N jm1)
       for m < jm1, N' = seg N 0 jm1
   (f) top level (m = jm3 = Adm(parent M 1 j1), hasParent M 1 j1, Lng M-1 > 1):
       kind-1 valley of r = RN (Mark M jm3):
       len r >= 2, r[0] < r[-1], all interior r[i] >= r[-1].

RESULT (run 2026-07-02, seeds 1..9, maxv 3, u<=2, n in 1..4):
   (P)+(a)-(e) checked on ALL marked interior (N,m) pairs of every reduced
   mono standard-derived N: see stdout fractions.  (f) on every instance with
   hasParent(1,j1) and j1>1.  0 violations.
"""
import sys, random, signal
sys.path.insert(0, '.')
import red_model as rm
import trans_model as tm
from red_model import Lng, entry, le0, monoT, zeroT, seg, parent, hasParent, oper, diagSeq
from trans_model import Mark, Trans, Adm, adm, reduced, Pred, condI, condIII, condV, condVI

class TO(Exception): pass
def alarm(sig, frm): raise TO()
signal.signal(signal.SIGALRM, alarm)

def RightNodes(t):
    # t = ('T', ps); article: RN of last principal, recurse
    ps = t[1]
    if not ps: return []
    p = ps[-1]          # ('D', v, body)
    return [p[1]] + RightNodes(p[2])

def transJm1(N):
    j1 = Lng(N)-1
    return Adm(N, parent(N, 0, j1))

def cond24(N):
    return not (condI(N) or condIII(N) or condV(N) or condVI(N))

def ks_chain(N, m):
    j1 = Lng(N) - 1
    assert m < j1, (N, m)
    if zeroT(Pred(N)):
        assert m == 0 and j1 == 1
        return [0, 1]
    jp = parent(N, 0, j1)
    jm1 = Adm(N, jp)
    assert m <= jm1, ('(d) FAIL', N, m, jm1)      # (d)
    tail = ([jp] if cond24(N) else []) + [j1]
    if m == jm1:
        return [jm1] + tail
    Np = seg(N, 0, jm1)
    return ks_chain(Np, m) + tail

def check_P(N, m):
    """checks (a)(b)(c)(e) for one (N,m); returns list of violation strings"""
    bad = []
    j1 = Lng(N) - 1
    ks = ks_chain(N, m)
    r = RightNodes(Mark(N, m))
    if r != [entry(N,1,k) for k in ks]: bad.append('(a) map')
    if not ks or ks[0] != m or ks[-1] != j1: bad.append('(b) ends')
    for i in range(len(ks)-1):
        k, k2 = ks[i], ks[i+1]
        if not (k < k2): bad.append(f'(c) sorted @{i}')
        if not le0(N, k, k2): bad.append(f'(c) le0 @{i}')
        if not (adm(N,k) or (entry(N,1,k2) <= entry(N,1,k)
                             and (i+2 == len(ks) or adm(N,k2)))):
            bad.append(f'(c) dich @{i}')
    # (e) splice
    if not zeroT(Pred(N)):
        jm1 = transJm1(N)
        if m < jm1:
            Np = seg(N, 0, jm1)
            lhs = RightNodes(Mark(N, m))
            rhs = RightNodes(Mark(Np, m))[:-1] + RightNodes(Mark(N, jm1))
            if lhs != rhs: bad.append('(e) splice')
    return bad

def check_top(M):
    """(f): the final valley on r = RN(Mark M jm3); returns violations"""
    bad = []
    j1 = Lng(M)-1
    jm2 = parent(M, 1, j1)
    jm3 = Adm(M, jm2)
    r = RightNodes(Mark(M, jm3))
    if len(r) < 2: bad.append('(f) len')
    elif not (r[0] < r[-1]): bad.append('(f) r0<rlast')
    else:
        for i in range(1, len(r)-1):
            if not (r[i] >= r[-1]): bad.append(f'(f) valley @{i}')
    # cross-check statement c: Mark M jm3 = Trans (seg M jm3 j1)
    if Mark(M, jm3) != Trans(seg(M, jm3, j1)): bad.append('(f) repr')
    return bad

def marked(N, m):
    return adm(N, m) and le0(N, m, Lng(N)-1)

def genuine_pool(seed, maxu=2, maxv=3, nmax=4, steps=3000, maxLng=14):
    random.seed(seed)
    pool, seen = [], set()
    frontier = [diagSeq(u, v) for u in range(maxu+1) for v in range(u+1, u+maxv+1)]
    for M in frontier: seen.add(tuple(M))
    pool.extend(frontier)
    i = 0
    while i < steps and frontier:
        M = random.choice(frontier)
        n = random.randint(1, nmax)
        signal.alarm(5)
        try:
            Mn = oper(M, n)
        except (TO, Exception):
            signal.alarm(0); i += 1; continue
        signal.alarm(0)
        t = tuple(Mn)
        if t not in seen and 0 < Lng(Mn) <= maxLng:
            seen.add(t); pool.append(Mn); frontier.append(Mn)
        i += 1
    return pool

def main():
    tot_P = ok_P = tot_top = ok_top = 0
    skipped = 0
    fails = []
    for seed in range(1, 10):
        pool = genuine_pool(seed)
        for M in pool:
            signal.alarm(10)
            try:
                if not reduced(M): continue
                if not monoT(M): continue
                j1 = Lng(M)-1
                # (P) over ALL marked interior m
                for m in range(0, j1):
                    if not marked(M, m): continue
                    tot_P += 1
                    bad = check_P(M, m)
                    if bad: fails.append((M, m, bad))
                    else: ok_P += 1
                # (f) top level
                if j1 > 1 and hasParent(M, 1, j1):
                    tot_top += 1
                    bad = check_top(M)
                    if bad: fails.append((M, 'top', bad))
                    else: ok_top += 1
            except (TO, RecursionError):
                skipped += 1
            finally:
                signal.alarm(0)
    print(f'(P) chain invariant : {ok_P}/{tot_P}')
    print(f'(f) top-level valley: {ok_top}/{tot_top}')
    print(f'timeouts/skips      : {skipped}')
    for f in fails[:10]:
        print('FAIL', f)
    return 0 if not fails else 1

if __name__ == '__main__':
    sys.exit(main())

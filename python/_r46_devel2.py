#!/usr/bin/env python3
"""r46-devel STEP-0 run 2: reverse-index test of the devel residual.

Pool = oper-closure of diagSeq(u,v) starts (u<=v) => every member is ST_PS
BY CONSTRUCTION (SkT_PS = expansions of diagonals).  Index Trans-value ->
(min Lng, witness).  For each applicable deep-insertion host M:
  dep  = last body principal of Trans M   (Dpt x q)
  prev = second-to-last                    (Dpt hdv qb)
Check:
 (i)   dep in index with Lng < Lng M       [slice residual / EX-N half]
 (ii)  prev in index with Lng < Lng M      [EX-N' half]
 (iii) dep == prev  or  lt_term            [order half, value-level]
 (iv)  witness shapes: is the dep witness the last branch of M itself?
       is the found witness an oper-development of the prev witness?
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, monoT, Br, diagSeq, oper, seg, Joints, Red)
from trans_model import Trans, Pred
import buchholz as bu
from collections import deque

class TO(Exception): pass
def _h(s, f): raise TO()
signal.signal(signal.SIGALRM, _h)
def safe(f, *a, budget=6):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TO, RecursionError, AssertionError, ValueError, IndexError,
            KeyError, RuntimeError):
        signal.alarm(0); return None

def bucOf(t):
    return [('D', p[1], bucOf(p[2])) for p in t[1]]

def key(l):  # hashable form of a bucOf list
    return repr(l)

def gen(maxlen, tmax, seeds):
    seen = set(); t0 = time.time()
    starts = [diagSeq(u, u + d) for u in range(0, 7) for d in range(0, 7)]
    dq = deque()
    for s in starts:
        k = tuple(s)
        if k not in seen: seen.add(k); dq.append(s); yield s
    tb = t0 + tmax * 0.55
    while dq and time.time() < tb:
        M = dq.popleft()
        for nn in range(1, 5):
            M2 = safe(oper, M, nn, budget=2)
            if M2 is None or M2 == M or Lng(M2) > maxlen: continue
            k = tuple(M2)
            if k not in seen: seen.add(k); dq.append(M2); yield M2
    for sd in seeds:
        if time.time() - t0 > tmax: return
        rng = random.Random(sd)
        for s in starts:
            M = list(s)
            for _ in range(120):
                if time.time() - t0 > tmax: return
                nn = rng.randrange(1, 5)
                M2 = safe(oper, M, nn, budget=2)
                if M2 is None or M2 == M or Lng(M2) > maxlen: break
                M = M2; k = tuple(M)
                if k not in seen: seen.add(k); yield M

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    t0 = time.time()
    pool = []
    for M in gen(maxlen, tmax * 0.5, seeds=[7, 13]):
        pool.append(M)
        if time.time() - t0 > tmax * 0.5: break
    # index: Trans value -> (Lng, M) minimal Lng
    idx = {}
    poolset = set(tuple(m) for m in pool)
    for M in pool:
        t = safe(Trans, M, budget=4)
        if t is None: continue
        k = key(bucOf(t))
        if k not in idx or Lng(M) < idx[k][0]:
            idx[k] = (Lng(M), M)
    print('pool=%d indexed=%d  t=%.0fs' % (len(pool), len(idx), time.time() - t0))
    S = dict(applic=0, dep_found=0, dep_miss=0, prev_found=0, prev_miss=0,
             both_found=0, order_eq=0, order_lt=0, order_fail=0,
             wit_is_lastbr=0, wit_not_lastbr=0,
             eqhead=0, eqhead_ok=0, eqhead_miss=0)
    ex_dep_miss, ex_prev_miss, ex_order, ex_shape = [], [], [], []
    for M in pool:
        if time.time() - t0 > tmax: break
        if not monoT(M) or Br(M) == [] or not (Lng(M) - 1 > 1): continue
        PM = Pred(M)
        v0 = entry(M, 1, 0)
        TM = safe(Trans, M, budget=5); TPM = safe(Trans, PM, budget=5)
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
        dep = listM[-1]; prev = listM[-2]
        kd = key([dep]); kp = key([prev])
        wd = idx.get(kd); wp = idx.get(kp)
        dep_ok = wd is not None and wd[0] < Lng(M)
        prev_ok = wp is not None and wp[0] < Lng(M)
        S['dep_found' if dep_ok else 'dep_miss'] += 1
        S['prev_found' if prev_ok else 'prev_miss'] += 1
        if not dep_ok and len(ex_dep_miss) < 8:
            ex_dep_miss.append((list(M), str(dep)))
        if not prev_ok and len(ex_prev_miss) < 8:
            ex_prev_miss.append((list(M), str(prev)))
        if dep_ok and prev_ok:
            S['both_found'] += 1
            # order half at value level
            if dep == prev: S['order_eq'] += 1
            elif bu.lt_term([dep], [prev]): S['order_lt'] += 1
            else:
                S['order_fail'] += 1
                if len(ex_order) < 8:
                    ex_order.append((list(M), str(dep), str(prev)))
            # witness shape
            B = Br(M)
            if wd[1] == B[-1]: S['wit_is_lastbr'] += 1
            else:
                S['wit_not_lastbr'] += 1
                if len(ex_shape) < 8:
                    ex_shape.append((list(M), wd[1], wp[1]))
        if dep[1] == prev[1]:
            S['eqhead'] += 1
            if dep_ok and prev_ok: S['eqhead_ok'] += 1
            else:
                S['eqhead_miss'] += 1
    print('==== r46 devel STEP-0 run2 ====')
    for k, v in S.items(): print('  %-14s = %d' % (k, v))
    if ex_dep_miss:
        print('\n *** deposit value NOT in standard index (< Lng M) ***')
        for e in ex_dep_miss: print('   ', e)
    if ex_prev_miss:
        print('\n *** prev value NOT in standard index (< Lng M) ***')
        for e in ex_prev_miss: print('   ', e)
    if ex_order:
        print('\n *** ORDER HALF FAILED at value level ***')
        for e in ex_order: print('   ', e)
    if ex_shape:
        print('\n  witness pairs (dep-witness != last branch):')
        for e in ex_shape: print('   M=%s N=%s NP=%s' % (e[0], e[1], e[2]))

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""r45-SPINE: STEP-0 for spx_trailing_descent (leBT q qp) + wholebody value bound.

At a deep-insertion host M (monoT, Br!=[], Lng-1>1, Trans M / Trans(Pred M)
sharing head v0):
  listM  = body principals of Trans M      = ps @ [D_x q]
  listPM = body principals of Trans(Pred M)

Regimes:
  PPFX (proper prefix, keystone cases 3/4): listPM = ps @ [D_x qp]
  WB   (whole body, keystone cases 1/2):    listPM = ps          (fresh append)

Checks:
  (1) PPFX: leBT q qp?  split by eqhead (x == hdv where last ps = D_hdv qb)
      and by q == qp vs strict.
  (2) WB & eqhead: leBT q qb?
  (3) identification on every PPFX host:
      [D_x q]  == bucOf(Trans(seg M j0' (LngM-1)))?
      [D_x qp] == bucOf(Trans(seg PM j0'_P (LngPM-1)))?
      seg PM j0'_P .. == butlast(seg M j0' ..)?  (one-Pred-step geometry)

Corpus = r44_final generator: diagSeq + condV SEED_HOSTS + root-attached
nested-unit repeats [(0,0)]+U*k (yaBMS-verified genuine ST_PS), closed under
oper (BFS + deep random chains).
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, monoT, Br, diagSeq, oper, seg, Joints)
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
    except (TO, RecursionError, AssertionError, ValueError, IndexError, KeyError, RuntimeError):
        signal.alarm(0); return None

def bucOf(t):
    return [('D', p[1], bucOf(p[2])) for p in t[1]]

UNITS = [
 [(1,1),(2,1)],
 [(1,1),(2,2),(2,1)],
 [(1,1),(2,2),(3,1),(4,2)],
 [(1,1),(2,2),(3,1),(4,2),(4,2)],
 [(1,1),(2,2),(3,3),(4,1),(5,2)],
 [(1,1),(2,1),(3,1)],
 [(1,1),(2,2),(2,1),(3,1)],
 [(1,1),(2,2),(3,2)],
 [(1,1),(2,2),(3,1),(4,3)],
]
def repeat_seed(U, k): return [(0,0)] + U * k
SEED_HOSTS = [
 [(0,0),(1,1),(2,2),(3,1),(4,2),(4,2)],
 [(0,0),(1,1),(2,2),(3,1),(4,0),(5,1),(6,2),(7,0),(6,2)],
]

def gen(maxlen, tmax, seeds):
    seen = set(); t0 = time.time()
    starts = [diagSeq(u, u+d) for u in range(0, 7) for d in range(1, 7)]
    starts += [list(x) for x in SEED_HOSTS]
    for U in UNITS:
        for k in (2, 3, 4):
            s = repeat_seed(U, k)
            if Lng(s) <= maxlen: starts.append(s)
    dq = deque()
    for s in starts:
        k = tuple(s)
        if k not in seen: seen.add(k); dq.append(s); yield s
    tb = t0 + tmax * 0.5
    while dq and time.time() < tb:
        M = dq.popleft()
        for nn in range(1, 4):
            M2 = safe(oper, M, nn, budget=2)
            if M2 is None or M2 == M or Lng(M2) > maxlen: continue
            k = tuple(M2)
            if k not in seen: seen.add(k); dq.append(M2); yield M2
    for sd in seeds:
        if time.time() - t0 > tmax: return
        rng = random.Random(sd)
        for s in starts:
            M = list(s)
            for _ in range(90):
                if time.time() - t0 > tmax: return
                nn = rng.randrange(1, 4)
                M2 = safe(oper, M, nn, budget=2)
                if M2 is None or M2 == M or Lng(M2) > maxlen: break
                M = M2; k = tuple(M)
                if k not in seen: seen.add(k); yield M

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 18
    S = dict(pool=0, applic=0, ppfx=0, wb=0, othershape=0,
             ppfx_eq=0, ppfx_eq_pass=0, ppfx_eq_fail=0, ppfx_eq_refl=0,
             ppfx_ne=0, ppfx_ne_pass=0, ppfx_ne_fail=0, ppfx_ne_refl=0,
             wb_eq=0, wb_eq_pass=0, wb_eq_fail=0,
             id_dep=0, id_dep_fail=0, id_depP=0, id_depP_fail=0,
             id_geom=0, id_geom_fail=0)
    fails_ppfx, fails_wb, ex_id, ppfx_ex = [], [], [], []
    t0 = time.time()
    for M in gen(maxlen, tmax, seeds=[11, 22, 33]):
        if time.time() - t0 > tmax: break
        S['pool'] += 1
        if not monoT(M) or Br(M) == [] or not (Lng(M) - 1 > 1): continue
        PM = Pred(M)
        v0 = entry(M, 1, 0)
        TM = safe(Trans, M, budget=5); TPM = safe(Trans, PM, budget=5)
        if TM is None or TPM is None: continue
        if len(TM[1]) != 1 or len(TPM[1]) != 1: continue
        if TM[1][0][1] != v0 or TPM[1][0][1] != v0: continue
        listM = bucOf(TM[1][0][2]); listPM = bucOf(TPM[1][0][2])
        if len(listM) < 2: continue
        S['applic'] += 1
        ps = listM[:-1]
        x, q = listM[-1][1], listM[-1][2]
        hdv, qb = ps[-1][1], ps[-1][2]
        eqhead = (x == hdv)
        if len(listPM) == len(listM) and listPM[:-1] == ps and listPM[-1][1] == x:
            S['ppfx'] += 1
            qp = listPM[-1][2]
            ok = bu.le_term(q, qp)
            key = 'ppfx_eq' if eqhead else 'ppfx_ne'
            S[key] += 1
            S[key + ('_pass' if ok else '_fail')] += 1
            if q == qp: S[key + '_refl'] += 1
            if not ok and len(fails_ppfx) < 12:
                fails_ppfx.append((list(M), eqhead, x, bu.fmt(q), bu.fmt(qp)))
            if len(ppfx_ex) < 5 and q != qp:
                ppfx_ex.append((list(M), eqhead, x, bu.fmt(q), bu.fmt(qp), ok))
            # identification probe on EVERY ppfx host
            J = Joints(M); B = Br(M)
            if J and B:
                j0p = J[len(B) - 1]
                sl = seg(M, j0p, Lng(M) - 1)
                TS = safe(Trans, sl, budget=5)
                if TS is not None:
                    S['id_dep'] += 1
                    if bucOf(TS) != [listM[-1]]:
                        S['id_dep_fail'] += 1
                        if len(ex_id) < 8:
                            ex_id.append(('dep', list(M), bu.fmt(bucOf(TS)), x, bu.fmt(q)))
                JP = Joints(PM); BP_ = Br(PM)
                if JP and BP_:
                    j0pP = JP[len(BP_) - 1]
                    slP = seg(PM, j0pP, Lng(PM) - 1)
                    S['id_geom'] += 1
                    if slP != sl[:-1]:
                        S['id_geom_fail'] += 1
                        if len(ex_id) < 8:
                            ex_id.append(('geom', list(M), slP, sl[:-1]))
                    TSP = safe(Trans, slP, budget=5)
                    if TSP is not None:
                        S['id_depP'] += 1
                        if bucOf(TSP) != [listPM[-1]]:
                            S['id_depP_fail'] += 1
                            if len(ex_id) < 8:
                                ex_id.append(('depP', list(M), bu.fmt(bucOf(TSP)), bu.fmt(qp)))
        elif listPM == ps:
            S['wb'] += 1
            if eqhead:
                S['wb_eq'] += 1
                ok = bu.le_term(q, qb)
                S['wb_eq_pass' if ok else 'wb_eq_fail'] += 1
                if not ok and len(fails_wb) < 12:
                    fails_wb.append((list(M), x, bu.fmt(q), bu.fmt(qb)))
        else:
            S['othershape'] += 1
    print('==== r45 spine STEP-0 (corpus r44-final) ====')
    for k, v in S.items(): print('  %-16s = %d' % (k, v))
    if fails_ppfx:
        print('\n *** PPFX descent FAILURES (leBT q qp false) ***')
        for f in fails_ppfx: print('   M=%s eqhead=%s x=%d q=%s qp=%s' % f)
    else:
        print('\n  PPFX: leBT q qp held everywhere (both eqhead and non-eqhead).')
    if fails_wb:
        print('\n *** WB eqhead FAILURES (leBT q qb false) ***')
        for f in fails_wb: print('   M=%s x=%d q=%s qb=%s' % f)
    else:
        print('\n  WB eqhead: leBT q qb held everywhere.')
    if ppfx_ex:
        print('\n  strict PPFX examples (q != qp):')
        for e in ppfx_ex: print('   M=%s eqhead=%s x=%d q=%s qp=%s le=%s' % e)
    if ex_id:
        print('\n  identification anomalies:')
        for e in ex_id: print('   ', e)

if __name__ == '__main__':
    main()

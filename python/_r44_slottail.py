#!/usr/bin/env python3
"""r44-SLOTTAIL: FALSENESS CHECK of stx_slotTail (the equal-head tail descent,
C2 core of rgx_Trans_preserves_OT_of_slots).

stx_slotTail (all premises must hold):
  M in ST_PS, monoT M, Br M != [], Lng M - 1 > 1,
  IH: N in ST_PS, Lng N < Lng M => Trans N in OT_B,
  Trans(Pred M) in OT_B,
  Trans(Pred M) = D_{v0}(Trm ps +_B r),
  Trans M      = D_{v0}(Trm ps +_B D_x q),
  ps != [], last ps = D_hdv qb, x = hdv
  ==> leBT q qb.

Because a8 fixes ps = butlast(bodyM), (x,q) = last(bodyM) UNIQUELY, and a7
needs ps to be a PREFIX of bodyPM (else no witness r -> vacuous), the check is:
  for a genuine deep monoT ST_PS host M, in the EQUAL-HEAD case (x == hdv),
  does leBT q qb hold?  This is exactly the descP condition on the last two
  principals of Trans M's body.  Special hunt: BRANCH-PREFIX = qb != 0_B
  (last ps is a nested branch principal, not a leaf).

Deep corpus = oper-orbit BFS from diagSeq(u,v) seeds INCLUDING u>0, intermediate
Lng >= DEEPMIN (default 14).  ST_PS is closed under diagSeq + oper by definition,
so every host is genuinely in ST_PS (no yaBMS needed).
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, monoT, Br, diagSeq, oper)
import red_model as rm
from trans_model import Trans, Pred, ZB
import buchholz as bu

class TimeoutErr(Exception): pass
def _handler(s, f): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)
def safe(f, *a, budget=8):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TimeoutErr, RecursionError, AssertionError, ValueError, IndexError, KeyError, RuntimeError):
        signal.alarm(0); return None

def bucOf(t):   # trans_model BT ('T',[...]) -> buchholz principal-list
    return [('D', p[1], bucOf(p[2])) for p in t[1]]

def check_slottail(M):
    """Return a dict describing the slotTail instance at host M, or None if N/A."""
    if not monoT(M): return None
    if Br(M) == []: return None
    if not (Lng(M) - 1 > 1): return None
    v0 = entry(M, 1, 0)
    TM = safe(Trans, M, budget=6)
    TPM = safe(Trans, Pred(M), budget=6)
    if TM is None or TPM is None: return None
    if len(TM[1]) != 1 or len(TPM[1]) != 1: return {'shape': False}
    pM, pPM = TM[1][0], TPM[1][0]
    if pM[1] != v0 or pPM[1] != v0: return {'shape': False}
    listM = bucOf(pM[2])      # body principals of Trans M
    listPM = bucOf(pPM[2])    # body principals of Trans(Pred M)
    if len(listM) < 2:        # need ps != [] i.e. >=2 principals
        return {'na': 'shortbody'}
    ps = listM[:-1]
    x, q = listM[-1][1], listM[-1][2]        # D_x q  (q is buchholz term = list)
    hdv, qb = ps[-1][1], ps[-1][2]           # last ps = D_hdv qb
    prefixok = (listPM[:len(ps)] == ps)      # a7 witness exists?
    eqhead = (x == hdv)
    branch = (qb != [])                      # branch-prefix: qb != 0_B
    # slotTail conclusion:
    leq = bu.le_term(q, qb)                  # leBT q qb
    # also verify Trans M in OT (the descP part that slotTail is an instance of):
    otM = safe(lambda: bu.in_OT(listM), budget=6)
    # a6: Trans(Pred M) in OT_B
    otPM = safe(lambda: bu.in_OT(listPM), budget=6)
    return {'prefixok': prefixok, 'eqhead': eqhead, 'branch': branch,
            'leq': leq, 'otM': otM, 'otPM': otPM,
            'ps': ps, 'x': x, 'q': q, 'hdv': hdv, 'qb': qb}

def gen_deep(rng, tmax, maxlen=20, nmax=3, steps=60, umax=6, dmax=7):
    """BFS over the oper-graph from diagSeq(u,v) seeds (u>=0), bounded by maxlen.
    Exhaustive up to the size bound -> best coverage for a falseness hunt."""
    t0 = time.time(); seen = set()
    from collections import deque
    starts = [diagSeq(u, u+d) for u in range(0, umax) for d in range(1, dmax)]
    dq = deque()
    for s in starts:
        k = tuple(s)
        if k not in seen:
            seen.add(k); dq.append(s)
            if 1 < Lng(s) <= maxlen: yield s
    while dq and time.time() - t0 < tmax:
        M = dq.popleft()
        for nn in range(1, nmax+1):
            M2 = safe(oper, M, nn, budget=2)
            if M2 is None or M2 == M or Lng(M2) > maxlen: continue
            k = tuple(M2)
            if k not in seen:
                seen.add(k); dq.append(M2)
                if 1 < Lng(M2) <= maxlen: yield M2
        if time.time() - t0 >= tmax: break

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    deepmin = int(sys.argv[2]) if len(sys.argv) > 2 else 14
    seeds = [int(s) for s in sys.argv[3:]] or [11,22,33,44,55,66,77,88,99,111]
    per = tmax // max(len(seeds), 1)
    S = {'pool':0, 'applic':0, 'eqhead':0, 'eqhead_deep':0,
         'eqhead_branch':0, 'eqhead_branch_deep':0,
         'eqhead_leaf':0, 'st_pass':0, 'st_fail':0,
         'prefix_ok':0, 'prefix_ok_eqhead':0, 'prefix_ok_eqhead_pass':0,
         'otM_fail':0, 'branchpref_pass':0, 'branchpref_fail':0,
         'shortbody':0, 'shape_fail':0}
    fails = []           # slotTail failures (leBT q qb false at equal head)
    otM_fail_ex = []
    branch_examples = []
    for sd in seeds:
        rng = random.Random(sd); t0 = time.time()
        for M in gen_deep(rng, per):
            if time.time()-t0 > per: break
            S['pool'] += 1
            deep = Lng(M) >= deepmin
            r = check_slottail(M)
            if r is None: continue
            if r.get('shape') is False:
                S['shape_fail'] += 1; continue
            if r.get('na') == 'shortbody':
                S['shortbody'] += 1; continue
            S['applic'] += 1
            if r['otM'] is False:
                S['otM_fail'] += 1
                if len(otM_fail_ex) < 8: otM_fail_ex.append(list(M))
            if r['prefixok']:
                S['prefix_ok'] += 1
            if r['eqhead']:
                S['eqhead'] += 1
                if deep: S['eqhead_deep'] += 1
                if r['branch']:
                    S['eqhead_branch'] += 1
                    if deep: S['eqhead_branch_deep'] += 1
                    if len(branch_examples) < 6:
                        branch_examples.append((list(M), r['x'], r['q'], r['qb'], r['leq']))
                else:
                    S['eqhead_leaf'] += 1
                # slotTail conclusion at equal head:
                if r['leq']:
                    S['st_pass'] += 1
                    if r['branch']: S['branchpref_pass'] += 1
                else:
                    S['st_fail'] += 1
                    if r['branch']: S['branchpref_fail'] += 1
                    fails.append((list(M), r['x'], r['q'], r['qb'],
                                  r['prefixok'], r['otM'], r['otPM'], r['branch']))
                if r['prefixok']:
                    S['prefix_ok_eqhead'] += 1
                    if r['leq']: S['prefix_ok_eqhead_pass'] += 1
        print('  [seed %d] pool=%d applic=%d eqhead=%d(branch=%d) st_pass=%d st_fail=%d otMfail=%d'
              % (sd, S['pool'], S['applic'], S['eqhead'], S['eqhead_branch'],
                 S['st_pass'], S['st_fail'], S['otM_fail']), flush=True)
    print('\n==== r44 slotTail falseness check ====')
    for k in ['pool','applic','shortbody','shape_fail','prefix_ok',
              'eqhead','eqhead_deep','eqhead_branch','eqhead_branch_deep','eqhead_leaf',
              'st_pass','st_fail','prefix_ok_eqhead','prefix_ok_eqhead_pass',
              'branchpref_pass','branchpref_fail','otM_fail']:
        print('  %-22s = %d' % (k, S[k]))
    print('\n  branch-prefix equal-head examples (M, x, q, qb, leBT q qb):')
    for ex in branch_examples:
        print('    ', ex)
    if fails:
        print('\n  *** SLOTTAIL FAILURES (leBT q qb FALSE at equal head) ***')
        for M, x, q, qb, pfx, otM, otPM, br in fails[:20]:
            print('    M=%s x=%d q=%s qb=%s prefixok=%s otM=%s otPM=%s branch=%s'
                  % (M, x, bu.fmt(q), bu.fmt(qb), pfx, otM, otPM, br))
    else:
        print('\n  NO SLOTTAIL FAILURES: leBT q qb held in every equal-head instance.')
    if otM_fail_ex:
        print('\n  (Trans M not in OT examples -- separate diagnostic:)')
        for m in otM_fail_ex: print('    ', m)

if __name__ == '__main__':
    main()

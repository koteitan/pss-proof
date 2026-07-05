#!/usr/bin/env python3
"""r39-OTKEY: DEEP validation of the exact resid and multiD/comple statements
(the surgery keystone {resid, multiD} the entire OT pillar rests on).

resid (per keystone M in ST_PS, monoT, Br!=[], Lng-1>1):
  with v0 = entry M 1 0, body_M = principals under the outer D_v0 of Trans M,
  body_PM likewise for Trans(Pred M):
    ps = body_M[:-1],  D_x q = body_M[-1].
  Provided body_PM starts with ps  (the keystone prefix guarantee), verify
    (1) isOT_BP (D_x q)
    (2) ps != [] -> leBT (D_x q) (Trm[last ps])
    (3) forall y in GBT v0 (Trm(ps@[D_x q])). lessBT y (Trm(ps@[D_x q]))

multiD (per N in ST_PS, multiT, drop(Pcut N) != [(0,0)]):
  as = principals of Trans(take Pcut N), bs = principals of Trans(drop Pcut N);
  as,bs != [] -> leBT (Trm[hd bs]) (Trm[last as]).
comple (its reduction):  leBT (Trans(drop Pcut N)) (Trans(P N[-2])).

DEEP corpus: oper-orbit BFS from diagSeq seeds, requiring intermediate
Lng >= DEEPMIN (default 12), exceeding plausible CEX oper-depth (r37 lesson).
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, parent, oper, seg, diagSeq, monoT, zeroT, P, Br)
import red_model as rm
from trans_model import (Trans, Pred, ZB)
import buchholz as bu

class TimeoutErr(Exception): pass
def _handler(s, f): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)
def safe(f, *a, budget=6):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TimeoutErr, RecursionError, AssertionError, ValueError, IndexError, KeyError):
        signal.alarm(0); return None

def bucOf(t):   # BT tuple -> buchholz principal-list
    return [('D', p[1], bucOf(p[2])) for p in t[1]]

def Pcut(M):
    comps = P(M)
    return Lng(M) - Lng(comps[-1])

# ---------- resid check ----------
def check_resid(M):
    """returns dict of per-conjunct pass/fail, or None if inapplicable/timeout."""
    if not monoT(M): return None
    if Br(M) == []: return None
    if not (Lng(M) - 1 > 1): return None
    v0 = entry(M, 1, 0)
    TM = safe(Trans, M, budget=8)
    TPM = safe(Trans, Pred(M), budget=8)
    if TM is None or TPM is None: return None
    # both must be single outer principal D_v0 (...)
    if len(TM[1]) != 1 or len(TPM[1]) != 1: return {'shape': False}
    pM, pPM = TM[1][0], TPM[1][0]
    if pM[1] != v0 or pPM[1] != v0: return {'shape': False}
    bodyM = pM[2]; bodyPM = pPM[2]
    listM = bucOf(bodyM)          # buchholz principal list
    listPM = bucOf(bodyPM)
    if not listM: return {'shape': 'emptybody'}
    ps = listM[:-1]
    lastp = listM[-1]             # ('D', x, q_buc)
    x, q = lastp[1], lastp[2]
    prefixok = (listPM[:len(ps)] == ps)
    if not prefixok:
        return {'prefix': False}   # no witness -> resid vacuous here; track separately
    # conjunct 1: isOT_BP (D_x q)
    c1 = bu.in_OT([('D', x, q)])
    # conjunct 2
    if ps:
        c2 = bu.le_term([('D', x, q)], [ps[-1]])
    else:
        c2 = True
    # conjunct 3
    body = ps + [('D', x, q)]
    c3 = bu.G_lt(v0, body, body)
    return {'prefix': True, 'c1': c1, 'c2': c2, 'c3': c3,
            'all': (c1 and c2 and c3)}

# ---------- multiD / comple check ----------
def check_multiD(N):
    if not rm.multiT(N): return None
    if not (Lng(N) > 1): return None
    c = Pcut(N)
    bJ = seg(N, c, Lng(N)-1)      # drop c N
    pre = seg(N, 0, c-1)          # take c N
    if bJ == [(0,0)]: return None  # junction free
    TA = safe(Trans, pre, budget=8)
    TB = safe(Trans, bJ, budget=8)
    if TA is None or TB is None: return None
    aslist = bucOf(TA); bslist = bucOf(TB)
    if not aslist or not bslist: return None
    # multiD: leBT(Trm[hd bs], Trm[last as])
    md = bu.le_term([bslist[0]], [aslist[-1]])
    # comple: leBT(Trans bJ, Trans(P N[-2]))
    comps = P(N)
    if len(comps) < 2: return None
    bJm1 = comps[-2]
    TBm1 = safe(Trans, bJm1, budget=8)
    if TBm1 is None: return None
    comple = bu.le_term(bucOf(TB), bucOf(TBm1))
    # also: are the two component HEADS equal? (claimed always)
    headeq = (bslist[0][1] == aslist[-1][1])
    return {'multiD': md, 'comple': comple, 'headeq': headeq}

# ---------- deep corpus generator ----------
def gen_deep(rng, tmax, deepmin, maxlen=40, nmax=5, steps=40):
    t0 = time.time(); seen = set()
    starts = [diagSeq(u, u+d) for u in range(0, 6) for d in range(1, 6)]
    rng.shuffle(starts)
    idx = 0
    while time.time() - t0 < tmax:
        if idx < len(starts):
            M = starts[idx]; idx += 1
        else:
            u = rng.randrange(0, 6); vv = u + rng.randrange(1, 6)
            M = diagSeq(u, vv)
        for _ in range(steps):
            key = tuple(M)
            if key not in seen and 1 < Lng(M) <= maxlen:
                seen.add(key)
                yield M
            nn = rng.randrange(1, nmax+1)
            M2 = safe(oper, M, nn, budget=1)
            if M2 is None or M2 == M or Lng(M2) > maxlen: break
            M = M2

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    deepmin = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    seeds = [int(s) for s in sys.argv[3:]] or [11,22,33,44,55,66,77,88]
    per = tmax // max(len(seeds), 1)
    # resid stats
    R = {'tot':0,'shape_fail':0,'prefix_fail':0,'applic':0,'c1':0,'c2':0,'c3':0,'all':0,
         'deep_applic':0,'deep_all':0}
    Rfail = []
    # multiD stats
    Mst = {'tot':0,'md':0,'comple':0,'headeq':0,'deep_tot':0,'deep_md':0,'deep_comple':0}
    Mfail = []
    pool = 0
    for sd in seeds:
        rng = random.Random(sd); t0 = time.time()
        for M in gen_deep(rng, per, deepmin):
            if time.time()-t0 > per: break
            pool += 1
            deep = Lng(M) >= deepmin
            r = check_resid(M)
            if r is not None:
                R['tot'] += 1
                if r.get('shape') is False: R['shape_fail'] += 1; Rfail.append(('shape',list(M)))
                elif r.get('prefix') is False: R['prefix_fail'] += 1
                elif 'all' in r:
                    R['applic'] += 1
                    if r['c1']: R['c1'] += 1
                    if r['c2']: R['c2'] += 1
                    if r['c3']: R['c3'] += 1
                    if r['all']: R['all'] += 1
                    else: Rfail.append((tuple(k for k in ('c1','c2','c3') if not r[k]), list(M)))
                    if deep:
                        R['deep_applic'] += 1
                        if r['all']: R['deep_all'] += 1
            md = check_multiD(M)
            if md is not None:
                Mst['tot'] += 1
                if md['multiD']: Mst['md'] += 1
                else: Mfail.append(('md', list(M)))
                if md['comple']: Mst['comple'] += 1
                else: Mfail.append(('comple', list(M)))
                if md['headeq']: Mst['headeq'] += 1
                if deep:
                    Mst['deep_tot'] += 1
                    if md['multiD']: Mst['deep_md'] += 1
                    if md['comple']: Mst['deep_comple'] += 1
        print('  [seed %d] pool=%d resid: applic=%d/all=%d (deep %d/%d) | multiD tot=%d md=%d comple=%d headeq=%d'
              % (sd, pool, R['applic'], R['all'], R['deep_applic'], R['deep_all'],
                 Mst['tot'], Mst['md'], Mst['comple'], Mst['headeq']), flush=True)
    print('\n==== RESID ====')
    print('  keystone samples tot   =', R['tot'])
    print('  shape_fail (not D_v0)  =', R['shape_fail'])
    print('  prefix_fail (vacuous)  =', R['prefix_fail'])
    print('  applicable (prefix ok) =', R['applic'])
    print('  c1(newOT)  pass = %d/%d' % (R['c1'], R['applic']))
    print('  c2(dstep)  pass = %d/%d' % (R['c2'], R['applic']))
    print('  c3(gbt)    pass = %d/%d' % (R['c3'], R['applic']))
    print('  ALL three  pass = %d/%d' % (R['all'], R['applic']))
    print('  DEEP(>=%d) ALL  = %d/%d' % (deepmin, R['deep_all'], R['deep_applic']))
    if Rfail:
        print('  RESID FAILURES (first 12):')
        for tag, M in Rfail[:12]:
            print('    ', tag, M)
    else:
        print('  NO RESID FAILURES.')
    print('\n==== MULTID / COMPLE ====')
    print('  multiT samples tot =', Mst['tot'])
    print('  multiD pass  = %d/%d   (deep %d/%d)' % (Mst['md'], Mst['tot'], Mst['deep_md'], Mst['deep_tot']))
    print('  comple pass  = %d/%d   (deep %d/%d)' % (Mst['comple'], Mst['tot'], Mst['deep_comple'], Mst['deep_tot']))
    print('  headeq       = %d/%d' % (Mst['headeq'], Mst['tot']))
    if Mfail:
        print('  MULTID FAILURES (first 12):')
        for tag, M in Mfail[:12]:
            print('    ', tag, M)
    else:
        print('  NO MULTID/COMPLE FAILURES.')

if __name__ == '__main__':
    main()

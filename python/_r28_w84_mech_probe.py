#!/usr/bin/env python3
"""r28-WIRE84 probe 3: per-host MECHANISM cross-tab for the condIII tail-share.

For each analysis unit (X, a, q) with a = jm3-analogue <= q = jm2:
  VEM : X = Pred M,  a = jm3, q = jm2   (endpoint Lng M - 2)
  VEL : X = L1,      a = Adm(L1,jm2), q = jm2
  D4B : X = M,       a = jm3, q = jm2   (endpoint Lng M - 1)
mechanisms for  bpHeadT(Trans(seg X a end)) = bpHeadT(Trans(seg X q end)):
  (i)  hostreg  : cfbx_reg q X            (host-level double application)
  (ii) slicereg : cfbx_reg (q-a) S, S = seg X a (Lng X - 1)  (incl. S reduced)
mech coverage = (i) or (ii); report per-conjunct failures of (ii) and the
uncovered hosts.  Corpus: genuine ST_PS pool condIII (cached), deep included.
"""
import sys, pickle, os
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, seg, monoT, parent, hasParent,
                       fmt, Br, FirstNodes, Joints, TrMax, zeroT)
from red_model import reduced
from _r15_vx_lib import Trans, gen_pool, condIII
from trans_model import bpHeadT, Adm, Pred

CACHE = '/tmp/claude-1000/-home-koteitan-proofs-pss-proof/8b6b910e-60c9-4662-aff1-4806ad270a61/scratchpad/w84_pool.pkl'

def pr(*a):
    print(*a); sys.stdout.flush()

def descending(Q):
    n = len(Q)
    for J0 in range(n):
        for J1 in range(J0, n):
            a0, a1 = Q[J0][0][0], Q[J1][0][0]
            if not (a0 >= a1): return False
            if a0 == a1 and not (Q[J0][0][1] >= Q[J1][0][1]): return False
    return True

def mcond(X, m):
    b = Br(X)
    if not b: return False
    J1 = len(b) - 1
    j0p = Joints(X)[J1]
    if j0p is None: return False
    if m < j0p: return True
    j1p = FirstNodes(X)[J1]
    return m == j0p and entry(X, 0, j1p) == entry(X, 1, j1p) and descending(b)

def hostreg(X, q):
    # X assumed reduced monoT for our hosts; check anyway
    return reduced(X) and monoT(X) and (not zeroT(X)) and mcond(X, q)

def slicereg_report(X, a, q):
    S = seg(X, a, Lng(X)-1)
    r = {}
    r['red'] = reduced(S)
    r['mono'] = (not zeroT(S)) and monoT(S)
    r['brne'] = len(Br(S)) > 0
    r['mc'] = mcond(S, q - a)
    r['ok'] = r['red'] and r['mono'] and r['brne'] and r['mc']
    return r

def jm2f(M): return parent(M, 1, Lng(M)-1)
def L1f(M):  return Pred(M) + [(entry(M, 0, Lng(M)-1), entry(M, 1, jm2f(M)))]

def in_shape(M):
    if Lng(M) < 4: return False
    if not monoT(M): return False
    if not hasParent(M, 1, Lng(M)-1): return False
    if not (1 < Lng(M)-1): return False
    j2 = jm2f(M)
    if j2 is None: return False
    if not (j2 + 1 < Lng(M)-1): return False
    return True

def get_corpus():
    if os.path.exists(CACHE):
        with open(CACHE, 'rb') as f:
            return pickle.load(f)
    pool = gen_pool(maxlen=9, maxn=4, maxseed=3, cap=4000, oper_budget=2)
    seen = set(); H = []
    for M in pool:
        k = tuple(M)
        if k in seen: continue
        seen.add(k)
        if in_shape(M) and reduced(M) and condIII(M):
            H.append(M)
    with open(CACHE, 'wb') as f:
        pickle.dump(H, f)
    return H

UNITS = ('VEM', 'VEL', 'D4B')

if __name__ == '__main__':
    H = get_corpus()
    pr(f"corpus: {len(H)} condIII hosts (deep {sum(1 for M in H if Lng(M)>=9)})")
    tot = 0
    st = {u: {'host': 0, 'slice': 0, 'both': 0, 'either': 0,
              'sl_red': 0, 'sl_mono': 0, 'sl_brne': 0, 'sl_mc': 0} for u in UNITS}
    uncov = {u: [] for u in UNITS}
    slfail_when_needed = {u: {} for u in UNITS}   # failing conjuncts when host fails
    for M in H:
        tot += 1
        n = Lng(M)
        j2 = jm2f(M); j3 = Adm(M, j2)
        Lh = L1f(M); aL = Adm(Lh, j2)
        for u, (X, a, q) in (('VEM', (Pred(M), j3, j2)),
                             ('VEL', (Lh, aL, j2)),
                             ('D4B', (M, j3, j2))):
            hr = hostreg(X, q)
            sr = slicereg_report(X, a, q)
            if hr: st[u]['host'] += 1
            if sr['ok']: st[u]['slice'] += 1
            if hr and sr['ok']: st[u]['both'] += 1
            if hr or sr['ok']: st[u]['either'] += 1
            else:
                if len(uncov[u]) < 10:
                    uncov[u].append((fmt(M), 'a', a, 'q', q,
                                     'slfail', [k for k in ('red','mono','brne','mc') if not sr[k]]))
            for k in ('red', 'mono', 'brne', 'mc'):
                if sr[k]: st[u]['sl_' + k] += 1
            if not hr:
                bad = tuple(k for k in ('red','mono','brne','mc') if not sr[k])
                slfail_when_needed[u][bad] = slfail_when_needed[u].get(bad, 0) + 1
    for u in UNITS:
        s = st[u]
        pr(f"[{u}] host {s['host']}/{tot}  slice {s['slice']}/{tot}  both {s['both']}"
           f"  EITHER {s['either']}/{tot}")
        pr(f"      slice conjuncts: red {s['sl_red']}  mono {s['sl_mono']}"
           f"  brne {s['sl_brne']}  mc {s['sl_mc']}")
        pr(f"      when host fails, slice-fail patterns: {slfail_when_needed[u]}")
        for c in uncov[u]: pr("      UNCOVERED:", c)

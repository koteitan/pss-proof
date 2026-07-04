#!/usr/bin/env python3
"""r29a-CIIIREG probe 2: the condIII BT-side facts + the STRUCTURAL claims
for the planned proofs, DEEP.

Per genuine condIII host (both guard m>0 and m=0):
  dbbody   : domB body == ('TB', ub)                      [dbbodyH]
  base0    : lessBT (D_ub 0) A0                           [base0H]
  base1    : lessBT A0 (unflat(s0+flat(D_ub(D_ub 0))+b0)) [base1H]
  A0lt     : lessBT A0 body                               [A0ltH]
STRUCTURE for the proofs:
  c1shape  : c1 == Dpt(v, t2)  (v=e1(jm1), t2=bpHeadT c1) [m_8_5_scbdec_c1_shape]
  c2shape  : c2 == Dpt(v, t2 + D_v1 0)                    [condIII transC2 branch]
  fA0      : flat A0 == u1 + flat(c1) + v1w
  fbody    : flat body == u1 + flat(c2) + v1w
  insEq    : ins1 == unflat(u1 + flat(Dpt(v, t2+[D_ub(D_ub 0)])) + v1w)
  h0gt     : bpHeadV A0 > ub  (first-component head)      [base0 route (a)]
  h0gev1   : bpHeadV A0 >= v1
  h0body   : bpHeadV A0 == bpHeadV body
  valley   : all interior RightNodes(Trans N) >= v1       [dbbody route]
  lastRN   : last RightNodes(Trans N) == v1
  RNlen2   : len(RightNodes(Trans N)) >= 2
"""
import sys, pickle, collections
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import Lng, entry, seg, parent, hasParent, monoT, fmt
from _r15_vx_lib import Trans, lessBT, domB, condIII
from trans_model import (Dpt, bpHeadT, bpHeadV, flatBT, unflatBT, scb_decomps,
                         ZB, Adm, Pred, addBT)
import trans_model as tm

SP = '/tmp/claude-1000/-home-koteitan-proofs-pss-proof/8b6b910e-60c9-4662-aff1-4806ad270a61/scratchpad/'

def pr(*a):
    print(*a); sys.stdout.flush()

def jm2f(M): return parent(M, 1, Lng(M)-1)

def in_shape(M):
    if Lng(M) < 4: return False
    if not monoT(M): return False
    if not hasParent(M, 1, Lng(M)-1): return False
    if not (1 < Lng(M)-1): return False
    j2 = jm2f(M)
    if j2 is None: return False
    if not (j2 + 1 < Lng(M)-1): return False
    return True

def RightNodes(t):
    out = []
    while t[1]:
        p = t[1][-1]
        out.append(p[1])
        t = p[2]
    return out

def internals(M):
    j1 = Lng(M) - 1
    j0 = parent(M, 0, j1)
    jm1 = Adm(M, j0)
    c1 = tm.Mark(Pred(M), jm1)
    v = bpHeadV(c1); t2 = bpHeadT(c1)
    c2 = tm._c2(M, j1, j0, v, t2)
    return j0, jm1, c1, v, t2, c2

KEYS = ['dbbody', 'base0', 'base1', 'A0lt', 'c1shape', 'c2shape', 'fA0',
        'fbody', 'insEq', 'h0gt', 'h0gev1', 'h0body', 'valley', 'lastRN',
        'RNlen2', 'pairs']

def run(tag, hosts):
    tot = deep = 0
    st = {k: {'g': [0, 0], 'z': [0, 0]} for k in KEYS}  # guard / m=0: [ok, tot]
    cex = collections.defaultdict(list)
    for M in hosts:
        tot += 1
        isdeep = Lng(M) >= 10
        if isdeep: deep += 1
        n = Lng(M)
        j2 = jm2f(M); j3 = Adm(M, j2)
        cls = 'g' if j3 < j2 else 'z'
        v1 = entry(M, 1, n-1); ub = v1 - 1; e3 = entry(M, 1, j3)
        try:
            j0, jm1, c1, v, t2, c2 = internals(M)
            N = seg(M, j3, n-1)
            TN = Trans(N)
            body = bpHeadT(TN)
            A0 = bpHeadT(Trans(seg(M, j3, n-2)))
            dnest = scb_decomps(TN, flatBT(c2))
            dhole = scb_decomps(c2, flatBT(Dpt(v1, ZB)))
            r = {}
            r['pairs'] = len(dnest) == 1 and len(dhole) >= 1
            u1h, v1w = dnest[0]
            u1 = u1h[1:]
            u2, v2 = dhole[0]
            s0 = u1 + u2; b0 = v2 + v1w
            r['dbbody'] = domB(body) == ('TB', ub)
            r['base0'] = lessBT(Dpt(ub, ZB), A0)
            ins1 = unflatBT(s0 + flatBT(Dpt(ub, Dpt(ub, ZB))) + b0)
            r['base1'] = lessBT(A0, ins1)
            r['A0lt'] = lessBT(A0, body)
            r['c1shape'] = c1 == Dpt(v, t2)
            r['c2shape'] = c2 == Dpt(v, addBT(t2, Dpt(v1, ZB)))
            r['fA0'] = flatBT(A0) == u1 + flatBT(c1) + v1w
            r['fbody'] = flatBT(body) == u1 + flatBT(c2) + v1w
            ins2 = unflatBT(u1 + flatBT(Dpt(v, addBT(t2, Dpt(ub, Dpt(ub, ZB)))))
                            + v1w)
            r['insEq'] = ins1 == ins2
            h0 = bpHeadV(A0)
            r['h0gt'] = h0 > ub
            r['h0gev1'] = h0 >= v1
            r['h0body'] = h0 == bpHeadV(body)
            RN = RightNodes(TN)
            r['RNlen2'] = len(RN) >= 2
            r['lastRN'] = RN and RN[-1] == v1
            r['valley'] = all(x >= v1 for x in RN[1:-1])
        except Exception as e:
            cex['EXC'].append((fmt(M), repr(e)))
            continue
        for k in KEYS:
            st[k][cls][1] += 1
            if r[k]:
                st[k][cls][0] += 1
            elif len(cex[k]) < 3:
                cex[k].append((cls, fmt(M), 'jm3', j3, 'jm2', j2, 'j0', j0,
                               'h0', bpHeadV(A0), 'ub', ub))
    pr(f"== {tag}: hosts {tot} (deep {deep})")
    for k in KEYS:
        g, z = st[k]['g'], st[k]['z']
        pr(f"  {k:8s} guard {g[0]}/{g[1]}   m=0 {z[0]}/{z[1]}")
    for k in cex:
        for c in cex[k][:3]:
            pr(f"   CEX[{k}]:", c)

if __name__ == '__main__':
    import random
    with open(SP + 'w84_pool.pkl', 'rb') as f:
        H4 = pickle.load(f)
    run("W84POOL (426, Lng<=9)", H4)
    with open(SP + 'r29pool.pkl', 'rb') as f:
        P = pickle.load(f)
    hosts = [M for M in P if in_shape(M) and condIII(M)]
    random.seed(31)
    deepH = [M for M in hosts if 10 <= Lng(M) <= 13]
    guard = [M for M in deepH if Adm(M, jm2f(M)) < jm2f(M)]
    quiet = [M for M in deepH if not (Adm(M, jm2f(M)) < jm2f(M))]
    random.shuffle(guard); random.shuffle(quiet)
    sel = guard[:220] + quiet[:120]
    pr(f"deep sel: {len(sel)} (guard {min(len(guard),220)})")
    run("R29POOL deep (Lng 10-13)", sel)

#!/usr/bin/env python3
"""r28-WIRE84 probe 5: the CORRECT (d4vx_core) condIII exchange witnesses.

Instantiation (mirroring the L6 closed form m_8_4_various_scb_IIIIV):
  N    = seg M jm3 j1,  body := bpHeadT (Trans N)
  (s1,b1) : kind-1 pair of Trans M at core flat(Trans N)      [m_8_4_Trans_scb]
  (u1,v1) : nest pair of Trans N at core flat(c2), head-stripped [s84d_dec2]
  (u2,v2) : c2-hole pair at core flat(D_v 0)                   [L6 (3)]
  s0 := u1@u2,  b0 := v2@v1,  ub := v-1,  A0 := bpHeadT (Trans (Pred N))
checks:
  dbbody   : domB body == ('TB', ub)
  inner_c  : flat body == s0 @ flat(D_v 0) @ b0     (composition identity)
  mnform   : for m in 1..3: flat(Trans(M[m])) ==
             s1 @ [D e3] @ (s0@[D ub])^(m-1) @ flat A0' @ b0^(m-1) @ b1
             where A0' := bpHeadT(Trans(Pred N))  (the L6 base)
  base0    : lessBT (D_ub 0) A0
  base1    : lessBT A0 (unflat(s0 @ flat(D_ub(D_ub 0)) @ b0))   [d4vx_ins]
  A0ltbody : lessBT A0 body                                     [descent (2)]
  A0eq     : A0 == bpHeadT (Trans (Pred Np))                    [veM value]
  uvOK     : e3 < v
"""
import sys, pickle
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import Lng, entry, seg, monoT, parent, hasParent, fmt
from _r15_vx_lib import Trans, lessBT, domB, condIII
from trans_model import (Dpt, bpHeadT, flatBT, unflatBT, scb_decomps, ZB,
                         Adm, Pred)
import trans_model as tm

CACHE = '/tmp/claude-1000/-home-koteitan-proofs-pss-proof/8b6b910e-60c9-4662-aff1-4806ad270a61/scratchpad/w84_pool.pkl'

def pr(*a):
    print(*a); sys.stdout.flush()

def jm2f(M): return parent(M, 1, Lng(M)-1)

def internals_c2(M):
    """(v-head e1jm1, c2) via trans_model internals"""
    j1 = Lng(M) - 1
    j0 = parent(M, 0, j1)
    jm1 = Adm(M, j0)
    c1 = tm.Mark(Pred(M), jm1)
    from trans_model import bpHeadV
    v = bpHeadV(c1); t2 = bpHeadT(c1)
    c2 = tm._c2(M, j1, j0, v, t2)
    return c2

KEYS = ['dbbody', 'inner_c', 'mn1', 'mn2', 'mn3', 'base0', 'base1',
        'A0ltbody', 'A0eq', 'uvOK', 'pairs_ok']

if __name__ == '__main__':
    with open(CACHE, 'rb') as f:
        H = pickle.load(f)
    pr(f"corpus: {len(H)} condIII hosts (deep {sum(1 for M in H if Lng(M)>=9)})")
    tot = deep = 0
    st = {k: 0 for k in KEYS}
    stdeep = {k: 0 for k in KEYS}
    cex = []
    from red_model import oper
    for M in H:
        tot += 1
        isdeep = Lng(M) >= 9
        if isdeep: deep += 1
        n = Lng(M)
        j2 = jm2f(M); j3 = Adm(M, j2)
        v = entry(M, 1, n-1); ub = v - 1; e3 = entry(M, 1, j3)
        r = {}
        try:
            N = seg(M, j3, n-1)
            TN = Trans(N)
            body = bpHeadT(TN)
            c2 = internals_c2(M)
            TM = Trans(M)
            A0 = bpHeadT(Trans(seg(M, j3, n-2)))       # bpHeadT (Trans (Pred N))
            # pairs
            dsb1 = scb_decomps(TM, flatBT(TN))
            dnest = scb_decomps(TN, flatBT(c2))
            dhole = scb_decomps(c2, flatBT(Dpt(v, ZB)))
            r['pairs_ok'] = len(dsb1) == 1 and len(dnest) == 1 and len(dhole) >= 1
            if not r['pairs_ok']:
                cex.append(('pairs', fmt(M), len(dsb1), len(dnest), len(dhole)))
            s1, b1 = dsb1[0]
            u1h, v1 = dnest[0]           # u1h = Dsym e3 # u1
            u1 = u1h[1:]
            u2, v2 = dhole[0]
            s0 = u1 + u2; b0 = v2 + v1
            r['dbbody'] = domB(body) == ('TB', ub)
            r['inner_c'] = flatBT(body) == s0 + flatBT(Dpt(v, ZB)) + b0
            fA0 = flatBT(A0)
            for m in (1, 2, 3):
                Mm = oper(M, m)
                want = (s1 + [('D', e3)]
                        + (s0 + [('D', ub)]) * (m - 1)
                        + fA0 + b0 * (m - 1) + b1)
                r['mn%d' % m] = flatBT(Trans(Mm)) == want
            r['base0'] = lessBT(Dpt(ub, ZB), A0)
            ins1 = unflatBT(s0 + flatBT(Dpt(ub, Dpt(ub, ZB))) + b0)
            r['base1'] = lessBT(A0, ins1)
            r['A0ltbody'] = lessBT(A0, body)
            r['A0eq'] = A0 == bpHeadT(Trans(seg(M, j2, n-2)))
            r['uvOK'] = e3 < v
        except Exception as ex:
            cex.append(('EXC', fmt(M), repr(ex)[:70]))
            continue
        for k in KEYS:
            if r.get(k):
                st[k] += 1
                if isdeep: stdeep[k] += 1
            elif len(cex) < 14:
                cex.append((k, fmt(M), 'jm2', j2, 'jm3', j3, 'v', v))
    pr(f"hosts {tot} (deep {deep})")
    pr("  " + "  ".join(f"{k} {st[k]}/{tot}" for k in KEYS))
    if deep:
        pr("  deep: " + "  ".join(f"{k} {stdeep[k]}/{deep}" for k in KEYS))
    for c in cex[:14]: pr("   CEX:", c)

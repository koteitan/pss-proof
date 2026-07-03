#!/usr/bin/env python3
"""r28-WIRE84 probe 4: the cfax_condIII_exchange13_of_CFvalues STRUCTURAL
witnesses, with the natural instantiation
  body := bpHeadT (Trans N),  N = seg M jm3 j1        (the jm3 kind-1 core body)
  A0   := bpHeadT (Trans (Pred N'))                   (= fPN body)
  s0/b0:= rightend pair minus head (fLp inner pair)
  L    := body of Trans L' minus its last top-level component D_ub 0
checks per genuine condIII host (hp1 & j1>2 & rng):
  dbbody : domB body == TBv (v-1)
  bodyne : body != Trm []
  LpShape: PB(bpHeadT(Trans Lp)) nonempty and last component == D_ub 0
  innerU : with L := Sigma(butlast PB(ALp)): flat(L + D_ub 0) splits with the
           SAME (s0,b0) as fLp  (string identity: flat(ALp) = s0 @ flat(D_ub 0) @ b0
           and L + D_ub 0 == ALp)
  ba     : lessBT A0 (L + D_ub (D_ub 0))
  bx     : lessBT (D_ub 0) A0   (re-check)
  A0TB   : dfree A0 (T_B)
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import Lng, entry, seg, monoT, parent, hasParent, fmt
from red_model import reduced
from _r15_vx_lib import Trans, gen_pool, condIII, lessBT, domB
from trans_model import (Dpt, addBT, PB, SigmaB, bpHeadT, bpHeadV, flatBT,
                         ZB, Adm, Pred, dfree_BT)
import pickle, os

CACHE = '/tmp/claude-1000/-home-koteitan-proofs-pss-proof/8b6b910e-60c9-4662-aff1-4806ad270a61/scratchpad/w84_pool.pkl'

def pr(*a):
    print(*a); sys.stdout.flush()

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

KEYS = ['dbbody', 'bodyne', 'LpShape', 'innerU_eq', 'ba', 'bx', 'A0TB']

if __name__ == '__main__':
    with open(CACHE, 'rb') as f:
        H = pickle.load(f)
    pr(f"corpus: {len(H)} condIII hosts (deep {sum(1 for M in H if Lng(M)>=9)})")
    tot = deep = 0
    st = {k: 0 for k in KEYS}
    stdeep = {k: 0 for k in KEYS}
    cex = []
    for M in H:
        tot += 1
        isdeep = Lng(M) >= 9
        if isdeep: deep += 1
        n = Lng(M)
        j2 = jm2f(M); j3 = Adm(M, j2)
        v = entry(M, 1, n-1); ub = v - 1
        r = {}
        try:
            body = bpHeadT(Trans(seg(M, j3, n-1)))
            A0 = bpHeadT(Trans(seg(M, j2, n-2)))
            sLp = seg(M, j2, n-2) + [(entry(M, 0, n-1), entry(M, 1, j2))]
            ALp = bpHeadT(Trans(sLp))
            r['dbbody'] = domB(body) == ('Tv', ub)
            r['bodyne'] = body != ZB
            comps = PB(ALp)
            r['LpShape'] = bool(comps) and comps[-1] == Dpt(ub, ZB)
            if r['LpShape']:
                L = SigmaB(comps[:-1])
                r['innerU_eq'] = addBT(L, Dpt(ub, ZB)) == ALp
                r['ba'] = lessBT(A0, addBT(L, Dpt(ub, Dpt(ub, ZB))))
            else:
                r['innerU_eq'] = False
                r['ba'] = False
            r['bx'] = lessBT(Dpt(ub, ZB), A0)
            r['A0TB'] = dfree_BT(A0)
        except Exception as ex:
            cex.append(('EXC', fmt(M), repr(ex)[:60]))
            continue
        for k in KEYS:
            if r.get(k):
                st[k] += 1
                if isdeep: stdeep[k] += 1
            elif len(cex) < 12:
                cex.append((k, fmt(M), 'jm2', j2, 'jm3', j3, 'v', v))
    pr(f"hosts {tot} (deep {deep})")
    pr("  " + "  ".join(f"{k} {st[k]}/{tot}" for k in KEYS))
    if deep:
        pr("  deep: " + "  ".join(f"{k} {stdeep[k]}/{deep}" for k in KEYS))
    for c in cex[:12]: pr("   CEX:", c)

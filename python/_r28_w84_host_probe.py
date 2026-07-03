#!/usr/bin/env python3
"""r28-WIRE84 probe 2: HOST-level terminal-slice-lemma hypothesis + value mechanics.

Strategy under test (the 'double application' bridging):
  m_8_2_condV_terminal_slice_Trans applied at host X in {M, Pred M, L1} with
  offsets jm2 and jm3 gives
     Trans (seg X q (Lng X - 1)) = Dpt (entry X 1 q) (bpHeadT (Trans X))
  for q in {jm2, jm3}; hence the two slices share their deep tail (VEM/VEL for
  X = Pred M / L1), and the d2/d3/d4a/d4b value forms follow.

Checks per genuine condIII host M (hp1 & 1<j1-1 & rng):
  hypM/hypP/hypL : Br X != [] and [jm2 < Joints X!last  OR  (= & diag & desc)]
  valNp   : Trans(seg M jm2 j1)      == Dpt(e1jm2, bpHeadT(Trans M))
  valN    : Trans(seg M jm3 j1)      == Dpt(e1jm3, bpHeadT(Trans M))
  valPNp  : Trans(seg M jm2 (n-2))   == Dpt(e1jm2, bpHeadT(Trans(Pred M)))
  valPN   : Trans(seg M jm3 (n-2))   == Dpt(e1jm3, bpHeadT(Trans(Pred M)))
  valPNp_t2: Trans(seg M jm2 (n-2))  == Dpt(e1jm2, t2)          [d3-general]
  valL2   : Trans(seg L1 jm2 (nL-1)) == Dpt(e1jm2, bpHeadT(Trans L1))
  valL3   : Trans(seg L1 jm3 (nL-1)) == Dpt(e1jm3, bpHeadT(Trans L1))
  veM/veL : the c3vx conclusions themselves
  bx      : lessBT (Dpt (v-1) 0) A0,  A0 = bpHeadT(Trans(seg M jm2 (n-2)))
  uv      : entry1 jm3 < v
  w_eq_c2 : bpHeadT(Trans M) == bpHeadT(c2)  [sanity: relation of tails]
Corpora: (G) genuine ST_PS pool via oper closure (deep Lng>=9 included),
         (B) brute-force diagSeq+tail standard (yaBMS), (W) non-standard wide.
"""
import sys, os, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, seg, monoT, parent, hasParent,
                       fmt, diagSeq, Br, FirstNodes, Joints, TrMax, zeroT)
from red_model import reduced
import red_model as rm
from _r15_vx_lib import (Trans, Mark, internals, lessBT, gen_pool, mono_hosts,
                         condIII, condIV)
from trans_model import Dpt, bpHeadT, ZB, Adm, adm, Pred

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

def hyp_at(X, m):
    """Br X != [] and the terminal-slice-lemma hypothesis at offset m; returns
    (ok, which) with which in {'lt','eq','no-br','no'}"""
    b = Br(X)
    if not b: return (False, 'no-br')
    J1 = len(b) - 1
    j0p = Joints(X)[J1]
    j1p = FirstNodes(X)[J1]
    if j0p is None: return (False, 'no')
    if m < j0p: return (True, 'lt')
    if m == j0p and entry(X, 0, j1p) == entry(X, 1, j1p) and descending(b):
        return (True, 'eq')
    return (False, 'no')

def jm2f(M): return parent(M, 1, Lng(M)-1)
def L1f(M):  return Pred(M) + [(entry(M, 0, Lng(M)-1), entry(M, 1, jm2f(M)))]

def in_shape(M):
    if Lng(M) < 4: return False
    if not monoT(M): return False
    if not hasParent(M, 1, Lng(M)-1): return False
    if not (1 < Lng(M)-1): return False
    j2 = jm2f(M)
    if j2 is None: return False
    if not (j2 + 1 < Lng(M)-1): return False   # rng
    return True

KEYS = ['hypM', 'hypP', 'hypL', 'valNp', 'valN', 'valPNp', 'valPN',
        'valPNp_t2', 'valL2', 'valL3', 'veM', 'veL', 'bx', 'uv', 'w_eq_c2']

def run(tag, hosts):
    tot = deep = 0
    st = {k: 0 for k in KEYS}
    stdeep = {k: 0 for k in KEYS}
    hyp_kinds = {'M': {}, 'P': {}, 'L': {}}
    cex = []
    for M in hosts:
        tot += 1
        isdeep = Lng(M) >= 9
        if isdeep: deep += 1
        n = Lng(M)
        j2 = jm2f(M); j3 = Adm(M, j2)
        e2 = entry(M, 1, j2); e3 = entry(M, 1, j3); v = entry(M, 1, n-1)
        Lh = L1f(M); nL = Lng(Lh)
        it = internals(M)
        r = {}
        hM = hyp_at(M, j2);      r['hypM'] = hM[0]
        hP = hyp_at(Pred(M), j2); r['hypP'] = hP[0]
        hL = hyp_at(Lh, j2);     r['hypL'] = hL[0]
        for kk, hh in (('M', hM), ('P', hP), ('L', hL)):
            hyp_kinds[kk][hh[1]] = hyp_kinds[kk].get(hh[1], 0) + 1
        try:
            TM = Trans(M); TP = Trans(Pred(M)); TL = Trans(Lh)
            r['valNp'] = Trans(seg(M, j2, n-1)) == Dpt(e2, bpHeadT(TM))
            r['valN'] = Trans(seg(M, j3, n-1)) == Dpt(e3, bpHeadT(TM))
            r['valPNp'] = Trans(seg(M, j2, n-2)) == Dpt(e2, bpHeadT(TP))
            r['valPN'] = Trans(seg(M, j3, n-2)) == Dpt(e3, bpHeadT(TP))
            t2 = it['t2'] if it else None
            r['valPNp_t2'] = (it is not None) and \
                Trans(seg(M, j2, n-2)) == Dpt(e2, t2)
            r['valL2'] = Trans(seg(Lh, j2, nL-1)) == Dpt(e2, bpHeadT(TL))
            r['valL3'] = Trans(seg(Lh, j3, nL-1)) == Dpt(e3, bpHeadT(TL))
            r['veM'] = bpHeadT(Trans(seg(M, j3, n-2))) == bpHeadT(Trans(seg(M, j2, n-2)))
            sLp = seg(M, j2, n-2) + [(entry(M,0,n-1), e2)]
            r['veL'] = bpHeadT(Trans(seg(Lh, j3, nL-1))) == bpHeadT(Trans(sLp))
            A0 = bpHeadT(Trans(seg(M, j2, n-2)))
            r['bx'] = lessBT(Dpt(v-1, ZB), A0)
            r['uv'] = e3 < v
            r['w_eq_c2'] = (it is not None) and bpHeadT(TM) == bpHeadT(it['c2'])
        except Exception as ex:
            cex.append(('EXC', fmt(M), repr(ex)[:60]))
            continue
        for k in KEYS:
            if r.get(k):
                st[k] += 1
                if isdeep: stdeep[k] += 1
            elif len(cex) < 15 and k in ('hypM','hypP','hypL','valNp','valPNp',
                                          'valPNp_t2','valL2','valL3','veM','veL','bx'):
                cex.append((k, fmt(M), 'jm2', j2, 'jm3', j3))
    pr(f"== {tag}: hosts {tot} (deep {deep})")
    pr("  " + "  ".join(f"{k} {st[k]}/{tot}" for k in KEYS))
    if deep:
        pr("  deep: " + "  ".join(f"{k} {stdeep[k]}/{deep}" for k in KEYS))
    pr(f"  hyp kinds: M {hyp_kinds['M']}  P {hyp_kinds['P']}  L {hyp_kinds['L']}")
    for c in cex[:15]: pr("   CEX:", c)

def gen_brute_standard(cap=200, cap_iter=200000):
    from red_model import is_standard
    hosts, seen, it = [], set(), 0
    for d in range(3, 8):
        base = diagSeq(0, d)
        rng = range(0, d+2)
        for ntail in (2, 3, 4):
            for tail in itertools.product(itertools.product(rng, rng), repeat=ntail):
                it += 1
                if it > cap_iter: return hosts
                M = base + list(tail)
                key = tuple(M)
                if key in seen: continue
                seen.add(key)
                if not in_shape(M): continue
                if not condIII(M): continue
                try:
                    if not is_standard(M): continue
                except Exception:
                    continue
                hosts.append(M)
                if len(hosts) >= cap: return hosts
    return hosts

def gen_wide_nonstd(cap=150, cap_iter=400000):
    from red_model import is_standard
    hosts, seen, it = [], set(), 0
    for d in range(3, 8):
        base = diagSeq(0, d)
        rng = range(0, d+2)
        for ntail in (2, 3, 4):
            for tail in itertools.product(itertools.product(rng, rng), repeat=ntail):
                it += 1
                if it > cap_iter: return hosts
                M = base + list(tail)
                key = tuple(M)
                if key in seen: continue
                seen.add(key)
                if not in_shape(M): continue
                if not condIII(M): continue
                try:
                    if is_standard(M): continue
                except Exception:
                    continue
                if not reduced(M): continue
                hosts.append(M)
                if len(hosts) >= cap: return hosts
    return hosts

if __name__ == '__main__':
    pr("building genuine ST_PS pool (oper closure)...")
    pool = gen_pool(maxlen=12, maxn=4, maxseed=3, cap=9000, oper_budget=3)
    HG = [M for M in pool if in_shape(M) and reduced(M) and condIII(M)]
    # dedupe
    seen = set(); H2 = []
    for M in HG:
        k = tuple(M)
        if k not in seen:
            seen.add(k); H2.append(M)
    pr(f"pool: {len(pool)} -> condIII shaped {len(H2)} (deep {sum(1 for M in H2 if Lng(M)>=9)})")
    run("GENUINE pool condIII", H2)
    pr("brute-force standard condIII (yaBMS)...")
    HB = gen_brute_standard()
    run("BRUTE standard condIII", HB)
    pr("wide NON-standard reduced monoT condIII...")
    HW = gen_wide_nonstd()
    run("WIDE non-standard condIII", HW)

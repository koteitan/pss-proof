#!/usr/bin/env python3
"""r29a-CIIIREG probe 1: the condIII slice regimes regS/regSP/regB, DEEP.

For each GENUINE (standard) condIII host M (hp1 & 1<j1 & rng), guard m>0
(jm3 < jm2), check the cfbx_reg conjuncts at:
  S  (regS) : N  = seg M jm3 (n-1),  m = jm2-jm3
  SP (regSP): PN = seg M jm3 (n-2),  m = jm2-jm3      [= regA host]
  B  (regB) : SB = seg L1 AjL (nL-1), m = jm2-AjL,  AjL = Adm L1 jm2

plus the STRUCTURE identities the proof plan needs:
  diag3   : entry M 0 jm3 == entry M 1 jm3            (slice already reduced)
  jm3tr   : jm3 <= TrMax M
  redN    : reduced N (raw slice)
  jointN  : Joints N ! last == j0 - jm3
  fnN     : FirstNodes N ! last == (n-1) - jm3        (singleton last branch)
  mlt     : jm2 - jm3 < j0 - jm3                       (d1 disjunct)
  trshift : TrMax N == TrMax M - jm3
  brlen   : len(Br N) == len(Br M)
  ajlEq   : Adm L1 jm2 == jm3                          (L1 column agreement)
  dichSP  : TrMax N + 2 < Lng N  (persistence route usable)
  regSPtruth on the edge TrMax N + 2 == Lng N hosts
"""
import sys, pickle, collections
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, seg, parent, hasParent, monoT, reduced,
                       zeroT, fmt, Br, FirstNodes, Joints, TrMax, Pred)
from trans_model import condIII, Adm

SP = '/tmp/claude-1000/-home-koteitan-proofs-pss-proof/8b6b910e-60c9-4662-aff1-4806ad270a61/scratchpad/'

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

def cfbx_reg(m, S):
    if len(S) == 0: return False, 'empty'
    if not reduced(S): return False, 'red'
    if zeroT(S) or not monoT(S): return False, 'mono'
    b = Br(S)
    if not b: return False, 'brne'
    J1 = len(b) - 1
    j0p = Joints(S)[J1]
    j1p = FirstNodes(S)[J1]
    if j0p is None: return False, 'joint-none'
    if m < j0p: return True, 'd1'
    if m == j0p and entry(S, 0, j1p) == entry(S, 1, j1p) and descending(b):
        return True, 'd2'
    return False, 'mcond'

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

KEYS = ['regS', 'regSP', 'regB', 'diag3', 'jm3tr', 'redN', 'jointN', 'fnN',
        'mlt', 'trshift', 'brlen', 'ajlEq', 'dichSP']

def run(tag, hosts):
    tot = deep = g = gdeep = 0
    st = {k: 0 for k in KEYS}
    stdeep = {k: 0 for k in KEYS}
    cex = collections.defaultdict(list)
    edge = []           # guard-firing hosts with TrMax N + 2 == Lng N
    m0edge = []         # guard-quiet (m=0) hosts with all-trunk Pred N
    for M in hosts:
        tot += 1
        isdeep = Lng(M) >= 10
        if isdeep: deep += 1
        n = Lng(M)
        j1 = n - 1
        j0 = parent(M, 0, j1)
        j2 = jm2f(M); j3 = Adm(M, j2)
        if not (j3 < j2):
            # guard quiet; still track the all-trunk edge for the m==0 route
            N = seg(M, j3, n-1)
            if TrMax(N) + 2 == Lng(N) and len(m0edge) < 8:
                m0edge.append(fmt(M))
            continue
        g += 1
        if isdeep: gdeep += 1
        m = j2 - j3
        N = seg(M, j3, n-1)
        PN = seg(M, j3, n-2)
        L1 = Pred(M) + [(entry(M, 0, n-1), entry(M, 1, j2))]
        AjL = Adm(L1, j2)
        SB = seg(L1, AjL, Lng(L1)-1)
        r = {}
        okS, whyS = cfbx_reg(m, N); r['regS'] = okS
        okSP, whySP = cfbx_reg(m, PN); r['regSP'] = okSP
        okB, whyB = cfbx_reg(j2 - AjL, SB); r['regB'] = okB
        r['diag3'] = entry(M, 0, j3) == entry(M, 1, j3)
        r['jm3tr'] = j3 <= TrMax(M)
        r['redN'] = reduced(N)
        bN = Br(N)
        if bN:
            r['jointN'] = Joints(N)[len(bN)-1] == j0 - j3
            r['fnN'] = FirstNodes(N)[len(bN)-1] == (n-1) - j3
        else:
            r['jointN'] = r['fnN'] = False
        r['mlt'] = j2 - j3 < j0 - j3
        r['trshift'] = TrMax(N) == TrMax(M) - j3
        r['brlen'] = len(bN) == len(Br(M))
        r['ajlEq'] = AjL == j3
        r['dichSP'] = TrMax(N) + 2 < Lng(N)
        if TrMax(N) + 2 == Lng(N):
            edge.append((fmt(M), okSP, whySP))
        for k in KEYS:
            if r[k]:
                st[k] += 1
                if isdeep: stdeep[k] += 1
            elif len(cex[k]) < 4:
                cex[k].append((fmt(M), 'm', m, 'whyS', whyS, 'whySP', whySP,
                               'whyB', whyB))
    pr(f"== {tag}: hosts {tot} (deep {deep}); guard m>0: {g} (deep {gdeep})")
    pr("  " + "  ".join(f"{k} {st[k]}/{g}" for k in KEYS))
    if gdeep:
        pr("  deep: " + "  ".join(f"{k} {stdeep[k]}/{gdeep}" for k in KEYS))
    for k in KEYS:
        for c in cex[k][:2]:
            pr(f"   CEX[{k}]:", c)
    pr(f"  guard-firing edge hosts (TrMax N+2 == Lng N): {len(edge)}")
    for e in edge[:8]: pr("    edge:", e)
    pr(f"  m==0 all-trunk-N sample: {len(m0edge)}")
    for e in m0edge[:4]: pr("    m0edge:", e)

if __name__ == '__main__':
    import random
    with open(SP + 'r29pool.pkl', 'rb') as f:
        P = pickle.load(f)
    hosts = [M for M in P if in_shape(M) and condIII(M)]
    pr(f"r29pool: {len(P)} -> condIII shape hosts {len(hosts)}")
    # stratified subsample: keep ALL guard-firing hosts up to a per-Lng cap
    random.seed(29)
    guard = [M for M in hosts if Adm(M, jm2f(M)) < jm2f(M)]
    pr(f"guard-firing: {len(guard)}")
    byL = collections.defaultdict(list)
    for M in guard: byL[Lng(M)].append(M)
    sel = []
    for L in sorted(byL):
        ms = byL[L]
        random.shuffle(ms)
        sel += ms[:120]
    pr(f"selected guard sample: {len(sel)} " +
       str(sorted(collections.Counter(Lng(M) for M in sel).items())))
    run("R29POOL guard-sample", sel)
    with open(SP + 'w84_pool.pkl', 'rb') as f:
        H4 = pickle.load(f)
    run("W84POOL (r28 426)", H4)

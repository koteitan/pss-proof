#!/usr/bin/env python3
"""r29a probe 3: the RED-slice regimes (correct formulation after the raw-slice
regS refutation) + last-branch identification data.

Per guard-firing (jm3<jm2) genuine condIII host:
  regSr   : cfbx_reg (jm2-jm3) (Red N),   N = seg M jm3 (n-1)
  regSPr  : cfbx_reg (jm2-jm3) (Red PN),  PN = seg M jm3 (n-2)
  jointGE : Joints(Red N)!last >= j0 - jm3
  jlast   : value of Joints(Red N)!last - jm3-offset classification:
            == jm2-jm3? == j0-jm3? other?
  fnlast  : FirstNodes(Red N)!last == Lng N - 1? == x1-jm3?
  x1      : first step of jm2's row-0 chain to j1
  nx1x    : nextR M 1 (x1-1) x1?
  edgeSP  : TrMax(Red PN) + 2 == Lng PN (all-trunk Pred)
"""
import sys, pickle, collections, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, seg, parent, hasParent, monoT, reduced,
                       zeroT, fmt, Br, FirstNodes, Joints, TrMax, Red)
import red_model as rm
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
    j0p = Joints(S)[J1]; j1p = FirstNodes(S)[J1]
    if j0p is None: return False, 'joint-none'
    if m < j0p: return True, 'd1'
    if m == j0p and entry(S, 0, j1p) == entry(S, 1, j1p) and descending(b):
        return True, 'd2'
    return False, 'mcond'

def jm2f(M): return parent(M, 1, Lng(M)-1)
def in_shape(M):
    if Lng(M) < 4 or not monoT(M): return False
    if not hasParent(M, 1, Lng(M)-1): return False
    if not (1 < Lng(M)-1): return False
    j2 = jm2f(M)
    return j2 is not None and j2 + 1 < Lng(M)-1

def first_step(M, a, b):
    """first x with nextrel0 a x on a chain a ->* b (min such x that still
    reaches b)"""
    n = Lng(M)
    for x in range(a+1, b+1):
        if rm.nextR(M, 0, a, x) and rm.le0(M, x, b):
            return x
    return None

KEYS = ['regSr', 'regSPr', 'jointGE', 'jl_jm2', 'jl_j0', 'jl_other',
        'fn_last', 'fn_x1', 'nx1x', 'edgeSP', 'SPd1']

def run(tag, hosts):
    st = collections.Counter(); tot = 0
    cex = collections.defaultdict(list)
    for M in hosts:
        n = Lng(M); j1 = n-1
        j0 = parent(M, 0, j1)
        j2 = jm2f(M); j3 = Adm(M, j2)
        if not (j3 < j2): continue
        tot += 1
        m = j2 - j3
        N = seg(M, j3, n-1); RN = Red(N)
        PN = seg(M, j3, n-2); RPN = Red(PN)
        okS, whyS = cfbx_reg(m, RN)
        okSP, whySP = cfbx_reg(m, RPN)
        if okS: st['regSr'] += 1
        elif len(cex['regSr']) < 4: cex['regSr'].append((fmt(M), whyS))
        if okSP: st['regSPr'] += 1
        elif len(cex['regSPr']) < 6: cex['regSPr'].append((fmt(M), whySP))
        if whySP == 'd1': st['SPd1'] += 1
        b = Br(RN)
        if b:
            jl = Joints(RN)[len(b)-1]; fn = FirstNodes(RN)[len(b)-1]
            if jl >= j0 - j3: st['jointGE'] += 1
            elif len(cex['jointGE']) < 4:
                cex['jointGE'].append((fmt(M), 'jl', jl, 'j0-j3', j0-j3))
            if jl == j2 - j3: st['jl_jm2'] += 1
            elif jl == j0 - j3: st['jl_j0'] += 1
            else:
                st['jl_other'] += 1
                if len(cex['jl_other']) < 4:
                    cex['jl_other'].append((fmt(M), 'jl', jl, 'jm2-j3', j2-j3,
                                            'j0-j3', j0-j3))
            if fn == Lng(N) - 1: st['fn_last'] += 1
            x1 = first_step(M, j2, j1)
            if x1 is not None and fn == x1 - j3: st['fn_x1'] += 1
            if x1 is not None and rm.nextR(M, 1, x1-1, x1): st['nx1x'] += 1
        if TrMax(RPN) + 2 == Lng(PN): st['edgeSP'] += 1
    pr(f"== {tag}: guard hosts {tot}")
    for k in KEYS: pr(f"  {k:8s} {st[k]}/{tot}")
    for k in cex:
        for c in cex[k]: pr(f"   CEX[{k}]:", c)

if __name__ == '__main__':
    with open(SP + 'w84_pool.pkl', 'rb') as f:
        H4 = pickle.load(f)
    run("W84POOL guard", H4)
    with open(SP + 'r29pool.pkl', 'rb') as f:
        P = pickle.load(f)
    hosts = [M for M in P if in_shape(M) and condIII(M) and Lng(M) <= 11]
    random.seed(5)
    guard = [M for M in hosts if Adm(M, jm2f(M)) < jm2f(M)]
    random.shuffle(guard)
    run("R29POOL Lng<=11 guard sample", guard[:300])

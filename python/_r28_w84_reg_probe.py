#!/usr/bin/env python3
"""r28-WIRE84 target (1): validate cfbx_reg at the two condIII VE' slices.

Slices (hosts of cfbx_reg / vcx_VE_all):
  A (VEM): S_A = seg M jm3 (Lng M - 2),        m_A = jm2 - jm3,   jm3 = Adm M jm2
  B (VEL): S_B = seg L1 AjL (Lng L1 - 1),      m_B = jm2 - AjL,   AjL = Adm L1 jm2
     L1 = Pred M @ [(M_{0,j1}, M_{1,jm2})]

cfbx_reg m S  <->  S in RT_PS  &  S in PT_PS  &  Br S != []
              &  ( m <  Joints S ! (|Br S|-1)
                 | ( m == Joints S ! (|Br S|-1)
                   & entry S 0 (FirstNodes S ! (|Br S|-1)) == entry S 1 (...)
                   & descending (Br S) ) )

Regimes probed:
  (G) genuine STANDARD hosts with hp1 & 1<j1 & rng   (the c3vx hypothesis set)
  (W) WIDE reduced-monoT (non-standard allowed) same shape hypotheses
      -- to learn whether standardness is load-bearing for some conjunct.
Per-conjunct fractions + which disjunct fires; deep Lng>=9 tracked separately.
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, seg, Adm, adm, leR, monoT, reduced,
                       parent, hasParent, is_standard, fmt, Pred, diagSeq,
                       Br, FirstNodes, Joints, TrMax, Red, zeroT)
from trans_model import condI, condIII, condV, condVI

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

def cfbx_reg_report(m, S):
    """returns dict of conjunct booleans"""
    r = {}
    r['ne'] = len(S) > 0
    r['red'] = reduced(S)
    r['mono'] = (not zeroT(S)) and monoT(S)
    b = Br(S)
    r['brne'] = len(b) > 0
    if b:
        J1 = len(b) - 1
        j0p = Joints(S)[J1]
        j1p = FirstNodes(S)[J1]
        r['d1'] = (j0p is not None) and (m < j0p)
        r['d2'] = (j0p is not None) and (m == j0p) \
                  and entry(S, 0, j1p) == entry(S, 1, j1p) and descending(b)
        r['mcond'] = r['d1'] or r['d2']
    else:
        r['d1'] = r['d2'] = r['mcond'] = False
    r['reg'] = r['red'] and r['mono'] and r['brne'] and r['mcond'] and r['ne']
    return r

def jm2(M): return parent(M, 1, Lng(M)-1)
def L1(M):  return Pred(M) + [(entry(M, 0, Lng(M)-1), entry(M, 1, jm2(M)))]

def in_shape_cheap(M):
    """all hypotheses except reducedness (reduced() is 90ms/call - do last)"""
    if Lng(M) < 4: return False
    if not monoT(M): return False
    if not hasParent(M, 1, Lng(M)-1): return False
    if not (1 < Lng(M)-1): return False
    if jm2(M) is None: return False
    if not (jm2(M) + 1 < Lng(M)-1): return False   # rng
    return True

def gen_hosts(cap_std=250, cap_wide=250, cap_iter=3000000):
    """single pass; returns (standard_hosts, wide_nonstandard_hosts).
    standard => reduced (standard-form reducedness), so reduced() is only
    called on the non-standard candidates (and only while hw is short)."""
    hs, hw, seen, it = [], [], set(), 0
    for d in range(3, 8):
        base = diagSeq(0, d)
        rng = range(0, d+2)
        for ntail in (2, 3, 4):
            for tail in itertools.product(itertools.product(rng, rng), repeat=ntail):
                it += 1
                if it > cap_iter: return hs, hw
                M = base + list(tail)
                key = tuple(M)
                if key in seen: continue
                seen.add(key)
                if not in_shape_cheap(M): continue
                try:
                    std = is_standard(M)
                except Exception:
                    continue
                if std:
                    if len(hs) < cap_std: hs.append(M)
                elif len(hw) < cap_wide and reduced(M):
                    hw.append(M)
                if it % 20000 == 0:
                    pr(f"  gen: it={it} std={len(hs)} wide={len(hw)}")
                if len(hs) >= cap_std and len(hw) >= cap_wide: return hs, hw
    return hs, hw

KEYS = ['ne', 'red', 'mono', 'brne', 'd1', 'd2', 'mcond', 'reg']

def run(tag, hosts):
    stats = {sl: {k: 0 for k in KEYS} for sl in ('A', 'B')}
    tot = deep = 0
    conds = {'I':0, 'III':0, 'V':0, 'VI':0, 'other':0}
    cex = []
    deepstats = {sl: {k: 0 for k in KEYS} for sl in ('A', 'B')}
    deteq = {'A': 0, 'B': 0}   # m == 0 (degenerate offset, adm jm2)
    for M in hosts:
        tot += 1
        isdeep = Lng(M) >= 9
        if isdeep: deep += 1
        if condI(M): conds['I'] += 1
        elif condIII(M): conds['III'] += 1
        elif condV(M): conds['V'] += 1
        elif condVI(M): conds['VI'] += 1
        else: conds['other'] += 1
        j2 = jm2(M); j3 = Adm(M, j2); n = Lng(M)
        SA = seg(M, j3, n-2); mA = j2 - j3
        Lh = L1(M); AjL = Adm(Lh, j2)
        SB = seg(Lh, AjL, Lng(Lh)-1); mB = j2 - AjL
        if mA == 0: deteq['A'] += 1
        if mB == 0: deteq['B'] += 1
        for sl, (m, S) in (('A', (mA, SA)), ('B', (mB, SB))):
            r = cfbx_reg_report(m, S)
            for k in KEYS:
                if r[k]:
                    stats[sl][k] += 1
                    if isdeep: deepstats[sl][k] += 1
            if not r['reg'] and len(cex) < 12:
                bad = [k for k in KEYS if not r[k]]
                cex.append((sl, fmt(M), 'm', m, 'slice', fmt(S), 'fails', bad))
    pr(f"== {tag}: hosts {tot} (deep {deep})  conds {conds}  m==0: {deteq}")
    for sl in ('A', 'B'):
        pr(f"  slice {sl}: " + "  ".join(f"{k} {stats[sl][k]}/{tot}" for k in KEYS))
        if deep:
            pr(f"  slice {sl} deep: " + "  ".join(f"{k} {deepstats[sl][k]}/{deep}" for k in KEYS))
    for c in cex: pr("   CEX:", c)
    return stats, tot

if __name__ == '__main__':
    pr("generating hosts (single pass)...")
    HG, HW = gen_hosts()
    run("GENUINE (standard, hp1 & j1>2 & rng)", HG)
    run("WIDE (non-standard reduced monoT, same shape)", HW)

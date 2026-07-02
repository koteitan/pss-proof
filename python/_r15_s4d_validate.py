#!/usr/bin/env python3
"""r15-S4d: empirical validation for the remaining §8.4 various-scb lemmas.

Targets (fresh seeds, GENUINE ST_PS regime = diagSeq closure under M[n]):
  A. L5 m_8_4_various_scb_IIIV re-validation (stage-1: 66/66, parts(4,5) 195/195).
  B. L6 m_8_4_various_scb_IIIIV re-validation (342/342; III only so far).
  C. NEW brick checks:
     P1   : c2-rightmost decomposition (slice_scb part (1) engine): unique
            (s,b) with s headed by Dsym e1(jm1) around c = flat(D_{e1 j1} 0),
            on the WIDE domain RT&PT, j1>0, t1!=0 (all conditions I-VI).
     DEC2 : L6(2) brick: Trans N != c2 (nontriviality of the jm3-vs-jm1 nest),
            head of the Trans N decomp = Dsym e1(jm3), RN-length strictness.
     BASE : the L_1 base-case invariants for the (5)(6) induction:
            transJm1(L_1) = jm1, transC1(L_1) = c1, per-branch
            transC2(L_1) = c2 with hole D_{e1 j1} 0 -> D_{e1 jm2} 0,
            surgery wrappers (s1,b1) shared between M and L_1.
  D. IVMINE: the condition-IV vacuity question for L6:
            condIV & jm3<jm1  <=>  condIV & (exists admissible j' in (jm2,j0)).
            Record j0-jm2, adm(jm2), jm3==jm1, admissible-in-gap over ALL
            condIV instances found (deep mine, multiple seeds/strategies).

Per-instance SIGALRM guard; timeouts counted, never dropped.
"""
import sys, signal, random, time
from collections import defaultdict

sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
import red_model as rm
from red_model import (Lng, entry, parent, hasParent, seg, oper, monoT, leR,
                       nextR, diagSeq)
import trans_model as tm
from trans_model import (ZB, Dpt, addBT, flatBT, scb_decomps, adm, Adm,
                         condI, condIII, condV, condVI, bpHeadV, bpHeadT, _c2)

def Pred(M): return M[:-1] if Lng(M) > 1 else M

# memoized Trans/Mark/Red
_origTrans, _origMark, _origRed, _origreduced = tm.Trans, tm.Mark, rm.Red, tm.reduced
_mT, _mM, _mR, _mred = {}, {}, {}, {}
def Trans(M, depth=0):
    k = tuple(M)
    if k not in _mT: _mT[k] = _origTrans(M, depth)
    return _mT[k]
def Mark(M, m, depth=0):
    k = (tuple(M), m)
    if k not in _mM: _mM[k] = _origMark(M, m, depth)
    return _mM[k]
def Red(M, depth=0):
    k = tuple(M)
    if k not in _mR: _mR[k] = _origRed(M, depth)
    return _mR[k]
def reduced(M):
    k = tuple(M)
    if k not in _mred: _mred[k] = _origreduced(M)
    return _mred[k]
tm.Trans, tm.Mark, rm.Red, tm.reduced = Trans, Mark, Red, reduced

class TimeoutErr(Exception): pass
def _handler(signum, frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)

def RightNodes(t):
    ps = t[1]
    if not ps: return []
    u, a = ps[-1][1], ps[-1][2]
    return [u] + RightNodes(a)

def condII(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) == 0 and not adm(M, jp)
def condIV(M):
    j1 = Lng(M)-1; jp = parent(M, 0, j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp) >= entry(M,1,j1) and not adm(M, jp)

def setup(M):
    j1 = Lng(M)-1
    j0 = parent(M, 0, j1)
    jm1 = Adm(M, j0)
    jm2 = parent(M, 1, j1)
    jm3 = Adm(M, jm2)
    Np = seg(M, jm2, j1)
    Lp = seg(M, jm2, j1-1) + [(entry(M,0,j1), entry(M,1,jm2))]
    N = seg(M, jm3, j1)
    return j1, j0, jm1, jm2, jm3, N, Np, Lp

def L_n(M, n):
    j1 = Lng(M)-1; jm2 = parent(M, 1, j1)
    return oper(M, n) + [(entry(M,0,jm2) + n*(entry(M,0,j1)-entry(M,0,jm2)),
                          entry(M,1,jm2))]

def Dj(M, j): return Dpt(entry(M,1,j), ZB)
def Dsym(M, j): return ('D', entry(M,1,j))
def rep(n, xs): return list(xs)*n

def gen_pool(max_len=13, cap=4000, seed=1, ns=(1,2,3), umax=2, vextra=4):
    rng = random.Random(seed)
    seen, out, work = set(), [], []
    for u in range(0, umax+1):
        for v in range(u, u+vextra):
            work.append(diagSeq(u, v))
    while work and len(out) < cap:
        i = rng.randrange(len(work))
        M = work.pop(i)
        k = tuple(M)
        if k in seen: continue
        seen.add(k)
        out.append(M)
        if Lng(M) > max_len: continue
        for n in ns:
            Mn = oper(M, n)
            if Lng(Mn) <= max_len + 3 and tuple(Mn) not in seen:
                work.append(Mn)
    return out

class Stat:
    def __init__(s): s.ok = 0; s.bad = 0; s.cex = []
    def rec(s, good, info):
        if good: s.ok += 1
        else:
            s.bad += 1
            if len(s.cex) < 4: s.cex.append(info)
    def __str__(s): return f"{s.ok}/{s.ok+s.bad}"

# ---------------- L5 (statement = stage-1 draft, EX!-coupled) ----------------
def check_L5(M, S):
    j1, j0, jm1, jm2, jm3, N, Np, Lp = setup(M)
    c1 = Mark(Pred(M), jm1)
    v, t2 = bpHeadV(c1), bpHeadT(c1)
    c2 = _c2(M, j1, j0, v, t2)
    ds = scb_decomps(c2, flatBT(Dj(M, j1)))
    S['L5u'].rec(len(ds) == 1, (M, len(ds)))
    if len(ds) != 1: return
    s, b = ds[0]
    head_ok = len(s) >= 1 and s[0] == Dsym(M, jm1)
    S['L5_1h'].rec(head_ok, (M, s[:2]))
    if not head_ok: return
    s1p, b1p = s[1:], b
    fNp = flatBT(Trans(Np))
    S['L5_2'].rec(fNp == [Dsym(M, jm2)] + s1p + flatBT(Dj(M, j1)) + b1p, (M,))
    fLp = flatBT(Trans(Lp))
    S['L5_2b'].rec(fLp == [Dsym(M, jm2)] + s1p + flatBT(Dj(M, jm2)) + b1p, (M,))
    S['L5_3'].rec(Trans(Pred(Np)) == Dpt(entry(M,1,jm2), t2), (M,))
    t1 = Trans(Pred(M))
    dt = scb_decomps(t1, flatBT(c1))
    S['L5s1u'].rec(len(dt) == 1, (M, len(dt)))
    if len(dt) != 1: return
    s1, b1 = dt[0]
    for n in (1, 2, 3):
        if Lng(L_n(M, n)) > 24: break
        f4 = flatBT(Trans(L_n(M, n)))
        want4 = (s1 + [Dsym(M, jm1)] + rep(n, s1p + [Dsym(M, jm2)]) + ['Z']
                 + rep(n, b1p) + b1)
        S['L5_4'].rec(f4 == want4, (M, n))
        f5 = flatBT(Trans(oper(M, n)))
        want5 = (s1 + [Dsym(M, jm1)] + rep(n-1, s1p + [Dsym(M, jm2)])
                 + flatBT(t2) + rep(n-1, b1p) + b1)
        S['L5_5'].rec(f5 == want5, (M, n))

# ---------------- L6 ----------------------------------------------------------
def check_L6(M, S):
    j1, j0, jm1, jm2, jm3, N, Np, Lp = setup(M)
    c1 = Mark(Pred(M), jm1)
    v, t2 = bpHeadV(c1), bpHeadT(c1)
    c2 = _c2(M, j1, j0, v, t2)
    TM, TN, TPredN = Trans(M), Trans(N), Trans(Pred(N))
    d0 = scb_decomps(TM, flatBT(TN))
    S['L6_1'].rec(len(d0) == 1, (M, len(d0)))
    if len(d0) != 1: return
    s0p, b0p = d0[0]
    # DEC2 brick facts
    S['DEC2ne'].rec(TN != c2, (M,))                      # nontriviality
    S['DEC2rn'].rec(len(RightNodes(TN)) > len(RightNodes(c2)), (M,))
    if entry(M,1,jm3) == entry(M,1,jm1): S['DEC2e1eq'].rec(True, (M,))
    else: S['DEC2e1ne'].rec(True, (M,))
    d1 = scb_decomps(TN, flatBT(c2))
    S['L6u1'].rec(len(d1) == 1, (M, len(d1)))
    if len(d1) != 1: return
    s_, b1p = d1[0]
    head_ok = len(s_) >= 1 and s_[0] == Dsym(M, jm3)
    S['L6_2h'].rec(head_ok, (M, s_[:2]))
    if not head_ok: return
    s1p = s_[1:]
    S['L6_2'].rec(flatBT(TPredN) == [Dsym(M, jm3)] + s1p + flatBT(c1) + b1p, (M,))
    d2 = scb_decomps(c2, flatBT(Dj(M, j1)))
    S['L6u2'].rec(len(d2) == 1, (M, len(d2)))
    if len(d2) != 1: return
    s2p, b2p = d2[0]
    S['L6_4a'].rec(flatBT(Trans(Pred(Np)))
                   == [Dsym(M, jm2)] + s1p + flatBT(c1) + b1p, (M,))
    S['L6_4b'].rec(flatBT(Trans(Np))
                   == [Dsym(M, jm2)] + s1p + flatBT(c2) + b1p, (M,))
    S['L6_4c'].rec(flatBT(Trans(Lp))
                   == [Dsym(M, jm2)] + s1p + s2p + flatBT(Dj(M, jm2)) + b2p + b1p,
                   (M,))
    for n in (1, 2, 3):
        if Lng(L_n(M, n)) > 24: break
        f5 = flatBT(Trans(L_n(M, n)))
        want5 = (s0p + [Dsym(M, jm3)] + rep(n, s1p + s2p + [Dsym(M, jm2)]) + ['Z']
                 + rep(n, b2p + b1p) + b0p)
        S['L6_5'].rec(f5 == want5, (M, n))
        f6 = flatBT(Trans(oper(M, n)))
        want6 = (s0p + [Dsym(M, jm3)] + rep(n-1, s1p + s2p + [Dsym(M, jm2)])
                 + s1p + flatBT(c1) + b1p + rep(n-1, b2p + b1p) + b0p)
        S['L6_6'].rec(f6 == want6, (M, n))

# ---------------- P1 : c2-rightmost decomp on the WIDE domain -----------------
def check_P1(M, S):
    j1, j0, jm1, jm2, jm3, N, Np, Lp = setup(M)
    t1 = Trans(Pred(M))
    if t1 == ZB: return
    c1 = Mark(Pred(M), jm1)
    v, t2 = bpHeadV(c1), bpHeadT(c1)
    c2 = _c2(M, j1, j0, v, t2)
    ds = scb_decomps(c2, flatBT(Dj(M, j1)))
    tag = ('I' if condI(M) else 'II' if condII(M) else 'III' if condIII(M)
           else 'IV' if condIV(M) else 'V' if condV(M) else 'VI' if condVI(M)
           else '?')
    S['P1u_'+tag].rec(len(ds) == 1, (M, len(ds)))
    if len(ds) != 1: return
    s, b = ds[0]
    S['P1h_'+tag].rec(len(s) >= 1 and s[0] == Dsym(M, jm1), (M, s[:2]))
    # b-shape prediction: shared branch b = [')'] if t2!=0 else [];
    # condIV branch (t2!=0): b = [')',')'] if t3-part nonempty else [')']
    if tag in ('I','III','V'):
        S['P1b_shared'].rec(b == ([')'] if t2 != ZB else []), (M, b, t2 == ZB))
    if tag in ('II','IV'):
        JJ1 = len(t2[1]) - 1
        pj = t2[1][JJ1] if t2[1] else None
        ldj = pj is not None and pj[1] == entry(M, 1, j0)
        t3 = ('T', t2[1][:JJ1]) if ldj else t2
        if t2 == ZB:
            S['P1b_IV0'].rec(b == [')'], (M, b))
        else:
            S['P1b_IV1'].rec(b == ([')',')'] if t3 != ZB else [')']),
                             (M, b, t3 == ZB))

# ---------------- BASE : L_1 surgery invariants -------------------------------
def transdata(X):
    j1 = Lng(X)-1
    j0 = parent(X, 0, j1)
    jm1 = Adm(X, j0)
    c1 = Mark(Pred(X), jm1)
    return j1, j0, jm1, c1

def check_BASE(M, S):
    j1, j0, jm1, jm2, jm3, N, Np, Lp = setup(M)
    c1 = Mark(Pred(M), jm1)
    v, t2 = bpHeadV(c1), bpHeadT(c1)
    c2 = _c2(M, j1, j0, v, t2)
    L1 = L_n(M, 1)
    j1L, j0L, jm1L, c1L = transdata(L1)
    S['B_jm1'].rec(j0L == j0 and jm1L == jm1, (M, j0L, jm1L))
    S['B_c1'].rec(c1L == c1, (M,))
    vL, t2L = bpHeadV(c1L), bpHeadT(c1L)
    c2L = _c2(L1, j1L, j0L, vL, t2L)
    # branch classification of L1
    if condVI(M) or adm(M, j0):
        S['B_cls'].rec(condI(L1) or condIII(L1), (M,))
    else:
        S['B_cls'].rec(condII(L1) or condIV(L1), (M,))
    # hole replacement: c2L = c2 with rightmost D_{e1 j1} 0 -> D_{e1 jm2} 0
    fc2, fc2L = flatBT(c2), flatBT(c2L)
    dsM = scb_decomps(c2, flatBT(Dj(M, j1)))
    dsL = scb_decomps(c2L, flatBT(Dj(M, jm2)))
    ok = (len(dsM) == 1 and len(dsL) == 1 and dsM[0] == dsL[0])
    S['B_hole'].rec(ok, (M, len(dsM), len(dsL)))
    # wrappers shared
    t1 = Trans(Pred(M))
    dt = scb_decomps(t1, flatBT(c1))
    dtL = scb_decomps(Trans(Pred(L1)), flatBT(c1L))
    S['B_s1b1'].rec(len(dt) == 1 and dt == dtL, (M, len(dt), len(dtL)))

# ---------------- IVMINE ------------------------------------------------------
def check_IVMINE(M, R):
    j1, j0, jm1, jm2, jm3, N, Np, Lp = setup(M)
    gap_adm = [jp for jp in range(jm2+1, j0) if adm(M, jp)]
    R['n'] += 1
    R['gapw'][j0 - jm2] += 1
    if adm(M, jm2): R['jm2adm'] += 1
    if jm3 == jm1: R['jm3eqjm1'] += 1
    else:
        R['CEX'].append((M, jm2, j0, jm1, jm3, gap_adm))
    if gap_adm: R['gapadm'] += 1

# ---------------- driver ------------------------------------------------------
def run(pool, budget, S, R, do_main=True, miner_only=False):
    t0 = time.time()
    nfil = defaultdict(int)
    timeouts = 0
    for M in pool:
        if time.time() - t0 > budget: break
        j1 = Lng(M)-1
        if j1 <= 1: continue
        if not monoT(M): continue
        if not hasParent(M, 1, j1): continue
        j0 = parent(M, 0, j1)
        jm2 = parent(M, 1, j1)
        jm1 = Adm(M, j0)
        cIII, cIV = condIII(M), condIV(M)
        nfil['base'] += 1
        if cIII: nfil['III'] += 1
        if cIV: nfil['IV'] += 1
        signal.alarm(8)
        try:
            if cIV:
                check_IVMINE(M, R)
            if not miner_only:
                check_P1(M, S)
                if (not condVI(M)) and Adm(M, jm2) == jm1 \
                   and (jm2 < j0 or adm(M, j0)):
                    nfil['L5'] += 1
                    check_L5(M, S)
                    check_BASE(M, S)
                if (cIII or cIV) and Adm(M, jm2) < jm1:
                    nfil['L6'] += 1
                    check_L6(M, S)
        except TimeoutErr:
            timeouts += 1
        except RecursionError:
            timeouts += 1
        finally:
            signal.alarm(0)
    return nfil, timeouts

def main():
    t0 = time.time()
    S = defaultdict(Stat)
    R = {'n': 0, 'jm2adm': 0, 'jm3eqjm1': 0, 'gapadm': 0,
         'gapw': defaultdict(int), 'CEX': []}
    # main validation runs (two fresh seeds)
    for seed, mlen, cap, bud in ((5, 13, 3000, 300), (11, 15, 3000, 300)):
        pool = gen_pool(max_len=mlen, cap=cap, seed=seed)
        nfil, to = run(pool, bud, S, R)
        print(f'[seed {seed}] pool {len(pool)} filters {dict(nfil)} timeouts {to}')
    # dedicated IV miner: wider strategies
    for seed, mlen, cap, ns, um, vx in ((77, 18, 8000, (1,2,3,4), 2, 5),
                                        (101, 20, 8000, (1,2,3,4,5), 3, 6),
                                        (202, 16, 12000, (1,2), 2, 7)):
        pool = gen_pool(max_len=mlen, cap=cap, seed=seed, ns=ns, umax=um, vextra=vx)
        nfil, to = run(pool, 150, S, R, miner_only=True)
        print(f'[mine {seed}] pool {len(pool)} filters {dict(nfil)} timeouts {to}')
    print()
    for k in sorted(S):
        st = S[k]
        print(f'{k:12s} {st}', 'CEX:' if st.bad else '', st.cex[:2] if st.bad else '')
    print()
    print('IVMINE: n=%d jm2adm=%d jm3eqjm1=%d gapadm=%d' %
          (R['n'], R['jm2adm'], R['jm3eqjm1'], R['gapadm']))
    print('  gap widths (j0-jm2):', dict(R['gapw']))
    if R['CEX']:
        print('  !!! jm3<jm1 condIV CEX (L6-IV nonvacuous):')
        for c in R['CEX'][:5]: print('   ', c)
    print('elapsed %.1fs' % (time.time()-t0))

if __name__ == '__main__':
    main()

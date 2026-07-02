#!/usr/bin/env python3
"""r14-S4a: empirical validation of the six deferred §8.4 scb-cluster lemmas
(content.md 4265-4999) over GENUINE ST_PS instances (diagSeq + oper chains,
the inductive definition of ST_PS, pss_defs.thy:439).

L1 m_8_4_rightend_Trans   (条件(III)～(V)の下での右端の置き換えとTransの関係, 4265)
L2 m_8_4_oper_props       (条件(III)～(VI)の下での展開規則の基本性質, 4389)
L3 m_8_4_Trans_scb        (条件(III)～(VI)の下でのTransとscb分解の関係, 4507)
L4 m_8_4_slice_scb        (条件(III)～(V)の下での切片のscb分解, 4605)
L5 m_8_4_various_scb_IIIV (条件(III)～(V)の下での各種scb分解, 4702)
L6 m_8_4_various_scb_IIIIV(条件(III)か(IV)の下での各種scb分解, 4802)

Setup symbols per M (Lng M - 1 = j1):
  j0 = parent M 0 j1, jm1 = Adm M j0, jm2 = parent M 1 j1 (needs hasParent M 1 j1),
  jm3 = Adm M jm2, N = seg M jm3 j1, N' = seg M jm2 j1,
  L' = seg M jm2 (j1-1) @ [(M0j1, M1jm2)],
  L_n = M[n] @ [(M0jm2 + n*(M0j1-M0jm2), M1jm2)].
"""
import sys, signal, random, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
import red_model as rm
from red_model import (Lng, entry, parent, hasParent, seg, oper, monoT, leR,
                       nextR, Pred, diagSeq)
import trans_model as tm
from trans_model import (ZB, Dpt, addBT, flatBT, scb_decomps, adm, Adm,
                         condI, condIII, condV, condVI, bpHeadV, bpHeadT, _c2)

# ---------------- memoized Trans/Mark/Red (Mark recursion is exponential) ----
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

def kind1_c(cterm):
    r = RightNodes(cterm)
    j1r = len(r) - 1
    return (j1r >= 1 and r[0] < r[j1r]
            and all(r[j] >= r[j1r] for j in range(1, j1r)))

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

def Dj(M, j): return Dpt(entry(M,1,j), ZB)          # D_{M_{1,j}} 0
def Dsym(M, j): return ('D', entry(M,1,j))          # string symbol D_{M_{1,j}}
def rep(n, xs): return list(xs)*n

# ---------------- ST_PS pool ------------------------------------------------
def gen_pool(max_len=13, cap=4000, seed=1):
    rng = random.Random(seed)
    seen, out, work = set(), [], []
    for u in range(0, 3):
        for v in range(u, u+4):
            work.append(diagSeq(u, v))
    while work and len(out) < cap:
        i = rng.randrange(len(work))
        M = work.pop(i)
        k = tuple(M)
        if k in seen: continue
        seen.add(k)
        out.append(M)
        if Lng(M) > max_len: continue
        for n in (1, 2, 3):
            Mn = oper(M, n)
            if Lng(Mn) <= max_len + 3 and tuple(Mn) not in seen:
                work.append(Mn)
    return out

# ---------------- per-lemma checks ------------------------------------------
class Stat:
    def __init__(s): s.ok = 0; s.bad = 0; s.cex = []
    def rec(s, good, info):
        if good: s.ok += 1
        else:
            s.bad += 1
            if len(s.cex) < 4: s.cex.append(info)
    def __str__(s): return f"{s.ok}/{s.ok+s.bad}"

def check_L1(M, S):
    j1, j0, jm1, jm2, jm3, N, Np, Lp = setup(M)
    if not (jm2 + 1 < j1): return          # j-2 < j1-1
    TN, TL = Trans(Np), Trans(Lp)
    ds = scb_decomps(TN, flatBT(Dj(M, j1)))
    S['L1u'].rec(len(ds) == 1, (M, 'n_decomps', len(ds)))
    if len(ds) != 1: return
    s, b = ds[0]
    fTL = flatBT(TL)
    caseA = (jm2 == j0) or adm(M, j0)
    good_corr = (fTL == s + flatBT(Dj(M, jm2)) + b)
    if caseA:
        S['L1_2'].rec(good_corr, (M,))
    else:
        # literal article (3): c = D_{M1j0}(t2 + D_{M1j0} 0), t2 = transT2 M
        c1 = Mark(Pred(M), jm1); t2 = bpHeadT(c1)
        lit = (fTL == s + flatBT(Dpt(entry(M,1,j0), addBT(t2, Dj(M, j0)))) + b)
        S['L1_3lit'].rec(lit, (M,))
        S['L1_3corr'].rec(good_corr, (M,))

def check_L2(M, S):
    j1, j0, jm1, jm2, jm3, N, Np, Lp = setup(M)
    # (1)
    if condIII(M) or condIV(M): S['L2_1'].rec(jm2 < j0, (M,))
    if condV(M) or condVI(M):   S['L2_1'].rec(jm2 == j0, (M,))
    # (2) n = 1..3
    for n in (1, 2, 3):
        Ln = L_n(M, n)
        if Lng(Ln) > 26: break
        S['L2_2'].rec(reduced(Ln) and monoT(Ln), (M, n))
    # (3) restriction agreement (i=0 all; i=1 off j1)
    L1seq = L_n(M, 1)
    ok = True
    for a in range(Lng(M)):
        for bb in range(Lng(M)):
            if leR(M, 0, a, bb) != leR(L1seq, 0, a, bb): ok = False
            if a != j1 and bb != j1:
                if leR(M, 1, a, bb) != leR(L1seq, 1, a, bb): ok = False
    S['L2_3'].rec(ok, (M,))
    # (4)
    if condVI(M) or adm(M, j0):
        S['L2_4'].rec(condI(L1seq) or condIII(L1seq), (M, 'VI/adm', L1seq))
    if (not condVI(M)) and (not adm(M, j0)):
        S['L2_4'].rec(condII(L1seq) or condIV(L1seq), (M, 'nVI/nadm', L1seq))
    # (5) n = 2,3.  Literal article: ∃!(s',b') with (5-1)∧(5-2)∧(5-3).
    # Corrected: ∃!(s',b') with (5-1)∧(5-2); (5-3) additionally when
    # ¬zeroT(Pred N') (fails exactly when Trans(Pred N')=0, cond VI & M1jm2=0,
    # where M[n] = L_{n-1}).
    zt = (Lng(Pred(Np)) == 1 and entry(Pred(Np), 1, 0) == 0)  # zeroT(Pred N')
    for n in (2, 3):
        Lnm1, Ln, Mn = L_n(M, n-1), L_n(M, n), oper(M, n)
        if Lng(Ln) > 24: break
        TLnm1, TLn, TMn = Trans(Lnm1), Trans(Ln), Trans(Mn)
        TLp, TPredNp = Trans(Lp), Trans(Pred(Np))
        d1 = scb_decomps(TLnm1, flatBT(Dj(M, jm2)))
        d2 = scb_decomps(TLn, flatBT(TLp))
        d3 = scb_decomps(TMn, flatBT(TPredNp))
        i12 = [sb for sb in d1 if sb in d2]
        inter = [sb for sb in i12 if sb in d3]
        S['L2_5lit'].rec(len(inter) == 1, (M, n, len(d1), len(d2), len(d3)))
        S['L2_5corr12'].rec(len(i12) == 1, (M, n))
        if not zt:
            S['L2_5corr3'].rec(len(i12) == 1 and i12[0] in d3, (M, n))
        else:
            S['L2_5zt_refut'].rec(len(inter) == 0, (M, n))

def check_L3(M, S):
    # domain: RT ∩ PT, j1>1, hasParent M 1 j1
    j1 = Lng(M)-1
    jm2 = parent(M, 1, j1); jm3 = Adm(M, jm2)
    N = seg(M, jm3, j1)
    TM, TN = Trans(M), Trans(N)
    ds = scb_decomps(TM, flatBT(TN))
    k1 = kind1_c(TN)
    S['L3'].rec(len(ds) == 1 and k1, (M, len(ds), k1))

def check_L4(M, S, tag='L4'):
    j1, j0, jm1, jm2, jm3, N, Np, Lp = setup(M)
    c1 = Mark(Pred(M), jm1)
    v, t2 = bpHeadV(c1), bpHeadT(c1)
    c2 = _c2(M, j1, j0, v, t2)
    # (1) unique decomp of c2 by D_{M1j1}0, with D_{M1jm1}-headed s
    ds = scb_decomps(c2, flatBT(Dj(M, j1)))
    S[tag+'u'].rec(len(ds) == 1, (M, len(ds)))
    if len(ds) != 1: return None
    s, b = ds[0]
    head_ok = len(s) >= 1 and s[0] == Dsym(M, jm1)
    S[tag+'_1'].rec(head_ok, (M, s[:2]))
    if not head_ok: return None
    s1p, b1p = s[1:], b
    # (2) Trans N' decomp
    fNp = flatBT(Trans(Np))
    S[tag+'_2'].rec(fNp == [Dsym(M, jm2)] + s1p + flatBT(Dj(M, j1)) + b1p, (M,))
    # (3) Trans(Pred N') = D_{M1jm2} t2
    S[tag+'_3'].rec(Trans(Pred(Np)) == Dpt(entry(M,1,jm2), t2), (M,))
    return s1p, b1p, t2, c1, c2

def check_L5(M, S):
    j1, j0, jm1, jm2, jm3, N, Np, Lp = setup(M)
    r = check_L4(M, S, tag='L5')
    if r is None: return
    s1p, b1p, t2, c1, c2 = r
    # (2b) Trans L'
    fLp = flatBT(Trans(Lp))
    S['L5_2b'].rec(fLp == [Dsym(M, jm2)] + s1p + flatBT(Dj(M, jm2)) + b1p, (M,))
    # s1, b1 : the unique scb decomp of t1 = Trans(Pred M) by c1
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

def check_L6(M, S):
    j1, j0, jm1, jm2, jm3, N, Np, Lp = setup(M)
    c1 = Mark(Pred(M), jm1)
    v, t2 = bpHeadV(c1), bpHeadT(c1)
    c2 = _c2(M, j1, j0, v, t2)
    TM, TN, TPredN = Trans(M), Trans(N), Trans(Pred(N))
    # (1)
    d0 = scb_decomps(TM, flatBT(TN))
    S['L6_1'].rec(len(d0) == 1, (M, len(d0)))
    if len(d0) != 1: return
    s0p, b0p = d0[0]
    # (2)
    d1 = scb_decomps(TN, flatBT(c2))
    S['L6u1'].rec(len(d1) == 1, (M, len(d1)))
    if len(d1) != 1: return
    s_, b1p = d1[0]
    head_ok = len(s_) >= 1 and s_[0] == Dsym(M, jm3)
    S['L6_2h'].rec(head_ok, (M, s_[:2]))
    if not head_ok: return
    s1p = s_[1:]
    S['L6_2'].rec(flatBT(TPredN) == [Dsym(M, jm3)] + s1p + flatBT(c1) + b1p, (M,))
    # (3)
    d2 = scb_decomps(c2, flatBT(Dj(M, j1)))
    S['L6u2'].rec(len(d2) == 1, (M, len(d2)))
    if len(d2) != 1: return
    s2p, b2p = d2[0]
    # (4)
    S['L6_4a'].rec(flatBT(Trans(Pred(Np)))
                   == [Dsym(M, jm2)] + s1p + flatBT(c1) + b1p, (M,))
    S['L6_4b'].rec(flatBT(Trans(Np))
                   == [Dsym(M, jm2)] + s1p + flatBT(c2) + b1p, (M,))
    S['L6_4c'].rec(flatBT(Trans(Lp))
                   == [Dsym(M, jm2)] + s1p + s2p + flatBT(Dj(M, jm2)) + b2p + b1p,
                   (M,))
    # (5)(6)
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

# ---------------- driver ------------------------------------------------------
def main():
    t0 = time.time()
    pool = gen_pool(max_len=int(sys.argv[1]) if len(sys.argv) > 1 else 13,
                    cap=int(sys.argv[2]) if len(sys.argv) > 2 else 4000)
    print('pool size', len(pool), 'maxLng', max(Lng(M) for M in pool))
    from collections import defaultdict
    S = defaultdict(Stat)
    nfil = defaultdict(int)
    timeouts = 0
    budget = float(sys.argv[3]) if len(sys.argv) > 3 else 400.0
    for M in pool:
        if time.time() - t0 > budget:
            print('time budget reached')
            break
        j1 = Lng(M)-1
        if j1 <= 1: continue
        if not monoT(M): continue
        if not hasParent(M, 1, j1): continue
        # base domain: ST ∩ PT ∩ hasParent(1,j1) ∩ j1>1
        j0 = parent(M, 0, j1)
        jm2 = parent(M, 1, j1)
        jm1 = Adm(M, j0)
        cIII, cIV, cV, cVI = condIII(M), condIV(M), condV(M), condVI(M)
        nfil['base'] += 1
        nfil['III'] += cIII; nfil['IV'] += cIV; nfil['V'] += cV; nfil['VI'] += cVI
        signal.alarm(6)
        try:
            check_L2(M, S)                       # L2: j1>1 only
            if jm2 + 1 < j1:
                nfil['L1'] += 1
                check_L1(M, S)
            if reduced(M):                        # ST pool is reduced; L3 domain RT∩PT
                nfil['L3'] += 1
                check_L3(M, S)
            if (not cVI) and Adm(M, jm2) == jm1:
                nfil['L4'] += 1
                check_L4(M, S)
                if jm2 < j0 or adm(M, j0):
                    nfil['L5'] += 1
                    check_L5(M, S)
            if (cIII or cIV) and Adm(M, jm2) < jm1:
                nfil['L6'] += 1
                check_L6(M, S)
        except TimeoutErr:
            timeouts += 1
        except RecursionError:
            timeouts += 1
        finally:
            signal.alarm(0)
    print('filters:', dict(nfil), 'timeouts', timeouts)
    for k in sorted(S):
        st = S[k]
        print(f'{k:10s} {st}', 'CEX:' if st.bad else '',
              st.cex[:2] if st.bad else '')
    print('elapsed %.1fs' % (time.time()-t0))

if __name__ == '__main__':
    main()

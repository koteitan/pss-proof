#!/usr/bin/env python3
"""r14-S5: empirical validation of the two DEFERRED §8.5 scb-decomposition lemmas.

(i)  補題（条件(V)の下での各種scb分解）      article 5213 (paper ~2114)
(ii) 補題（条件(V)の下での基本列のscb分解）  article 5352 (paper ~2125)

Setup (Trans recursion internals, non-degenerate branch: reduced, monoT, j1>0, t1/=0):
  j1 = Lng M - 1, j0 = parent M 0 j1, jm1 = Adm M j0,
  t1 = Trans(Pred M), c1 = Mark(Pred M) jm1, v = bpHeadV c1, t2 = bpHeadT c1,
  c2 = transC2 M, (s1,b1) = THE scb-decomp of t1 with core flat(c1).

Lemma (i): M in ST_PS∩PT_PS, n>=1, j1>1, condV M, ~adm M j0.
  N' = seg M j0 j1;  L' = seg M j0 (j1-1) ++ [(M00j1, M1j0)];
  Ln = M[n] ++ [(M0j0 + n*(M0j1-M0j0), M1j0)].
  Unique (s'1,b'1) with:
  (1) (D_{M1jm1} s'1, D_{M1j1} 0, b'1) scb-decomp of c2
  (2) (D_{M1j0} s'1, D_{M1j1} 0, b'1) scb of Trans N';  (D_{M1j0} s'1, D_{M1j0} 0, b'1) scb of Trans L'
  (3) Trans(Pred N') = D_{M1j0} t2
  (4) flat(Trans Ln)   = s1 [Dv] (s'1 [Dj0])^{n+1} [Z] (b'1)^{n+1} b1
  (5) flat(Trans M[n]) = s1 [Dv] (s'1 [Dj0])^n  flat(t2) (b'1)^n b1

Lemma (ii): M in ST_PS∩PT_PS, n>=1, j1>1, condV M; mn = n-1 if adm M j0 else n.
  Unique (u, s'0, b'0, t') with:
  (1) (s'0, D_u t2, b'0)                    scb of Trans(M[n])
  (2) (s'0, D_u(t2 + D_{M1j0} 0), b'0)      scb of operB (Trans M) (numBT mn)
  (3) (s'0, D_u(t2 + D_{M1j0} t'), b'0)     scb of Trans(M[n+1])

Run: python3 _r14_s5_scbdec.py [timelimit_seconds]
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT, P)
import red_model as rm
import trans_model as tm
from trans_model import (Trans, Mark, Pred, adm, Adm, condV, condI, condIII,
                         condVI, Dpt, addBT, PB, SigmaB, bpHeadV, bpHeadT,
                         flatBT, unflatBT, scb_decomps, ZB, reduced, _c2,
                         isPTB_str)

INF = float('inf')

class TimeoutErr(Exception): pass
def _handler(signum, frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)

def safe(f, *a, budget=2):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except Exception:
        signal.alarm(0); return None

# ---------- Buchholz operB model (pss_paper.thy 744-777, faithful) ----------
def numBT(n): return ('T', [('D', 0, ZB)] * n)
def numNat(z): return len(z[1])

def multBT(a, n):
    out = ZB
    for _ in range(n): out = addBT(out, a)
    return out

def domB(a):
    ps = a[1]
    if not ps: return 'EMPTY'
    if len(ps) == 1:
        _, v, b = ps[0]
        if b == ZB:
            if v == 0: return 'ZERO'          # {0} = {Trm []}
            if v == INF: return 'NAT'
            return ('TB', v - 1)
        db = domB(b)
        if db == 'ZERO': return 'NAT'
        if isinstance(db, tuple) and db[0] == 'TB' and v <= db[1]: return 'NAT'
        return db
    return domB(('T', [ps[-1]]))

def operB(a, z):
    ps = a[1]
    if not ps: return ZB
    if len(ps) == 1:
        _, v, b = ps[0]
        if b == ZB:
            if v == 0: return ZB
            if v == INF: return Dpt(numNat(z) + 1, ZB)
            return z
        db = domB(b)
        if db == 'ZERO':
            return multBT(Dpt(v, operB(b, ZB)), numNat(z) + 1)
        if isinstance(db, tuple) and db[0] == 'TB' and v <= db[1]:
            return Dpt(v, xseq(b, db[1], numNat(z)))
        return Dpt(v, operB(b, z))
    return addBT(('T', ps[:-1]), operB(('T', [ps[-1]]), z))

def xseq(b, u, i):
    if i == 0: return Dpt(u, ZB)
    return operB(b, Dpt(u, xseq(b, u, i - 1)))

# ---------- Trans internal symbols ----------
def internals(M):
    """Return dict of Trans recursion internals for reduced mono M with t1/=0."""
    j1 = Lng(M) - 1
    j0 = parent(M, 0, j1)
    jm1 = Adm(M, j0)
    t1 = Trans(Pred(M))
    c1 = Mark(Pred(M), jm1)
    v = bpHeadV(c1); t2 = bpHeadT(c1)
    c2 = _c2(M, j1, j0, v, t2)
    ds1 = scb_decomps(t1, flatBT(c1))
    return dict(j1=j1, j0=j0, jm1=jm1, t1=t1, c1=c1, v=v, t2=t2, c2=c2, ds1=ds1)

# ---------- generators ----------
def gen_ST(rng, tmax, maxlen=13, maxseed=3, nmax=3, steps=6):
    """Yield genuine ST_PS members: diag seeds + iterated oper."""
    t0 = time.time()
    seen = set()
    while time.time() - t0 < tmax:
        u = rng.randrange(0, maxseed)
        vv = u + rng.randrange(1, maxseed + 1)
        M = diagSeq(u, vv)
        for _ in range(steps):
            key = tuple(M)
            if key not in seen and 2 < Lng(M) <= maxlen:
                seen.add(key)
                yield M
            n = rng.randrange(1, nmax + 1)
            M2 = safe(oper, M, n, budget=1)
            if M2 is None or M2 == M or Lng(M2) > maxlen * 3: break
            M = M2

# ---------- checks ----------
def check_lemma_i(M, ns=(1, 2, 3)):
    """Return (ok_dict, msg) for lemma (i) instance M (guards already filtered)."""
    it = internals(M)
    j1, j0, jm1, v, t2, c2 = it['j1'], it['j0'], it['jm1'], it['v'], it['t2'], it['c2']
    t1, c1, ds1 = it['t1'], it['c1'], it['ds1']
    e1j1 = entry(M, 1, j1); e1j0 = entry(M, 1, j0); e1jm1 = entry(M, 1, jm1)
    res = {}
    # sanity: v = M_{1,jm1}; (s1,b1) unique
    res['v_eq'] = (v == e1jm1)
    res['s1b1_uniq'] = (len(ds1) == 1)
    if not ds1: return res, 'no (s1,b1)'
    s1, b1 = ds1[0]
    # (1) unique (s'1,b'1)
    core1 = flatBT(Dpt(e1j1, ZB))
    d = scb_decomps(c2, core1)
    res['p1_uniq'] = (len(d) == 1)
    if len(d) != 1: return res, 'p1 not unique: %d' % len(d)
    s_full, b_p1 = d[0]
    res['p1_head'] = (len(s_full) >= 1 and s_full[0] == ('D', e1jm1))
    sp1 = s_full[1:]; bp1 = b_p1
    # (2)
    Np = seg(M, j0, j1)
    TN = safe(Trans, Np)
    if TN is None: return res, 'Trans Np timeout'
    d2a = scb_decomps(TN, core1)
    res['p2a'] = (d2a == [([('D', e1j0)] + sp1, bp1)])
    Lp = seg(M, j0, j1 - 1) + [(entry(M, 0, j1), e1j0)]
    TL = safe(Trans, Lp)
    if TL is None: return res, 'Trans Lp timeout'
    core0 = flatBT(Dpt(e1j0, ZB))
    d2b = scb_decomps(TL, core0)
    res['p2b'] = (d2b == [([('D', e1j0)] + sp1, bp1)])
    # (3)
    TPN = safe(Trans, seg(M, j0, j1 - 1))
    if TPN is None: return res, 'Trans PredNp timeout'
    res['p3'] = (TPN == Dpt(e1j0, t2))
    # (4)/(5)
    for n in ns:
        Mn = safe(oper, M, n, budget=1)
        if Mn is None: return res, 'oper timeout'
        Ln = Mn + [(entry(M, 0, j0) + n * (entry(M, 0, j1) - entry(M, 0, j0)), e1j0)]
        TLn = safe(Trans, Ln, budget=4)
        TMn = safe(Trans, Mn, budget=4)
        if TLn is None or TMn is None: return res, 'Trans Ln/Mn timeout n=%d' % n
        rep = sp1 + [('D', e1j0)]
        want4 = s1 + [('D', v)] + rep * (n + 1) + ['Z'] + bp1 * (n + 1) + b1
        want5 = s1 + [('D', v)] + rep * n + flatBT(t2) + bp1 * n + b1
        res['p4_n%d' % n] = (flatBT(TLn) == want4)
        res['p5_n%d' % n] = (flatBT(TMn) == want5)
    return res, None

def lessBT(a, b):
    """[Buc1] lexicographic order (pss_paper.thy 629-634)."""
    pa, pb = a[1], b[1]
    if not pa: return bool(pb)
    if not pb: return False
    if lessBP(pa[0], pb[0]): return True
    if pa[0] == pb[0]: return lessBT(('T', pa[1:]), ('T', pb[1:]))
    return False

def lessBP(p, q):
    (_, u, a), (_, v, b) = p, q
    return u < v or (u == v and lessBT(a, b))

def leBT(a, b): return lessBT(a, b) or a == b

def check_lemma_ii(M, ns=(1, 2, 3)):
    it = internals(M)
    j1, j0, jm1, v, t2 = it['j1'], it['j0'], it['jm1'], it['v'], it['t2']
    t1, c1, c2, ds1 = it['t1'], it['c1'], it['c2'], it['ds1']
    e1j0 = entry(M, 1, j0); e1jm1 = entry(M, 1, jm1)
    admj0 = adm(M, j0)
    res = {}
    if len(ds1) != 1: return res, 'no unique (s1,b1)'
    s1, b1 = ds1[0]
    # (s'1,b'1) from c2 (exists for both adm and nonadm since condV c2 shape same)
    core1 = flatBT(Dpt(entry(M, 1, j1), ZB))
    d = scb_decomps(c2, core1)
    if len(d) != 1: return res, 'c2 decomp not unique'
    sp1 = d[0][0][1:]; bp1 = d[0][1]
    TM = safe(Trans, M, budget=4)
    if TM is None: return res, 'Trans M timeout'
    umax = max(max(a, b) for (a, b) in M) + 2
    obs = []
    for n in ns:
        mn_art = n - 1 if admj0 else n     # article m_n
        mn_cor = mn_art + 1                # A24-shifted m_n
        Mn = safe(oper, M, n, budget=1); Mn1 = safe(oper, M, n + 1, budget=1)
        if Mn is None or Mn1 is None: return res, 'oper timeout'
        TMn = safe(Trans, Mn, budget=4); TMn1 = safe(Trans, Mn1, budget=6)
        TMmn_a = safe(operB, TM, numBT(mn_art), budget=4)
        TMmn_c = safe(operB, TM, numBT(mn_cor), budget=4)
        if TMn is None or TMn1 is None or TMmn_a is None or TMmn_c is None:
            return res, 'Trans/operB timeout n=%d' % n
        # exchange: article m_n vs corrected m_n (Isabelle A23 operB semantics)
        res['exch1art_n%d' % n] = leBT(TMn, TMmn_a)
        res['exch1cor_n%d' % n] = lessBT(TMn, TMmn_c)
        res['exch2_n%d' % n] = lessBT(TMn, TM)
        res['exch3art_n%d' % n] = leBT(TMmn_a, TMn1)
        res['exch3cor_n%d' % n] = lessBT(TMmn_c, TMn1)
        # enumerate candidate (u,s,b) from (1): core D_u t2 of Trans(M[n])
        tuples = []
        for u in range(umax + 1):
            cA = flatBT(Dpt(u, t2))
            for (sA, bA) in scb_decomps(TMn, cA):
                def mid_of(term):
                    f = flatBT(term)
                    ls, lb = len(sA), len(bA)
                    if len(f) < ls + lb: return None
                    if f[:ls] != sA or (lb and f[-lb:] != bA): return None
                    m = f[ls:len(f) - lb] if lb else f[ls:]
                    try:
                        return unflatBT(m)
                    except Exception:
                        return None
                c2obs = mid_of(TMmn_c)
                c3obs = mid_of(TMn1)
                tuples.append((u, tuple(sA), tuple(bA), c2obs, c3obs))
        res['pII_ex_n%d' % n] = (len(tuples) >= 1)
        res['pII_1uniq_n%d' % n] = (len(tuples) <= 1)
        for (u, sA, bA, c2obs, c3obs) in tuples:
            # corrected (2)-core: D_u(t2 + D_{e1j0}(D_{e1j0} 0)) at m_n+1
            cor2 = Dpt(u, addBT(t2, Dpt(e1j0, Dpt(e1j0, ZB))))
            res.setdefault('pII_2cor_n%d' % n, c2obs == cor2)
            # (3) core: D_u(t2 + D_{e1j0} t') for some t' in T_B?
            ok3 = False; tp = None
            if c3obs is not None and c3obs[1] and c3obs[1][0][1] == u:
                w = c3obs[1][0][2]
                nt2 = len(t2[1])
                if len(c3obs[1]) == 1 and list(w[1][:nt2]) == list(t2[1]):
                    restp = w[1][nt2:]
                    if len(restp) == 1 and restp[0][1] == e1j0:
                        ok3 = True; tp = restp[0][2]
            res.setdefault('pII_3shape_n%d' % n, ok3)
            # article t' construction: t2 (adm) / t2 + D_j0 t2 (non-adm)
            t_art = t2 if admj0 else addBT(t2, Dpt(e1j0, t2))
            if ok3: res.setdefault('pII_3tart_n%d' % n, tp == t_art)
            obs.append((n, mn_cor, u, admj0, c2obs, c3obs, tp))
    return res, obs

def main():
    tmax = float(sys.argv[1]) if len(sys.argv) > 1 else 120
    seeds = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    tally = {}
    fails = []
    inst_i = inst_ii = 0
    adm_cnt = nadm_cnt = 0
    seen = set()
    for sd in range(seeds):
        rng = random.Random(1000 + sd)
        for M in gen_ST(rng, tmax / seeds):
            key = tuple(M)
            if key in seen: continue
            seen.add(key)
            if safe(reduced, M, budget=1) is not True: continue
            if not monoT(M): continue
            j1 = Lng(M) - 1
            if j1 <= 1: continue
            if not condV(M): continue
            j0 = parent(M, 0, j1)
            t1 = safe(Trans, Pred(M), budget=3)
            if t1 is None or t1 == ZB: continue
            if adm(M, j0): adm_cnt += 1
            else: nadm_cnt += 1
            # lemma (ii): all condV
            r2, obs2 = check_lemma_ii(M)
            inst_ii += 1
            for k, ok in r2.items():
                a, b = tally.get(('ii', k), (0, 0))
                tally[('ii', k)] = (a + (1 if ok else 0), b + 1)
                if not ok: fails.append(('ii', k, M, obs2))
            if isinstance(obs2, str): fails.append(('ii', 'MSG', M, obs2))
            # lemma (i): non-adm j0 only
            if adm(M, j0): continue
            r1, msg1 = check_lemma_i(M)
            inst_i += 1
            for k, ok in r1.items():
                a, b = tally.get(('i', k), (0, 0))
                tally[('i', k)] = (a + (1 if ok else 0), b + 1)
                if not ok: fails.append(('i', k, M, msg1))
            if msg1: fails.append(('i', 'MSG', M, msg1))
    print('instances: lemma(i) %d, lemma(ii) %d (adm %d / nonadm %d), distinct M %d' %
          (inst_i, inst_ii, adm_cnt, nadm_cnt, len(seen)))
    for k in sorted(tally):
        a, b = tally[k]
        flag = '' if a == b else '   <-- FAIL'
        print('%-22s %d/%d%s' % ('%s.%s' % k, a, b, flag))
    print('fail count:', len(fails))
    for f in fails[:12]:
        print('FAIL:', f[0], f[1], 'M=', f[2], f[3])

if __name__ == '__main__':
    main()

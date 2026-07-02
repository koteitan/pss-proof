#!/usr/bin/env python3
"""r15-S5b run 2: same checks as _r15_s5b_adm_check.py, seed from argv[2] (used: 777),

Under M in ST_PS cap PT_PS, j1 > 1, condV M, adm M j0 (=> jm1 = Adm j0 = j0,
jm2 = parent M 1 j1 = j0), with
  j0e = M_{1,j0}, j1e = M_{1,j1} = j0e + 1,
  (s1,b1) = THE pair of Trans(Pred M) at core flat(c1), c1 = D_{j0e} t2,
  (s0,b0) = tail of THE pair of c2 at core flat(D_{j1e} 0)
            (c2 = D_{j0e}(t2 + D_{j1e} 0)),
  X = s0 @ [D j0e],  Y = [D j0e] @ s0  (rotation),
CLAIMS (to be proven in Isabelle):
  C1 jm1 = j0 = jm2; hasParent M 1 j1
  C2 Trans(seg M j0 j1)      = c2
  C3 Trans(seg M j0 (j1-1))  = c1 = D_{j0e} t2          [zeroT-free]
  C4 Trans(L') = D_{j0e}(t2 + D_{j0e} 0),  L' = seg M j0 (j1-1) ++ [(M0j1, j0e)]
  C5 flat(Trans L_n)  = s1 [Dj0e] X^n [Z] b0^n b1        (n >= 1)
  C6 flat(Trans M[n]) = s1 [Dj0e] X^(n-1) flat(t2) b0^(n-1) b1  (n >= 1)
  C7 flat(operB (Trans M) (numBT n)) = s1 [Dj0e] X^n [Dj0e] [Z] b0^n b1
     (the PROVEN m_8_5_scbdec_fseq_condV closed form; python cross-check)
  E1 Trans(M[n]) < Trans(M)[n]           (corrected exchange (1), m_n+1 = n)
  E2 Trans(M[n]) < Trans(M)              (via Buc1 3.2a; python direct check)
  E3 Trans(M)[n] <= Trans(M[n+1]), strict iff Dpt j0e 0 < t2
  T2 t2 /= 0;  every component of t2 >= D_{j1e} 0 (head >= j1e);
     hence leBT (Dpt j0e 0) t2
Run: python3 _r15_s5b_adm_check.py [timelimit_seconds]
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT)
import red_model as rm
from trans_model import (Trans, Mark, Pred, adm, Adm, condV, Dpt, addBT, PB,
                         bpHeadV, bpHeadT, flatBT, scb_decomps, ZB, reduced,
                         _c2)

INF = float('inf')

class TimeoutErr(Exception): pass
def _handler(signum, frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)

def safe(f, *a, budget=3):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except Exception:
        signal.alarm(0); return None

# ---------- Buchholz operB model (A23 form, as in _r14_s5_scbdec.py) ----------
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
            if v == 0: return 'ZERO'
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

def lessBT(a, b):
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

# ---------- generators ----------
def gen_ST(rng, tmax, maxlen=16, maxseed=4, nmax=4, steps=8):
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

# ---------- per-instance check ----------
def check(M, ns=(1, 2, 3, 4)):
    res, msg = {}, None
    j1 = Lng(M) - 1
    j0 = parent(M, 0, j1)
    jm1 = Adm(M, j0)
    j0e = entry(M, 1, j0); j1e = entry(M, 1, j1)
    t1 = safe(Trans, Pred(M))
    if t1 is None: return res, 'timeout t1'
    c1 = safe(Mark, Pred(M), jm1)
    if c1 is None: return res, 'timeout c1'
    v = bpHeadV(c1); t2 = bpHeadT(c1)
    c2 = _c2(M, j1, j0, v, t2)
    # C1
    res['C1_jm1'] = (jm1 == j0)
    hp1 = hasParent(M, 1, j1)
    res['C1_hp1'] = hp1
    if hp1:
        res['C1_jm2'] = (parent(M, 1, j1) == j0)
    # pairs
    ds1 = scb_decomps(t1, flatBT(c1))
    res['s1b1_uniq'] = (len(ds1) == 1)
    if len(ds1) != 1: return res, 'no unique (s1,b1)'
    s1, b1 = ds1[0]
    dc2 = scb_decomps(c2, flatBT(Dpt(j1e, ZB)))
    res['c2pair_uniq'] = (len(dc2) == 1)
    if len(dc2) != 1: return res, 'no unique c2 pair'
    s_full, b0 = dc2[0]
    res['c2pair_head'] = (len(s_full) >= 1 and s_full[0] == ('D', j0e))
    s0 = s_full[1:]
    # C2
    Np = seg(M, j0, j1)
    TN = safe(Trans, Np)
    if TN is None: return res, 'timeout TN'
    res['C2'] = (TN == c2)
    # C3
    TPN = safe(Trans, seg(M, j0, j1 - 1))
    if TPN is None: return res, 'timeout TPN'
    res['C3'] = (TPN == c1 and c1 == Dpt(j0e, t2))
    # C4
    Lp = seg(M, j0, j1 - 1) + [(entry(M, 0, j1), j0e)]
    TL = safe(Trans, Lp)
    if TL is None: return res, 'timeout TL'
    res['C4'] = (TL == Dpt(j0e, addBT(t2, Dpt(j0e, ZB))))
    # T2 bound
    res['T2_ne'] = (t2 != ZB)
    comps = t2[1]
    res['T2_comps'] = all(leBT(Dpt(j1e, ZB), ('T', [p])) for p in comps) \
                      and bool(comps)
    res['T2_leBT'] = leBT(Dpt(j0e, ZB), t2)
    # C5/C6/C7 + exchanges
    TM = safe(Trans, M, budget=4)
    if TM is None: return res, 'timeout TM'
    X = s0 + [('D', j0e)]
    for n in ns:
        Mn = safe(oper, M, n, budget=1)
        Mn1 = safe(oper, M, n + 1, budget=1)
        if Mn is None or Mn1 is None: return res, 'timeout oper n=%d' % n
        Ln = Mn + [(entry(M, 0, j0) + n * (entry(M, 0, j1) - entry(M, 0, j0)),
                    j0e)]
        TLn = safe(Trans, Ln, budget=5)
        TMn = safe(Trans, Mn, budget=5)
        TMn1 = safe(Trans, Mn1, budget=6)
        FSn = safe(operB, TM, numBT(n), budget=5)
        if TLn is None or TMn is None or TMn1 is None or FSn is None:
            return res, 'timeout n=%d' % n
        res['C5_n%d' % n] = (flatBT(TLn)
            == s1 + [('D', j0e)] + X * n + ['Z'] + b0 * n + b1)
        res['C6_n%d' % n] = (flatBT(TMn)
            == s1 + [('D', j0e)] + X * (n - 1) + flatBT(t2) + b0 * (n - 1) + b1)
        res['C7_n%d' % n] = (flatBT(FSn)
            == s1 + [('D', j0e)] + X * n + [('D', j0e)] + ['Z'] + b0 * n + b1)
        res['E1_n%d' % n] = lessBT(TMn, FSn)
        res['E2_n%d' % n] = lessBT(TMn, TM)
        res['E3le_n%d' % n] = leBT(FSn, TMn1)
        res['E3strict_iff_n%d' % n] = \
            (lessBT(FSn, TMn1) == lessBT(Dpt(j0e, ZB), t2))
    return res, msg

def main():
    tmax = float(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 20260702)
    t0 = time.time()
    tot = {}; bad = {}; inst = 0; timeouts = 0; nonadm = 0
    seen = set()
    for M in gen_ST(rng, tmax):
        if time.time() - t0 > tmax: break
        j1 = Lng(M) - 1
        if j1 <= 1: continue
        if not monoT(M): continue
        if not safe(reduced, M, budget=2): continue
        if not condV(M): continue
        j0 = parent(M, 0, j1)
        if not adm(M, j0):
            nonadm += 1
            print('NON-ADM condV instance!', M)
            continue
        # t1 != 0 check (Pred M nonzero: automatic for Lng >= 3 mono, but check)
        key = tuple(M)
        if key in seen: continue
        seen.add(key)
        inst += 1
        res, msg = check(M)
        if msg is not None:
            timeouts += 1
        for k, ok in res.items():
            tot[k] = tot.get(k, 0) + 1
            if not ok:
                bad[k] = bad.get(k, 0) + 1
                if bad[k] <= 2:
                    print('FAIL %s: M=%s' % (k, M))
    print('=' * 60)
    print('instances (genuine ST, condV, adm j0, j1>1): %d  (timeouts %d,'
          ' nonadm-condV seen %d)' % (inst, timeouts, nonadm))
    for k in sorted(tot):
        b = bad.get(k, 0)
        print('  %-22s %d/%d %s' % (k, tot[k] - b, tot[k],
                                    'FAIL' if b else ''))

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""r16-E4: OT-membership pillar — empirical coverage + the GENERATION-ROUTE step.

Discovered map fact (this front): the article's SS8.7 proof of
補題（Transが標準形を保つこと） (content.md 6122) inducts on the ST_PS GENERATION
RANK k0 (min k with M in S_kT_PS), NOT on Lng/Pred.  The whole mechanized
Pred-induction skeleton (m_8_7_Trans_preserves_OT[_modulo], R2 dstep, R3
newOT/gbt, multiD) is OUR OWN reformulation; the article instead uses, per
oper step M = N[n] with Trans(N) in OT_B:
    [Buc1] Lemma 3.3 (= m_buc1_3_2_OT_B_closed, GREEN r14)   -- OT_B closed
    under t[m] and t[0]^k -- plus the VALUE identity
        Trans(N[n]) = (Trans(N)[m_n]) [0]^k        for some k      (art. 6216)
which needs NO G_B condition, NO descP step, NO newOT: OT-ness flows through
the closure lemma alone.

THIS SCRIPT validates, on the GENUINE regime (oper-BFS from diagSeq seeds
= literal ST_PS members):
  (A) coverage: isOT(Trans M) and isOT(Trans(M[n])) per branch (which
      transC2 case fires: mono/multi, t1=0, conds I..VI, adm j0, j1=1),
  (B) the condV+adm STEP identity (A28-corrected index m_n+1 = n):
      B1: FSn := operB (Trans M) (numBT n) is in OT_B          [closure sanity]
      B2: minimal k with (op0^k)(FSn) == Trans(M[n]);  expect k == 2
      B3: the [0]-trajectory stays on the closed-form strings:
            core c_A = D_e(t2 + D_e(D_e 0))  (m_8_5_scbdec_oper_general_condV_adm)
            --0--> c_B = D_e(t2 + D_e 0)  --0--> c_C = D_e t2
          at the SAME (S,B) pair, i.e. flat(op0^i FSn) = S+flat(c_i)+B,
      B4: domB(FSn) = TBv(e-1) for e>0, NAT for e=0   [the spine-transport
          hypothesis of operB_TBv_body_spine / operB_scb_spine]
  (C) the per-cond (m,k) TABLE: for each genuine (M,n) mono keystone
      instance, the smallest (m,k), m in {n-2..n+1}, k <= KMAX with
      Trans(M[n]) == (op0^k)(operB (Trans M) (numBT m)) — the map datum
      that tells which conds get the generation step from which index.

Run: python3 _r16_e4_check.py [tmax_seconds] [seed...]
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT, P)
import red_model as rm
from trans_model import (Trans, Mark, Pred, adm, Adm, condI, condIII, condV,
                         condVI, Dpt, addBT, PB, bpHeadV, bpHeadT, flatBT,
                         scb_decomps, ZB, reduced)
import buchholz as bu

INF = float('inf')

class TimeoutErr(Exception): pass
def _handler(signum, frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)

def safe(f, *a, budget=3):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TimeoutErr, RecursionError, AssertionError):
        signal.alarm(0); return None

# ---------- Buchholz operB model on the ('T',ps) repr (A23 form, as r15) ----
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

def op0(a): return operB(a, numBT(0))

# ---------- OT via buchholz.py (independent model) ----------
def bucOf(t): return [('D', p[1], bucOf(p[2])) for p in t[1]]
def isOT(t): return bu.in_OT(bucOf(t))

# ---------- branch classification ----------
def condII(M):
    j1 = Lng(M) - 1; jp = parent(M, 0, j1)
    return entry(M, 1, j1) == 0 and not adm(M, jp)
def condIV(M):
    j1 = Lng(M) - 1; jp = parent(M, 0, j1)
    return (entry(M, 1, j1) > 0 and entry(M, 1, jp) >= entry(M, 1, j1)
            and not adm(M, jp))

def branch_of(M):
    j1 = Lng(M) - 1
    if not monoT(M): return 'multi'
    if j1 == 0: return 'single'
    t1 = safe(Trans, Pred(M))
    if t1 is None: return 'timeout'
    if t1 == ZB: return 't1zero'
    tag = None
    for nm, c in (('I', condI), ('II', condII), ('III', condIII),
                  ('IV', condIV), ('V', condV), ('VI', condVI)):
        if c(M): tag = nm; break
    if tag is None: tag = '??'
    jp = parent(M, 0, j1)
    return 'cond%s%s%s' % (tag, '-adm' if adm(M, jp) else '-nadm',
                           '-j1eq1' if j1 == 1 else '')

# ---------- generators ----------
def gen_ST(rng, tmax, maxlen=13, maxseed=3, nmax=3, steps=6):
    t0 = time.time()
    seen = set()
    while time.time() - t0 < tmax:
        u = rng.randrange(0, maxseed)
        vv = u + rng.randrange(1, maxseed + 1)
        M = diagSeq(u, vv)
        for _ in range(steps):
            key = tuple(M)
            if key not in seen and 1 < Lng(M) <= maxlen:
                seen.add(key)
                yield M
            n = rng.randrange(1, nmax + 1)
            M2 = safe(oper, M, n, budget=1)
            if M2 is None or M2 == M or Lng(M2) > maxlen * 3: break
            M = M2

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    seeds = [int(s) for s in sys.argv[2:]] or [20260702, 777]
    KMAX = 14
    covA = {}          # branch -> [ok, tot] for isOT(Trans M)
    covAn = {}         # branch -> [ok, tot] for isOT(Trans(M[n]))
    B = dict(inst=0, B1=0, B2=0, B3=0, B4=0, kvals={}, fails=[])
    Ctab = {}          # branch -> {(m_off,k): count}  m_off = m - n
    Cnone = {}         # branch -> count with NO (m,k) found
    per_seed = tmax // max(len(seeds), 1)
    pool = 0
    for sd in seeds:
        rng = random.Random(sd)
        t0 = time.time()
        for M in gen_ST(rng, per_seed):
            if time.time() - t0 > per_seed: break
            pool += 1
            TM = safe(Trans, M, budget=4)
            if TM is None: continue
            br = branch_of(M)
            covA.setdefault(br, [0, 0])
            covA[br][1] += 1
            covA[br][0] += 1 if isOT(TM) else 0
            j1 = Lng(M) - 1
            for n in (1, 2, 3):
                Mn = safe(oper, M, n, budget=1)
                if Mn is None: continue
                TMn = safe(Trans, Mn, budget=5)
                if TMn is None: continue
                covAn.setdefault(br, [0, 0])
                covAn[br][1] += 1
                covAn[br][0] += 1 if isOT(TMn) else 0
                # (C) generation-step (m,k) table for mono keystone hosts
                if br.startswith('cond') and j1 > 1:
                    found = None
                    for moff in (0, -1, -2, 1):
                        m = n + moff
                        if m < 0: continue
                        t = safe(operB, TM, numBT(m), budget=4)
                        if t is None: continue
                        for k in range(KMAX + 1):
                            if t == TMn:
                                found = (moff, k); break
                            t = safe(op0, t, budget=4)
                            if t is None: break
                        if found: break
                    key = Ctab.setdefault(br, {})
                    if found: key[found] = key.get(found, 0) + 1
                    else: Cnone[br] = Cnone.get(br, 0) + 1
                # (B) condV+adm detailed trajectory
                if br == 'condV-adm' and j1 > 1:
                    jp = parent(M, 0, j1)
                    e = entry(M, 1, jp); j1e = entry(M, 1, j1)
                    c1 = safe(Mark, Pred(M), Adm(M, jp))
                    if c1 is None: continue
                    t2 = bpHeadT(c1)
                    B['inst'] += 1
                    FS = safe(operB, TM, numBT(n), budget=4)
                    if FS is None: continue
                    ok1 = isOT(FS)
                    B['B1'] += 1 if ok1 else 0
                    # B4 dom
                    dFS = domB(FS)
                    okd = (dFS == ('TB', e - 1)) if e > 0 else (dFS == 'NAT')
                    B['B4'] += 1 if okd else 0
                    # B2/B3 trajectory
                    cA = Dpt(e, addBT(t2, Dpt(e, Dpt(e, ZB))))
                    cB = Dpt(e, addBT(t2, Dpt(e, ZB)))
                    cC = Dpt(e, t2)
                    dsA = scb_decomps(FS, flatBT(cA))
                    ok3 = False
                    t_1 = safe(op0, FS, budget=4)
                    t_2 = safe(op0, t_1, budget=4) if t_1 is not None else None
                    if dsA and t_1 is not None and t_2 is not None:
                        S, Bb = dsA[0]
                        ok3 = (flatBT(t_1) == S + flatBT(cB) + Bb
                               and flatBT(t_2) == S + flatBT(cC) + Bb)
                    B['B3'] += 1 if ok3 else 0
                    kfound = None
                    t = FS
                    for k in range(KMAX + 1):
                        if t == TMn: kfound = k; break
                        t = safe(op0, t, budget=4)
                        if t is None: break
                    if kfound is not None:
                        B['B2'] += 1
                        B['kvals'][kfound] = B['kvals'].get(kfound, 0) + 1
                    else:
                        if len(B['fails']) < 5:
                            B['fails'].append((M, n))
    print('pool =', pool)
    print('\n(A) isOT(Trans M) per branch:')
    for br in sorted(covA): print('  %-22s %d/%d' % (br, covA[br][0], covA[br][1]))
    print('(A) isOT(Trans(M[n])) per branch (n=1..3):')
    for br in sorted(covAn): print('  %-22s %d/%d' % (br, covAn[br][0], covAn[br][1]))
    print('\n(B) condV-adm generation step: inst =', B['inst'])
    print('  B1 FSn in OT      :', B['B1'], '/', B['inst'])
    print('  B2 exists k<=%d    :' % KMAX, B['B2'], '/', B['inst'], ' kvals =', B['kvals'])
    print('  B3 trajectory     :', B['B3'], '/', B['inst'])
    print('  B4 domB(FSn)      :', B['B4'], '/', B['inst'])
    if B['fails']: print('  B2 FAILS:', B['fails'])
    print('\n(C) generation (m-n, k) table per branch:')
    for br in sorted(Ctab):
        tot = sum(Ctab[br].values()) + Cnone.get(br, 0)
        print('  %-22s tot=%d none=%d %s' % (br, tot, Cnone.get(br, 0),
              sorted(Ctab[br].items(), key=lambda x: -x[1])[:6]))
    for br in sorted(set(Cnone) - set(Ctab)):
        print('  %-22s tot=%d none=%d' % (br, Cnone[br], Cnone[br]))

if __name__ == '__main__':
    main()

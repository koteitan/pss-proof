#!/usr/bin/env python3
"""r28-OTMEM probe 3: the definitive stepval truth map.

Branch key = (branch, e-class, n-class) where e = entry M 1 (parent M 0 j1)
(the marked-leaf head; e=0 <=> [0]-steps annihilate locally, e>=1 <=> the
root kind-1 guard collapses the whole term).  Pred-corner (M[n] = Pred M)
separated; zero-last-col separated.

Validates the EXACT witnesses to be proven in Isabelle:
  W1 condVI-adm  n>=2         : (m,k) = (n-2, 0)   [c613x (2)]
  W2 condVI-nadm n>=1         : (m,k) = (n-1, 0)   [c6nx (2)]
  W3 condI j1>1 j0=0 n>=1     : (m,k) = (n-1, 0)   [n1 + replicate]
  W4 condI j1>1 j0>0 n>=2     : (m,k) = (n-1, 0)   [exchI residual - true?]
  W5 condI j1=1 n>=2          : u>0: (n-1,0); u=0: (n-2,0)
  W6 condVI j1=1 n>=2         : (n-2, 0)
  W7 zero-last-col any n      : (0, 0)  [operB kills trailing D_0 0]
  W8 Lng=2 n=1 (Pred single)  : Trans(Pred M) in {0, D_x 0}
  W9 condII n>=2              : exists m. (m, 0)
Refutation reconfirmation:
  R1 condIII/IV/V (e>=1) n>=2 : NO (m,k), orbit dies (DIED)
  R2 condVI-adm n=1 (u>=1)    : NO (m,k)
  R3 condV-adm e>=1           : breed and test (expect NO) - r16 (n,2) was e=0-only?
  R4 mono Pred-corner n>=2 nonzero-last (no-parent): reachable at all?
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT, P, idx1)
from trans_model import (Trans, Mark, Pred, adm, Adm, condI, condIII, condV,
                         condVI, Dpt, addBT, ZB, flatBT)
from _r28_otx_widewin import (numBT, operB, op0, domB, branch_of, safe,
                              condII, condIV)

def stepval_at(TM, TMn, m, k):
    t = safe(operB, TM, numBT(m), budget=5)
    if t is None: return None
    for _ in range(k):
        t = safe(op0, t, budget=5)
        if t is None: return None
    return t == TMn

def find_mk_definitive(TM, TMn, mmax=8, kcap=400):
    """(m,k) search; returns ('HIT',m,k) / ('DIED',) if all orbits died / ('CAP',)."""
    all_died = True
    for m in range(mmax + 1):
        t = safe(operB, TM, numBT(m), budget=5)
        if t is None: all_died = False; continue
        k = 0
        while k <= kcap:
            if t == TMn: return ('HIT', m, k)
            if t == ZB: break
            t = safe(op0, t, budget=5)
            if t is None: all_died = False; break
            k += 1
        else:
            all_died = False
    return ('DIED',) if all_died else ('CAP',)

def gen_ST(rng, tmax, maxlen=15, maxseed=3, nmax=4, steps=8):
    t0 = time.time()
    seen = set()
    while time.time() - t0 < tmax:
        u = rng.randrange(0, maxseed)
        vv = u + rng.randrange(1, maxseed + 1)
        M = diagSeq(u, vv)
        for _ in range(steps):
            key = tuple(M)
            if key not in seen and 1 <= Lng(M) <= maxlen:
                seen.add(key)
                yield M
            n = rng.randrange(1, nmax + 1)
            M2 = safe(oper, M, n, budget=1)
            if M2 is None or M2 == M or Lng(M2) > maxlen * 3: break
            M = M2

def key_of(M, n, Mn):
    j1 = Lng(M) - 1
    if j1 == 0: return 'fixpoint(Lng1)'
    zc = (entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0)
    if Mn == Pred(M):
        if n == 1: return 'pred-n1'
        return 'pred-n2+-%s' % ('zerocol' if zc else 'NONZEROCOL')
    br = branch_of(M)
    if br == 'multi': return 'multi-NP'
    e = entry(M, 1, parent(M, 0, j1))
    return '%s-e%s%s' % (br, '0' if e == 0 else 'P',
                         '' if j1 > 1 else '-j1eq1')

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 420
    seeds = [int(s) for s in sys.argv[2:]] or [20260703, 555, 31337]
    per_seed = tmax // max(len(seeds), 1)
    ok = {}; bad = {}; tab = {}
    witfail = []
    pool = 0
    for sd in seeds:
        rng = random.Random(sd)
        t0 = time.time()
        for M in gen_ST(rng, per_seed):
            if time.time() - t0 > per_seed: break
            pool += 1
            TM = safe(Trans, M, budget=5)
            if TM is None: continue
            j1 = Lng(M) - 1
            for n in (1, 2, 3, 4):
                Mn = safe(oper, M, n, budget=1)
                if Mn is None: continue
                TMn = safe(Trans, Mn, budget=6)
                if TMn is None: continue
                key = key_of(M, n, Mn)
                # --- witness checks per key
                expect = None   # (m,k) or 'NONE' or 'skip'
                if key == 'fixpoint(Lng1)': expect = 'skip'   # IH leg
                elif key == 'pred-n1' or key.startswith('pred-n2'):
                    br = branch_of(M)
                    zc = key.endswith('zerocol') and not key.endswith('NONZEROCOL')
                    if key == 'pred-n1':
                        # green subcases: Lng=2 / t1zero / zerocol / condI(j1>1) / condVI-nadm
                        if Lng(M) == 2: expect = 'skip'  # singleton value leg
                        elif entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0:
                            expect = (0, 0)
                        elif br.startswith('condI-') and j1 > 1:
                            expect = (0, 0)
                        elif br.startswith('condVI-nadm') and j1 > 1:
                            expect = (0, 0)
                        else: expect = None  # residual OTpred: just record table
                    else:
                        expect = (0, 0) if zc else None
                elif key.startswith('condI-'):
                    if '-j1eq1' in key:
                        u = entry(M, 1, 0)
                        expect = (n - 1, 0) if u > 0 else (n - 2, 0)
                    else:
                        expect = (n - 1, 0)
                elif key.startswith('condII-'):
                    expect = 'existsm'
                elif key.startswith('condVI-adm') or (key.startswith('condVI-e') and adm(M, parent(M, 0, j1))):
                    pass
                if key.startswith('condVI') and '-j1eq1' not in key:
                    jp = parent(M, 0, j1)
                    expect = (n - 2, 0) if adm(M, jp) else (n - 1, 0)
                elif key.startswith('condVI') and '-j1eq1' in key:
                    expect = (n - 2, 0)
                if key.startswith('condIII') or key.startswith('condIV') or key.startswith('condV-'):
                    expect = 'probe'   # deep-probe the truth per e-class
                # --- evaluate
                if expect == 'skip': continue
                if isinstance(expect, tuple):
                    m, k = expect
                    if m < 0:
                        r = find_mk_definitive(TM, TMn, mmax=6, kcap=120)
                        tab.setdefault(key + '|n%d' % n, {}).setdefault(r[0] + str(r[1:]), 0)
                        tab[key + '|n%d' % n][r[0] + str(r[1:])] = tab[key + '|n%d' % n].get(r[0] + str(r[1:]), 0) + 1
                        continue
                    got = stepval_at(TM, TMn, m, k)
                    d = ok if got else bad
                    d[key] = d.get(key, 0) + 1
                    if not got and len(witfail) < 10:
                        witfail.append((key, n, M))
                elif expect == 'existsm':
                    r = find_mk_definitive(TM, TMn, mmax=8, kcap=10)
                    good = (r[0] == 'HIT' and r[2] == 0)
                    d = ok if good else bad
                    d[key] = d.get(key, 0) + 1
                    if not good and len(witfail) < 10:
                        witfail.append((key, n, M, r))
                else:
                    r = find_mk_definitive(TM, TMn, mmax=6, kcap=200)
                    kk = key + '|n%d' % ('1' == str(n) and 1 or n)
                    kk = '%s|n%d' % (key, n)
                    tab.setdefault(kk, {})
                    rs = r[0] + (str(r[1:]) if r[0] == 'HIT' else '')
                    tab[kk][rs] = tab[kk].get(rs, 0) + 1
    print('pool =', pool)
    print('\nWITNESS ok / bad:')
    for k in sorted(set(ok) | set(bad)):
        print('  %-34s ok=%-5d bad=%d' % (k, ok.get(k, 0), bad.get(k, 0)))
    if witfail:
        print('WITNESS FAILURES:')
        for w in witfail: print('  ', w)
    print('\nPROBE table (residual/interleave keys):')
    for kk in sorted(tab):
        tot = sum(tab[kk].values())
        print('  %-34s tot=%-4d %s' % (kk, tot,
              sorted(tab[kk].items(), key=lambda x: -x[1])[:4]))

if __name__ == '__main__':
    main()

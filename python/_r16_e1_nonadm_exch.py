#!/usr/bin/env python3
"""r16-E1: exchange-shape map on the (newly REACHABLE) non-adm condV regime,
plus DEEP re-validation of the adm-regime residuals (HB / t2lb).

Background: rounds 14-15 believed non-adm condV unreachable in genuine ST_PS
(0/20049, shallow).  _r16_e1_chains.py found genuine oper-chain instances at
Lng >= 9 (yaBMS-confirmed standard).  This harness mines them and answers:
  [N-E2]    lessBT (Trans M[n]) (Trans M)?
  [N-minK]  min k with leBT (Trans M[n]) (Trans(M)[k]); strict?
            (article printed m_n = n for non-adm; A28 shifted the adm case)
  [N-E3]    leBT (Trans(M)[k]) (Trans M[n+1]) at k = printed n and k = minK
  [N-hp1]   nextR M 1 j0 j1 (hypothesis of the Joints/FirstNodes lemma)?
  [N-HB]    every component of t2 >= D_{M1,j1} 0 (article part (3), non-adm)
  [N-t2lb]  leBT (D_{e} 0) t2, e = entry M 1 jm1?  (which e is right here?)
  [A-HB]    the adm-regime HB residual re-checked on DEEP (Lng>=9) instances
Run: python3 _r16_e1_nonadm_exch.py [secs_mine] [secs_check] [seed]
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from _r15_vx_lib import (Trans, Mark, operB, numBT, lessBT, leBT, guarded, SKIP,
                         internals, ZB, Dpt, PB, flatBT)
from red_model import Lng, entry, parent, oper, diagSeq, monoT
import red_model as rm
import trans_model as tm
from trans_model import adm, Adm, condV, reduced, Pred

def mine(tmax, rng, want_nonadm=40):
    t0 = time.time(); seen = set()
    nonadm, adm_deep = [], []
    while time.time() - t0 < tmax and len(nonadm) < want_nonadm:
        u = rng.randrange(0, 6)
        vv = u + rng.randrange(1, 7)
        M = diagSeq(u, vv)
        for _ in range(rng.randrange(6, 34)):
            if time.time() - t0 > tmax: break
            n = rng.choice((1,1,1,2,2,2,2,3,4))
            M2 = guarded(oper, M, n, budget=2)
            if M2 is SKIP or M2 is None or M2 == M or Lng(M2) > 24:
                break
            M = M2
            key = tuple(M)
            if key in seen: continue
            seen.add(key)
            j1 = Lng(M) - 1
            if j1 <= 1 or not monoT(M) or not condV(M): continue
            j0 = parent(M, 0, j1)
            if adm(M, j0):
                if Lng(M) >= 9 and len(adm_deep) < 60:
                    adm_deep.append(M)
            else:
                nonadm.append(M)
    return nonadm, adm_deep

class Tally:
    def __init__(self): self.d = {}
    def add(self, k, ok):
        p, t = self.d.get(k, (0, 0))
        self.d[k] = (p + (1 if ok else 0), t + 1)
    def report(self):
        for k in sorted(self.d):
            p, t = self.d[k]
            print('  %-26s %d/%d%s' % (k, p, t, '' if p == t else '  <-- not-all'))

def main():
    tmine = float(sys.argv[1]) if len(sys.argv) > 1 else 240
    tchk = float(sys.argv[2]) if len(sys.argv) > 2 else 480
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 777
    rng = random.Random(seed)
    nonadm, adm_deep = mine(tmine, rng)
    # dedup by tuple
    nonadm = [list(t) for t in dict.fromkeys(tuple(m) for m in nonadm)]
    adm_deep = [list(t) for t in dict.fromkeys(tuple(m) for m in adm_deep)]
    print('mined: nonadm=%d  adm_deep=%d' % (len(nonadm), len(adm_deep)))
    T = Tally(); t0 = time.time(); to = 0
    minK_hist = {}
    for M in nonadm:
        if time.time() - t0 > tchk: break
        j1 = Lng(M) - 1; j0 = parent(M, 0, j1)
        jm1 = Adm(M, j0)
        TM = guarded(Trans, M, budget=20)
        if TM is SKIP or TM is None: to += 1; continue
        ii = internals(M)
        if ii is None: to += 1; continue
        t2 = ii['t2']
        e_j1 = entry(M, 1, j1); e_j0 = entry(M, 1, j0); e_jm1 = entry(M, 1, jm1)
        T.add('N-hp1 nextR1 j0 j1', rm.nextR(M, 1, j0, j1))
        T.add('N-jm1<j0', jm1 < j0)
        T.add('N-t2ne', t2 != ZB)
        T.add('N-HB comps>=Dj1e', bool(t2[1]) and
              all(leBT(Dpt(e_j1, ZB), ('T', [p])) for p in t2[1]))
        T.add('N-t2lb Dv0<=t2 (v=head c1)', leBT(Dpt(ii['v'], ZB), t2)
              if ii['v'] != 0 or True else False)
        for n in (1, 2, 3):
            Mn = guarded(oper, M, n, budget=2)
            Mn1 = guarded(oper, M, n + 1, budget=2)
            if Mn is SKIP or Mn1 is SKIP: to += 1; break
            TMn = guarded(Trans, Mn, budget=20)
            TMn1 = guarded(Trans, Mn1, budget=25)
            if TMn is SKIP or TMn is None or TMn1 is SKIP or TMn1 is None:
                to += 1; break
            T.add('N-E2 n=%d' % n, lessBT(TMn, TM))
            mink = None
            for k in range(0, n + 4):
                FSk = guarded(operB, TM, numBT(k), budget=15)
                if FSk is SKIP or FSk is None: break
                if leBT(TMn, FSk):
                    mink = k; break
            if mink is None:
                T.add('N-minK exists<=n+3 n=%d' % n, False); continue
            T.add('N-minK exists<=n+3 n=%d' % n, True)
            minK_hist[(n, mink)] = minK_hist.get((n, mink), 0) + 1
            T.add('N-minK==n n=%d' % n, mink == n)
            FSn = guarded(operB, TM, numBT(n), budget=15)
            if not (FSn is SKIP or FSn is None):
                T.add('N-printed1 le@n n=%d' % n, leBT(TMn, FSn))
                T.add('N-strict1 @n n=%d' % n, lessBT(TMn, FSn))
                T.add('N-E3 printed le@n n=%d' % n, leBT(FSn, TMn1))
    print('non-adm regime checks (timeouts %d):' % to)
    T.report()
    print('  minK histogram {(n, minK): count}:', minK_hist)
    # ---- adm-regime deep re-validation of HB/t2lb ----
    TA = Tally(); toA = 0; t0 = time.time()
    for M in adm_deep:
        if time.time() - t0 > tchk / 2: break
        j1 = Lng(M) - 1; j0 = parent(M, 0, j1)
        ii = internals(M)
        if ii is None: toA += 1; continue
        t2 = ii['t2']
        e_j1 = entry(M, 1, j1); e_j0 = entry(M, 1, j0)
        TA.add('A-t2ne', t2 != ZB)
        TA.add('A-HB comps>=Dj1e', bool(t2[1]) and
               all(leBT(Dpt(e_j1, ZB), ('T', [p])) for p in t2[1]))
        TA.add('A-t2lb Dj0e0<=t2', leBT(Dpt(e_j0, ZB), t2))
    print('adm regime DEEP (Lng>=9) residual checks (timeouts %d):' % toA)
    TA.report()

if __name__ == '__main__':
    main()

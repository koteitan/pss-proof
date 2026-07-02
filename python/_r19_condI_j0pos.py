#!/usr/bin/env python3
r"""r19-CONDI: validation for the §8.1 condition-(I), j0>0 exchange (1)
    (the dispatcher hypothesis exchI of f7x_fseq_descend_mono / lemma
     c1x_condI_j0pos_exchange in layerC/pss_scratch.thy).

Over the GENUINE regime (reduced & monoT & condI & j0>0 & j1>1) it checks:

  (A) EXCHANGE EQUALITY   Trans(M[m]) == operB(Trans M)(numBT (m-1))   (m = 2..6)
      and the DESCENT     lessBT(Trans(M[m]), Trans M).

  (B) NON-VACUITY of the CF_I residual (dM + lhsCF): for every host there EXIST
      (s,b,u,v,t0,t1) with
        dM :  scb_decomp(Trans M) s (flatBT (D_u(t0 + D_v(t1 + D_0 0)))) b     and
        lhsCF: Trans(M[k+1]) == unflatBT(s + flatBT(D_u(t0 + (D_v t1)*(k+1))) + b)
      i.e. the two hypotheses of c1x_condI_j0pos_exchange are simultaneously
      satisfiable (deepest fold-site + the model's own scb_decomps).

Hosts are constructed by direct brute enumeration (reduced/monoT/condI/j0>0),
which is fast; the oper-closure filter is O(n^5) in reduced() and hangs on big
pools, so it is NOT used here.

Result (seed-free brute, Lng 3..6):
  found ~95-135 hosts;  EXCHANGE 475/475, DESCENT 475/475, no failures;
  deepest-site  scb_exists = lhsCF_valid = BOTH = 100% (0 vacuous).
  Trans M top-width ranges 1..4 (non-spine hosts included), so the CF_I shape
  is validated with NON-TRIVIAL surgery pair (s,b), not only pure spines.

Run:  python3 _r19_condI_j0pos.py
"""
import sys, os, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trans_model as tm
from red_model import Lng, parent, oper, fmt, entry, monoT, zeroT, reduced
from trans_model import (condI as tcondI, flatBT, Dpt, addBT, ZB, unflatBT,
                         scb_decomps)
from _r15_vx_lib import operB, numBT, multBT, lessBT

def T(M): return tm.Trans(list(M))
def pr(*a): print(*a, flush=True)

D0z = ('D', 0, ZB)   # D_0 0

def isj(M):
    if Lng(M) < 3 or zeroT(M) or entry(M, 1, Lng(M) - 1) != 0: return False
    if not monoT(M) or not reduced(M): return False
    j1 = Lng(M) - 1; j0 = parent(M, 0, j1)
    return j0 is not None and j1 > 1 and tcondI(M) and j0 > 0

def find_dM_deep(TM):
    """Deepest rightmost-spine fold-site X = D_u(t0 + D_v(t1 + D_0 0))."""
    t = TM; best = None
    while t[1]:
        X = t[1][-1]; bodyU = X[2]
        if bodyU[1]:
            Y = bodyU[1][-1]; bodyV = Y[2]
            if bodyV[1] and bodyV[1][-1] == D0z:
                best = (X[1], Y[1], ('T', bodyU[1][:-1]),
                        ('T', bodyV[1][:-1]), ('T', [X]))
        t = X[2]
    return best

def gen_len(L, maxe):
    cols = [(a, b) for a in range(maxe + 1) for b in range(maxe + 1)]
    for tail in itertools.product(cols, repeat=L - 1):
        yield [(0, 0)] + list(tail)

def top_width(TM):
    w = 0; t = TM
    while t[1]:
        w = max(w, len(t[1])); t = t[1][-1][2]
    return w

def main():
    t0 = time.time()
    hosts = []; checked = 0
    for L in range(3, 7):
        n = 0
        for M in gen_len(L, min(L, 4)):
            checked += 1
            if checked > 3_000_000: break
            if entry(M, 1, L - 1) != 0: continue
            if not monoT(M) or not reduced(M) or not isj(M): continue
            hosts.append(M); n += 1
            if n >= 60: break
    pr(f"hosts={len(hosts)} (Lng 3..6)  build_s={round(time.time()-t0,1)}")
    exch_ok = exch_bad = nd = 0; widths = set()
    scb_ok = lhs_ok = both = none = 0; cex = []
    for M in hosts:
        TM = T(M); widths.add(top_width(TM))
        # (A) exchange + descent
        for m in range(2, 7):
            lhs = T(oper(M, m)); rhs = operB(TM, numBT(m - 1))
            if lhs == rhs: exch_ok += 1
            else:
                exch_bad += 1
                if len(cex) < 8: cex.append((fmt(M), m))
            if not lessBT(lhs, TM): nd += 1
        # (B) CF_I non-vacuity (dM + lhsCF)
        r = find_dM_deep(TM)
        if r is None: none += 1; continue
        u, v, tt0, tt1, Xterm = r
        decs = scb_decomps(TM, flatBT(Xterm))
        if decs:
            scb_ok += 1
            s, b = decs[0]
            good = all(T(oper(M, k + 1)) ==
                       unflatBT(s + flatBT(Dpt(u, addBT(tt0,
                                 multBT(Dpt(v, tt1), k + 1)))) + b)
                       for k in (1, 2))
            if good: lhs_ok += 1
            if good: both += 1
    pr(f"(A) EXCHANGE ok={exch_ok} bad={exch_bad}  DESCENT_fail={nd}  "
       f"TransM_top_width={sorted(widths)}")
    if cex: pr("    EXCH CEX:", cex)
    pr(f"(B) CF_I: hosts_with_site={len(hosts)-none} none={none}  "
       f"scb_exists={scb_ok}  lhsCF_valid={lhs_ok}  BOTH={both}/{len(hosts)}")
    pr(f"total_s={round(time.time()-t0,1)}")

if __name__ == '__main__':
    main()

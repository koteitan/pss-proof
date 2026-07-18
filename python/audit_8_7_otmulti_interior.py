#!/usr/bin/env python3
"""Empirical audit for lean/8/8.7-otmulti-interior.lean (otMultiInterior field).

`otMultiInterior_holds` closes `OTmulti_interior_om2` (the mono last-component
interior residual of Isabelle `opx_OTmulti`) for ALL of condition (I):

  * C-false  (first P-block of oper L m is not [(0,0)]) -> operB exchange leg;
  * C-true & Lng L = 2 (the zero-leg oper L m = ((0,0))^m) -> numeral fold.

It EXPOSES one narrower Prop `OTmulti_interior_notCondI_om2` under the guard

      ¬ transCondI L  ∨  (C-true ∧ 1 < Lng L - 1).

This script checks, on the ST_PS orbit (diagSeq u v closed under oper), that the
two exposed disjuncts are EMPIRICALLY VACUOUS for the actual mono last-components
L = last (P N) (1 < Lng L) of multi standard hosts N:

  * every such L satisfies condition (I)      -> ¬ transCondI L never fires;
  * C-true happens exactly when Lng L = 2     -> the C-true & Lng>2 leg is empty
    (for Lng L > 2 the first P-block of oper L m has length >= 2, never [(0,0)]).

So the residual actually met by the termination proof lands entirely in the
closed condition-(I) region; the exposed leaf is a vacuous safety valve.

Usage:  python3 python/audit_8_7_otmulti_interior.py
"""
import collections
import sys

import trans_model as T
import red_model as rm


def diagSeq(u, v):
    return [(u, u)] if u == v else [(u, u), (v, v)]


def key(M):
    return tuple(map(tuple, M))


def build_orbit(umax=4, vmax=5, nmax=6, lenmax=9):
    seeds = [diagSeq(u, v) for u in range(umax) for v in range(u, vmax)]
    orbit = set()
    q = collections.deque(seeds)
    while q:
        M = q.popleft()
        k = key(M)
        if k in orbit or len(M) > lenmax:
            continue
        orbit.add(k)
        if T.Lng(M) > 1:
            for n in range(1, nmax):
                o = rm.oper(M, n)
                if T.Lng(o) <= lenmax and key(o) not in orbit:
                    q.append(o)
    return orbit


def main():
    orbit = build_orbit()
    not_condI = 0                       # mono last-comps that are NOT condition (I)
    ctrue_lng_gt2 = 0                   # C-true with Lng L > 2 (exposed but should be 0)
    seen_L = 0
    seen_pairs = 0
    for k in orbit:
        M = [tuple(c) for c in k]
        P = T.P(M)
        if len(P) <= 1:
            continue
        L = P[-1]
        if not (T.monoT(L) and T.Lng(L) > 1):
            continue
        seen_L += 1
        if not T.condI(L):
            not_condI += 1
        for m in range(2, 6):
            o = rm.oper(L, m)
            Po = T.P(o)
            ctrue = bool(Po) and Po[0] == [(0, 0)]
            seen_pairs += 1
            if ctrue and T.Lng(L) - 1 > 1:
                ctrue_lng_gt2 += 1

    print(f"orbit size                      : {len(orbit)}")
    print(f"mono last-components (Lng>1)    : {seen_L}")
    print(f"  ... NOT condition (I)         : {not_condI}   (exposed disjunct 1)")
    print(f"(L,m) pairs checked             : {seen_pairs}")
    print(f"  ... C-true with Lng L > 2     : {ctrue_lng_gt2}   (exposed disjunct 2)")
    ok = (not_condI == 0 and ctrue_lng_gt2 == 0)
    print("VACUITY OF EXPOSED Prop         :", "OK (both disjuncts empty)" if ok
          else "FAILED (exposed leg is non-empty!)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

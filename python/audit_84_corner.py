#!/usr/bin/env python3
"""Audit: is the condIV admeq CORNER (s84x_jm3 M = transJm1 M) inhabited among
STPS sequences meeting the NestScbCornerTriple_ns premises?

If a corner M exists, the target dP is analytically degenerate:
  Trans(Pred(s84x_N M)) = transC1 M  (both = Trans(seg M jm1 (Lng M-2))),
so dP = scb_decomp (transC1 M) (Dsym e3 :: u1) (flatBT transC1 M) v1 forces the
nonempty prefix to be empty -> UNSATISFIABLE.  So a nonempty corner set REFUTES
the residual; an empty corner set means it is vacuous.

Only cheap index conditions are computed (no Trans/Mark)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, monoT, zeroT, oper, parent, adm, Adm, reduced,
                       hasParent)

def hasParent1(M): return hasParent(M, 1, Lng(M) - 1)

def lastParent(M): return parent(M, 0, Lng(M) - 1)
def transJ0(M): return lastParent(M)
def transJm1(M):
    j0 = transJ0(M)
    return Adm(M, j0) if j0 is not None else None
def s84x_jm2(M): return parent(M, 1, Lng(M) - 1)
def s84x_jm3(M):
    j2 = s84x_jm2(M)
    return Adm(M, j2) if j2 is not None else None

def transCondIV(M):
    j1 = Lng(M) - 1; jp = lastParent(M)
    if jp is None: return False
    return (entry(M,1,j1) > 0 and entry(M,1,j1) <= entry(M,1,jp)
            and not adm(M, jp))
def transCondIII(M):
    j1 = Lng(M) - 1; jp = lastParent(M)
    if jp is None: return False
    return (entry(M,1,j1) > 0 and entry(M,1,j1) <= entry(M,1,jp)
            and adm(M, jp))

def build_orbit(umax=3, vmax=4, steps=40, nmax=4, cap=40000, lenmax=11):
    seen = set(); frontier = []
    for u in range(umax+1):
        for v in range(u, vmax+1):
            M = tuple((j,j) for j in range(u, v+1))
            seen.add(M); frontier.append(M)
    for _ in range(steps):
        newf = []
        for M in frontier:
            for n in range(1, nmax+1):
                try:
                    Mn = tuple(tuple(c) for c in oper([list(x) for x in M], n))
                except Exception:
                    continue
                if Mn not in seen and len(Mn) <= lenmax:
                    seen.add(Mn); newf.append(Mn)
                    if len(seen) >= cap: return seen
        frontier = newf
        if not frontier: break
    return seen

if __name__ == "__main__":
    orbit = build_orbit()
    print(f"orbit size = {len(orbit)}", flush=True)
    n_prem = 0; corners = []; corners_III = []
    for Mt in orbit:
        M = [list(x) for x in Mt]
        L = Lng(M)
        if L < 3 or zeroT(M) or not monoT(M): continue
        if not reduced(M): continue
        if not hasParent1(M): continue
        if not (1 < L - 1): continue
        cIV = transCondIV(M); cIII = transCondIII(M)
        if not (cIII or cIV): continue
        n_prem += 1
        j3 = s84x_jm3(M); jm1 = transJm1(M)
        if j3 is None or jm1 is None: continue
        if j3 == jm1:
            if cIV: corners.append((Mt, j3, jm1, s84x_jm2(M)))
            if cIII: corners_III.append((Mt, j3, jm1, s84x_jm2(M)))
    print(f"premise-satisfying (condIII or IV) = {n_prem}", flush=True)
    print(f"condIV admeq corners (jm3==jm1)    = {len(corners)}", flush=True)
    print(f"condIII admeq corners (should be 0)= {len(corners_III)}", flush=True)
    for (Mt,j3,jm1,j2) in corners[:25]:
        s = ''.join(f'({a},{b})' for a,b in Mt)
        print(f"  CORNER M={s}  jm3={j3} jm1={jm1} jm2={j2}")

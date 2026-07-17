#!/usr/bin/env python3
"""DEEP adversarial search for a counterexample to the RT_PS-stated tail value.

WHY THIS SCRIPT EXISTS
----------------------
The built «8».«8.3-TransCondII-engine» declares

    def CondII_masterCF : Prop :=
      forall M, RTPS M -> monoT M -> 1 < Lng M - 1 -> transCondII M -> <witnesses>

on RT_PS and with NO tail-value hypothesis.  Isabelle's original
`c2sx_condII_masterCF` (pss_wip.thy:87430) carries the extra hypothesis
`TV : c2sx_tailval M`, and TV's ONLY discharger `y3j_condII_tailval`
(pss_scratch.thy:17076) assumes `MST : M : ST_PS` -- NOT `M : RT_PS`.  The route
is `ljx_TVall_of_fin` (pss_wip.thy:115242) + `ot9_FINRC`, and BOTH are ST_PS-bound.
So the Lean Prop is NOT underwritten by the Isabelle corpus, and everything hinges
on whether `c2sx_tailval` happens to hold on ALL of RT_PS.

The predecessor audit (python/audit_83_condII_masterCF.py) answered "10/10 holds",
but it brute-forced components in range(0,6) with Lng <= 5.  lean/memo.md par.3:
  "数値検証で成分の上限を小さく取るな。反例は成分 6-9 に潜んでいる。
   「成分 < 3」「成分 < 4」の走査で 13 回の偽陽性を出した。"
i.e. cap=6 sits BELOW the band where counterexamples are known to hide, so that
"10/10" is exactly the shape of the project's 13 recorded false positives.  Its
PSS_AUDIT_FULL mode (cap 7, Lng 6) is 7**10 ~ 282M brute-force tuples = impractical.

METHOD (what makes the deeper scan affordable)
----------------------------------------------
`reduced` is PREFIX-CLOSED: trans_model.reduced is a conjunction of per-column
RedCondA/RedCondB conditions at column j that depend only on columns 0..j
(nextrel0(a,b) reads only columns a..b; nextrel1(j0,j1)'s trailing quantifier
ranges over j>j0 but is guarded by le0(M,j,j1), and nextrel0-edges go strictly
forward, so le0(M,j,j1) is False for j>j1 and vacuous at j=j1).  This is not a
guess: the Lean side PROVES closure under Pred=butlast (`RTPS_Pred`, used by
lean/8/8.3-condII-masterCF.lean), and by induction every prefix of a reduced
sequence is reduced.  Hence a DFS over columns may PRUNE the instant a prefix
stops being reduced -- which collapses cap**(2L) into a tractable tree and lets
us reach components 0..CAP-1 with CAP up to ~10 and Lng up to 7.

We also do NOT hardcode M[0] = (0,0): `reduced` at column 0 only forces
M[0] = (a,a), so a genuine RT_PS host could start at (a,a) with a>0.  The
predecessor pinned column 0 to (0,0); we enumerate all (a,a) to close that gap.

Exit code 0 = no counterexample found.
"""
import sys, os, itertools

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(100000)

from red_model import Lng, entry, parent, monoT, oper, seg
from trans_model import (Trans, Mark, Adm, adm, ZB, Dpt, PB, SigmaB,
                         bpHeadV, bpHeadT, reduced, Pred)

# ---------------------------------------------- Isabelle transJ/transC (1:1)
def transJ0(M):  return parent(M, 0, Lng(M) - 1)
def transJm1(M): return Adm(M, transJ0(M))
def transC1(M):  return Mark(Pred(M), transJm1(M))
def transT2(M):  return bpHeadT(transC1(M))

def condII(M):
    j1 = Lng(M) - 1
    jp = parent(M, 0, j1)
    if jp is None:
        return False
    return entry(M, 1, j1) == 0 and not adm(M, jp)

# ---------------------------------------------- the c2sx branch data (86431-)
def c2sx_pj(M):
    ps = PB(transT2(M))
    return ps[len(ps) - 1] if ps else ZB

def c2sx_ldj(M):
    return bpHeadV(c2sx_pj(M)) == entry(M, 1, transJ0(M))

def c2sx_t4(M):
    return bpHeadT(c2sx_pj(M)) if c2sx_ldj(M) else transT2(M)

def c2sx_W(M):
    return Trans(seg(M, transJ0(M), Lng(M) - 2))

def c2sx_tailval(M):
    return c2sx_W(M) == Dpt(entry(M, 1, transJ0(M)), c2sx_t4(M))

# ---------------------------------------------- pruned DFS over reduced seqs
def dfs_reduced(cap, lmax):
    """Yield every reduced M with components < cap and 3 <= Lng M <= lmax.

    Prunes on the prefix-closure of `reduced` (see the module docstring)."""
    stack = [[(a, a)] for a in range(cap)]
    stack = [M for M in stack if reduced(M)]
    while stack:
        M = stack.pop()
        if 3 <= Lng(M) <= lmax:
            yield M
        if Lng(M) >= lmax:
            continue
        for x in range(cap):
            for y in range(cap):
                N = M + [(x, y)]
                try:
                    if reduced(N):
                        stack.append(N)
                except Exception:
                    pass

def main():
    CAP  = int(os.environ.get("PSS_CAP", "10"))
    LMAX = int(os.environ.get("PSS_LMAX", "7"))
    print("=" * 78)
    print("DEEP RT_PS condition-(II) tail-value audit")
    print("  components < %d   (memo: counterexamples hide at 6..9)" % CAP)
    print("  Lng <= %d          (pruned DFS on prefix-closed `reduced`)" % LMAX)
    print("  column 0 NOT pinned to (0,0): all (a,a) enumerated")
    print("=" * 78)

    n_red = n_host = tv_ok = tv_bad = n_exc = 0
    cex = []
    ldj_seen = {True: 0, False: 0}
    maxcomp = 0

    for M in dfs_reduced(CAP, LMAX):
        n_red += 1
        try:
            if not (1 < Lng(M) - 1):
                continue
            if entry(M, 1, Lng(M) - 1) != 0:      # cheap condII prefilter
                continue
            if not monoT(M) or not condII(M):
                continue
        except Exception:
            n_exc += 1
            continue
        n_host += 1
        maxcomp = max(maxcomp, max(max(a, b) for (a, b) in M))
        try:
            ldj = c2sx_ldj(M)
            ldj_seen[ldj] = ldj_seen.get(ldj, 0) + 1
            ok = c2sx_tailval(M)
        except Exception as e:
            n_exc += 1
            print("   EXC", M, e)
            continue
        if ok:
            tv_ok += 1
        else:
            tv_bad += 1
            cex.append(M)
            if len(cex) <= 10:
                print("   *** CEX c2sx_tailval FAILS ***")
                print("       M   =", M)
                print("       j0  =", transJ0(M), " jm1 =", transJm1(M),
                      " ldj =", ldj)
                print("       W   =", c2sx_W(M))
                print("       D   =", Dpt(entry(M, 1, transJ0(M)), c2sx_t4(M)))

    print()
    print("   reduced sequences visited :", n_red)
    print("   RT_PS condition-(II) hosts:", n_host)
    print("   max component among hosts :", maxcomp)
    print("   ldj branch coverage       : True=%d  False=%d"
          % (ldj_seen.get(True, 0), ldj_seen.get(False, 0)))
    print("   tailval holds : %d   FAILS : %d   exceptions : %d"
          % (tv_ok, tv_bad, n_exc))
    print()
    print("=" * 78)
    if tv_bad:
        print("RESULT: %d COUNTEREXAMPLE(S) -- CondII_TailvalAll is FALSE on RT_PS"
              % tv_bad)
        print("        => the engine's CondII_masterCF is stated too strongly.")
    else:
        print("RESULT: NO COUNTEREXAMPLE (tailval holds on %d RT_PS hosts)" % tv_ok)
    print("=" * 78)
    return 1 if tv_bad else 0

if __name__ == "__main__":
    sys.exit(main())

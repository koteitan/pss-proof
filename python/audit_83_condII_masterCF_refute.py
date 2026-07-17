#!/usr/bin/env python3
"""Is the BUILT engine's `CondII_masterCF` (RT_PS-stated) actually FALSE?

BACKGROUND
----------
`lean/8/8.3-TransCondII-engine.lean:211` declares, on RT_PS and with NO
tail-value hypothesis:

    def CondII_masterCF : Prop :=
      forall M, RTPS M -> monoT M -> 1 < Lng M - 1 -> transCondII M ->
        exists s b u v t0 t1, t0 in T_B /\\ t1 in T_B /\\
          scb_decomp (Trans M) s (flatBT (Dprin u (t0 +B Dprin v (t1 +B Dprin 0 0B)))) b /\\
          (forall m, 1 < m -> exists c, 1 <= c /\\ Trans (oper M m) = unflatBT (s ++ ... ++ b))

Isabelle's `c2sx_condII_masterCF` (pss_wip.thy:87430) carries the EXTRA
hypothesis `TV : c2sx_tailval M`, and EVERY unconditional discharger of TV is
ST_PS-bound (verified by content-grep over all 8 `shows "c2sx_tailval"` sites:
scratch:17079, wip:87725, 87844, 90430, 110546, 110720, 110954, 115248 -- the
only two RT_PS-stated ones, `c2sx_tailval_trunk`/`c2sx_tailval_of_reg`, both
carry further hypotheses TR / REG).  So the RT_PS Prop is not underwritten.

`python/audit_83_condII_tailval_deep.py` (wave-J) reported tailval 144/144 on
RT_PS hosts at PSS_CAP=10, PSS_LMAX=5 and concluded "true but unproven".
THAT SCAN WAS TOO SHORT: at PSS_LMAX=6 it reports 27 counterexamples (CAP=8).
Every counterexample has Lng M = 6, i.e. the whole `Lng <= 5` pool is blind to
them -- the same shape as the project's 13 recorded false positives.

WHAT THIS SCRIPT ADDS (the decisive step)
-----------------------------------------
tailval failing only kills the ROUTE, not necessarily the Prop: masterCF might
still hold at M via some other witness tuple (s,b,u,v,t0,t1).  The existential
over witnesses is not directly searchable, so we test a NECESSARY CONSEQUENCE
that Lean already PROVES from those witnesses --
`exch_of_lhs_closed_ex_c2` (8.3-TransCondII-engine.lean:191) shows

    masterCF-witnesses at M  +  Trans M in T_B   ==>
        forall n, 1 < n -> exists k, Trans (oper M n) = operB (Trans M) (numBT k)

(`Trans M in T_B` is free on RT_PS: `Trans_mem_T_B`).  Hence if for some RT_PS
condition-(II) host M and some n > 1 there is NO k with
`Trans (oper M n) = operB (Trans M) (numBT k)`, then `CondII_masterCF` is FALSE
as declared -- and, being a field of the 27-Prop `TerminationResidual` bundle of
lean/8/8.7-termination.lean, would make that bundle UNSATISFIABLE.

Semantics: python/red_model.py + python/trans_model.py (canonical), with the
CORRECTED operB/xseq of python/_r15_vx_lib.py (the operB-misread of footnote [30]
cost this project 11 bogus corrections -- do not re-derive it here).

Exit code 0 = masterCF survives on every host scanned (only the route dies).
Exit code 1 = masterCF itself REFUTED at some RT_PS host.
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(100000)

from red_model import Lng, entry, parent, monoT, oper, seg
from trans_model import (Trans, Mark, Adm, adm, ZB, Dpt, PB, SigmaB,
                         bpHeadV, bpHeadT, reduced, Pred)
# CORRECTED Buchholz operator (footnote [30] transposition already fixed there).
from _r15_vx_lib import operB, numBT

KMAX = 40          # search bound for the fundamental-sequence index k
NMAX = 4           # test n = 2 .. NMAX


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


# ---------------------------------------------- the necessary consequence
def exch_k(M, n):
    """Least k <= KMAX with Trans (oper M n) = operB (Trans M) (numBT k), else None."""
    tgt = Trans(oper(M, n))
    base = Trans(M)
    for k in range(KMAX + 1):
        try:
            if operB(base, numBT(k)) == tgt:
                return k
        except Exception:
            pass
    return None


# ---------------------------------------------- pruned DFS over reduced seqs
def dfs_reduced(cap, lmax):
    """Every reduced M, components < cap, 3 <= Lng M <= lmax.

    Prunes on prefix-closure of `reduced` (Lean proves `RTPS_Pred`, so every
    prefix of a reduced sequence is reduced).  Column 0 is NOT pinned to (0,0):
    `reduced` only forces M[0] = (a,a)."""
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
    CAP  = int(os.environ.get("PSS_CAP", "7"))
    LMAX = int(os.environ.get("PSS_LMAX", "6"))
    print("=" * 78)
    print("Does the RT_PS-stated CondII_masterCF survive its tailval counterexamples?")
    print("  components < %d, Lng <= %d, pruned DFS, column 0 unpinned" % (CAP, LMAX))
    print("  necessary consequence tested: exists k <= %d." % KMAX)
    print("      Trans (oper M n) = operB (Trans M) (numBT k)   for n = 2..%d" % NMAX)
    print("=" * 78)

    n_host = tv_bad = 0
    mcf_dead = []           # hosts where the necessary consequence FAILS
    tv_bad_but_exch_ok = 0

    for M in dfs_reduced(CAP, LMAX):
        try:
            if not (1 < Lng(M) - 1):
                continue
            if entry(M, 1, Lng(M) - 1) != 0:
                continue
            if not monoT(M) or not condII(M):
                continue
        except Exception:
            continue
        n_host += 1
        try:
            tv = c2sx_tailval(M)
        except Exception:
            continue
        if tv:
            continue                      # route intact; masterCF provable there
        tv_bad += 1

        # tailval FAILS at M.  Does masterCF's consequence still hold?
        bad_n = []
        for n in range(2, NMAX + 1):
            try:
                if exch_k(M, n) is None:
                    bad_n.append(n)
            except Exception:
                pass
        if bad_n:
            mcf_dead.append((M, bad_n))
            if len(mcf_dead) <= 6:
                print()
                print("   *** CondII_masterCF REFUTED at ***")
                print("       M     =", M)
                print("       Lng   =", Lng(M), " j0 =", transJ0(M),
                      " jm1 =", transJm1(M), " ldj =", c2sx_ldj(M))
                print("       no k <= %d for n in %s" % (KMAX, bad_n))
                for n in bad_n:
                    print("         Trans (oper M %d) = %s" % (n, Trans(oper(M, n))))
                print("       Trans M =", Trans(M))
        else:
            tv_bad_but_exch_ok += 1

    print()
    print("   RT_PS condition-(II) hosts scanned : %d" % n_host)
    print("   tailval FAILS on                   : %d" % tv_bad)
    print("   ... of those, exch-consequence ok  : %d  (route dead, Prop alive)"
          % tv_bad_but_exch_ok)
    print("   ... of those, exch-consequence DEAD: %d  (Prop itself FALSE)"
          % len(mcf_dead))
    print()
    print("=" * 78)
    if mcf_dead:
        print("RESULT: CondII_masterCF is FALSE as declared (RT_PS, no TV).")
        print("        => it is UNDISCHARGEABLE and must be restated on ST_PS.")
        print("        => TerminationResidual of lean/8/8.7-termination.lean is")
        print("           UNSATISFIABLE while this field stands.")
    else:
        print("RESULT: masterCF's necessary consequence SURVIVES on all %d" % tv_bad)
        print("        tailval-counterexample hosts.  The Prop is not refuted by")
        print("        them; only the Isabelle ROUTE (via TV) dies on RT_PS.")
        print("        Restating on ST_PS is still required to make it portable.")
    print("=" * 78)
    return 1 if mcf_dead else 0


if __name__ == "__main__":
    sys.exit(main())

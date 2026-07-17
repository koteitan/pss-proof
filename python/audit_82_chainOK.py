#!/usr/bin/env python3
"""Adversarial numeric audit for lean/8/8.2-subexpr-chainOK.lean.

That file discharges the LAST TWO green-modulo bricks of the §8.2 keystone
campaign (`SXP_wid_cpU`, `SXP_wid_baseU` -- the two residuals Isabelle's
`m_8_2_wid`, layerB/pss_wip.thy:29605, also carries as `assumes`) and lands
`keystone` (Isabelle `m_8_2_keystone`, wip 32461) UNCONDITIONAL.

Claims re-stated 1:1 from the Lean sources and checked here:

  transJ0_eq_TrMax        <- m_8_2_transJ0_eq_TrMax        (wip 32316)
  joints_all_TrMax        <- m_8_2_joints_all_TrMax        (wip 32350)
  branchHigh              <- m_8_2_branchHigh              (wip 32391)
  branchPar               <- m_8_2_branchPar               (wip 32434)
  TrMax_ge_1              <- m_8_2_TrMax_ge_1              (wip 31683)
  descAdm_of_premises     <- m_8_2_descAdm_of_premises     (wip 31725)
  chainOK_of_descAdm      <- m_8_2_chainOK_of_descAdm      (wip 31113)
  chainOK_of_branchPar    <- m_8_2_chainOK_of_branchPar    (wip 31764)
  chainOK_imp_widTrM      <- m_8_2_chainOK_imp_widTrM      (wip 30747)
  cpU_rhs_eq              <- m_8_2_cpU_rhs_eq              (wip 29918)
  cpU_of_widTrMaxM        <- m_8_2_cpU_of_widTrMaxM        (wip 29946)
  cpU_of_chainOK          <- m_8_2_cpU_of_chainOK          (wip 30841)
  baseU_Br_empty_TrMax    <- baseU_Br_empty_TrMax          (wip 29985)
  baseU_alltrunk_diag_entry <- baseU_alltrunk_diag_entry   (wip 29996)
  baseU_alltrunk_Trans_RN1  <- baseU_alltrunk_Trans_RN1    (wip 30086)
  baseU_twoseg_monoT      <- baseU_twoseg_monoT            (wip 30140)
  baseU_caseI_geom        <- baseU_caseI_geom              (wip 30155)
  baseU  == SXP_wid_baseU <- m_8_2_baseU                   (wip 30183)
  sxp_wid_cpU_holds == SXP_wid_cpU (the discharged residual)

plus two NEGATIVE controls that must REPRODUCE known falsity, so we know the
pool is strong enough to see the failure mode the chainOK device exists for:

  (N1) the naive local condition `Admpos M & j1eq M ==> widTrM M` is FALSE
       (Isabelle wip 30713 cites the length-4 counterexample (0,0)(1,0)(1,1)(2,0));
  (N2) `chainOK M <-> Br M != [] & Lng M - 1 > 1 & TrMax M >= 1 & descAdm M`
       (Isabelle wip 31108 reports 0 mismatch) -- checked as an equivalence.

Semantics is python/red_model.py + python/trans_model.py (the canonical
models); Red returns a LIST OF TUPLES.  The pool is the established idiom
(diagSeq closed under `oper`, then row-0 ancestor slices Red(seg(M,j0,j1)),
then the Pred-closure) -- random pair sequences are almost never reduced.
The shared helper layer is imported from audit_82_subexpr so that the Lean
spellings of Joints/adm/Adm/transJ0/transJm1/RightNodes are literally the
ones that audit already cross-checked against red_model (14618/0).
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from audit_82_subexpr import (  # noqa: E402
    rm, tm, Lng, seg, Pred, Red, RTPS, monoT, TrMax, Br, FirstNodes,
    Joints, adm, Adm, transJ0, transJm1, getD, ent, RightNodes, Trans,
    fmt, standard_pool, rtps_mono_pool, Claim, parent_lean, ZB, Dpt,
)


# ------------------------------------------------------------ Lean spellings
def parent(M, j):
    """Lean `parent M 0 j`."""
    return parent_lean(M, 0, j)


def hasParent(M, j):
    return sum(1 for j0 in range(Lng(M)) if rm.nextR(M, 0, j0, j)) == 1


def J1(M):
    """Lean `(Br M).length - 1` in NAT arithmetic."""
    return len(Br(M)) - 1 if Br(M) else 0


def j1eq(M):
    """Lean `(FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1`."""
    return getD(FirstNodes(M), J1(M), 0) == Lng(M) - 1


def good(M):
    """Isabelle `good M == Br M != [] & Lng M - 1 > 1`."""
    return Br(M) != [] and Lng(M) - 1 > 1


def Admpos(M):
    return transJm1(M) > 0


def widTrM(M):
    """Lean `(RightNodes (Trans M)).getD 1 0 = entry M 1 (TrMax M)`."""
    return getD(RightNodes(Trans(M)), 1, 0) == ent(M, 1, TrMax(M))


def wid(M):
    """Lean `wid` (8.2-subexpr-wid.lean:60)."""
    rn = getD(RightNodes(Trans(M)), 1, 0)
    return (rn == ent(M, 1, getD(FirstNodes(M), J1(M), 0))
            or rn == ent(M, 1, getD(Joints(M), J1(M), 0)))


def descAdm(M):
    """Lean `∀ b, TrMax M < b → b ≤ Lng M - 1 → 0 < transJm1 (seg M 0 b)`."""
    return all(transJm1(seg(M, 0, b)) > 0
               for b in range(TrMax(M) + 1, Lng(M)))


def branchPar_prop(M):
    """Lean `∀ b, TrMax M < b → b ≤ Lng M - 1 → TrMax M ≤ parent M 0 b`."""
    return all(TrMax(M) <= parent(M, b) for b in range(TrMax(M) + 1, Lng(M)))


def chainOK(M, _depth=0):
    """Isabelle `chainOK` (wip 30726) / Lean `chainOK` (def, WF on Lng)."""
    if _depth > 64:
        raise RuntimeError("chainOK recursion runaway")
    if not (transJm1(M) > 0 and Br(M) != [] and Lng(M) - 1 > 1):
        return False
    P = Pred(M)
    return Br(P) == [] or chainOK(P, _depth + 1)


def scb_ok(M):
    """Guard: Trans is only meaningful on RT_PS & PT_PS here."""
    return RTPS(M) and monoT(M)


def main():
    base = standard_pool()
    print(f"standard pool (diagSeq closed under oper): {len(base)} forms, "
          f"maxlen {max(Lng(M) for M in base)}", flush=True)
    pool = rtps_mono_pool(base)
    print(f"RT_PS & PT_PS pool: {len(pool)} forms, maxlen "
          f"{max(Lng(M) for M in pool)}, max entry "
          f"{max(x for M in pool for p in M for x in p)}", flush=True)

    C = {}

    def mk(n, s):
        C[n] = Claim(n, s)
        return C[n]

    c_tj0 = mk("transJ0_eq_TrMax", "wip 32316")
    c_jall = mk("joints_all_TrMax", "wip 32350")
    c_bhi = mk("branchHigh", "wip 32391")
    c_bpar = mk("branchPar", "wip 32434")
    c_tr1 = mk("TrMax_ge_1", "wip 31683")
    c_desc = mk("descAdm_of_premises", "wip 31725")
    c_cod = mk("chainOK_of_descAdm", "wip 31113")
    c_cob = mk("chainOK_of_branchPar", "wip 31764")
    c_ciw = mk("chainOK_imp_widTrM", "wip 30747")
    c_crhs = mk("cpU_rhs_eq", "wip 29918")
    c_cwid = mk("cpU_of_widTrMaxM", "wip 29946")
    c_cok = mk("cpU_of_chainOK", "wip 30841")
    c_bemp = mk("baseU_Br_empty_TrMax", "wip 29985")
    c_bdiag = mk("baseU_alltrunk_diag_entry", "wip 29996")
    c_brn1 = mk("baseU_alltrunk_Trans_RN1", "wip 30086")
    c_b2seg = mk("baseU_twoseg_monoT", "wip 30140")
    c_bgeom = mk("baseU_caseI_geom", "wip 30155")
    c_baseU = mk("baseU  (== SXP_wid_baseU)", "wip 30183")
    c_cpU = mk("sxp_wid_cpU_holds (== SXP_wid_cpU)", "wip 30841+32434")
    c_key = mk("keystone: wid M (readback)", "wip 32461")

    for M in pool:
        if not scb_ok(M):
            continue
        L, tr, br = Lng(M), TrMax(M), Br(M)
        P = Pred(M) if L > 1 else None

        # --- baseU_Br_empty_TrMax : Br Q = [] -> TrMax Q = Lng Q - 1
        c_bemp.check(br == [], tr == L - 1, M)

        # --- baseU_alltrunk_diag_entry
        if tr == L - 1:
            ok = all(ent(M, 0, j) == ent(M, 1, 0) + j
                     and ent(M, 1, j) == ent(M, 1, 0) + j
                     for j in range(L))
            c_bdiag.check(True, ok, M)
            # --- baseU_alltrunk_Trans_RN1  (needs 1 < Lng Q)
            c_brn1.check(L > 1,
                         getD(RightNodes(Trans(M)), 1, 0) == ent(M, 1, L - 1), M)

        # --- baseU_twoseg_monoT
        c_b2seg.check(L == 2 and ent(M, 0, 0) < ent(M, 0, 1), monoT(M), M)

        if not (br != [] and L - 1 > 1):
            continue
        ap = Admpos(M)

        # --- TrMax_ge_1 / transJ0_eq_TrMax / branch* : hyps = Brne, Admpos, j1eq
        hyp = ap and j1eq(M)
        c_tr1.check(hyp, tr >= 1, M)
        c_tj0.check(hyp, transJ0(M) == tr, M)
        c_jall.check(hyp, all(getD(Joints(M), J, 0) == tr
                              for J in range(len(br))), M)
        c_bhi.check(hyp, all(ent(M, 0, tr) < ent(M, 0, b)
                             for b in range(tr + 1, L)), M)
        c_bpar.check(hyp, branchPar_prop(M), M)

        # --- baseU_caseI_geom : hyps + TrMax M = Lng M - 2
        c_bgeom.check(ap and tr == L - 2,
                      len(br) == 1 and getD(FirstNodes(M), 0, 0) == L - 1
                      and getD(Joints(M), 0, 0) == tr, M)

        # --- baseU (== SXP_wid_baseU)
        if P is not None:
            c_baseU.check(ap and (Br(P) == [] or not (Lng(P) - 1 > 1)),
                          wid(M), M)

        # --- chainOK_of_descAdm : hyps = Brne, j1gt, TrMax>=1, descAdm
        c_cod.check(tr >= 1 and descAdm(M), chainOK(M), M)

        if P is None or Br(P) == []:
            continue
        brP = True

        # --- descAdm_of_premises / chainOK_of_branchPar
        hyp2 = ap and brP and j1eq(M)
        c_desc.check(hyp2 and branchPar_prop(M), tr >= 1 and descAdm(M), M)
        c_cob.check(hyp2 and branchPar_prop(M), chainOK(M), M)

        # --- chainOK_imp_widTrM
        c_ciw.check(chainOK(M), widTrM(M), M)

        # --- cpU_rhs_eq
        rhs = ent(P, 1, getD(Joints(P), len(Br(P)) - 1, 0))
        c_crhs.check(hyp2, rhs == ent(M, 1, tr), M)

        # --- cpU_of_widTrMaxM / cpU_of_chainOK / SXP_wid_cpU (discharged)
        cpU_concl = getD(RightNodes(Trans(P)), 1, 0) == rhs
        c_cwid.check(hyp2 and widTrM(M), cpU_concl, M)
        c_cok.check(hyp2 and chainOK(M), cpU_concl, M)
        c_cpU.check(hyp2, cpU_concl, M)

    # --- keystone readback: the 4-clause disjunction pins RightNodes(Trans M)_1
    #     to a FirstNodes/Joints row-1 value, i.e. `wid M` (keystone_imp_wid).
    for M in pool:
        if scb_ok(M) and Br(M) != [] and Lng(M) - 1 > 1:
            c_key.check(True, wid(M), M)

    print("\nclaims (hypotheses satisfied = non-vacuously exercised):")
    bad = 0
    for c in C.values():
        print(c.line())
        bad += c.bad
        for f, e in c.cex:
            print(f"        CEX {f} {e}")

    # ---------------------------------------------------- negative controls
    print("\nnegative controls (these MUST reproduce the known failure modes):")

    # (N1) `widTrM` is NOT local: the naive `Admpos & good ==> widTrM` is FALSE.
    # NOTE (audit finding, 2026-07-17): Isabelle's comment at wip 30713 states
    # the refuted claim as `Admpos M & j1eq M ==> widTrM M` and cites
    # (0,0)(1,0)(1,1,)(2,0).  That witness has j1eq = FALSE (FirstNodes[J1] = 2,
    # Lng - 1 = 3), so it refutes the `Admpos & good` form, NOT the j1eq form.
    # The Isabelle docstring's PREMISE SET is imprecise; the mathematics is
    # unaffected (widTrM really is non-local, chainOK really is needed, and the
    # cited sequence really is a counterexample -- to the weaker statement).
    # Consistently, `Admpos & j1eq ==> widTrM` holds on 80/80 pool instances --
    # exactly as it must, since lean/8/8.2-subexpr-chainOK.lean PROVES
    # `j1eq & Admpos & good & Br (Pred M) != [] ==> chainOK M ==> widTrM M`.
    cex = [M for M in pool
           if scb_ok(M) and Admpos(M) and good(M) and not widTrM(M)]
    n1_hits = sum(1 for M in pool if scb_ok(M) and Admpos(M) and good(M))
    st = "OK  " if cex else "FAIL"
    print(f"  [{st}] (N1) naive `Admpos & good ==> widTrM` refuted: "
          f"{len(cex)} counterexample(s) of {n1_hits} instances "
          f"(must be > 0: widTrM is non-local, hence chainOK)")
    for M in cex[:3]:
        print(f"        refuting {fmt(M)}")
    if not cex:
        bad += 1
    # the Isabelle-cited witness, checked directly
    W = [(0, 0), (1, 0), (1, 1), (2, 0)]
    print(f"        Isabelle-cited witness {fmt(W)}: RTPS={RTPS(W)} "
          f"monoT={monoT(W)} Admpos={Admpos(W)} good={good(W)} "
          f"j1eq={j1eq(W)} widTrM={widTrM(W)} chainOK={chainOK(W)}")
    print(f"        -> refutes `Admpos & good ==> widTrM`; j1eq is FALSE on it, "
          f"so it does NOT bear on the j1eq form (Isabelle docstring imprecise)")
    n1b = sum(1 for M in pool if scb_ok(M) and Admpos(M) and j1eq(M))
    n1b_bad = sum(1 for M in pool
                  if scb_ok(M) and Admpos(M) and j1eq(M) and not widTrM(M))
    print(f"        for the record, `Admpos & j1eq ==> widTrM`: "
          f"{n1b} instances, {n1b_bad} counterexample(s) "
          f"(0 expected -- this file proves it)")

    # (N2) chainOK <-> good & TrMax>=1 & descAdm  (Isabelle wip 31108: 0 mismatch)
    mism = [M for M in pool
            if scb_ok(M) and chainOK(M) != (good(M) and TrMax(M) >= 1
                                            and descAdm(M))]
    st = "OK  " if not mism else "FAIL"
    print(f"  [{st}] (N2) chainOK <-> good & TrMax>=1 & descAdm: "
          f"{len(mism)} mismatch(es) of {sum(1 for M in pool if scb_ok(M))} "
          f"(Isabelle wip 31108 expects 0)")
    for M in mism[:3]:
        print(f"        mismatch {fmt(M)}")
    bad += len(mism)

    print("\nAUDIT " + ("OK — no counterexample" if bad == 0
                        else f"FAILED — {bad} counterexample(s)"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

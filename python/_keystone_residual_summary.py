"""§8.5 keystone -- residual state after the 2026-07-01 telescoping round.

WHAT THIS ROUND ADDED (layerC/pss_scratch.thy, m_8_5_keystone_telescope /
_recursion / _allq / _fold_C_commute, commit a360f86 on main):

  The keystone was previously a FLAT obligation: for every outer tower level q,
      bpHeadT (Trans (slice_q @ B)) = C (bpHeadT (Trans slice_q))        (*)
  "47/47 empirical, NOT mechanically reducible" (per the b3_markstep_skeleton
  text block), i.e. q-many independent instances of the same hard fact.

  This round formalizes (proves, green, unconditionally) a pure function-
  iteration lemma: writing z(n) for the value at tower level n and F for the
  period-fold,

      m_8_5_keystone_allq:
        zrec: z(Suc n) = F (z n)
        base: F (z 0) = C (z 0)                          -- ONE instance
        Cinv, commute: Inv (z0) closed under C, F(Cw)=C(Fw) on Inv  -- GENERIC
        ==> F (z n) = C (z n)                             -- ALL n

  So (*) for ALL q now reduces to TWO strictly smaller, independently-named
  residuals instead of one flat forall-q claim:

    R1 (BASE). The keystone at q=2 alone: F(z0)=C(z0), i.e. ONE concrete
       instance of (*) for the smallest valid q.  NOT yet attempted/closed
       this round -- likely the same composition-of-w-columns difficulty as
       the general case, just frozen at one instance.

    R2 (COMMUTE).  F(Cw) = C(Fw) for w on the C-orbit of z0.  Reduced FURTHER,
       concretely, by m_8_5_fold_C_commute, to:
         anchor: for every column m < w, scb_decomp (fold op [0..<m] acc0)
                  sx (flatBT (c1 m)) bx  -- i.e. the scb-context of column m's
                  substituted core c1(m) is found WITHIN the accumulated z-part
                  at every step of the period fold.
       This is the SAME kind of per-column anchoring data the EXISTING
       b3b_rnav_fold_drive / b3b_spineLeaf_fold_drive engines already require
       (there called `ladder` / depth ladder B3a) and which the file already
       flags as open ("otasm-confirmed empirically", not yet derived from the
       geometric gpar/cinv machinery).  m_8_5_fold_C_commute's `anchor` is
       actually WEAKER (plain scb_decomp existence, no explicit rspine_r depth
       count needed) -- so this is a slight strengthening of the existing
       engine, not a new open problem, but it is NOT closed either.

  NET: the keystone's open content is now PRECISELY "R1 + R2", both already-
  named residuals of the EXISTING development (R1 ~ one instance of the
  47/47 empirical fact; R2 ~ the existing B3a depth ladder), not a new
  unknown.  What's new is the MECHANICAL GLUE: R1+R2 ==> the keystone for
  EVERY q, proved once, unconditionally, instead of needed q times.

EMPIRICAL EVIDENCE for the telescoping premise itself (q-uniform C; see
_rnav_descend.py/_2/_3 in this directory): across 8 hand-built seeds, q=2..7,
  z(Suc q) = C(z q)   with C the SAME (W, vm1) pinned once at q=2->3
held in EVERY seed with condV(M) = True (the kernel's own scoping regime),
and FAILED in the one seed with condV(M) = False -- i.e. failure tracks
exactly the documented domain boundary, not a counterexample to the keystone.

WHAT WAS *NOT* ATTEMPTED THIS ROUND (real remaining work, for the next pass):
  - Closing R1 (the q=2 base instance) directly -- candidate routes: (a) try
    the SAME per-column composition machinery already in the file
    (m_8_5_Mark_bpHeadT_step_condV/condVI/tt2zero/else) composed w times for
    the SMALLEST concrete w, hoping smallness makes it tractable where the
    general case wasn't; (b) look for a structural reason q=2 is special
    (e.g. Pred(M[2]) = M, no prior "history" to track) that the existing
    m_8_3_kind1_base_basepoint / m_8_5_basepoint family may already supply.
  - Closing R2's `anchor` hypothesis for all m < w -- candidate routes: wire
    m_8_5_iterscb / m_8_5_brickB (already proven scb-context facts for ONE
    column, "ITERSCB") through an induction over m, paralleling how
    b3b_rnav_fold_drive itself is built; this needs the per-column scb_decomp
    EXISTENCE (not depth), so may be easier than the full rspine_r ladder --
    but still needs the per-MIDDLE-column (not just m=0) case, which is the
    part m_8_5_iterscb does not yet cover (it is keyed to the m=0 host
    Mq @ [col] specifically).

Re-run instructions: this file is documentation, not an executable check (the
empirical numbers above were produced by _rnav_descend3.py in this directory;
re-run that script to reproduce the 8-seed condV-scoped confirmation).
"""

#!/usr/bin/env python3
"""r14-S4p-C1 (front S4 prover, chain C1) — detailed notes.

TASK: prove, in order, m_8_4_oper_props_1..5 and m_8_4_slice_scb
(statements from stage-1 commit 96eefa1, python/_r14_s4_statements.py).

RESULT: 5/6 GREEN — m_8_4_oper_props_1, _2, _3, _4, _5 fully proven
(sorry 0, `Finished PSS_C`); m_8_4_slice_scb STOPPED on the anticipated
external blocker p_8_2_condV_terminal_slice_Trans (sorry, pss_paper 1604).

======================================================================
SESSION RECOVERY NOTE
======================================================================
A previous incarnation of this front left 736 UNCOMMITTED lines
(props_1..4 + congruence infra) whose last build (build5) had FAILED at
the two `_cong` lemmas.  Root cause: `thus P by (rule dir[OF L E0])` —
the chained-fact `rule` composition fails where the fully-explicit
`show P by (rule dir[OF L E0 A])` succeeds (same [OF L E0] works
un-chained elsewhere).  Lesson: with meta-quantified premises in the
rule, prefer explicit OF over chained `thus/rule`.

======================================================================
PROOF MECHANISMS (for reuse)
======================================================================
props_1: parent arithmetic.  (III/IV) => e1(j1) <= e1(j0) while
  e1(jm2) < e1(j1), so jm2 != j0; jm2 <= j0 by row-0 parent maximality
  (parent_max) since (1,jm2)<^Next(1,j1) contains le0 M jm2 j1.
  (V/VI) => e1(j0) < e1(j1) makes (1,j0)<^Next(1,j1) an edge
  (universality via parent_max detour) => uniqueness => jm2 = j0.

props_2: L_n = take (Lng M[n] + 1) M[n+1] (s84c1_L_take from
  m_8_4_oper_genform); RT via RT_PS_take (ST_PS take-closure +
  m_6_7_ST_PS_subseteq_RT_PS); mono via m_6_2_nonmulti_oper_2 (P
  singleton) + m_6_2_mono_prefix.

props_3/4: generic congruence lemmas s84c1_nextrel0/1_cong, s84c1_le0/
  le1_cong (equal Lng + row-0 entries equal everywhere + row-1 equal
  below a bound c covering the target).  L_1 = Pred M oplus (M0j1,
  M1jm2) differs from M only in the row-1 entry of the last column.
  props_4 splits on adm(L_1)(j0) with the entry-pattern step; the
  non-VI & nadm branch derives j0+1 < j1 from RedCondA (stdCA_ST_PS):
  j0+1=j1 & row-1 edge at j0 would force jm2=j0 and condVI.

props_5 (the main new brick this round):
  m* := jm2 + (n-1)w, w := j1 - jm2, kk := (n-1)*d0.
  List identities (block reading of m_8_4_oper_genform):
    s84c1_oper_lastblock: drop m* M[n] = block_{n-1}
    s84c1_L_tail:  drop m* L_n = (IncrFirst^^kk) L'
    s84c1_Mn_tail: drop m* M[n] = (IncrFirst^^kk) (Pred N')
    s84c1_L_prefix: seg (L_n|M[n]) 0 m* = L_{n-1}   (n>=2)
    s84c1_Pred_L: Pred L_n = M[n]
  Basepoint:
    s84c1_adm_L_mstar: adm L_n m* by contradiction — a left row-1 edge
      at m* reads off block entries (oper_d0pos_nth) as
      e1(j1-1) < e1(jm2) and e0(j1-1) < e0(j1), making (1,j1-1) an
      M-edge to j1, so jm2 = j1-1, contradicting e1(j1-1) < e1(jm2).
    s84c1_le0_L_mstar: le0 M jm2 j1 --(adm_le0_seg)--> le0 N' 0 w
      --(s84c1_le0_cong, row-0 of L' = row-0 of N')--> le0 L' 0 w
      --(le0_funpow_IncrFirst_eq)--> tail slice --(adm_le0_seg)-->
      le0 L_n m* (Lng L_n - 1).
    => (L_n, m*) in Marked; (M[n], m*) in Marked via Marked_Pred.
  Mark evaluation:
    Mark X m* = Trans (tail) by m_7_4_Mark_Trans_repr; tail =
    (IncrFirst^^kk) Y; Trans ignores the shift via
    Trans_funpow_IncrFirst whose Red-input comes from
    slice_Red_in_RT_PS (leR from Marked) + a1_Red_funpow_IncrFirst
    (Red Y = Red(tail) in RT_PS).  Gives Mark L_n m* = Trans L' and
    (interior case jm2+1 < j1) Mark M[n] m* = Trans (Pred N').
  Assembly: m_7_4_Trans_Mark_seg on (L_n, m*) gives the EXACT
    exists-unique pair (5-1)&(5-2) after rewriting seg/entry/Mark.
    (5-3) under the [C-2] guard ~zeroT(Pred N'):
    - interior (w >= 2): Trans_Mark_seg again on (M[n], m*); the two
      witnesses share conjunct (5-1) (same t = Trans L_{n-1} != 0_B by
      m_7_3_Trans_zeroT, same c), so m_7_2_scb_unique_sb pins them
      equal; (5-3) transfers.
    - boundary (jm2+1 = j1, w = 1): M[n] = L_{n-1} (the appended
      interior of s84c1_oper_Suc_eq_L_app is empty) and Pred N' =
      [(M0jm2, M1jm2)] with Red_singleton + m_7_3_Trans_Red +
      Trans_singleton giving Trans(Pred N') = D_{M1jm2} 0; (5-3)
      becomes (5-1) verbatim.  This is where the literal (5-3) FAILS
      when e1(jm2)=0 (zeroT): CEX (0,0)(1,1)(2,0)(3,1), n=2 [C-2].

======================================================================
m_8_4_slice_scb — STOPPED (external blocker), draft + route notes
======================================================================
Draft statement (typechecked in stage 1; NOT in pss_scratch now):

lemma m_8_4_slice_scb:
  assumes "M : ST_PS" "M : PT_PS"
    and "hasParent M 1 (Lng M - 1)"
    and "~ transCondVI M" "Adm M (s84x_jm2 M) = transJm1 M"
  shows "EX!sb. scb_decomp (transC2 M)
                 (Dsym (enat (entry M 1 (transJm1 M))) # fst sb)
                 (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0_B)) (snd sb)
             & scb_decomp (Trans (s84x_Np M))
                 (Dsym (enat (entry M 1 (s84x_jm2 M))) # fst sb)
                 (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0_B)) (snd sb)"
    and "Trans (Pred (s84x_Np M)) = Dpt (enat (entry M 1 (s84x_jm2 M))) (transT2 M)"

Article proof (content.md 4605-4699) needs, on top of the PROVEN
m_7_3_Mark_rightmost1/2, Mark_MarkedB_nest, Mark_leftend_form,
m_8_2_standard_slice_Red_strongmono, m_8_1_diagSeq family:

  * BLOCKER: 補題（条件(V)の下での終切片とTransの関係）
    = p_8_2_condV_terminal_slice_Trans (pss_paper 1604, SORRY).
    Both part (2) (transport of the c2-scb-decomposition from the
    admissible basepoint jm1 = Adm(jm2) to the non-admissible jm2:
    Trans N' = D_{M1,jm2} X with the SAME body X as c2 = D_{M1,jm1} X)
    and part (3) (Trans(Pred N') = D_{M1,jm2} t2) hinge on it (or on
    its sibling 公差(1,1) case at TrMax = j1-1-jm1).  No proven
    surrogate found (grepped: surg_*, bpHeadT-keystones of §8.5 are
    about append-tails, not head-rebasing at a deeper trunk index).

  * EASY SUBCASE (recorded for the future prover): if jm2 is
    M-admissible then Adm(jm2) = jm2 = jm1, N' = N, and:
    (2) collapses to (1) (Trans N' = Mark M jm1 = c2 via
        m_7_4_Mark_Trans_repr + m_7_3_Mark_rightmost2), and
    (3) is Mark (Pred M) jm1 = c1 = D_{M1,jm1} t2 via Mark_Trans_repr
        on Pred M + transC1/transT2 defs (c1 head form needs
        Mark_leftend_form or bpHead lemmas).
    The genuinely blocked regime is jm1 < jm2 (jm2 non-admissible).

  * Part (1) alone is likely provable now (rightmost1/2 +
    Mark_MarkedB_nest + triviality criterion + leftend form), but the
    EX! couples (1) with (2), so no self-contained partial lemma was
    committed.

Empirical status: L4 validated 85/85 (stage 1) + 14/14 (fresh seed 99,
this session) — the statement is TRUE on the genuine regime; only the
mechanized transport is missing.

======================================================================
BUILDS
======================================================================
build6  FAIL (inherited state: the two _cong chained-rule steps)
build7  GREEN (props_1..4)                  commit e824b52
build8  FAIL (nat-sub distribution x4)
build9  GREEN (block/tail identities)
build10 FAIL (mspos simp, le0_cong `of` positional mishit)
build11 FAIL (numeral 2 vs Suc(Suc 0))
build12 FAIL (elim conjE on premise-free conjunct goals)
build13 KILLED (blast divergence: hasParent_def+nextR_def unfold;
        fix = pre-simp nextR then blast on hasParent_def only)
build14 GREEN (adm/le0/Marked basepoint)    commit f5f3041
build15 GREEN (m_8_4_oper_props_5)          commit 238fc54
"""

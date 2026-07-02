#!/usr/bin/env python3
"""r15-S4d notes: the two remaining §8.4 various-scb lemmas L5/L6 + L4 part (1).

======================================================================
OUTCOME (all green, layerC/pss_scratch.thy, appended block "round 15
front S4d"; build: Finished PSS_C, 0 errors, sorry/oops 0)
======================================================================

PROVEN UNCONDITIONALLY (no p_* citation anywhere):
  s84d_c2hole (def) + s84d_c2hole_at_j1
      transC2 with the innermost right-end core D_{e1 j1} 0 replaced by a
      parameter D_a 0; transC2 M = c2hole M (M_{1,j1}) definitionally.
  s84d_corepair_shared / s84d_corepair_nested
      ONE (w,w') marks the trailing D_a 0 for EVERY a (m_7_2_add_scb
      conj1/conj2 at a=0 then transported).
  s84d_c2hole_scb
      the hole engine: a-uniform scb wrapper (Dsym v # w, D_a 0, w') of
      c2hole M a, all four branch shapes of the c2 let-chain.
  s84d_c2_rightmost_scb
      L4/L6 part "(s'_2, D_{M1,j1} 0, b'_2) of c2" as a UNIQUE
      decomposition with head Dsym e1(jm1), on the WIDE regime
      (RT&PT, j1>0, t1!=0 -- conditions I-VI all covered).
  s84d_L4_regime : L4 hypothesis set forces j1 > 1 and t1 != 0
      (Lng M = 2 would force condVI via row1_last_bound dichotomy).
  m_8_4_slice_scb_part1  == L4 part (1)  [STAGE-1 NAME + hypotheses]
  s84d_jm3_Marked / s84d_jm1_Marked : (M,jm3),(M,jm1) in Marked.
  s84d_dec1_Trans_N_scb  == L6 conjunct (1) (unique (s'_0,b'_0) around
      Trans N in Trans M; Mark-Trans repr at jm3).
  s84d_Mark_neq : marked m < m' < j1  ==>  Mark M m != Mark M m'
      (RightNodes length strictness; m=0 case via RightAnces chain of the
      prefix slice having >= 2 nodes).
  s84d_dec2_nest_scb  == L6 conjuncts (2)+(3) (unique (s'_1,b'_1), head
      Dsym e1(jm3), simultaneously around c2 in Trans N and c1 in
      Trans (Pred N); engine Mark_nest_common_marked at (jm3, jm1),
      nontriviality via s84d_Mark_neq + m_7_2_scb_triviality).
  s84d_rep_shift / s84d_concat_rep_snoc / s84d_set_concat_rep
      list algebra for the replicate (string-power) formulas.
  s84d_L5_branch : L5 hypothesis set ==> condIII|IV|V.
  s84d_L5_rng    : L5 hypothesis set ==> jm2 + 1 < j1 (interior regime).
  s84d_L1_data   : L_1 = M[1] (+) ((M0j1, M1jm2)) shares Pred, Lng, j0,
      jm1, c1, v, t2, t1 with M (the surgery recursion data), 11 parts.
      Key case: Adm agreement at j0 when j0+1 = j1 (both sides admissible
      by the row1_last_bound dichotomy resp. e1(jm2) <= e1(j0)).
  s84d_c2hole_L1 : transC2 L_1 = c2hole M (M_{1,jm2}) (branch alignment
      via m_8_4_oper_props_4; under (IV) both M and L_1 take the surgery
      branch with the SAME t3/t4 since t2, j0-entry agree).

PROVEN MODULO THE SINGLE §8.2 RESIDUAL (green-modulo reduction; the
blocked facts are HYPOTHESES, never cited as facts):
  m_8_4_various_scb_IIIV_from_slice   == FULL L5 (6 conjuncts, exists-1)
      from d1 (pin of (s1',b1') = the provable c2 wrapper) + d2/d3
      (the two transports of L4 parts (2)(3)).
  m_8_4_various_scb_IIIIV_from_slice  == FULL L6 (9 conjuncts, exists-1
      6-tuple) from d2 (pin of the provable nest wrapper (s1',b1')) +
      d4a/d4b (the two head-rebase transports jm3 -> jm2 of the article's
      conjunct (4)).  Conjunct (4)'s Trans L' part is DERIVED
      (m_7_2_scb_compose of d4b with the c2 wrapper, then
      m_8_4_rightend_Trans + uniqueness pinning); formulas (5)(6) by the
      same replicate induction as L5 gluing m_8_4_oper_props_5, base case
      L_1 via s84d_c2hole_L1 and the wrapper split
      s1 = s0 @ D_{jm3} # s1', b1 = b1' @ b0 (m_7_2_scb_compose +
      m_7_2_scb_unique_sb on Trans M).
  ==> The ENTIRE §8.4 various-scb cluster (L4 parts (2)(3), L5, L6) is
      now reduced to exactly ONE unproven fact:
      p_8_2_condV_terminal_slice_Trans (pss_paper 1604).

======================================================================
KEY NEGATIVE RESULT: round-14 condIV-vacuity hypothesis REFUTED
======================================================================
Round-14 run E: "condIV & jm3<jm1 NOT FOUND in ~89k genuine standard
sequences (possibly vacuous on ST_PS)".  REFUTED by deeper mining
(strategy that worked: ns=(1,2) only + deeper maxLng + wider diagSeq
seeds; see _r15_s4d_validate.py gen_pool params seeds 202/303/404):
  393 condIV instances mined; 387 have jm3 = jm1; SIX have jm3 < jm1:
    (0,0)(1,1)(2,2)(3,3)(3,2)(4,1)(5,2)(6,3)(6,1)     [jm2=0 j0=6 jm1=5 jm3=0]
    ... (5 more, see _r15_s4d_condIV_L6.py output; gap widths j0-jm2 up
    to 8, admissible nodes inside the gap in all 6).
  Mechanism: condIV needs ~adm(j0); jm3<jm1 needs an admissible j' with
  jm2 < j' <= jm1 strictly above Adm(jm2) -- requires a long row-0
  parent gap (j0 - jm2 >= 2) with an interior admissible column, which
  needs 3-row-deep braiding; the standard M[n] closure reaches it only
  at Lng >= 9, beyond the round-14 pool's effective depth.
LESSON (verify-rank-depth again): absence in 89k shallow instances is
NOT vacuity evidence; the refuting instances all have Lng >= 9 and
n-values in {1,2} only.

======================================================================
EMPIRICAL VALIDATION (fresh runs, this round)
======================================================================
_r15_s4d_condIV_L6.py (486s, seeds 202/303/404, GENUINE = diagSeq
closure under M[n], per-instance SIGALRM 15s, 0 timeouts):
  P1 engine (condIV)          393/393 (P1u/P1h/P1b_IV1)
  L5 conjuncts on cond IV     387/387 (L5u/L5s1u/L5_1h/L5_2/L5_2b/L5_3)
  L5 formulas (4)(5)          1096/1096 (instance x n, n=1..3)
  L6 conjuncts (IV & jm3<jm1) 6/6 (L6_1/L6u1/L6_2h/L6_2/L6u2/L6_4a/4b/4c)
  L6 formulas (5)(6)          11/11
  L_1 base-case invariants    387/387 (B_jm1/B_c1/B_hole/B_s1b1/B_cls)
_r15_s4d_validate.py (seeds 5/11 + miners 77/101/202): L5 496/496,
  L5 formulas 1341/1341, L6 (condIII) 1053/1053, P1 2617/2617 across
  III/IV/V/VI, BASE 496/496, DEC2 1053/1053.  (Numbers quoted in the
  .thy header; re-run this round -- see scratchpad r15_s4d_validate.out.)

======================================================================
ISABELLE PITFALLS HIT (fix patterns for future agents)
======================================================================
1. adm/nadm unfolding: nadm has a "j > Lng M" disjunct; from ~adm you
   CANNOT get the nextR edge by (auto simp: adm_def nadm_def) alone --
   supply the range fact (j0lt) or auto leaves the phantom
   "Lng M < j" subgoal.  (build4 failure at 17168.)
2. 1 -> Suc 0 normalization strikes again: transports like
   "transC1 (s84x_L M 1) = transC1 M by (simp add: transC1_def PredL1
   tJm1)" fail because simp normalizes the goal's 1 to Suc 0 while the
   rule LHSs keep literal 1.  Fix: unfolding transC1_def PredL1 tJm1
   by (rule refl).  (build5 failure at 17197.)
3. The ex1I-over-6-tuple pattern: state the case-form, prove a flat
   "big" conjunction first, close the case goal with "using big by
   simp"; uniqueness via prod_cases6 + component-wise
   m_7_2_scb_unique_sb pins.  Works first try.

======================================================================
RESIDUAL (for the round-16 planner)
======================================================================
- SINGLE blocker for the whole §8.4 various-scb cluster:
  p_8_2_condV_terminal_slice_Trans (pss_paper 1604).  Once proven, the
  parent instantiates d2/d3 of m_8_4_various_scb_IIIV_from_slice and
  d4a/d4b of m_8_4_various_scb_IIIIV_from_slice to discharge the
  stage-1 statements m_8_4_various_scb_IIIV / m_8_4_various_scb_IIIIV
  verbatim (and L4 = m_8_4_slice_scb parts (2)(3)).
- Note the transports needed are exactly:
    L5: d2 = (D_{jm2} s1', D_{j1} 0, b1') of Trans N'
        d3 = Trans (Pred N') = D_{jm2} t2
    L6: d4a = (D_{jm2} s1', c1, b1') of Trans (Pred N')
        d4b = (D_{jm2} s1', c2, b1') of Trans N'
  (L6's needs are the c1/c2-level transports, L5's the D_{j1}0-level;
  both follow from the terminal-slice lemma's head-rebase mechanism.)
"""
if __name__ == '__main__':
    print(__doc__)

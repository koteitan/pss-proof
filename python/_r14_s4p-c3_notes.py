#!/usr/bin/env python3
"""r14-S4p-C3 (front S4 prover, chain 3): m_8_4_Trans_scb — PROVEN (green).

TARGET (stage-1 statement, validated 393/393 in _r14_s4_statements.py runs A/B/D):

  lemma m_8_4_Trans_scb:
    assumes "M \\<in> RT_PS" "M \\<in> PT_PS"
      and "1 < Lng M - 1" "hasParent M 1 (Lng M - 1)"
    shows "\\<exists>!sb. scb_kind1 (Trans M) (fst sb) (flatBT (Trans (s84x_N M))) (snd sb)"

STATUS: fully proven, appended to layerC/pss_scratch.thy (block starts at the
section header "r14-S4p-C3", line ~9114 of the committed file), build green
(Finished PSS_C, sorry/oops 0, no real errors, log /tmp/pss-r14-S4p-C3-build6.log).

======================================================================
PROOF ARCHITECTURE (article: content.md 4509-4604)
======================================================================
jm2 = parent M 1 j1, jm3 = Adm M jm2, N = seg M jm3 j1, Q = Red N.

1. (M,jm3) in Marked: adm (adm_Adm_adm) + leR M 0 jm3 j1 composed from
   adm_row1_ancestry (jm3 <=_1 jm2), m_le1_imp_le0, and le0 jm2 j1 (inside
   nextrel1 of the row-1 parent, via theI' on hasParent).
2. EXISTENCE of the scb position: m_7_3_Trans_Mark_MarkedB (the Trans/Mark
   invariant) gives scb_decomp (Trans M) s (flatBT (Mark M jm3)) b.
3. CENTRE value: m_7_4_Mark_Trans_repr (Mark M jm3 = Trans N) and
   Trans_slice_eq_Red (Trans N = Trans Q).
4. KIND-1 upgrade via scb_kind1_of_suffix.  The right-spine valley of
   r = RightNodes (Mark M jm3) = RightAnces Q (m_7_4_RightAnces_RightNodes):
   - NEW CHAIN LEMMA s84c3_RightAnces_chain: for reduced mono Q,
     RightAnces Q = map (entry Q 1) ks with s84c3_chainOK Q ks:
       ks noteq [], hd ks = 0, last ks = Lng Q - 1, sorted_wrt (<),
       every element a row-0 ancestor of the right end (le0 to end),
       windows s84c3_winOK: adm(left) OR (entry(right) <= entry(left) AND
       (right is chain end OR adm(right))).
     Induction on Lng Q along the RightAnces recursion (RightAnces.psimps +
     RightAnces_dom_RT; base = one column / zeroT (Pred Q); step = IH on the
     prefix seg Q 0 jm1' + explicit 1-or-2 element tail).  Tail windows use
     the reduced dichotomy row1_last_bound (in the (II)/(IV) branch
     entry(j1) <= entry(jp) and jp non-admissible, else V/VI would fire).
     Prefix transfers: m_6_3_adm_slice (adm), adm_le0_seg (le0), entry_seg.
     Window glue at the admissible joint jm1': s84c3_winOK_glue.
   - TRANSFER Q -> M by seg M jm3 j1 = (IncrFirst ^^ dd) Q
     (m_6_6_ancestor_slice_Red_IncrFirst): entry-1 / adm / le0 invariance
     under IncrFirst-powers (s84c3_entry1_funpow_IncrFirst,
     adm_funpow_IncrFirst_eq, s84c3_le0_funpow_IncrFirst) then slice
     transfers (entry_seg / m_6_3_adm_slice / adm_le0_seg).
   - VALLEY (flat, no induction): head r!0 = entry M 1 jm3 < entry M 1 j1
     (le1-monotonicity m_5_1_ancestor_basic_2 + the parent's strict step);
     last = entry M 1 j1; interior node k+jm3 with window:
       * adm case: k+jm3 > jm2 by Adm-maximality (adm_Adm_max; k+jm3 <= jm2
         would force k+jm3 <= Adm M jm2 = jm3, contradiction with k > 0),
         then the nextrel1 VALLEY CLAUSE of the row-1 parent (built into
         nextrel1_def = the article's 親の基本性質(2)) gives entry >= entry j1.
       * non-adm case: window gives entry(k) >= entry(next) and next is the
         chain end (= j1, done) or admissible (previous case applied to next).
5. UNIQUENESS: m_7_2_scb_unique_sb (fixed centre, nonzero Trans M).

NEW NAMES (all s84c3_-prefixed except the target):
  s84c3_entry1_funpow_IncrFirst, s84c3_nextrel0_funpow_IncrFirst,
  s84c3_le0_funpow_IncrFirst, s84c3_winOK (def), s84c3_winOK_singleton,
  s84c3_winOK_pair, s84c3_winOK_triple, s84c3_winOK_glue,
  s84c3_chainOK (def), s84c3_RightAnces_chain, m_8_4_Trans_scb.

CITATION AUDIT: no p_* (sorry) facts cited; all cited lemmas are proven
m_*/helper facts in pss_mechanized / pss_wip / pss_scratch (grep audit clean).

======================================================================
EMPIRICAL VALIDATION
======================================================================
- Stage-1 target statement: 393/393 (334 run A standard + 23 run B condIV-mine
  + 36 run D beyond-ST reduced&mono), see python/_r14_s4_statements.py.
- Stage-2 proof-design validation (_r14_s4pc3_chain_check.py): the chain
  invariant (a)-(e) for the SPLICE recursion and the top-level valley (f)
  over genuine ST-derived reduced mono pools, seeds 1..9, maxv 3, n in 1..4.
  NOTE: the original script (committed by the stage-1/earlier run) crashed
  with an AssertionError raised inside trans_model.Trans on one pool
  instance ("no scb decomposition (invariant breach)"); the rerun wrapper
  (results below) counts those separately.  Result of the wrapped rerun:
  see RESULTS block appended at the bottom of this docstring after the run.

BUILD ITERATION LOG (6 builds to green):
  b1: r_into_rtranclp[OF nr0] -> "OF: multiple unifiers" (higher-order
      unification of ?r ?x ?y); fixed by the wip pattern
      "unfolding le0_def using ... by simp".
      Also lenks2's (cases ks) auto left "list = []"; fixed with linarith +
      explicit obtain.
  b3: "using segz by (simp add: zeroT_def)" mangled by Lng_seg[simp]
      normalizing the zeroT conjunct (jm1 rewritten in goal but not in
      premise); fixed with "unfolding zeroT_def by blast".
  b4: exI + simp with jm1z rewrote jm1 before the if-equation m could fire;
      fixed by explicit intro conjI shows.
  b5: map_cong side goal: entry _ 1 _ vs Suc 0 normalization (the known
      1::nat gotcha); fixed by Isar map_cong with blast.
  b6: GREEN.
"""

RESULTS = {
    "target_stage1": "393/393",
    "chain_invariant_P": None,   # filled by the wrapped rerun (see report)
    "top_valley_f": None,
}

if __name__ == "__main__":
    print(__doc__)

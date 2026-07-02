#!/usr/bin/env python3
"""r14-S4p-C2 (front S4 prover, chain C2): m_8_4_rightend_Trans — PROVEN GREEN.

TARGET (stage-1 statement 96eefa1, merged/corrected form [C-1]):
  lemma m_8_4_rightend_Trans:
    assumes "M : ST_PS" "M : PT_PS"
      and "hasParent M 1 (Lng M - 1)"
      and "s84x_jm2 M + 1 < Lng M - 1"
    shows "EX! sb. scb_decomp (Trans (s84x_Np M)) (fst sb)
                     (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0_B)) (snd sb)
                 & scb_decomp (Trans (s84x_Lp M)) (fst sb)
                     (flatBT (Dpt (enat (entry M 1 (s84x_jm2 M))) 0_B)) (snd sb)"
  = article Section 8.4 L1 (content.md 4265, proof 4275-4390) with parts (2)/(3)
  merged per correction [C-1] (literal (3) refuted 0/40; see _r14_s4_statements.py).

STATUS: GREEN (build6: Finished PSS_C == 1, zero real errors, sorry/oops == 0).
Block: layerC/pss_scratch.thy, appended after the s84x_ definitions
(marker "r14-S4p-C2: §8.4 L1", ~970 lines).  New names (all s84c2_-prefixed
except the target):
  s84c2_funpow_IncrFirst_append   (IF^k distributes over @)
  s84c2_funpow_IncrFirst_single   (IF^k [(x,y)] = [(x+k,y)])
  s84c2_seg_butlast               (butlast (seg M a b) = seg M a (b-1), a<b)
  s84c2_scb_self                  (trivial scb self-decomposition of Dpt v t)
  s84c2_R_base                    (rightend replacement R: Lng/nth/entry/Pred)
  s84c2_R_facts                   (R : RT_PS, monoT R, parent/adm/Adm agreement,
                                   Q_{1,0}+1 = Q_{1,j1} (RedCondA at row-1 parent 0),
                                   dichotomy e1(j0') >= e1(j1Q) | j0' = 0,
                                   j0' < j1Q)
  s84c2_concat_map_single
  s84c2_Trans_c2_decomp           (surgery packaging: scb_decomp (Trans M) s1
                                   (flat (transC2 M)) b1 sharing the c1-wrappers
                                   of Trans (Pred M); trans_surgery_localized +
                                   scb_replace_principal + unflatBT_flat)
  m_8_4_rightend_Trans            (the target)

PROOF ARCHITECTURE (follows the article, content.md 4275-4390):
  1. Q := Red N' reduced+mono via m_6_6_ancestor_slice_Red_IncrFirst
     (leR M 0 jm2 j1 from the nextrel1 hypothesis); N' = IF^k Q readback.
  2. Slice heredity: nextR Q 1 0 j1Q via adm_nextR1_seg + nextR_funpow_IncrFirst_eq.
  3. R := butlast Q @ [(Q_{0,j1Q}, Q_{1,0})] (the article's rightend replacement).
     s84c2_R_facts: row-0 relations of R = those of Q (nextrel0_prefix_row0 with
     c = Lng Q - 1: row 0 agrees EVERYWHERE incl. the last column); row-1
     relations agree strictly below j1Q (nextrel1_prefix_imp, c = j1Q - 1);
     the last column has NO row-1 parent in R (uniqueness of the row-1 parent
     nextR1_unique + the nextrel1 forall-clause of par1); RedCondA/RedCondB
     transfer => R : RT_PS by the section 6.6 keystone m_6_6_reduced_iff_cond;
     adm/Adm agreement at j0' (adm_prefix_agree_eq for the interior, the dead
     (j0', j1Q) edge argument for the boundary j0'+1 = j1Q).
  4. L' = IF^k R (butlast/single funpow computation + entry_funpow bridges),
     Red L' = R (a1_Red_funpow_IncrFirst + R reduced), so
     Trans N' = Trans Q, Trans L' = Trans R (m_7_3_Trans_Red).
  5. Shared recursion data: Pred R = Pred Q => transC1/transV/transT2/transT1
     equal (transJm1 via the Adm agreement); the surgery wrappers (s1,b1)
     coincide by m_7_2_scb_unique_sb on Trans (Pred Q) with core flat(transC1).
  6. Branch classification: e1(Q,0)+1 = e1(Q,j1Q) (RedCondA at the row-1 parent
     0); dichotomy e1(Q,j0') >= e1(Q,j1Q) or j0' = 0 (else nextrel1 Q j0' j1Q
     would be a second row-1 parent); hence
       ~transCondVI Q, ~transCondVI R, ~transCondV R,
       condA(Q) <-> adm Q j0' <-> condA(R)   (condA = I|III|V).
  7. Core swap at the transC2 level (3 cases: condA / ~condA & t2=0 /
     ~condA & t2!=0): m_7_2_add_scb_conj1 gives the (pre,post) mark of the
     innermost D_{aQ} 0; m_7_2_add_scb_conj2 transports it to D_{aR} 0 with the
     SAME (pre,post); scb_Dpt_lift through the D_v / D_{u'} heads;
     m_7_2_scb_compose glues nested additions (t2!=0 case: t3/t4 dfree via
     PB/SigmaB computation).  transC2 values from transC2_def+Let_def with the
     entry-value equalities passed as PREMISES (the 1/Suc 0 normalization
     gotcha: simp-rules with numeral 1 do not fire on Suc 0 goals).
  8. Compose with the outer surgery decomposition (s84c2_Trans_c2_decomp);
     witness (s1 @ w, w' @ b1); uniqueness from conjunct 1 alone via
     m_7_2_scb_unique_sb (Trans Q != Trm [] from monoT + m_7_3_Trans_zeroT).

EMPIRICAL (genuine ST_PS regime = the lemma's own hypotheses over the
diagSeq-closure pool, SIGALRM-guarded):
  _r14_s4p-c2_recheck.py (seed 42, pool 1500, maxLng 12): domain 586,
    (a) lemma shape unique-both 586/586 (6 later-phase timeouts),
    (b) R reduced&mono & L'=IF^k R & Red L' = R: 580/580,
    (c) parent/adm/Adm/c1 agreement + branch match + no condVI: 580/580.
  _r14_s4p-c2_micro.py (seed 1234, pool 1500): 427 domain instances, 0 timeouts,
    m1 row-1-parent-of-j1Q = {0} + e1(0)+1=e1(j1Q): 427/427
    m2 dichotomy (incl. weak form):                 427/427
    m3 ~VI(Q), ~VI(R), ~V(R):                       427/427
    m4 condA(Q)<->adm(Q,j0') = condA(R)<->adm(R,j0'): 427/427
    m5 c1 shared (Mark (Pred .) (Adm . j0')):       427/427
    m6 lemma shape unique-both:                     427/427
  Stage-1 (96eefa1, seeds 1 & 7): 204/204 + 40/40 = 244/244.

CITATION AUDIT: zero p_* citations in the block (grep-verified); all external
facts are proven m_*/helper lemmas from the frozen layers or in-block s84c2_*.

BUILD ISSUES HIT (for future agents):
  - the_equality via OF needs [where P=...] (multiple HO unifiers on THE).
  - chained-fact + rule adm_prefix_agree_eq failed; explicit OF works.
  - 1 vs Suc 0: entry-value equations must be premises (using), not simp adds,
    when the goal is produced by unfolding transC2_def Let_def.
  - Lng M - 2 vs Lng M - Suc (Suc 0): add numeral_2_eq_2.
"""
STATUS = {"m_8_4_rightend_Trans": "proven",
          "helpers": ["s84c2_funpow_IncrFirst_append", "s84c2_funpow_IncrFirst_single",
                      "s84c2_seg_butlast", "s84c2_scb_self", "s84c2_R_base",
                      "s84c2_R_facts", "s84c2_concat_map_single",
                      "s84c2_Trans_c2_decomp"]}
if __name__ == '__main__':
    print(STATUS)

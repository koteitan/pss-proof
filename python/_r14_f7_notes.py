#!/usr/bin/env python3
"""r14-F7 notes: the SS 8.7 fseq_descend DISPATCHER — status, wiring, and the
hypothesis-discharge CHECKLIST ("keystone falls => termination descent assembles").

DELIVERED (green, layerC/pss_scratch.thy, block "r14-F7"):

  m_8_7_fseq_descend_dispatcher
      M : ST_PS ==> n >= 1 ==> Lng M > 1 ==> lessBT (Trans (M[n])) (Trans M)
    GREEN modulo exactly SEVEN named meta-hypotheses (TOT, exchI..exchVI).
    m_8_7_fseq_descend_of_exchange re-states it with anonymous assumptions so a
    future discharge is a single OF-application producing p_8_7_fseq_descend's
    statement verbatim.

  f7x_fseq_descend_mono          -- the mono-host dispatcher (same 7 hypotheses)
  f7x_Trans_append_Pblocks       -- Trans additivity across an aligned P-boundary
                                    (with the D_0 0 correction for a leading
                                    [(0,0)] component); NEW, unconditional, green
  f7x_multBT_lessBT_principal / f7x_Dpow_lessBT_Dpt / f7x_lessBT_D00_imp_zero
  f7x_multBT_single / f7x_addBT_assoc / f7x_addBT_zero_right
  f7x_parent_one_zero / f7x_adm_zero
  f7x_concat_replicate_single / f7x_concat_map_singleton

CASE TREE PROVEN OUTRIGHT (no hypothesis consumed):
  [A]   M[n] = Pred M                    -> m_7_3_Pred_Trans_descend
  [I,j1=1]  M in {((u,u),(u+1,0))}      -> M[n] = ((u,u))^n; const00 closed form
            (covers the article's t1=0 case ((0,0),(1,0)) uniformly, u >= 0)
  [I,j1>1,j0=0]  copy-additivity        -> operI_j0zero_trans_mult +
            m_8_2_subexpr_component_Pred_Adm0_clause1 + head comparison; NO TOT!
  [VI,j1=1] M in {((u,u),(u+1,u+1))}    -> M[n] = rcseq u (n-1) (proved from
            poper_oper_expand: i1=1, parent=0, d0=1); m_8_6_rcseq_Trans tower;
            (covers the article's t1=0 case ((0,0),(1,1)) uniformly)
  [II/III/IV j1=1], [V j1=1]            -> IMPOSSIBLE in case B (proved):
            II: adm M 0 always; III/IV: the row-1 parent of column 1 forces
            entry M 1 0 < entry M 1 1, contradicting M_{1,j0} >= M_{1,j1};
            V: j0+1 < j1 forces j1 >= 2 by definition.
  [multi]  Pcut M <= j0 < j1 (a j0 = 0 parent would make M mono; Pcut = LEAST),
            M[n] = A @ PJ[n] and P(M[n]) = P A @ P (PJ[n]) (m_6_2_P_oper_2),
            PJ standard (m_6_7_standard_P_components) mono with Lng > 1,
            f7x_Trans_append_Pblocks + lessBT_addBT_mono_right lift the mono
            dispatcher on PJ.  The D_0 0-correction case (leading [(0,0)]
            component of PJ[n], e.g. PJ = ((0,0),(1,0)) -> PJ[n] = ((0,0))^n)
            closes by a HEAD comparison against the single-principal
            Trans PJ = Trm [DB w body] (m_7_3_Trans_monoT + m_7_3_Trans_leftmost),
            with body != 0 at w = 0 via the Pred-descent readback
            (f7x_lessBT_D00_imp_zero + m_7_3_twoColumn_Trans) -- the component
            descent is NOT needed there.

EMPIRICAL COVERAGE (python/_r14_f7_dispatcher_check.py; genuine regime =
  diagSeq seeds closed under oper = literal ST_PS members; every case-tree
  assertion checked per (M,n) pair, plus the final descent itself):
  run 1 (maxlen 8, cap 900, n in 1..3, seeds u<3,v<=u+4):
      pool=897  pairs=2691  FAILS=0  skipped=0
      A=1115 B=1576 (mono=1394 multi=182)
      condI=740 condII=0 condIII=252 condIV=6 condV=154 condVI=242
      condI-j1=1: 2   condVI-j1=1: 6   multi D_0 0-correction: 44
      final descent 2691/2691
  run 2 (re-seeded: maxlen 7, cap 1200, n in 1..4, seeds u<5,v<=u+6):
      pool=937  pairs=3748  FAILS=0  skipped=0
      A=1417 B=2331 (mono=1989 multi=342)
      condI=807 condII=24 condIII=585 condIV=9 condV=156 condVI=408
      condI-j1=1: 3   condVI-j1=1: 15   multi D_0 0-correction: 72
      final descent 3748/3748
  NOTE condII fired 0 times on run 1's narrow seeds but 24 times on run 2's
  wider seeds (u < 5) -- exchII is NOT vacuous in the genuine regime; all six
  exchange hypotheses are live.

HYPOTHESIS-DISCHARGE CHECKLIST (one line per named hypothesis of
m_8_7_fseq_descend_dispatcher; "owner" = the task.md / roadmap item whose
closure discharges it by one OF-application):

  TOT   : Trans N : OT_B  (N : ST_PS, mono, Lng N - 1 > 1)
          owner: SS 8.7 p_8_7_Trans_preserves_OT.  Already reduced to the
          keystone branch: m_8_7_Trans_OT_nonkey (scratch) closes every
          non-keystone host; m_8_7_OT_keystone_step / m_8_7_Trans_preserves_OT_step
          carry the keystone recursion.  When m_8_7_Trans_preserves_OT lands,
          TOT := m_8_7_Trans_preserves_OT[OF ST-membership].

  exchI : condI, j0 > 0, m > 1:
          Trans (N[m]) = operB (Trans N) (numBT (m-1))
          owner: SS 8.1 commutation (p_8_1_Trans_fseq_condI (1)) = the c1-around
          assembly m_8_1_c1_around_part1..part5 + induction glue
          (m_8_1_stepT_j0pos_of_lhs_closed carries the j0>0 step; the j0=0 leg
          is ALREADY closed here).  Shape matches
          m_8_1_Trans_fseq_condI_descent's `commute` hypothesis exactly.

  exchII: condII, m > 1:
          EX k. Trans (N[m]) = operB (Trans N) (numBT k)
          owner: SS 8.3 (p_8_3_TransCondII_oper_descend conclusion (2), exposed
          operB form) = m_8_3_exch_of_lhs_closed's lhs residual (kind-0).
          Shape = m_8_3_TransCondII_oper_descend_engine's `exch` exactly.
          (Empirically vacuous on the genuine pool -- see NOTE above.)

  exchIII/exchIV/exchV/exchVI: condX, m > 1:
          EX k. leBT (Trans (N[m])) (operB (Trans N) (numBT k))
          owner: the SHARED kind-1 lhs marking-nesting surgery (the SS 8 wall):
          m_8_4_exch_of_lhs_closed (III), m_8_5_exch_of_lhs_closed (V),
          m_8_6_exch_of_lhs_closed (VI) each reduce their exch to the SAME
          "core A" replicate-count residual; the SS 8.5 surgery master key
          (m_8_5_markstep_of_Trans_keystone green-modulo chain, memory
          pss-85-surgery-masterkey) is the single exposed keystone.
          condIV's commutation shape still needs empirical validation
          (cf. A27 Pred_oper0 falsity note) -- hence a separate hypothesis.
          Shapes = the engines' `exch` hypotheses exactly
          (m_8_5_TransCondV_oper_descend_engine / m_8_6_TransCondVI_oper_descend_engine;
          III/IV are inlined engine bodies in f7x_fseq_descend_mono).

ASSEMBLY ACCOUNT: once {TOT, exchI, exchIII..exchVI} land (exchII if non-vacuous),
  p_8_7_fseq_descend = m_8_7_fseq_descend_of_exchange[OF _ _ _ TOT exchI ... exchVI]
  and with it the SS 8.7 main-result chain (fseq descent -> wf lessBT on OT_B
  [buc1_2_2_wf] -> Fdom totality) has no remaining pair-sequence-side gap in
  the descent pillar.

DEAD ENDS / PITFALLS hit this round (do not re-walk):
  - Trans additivity "Trans (A @ N) = Trans A + Trans N" is FALSE bare: a
    leading [(0,0)] component of N contributes D_0 0 embedded vs 0 standalone
    (CEX: A=((0,0)), N=((0,0))^n from PJ=((0,0),(1,0))).  The corrected form
    (f7x_Trans_append_Pblocks) carries the if-correction.
  - `using trans_multi_split_full ... by simp` breaks: simp normalizes
    take/drop-of-append in the FACTS (take_append/drop_append) so they no
    longer match; use `unfolding dropN takeA` (pure rewrites) instead.
  - The engine-facing exch hypotheses MUST keep the `1 < m` guard: n = 1 is
    always the Pred leaf (m_8_4_oper1_eq_Pred) and several closed forms are
    false at n = 1.
"""

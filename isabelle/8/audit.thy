theory audit
  imports
    P_8_2_standard_slice_Red_strongmono
    P_8_2_strongmono_slice
    P_8_2_subexpr_component_Pred
    P_8_2_subexpr_component_strongmono
    P_8_2_condV_rightmost_parent
    P_8_2_condV_terminal_slice_Trans
    P_8_2_condIIIV_terminal_slice_Trans
    P_8_1_diagSeq_Trans
    P_8_1_Pred_diagSeq_Trans
    P_8_1_condI_III_c1_around
    P_8_1_Trans_fseq_condI
    P_8_3_kind0_base_ineq
    P_8_3_kind0_branch_rule
    P_8_3_kind0_base_basepoint
    P_8_3_TransCondII_oper_descend
    P_8_4_Trans_oper_exchange
    P_8_4_rightmost_nonadm_ancestor
    P_8_4_oper_basic
    P_8_5_Trans_oper_exchange
    P_8_5_Joints_FirstNodes_basic
    P_8_6_const2nd_Trans
    P_8_6_diagSeq_Trans_oper
    P_8_6_trailing_principal_annihilable
    P_8_6_Trans_fseq_condVI
    P_8_7_const00_Trans
    P_8_7_fseq_descend
    P_8_7_OT_scb_recursive
    P_8_7_OT_dom_hereditary
    P_8_7_OT_tail_annihilable
    P_8_7_Pred_oper0
    P_8_7_OT_examples
    P_8_7_Trans_preserves_OT
    P_8_7_termination
begin

ML \<open>
  fun sorry_deps th =
    let
      val all_sorries =
        ["P_5_1_parent_exists_1.p_5_1_parent_exists_1", "P_5_1_parent_exists_2.p_5_1_parent_exists_2", "P_5_1_parent_exists_3.p_5_1_parent_exists_3", "P_5_1_parent_exists_4.p_5_1_parent_exists_4", "P_5_1_parent_basic_1.p_5_1_parent_basic_1", "P_5_1_parent_basic_2.p_5_1_parent_basic_2", "P_5_1_ancestor_basic_1.p_5_1_ancestor_basic_1", "P_5_1_ancestor_basic_2.p_5_1_ancestor_basic_2", "P_5_1_ancestor_tree_1.p_5_1_ancestor_tree_1", "P_5_1_ancestor_tree_2.p_5_1_ancestor_tree_2", "P_5_3_pred_is_oper1.p_5_3_pred_is_oper1", "P_5_4_F_oper_dom.p_5_4_F_oper_dom", "P_5_4_F_oper_val.p_5_4_F_oper_val", "P_6_1_le_IncrFirst_inv.p_6_1_le_IncrFirst_inv", "P_6_2_multi_crit_12.p_6_2_multi_crit_12", "P_6_2_multi_crit_23.p_6_2_multi_crit_23", "P_6_2_mono_prefix.p_6_2_mono_prefix", "P_6_2_mono_ancestor_slice.p_6_2_mono_ancestor_slice", "P_6_2_P_IncrFirst.p_6_2_P_IncrFirst", "P_6_2_P_components_1.p_6_2_P_components_1", "P_6_2_P_components_2.p_6_2_P_components_2", "P_6_2_P_additive.p_6_2_P_additive", "P_6_2_P_oper_1.p_6_2_P_oper_1", "P_6_2_P_oper_2.p_6_2_P_oper_2", "P_6_2_nonmulti_oper_1.p_6_2_nonmulti_oper_1", "P_6_2_nonmulti_oper_2.p_6_2_nonmulti_oper_2", "P_6_3_adm_slice.p_6_3_adm_slice", "P_6_3_admof_slice.p_6_3_admof_slice", "P_6_3_marked_slice.p_6_3_marked_slice", "P_6_4_P_IdxSum.p_6_4_P_IdxSum", "P_6_4_P_IdxSum.p_6_4_P_IdxSum_char_1", "P_6_4_P_IdxSum.p_6_4_P_IdxSum_char_2", "P_6_4_P_leftend_mono.p_6_4_P_leftend_mono", "P_6_4_mono_slice.p_6_4_mono_slice_next", "P_6_4_FirstNodes_TrMax_Joints.p_6_4_FirstNodes_TrMax_Joints", "P_6_4_FirstNodes_Joints_mono.p_6_4_FirstNodes_Joints_mono", "P_6_4_mono_slice.p_6_4_mono_slice", "P_6_5_Red_welldef.p_6_5_Red_welldef", "P_6_5_Red_IncrFirst.p_6_5_Red_IncrFirst", "P_6_5_Lng_Red.p_6_5_Lng_Red", "P_6_5_Red_zeroT.p_6_5_Red_zeroT", "P_6_5_Red_le.p_6_5_Red_le", "P_6_5_Red_monoT.p_6_5_Red_monoT", "P_6_5_P_Red.p_6_5_P_Red", "P_6_5_monoT_Red.p_6_5_monoT_Red", "P_6_5_Red_idem.p_6_5_Red_idem", "P_6_5_Red_Pred.p_6_5_Red_Pred", "P_6_5_Red_oper.p_6_5_Red_oper", "P_6_5_Red_adm.p_6_5_Red_adm", "P_6_5_admof_Red.p_6_5_admof_Red", "P_6_5_Red_marked.p_6_5_Red_marked", "P_6_6_reduced_slice.p_6_6_reduced_slice", "P_6_6_P_reduced.p_6_6_P_reduced", "P_6_6_reduced_oper.p_6_6_reduced_oper", "P_6_6_reduced_iff_cond.p_6_6_reduced_iff_cond", "P_6_6_Red_leftend_1.p_6_6_Red_leftend_1", "P_6_6_Red_leftend_2.p_6_6_Red_leftend_2", "P_6_6_reduced_coeff.p_6_6_reduced_coeff", "P_6_6_reduced_leftend.p_6_6_reduced_leftend", "P_6_6_condAB_coeff.p_6_6_condAB_coeff", "P_6_6_ancestor_slice_Red_IncrFirst.p_6_6_ancestor_slice_Red_IncrFirst", "P_6_6_oneColumn.p_6_6_oneColumn", "P_6_7_standard_reduced.p_6_7_standard_reduced", "P_6_7_ST_eq_Union_SkT.p_6_7_ST_eq_Union_SkT", "P_6_7_standard_P_components.p_6_7_standard_P_components", "P_6_7_standard_prefix.p_6_7_standard_prefix", "P_6_8_standard_slice_Br_descending.p_6_8_standard_slice_Br_descending", "P_6_8_standard_P_descending.p_6_8_standard_P_descending", "P_7_1_lessBT_linord.p_7_1_lessBT_linord", "P_7_1_term_components.p_7_1_term_components", "pss_paper.buc1_2_2_OT_B_wf", "pss_paper.buc1_3_2a_fseq_lt", "pss_paper.buc1_3_2_OT_B_closed", "P_7_1_paren_balance.p_7_1_paren_balance", "P_7_2_scb_replaceable.p_7_2_scb_replaceable", "P_7_2_scb_compose.p_7_2_scb_compose", "P_7_2_scb_triviality.p_7_2_scb_triviality", "P_7_2_scb_unique.p_7_2_scb_unique", "P_7_2_add_scb.p_7_2_add_scb", "P_7_2_scb_fseq.p_7_2_scb_fseq", "P_7_2_RightNodes_subexpr.p_7_2_RightNodes_subexpr", "P_7_3_twoColumn.p_7_3_twoColumn", "P_7_3_Trans_IncrFirst_Red.p_7_3_Trans_IncrFirst_Red", "P_7_3_Mark_IncrFirst_Red.p_7_3_Mark_IncrFirst_Red", "P_7_3_Trans_zeroT.p_7_3_Trans_zeroT", "P_7_3_c1_c2.p_7_3_c1_c2", "P_7_3_Pred_Trans_descend.p_7_3_Pred_Trans_descend", "P_7_3_Mark_rightmost1.p_7_3_Mark_rightmost1", "P_7_3_Trans_monoT.p_7_3_Trans_monoT", "P_7_4_Adm_nextAdm.p_7_4_Adm_nextAdm", "P_7_4_Trans_nextAdm.p_7_4_Trans_nextAdm", "P_7_4_Mark_nextAdm.p_7_4_Mark_nextAdm", "P_7_4_Trans_Mark_Pred.p_7_4_Trans_Mark_Pred", "P_7_4_Mark_Trans_repr.p_7_4_Mark_Trans_repr", "P_7_4_Trans_Mark_seg.p_7_4_Trans_Mark_seg", "P_7_4_RightNodes_Mark.p_7_4_RightNodes_Mark", "P_7_4_RightAnces_RightNodes.p_7_4_RightAnces_RightNodes", "P_7_4_RightAnces_zeroT.p_7_4_RightAnces_zeroT", "P_8_2_standard_slice_Red_strongmono.p_8_2_standard_slice_Red_strongmono", "P_8_2_strongmono_slice.p_8_2_strongmono_slice", "P_8_2_subexpr_component_Pred.p_8_2_subexpr_component_Pred", "P_8_2_subexpr_component_strongmono.p_8_2_subexpr_component_strongmono", "P_8_2_condV_rightmost_parent.p_8_2_condV_rightmost_parent", "P_8_2_condV_terminal_slice_Trans.p_8_2_condV_terminal_slice_Trans", "P_8_2_condIIIV_terminal_slice_Trans.p_8_2_condIIIV_terminal_slice_Trans", "P_8_1_diagSeq_Trans.p_8_1_diagSeq_Trans", "P_8_1_Pred_diagSeq_Trans.p_8_1_Pred_diagSeq_Trans", "P_8_1_condI_III_c1_around.p_8_1_condI_III_c1_around", "P_8_1_Trans_fseq_condI.p_8_1_Trans_fseq_condI", "P_8_3_kind0_base_ineq.p_8_3_kind0_base_ineq", "P_8_3_kind0_branch_rule.p_8_3_kind0_branch_rule", "P_8_3_kind0_base_basepoint.p_8_3_kind0_base_basepoint", "P_8_3_TransCondII_oper_descend.p_8_3_TransCondII_oper_descend", "P_8_4_Trans_oper_exchange.p_8_4_Trans_oper_exchange", "P_8_4_rightmost_nonadm_ancestor.p_8_4_rightmost_nonadm_ancestor", "P_8_4_oper_basic.p_8_4_oper_basic", "P_8_5_Trans_oper_exchange.p_8_5_Trans_oper_exchange", "P_8_5_Joints_FirstNodes_basic.p_8_5_Joints_FirstNodes_basic", "P_8_6_const2nd_Trans.p_8_6_const2nd_Trans", "P_8_6_diagSeq_Trans_oper.p_8_6_diagSeq_Trans_oper", "P_8_6_trailing_principal_annihilable.p_8_6_trailing_principal_annihilable", "P_8_6_Trans_fseq_condVI.p_8_6_Trans_fseq_condVI", "P_8_7_const00_Trans.p_8_7_const00_Trans", "P_8_7_fseq_descend.p_8_7_fseq_descend", "P_8_7_OT_scb_recursive.p_8_7_OT_scb_recursive", "P_8_7_OT_dom_hereditary.p_8_7_OT_dom_hereditary", "P_8_7_OT_tail_annihilable.p_8_7_OT_tail_annihilable", "P_8_7_Pred_oper0.p_8_7_Pred_oper0", "P_8_7_OT_examples.p_8_7_OT_examples", "P_8_7_Trans_preserves_OT.p_8_7_Trans_preserves_OT", "P_8_7_termination.p_8_7_termination"];
      val ds =
        Proofterm.fold_body_thms
          (fn {thm_name, ...} => fn acc => insert (op =) (Thm_Name.short thm_name) acc)
          [Thm.proof_body_of th] [];
    in filter (member (op =) all_sorries) ds end;

  fun assert_clean (n, th) =
    (case filter (fn d => Long_Name.base_name d <> n) (sorry_deps th) of
       [] => ()
     | bad => error ("AUDIT FAILED: " ^ n ^ " depends on sorry: " ^ commas bad));

  fun assert_all_clean (n, ths) =
    List.app (fn th => assert_clean (n, th)) ths;

  fun assert_only_stale (n, th) =
    (case sorry_deps th of
       ["pss_paper.buc1_3_2a_fseq_lt"] => ()
     | bad => error ("AUDIT FAILED: " ^ n ^ " sorry-deps = [" ^ commas bad ^
                     "] (expected exactly the stale buc1_3_2a_fseq_lt)"));

  val _ = map assert_clean
    [("y4_buc1_2_2_OT_B_wf", @{thm y4_buc1_2_2_OT_B_wf}),
     ("y4_wf_RPrel",         @{thm y4_wf_RPrel}),
     ("y4_cof0",             @{thm y4_cof0}),
     ("y4_bwl_cof",          @{thm y4_bwl_cof}),
     ("y4_PSS_acc_of_KK",    @{thm y4_PSS_acc_of_KK}),
     ("y4_PSS_wf_of_KK",     @{thm y4_PSS_wf_of_KK}),
     ("oi10_census_KK",      @{thm oi10_census_KK(1)}),
     \<comment> \<open>r72: the residual KK is DISCHARGED --- these are UNCONDITIONAL\<close>
     ("ox12_KK_free",        @{thm ox12_KK_free}),
     ("oi12_census(1)",      @{thm oi12_census(1)}),
     ("oi12_census(2)",      @{thm oi12_census(2)}),
     ("y5_Trans_OT_B",       @{thm y5_Trans_OT_B}),
     ("y5_Trans_descend",    @{thm y5_Trans_descend}),
     ("y5_PSS_acc",          @{thm y5_PSS_acc}),
     ("y5_PSS_wf",           @{thm y5_PSS_wf}),
     \<comment> \<open>r72: the ARTICLE'S OWN termination statement, p_8_7_termination\<close>
     ("y5_Fdom",             @{thm y5_Fdom}),
     \<comment> \<open>r72: the \<section>8.1 / \<section>8.3 OT-membership slots\<close>
     ("y5_8_1_condI_OT",     @{thm y5_8_1_condI_OT(2)}),
     ("y5_8_3_condII_OT",    @{thm y5_8_3_condII_OT(2)}),
     ("y5_8_3_TransCondII_oper_descend", @{thm y5_8_3_TransCondII_oper_descend}),
     \<comment> \<open>r73: the \<section>8.1 proposition on its FULL article domain \<open>RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close>
         (the \<open>ST\<^bsub>PS\<^esub>\<close> scope gap) --- both conclusions, all \<open>n \<ge> 1\<close>\<close>
     ("y3g_condI_exchange1_rtps",    @{thm y3g_condI_exchange1_rtps}),
     ("y3g_condI_descent_rtps",      @{thm y3g_condI_descent_rtps}),
     ("y3g_p_8_1_Trans_fseq_condI(1)", @{thm y3g_p_8_1_Trans_fseq_condI(1)}),
     ("y3g_p_8_1_Trans_fseq_condI(2)", @{thm y3g_p_8_1_Trans_fseq_condI(2)}),
     \<comment> \<open>r74: the \<section>8.5 命題（条件(V)の下での\<open>Trans\<close>と基本列の交換関係）, all three
         conclusions at the article's OWN printed index \<open>m\<^sub>n\<close> --- both legs\<close>
     ("y3h_p_8_5_Trans_oper_exchange(1)", @{thm y3h_p_8_5_Trans_oper_exchange(1)}),
     ("y3h_p_8_5_Trans_oper_exchange(2)", @{thm y3h_p_8_5_Trans_oper_exchange(2)}),
     ("y3h_p_8_5_Trans_oper_exchange(3)", @{thm y3h_p_8_5_Trans_oper_exchange(3)}),
     \<comment> \<open>r74: the \<section>8.4 補題（条件(III)か(IV)の下での基本列の基本性質）, parts (1) and (3)\<close>
     ("y3h_p_8_4_oper_basic(1)", @{thm y3h_p_8_4_oper_basic(1)}),
     ("y3h_p_8_4_oper_basic(2)", @{thm y3h_p_8_4_oper_basic(2)}),
     \<comment> \<open>r75: the \<section>8.4 internal-symbol lemma cluster (the six article lemmas)\<close>
     ("y3i_Trans_s1_c2_b1(1)",   @{thm y3i_Trans_s1_c2_b1(1)}),
     ("y3i_Trans_s1_c2_b1(2)",   @{thm y3i_Trans_s1_c2_b1(2)}),
     ("y3i_L1_rightend_Trans",   @{thm y3i_L1_rightend_Trans}),
     ("y3i_L2_oper_props(1)",    @{thm y3i_L2_oper_props(1)}),
     ("y3i_L2_oper_props(3)",    @{thm y3i_L2_oper_props(3)}),
     ("y3i_L2_oper_props(6)",    @{thm y3i_L2_oper_props(6)}),
     ("y3i_L2_oper_props(8)",    @{thm y3i_L2_oper_props(8)}),
     ("y3i_L3_Trans_scb",        @{thm y3i_L3_Trans_scb}),
     ("y3i_L4_slice_scb(1)",     @{thm y3i_L4_slice_scb(1)}),
     ("y3i_L4_slice_scb(2)",     @{thm y3i_L4_slice_scb(2)}),
     ("y3i_L5_various_scb_IIIV", @{thm y3i_L5_various_scb_IIIV}),
     ("y3i_L6_various_scb_IIIIV", @{thm y3i_L6_various_scb_IIIIV}),

     \<comment> \<open>r75: RED2 --- \<open>Red (Red M) \<in> RT\<^bsub>PS\<^esub>\<close> on all of \<open>T\<^bsub>PS\<^esub>\<close>, hence
         \<open>RedStab = T\<^bsub>PS\<^esub>\<close>, hence the four \<section>7 propositions on BARE \<open>T\<^bsub>PS\<^esub>\<close>\<close>
     ("y3r_RED2",                 @{thm y3r_RED2}),
     ("y3r_Red3_eq_Red2",         @{thm y3r_Red3_eq_Red2}),
     ("y3r_RedStab_TPS",          @{thm y3r_RedStab_TPS}),
     ("y3r_7_3_Trans_zeroT_TPS",  @{thm y3r_7_3_Trans_zeroT_TPS}),
     ("y3r_7_3_Pred_Trans_descend_TPS", @{thm y3r_7_3_Pred_Trans_descend_TPS}),
     ("y3r_7_4_RightAnces_RightNodes_TPS", @{thm y3r_7_4_RightAnces_RightNodes_TPS}),
     ("y3r_7_4_RightAnces_zeroT_TPS", @{thm y3r_7_4_RightAnces_zeroT_TPS}),

     \<comment> \<open>r76: the \<section>6.5 命題（単項性と \<open>Red\<close> の関係）on its FULL domain \<open>PT\<^bsub>PS\<^esub>\<close>
         (guarded leading diagonal; no \<open>m\<^sub>1\<^sub>0 > 0\<close> side condition)\<close>
     ("y3q_6_5_monoT_Red",        @{thm y3q_6_5_monoT_Red}),
     \<comment> \<open>r76: \<section>8.3 命題 conclusions (1)(2)(3) --- the exchange relation under
         condition (II), in the \<open>Trans\<close>-recursion's internal symbols\<close>
     ("y3j_condII_tailval",        @{thm y3j_condII_tailval}),
     ("y3j_condII_INV",            @{thm y3j_condII_INV}),
     ("y3j_p_8_3_condII_exchange_1", @{thm y3j_p_8_3_condII_exchange_1}),
     ("y3j_p_8_3_condII_exchange_2", @{thm y3j_p_8_3_condII_exchange_2}),
     ("y3j_p_8_3_condII_exchange_3", @{thm y3j_p_8_3_condII_exchange_3}),
     ("y3j_p_8_3_TransCondII_oper_exchange(1)",
        @{thm y3j_p_8_3_TransCondII_oper_exchange(1)}),
     ("y3j_p_8_3_TransCondII_oper_exchange(2)",
        @{thm y3j_p_8_3_TransCondII_oper_exchange(2)}),
     ("y3j_p_8_3_TransCondII_oper_exchange(3)",
        @{thm y3j_p_8_3_TransCondII_oper_exchange(3)}),
     ("y3j_p_8_3_TransCondII_oper_exchange(4)",
        @{thm y3j_p_8_3_TransCondII_oper_exchange(4)}),
     \<comment> \<open>r76: the \<open>reg\<close>-free REGS/REGSP chain and \<section>8.4 L4 without \<open>reg\<close>\<close>
     ("y3k_jm2_lt_Lm2",       @{thm y3k_jm2_lt_Lm2}),
     ("y3k_regS",             @{thm y3k_regS}),
     ("y3k_regSP_uncond",     @{thm y3k_regSP_uncond}),
     ("y3k_REGS",             @{thm y3k_REGS}),
     ("y3k_REGSP",            @{thm y3k_REGSP}),
     ("y3k_L4_slice_scb(1)",  @{thm y3k_L4_slice_scb(1)}),
     ("y3k_L4_slice_scb(2)",  @{thm y3k_L4_slice_scb(2)}),
     \<comment> \<open>r76: \<section>8.4 補題 part (2) --- the Trans/fseq exchange on \<open>L\<^sub>n\<close>\<close>
     ("y3l_op1pow_take",      @{thm y3l_op1pow_take}),
     ("y3l_L_eq_op1pow",      @{thm y3l_L_eq_op1pow}),
     ("y3l_p_8_4_oper_basic_part2", @{thm y3l_p_8_4_oper_basic_part2}),
     ("y3l_p_8_4_oper_basic_part2_condIII",
        @{thm y3l_p_8_4_oper_basic_part2_condIII}),
     \<comment> \<open>r77: \<section>8.4 補題 part (2) --- the condIV \<open>admeq\<close> corner, and the FULL
         (III)-or-(IV) statement with no regime side condition\<close>
     ("y3m_c2_principal",     @{thm y3m_c2_principal}),
     ("y3m_N_eq_c2",          @{thm y3m_N_eq_c2}),
     ("y3m_p_8_4_oper_basic_part2_condIV_admeq",
        @{thm y3m_p_8_4_oper_basic_part2_condIV_admeq}),
     ("y3m_p_8_4_oper_basic_part2_full",
        @{thm y3m_p_8_4_oper_basic_part2_full}),
     \<comment> \<open>r77: the CORRECTED forms of the nine FALSE \<open>pss_paper\<close> statements ---
         each must itself be free of every \<open>pss_paper\<close> \<open>sorry\<close> (in particular it
         must not cite the false statement it replaces)\<close>
     ("y3u_p_7_2_scb_replaceable",   @{thm y3u_p_7_2_scb_replaceable}),
     ("y3u_p_7_2_scb_compose_2",     @{thm y3u_p_7_2_scb_compose_2}),
     ("y3u_p_7_2_add_scb_3",         @{thm y3u_p_7_2_add_scb_3}),
     ("y3u_p_7_3_Mark_rightmost1",   @{thm y3u_p_7_3_Mark_rightmost1}),
     ("y3u_p_7_4_Trans_nextAdm",     @{thm y3u_p_7_4_Trans_nextAdm}),
     ("y3u_p_7_4_Mark_nextAdm",      @{thm y3u_p_7_4_Mark_nextAdm}),
     ("y3u_p_7_4_Trans_Mark_Pred",   @{thm y3u_p_7_4_Trans_Mark_Pred}),
     ("y3u_p_8_1_c1_around_part1",   @{thm y3u_p_8_1_c1_around_part1}),
     ("y3u_p_8_1_c1_around_part5",   @{thm y3u_p_8_1_c1_around_part5}),
     ("y3u_p_8_3_kind0_base_ineq",   @{thm y3u_p_8_3_kind0_base_ineq}),
     \<comment> \<open>r77: the \<section>8.7 top-level tail annihilation, freed of the
         sorry'd \<open>buc1_2_2_OT_B_wf\<close> citation (uses \<open>y4_buc1_2_2_OT_B_wf\<close>)\<close>
     ("y3t_toplevel_OT_tail_annihilate", @{thm y3t_toplevel_OT_tail_annihilate}),
     \<comment> \<open>r77: the \<section>7.4 \<open>Mark\<close>/\<open>NextAdm\<close> proposition on \<open>T\<^bsub>PS\<^esub>\<close>, modulo the two
         \<open>Marked\<close>-transport bricks (Brick A / Brick B) --- sorry-free\<close>
     ("y3t_7_4_Mark_nextAdm_TPS_of_bricks", @{thm y3t_7_4_Mark_nextAdm_TPS_of_bricks}),
     \<comment> \<open>r78: (F) --- \<open>Red\<close> only ADDS row-0 ancestor edges, on ALL of \<open>T\<^bsub>PS\<^esub>\<close>;
         and the \<section>7.4 \<open>Mark\<close>/\<open>NextAdm\<close> proposition on \<open>T\<^bsub>PS\<^esub>\<close> with its residue
         reduced to the two \<open>adm\<close> facts at the reduct\<close>
     ("y3w_Red_le0",              @{thm y3w_Red_le0}),
     ("y3w_Red2_le0",             @{thm y3w_Red2_le0}),
     ("y3w_Red2_leR0",            @{thm y3w_Red2_leR0}),
     ("y3w_nadm_local",           @{thm y3w_nadm_local}),
     ("y3w_7_4_Mark_nextAdm_TPS_of_adm", @{thm y3w_7_4_Mark_nextAdm_TPS_of_adm}),
     \<comment> \<open>r80: \<open>Mark N k\<close> is principal-or-zero for EVERY column of a reduced \<open>N\<close>\<close>
     ("y3y_Mark_princ(1)",        @{thm y3y_Mark_princ(1)}),
     ("y3y_Mark_princ(2)",        @{thm y3y_Mark_princ(2)}),
     \<comment> \<open>r81-Y4: the FREE nesting engine --- no \<open>adm\<close>, no \<open>Marked\<close>, no ancestry, no range
         condition; and the honest \<open>RT\<^bsub>PS\<^esub>\<close> JOINT engine, whose real hypothesis is the
         surgery guard \<open>j\<^sub>0 \<le> transJm1 N\<close> and not \<open>Marked\<close>-ness\<close>
     ("y4b_Mark_nest_free",       @{thm y4b_Mark_nest_free}),
     ("y4c_Mark_nest_free_ex1",   @{thm y4c_Mark_nest_free_ex1}),
     ("y4d_Mark_nest_Pred_joint", @{thm y4d_Mark_nest_Pred_joint}),
     ("y4e_Mark_nest_relaxed",    @{thm y4e_Mark_nest_relaxed}),
     ("y4e_Mark_nest_relaxed_Pred", @{thm y4e_Mark_nest_relaxed_Pred}),
     ("y4f_surg_guard_of_jm1",    @{thm y4f_surg_guard_of_jm1}),
     ("y4f_Mark_nest_Pred_joint_sharp", @{thm y4f_Mark_nest_Pred_joint_sharp}),
     \<comment> \<open>The \<section>7.4 counterexample conclusions and their annotations are now
         checked by the sibling \<open>PSS_CORRECTIONS\<close> session.  This live prerequisite of
         that archive remains proof-term clean.\<close>
     ("y6B6_nadm3",               @{thm y6B6_nadm3})];

  \<comment> \<open>Phase 4: the documented wrappers retained exactly from main must
      remain explicit skip-proofs.  The \<section>8.1 wrapper is article-false under the
      live A20/A21 corrections; the four \<section>8.6/\<section>8.7 wrappers are true but
      unproved in main (A25--A27/A34/A37 are retracted).  Their proved restricted
      helper families above remain proof-term clean and the termination path must
      not depend on them.\<close>
  val _ = List.app
    (fn (n, th) =>
      if Thm_Deps.has_skip_proof [th] then ()
      else error ("AUDIT FAILED: " ^ n ^ " is no longer the documented stub"))
    [("p_8_1_condI_III_c1_around", @{thm p_8_1_condI_III_c1_around}),
     ("p_8_6_trailing_principal_annihilable", @{thm p_8_6_trailing_principal_annihilable}),
     ("p_8_6_Trans_fseq_condVI", @{thm p_8_6_Trans_fseq_condVI}),
     ("p_8_7_OT_tail_annihilable", @{thm p_8_7_OT_tail_annihilable}),
     ("p_8_7_Pred_oper0", @{thm p_8_7_Pred_oper0})];

  \<comment> \<open>Every other relocated \<section>8 article proposition is proof-term clean.
      Using \<open>@{thms ...}\<close> audits every exported conclusion of multi-result facts.\<close>
  val _ = map assert_all_clean
    [("p_8_1_diagSeq_Trans", @{thms p_8_1_diagSeq_Trans}),
     ("p_8_1_Pred_diagSeq_Trans", @{thms p_8_1_Pred_diagSeq_Trans}),
     ("p_8_1_Trans_fseq_condI", @{thms p_8_1_Trans_fseq_condI}),
     ("p_8_2_standard_slice_Red_strongmono", @{thms p_8_2_standard_slice_Red_strongmono}),
     ("p_8_2_strongmono_slice", @{thms p_8_2_strongmono_slice}),
     ("p_8_2_subexpr_component_Pred", @{thms p_8_2_subexpr_component_Pred}),
     ("p_8_2_subexpr_component_strongmono", @{thms p_8_2_subexpr_component_strongmono}),
     ("p_8_2_condV_rightmost_parent", @{thms p_8_2_condV_rightmost_parent}),
     ("p_8_2_condV_terminal_slice_Trans", @{thms p_8_2_condV_terminal_slice_Trans}),
     ("p_8_2_condIIIV_terminal_slice_Trans", @{thms p_8_2_condIIIV_terminal_slice_Trans}),
     ("p_8_3_kind0_base_ineq", @{thms p_8_3_kind0_base_ineq}),
     ("p_8_3_kind0_branch_rule", @{thms p_8_3_kind0_branch_rule}),
     ("p_8_3_kind0_base_basepoint", @{thms p_8_3_kind0_base_basepoint}),
     ("p_8_3_TransCondII_oper_descend", @{thms p_8_3_TransCondII_oper_descend}),
     ("p_8_4_Trans_oper_exchange", @{thms p_8_4_Trans_oper_exchange}),
     ("p_8_4_rightmost_nonadm_ancestor", @{thms p_8_4_rightmost_nonadm_ancestor}),
     ("p_8_4_oper_basic", @{thms p_8_4_oper_basic}),
     ("p_8_5_Trans_oper_exchange", @{thms p_8_5_Trans_oper_exchange}),
     ("p_8_5_Joints_FirstNodes_basic", @{thms p_8_5_Joints_FirstNodes_basic}),
     ("p_8_6_const2nd_Trans", @{thms p_8_6_const2nd_Trans}),
     ("p_8_6_diagSeq_Trans_oper", @{thms p_8_6_diagSeq_Trans_oper}),
     ("p_8_7_const00_Trans", @{thms p_8_7_const00_Trans}),
     ("p_8_7_fseq_descend", @{thms p_8_7_fseq_descend}),
     ("p_8_7_OT_scb_recursive", @{thms p_8_7_OT_scb_recursive}),
     ("p_8_7_OT_dom_hereditary", @{thms p_8_7_OT_dom_hereditary}),
     ("p_8_7_OT_examples", @{thms p_8_7_OT_examples}),
     ("p_8_7_Trans_preserves_OT", @{thms p_8_7_Trans_preserves_OT}),
     ("p_8_7_termination", @{thms p_8_7_termination})];

  \<comment> \<open>r72: assert the termination theorems carry NO free hypothesis left ---
      \<open>y5_PSS_wf\<close> must be a closed statement (no meta-premises, no schematics).\<close>
  val _ =
    let
      val th = @{thm y5_PSS_wf};
      val t  = Thm.prop_of th;
    in
      if Thm.nprems_of th = 0 andalso null (Thm.hyps_of th)
         andalso null (Term.add_frees t []) andalso null (Term.add_vars t [])
      then () else error "AUDIT FAILED: y5_PSS_wf is not a closed hypothesis-free statement"
    end;

  \<comment> \<open>The three termination endpoints must carry no ambient theorem
      hypotheses.  The article-facing \<open>p_8_7_termination\<close> and \<open>y5_Fdom\<close>
      naturally retain their three printed meta-premises; the unconditional
      \<open>y5_PSS_wf\<close> is additionally checked above to have no premises or frees.\<close>
  val _ = List.app
    (fn (n, th) =>
      if null (Thm.hyps_of th) then ()
      else error ("AUDIT FAILED: " ^ n ^ " carries theorem hypotheses"))
    [("p_8_7_termination", @{thm p_8_7_termination}),
     ("y5_Fdom", @{thm y5_Fdom}),
     ("y5_PSS_wf", @{thm y5_PSS_wf})];
\<close>
end

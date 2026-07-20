theory Support_6_042
  imports Frontier_6_062
begin

text \<open>CONDITIONAL keystone forward (monoT core), modulo the last-column \<open>RedCondA\<close>
  obligation \<open>condA_top\<close>.  Full \<open>measure_induct\<close> on \<open>Lng M\<close>:
  the \<open>zeroT\<close>/length-1 base is vacuous (no parents), the TRUNK case is
  @{thm [source] kfwd_reduced_core_trunk_condAB}, every \<open>RedCondA\<close>/\<open>RedCondB\<close>
  witness strictly below the last column lifts to \<open>Pred M\<close> (reduced shorter core
  by @{thm [source] ncons_Pred_core}) and uses the IH, the last-column \<open>RedCondB\<close>
  witness is vacuous (@{thm [source] kfwd_monoT_hasParent_top}), and the
  last-column \<open>RedCondA\<close> witness is the hypothesis \<open>condA_top\<close>.\<close>

lemma kst_reduced_imp_condAB_monoT_core_cond:
  assumes condA_top:
    "\<And>N i. N \<in> RT_PS \<Longrightarrow> monoT N \<Longrightarrow> entry N 0 0 = 0 \<Longrightarrow> entry N 1 0 = 0
       \<Longrightarrow> TrMax N \<noteq> Lng N - 1 \<Longrightarrow> i \<le> 1 \<Longrightarrow> hasParent N i (Lng N - 1)
       \<Longrightarrow> entry N i (parent N i (Lng N - 1)) + 1 = entry N i (Lng N - 1)"
  assumes M0: "M \<in> RT_PS" and mono0: "monoT M"
    and e000: "entry M 0 0 = 0" and e100: "entry M 1 0 = 0"
  shows "RedCondA M \<and> RedCondB M"
  using M0 mono0 e000 e100
proof (induction M rule: measure_induct_rule[where f = Lng])
  case (less M)
  have M: "M \<in> RT_PS" by (rule less.prems(1))
  have mono: "monoT M" by (rule less.prems(2))
  have e00: "entry M 0 0 = 0" by (rule less.prems(3))
  have e10: "entry M 1 0 = 0" by (rule less.prems(4))
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  let ?j1 = "Lng M - 1"
  show ?case
  proof (cases "TrMax M = Lng M - 1")
    case True
    show ?thesis by (rule kfwd_reduced_core_trunk_condAB[OF M mono e00 e10 True])
  next
    case tne: False
    have trlt: "TrMax M < Lng M - 1" using TrMax_bound[OF MT] tne by linarith
    have L2: "1 < Lng M" using trlt LMpos by linarith
    \<comment> \<open>--- RedCondA M ---\<close>
    have condA: "RedCondA M"
      unfolding RedCondA_def
    proof (intro allI impI)
      fix i j1' assume i: "i \<le> 1" and hp: "hasParent M i j1'"
      have j1L: "j1' < Lng M"
        using hp unfolding hasParent_def nextR_def nextrel0_def nextrel1_def
        by (auto split: if_splits)
      have par_lt: "parent M i j1' < j1'"
      proof -
        obtain q where q: "nextR M i q j1'"
          and uq: "\<And>r. nextR M i r j1' \<Longrightarrow> r = q"
          using hp unfolding hasParent_def by blast
        have "parent M i j1' = q"
          unfolding parent_def using q uq by (blast intro: the1_equality)
        moreover have "q < j1'" using q
          unfolding nextR_def nextrel0_def nextrel1_def by (auto split: if_splits)
        ultimately show ?thesis by simp
      qed
      show "entry M i (parent M i j1') + 1 = entry M i j1'"
      proof (cases "j1' = ?j1")
        case top: True
        have hp': "hasParent M i ?j1" using hp top by simp
        have "entry M i (parent M i ?j1) + 1 = entry M i ?j1"
          by (rule condA_top[OF M mono e00 e10 tne i hp'])
        thus ?thesis using top by simp
      next
        case below: False
        have jpos: "0 < j1'" using par_lt by linarith
        have jle: "j1' \<le> Lng M - 2" using j1L below by linarith
        have L3: "2 < Lng M" using jpos jle by linarith
        \<comment> \<open>\<open>Pred M\<close> is a strictly shorter reduced \<open>monoT\<close> core (needs \<open>2 < Lng M\<close>).\<close>
        have predRT: "Pred M \<in> RT_PS" and predmono: "monoT (Pred M)"
          and pred00: "entry (Pred M) 0 0 = 0" and pred10: "entry (Pred M) 1 0 = 0"
          and predLlt: "Lng (Pred M) < Lng M"
          using ncons_Pred_core[OF M mono e00 e10 tne L3] by blast+
        have condA_pred: "RedCondA (Pred M)"
          using less.IH[OF predLlt predRT predmono pred00 pred10] by simp
        have hpP: "hasParent (Pred M) i j1'"
          using kfwd_hasParent_Pred_iff[OF MT L2 i jle] hp by simp
        have parP: "parent (Pred M) i j1' = parent M i j1'"
          by (rule kfwd_parent_Pred_eq[OF MT L2 i jle hp])
        have parle: "parent M i j1' \<le> Lng M - 2" using par_lt jle by linarith
        \<comment> \<open>relation in \<open>Pred M\<close> (IH), pulled back via entry-agreement.\<close>
        have relP: "entry (Pred M) i (parent (Pred M) i j1') + 1
                     = entry (Pred M) i j1'"
          using condA_pred hpP i unfolding RedCondA_def by blast
        have e_par: "entry (Pred M) i (parent M i j1') = entry M i (parent M i j1')"
          by (rule kfwd_entry_Pred_eq[OF L2 parle])
        have e_j1: "entry (Pred M) i j1' = entry M i j1'"
          by (rule kfwd_entry_Pred_eq[OF L2 jle])
        show ?thesis using relP parP e_par e_j1 by simp
      qed
    qed
    \<comment> \<open>--- RedCondB M ---\<close>
    have condB: "RedCondB M"
      unfolding RedCondB_def
    proof (intro allI impI)
      fix j1' assume H: "\<not> hasParent M 0 j1' \<and> j1' \<le> Lng M - 1"
      hence noP: "\<not> hasParent M 0 j1'" and hle: "j1' \<le> Lng M - 1" by simp_all
      show "entry M 0 j1' = entry M 1 j1'"
      proof (cases "j1' = ?j1")
        case top: True
        \<comment> \<open>last column always has a row-0 parent for monoT — contradiction.\<close>
        have "hasParent M 0 ?j1" by (rule kfwd_monoT_hasParent_top[OF MT mono L2])
        thus ?thesis using noP top by simp
      next
        case below: False
        have jle: "j1' \<le> Lng M - 2" using hle below by linarith
        show ?thesis
        proof (cases "j1' = 0")
          case True
          show ?thesis using True e00 e10 by simp
        next
          case False
          have jpos: "0 < j1'" using False by simp
          have L3: "2 < Lng M" using jpos jle by linarith
          have predRT: "Pred M \<in> RT_PS" and predmono: "monoT (Pred M)"
            and pred00: "entry (Pred M) 0 0 = 0" and pred10: "entry (Pred M) 1 0 = 0"
            and predLlt: "Lng (Pred M) < Lng M"
            using ncons_Pred_core[OF M mono e00 e10 tne L3] by blast+
          have LP: "Lng (Pred M) = Lng M - 1" using L2 by (simp add: Pred_def length_butlast)
          have IHpred: "RedCondA (Pred M) \<and> RedCondB (Pred M)"
            by (rule less.IH[OF predLlt predRT predmono pred00 pred10])
          have noPP: "\<not> hasParent (Pred M) 0 j1'"
            using kfwd_hasParent_Pred_iff[OF MT L2 _ jle] noP by simp
          have hleP: "j1' \<le> Lng (Pred M) - 1" using jle LP by linarith
          have relB: "entry (Pred M) 0 j1' = entry (Pred M) 1 j1'"
            using IHpred noPP hleP unfolding RedCondB_def by blast
          have e0: "entry (Pred M) 0 j1' = entry M 0 j1'"
            by (rule kfwd_entry_Pred_eq[OF L2 jle])
          have e1: "entry (Pred M) 1 j1' = entry M 1 j1'"
            by (rule kfwd_entry_Pred_eq[OF L2 jle])
          show ?thesis using relB e0 e1 by simp
        qed
      qed
    qed
    show ?thesis using condA condB by blast
  qed
qed

end

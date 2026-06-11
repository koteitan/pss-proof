theory pss_wip
  imports pss_mechanized
begin

text \<open>
  Work-in-progress lemmas; stable results graduate back into pss_mechanized.thy.
  (Emptied 2026-06-11: the entire §6.5/§6.6/§6.7 completion arc graduated.)
\<close>


section \<open>§7.3 Trans well-definedness, brick 1: RT_PS closure under the
  Trans/Mark recursion calls (memory pss-73-trans-wd)\<close>

text \<open>Reducedness is preserved by \<open>Pred\<close>, unconditionally: for \<open>Lng M \<le> 1\<close>,
  \<open>Pred M = M\<close>; otherwise via the keystone @{thm [source] m_6_6_reduced_iff_cond}
  and the condition transfers @{thm [source] RedCondA_Pred} /
  @{thm [source] RedCondB_Pred}.\<close>

lemma Pred_RT_PS:
  assumes M: "M \<in> RT_PS"
  shows "Pred M \<in> RT_PS"
proof (cases "Lng M \<le> 1")
  case True
  thus ?thesis using M by (simp add: Pred_def)
next
  case False
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have condA: "RedCondA M" and condB: "RedCondB M"
    using m_6_6_reduced_iff_cond[OF MT] M by auto
  have PA: "RedCondA (Pred M)" by (rule RedCondA_Pred[OF MT condA])
  have PB: "RedCondB (Pred M)" by (rule RedCondB_Pred[OF MT condB])
  have "Pred M = butlast M" using False by (simp add: Pred_def)
  moreover have "0 < Lng (butlast M)" using False by simp
  ultimately have PT: "Pred M \<in> T_PS"
    using length_greater_0_conv by (fastforce simp: T_PS_def)
  show ?thesis using m_6_6_reduced_iff_cond[OF PT] PA PB by blast
qed


text \<open>RT_PS closure for the (C) multiT branch of \<open>Trans\<close>/\<open>Mark\<close>: the prefix
  \<open>take (Pcut M) M\<close> (= the article's \<open>(M\<^sub>j)\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>0-1\<^esup>\<close>) is reduced, its
  \<open>P\<close>-decomposition being \<open>butlast (P M)\<close> (@{thm [source] poper_last_P_multi})
  whose components are components of \<open>M\<close>
  (@{thm [source] m_6_6_P_reduced} both ways).
  Empirically: 0/24,243 reduced multi (len \<le> 6, e \<le> 3).\<close>

lemma trans_multiT_prefix_RT_PS:
  assumes M: "M \<in> RT_PS" and mu: "multiT M"
  shows "take (Pcut M) M \<in> RT_PS"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  have Pb: "butlast (P M) = P (take (Pcut M) M)"
    using poper_last_P_multi[OF mu L] by simp
  have PM: "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
    by (rule poper_P_multi) (use mu L in simp)
  have lenP: "Lng (P (take (Pcut M) M)) = Lng (P M) - 1" using PM by simp
  have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
  have tT: "take (Pcut M) M \<in> T_PS"
  proof -
    have Mne: "M \<noteq> []" using L by (cases M) auto
    have "0 < Lng (take (Pcut M) M)" using cut L Mne by simp
    hence "take (Pcut M) M \<noteq> []" using length_greater_0_conv by blast
    thus ?thesis by (simp add: T_PS_def)
  qed
  have comps: "\<And>J. J < Lng (P (take (Pcut M) M))
                 \<Longrightarrow> P (take (Pcut M) M) ! J \<in> RT_PS"
  proof -
    fix J assume JL: "J < Lng (P (take (Pcut M) M))"
    have "P (take (Pcut M) M) ! J = butlast (P M) ! J" using Pb by simp
    also have "\<dots> = P M ! J"
      using JL lenP by (intro nth_butlast) simp
    finally have eq: "P (take (Pcut M) M) ! J = P M ! J" .
    have "J < Lng (P M)" using JL lenP by simp
    thus "P (take (Pcut M) M) ! J \<in> RT_PS"
      using m_6_6_P_reduced[OF MT] M eq by simp
  qed
  show ?thesis using m_6_6_P_reduced[OF tT] comps by blast
qed

text \<open>Index bookkeeping tying the \<open>Trans\<close> body's \<open>j\<^sub>0 = j\<^sub>1 - Lng PJ + 1\<close> to
  \<open>Pcut M\<close>: the last \<open>P\<close>-component is \<open>drop (Pcut M) M\<close>.\<close>

lemma trans_multiT_last_component:
  assumes MT: "M \<in> T_PS" and mu: "multiT M"
  shows "P M ! (Lng (P M) - 1) = drop (Pcut M) M"
    and "Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 = Pcut M"
proof -
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  have lastP: "last (P M) = drop (Pcut M) M"
    using poper_last_P_multi[OF mu L] by simp
  have Pne: "P M \<noteq> []" by (rule P_nonempty)
  show nth_last: "P M ! (Lng (P M) - 1) = drop (Pcut M) M"
    using lastP Pne by (simp add: last_conv_nth)
  have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
  have "Lng (P M ! (Lng (P M) - 1)) = Lng M - Pcut M" using nth_last by simp
  thus "Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 = Pcut M"
    using cut L by linarith
qed




section \<open>§7.3 命題（\<open>Trans\<close>の well-defined 性） — totality on RT_PS\<close>

text \<open>The recursion of \<open>Trans\<close>/\<open>Mark\<close> terminates on \<open>RT\<^sub>PS\<close>, by strong
  induction on \<open>Lng M\<close>: the \<open>M \<notin> RT\<^sub>PS\<close> branch is unreachable, \<open>Pred\<close>
  preserves reducedness (@{thm [source] Pred_RT_PS}), and the multiT branch
  recurses into the prefix \<open>take (Pcut M) M\<close>
  (@{thm [source] trans_multiT_prefix_RT_PS}) and the last \<open>P\<close>-component
  \<open>drop (Pcut M) M\<close> (@{thm [source] m_6_6_P_reduced}), all of strictly
  smaller length.  (On all of \<open>T\<^sub>PS\<close> totality is NOT provable along the
  article's one-line argument: the (D) branch needs \<open>Red M\<close> reduced, i.e.
  idempotency, which is FALSE on \<open>T\<^sub>PS\<close> (correction A4); the §7/§8 use-sites
  are reduced/standard, so the RT_PS domain suffices.)\<close>

lemma Trans_Mark_dom_RT_PS_aux:
  "M \<in> RT_PS \<longrightarrow> Trans_Mark_dom (Inl M) \<and> (\<forall>m. Trans_Mark_dom (Inr (M, m)))"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (rule impI)
    assume MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    \<comment> \<open>shared dischargers\<close>
    have predD: "\<And>L1. \<not> Lng M \<le> Suc 0
        \<Longrightarrow> Trans_Mark_dom (Inl (Pred M)) \<and> (\<forall>m. Trans_Mark_dom (Inr (Pred M, m)))"
    proof -
      fix L1 assume L: "\<not> Lng M \<le> Suc 0"
      have "Pred M = butlast M" using L by (simp add: Pred_def)
      hence "Lng (Pred M) < Lng M" using L by simp
      moreover have "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
      ultimately show "Trans_Mark_dom (Inl (Pred M))
                       \<and> (\<forall>m. Trans_Mark_dom (Inr (Pred M, m)))"
        using less.IH by blast
    qed
    have vac: "\<And>R. \<not> Lng M \<le> Suc 0 \<Longrightarrow> \<not> monoT M \<Longrightarrow> \<not> multiT M \<Longrightarrow> R"
    proof -
      fix R assume L: "\<not> Lng M \<le> Suc 0" and nm: "\<not> monoT M" and nmu: "\<not> multiT M"
      have "zeroT M" using nm nmu by (simp add: multiT_def)
      hence "Lng M = 1" by (simp add: zeroT_def)
      thus R using L by simp
    qed
    have prefD: "\<not> Lng M \<le> Suc 0 \<Longrightarrow> multiT M
        \<Longrightarrow> Trans_Mark_dom (Inl (seg M 0 (Lng M - Suc (Lng M - Pcut M))))"
    proof -
      assume L: "\<not> Lng M \<le> Suc 0" and mu: "multiT M"
      have L1: "1 < Lng M" using L by simp
      have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L1] by simp
      have ept: "Lng M - Suc (Lng M - Pcut M) = Pcut M - 1" using cut by linarith
      have "Suc (Pcut M - 1) \<le> Lng M" using cut L1 by linarith
      hence "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
        by (rule seg_0_eq_take)
      also have "\<dots> = take (Pcut M) M" using cut by simp
      finally have segt: "seg M 0 (Lng M - Suc (Lng M - Pcut M)) = take (Pcut M) M"
        using ept by simp
      have tRT: "take (Pcut M) M \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF MR mu])
      have plt: "Pcut M < Lng M" using cut L1 by linarith
      have "Lng (take (Pcut M) M) < Lng M" using plt by (simp add: min_def)
      thus "Trans_Mark_dom (Inl (seg M 0 (Lng M - Suc (Lng M - Pcut M))))"
        using less.IH tRT segt by auto
    qed
    have dropRT: "\<not> Lng M \<le> Suc 0 \<Longrightarrow> multiT M \<Longrightarrow> drop (Pcut M) M \<in> RT_PS"
    proof -
      assume L: "\<not> Lng M \<le> Suc 0" and mu: "multiT M"
      have nth_last: "P M ! (Lng (P M) - 1) = drop (Pcut M) M"
        by (rule trans_multiT_last_component(1)[OF MT mu])
      have "Lng (P M) - 1 < Lng (P M)"
        using P_nonempty[of M] by (cases "P M") auto
      hence "P M ! (Lng (P M) - 1) \<in> RT_PS"
        using m_6_6_P_reduced[OF MT] MR by blast
      thus "drop (Pcut M) M \<in> RT_PS" using nth_last by simp
    qed
    have dropD: "\<not> Lng M \<le> Suc 0 \<Longrightarrow> multiT M
        \<Longrightarrow> Trans_Mark_dom (Inl (drop (Pcut M) M))
            \<and> (\<forall>m. Trans_Mark_dom (Inr (drop (Pcut M) M, m)))"
    proof -
      assume L: "\<not> Lng M \<le> Suc 0" and mu: "multiT M"
      have L1: "1 < Lng M" using L by simp
      have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L1] by simp
      have "Lng (drop (Pcut M) M) = Lng M - Pcut M" by simp
      hence "Lng (drop (Pcut M) M) < Lng M" using cut L1 by linarith
      thus ?thesis using less.IH dropRT[OF L mu] by blast
    qed
    have inl: "Trans_Mark_dom (Inl M)"
    proof (rule Trans_Mark.domintros(1))
      show "M \<notin> RT_PS \<Longrightarrow> Trans_Mark_dom (Inl (Red M))" using MR by simp
    next
      show "\<not> Lng M \<le> Suc 0 \<Longrightarrow> monoT M \<Longrightarrow> Trans_Mark_dom (Inl (Pred M))"
        if "M \<in> RT_PS" using predD by blast
    next
      show "Trans_Mark_dom (Inr (Pred M, Adm M (parent M 0 (Lng M - Suc 0))))"
        if "M \<in> RT_PS" "\<not> Lng M \<le> Suc 0" "monoT M" "Trans (Pred M) \<noteq> 0\<^sub>B"
        using predD that by blast
    next
      show "Trans_Mark_dom (Inl (seg M 0 (Lng M - Suc (Lng M - Pcut M))))"
        if "M \<in> RT_PS" "\<not> Lng M \<le> Suc 0" "\<not> monoT M"
           "[(0, 0)] = drop (Pcut M) M" "multiT M"
        using prefD that by blast
    next
      show "Trans_Mark_dom (Inl (seg M 0 (Lng M - Suc (Lng M - Pcut M))))"
        if "M \<in> RT_PS" "\<not> Lng M \<le> Suc 0" "\<not> monoT M"
           "drop (Pcut M) M \<noteq> [(0, 0)]" "multiT M"
        using prefD that by blast
    next
      show "Trans_Mark_dom (Inl (seg M 0 0))"
        if "M \<in> RT_PS" "\<not> Lng M \<le> Suc 0" "\<not> monoT M" "M \<noteq> [(0, 0)]" "\<not> multiT M"
        using vac that by blast
    next
      show "Trans_Mark_dom (Inl (drop (Pcut M) M))"
        if "M \<in> RT_PS" "\<not> Lng M \<le> Suc 0" "\<not> monoT M"
           "drop (Pcut M) M \<noteq> [(0, 0)]" "multiT M"
        using dropD that by blast
    next
      show "Trans_Mark_dom (Inl M)"
        if "M \<in> RT_PS" "\<not> Lng M \<le> Suc 0" "\<not> monoT M" "M \<noteq> [(0, 0)]" "\<not> multiT M"
        using vac that by blast
    qed
    have inr: "\<And>m. Trans_Mark_dom (Inr (M, m))"
    proof -
      fix m
      show "Trans_Mark_dom (Inr (M, m))"
      proof (rule Trans_Mark.domintros(2))
        show "M \<notin> RT_PS \<Longrightarrow> Trans_Mark_dom (Inr (Red M, m))" using MR by simp
      next
        show "Trans_Mark_dom (Inl (Pred M))"
          if "M \<in> RT_PS" "\<not> Lng M \<le> Suc 0" "monoT M"
          using predD that by blast
      next
        show "Trans_Mark_dom (Inr (Pred M, Adm M (parent M 0 (Lng M - Suc 0))))"
          if "M \<in> RT_PS" "\<not> Lng M \<le> Suc 0" "monoT M" "Trans (Pred M) \<noteq> 0\<^sub>B"
          using predD that by blast
      next
        show "Trans_Mark_dom (Inr (Pred M, m))"
          if "M \<in> RT_PS" "\<not> Lng M \<le> Suc 0" "monoT M" "Trans (Pred M) \<noteq> 0\<^sub>B"
             "m < Lng M - Suc 0"
          using predD that by blast
      next
        show "Trans_Mark_dom (Inr (drop (Pcut M) M,
                                   m - Suc (Lng M - Suc (Lng M - Pcut M))))"
          if "M \<in> RT_PS" "\<not> Lng M \<le> Suc 0" "\<not> monoT M"
             "drop (Pcut M) M \<noteq> [(0, 0)]" "multiT M"
          using dropD that by blast
      next
        show "Trans_Mark_dom (Inr (M, m - Suc 0))"
          if "M \<in> RT_PS" "\<not> Lng M \<le> Suc 0" "\<not> monoT M" "M \<noteq> [(0, 0)]" "\<not> multiT M"
          using vac that by blast
      qed
    qed
    show "Trans_Mark_dom (Inl M) \<and> (\<forall>m. Trans_Mark_dom (Inr (M, m)))"
      using inl inr by blast
  qed
qed

text \<open>命題（\<open>Trans\<close>の well-defined 性）, totality part, on \<open>RT\<^sub>PS\<close>.\<close>

lemma m_7_3_Trans_welldef:
  assumes "M \<in> RT_PS"
  shows "Trans_Mark_dom (Inl M)"
  using Trans_Mark_dom_RT_PS_aux assms by blast

lemma m_7_3_Mark_welldef:
  assumes "M \<in> RT_PS"
  shows "Trans_Mark_dom (Inr (M, m))"
  using Trans_Mark_dom_RT_PS_aux assms by blast

end

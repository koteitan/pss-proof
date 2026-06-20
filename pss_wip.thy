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


text \<open>First value bricks on the new domain: \<open>Trans\<close>/\<open>Mark\<close> on reduced
  singletons \<open>[(v,v)]\<close> (= all reduced length-1 sequences,
  @{thm [source] m_6_6_oneColumn}), via the (A) branch of the recursion.\<close>

lemma Trans_singleton:
  "Trans [(v, v)] = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
proof -
  have RT: "[(v, v)] \<in> RT_PS"
  proof -
    have "([(v, v)]::pairseq) \<in> T_PS" by (simp add: T_PS_def)
    thus ?thesis using m_6_6_oneColumn[of "[(v, v)]"] by auto
  qed
  have dom: "Trans_Mark_dom (Inl [(v, v)])" by (rule m_7_3_Trans_welldef[OF RT])
  show ?thesis
    using Trans.psimps[OF dom] RT by (simp add: entry_def)
qed

lemma Mark_singleton:
  "Mark [(v, v)] m = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
proof -
  have RT: "[(v, v)] \<in> RT_PS"
  proof -
    have "([(v, v)]::pairseq) \<in> T_PS" by (simp add: T_PS_def)
    thus ?thesis using m_6_6_oneColumn[of "[(v, v)]"] by auto
  qed
  have dom: "Trans_Mark_dom (Inr ([(v, v)], m))" by (rule m_7_3_Mark_welldef[OF RT])
  show ?thesis
    using Mark.psimps[OF dom] RT by (simp add: entry_def)
qed


text \<open>\<open>unflatBT\<close> inverts \<open>flatBT\<close> (by @{thm [source] m_7_flatBT_inj}); this is
  how the \<open>s\<^sub>1 c\<^sub>2 b\<^sub>1\<close> concatenations in \<open>Trans\<close>/\<open>Mark\<close> evaluate.\<close>

lemma unflatBT_flat: "unflatBT (flatBT t) = t"
  unfolding unflatBT_def
  by (rule the_equality) (auto intro: m_7_flatBT_inj)


text \<open>Evaluating the \<open>SOME\<close> scb-extraction of \<open>Trans\<close>/\<open>Mark\<close> in the trivial
  case \<open>t\<^sub>1 = c\<^sub>1\<close> (e.g. both \<open>D\<^sub>v 0\<close>): the unique \<open>(s,b)\<close> is \<open>([], [])\<close>
  (@{thm [source] m_7_2_scb_unique_sb}).\<close>

lemma isPTB_str_Dpt:
  assumes "v \<noteq> \<infinity>" and "dfree_BT t"
  shows "isPTB_str (flatBT (Dpt v t))"
proof -
  have "dfree_BP (DB v t)" using assms by simp
  moreover have "flatBT (Dpt v t) = flatBP (DB v t)" by simp
  ultimately show ?thesis unfolding isPTB_str_def by blast
qed

lemma scb_decomp_self:
  assumes "isPTB_str (flatBT t)"
  shows "scb_decomp t [] (flatBT t) []"
  using assms by (simp add: scb_decomp_def)

lemma scb_SOME_self:
  assumes pt: "isPTB_str (flatBT t)" and tne: "t \<noteq> Trm []"
  shows "(SOME sb. scb_decomp t (fst sb) (flatBT t) (snd sb)) = ([], [])"
proof (rule some_equality)
  show "scb_decomp t (fst ([], [])) (flatBT t) (snd ([], []))"
    using scb_decomp_self[OF pt] by simp
next
  fix sb assume h: "scb_decomp t (fst sb) (flatBT t) (snd sb)"
  have "fst sb = [] \<and> snd sb = []"
    using m_7_2_scb_unique_sb[OF h scb_decomp_self[OF pt] tne] by simp
  thus "sb = ([], [])" by (cases sb) auto
qed


section \<open>§7.3 命題（\<open>2\<close>列ペア数列の基本性質）, part (1): the \<open>Trans\<close> value\<close>

text \<open>For reduced mono \<open>M\<close> of length 2 (head diagonal \<open>(v,v)\<close> by
  @{thm [source] reduced_mono_head_diag}): \<open>Trans M = D\<^bsub>M\<^bsub>1,0\<^esub>\<^esub> D\<^bsub>M\<^bsub>1,1\<^esub>\<^esub> 0\<close>.
  Article 2190; the conditions fire as (I) (\<open>b=0\<close>), (III) (\<open>0<b\<le>v\<close>) or (VI)
  (\<open>b=v+1\<close>, forced by RedCondA at the row-1 parent), and the scb-\<open>SOME\<close>
  evaluates to \<open>([],[])\<close> (@{thm [source] scb_SOME_self}).\<close>

lemma m_7_3_twoColumn_Trans:
  assumes M: "M \<in> RT_PS" and mono: "monoT M" and L2: "Lng M = 2"
  shows "Trans M = Dpt (enat (entry M 1 0)) (Dpt (enat (entry M 1 1)) 0\<^sub>B)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  define v where "v = entry M 1 0"
  define b where "b = entry M 1 1"
  have hd0: "entry M 0 0 = v"
    using reduced_mono_head_diag[OF M mono] v_def by simp
  have predM: "Pred M = [(v, v)]"
  proof -
    obtain p0 p1 where Mp: "M = [p0, p1]"
      using L2 by (cases M rule: remdups_adj.cases) auto
    have "p0 = (v, v)"
      using hd0 v_def Mp by (cases p0) (simp add: entry_def)
    thus ?thesis using Mp by (simp add: Pred_def)
  qed
  have dom: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF M])
  have j1v: "Lng M - 1 = 1" using L2 by simp
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L2 by simp
  have le01: "le0 M 0 1" using mono j1v by (simp add: monoT_def leR_def)
  have nr01: "nextrel0 M 0 1"
    using le0_adjacent_step[of M 0] le01 by simp
  have par0: "parent M 0 1 = 0"
  proof -
    have uniq: "\<And>j. nextR M 0 j 1 \<Longrightarrow> j = 0"
      by (auto simp: nextR_def nextrel0_def)
    have ex1: "\<exists>!j. nextR M 0 j 1"
      using nr01 uniq by (auto simp: nextR_def)
    show ?thesis unfolding parent_def
      using the1_equality[OF ex1] nr01 uniq by (auto simp: nextR_def)
  qed
  have adm0: "adm M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
  have Adm0: "Adm M 0 = 0" using adm0 by (simp add: Adm_def)
  have e10: "entry M 1 0 = v" using v_def by simp
  have e11: "entry M 1 1 = b" using b_def by simp
  show ?thesis
  proof (cases "v = 0")
    case True
    have t1z: "Trans (Pred M) = 0\<^sub>B" using predM Trans_singleton True by simp
    have "Trans M = Dpt 0 (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
      using Trans.psimps[OF dom] M j1v Lgt1 mono t1z by (simp add: Let_def)
    thus ?thesis using True e10 j1v by (simp add: zero_enat_def)
  next
    case False
    have vpos: "0 < v" using False by simp
    have t1v: "Trans (Pred M) = Dpt (enat v) 0\<^sub>B"
      using predM Trans_singleton False by simp
    have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B" using t1v by simp
    have c1v: "Mark (Pred M) 0 = Dpt (enat v) 0\<^sub>B"
      using predM Mark_singleton False by simp
    have somev: "(SOME sb. scb_decomp (Trans (Pred M)) (fst sb)
                    (flatBT (Dpt (enat v) 0\<^sub>B)) (snd sb)) = ([], [])"
    proof -
      have pt: "isPTB_str (flatBT (Dpt (enat v) (0\<^sub>B)))"
        by (rule isPTB_str_Dpt) simp_all
      show ?thesis
        using scb_SOME_self[OF pt] t1v by simp
    qed
    have conds: "(transCondI M \<or> transCondIII M \<or> transCondV M) \<or> transCondVI M"
    proof (cases "b = 0")
      case True
      thus ?thesis using adm0 par0 j1v e11 by (simp add: transCondI_def)
    next
      case bpos: False
      show ?thesis
      proof (cases "b \<le> v")
        case True
        thus ?thesis using bpos adm0 par0 j1v e10 e11
          by (simp add: transCondIII_def)
      next
        case False
        have vlb: "v < b" using False by simp
        have nr1: "nextrel1 M 0 1"
        proof -
          have valley: "\<And>j. 0 < j \<Longrightarrow> le0 M j 1 \<Longrightarrow> entry M 1 1 \<le> entry M 1 j"
          proof -
            fix j assume j0: "0 < j" and lej: "le0 M j 1"
            have "j < Lng M" using lej by (simp add: le0_def)
            hence "j = 1" using j0 L2 by simp
            thus "entry M 1 1 \<le> entry M 1 j" by simp
          qed
          show ?thesis
            unfolding nextrel1_def
            using L2 e10 e11 vlb le01 valley by auto
        qed
        have hp1: "hasParent M 1 1"
        proof -
          have "\<And>j. nextR M 1 j 1 \<Longrightarrow> j = 0"
            by (auto simp: nextR_def nextrel1_def)
          thus ?thesis using nr1 unfolding hasParent_def nextR_def by auto
        qed
        have par1: "parent M 1 1 = 0"
        proof -
          have uniq: "\<And>j. nextR M 1 j 1 \<Longrightarrow> j = 0"
            by (auto simp: nextR_def nextrel1_def)
          have ex1: "\<exists>!j. nextR M 1 j 1"
            using nr1 uniq by (auto simp: nextR_def)
          show ?thesis unfolding parent_def
            using the1_equality[OF ex1] nr1 uniq by (auto simp: nextR_def)
        qed
        have condA: "RedCondA M"
          using m_6_6_reduced_iff_cond[OF MT] M by auto
        have "entry M 1 (parent M 1 1) + 1 = entry M 1 1"
          using condA[unfolded RedCondA_def, rule_format, of 1 1] hp1 by simp
        hence "v + 1 = b" using par1 e10 e11 by simp
        thus ?thesis using vlb par0 j1v e10 e11
          by (simp add: transCondVI_def)
      qed
    qed
    have trans_val: "Trans M = unflatBT (flatBT (Dpt (enat v) (Dpt (enat b) 0\<^sub>B)))"
    proof (cases "transCondI M \<or> transCondIII M \<or> transCondV M")
      case True
      show ?thesis
        using Trans.psimps[OF dom] M j1v Lgt1 mono t1ne t1v c1v somev True
              par0 Adm0 e11
        by (simp add: Let_def)
    next
      case False
      hence VI: "transCondVI M" using conds by blast
      show ?thesis
        using Trans.psimps[OF dom] M j1v Lgt1 mono t1ne t1v c1v somev False VI
              par0 Adm0 e11
        by (simp add: Let_def)
    qed
    have ufl: "unflatBT (flatBT (Dpt (enat v) (Dpt (enat b) 0\<^sub>B)))
               = Dpt (enat v) (Dpt (enat b) 0\<^sub>B)"
      by (rule unflatBT_flat)
    show ?thesis using trans_val e10 e11 ufl by simp
  qed
qed


text \<open>Parts (2)–(5) of 命題（\<open>2\<close>列ペア数列の基本性質）: the marked-pair
  membership and the \<open>Mark\<close> values.\<close>

lemma m_7_3_twoColumn_Marked:
  assumes M: "M \<in> RT_PS" and mono: "monoT M" and L2: "Lng M = 2"
  shows "(M, 0) \<in> Marked" and "(M, 1) \<in> Marked"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have adm0: "adm M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
  have adm1: "adm M 1"
    by (simp add: adm_def nadm_def nextR_def nextrel1_def L2)
  have le01: "leR M 0 0 1" using mono L2 by (simp add: monoT_def leR_def)
  have le11: "leR M 0 1 1" using L2 by (simp add: leR_def le0_def)
  show "(M, 0) \<in> Marked"
    using MT adm0 le01 L2 by (simp add: Marked_def)
  show "(M, 1) \<in> Marked"
    using MT adm1 le11 L2 by (simp add: Marked_def)
qed

lemma m_7_3_twoColumn_Mark:
  assumes M: "M \<in> RT_PS" and mono: "monoT M" and L2: "Lng M = 2"
  shows "Mark M 0 = Dpt (enat (entry M 1 0)) (Dpt (enat (entry M 1 1)) 0\<^sub>B)"
    and "Mark M 1 = Dpt (enat (entry M 1 1)) 0\<^sub>B"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  define v where "v = entry M 1 0"
  define b where "b = entry M 1 1"
  have hd0: "entry M 0 0 = v"
    using reduced_mono_head_diag[OF M mono] v_def by simp
  have predM: "Pred M = [(v, v)]"
  proof -
    obtain p0 p1 where Mp: "M = [p0, p1]"
      using L2 by (cases M rule: remdups_adj.cases) auto
    have "p0 = (v, v)"
      using hd0 v_def Mp by (cases p0) (simp add: entry_def)
    thus ?thesis using Mp by (simp add: Pred_def)
  qed
  have dom0: "Trans_Mark_dom (Inr (M, 0))" by (rule m_7_3_Mark_welldef[OF M])
  have dom1: "Trans_Mark_dom (Inr (M, 1))" by (rule m_7_3_Mark_welldef[OF M])
  have j1v: "Lng M - 1 = 1" using L2 by simp
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L2 by simp
  have le01: "le0 M 0 1" using mono j1v by (simp add: monoT_def leR_def)
  have nr01: "nextrel0 M 0 1"
    using le0_adjacent_step[of M 0] le01 by simp
  have par0: "parent M 0 1 = 0"
  proof -
    have uniq: "\<And>j. nextR M 0 j 1 \<Longrightarrow> j = 0"
      by (auto simp: nextR_def nextrel0_def)
    have ex1: "\<exists>!j. nextR M 0 j 1"
      using nr01 uniq by (auto simp: nextR_def)
    show ?thesis unfolding parent_def
      using the1_equality[OF ex1] nr01 uniq by (auto simp: nextR_def)
  qed
  have adm0: "adm M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
  have Adm0: "Adm M 0 = 0" using adm0 by (simp add: Adm_def)
  have e10: "entry M 1 0 = v" using v_def by simp
  have e11: "entry M 1 1 = b" using b_def by simp
  show g4: "Mark M 0 = Dpt (enat (entry M 1 0)) (Dpt (enat (entry M 1 1)) 0\<^sub>B)"
  proof (cases "v = 0")
    case True
    have t1z: "Trans (Pred M) = 0\<^sub>B" using predM Trans_singleton True by simp
    have "Mark M 0 = Dpt 0 (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
      using Mark.psimps[OF dom0] M j1v Lgt1 mono t1z by (simp add: Let_def)
    thus ?thesis using True e10 j1v by (simp add: zero_enat_def)
  next
    case False
    have t1v: "Trans (Pred M) = Dpt (enat v) 0\<^sub>B"
      using predM Trans_singleton False by simp
    have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B" using t1v by simp
    have c1v: "Mark (Pred M) 0 = Dpt (enat v) 0\<^sub>B"
      using predM Mark_singleton False by simp
    have pt: "isPTB_str (flatBT (Dpt (enat v) (0\<^sub>B)))"
      by (rule isPTB_str_Dpt) simp_all
    have mb: "(Mark (Pred M) 0, Mark (Pred M) 0) \<in> MarkedB"
      using scb_decomp_self[OF pt] c1v unfolding MarkedB_def by auto
    have somev: "(SOME sb. scb_decomp (Mark (Pred M) 0) (fst sb)
                    (flatBT (Dpt (enat v) 0\<^sub>B)) (snd sb)) = ([], [])"
      using scb_SOME_self[OF pt] c1v by simp
    have conds: "(transCondI M \<or> transCondIII M \<or> transCondV M) \<or> transCondVI M"
    proof (cases "b = 0")
      case True
      thus ?thesis using adm0 par0 j1v e11 by (simp add: transCondI_def)
    next
      case bpos: False
      show ?thesis
      proof (cases "b \<le> v")
        case True
        thus ?thesis using bpos adm0 par0 j1v e10 e11
          by (simp add: transCondIII_def)
      next
        case False
        have vlb: "v < b" using False by simp
        have nr1: "nextrel1 M 0 1"
        proof -
          have valley: "\<And>j. 0 < j \<Longrightarrow> le0 M j 1 \<Longrightarrow> entry M 1 1 \<le> entry M 1 j"
          proof -
            fix j assume j0: "0 < j" and lej: "le0 M j 1"
            have "j < Lng M" using lej by (simp add: le0_def)
            hence "j = 1" using j0 L2 by simp
            thus "entry M 1 1 \<le> entry M 1 j" by simp
          qed
          show ?thesis
            unfolding nextrel1_def
            using L2 e10 e11 vlb le01 valley by auto
        qed
        have hp1: "hasParent M 1 1"
        proof -
          have "\<And>j. nextR M 1 j 1 \<Longrightarrow> j = 0"
            by (auto simp: nextR_def nextrel1_def)
          thus ?thesis using nr1 unfolding hasParent_def nextR_def by auto
        qed
        have par1: "parent M 1 1 = 0"
        proof -
          have uniq: "\<And>j. nextR M 1 j 1 \<Longrightarrow> j = 0"
            by (auto simp: nextR_def nextrel1_def)
          have ex1: "\<exists>!j. nextR M 1 j 1"
            using nr1 uniq by (auto simp: nextR_def)
          show ?thesis unfolding parent_def
            using the1_equality[OF ex1] nr1 uniq by (auto simp: nextR_def)
        qed
        have condA: "RedCondA M"
          using m_6_6_reduced_iff_cond[OF MT] M by auto
        have "entry M 1 (parent M 1 1) + 1 = entry M 1 1"
          using condA[unfolded RedCondA_def, rule_format, of 1 1] hp1 by simp
        hence "v + 1 = b" using par1 e10 e11 by simp
        thus ?thesis using vlb par0 j1v e10 e11
          by (simp add: transCondVI_def)
      qed
    qed
    have mark_val: "Mark M 0 = unflatBT (flatBT (Dpt (enat v) (Dpt (enat b) 0\<^sub>B)))"
    proof (cases "transCondI M \<or> transCondIII M \<or> transCondV M")
      case True
      show ?thesis
        using Mark.psimps[OF dom0] M j1v Lgt1 mono t1ne t1v c1v somev mb True
              par0 Adm0 e11
        by (simp add: Let_def)
    next
      case False
      hence VI: "transCondVI M" using conds by blast
      show ?thesis
        using Mark.psimps[OF dom0] M j1v Lgt1 mono t1ne t1v c1v somev mb False VI
              par0 Adm0 e11
        by (simp add: Let_def)
    qed
    have ufl: "unflatBT (flatBT (Dpt (enat v) (Dpt (enat b) 0\<^sub>B)))
               = Dpt (enat v) (Dpt (enat b) 0\<^sub>B)"
      by (rule unflatBT_flat)
    show ?thesis using mark_val e10 e11 ufl by simp
  qed
  show "Mark M 1 = Dpt (enat (entry M 1 1)) 0\<^sub>B"
  proof (cases "v = 0")
    case True
    have t1z: "Trans (Pred M) = 0\<^sub>B" using predM Trans_singleton True by simp
    show ?thesis
      using Mark.psimps[OF dom1] M j1v Lgt1 mono t1z by (simp add: Let_def)
  next
    case False
    have t1v: "Trans (Pred M) = Dpt (enat v) 0\<^sub>B"
      using predM Trans_singleton False by simp
    have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B" using t1v by simp
    show ?thesis
      using Mark.psimps[OF dom1] M j1v Lgt1 mono t1ne by (simp add: Let_def)
  qed
qed


section \<open>§7.3 命題（\<open>Trans\<close>の\<open>(IncrFirst,Red)\<close>不変性） — A4-corrected domain\<close>

text \<open>\<open>Trans M = Trans (Red M)\<close> and \<open>Trans (IncrFirst M) = Trans M\<close> on the
  domain \<open>Red M \<in> RT\<^sub>PS\<close> (the article states them on all of \<open>T\<^sub>PS\<close>, but the
  (D) recursion only reaches a defined value when \<open>Red M\<close> is reduced —
  the same A4 idempotency caveat as the well-definedness).  The \<open>IncrFirst\<close>
  invariance is immediate from the \<open>Red\<close> one via
  @{thm [source] m_6_5_Red_IncrFirst}.\<close>

lemma m_7_3_Trans_Red:
  assumes RR: "Red M \<in> RT_PS"
  shows "Trans M = Trans (Red M)"
proof (cases "M \<in> RT_PS")
  case True
  hence "Red M = M" by (simp add: RT_PS_def)
  thus ?thesis by simp
next
  case False
  have domR: "Trans_Mark_dom (Inl (Red M))" by (rule m_7_3_Trans_welldef[OF RR])
  have domM: "Trans_Mark_dom (Inl M)"
    by (rule Trans_Mark.domintros(1)) (use False domR in \<open>simp_all\<close>)
  show ?thesis using Trans.psimps[OF domM] False by simp
qed

lemma m_7_3_Mark_Red:
  assumes RR: "Red M \<in> RT_PS"
  shows "Mark M m = Mark (Red M) m"
proof (cases "M \<in> RT_PS")
  case True
  hence "Red M = M" by (simp add: RT_PS_def)
  thus ?thesis by simp
next
  case False
  have domR: "Trans_Mark_dom (Inr (Red M, m))" by (rule m_7_3_Mark_welldef[OF RR])
  have domM: "Trans_Mark_dom (Inr (M, m))"
    by (rule Trans_Mark.domintros(2)) (use False domR in \<open>simp_all\<close>)
  show ?thesis using Mark.psimps[OF domM] False by simp
qed

lemma m_7_3_Trans_IncrFirst:
  assumes MT: "M \<in> T_PS" and RR: "Red M \<in> RT_PS"
  shows "Trans (IncrFirst M) = Trans M"
proof -
  have RI: "Red (IncrFirst M) = Red M" by (rule m_6_5_Red_IncrFirst[OF MT])
  have RRI: "Red (IncrFirst M) \<in> RT_PS" using RI RR by simp
  have "Trans (IncrFirst M) = Trans (Red (IncrFirst M))"
    by (rule m_7_3_Trans_Red[OF RRI])
  also have "\<dots> = Trans (Red M)" using RI by simp
  also have "\<dots> = Trans M" by (rule m_7_3_Trans_Red[OF RR, symmetric])
  finally show ?thesis .
qed

lemma m_7_3_Mark_IncrFirst:
  assumes MT: "M \<in> T_PS" and RR: "Red M \<in> RT_PS"
  shows "Mark (IncrFirst M) m = Mark M m"
proof -
  have RI: "Red (IncrFirst M) = Red M" by (rule m_6_5_Red_IncrFirst[OF MT])
  have RRI: "Red (IncrFirst M) \<in> RT_PS" using RI RR by simp
  have "Mark (IncrFirst M) m = Mark (Red (IncrFirst M)) m"
    by (rule m_7_3_Mark_Red[OF RRI])
  also have "\<dots> = Mark (Red M) m" using RI by simp
  also have "\<dots> = Mark M m" by (rule m_7_3_Mark_Red[OF RR, symmetric])
  finally show ?thesis .
qed


section \<open>§7.3 value-invariant prerequisite: the scb image-existence lemma,
  brick 1 (balance pinning)\<close>

text \<open>A balanced (well-formed) prefix with an all-\<open>RP\<close> remainder exhausts the
  string: from @{thm [source] m_7_1_paren_balance} the \<open>(\<close>/\<open>)\<close> counts of both
  \<open>flat t\<close> and \<open>flat c\<close> agree, so the all-\<open>RP\<close> remainder has length 0.
  (Pins the \<open>s = []\<close> occurrence of the image lemma to the whole term.)\<close>

lemma scbimg_prefix_whole:
  assumes tT: "t \<in> T_B" and cT: "c \<in> T_B"
    and eq: "flatBT t = flatBT c @ b"
    and rb: "\<forall>x \<in> set b. x = RP"
  shows "b = []"
proof -
  have bt: "length (filter (\<lambda>x. x = LP) (flatBT t))
            = length (filter (\<lambda>x. x = RP) (flatBT t))"
    by (rule m_7_1_paren_balance[OF tT])
  have bc: "length (filter (\<lambda>x. x = LP) (flatBT c))
            = length (filter (\<lambda>x. x = RP) (flatBT c))"
    by (rule m_7_1_paren_balance[OF cT])
  have lb: "length (filter (\<lambda>x. x = LP) b) = 0"
    using rb by (auto simp: filter_empty_conv)
  have rbn: "length (filter (\<lambda>x. x = RP) b) = length b"
    using rb by (induction b) auto
  show ?thesis using bt bc lb rbn by (simp add: eq)
qed


text \<open>Brick 2: descent through a principal head — a non-initial occurrence in
  \<open>flat (Trm [DB v u]) = Dsym v # flat u\<close> lies in the body \<open>u\<close>.\<close>

lemma scbimg_principal_descend:
  assumes eq: "flatBT (Trm [DB v u]) = s @ fc @ b" and sne: "s \<noteq> []"
  shows "\<exists>s'. s = Dsym v # s' \<and> flatBT u = s' @ fc @ b"
proof -
  have "Dsym v # flatBT u = s @ fc @ b" using eq by simp
  thus ?thesis using sne by (cases s) auto
qed


text \<open>Brick 3 (the join sweep): in a \<open>CM\<close>-joined component list closed by the
  outer \<open>RP\<close>, an occurrence of a principal string \<open>flatBP cp\<close> with all-\<open>RP\<close>
  tail \<open>b\<close> lies inside a single component, and only the LAST one — crossing a
  component boundary would give the occurrence a proper prefix of negative
  \<open>flatinj_dsum\<close> (the component suffix), contradicting
  @{thm [source] flatinj_prefix_nonneg_BP}.  The component is then replaced
  via the supplied (inductive) replacement hypothesis.\<close>

lemma scbimg_join:
  assumes IHr: "\<And>r s b. r \<in> set rs \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                  \<Longrightarrow> \<forall>x \<in> set b. x = RP
                  \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b"
    and eq: "concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = s @ flatBP cp @ b"
    and rb: "\<forall>x \<in> set b. x = RP"
  shows "\<exists>rs'. length rs' = length rs
             \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = s @ flatBP cp' @ b"
  using IHr eq rb
proof (induction rs arbitrary: s b)
  case Nil
  \<comment> \<open>\<open>[RP] = s @ flatBP cp @ b\<close>: but \<open>flatBP cp\<close> starts with \<open>Dsym\<close>.\<close>
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?case
    using Nil.prems(2) cpw by (cases s) auto
next
  case (Cons r0 rs)
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  have fchd: "flatBP cp = Dsym w # flatBT cb" using cpw by simp
  \<comment> \<open>peel the leading \<open>CM\<close>\<close>
  have eq0: "CM # flatBP r0 @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
             = s @ flatBP cp @ b"
    using Cons.prems(2) by simp
  have sne: "s \<noteq> []"
  proof
    assume "s = []"
    hence "CM = Dsym w" using eq0 fchd by simp
    thus False by simp
  qed
  then obtain s1 where ss: "s = CM # s1"
    using eq0 by (cases s) auto
  have eq1: "flatBP r0 @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
             = s1 @ flatBP cp @ b"
    using eq0 ss by simp
  \<comment> \<open>split at the end of \<open>flatBP r0\<close>\<close>
  from append_eq_append_conv2[THEN iffD1, OF eq1]
  obtain us where split:
      "flatBP r0 = s1 @ us \<and> us @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = flatBP cp @ b
     \<or> flatBP r0 @ us = s1 \<and> concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = us @ flatBP cp @ b" by blast
  show ?case
  proof (cases "flatBP r0 @ us = s1 \<and> concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = us @ flatBP cp @ b")
    case True
    \<comment> \<open>occurrence beyond \<open>r0\<close>: recurse into the tail join\<close>
    have IHtail: "\<And>r s b. r \<in> set rs \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                    \<Longrightarrow> \<forall>x \<in> set b. x = RP
                    \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b"
    proof -
      fix r s b
      assume "r \<in> set rs" "flatBP r = s @ flatBP cp @ b" "\<forall>x \<in> set b. x = RP"
      thus "\<exists>r'. flatBP r' = s @ flatBP cp' @ b"
        using Cons.prems(1)[of r s b] by simp
    qed
    have tail: "concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = us @ flatBP cp @ b"
      using True by simp
    have "\<exists>rs'. length rs' = length rs
              \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b"
      by (rule Cons.IH[OF IHtail tail Cons.prems(3)])
    then obtain rs' where rs': "length rs' = length rs"
        "concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b" by blast
    have "concat (map (\<lambda>r. CM # flatBP r) (r0 # rs')) @ [RP]
          = CM # flatBP r0 @ us @ flatBP cp' @ b" using rs' by simp
    also have "\<dots> = s @ flatBP cp' @ b" using ss True by simp
    finally show ?thesis using rs' by (intro exI[of _ "r0 # rs'"]) simp
  next
    case False
    with split have inr0: "flatBP r0 = s1 @ us"
        and rest: "us @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = flatBP cp @ b"
      by auto
    \<comment> \<open>split \<open>fc\<close> against \<open>us\<close>\<close>
    from append_eq_append_conv2[THEN iffD1, OF rest[symmetric]]
    obtain vs where split2:
        "flatBP cp = us @ vs \<and> vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
       \<or> flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
      by blast
    show ?thesis
    proof (cases "flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]")
      case True
      \<comment> \<open>occurrence wholly inside \<open>r0\<close>: tail of \<open>b\<close> forces \<open>rs = []\<close>\<close>
      have ball: "\<forall>x \<in> set (vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]). x = RP"
        using True Cons.prems(3) by simp
      have rsnil: "rs = []"
      proof (cases rs)
        case (Cons r1 rs1)
        hence "CM \<in> set (concat (map (\<lambda>r. CM # flatBP r) rs))" by simp
        thus ?thesis using ball by auto
      qed simp
      have vsRP: "\<forall>x \<in> set vs. x = RP" using ball by auto
      have r0eq: "flatBP r0 = s1 @ flatBP cp @ vs" using inr0 True by simp
      obtain r0' where r0': "flatBP r0' = s1 @ flatBP cp' @ vs"
        using Cons.prems(1)[of r0 s1 vs] r0eq vsRP by auto
      have "concat (map (\<lambda>r. CM # flatBP r) [r0']) @ [RP]
            = CM # s1 @ flatBP cp' @ vs @ [RP]" using r0' by simp
      also have "\<dots> = s @ flatBP cp' @ b" using ss True rsnil by simp
      finally show ?thesis using rsnil by (intro exI[of _ "[r0']"]) simp
    next
      case False
      with split2 have fcsplit: "flatBP cp = us @ vs"
          and vsb: "vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]" by auto
      \<comment> \<open>crossing: \<open>us\<close> is a PROPER suffix-piece of \<open>r0\<close> and a proper prefix of
          \<open>fc\<close> with negative depth-sum — contradiction\<close>
      have vsne: "vs \<noteq> []"
      proof
        assume v0: "vs = []"
        hence "flatBP cp = us" using fcsplit by simp
        hence "b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]" using vsb v0 by simp
        \<comment> \<open>then the whole tail join is in \<open>b\<close>: \<open>rs = []\<close> as above, so
            \<open>flatBP r0 = s1 @ flatBP cp\<close> with \<open>vs = []\<close> — covered by the
            inside-\<open>r0\<close> case, contradicting \<open>False\<close>\<close>
        hence "flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
          using fcsplit v0 vsb by simp
        thus False using False by simp
      qed
      have usne_or: "us = [] \<or> us \<noteq> []" by simp
      show ?thesis
      proof (cases "us = []")
        case True
        \<comment> \<open>\<open>fc = vs\<close> begins exactly at the tail join, whose head is \<open>CM\<close> or \<open>RP\<close>\<close>
        have "flatBP cp = vs" using fcsplit True by simp
        hence hd: "hd (vs @ b) = Dsym w" using fchd vsne by (cases vs) auto
        have "hd (concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]) = CM
              \<or> hd (concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]) = RP"
          by (cases rs) auto
        thus ?thesis using vsb hd by auto
      next
        case False
        have dsus_neg: "flatinj_dsum us < 0"
        proof -
          have "flatinj_dsum (flatBP r0) = -1"
            by (rule flatinj_dsum_flatBP)
          moreover have "0 \<le> flatinj_dsum s1"
            using flatinj_prefix_nonneg_BP[OF inr0] False by simp
          moreover have "flatinj_dsum (flatBP r0) = flatinj_dsum s1 + flatinj_dsum us"
            using inr0 by simp
          ultimately show ?thesis by simp
        qed
        have "0 \<le> flatinj_dsum us"
          using flatinj_prefix_nonneg_BP[OF fcsplit] vsne by simp
        thus ?thesis using dsus_neg by simp
      qed
    qed
  qed
qed


text \<open>The image-existence lemma (§7.3 value-invariant prerequisite): replacing
  the principal middle of an scb-style split (all-\<open>RP\<close> tail) by any other
  principal string stays inside the image of \<open>flatBT\<close>.  Empirically 0/7,224
  (python/scb_image_audit.py).\<close>

lemma scbimg_image_BT:
  "flatBT t = s @ flatBP cp @ b \<Longrightarrow> \<forall>x \<in> set b. x = RP
   \<Longrightarrow> \<exists>t'. flatBT t' = s @ flatBP cp' @ b"
  and scbimg_image_BP:
  "flatBP p = s @ flatBP cp @ b \<Longrightarrow> \<forall>x \<in> set b. x = RP
   \<Longrightarrow> \<exists>p'. flatBP p' = s @ flatBP cp' @ b"
proof (induct t and p arbitrary: s b and s b rule: flatBT_flatBP.induct)
  case (1 s b)
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?case using 1(1) cpw by (cases s) auto
next
  case (2 p s b)
  have "flatBP p = s @ flatBP cp @ b" using 2(2) by simp
  then obtain p' where "flatBP p' = s @ flatBP cp' @ b"
    using 2(1) 2(3) by blast
  thus ?case by (intro exI[of _ "Trm [p']"]) simp
next
  case (3 p q ps s b)
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  have fchd: "flatBP cp = Dsym w # flatBT cb" using cpw by simp
  let ?JOIN = "concat (map (\<lambda>r. CM # flatBP r) (q # ps))"
  have flat3: "flatBT (Trm (p # q # ps)) = LP # (flatBP p @ ?JOIN) @ [RP]" by simp
  have sne: "s \<noteq> []"
  proof
    assume "s = []"
    hence "LP = Dsym w" using 3(3) fchd flat3 by simp
    thus False by simp
  qed
  then obtain s1 where ss: "s = LP # s1" using 3(3) flat3 by (cases s) auto
  have eq1: "flatBP p @ ?JOIN @ [RP] = s1 @ flatBP cp @ b"
    using 3(3) flat3 ss by simp
  from append_eq_append_conv2[THEN iffD1, OF eq1]
  obtain us where split:
      "flatBP p = s1 @ us \<and> us @ ?JOIN @ [RP] = flatBP cp @ b
     \<or> flatBP p @ us = s1 \<and> ?JOIN @ [RP] = us @ flatBP cp @ b" by blast
  show ?case
  proof (cases "flatBP p @ us = s1 \<and> ?JOIN @ [RP] = us @ flatBP cp @ b")
    case True
    \<comment> \<open>occurrence in the join: brick 3\<close>
    have IHr: "\<And>r s b. r \<in> set (q # ps) \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                 \<Longrightarrow> \<forall>x \<in> set b. x = RP
                 \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b"
    proof -
      fix r s b
      assume rin: "r \<in> set (q # ps)" and req: "flatBP r = s @ flatBP cp @ b"
        and rrb: "\<forall>x \<in> set b. x = RP"
      show "\<exists>r'. flatBP r' = s @ flatBP cp' @ b"
        using 3(2) rin req rrb by blast
    qed
    have "\<exists>rs'. length rs' = length (q # ps)
              \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b"
    proof (rule scbimg_join[where cp = cp])
      fix r s b
      assume "r \<in> set (q # ps)" "flatBP r = s @ flatBP cp @ b"
        "\<forall>x \<in> set b. x = RP"
      thus "\<exists>r'. flatBP r' = s @ flatBP cp' @ b" by (rule IHr)
    next
      show "concat (map (\<lambda>r. CM # flatBP r) (q # ps)) @ [RP]
            = us @ flatBP cp @ b" using True by simp
    next
      show "\<forall>x \<in> set b. x = RP" by (rule 3(4))
    qed
    then obtain rs' where rs': "length rs' = length (q # ps)"
        "concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b"
      by blast
    obtain r1' rest' where rsc: "rs' = r1' # rest'"
      using rs' by (cases rs') auto
    have "flatBT (Trm (p # r1' # rest'))
          = LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) rs')) @ [RP]"
      using rsc by simp
    also have "\<dots> = LP # flatBP p @ (concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP])"
      by simp
    also have "\<dots> = LP # flatBP p @ us @ flatBP cp' @ b" using rs'(2) by simp
    also have "\<dots> = s @ flatBP cp' @ b" using ss True by simp
    finally show ?thesis by blast
  next
    case False
    with split have inp: "flatBP p = s1 @ us"
        and rest: "us @ ?JOIN @ [RP] = flatBP cp @ b" by auto
    \<comment> \<open>occurrence (purportedly) inside the FIRST component: impossible\<close>
    from append_eq_append_conv2[THEN iffD1, OF rest]
    obtain vs where split2:
        "us = flatBP cp @ vs \<and> vs @ ?JOIN @ [RP] = b
       \<or> us @ vs = flatBP cp \<and> ?JOIN @ [RP] = vs @ b" by blast
    have False
    proof (cases "us = flatBP cp @ vs \<and> vs @ ?JOIN @ [RP] = b")
      case True
      hence "CM \<in> set b" by auto
      thus False using 3(4) by auto
    next
      case False
      with split2 have fcsplit: "us @ vs = flatBP cp"
          and jrest: "?JOIN @ [RP] = vs @ b" by auto
      show False
      proof (cases "us = []")
        case True
        hence "vs = flatBP cp" using fcsplit by simp
        hence hdD: "hd (vs @ b) = Dsym w" using fchd by simp
        have "vs @ b = CM # flatBP q @ concat (map (\<lambda>r. CM # flatBP r) ps) @ [RP]"
          using jrest by simp
        hence "hd (vs @ b) = CM" by simp
        thus False using hdD by simp
      next
        case usne: False
        have vsne: "vs \<noteq> []"
        proof
          assume v0: "vs = []"
          hence "?JOIN @ [RP] = b" using jrest by simp
          hence "CM \<in> set b" by auto
          thus False using 3(4) by auto
        qed
        have "flatinj_dsum us < 0"
        proof -
          have "flatinj_dsum (flatBP p) = -1" by (rule flatinj_dsum_flatBP)
          moreover have "0 \<le> flatinj_dsum s1"
            using flatinj_prefix_nonneg_BP[OF inp usne] .
          moreover have "flatinj_dsum (flatBP p) = flatinj_dsum s1 + flatinj_dsum us"
            using inp by simp
          ultimately show ?thesis by simp
        qed
        moreover have "0 \<le> flatinj_dsum us"
          using flatinj_prefix_nonneg_BP[OF fcsplit[symmetric] vsne] .
        ultimately show False by simp
      qed
    qed
    thus ?thesis ..
  qed
next
  case (4 u a s b)
  show ?case
  proof (cases "s = []")
    case True
    have "flatBP (DB u a) @ [] = flatBP cp @ b" using 4(2) True by simp
    hence "flatBP (DB u a) = flatBP cp \<and> [] = b"
      using flatinj_flatBP_cancel by blast
    thus ?thesis using True by (intro exI[of _ cp']) simp
  next
    case False
    have "Dsym u # flatBT a = s @ flatBP cp @ b" using 4(2) by simp
    then obtain s1 where ss: "s = Dsym u # s1" and aeq: "flatBT a = s1 @ flatBP cp @ b"
      using False by (cases s) auto
    obtain a' where "flatBT a' = s1 @ flatBP cp' @ b"
      using 4(1)[OF aeq 4(3)] by blast
    thus ?thesis using ss by (intro exI[of _ "DB u a'"]) simp
  qed
qed


text \<open>The corrected scb replacement (A12, now with the image hypothesis
  DISCHARGED by @{thm [source] scbimg_image_BT}): replacing the principal
  middle of an scb-decomposition yields a term with the corresponding
  scb-decomposition.\<close>

lemma scb_replace_principal:
  assumes d: "scb_decomp t s (flatBT (Trm [cp])) b"
    and pc': "isPTB_str (flatBT (Trm [cp']))"
  shows "\<exists>t'. flatBT t' = s @ flatBT (Trm [cp']) @ b
            \<and> scb_decomp t' s (flatBT (Trm [cp'])) b"
proof -
  from d have eq: "flatBT t = s @ flatBP cp @ b"
    and rb: "\<forall>x \<in> set b. x = RP"
    by (auto simp: scb_decomp_def)
  obtain t' where t': "flatBT t' = s @ flatBP cp' @ b"
    using scbimg_image_BT[OF eq rb] by blast
  have "scb_decomp t' s (flatBT (Trm [cp'])) b"
    unfolding scb_decomp_def using t' pc' rb by simp
  thus ?thesis using t' by auto
qed

text \<open>\<open>dfree\<close> reads off the flat string: no \<open>Dsym \<infinity>\<close> letters.  Transfers
  \<open>T\<^sub>B\<close>-membership to terms built by string surgery.\<close>

lemma dfree_flat_BT: "dfree_BT t \<longleftrightarrow> (\<forall>v. Dsym v \<in> set (flatBT t) \<longrightarrow> v \<noteq> \<infinity>)"
  and dfree_flat_BP: "dfree_BP p \<longleftrightarrow> (\<forall>v. Dsym v \<in> set (flatBP p) \<longrightarrow> v \<noteq> \<infinity>)"
proof (induct t and p rule: flatBT_flatBP.induct)
  case 1 show ?case by simp
next
  case (2 p) thus ?case by simp
next
  case (3 p q ps)
  have "dfree_BT (Trm (p # q # ps))
        \<longleftrightarrow> (dfree_BP p \<and> (\<forall>r \<in> set (q # ps). dfree_BP r))" by simp
  also have "\<dots> \<longleftrightarrow> ((\<forall>v. Dsym v \<in> set (flatBP p) \<longrightarrow> v \<noteq> \<infinity>)
        \<and> (\<forall>r \<in> set (q # ps). \<forall>v. Dsym v \<in> set (flatBP r) \<longrightarrow> v \<noteq> \<infinity>))"
    using 3(1) 3(2) by blast
  also have "\<dots> \<longleftrightarrow> (\<forall>v. Dsym v \<in> set (flatBT (Trm (p # q # ps))) \<longrightarrow> v \<noteq> \<infinity>)"
  proof -
    have sf: "set (flatBT (Trm (p # q # ps)))
          = {LP, RP} \<union> set (flatBP p)
            \<union> (\<Union>r \<in> set (q # ps). insert CM (set (flatBP r)))"
      by auto
    show ?thesis unfolding sf by auto
  qed
  finally show ?case .
next
  case (4 u a) thus ?case by auto
qed


text \<open>Marked-pair bookkeeping for the \<open>Trans\<close>/\<open>Mark\<close> value invariant: the
  recursion's \<open>Mark (Pred M) \<dots>\<close> calls stay inside \<open>Marked\<close>.  Empirically
  0/1,575 and 0/2,313 (anchor: ancestor-interval property
  @{thm [source] m_5_1_ancestor_tree_1} + verbatim prefix transfer
  @{thm [source] le0_prefix_agree} / @{thm [source] nextR1_pred_agree}).\<close>

lemma adm_Pred_transfer:
  assumes L: "1 < Lng M" and mlt: "m < Lng M - 1" and a: "adm M m"
  shows "adm (Pred M) m"
proof -
  have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using pb by simp
  show ?thesis
  proof (cases "m + 1 < Lng M - 1")
    case True
    have "\<not> nadm (Pred M) m"
    proof
      assume n: "nadm (Pred M) m"
      have "\<not> m > Lng (Pred M)" using mlt LP by simp
      hence pair: "nextR (Pred M) 1 (m - 1) m \<and> nextR (Pred M) 1 m (m + 1)"
        using n by (simp add: nadm_def)
      have b1: "m - 1 \<le> Lng M - 2" and b2: "m \<le> Lng M - 2"
        and b3: "m + 1 \<le> Lng M - 2" using True by simp_all
      have "nextR M 1 (m - 1) m \<and> nextR M 1 m (m + 1)"
        using pair nextR1_pred_agree[OF L b1 b2] nextR1_pred_agree[OF L b2 b3]
        by simp
      hence "nadm M m" by (simp add: nadm_def)
      thus False using a by (simp add: adm_def)
    qed
    thus ?thesis by (simp add: adm_def)
  next
    case False
    \<comment> \<open>\<open>m + 1 \<ge> Lng (Pred M)\<close>: the second \<open>nextR\<close> of \<open>nadm\<close> is out of range\<close>
    have "\<not> nextR (Pred M) 1 m (m + 1)"
      using False LP by (auto simp: nextR_def nextrel1_def)
    hence "\<not> nadm (Pred M) m" using mlt LP by (auto simp: nadm_def)
    thus ?thesis by (simp add: adm_def)
  qed
qed

lemma Marked_Pred:
  assumes MT: "M \<in> T_PS" and L: "1 < Lng M"
    and mM: "(M, m) \<in> Marked" and mlt: "m < Lng M - 1"
  shows "(Pred M, m) \<in> Marked"
proof -
  from mM have admM: "adm M m" and leM: "leR M 0 m (Lng M - 1)"
    by (auto simp: Marked_def)
  have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using pb by simp
  have PT: "Pred M \<in> T_PS"
  proof -
    have "0 < Lng (Pred M)" using LP L by simp
    thus ?thesis using length_greater_0_conv by (fastforce simp: T_PS_def)
  qed
  have le2: "leR M 0 m (Lng M - 2)"
    by (rule m_5_1_ancestor_tree_1[OF MT leM]) (use mlt in linarith)+
  have leP: "le0 (Pred M) m (Lng M - 2)"
  proof (rule le0_prefix_agree[of "Lng M - 2" M "Pred M"])
    show "\<And>j. j \<le> Lng M - 2 \<Longrightarrow> M ! j = Pred M ! j"
      using pb L by (simp add: nth_butlast)
    show "Lng M - 2 < Lng M" using L by linarith
    show "Lng M - 2 < Lng (Pred M)" using LP L by linarith
    show "m \<le> Lng M - 2" using mlt by linarith
    show "Lng M - 2 \<le> Lng M - 2" by simp
    show "le0 M m (Lng M - 2)" using le2 by (simp add: leR_def)
  qed
  have admP: "adm (Pred M) m" by (rule adm_Pred_transfer[OF L mlt admM])
  show ?thesis using PT admP leP LP
    by (simp add: Marked_def leR_def numeral_2_eq_2)
qed

lemma Marked_Pred_Adm:
  assumes MT: "M \<in> T_PS" and L: "1 < Lng M"
    and hp: "hasParent M 0 (Lng M - 1)"
  shows "(Pred M, Adm M (parent M 0 (Lng M - 1))) \<in> Marked"
proof -
  let ?j1 = "Lng M - 1"  let ?jp = "parent M 0 ?j1"  let ?a = "Adm M ?jp"
  have parR: "nextR M 0 ?jp ?j1"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have jplt: "?jp < ?j1" using parR by (simp add: nextR_def nextrel0_def)
  have jpb: "?jp \<le> Lng M - 1" using jplt by simp
  have admA: "adm M ?a" by (rule adm_Adm_adm)
  have aLe: "?a \<le> ?jp" by (rule adm_Adm_le)
  have alt: "?a < ?j1" using aLe jplt by linarith
  \<comment> \<open>row-1 ancestry to \<open>?jp\<close>, then the row-0 parent step to \<open>?j1\<close>\<close>
  have le1a: "leR M 1 ?a ?jp" by (rule adm_row1_ancestry[OF MT jpb])
  have le0a: "leR M 0 ?a ?jp" by (rule m_le1_imp_le0[OF le1a])
  have "le0 M ?a ?j1"
  proof -
    have st: "nextrel0 M ?jp ?j1" using parR by (simp add: nextR_def)
    have "(nextrel0 M)\<^sup>*\<^sup>* ?a ?jp" using le0a by (simp add: leR_def le0_def)
    hence "(nextrel0 M)\<^sup>*\<^sup>* ?a ?j1" using st by (rule rtranclp.rtrancl_into_rtrancl)
    moreover have "?a < Lng M" using alt by linarith
    moreover have "?j1 < Lng M" using L by linarith
    ultimately show ?thesis by (simp add: le0_def)
  qed
  hence leMa: "leR M 0 ?a ?j1" by (simp add: leR_def)
  show ?thesis
    by (rule Marked_Pred[OF MT L _ alt])
       (use MT admA leMa in \<open>simp add: Marked_def\<close>)
qed


text \<open>Marked bookkeeping for the (C) multiT branch: a marked column of a multi
  \<open>M\<close> lies in the LAST \<open>P\<close>-component (directly from \<open>Pcut\<close> being the LEAST
  anchored cut), and restricts to a marked column of it.
  Empirically 0/6,080.\<close>

lemma multi_Marked_last_component:
  assumes MT: "M \<in> T_PS" and mu: "multiT M"
    and mM: "(M, m) \<in> Marked"
  shows "Pcut M \<le> m" and "(drop (Pcut M) M, m - Pcut M) \<in> Marked"
proof -
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  from mM have admM: "adm M m" and leM: "leR M 0 m (Lng M - 1)"
    by (auto simp: Marked_def)
  have mlt: "m < Lng M" using leM by (simp add: leR_def le0_def)
  have m0: "0 < m"
  proof (rule ccontr)
    assume "\<not> 0 < m"
    hence "leR M 0 0 (Lng M - 1)" using leM by simp
    thus False using m_6_2_not_multi_iff_le[OF MT] mu by simp
  qed
  show cut: "Pcut M \<le> m"
    unfolding Pcut_def
    by (rule Least_le) (use m0 mlt leM in linarith)
  \<comment> \<open>now the component view\<close>
  let ?j0 = "Pcut M"  let ?j1 = "Lng M - 1"  let ?K = "drop ?j0 M"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have L0: "0 < Lng M" using L by linarith
  have segK: "?K = seg M ?j0 ?j1" using seg_to_last_eq_drop[OF L0] by simp
  have cb: "0 < ?j0 \<and> ?j0 \<le> ?j1" using Pcut_le[OF L] by simp
  have j1lt: "?j1 < Lng M" using L by simp
  have LK: "Lng ?K = Lng M - ?j0" by simp
  have KT: "?K \<in> T_PS"
  proof -
    have "0 < Lng ?K" using LK cb L by linarith
    thus ?thesis using length_greater_0_conv by (fastforce simp: T_PS_def)
  qed
  \<comment> \<open>le0 restricts to the component window\<close>
  have leK: "le0 ?K (m - ?j0) (Lng ?K - 1)"
  proof -
    have b1: "m - ?j0 \<le> ?j1 - ?j0" using mlt by linarith
    have b2: "?j1 - ?j0 \<le> ?j1 - ?j0" by simp
    have "le0 (seg M ?j0 ?j1) (m - ?j0) (?j1 - ?j0)
          \<longleftrightarrow> le0 M (?j0 + (m - ?j0)) (?j0 + (?j1 - ?j0))"
      by (rule adm_le0_seg[OF j1lt b1 b2]) (use cb in linarith)
    moreover have "?j0 + (m - ?j0) = m" using cut by simp
    moreover have "?j0 + (?j1 - ?j0) = ?j1" using cb by linarith
    ultimately have "le0 (seg M ?j0 ?j1) (m - ?j0) (?j1 - ?j0)"
      using leM by (simp add: leR_def)
    moreover have "Lng ?K - 1 = ?j1 - ?j0" using LK cb by linarith
    ultimately show ?thesis using segK by simp
  qed
  \<comment> \<open>admissibility restricts (last component: the right edges align)\<close>
  have admK: "adm ?K (m - ?j0)"
  proof -
    have "\<not> nadm ?K (m - ?j0)"
    proof
      assume n: "nadm ?K (m - ?j0)"
      have mb: "m - ?j0 \<le> Lng ?K" using LK mlt by linarith
      hence pair: "nextR ?K 1 (m - ?j0 - 1) (m - ?j0)
                 \<and> nextR ?K 1 (m - ?j0) (m - ?j0 + 1)"
        using n by (simp add: nadm_def)
      have r2: "nextrel1 ?K (m - ?j0) (m - ?j0 + 1)"
        using pair by (simp add: nextR_def)
      have ub: "m - ?j0 + 1 < Lng ?K" using r2 by (simp add: nextrel1_def)
      have b0: "m - ?j0 - 1 < Lng (seg M ?j0 ?j1)"
        and b1: "m - ?j0 < Lng (seg M ?j0 ?j1)"
        and b2: "m - ?j0 + 1 < Lng (seg M ?j0 ?j1)"
        using ub segK by simp_all
      have t1: "nextrel1 M (?j0 + (m - ?j0 - 1)) (?j0 + (m - ?j0))"
        using pair adm_nextrel1_seg[OF j1lt b0 b1] segK by (simp add: nextR_def)
      have t2: "nextrel1 M (?j0 + (m - ?j0)) (?j0 + (m - ?j0 + 1))"
        using r2 adm_nextrel1_seg[OF j1lt b1 b2] segK by simp
      have e1: "?j0 + (m - ?j0) = m" using cut by simp
      have "nextrel1 M (m - 1) m"
      proof (cases "m - ?j0 = 0")
        case True
        \<comment> \<open>then \<open>t1\<close> is \<open>nextrel1 M m m\<close>, impossible\<close>
        have "nextrel1 M m m" using t1 True e1 by simp
        thus ?thesis by (simp add: nextrel1_def)
      next
        case False
        have "?j0 + (m - ?j0 - 1) = m - 1" using cut False by linarith
        thus ?thesis using t1 e1 by simp
      qed
      moreover have "nextrel1 M m (m + 1)" using t2 e1 cut by simp
      ultimately have "nadm M m" by (simp add: nadm_def nextR_def)
      thus False using admM by (simp add: adm_def)
    qed
    thus ?thesis by (simp add: adm_def)
  qed
  show "(?K, m - ?j0) \<in> Marked"
    using KT admK leK by (simp add: Marked_def leR_def)
qed


text \<open>\<open>MarkedB\<close> depends only on the LAST principal component: the all-\<open>RP\<close>
  tail pins the marked occurrence into the last component (the
  @{thm [source] scbimg_join} crossing analysis, as an extractor), and a
  component-level occurrence lifts into any term sharing that last component
  (in particular across \<open>+\<^sub>B\<close>: the (C) branch of the \<open>Trans\<close>/\<open>Mark\<close>
  invariant).\<close>

lemma scbext_join:
  assumes eq: "concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = s @ flatBP cp @ b"
    and rb: "\<forall>x \<in> set b. x = RP"
  shows "\<exists>sc bc. flatBP (last rs) = sc @ flatBP cp @ bc \<and> (\<forall>x \<in> set bc. x = RP)"
  using eq rb
proof (induction rs arbitrary: s b)
  case Nil
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?case using Nil.prems(1) cpw by (cases s) auto
next
  case (Cons r0 rs)
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  have fchd: "flatBP cp = Dsym w # flatBT cb" using cpw by simp
  have eq0: "CM # flatBP r0 @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
             = s @ flatBP cp @ b"
    using Cons.prems(1) by simp
  have sne: "s \<noteq> []"
  proof
    assume "s = []"
    hence "CM = Dsym w" using eq0 fchd by simp
    thus False by simp
  qed
  then obtain s1 where ss: "s = CM # s1" using eq0 by (cases s) auto
  have eq1: "flatBP r0 @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
             = s1 @ flatBP cp @ b"
    using eq0 ss by simp
  from append_eq_append_conv2[THEN iffD1, OF eq1]
  obtain us where split:
      "flatBP r0 = s1 @ us \<and> us @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = flatBP cp @ b
     \<or> flatBP r0 @ us = s1 \<and> concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = us @ flatBP cp @ b" by blast
  show ?case
  proof (cases "flatBP r0 @ us = s1 \<and> concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = us @ flatBP cp @ b")
    case True
    have rsne: "rs \<noteq> []"
    proof
      assume "rs = []"
      hence "[RP] = us @ flatBP cp @ b" using True by simp
      thus False using fchd by (cases us) auto
    qed
    have "\<exists>sc bc. flatBP (last rs) = sc @ flatBP cp @ bc \<and> (\<forall>x \<in> set bc. x = RP)"
      using Cons.IH True Cons.prems(2) by blast
    thus ?thesis using rsne by simp
  next
    case False
    with split have inr0: "flatBP r0 = s1 @ us"
        and rest: "us @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = flatBP cp @ b" by auto
    from append_eq_append_conv2[THEN iffD1, OF rest[symmetric]]
    obtain vs where split2:
        "flatBP cp = us @ vs \<and> vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
       \<or> flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
      by blast
    show ?thesis
    proof (cases "flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]")
      case True
      have ball: "\<forall>x \<in> set (vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]). x = RP"
        using True Cons.prems(2) by simp
      have rsnil: "rs = []"
      proof (cases rs)
        case (Cons r1 rs1)
        hence "CM \<in> set (concat (map (\<lambda>r. CM # flatBP r) rs))" by simp
        thus ?thesis using ball by auto
      qed simp
      have vsRP: "\<forall>x \<in> set vs. x = RP" using ball by auto
      have "flatBP r0 = s1 @ flatBP cp @ vs" using inr0 True by simp
      thus ?thesis using rsnil vsRP by auto
    next
      case False
      with split2 have fcsplit: "flatBP cp = us @ vs"
          and jrest: "vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]" by auto
      have False
      proof (cases "us = []")
        case True
        hence "vs = Dsym w # flatBT cb" using fcsplit fchd by simp
        hence "hd (vs @ b) = Dsym w" by simp
        moreover have "vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
          using jrest by simp
        moreover have "hd (concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]) = CM
              \<or> hd (concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]) = RP"
          by (cases rs) auto
        ultimately show False by auto
      next
        case usne: False
        have vsne: "vs \<noteq> []"
        proof
          assume v0: "vs = []"
          hence "flatBP cp = us \<and> b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
            using fcsplit jrest by simp
          thus False using False v0 by simp
        qed
        have "flatinj_dsum us < 0"
        proof -
          have "flatinj_dsum (flatBP r0) = -1" by (rule flatinj_dsum_flatBP)
          moreover have "0 \<le> flatinj_dsum s1"
            using flatinj_prefix_nonneg_BP[OF inr0 usne] .
          moreover have "flatinj_dsum (flatBP r0) = flatinj_dsum s1 + flatinj_dsum us"
            using inr0 by simp
          ultimately show ?thesis by simp
        qed
        moreover have "0 \<le> flatinj_dsum us"
          using flatinj_prefix_nonneg_BP[OF fcsplit vsne] .
        ultimately show False by simp
      qed
      thus ?thesis ..
    qed
  qed
qed

text \<open>Destructor: an scb-decomposition pins to the last principal component.\<close>

lemma scb_to_last_component:
  assumes d: "scb_decomp u s (flatBT (Trm [cp])) b" and une: "u \<noteq> Trm []"
  shows "\<exists>sc bc. flatBP (last (untrm u)) = sc @ flatBP cp @ bc
               \<and> (\<forall>x \<in> set bc. x = RP)"
proof -
  from d have eq: "flatBT u = s @ flatBP cp @ b" and rb: "\<forall>x \<in> set b. x = RP"
    by (auto simp: scb_decomp_def)
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?thesis
  proof (cases u)
    case (Trm ps)
    show ?thesis
    proof (cases ps)
      case Nil thus ?thesis using Trm une by simp
    next
      case (Cons p0 ps1)
      show ?thesis
      proof (cases ps1)
        case Nil
        \<comment> \<open>single component: the decomposition is already component-level\<close>
        have "flatBP p0 = s @ flatBP cp @ b" using eq Trm Cons Nil by simp
        thus ?thesis using Trm Cons Nil rb by auto
      next
        case (Cons q ps2)
        have eq3: "LP # (flatBP p0
              @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2))) @ [RP]
              = s @ flatBP cp @ b"
          using eq Trm \<open>ps = p0 # ps1\<close> Cons by simp
        have sne: "s \<noteq> []"
        proof
          assume "s = []"
          hence "LP = Dsym w" using eq3 cpw by simp
          thus False by simp
        qed
        then obtain s1 where ss: "s = LP # s1" using eq3 by (cases s) auto
        have eq4: "flatBP p0 @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
              = s1 @ flatBP cp @ b"
          using eq3 ss by simp
        \<comment> \<open>first-component occurrence is impossible; join occurrence extracts\<close>
        from append_eq_append_conv2[THEN iffD1, OF eq4]
        obtain us where split:
            "flatBP p0 = s1 @ us \<and> us @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
                                    = flatBP cp @ b
           \<or> flatBP p0 @ us = s1 \<and> concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
                                    = us @ flatBP cp @ b" by blast
        show ?thesis
        proof (cases "flatBP p0 @ us = s1
              \<and> concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
                = us @ flatBP cp @ b")
          case True
          have "\<exists>sc bc. flatBP (last (q # ps2)) = sc @ flatBP cp @ bc
                      \<and> (\<forall>x \<in> set bc. x = RP)"
            using scbext_join True rb by blast
          thus ?thesis using Trm \<open>ps = p0 # ps1\<close> Cons by simp
        next
          case False
          with split have inp: "flatBP p0 = s1 @ us"
              and rest: "us @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
                         = flatBP cp @ b" by auto
          from append_eq_append_conv2[THEN iffD1, OF rest[symmetric]]
          obtain vs where split2:
              "flatBP cp = us @ vs
                 \<and> vs @ b = concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
             \<or> flatBP cp @ vs = us
                 \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]"
            by blast
          have False
          proof (cases "flatBP cp @ vs = us
                \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]")
            case True
            hence "CM \<in> set b" by auto
            thus False using rb by auto
          next
            case False
            with split2 have fcsplit: "flatBP cp = us @ vs"
                and jrest: "vs @ b
                  = concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]" by auto
            show False
            proof (cases "us = []")
              case True
              hence "vs = Dsym w # flatBT cb" using fcsplit cpw by simp
              hence "hd (vs @ b) = Dsym w" by simp
              moreover have "hd (concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]) = CM"
                by simp
              ultimately show False using jrest by simp
            next
              case usne: False
              have vsne: "vs \<noteq> []"
              proof
                assume v0: "vs = []"
                hence "flatBP cp @ vs = us \<and> b
                  = vs @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]"
                  using fcsplit jrest by simp
                thus False using False by simp
              qed
              have "flatinj_dsum us < 0"
              proof -
                have "flatinj_dsum (flatBP p0) = -1" by (rule flatinj_dsum_flatBP)
                moreover have "0 \<le> flatinj_dsum s1"
                  using flatinj_prefix_nonneg_BP[OF inp usne] .
                moreover have "flatinj_dsum (flatBP p0)
                  = flatinj_dsum s1 + flatinj_dsum us" using inp by simp
                ultimately show ?thesis by simp
              qed
              moreover have "0 \<le> flatinj_dsum us"
                using flatinj_prefix_nonneg_BP[OF fcsplit vsne] .
              ultimately show False by simp
            qed
          qed
          thus ?thesis ..
        qed
      qed
    qed
  qed
qed

text \<open>Constructor: a component-level occurrence lifts into any term sharing
  that last component.\<close>

lemma scb_from_last_component:
  assumes comp: "flatBP (last (untrm w)) = sc @ flatBP cp @ bc"
    and rb: "\<forall>x \<in> set bc. x = RP"
    and wne: "untrm w \<noteq> []"
    and pc: "dfree_BP cp"
  shows "\<exists>s' b'. scb_decomp w s' (flatBT (Trm [cp])) b'"
proof -
  obtain ws where wTrm: "w = Trm ws" by (cases w) auto
  have ipt: "isPTB_str (flatBT (Trm [cp])) \<or> True" by simp
  show ?thesis
  proof (cases ws)
    case Nil thus ?thesis using wTrm wne by simp
  next
    case (Cons p0 ps1)
    show ?thesis
    proof (cases ps1)
      case Nil
      have "flatBT w = sc @ flatBP cp @ bc"
        using wTrm Cons Nil comp by simp
      hence "scb_decomp w sc (flatBT (Trm [cp])) bc"
        unfolding scb_decomp_def using rb pc
        by (auto simp: isPTB_str_def intro: exI[of _ cp])
      thus ?thesis by blast
    next
      case (Cons q ps2)
      have lastc: "last ws = last (q # ps2)" using \<open>ws = p0 # ps1\<close> Cons by simp
      have joinsnoc: "concat (map (\<lambda>r. CM # flatBP r) (q # ps2))
            = concat (map (\<lambda>r. CM # flatBP r) (butlast (q # ps2)))
              @ CM # flatBP (last (q # ps2))"
      proof -
        have eq: "q # ps2 = butlast (q # ps2) @ [last (q # ps2)]"
          by (simp add: append_butlast_last_id)
        have "concat (map (\<lambda>r. CM # flatBP r) (q # ps2))
            = concat (map (\<lambda>r. CM # flatBP r) (butlast (q # ps2) @ [last (q # ps2)]))"
          using eq by (rule arg_cong[where f="\<lambda>xs. concat (map (\<lambda>r. CM # flatBP r) xs)"])
        also have "\<dots> = concat (map (\<lambda>r. CM # flatBP r) (butlast (q # ps2)))
                      @ CM # flatBP (last (q # ps2))"
          by simp
        finally show ?thesis .
      qed
      have "flatBT w = LP # (flatBP p0
            @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2))) @ [RP]"
        using wTrm \<open>ws = p0 # ps1\<close> Cons by simp
      also have "\<dots> = (LP # flatBP p0
            @ concat (map (\<lambda>r. CM # flatBP r) (butlast (q # ps2)))
            @ CM # sc) @ flatBP cp @ (bc @ [RP])"
        using joinsnoc comp wTrm lastc \<open>ws = p0 # ps1\<close> by simp
      finally have "scb_decomp w (LP # flatBP p0
            @ concat (map (\<lambda>r. CM # flatBP r) (butlast (q # ps2)))
            @ CM # sc) (flatBT (Trm [cp])) (bc @ [RP])"
        unfolding scb_decomp_def using rb pc
        by (auto simp: isPTB_str_def intro: exI[of _ cp])
      thus ?thesis by blast
    qed
  qed
qed


text \<open>The combined transfer: \<open>MarkedB\<close> membership depends only on the last
  principal component (used for the \<open>+\<^sub>B\<close> assembly in the (C) branch of the
  \<open>Trans\<close>/\<open>Mark\<close> value invariant).\<close>

lemma MarkedB_last_component_transfer:
  assumes uc: "(u, c) \<in> MarkedB" and une: "u \<noteq> Trm []"
    and lc: "last (untrm u) = last (untrm w)"
    and wne: "untrm w \<noteq> []"
  shows "(w, c) \<in> MarkedB"
proof -
  from uc obtain s b where d: "scb_decomp u s (flatBT c) b"
    by (auto simp: MarkedB_def)
  have ipt: "isPTB_str (flatBT c)" using d une by (simp add: scb_decomp_def)
  then obtain p where pf: "dfree_BP p" and pfl: "flatBT c = flatBP p"
    by (auto simp: isPTB_str_def)
  have cp: "c = Trm [p]"
  proof -
    have "flatBT c = flatBT (Trm [p])" using pfl by simp
    thus ?thesis by (rule m_7_flatBT_inj)
  qed
  have d': "scb_decomp u s (flatBT (Trm [p])) b" using d cp by simp
  obtain sc bc where comp: "flatBP (last (untrm u)) = sc @ flatBP p @ bc"
      and rbc: "\<forall>x \<in> set bc. x = RP"
    using scb_to_last_component[OF d' une] by blast
  have comp': "flatBP (last (untrm w)) = sc @ flatBP p @ bc"
    using comp lc by simp
  have "\<exists>s' b'. scb_decomp w s' (flatBT (Trm [p])) b'"
    by (rule scb_from_last_component[OF comp' rbc wne pf])
  thus ?thesis using cp by (auto simp: MarkedB_def)
qed


text \<open>A mono sequence's last column has a (unique) row-0 parent: its row-0
  entry strictly exceeds the left end (@{thm [source] m_5_1_ancestor_basic_1}),
  so it is not a running minimum (@{thm [source] idxsum_no_parent0_iff}).\<close>

lemma monoT_hasParent0_last:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and L: "1 < Lng M"
  shows "hasParent M 0 (Lng M - 1)"
proof -
  have j1lt: "Lng M - 1 < Lng M" using L by simp
  have leM: "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
  have "entry M 0 0 < entry M 0 (Lng M - 1)"
    by (rule m_5_1_ancestor_basic_1[OF MT _ order.refl leM]) (use L in linarith)
  hence "\<not> (\<forall>j < Lng M - 1. entry M 0 j \<ge> entry M 0 (Lng M - 1))"
    using L by (auto intro!: exI[of _ 0])
  thus ?thesis
    using idxsum_no_parent0_iff[OF MT j1lt]
    unfolding hasParent_def by blast
qed


text \<open>Three small \<open>MarkedB\<close>/scb helpers for the value-invariant assembly:
  lifting a decomposition through a principal head, through a right summand
  of \<open>+\<^sub>B\<close>, and the \<open>BP\<close>-level principal replacement (principality of the
  replaced term).\<close>

lemma scb_Dpt_lift:
  assumes d: "scb_decomp X s c b" and ipt: "isPTB_str c"
  shows "scb_decomp (Dpt v X) (Dsym v # s) c b"
proof -
  from d have "flatBT X = s @ c @ b" and "\<forall>x \<in> set b. x = RP"
    by (auto simp: scb_decomp_def)
  moreover have "flatBT (Dpt v X) = Dsym v # flatBT X" by simp
  ultimately show ?thesis using ipt by (simp add: scb_decomp_def)
qed

lemma MarkedB_addBT_right:
  assumes mb: "(X, c) \<in> MarkedB" and Xne: "X \<noteq> 0\<^sub>B"
  shows "(Y +\<^sub>B X, c) \<in> MarkedB"
proof -
  obtain as where Yt: "Y = Trm as" by (cases Y) auto
  obtain bs where Xt: "X = Trm bs" by (cases X) auto
  have bsne: "bs \<noteq> []" using Xne Xt by simp
  have lastEq: "last (untrm X) = last (untrm (Y +\<^sub>B X))"
    using Yt Xt bsne by simp
  have wne: "untrm (Y +\<^sub>B X) \<noteq> []" using Yt Xt bsne by simp
  show ?thesis
    by (rule MarkedB_last_component_transfer[OF mb _ lastEq wne])
       (use Xne Xt in simp)
qed

lemma scb_replace_principal_BP:
  assumes d: "scb_decomp (Trm [p0]) s (flatBT (Trm [cp])) b"
    and pc': "isPTB_str (flatBT (Trm [cp']))"
  shows "\<exists>p'. flatBP p' = s @ flatBT (Trm [cp']) @ b
            \<and> scb_decomp (Trm [p']) s (flatBT (Trm [cp'])) b"
proof -
  from d have eq: "flatBP p0 = s @ flatBP cp @ b"
    and rb: "\<forall>x \<in> set b. x = RP"
    by (auto simp: scb_decomp_def)
  obtain p' where p': "flatBP p' = s @ flatBP cp' @ b"
    using scbimg_image_BP[OF eq rb] by blast
  have "scb_decomp (Trm [p']) s (flatBT (Trm [cp'])) b"
    unfolding scb_decomp_def using p' pc' rb by simp
  thus ?thesis using p' by auto
qed


text \<open>\<open>MarkedB\<close> through a principal head.\<close>

lemma MarkedB_Dpt_lift:
  assumes mb: "(X, c) \<in> MarkedB" and ipt: "isPTB_str (flatBT c)"
  shows "(Dpt v X, c) \<in> MarkedB"
proof -
  from mb obtain s b where "scb_decomp X s (flatBT c) b"
    by (auto simp: MarkedB_def)
  hence "scb_decomp (Dpt v X) (Dsym v # s) (flatBT c) b"
    by (rule scb_Dpt_lift[OF _ ipt])
  thus ?thesis unfolding MarkedB_def by auto
qed

text \<open>The hard (B) branch of the \<open>Trans\<close>/\<open>Mark\<close> value invariant
  (\<open>monoT M\<close>, \<open>t\<^sub>1 \<noteq> 0\<close>), as a dedicated lemma taking the induction
  hypotheses for \<open>Pred M\<close> as named assumptions.\<close>

lemma trans_inv_B_hard:
  assumes MR: "M \<in> RT_PS" and mono: "monoT M" and L: "1 < Lng M"
    and t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B"
    and IHt1: "dfree_BT (Trans (Pred M))"
    and IHmk: "\<And>m'. (Pred M, m') \<in> Marked
                 \<Longrightarrow> dfree_BT (Mark (Pred M) m')
                   \<and> (Trans (Pred M), Mark (Pred M) m') \<in> MarkedB"
  shows "dfree_BT (Trans M) \<and> Trans M \<noteq> 0\<^sub>B
       \<and> (\<forall>m. (M, m) \<in> Marked
              \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
  have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  let ?t1 = "Trans (Pred M)"
  let ?bv = "entry M 1 (Lng M - 1)"
  define jp where "jp = parent M 0 (Lng M - 1)"
  define c1 where "c1 = Mark (Pred M) (Adm M jp)"
  define vv where "vv = bpHeadV c1"
  define tt2 where "tt2 = bpHeadT c1"
  define JJ1 where "JJ1 = Lng (PB tt2) - 1"
  define pj where "pj = PB tt2 ! JJ1"
  define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
  define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
  define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
  define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                         then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                         else if transCondVI M
                         then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                         else if tt2 = 0\<^sub>B
                         then Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                         else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                            (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
  define sb1 where "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
  have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
    using Trans.psimps[OF domT] MR Lgt1 mono t1ne
    unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
              tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
              ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
              c2_def[symmetric] sb1_def[symmetric]
    by simp
  \<comment> \<open>induction facts for \<open>c\<^sub>1\<close>\<close>
  have mkdA: "(Pred M, Adm M jp) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp] jp_def by simp
  have c1df: "dfree_BT c1" and mb1: "(?t1, c1) \<in> MarkedB"
    using IHmk[OF mkdA] c1_def by auto
  have t1neT: "?t1 \<noteq> Trm []" using t1ne by simp
  \<comment> \<open>the SOME decomposition exists\<close>
  have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
    using mb1 unfolding MarkedB_def by auto
  have dsome: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
    unfolding sb1_def by (rule someI_ex[OF exsb])
  \<comment> \<open>\<open>c\<^sub>1\<close> is a principal dfree term\<close>
  have iptc1: "isPTB_str (flatBT c1)"
    using dsome t1neT by (simp add: scb_decomp_def)
  then obtain pc where pcf: "dfree_BP pc" and pcl: "flatBT c1 = flatBP pc"
    by (auto simp: isPTB_str_def)
  have c1p: "c1 = Trm [pc]"
  proof -
    have "flatBT c1 = flatBT (Trm [pc])" using pcl by simp
    thus ?thesis by (rule m_7_flatBT_inj)
  qed
  obtain wv tb where pcw: "pc = DB wv tb" by (cases pc) auto
  have vvv: "vv = wv" using vv_def c1p pcw by simp
  have tt2v: "tt2 = tb" using tt2_def c1p pcw by simp
  have wvne: "wv \<noteq> \<infinity>" and tbdf: "dfree_BT tb" using pcf pcw by auto
  \<comment> \<open>\<open>c\<^sub>2\<close> is a principal dfree term ending (spine-wise) in \<open>D\<^bsub>?bv\<^esub> 0\<close>\<close>
  have c2shape: "\<exists>X. c2 = Dpt vv X \<and> dfree_BT X \<and> (X, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
  proof -
    have selfb: "(Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
    proof -
      have "scb_decomp (Dpt (enat ?bv) 0\<^sub>B) [] (flatBT (Dpt (enat ?bv) 0\<^sub>B)) []"
        by (rule scb_decomp_self) (rule isPTB_str_Dpt, simp_all)
      thus ?thesis unfolding MarkedB_def by auto
    qed
    have iptb: "isPTB_str (flatBT (Dpt (enat ?bv) 0\<^sub>B))"
      by (rule isPTB_str_Dpt) simp_all
    have dbne: "Dpt (enat ?bv) 0\<^sub>B \<noteq> 0\<^sub>B" by simp
    consider (A) "transCondI M \<or> transCondIII M \<or> transCondV M"
      | (VI) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "transCondVI M"
      | (Z) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "\<not> transCondVI M"
            "tt2 = 0\<^sub>B"
      | (E) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "\<not> transCondVI M"
            "tt2 \<noteq> 0\<^sub>B"
      by blast
    thus ?thesis
    proof cases
      case A
      have x: "c2 = Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)" using A c2_def by simp
      have df: "dfree_BT (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)"
        using tt2v tbdf by (cases tb) auto
      have mb: "(tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF selfb dbne])
      show ?thesis using x df mb by blast
    next
      case VI
      have x: "c2 = Dpt vv (Dpt (enat ?bv) 0\<^sub>B)" using VI c2_def by simp
      have mb: "(Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB" by (rule selfb)
      show ?thesis using x mb by auto
    next
      case Z
      have x: "c2 = Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))"
        using Z c2_def by simp
      have mb: "(Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B),
                 Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_Dpt_lift[OF selfb iptb])
      show ?thesis using x mb by auto
    next
      case E
      have x: "c2 = Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                   (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B))"
        using E c2_def by simp
      have df3: "dfree_BT tt3"
      proof -
        have "dfree_BT (SigmaB (take JJ1 (PB tb)))"
          using tbdf by (cases tb) (auto simp: SigmaB_def PB_def dest!: in_set_takeD)
        thus ?thesis using tt3_def tt2v tbdf by simp
      qed
      have df4: "dfree_BT tt4"
      proof -
        have tbne: "untrm tb \<noteq> []" using E(3) tt2v by (cases tb) auto
        have inr: "JJ1 < Lng (PB tb)"
          using JJ1_def tt2v tbne by (simp add: PB_def)
        have "pj \<in> set (PB tb)" using pj_def tt2v inr by simp
        hence "dfree_BT pj" using tbdf by (cases tb) (auto simp: PB_def)
        hence "dfree_BT (bpHeadT pj)" by (cases pj rule: bpHeadT.cases) auto
        thus ?thesis using tt4_def tt2v tbdf by simp
      qed
      have dfsum: "dfree_BT (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)"
        using df4 by (cases tt4) auto
      have mbin: "(tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF selfb dbne])
      have mbmid: "(Dpt (enat (entry M 1 jp)) (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B),
                    Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_Dpt_lift[OF mbin iptb])
      have mbout: "(tt3 +\<^sub>B Dpt (enat (entry M 1 jp)) (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B),
                    Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF mbmid]) simp
      have dfall: "dfree_BT (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                    (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B))"
        using df3 dfsum by (cases tt3) auto
      show ?thesis using x mbout dfall by blast
    qed
  qed
  obtain X2 where c2X: "c2 = Dpt vv X2" and X2df: "dfree_BT X2"
      and X2mb: "(X2, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
    using c2shape by blast
  have c2df: "dfree_BT c2" using c2X X2df wvne vvv by simp
  have iptc2: "isPTB_str (flatBT c2)"
    using c2X by (intro isPTB_str_Dpt[of vv X2, folded c2X])
                 (use wvne vvv X2df in simp_all)
  have c2mb: "(c2, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
  proof -
    have iptb: "isPTB_str (flatBT (Dpt (enat ?bv) 0\<^sub>B))"
      by (rule isPTB_str_Dpt) simp_all
    show ?thesis using MarkedB_Dpt_lift[OF X2mb iptb] c2X by simp
  qed
  obtain pc2 where c2p: "c2 = Trm [pc2]" using c2X by auto
  \<comment> \<open>the replaced \<open>Trans\<close> value\<close>
  have dsome': "scb_decomp ?t1 (fst sb1) (flatBT (Trm [pc])) (snd sb1)"
    using dsome c1p by simp
  have iptc2': "isPTB_str (flatBT (Trm [pc2]))" using iptc2 c2p by simp
  obtain t' where t'f: "flatBT t' = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
      and t'd: "scb_decomp t' (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
    using scb_replace_principal[OF dsome' iptc2'] by blast
  have transM: "Trans M = t'"
    using trans_val t'f c2p unflatBT_flat[of t'] by simp
  \<comment> \<open>dfree and nonzero\<close>
  have sb_sub: "set (fst sb1) \<subseteq> set (flatBT ?t1)"
      and bb_sub: "set (snd sb1) \<subseteq> set (flatBT ?t1)"
    using dsome by (auto simp: scb_decomp_def)
  have t'df: "dfree_BT t'"
  proof -
    have "\<And>v'. Dsym v' \<in> set (flatBT t') \<Longrightarrow> v' \<noteq> \<infinity>"
    proof -
      fix v' assume "Dsym v' \<in> set (flatBT t')"
      hence "Dsym v' \<in> set (flatBT ?t1) \<or> Dsym v' \<in> set (flatBT c2)"
        using t'f c2p sb_sub bb_sub by auto
      thus "v' \<noteq> \<infinity>"
        using IHt1 c2df dfree_flat_BT by blast
    qed
    thus ?thesis using dfree_flat_BT by blast
  qed
  have t'ne: "t' \<noteq> 0\<^sub>B"
  proof
    assume "t' = 0\<^sub>B"
    hence z: "flatBT t' = [Zsym]" by simp
    have pc2v: "pc2 = DB vv X2" using c2p c2X by simp
    have "Dsym vv \<in> set (flatBP pc2)" using pc2v by simp
    hence "Dsym vv \<in> set (flatBT t')" using t'f by simp
    thus False using z by simp
  qed
  \<comment> \<open>the Mark values\<close>
  have markB: "\<And>m. (M, m) \<in> Marked
       \<Longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB"
  proof -
    fix m assume mM: "(M, m) \<in> Marked"
    \<comment> \<open>the fallback value \<open>D\<^bsub>?bv\<^esub> 0\<close> always satisfies both conjuncts\<close>
    have fb_df: "dfree_BT (Dpt (enat ?bv) 0\<^sub>B)" by simp
    have fb_mb: "(Trans M, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
    proof -
      from c2mb obtain s2x b2x where d2x: "scb_decomp c2 s2x (flatBT (Dpt (enat ?bv) 0\<^sub>B)) b2x"
        by (auto simp: MarkedB_def)
      have "scb_decomp t' (fst sb1 @ s2x) (flatBT (Dpt (enat ?bv) 0\<^sub>B)) (b2x @ snd sb1)"
        by (rule m_7_2_scb_compose[OF _ _ d2x])
           (use c2p t'd in auto)
      thus ?thesis using transM unfolding MarkedB_def by auto
    qed
    show "dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB"
    proof (cases "m < Lng M - 1")
      case False
      have "Mark M m = Dpt (enat ?bv) 0\<^sub>B"
        using Mark.psimps[OF domK] MR Lgt1 mono t1ne False
        unfolding Let_def jp_def[symmetric] c1_def[symmetric]
        by simp
      thus ?thesis using fb_df fb_mb by simp
    next
      case mlt: True
      define c0 where "c0 = Mark (Pred M) m"
      define sm1 where "sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))"
      have mark_val_raw: "Mark M m = (if (Mark (Pred M) m, c1) \<in> MarkedB
            then unflatBT
                   (fst (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                    (flatBT c1) (snd sb))
                    @ flatBT c2
                    @ snd (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                      (flatBT c1) (snd sb)))
            else Dpt (enat ?bv) 0\<^sub>B)"
        using Mark.psimps[OF domK] MR Lgt1 mono t1ne mlt
        unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                  tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                  ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                  c2_def[symmetric]
        by simp
      have mark_val: "Mark M m = (if (c0, c1) \<in> MarkedB
            then unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
            else Dpt (enat ?bv) 0\<^sub>B)"
        using mark_val_raw by (simp add: c0_def sm1_def)
      show ?thesis
      proof (cases "(c0, c1) \<in> MarkedB")
        case False
        thus ?thesis using mark_val fb_df fb_mb by simp
      next
        case mbc: True
        have mPred: "(Pred M, m) \<in> Marked"
          by (rule Marked_Pred[OF MT L mM mlt])
        have c0df: "dfree_BT c0" and mb0: "(?t1, c0) \<in> MarkedB"
          using IHmk[OF mPred] c0_def by auto
        \<comment> \<open>\<open>c\<^sub>0\<close> is principal\<close>
        from mb0 obtain s0 b0 where d0: "scb_decomp ?t1 s0 (flatBT c0) b0"
          by (auto simp: MarkedB_def)
        have iptc0: "isPTB_str (flatBT c0)"
          using d0 t1neT by (simp add: scb_decomp_def)
        then obtain pc0 where pc0f: "dfree_BP pc0" and pc0l: "flatBT c0 = flatBP pc0"
          by (auto simp: isPTB_str_def)
        have c0p: "c0 = Trm [pc0]"
        proof -
          have "flatBT c0 = flatBT (Trm [pc0])" using pc0l by simp
          thus ?thesis by (rule m_7_flatBT_inj)
        qed
        \<comment> \<open>the \<open>SOME\<close> for \<open>c\<^sub>0\<close>\<close>
        have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
          using mbc unfolding MarkedB_def by auto
        have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
          unfolding sm1_def by (rule someI_ex[OF exsm])
        have dsm': "scb_decomp (Trm [pc0]) (fst sm1) (flatBT (Trm [pc])) (snd sm1)"
          using dsm c0p c1p by simp
        \<comment> \<open>the replaced \<open>Mark\<close> value (principal)\<close>
        obtain pm where pmf: "flatBP pm = fst sm1 @ flatBT (Trm [pc2]) @ snd sm1"
            and pmd: "scb_decomp (Trm [pm]) (fst sm1) (flatBT (Trm [pc2])) (snd sm1)"
          using scb_replace_principal_BP[OF dsm' iptc2'] by blast
        have markM: "Mark M m = Trm [pm]"
        proof -
          have "flatBT (Trm [pm]) = fst sm1 @ flatBT c2 @ snd sm1"
            using pmf c2p by simp
          thus ?thesis
            using mark_val mbc unflatBT_flat[of "Trm [pm]"] by simp
        qed
        \<comment> \<open>dfree of the replaced value\<close>
        have sm_sub: "set (fst sm1) \<subseteq> set (flatBT c0)"
            and bm_sub: "set (snd sm1) \<subseteq> set (flatBT c0)"
          using dsm by (auto simp: scb_decomp_def)
        have mmdf: "dfree_BT (Trm [pm])"
        proof -
          have "\<And>v'. Dsym v' \<in> set (flatBT (Trm [pm])) \<Longrightarrow> v' \<noteq> \<infinity>"
          proof -
            fix v' assume "Dsym v' \<in> set (flatBT (Trm [pm]))"
            hence "Dsym v' \<in> set (flatBT c0) \<or> Dsym v' \<in> set (flatBT c2)"
              using pmf c2p sm_sub bm_sub by auto
            thus "v' \<noteq> \<infinity>" using c0df c2df dfree_flat_BT by blast
          qed
          thus ?thesis using dfree_flat_BT by blast
        qed
        \<comment> \<open>coherence: the two-step decomposition equals the direct one\<close>
        have comp: "scb_decomp ?t1 (s0 @ fst sm1) (flatBT c1) (snd sm1 @ b0)"
          by (rule m_7_2_scb_compose[OF _ _ dsm]) (use c0p d0 in auto)
        have coh: "fst sb1 = s0 @ fst sm1 \<and> snd sb1 = snd sm1 @ b0"
          by (rule m_7_2_scb_unique_sb[OF dsome comp t1neT])
        have t'flat: "flatBT t' = s0 @ flatBT (Trm [pm]) @ b0"
          using t'f coh pmf c2p by simp
        have b0rp: "\<forall>x \<in> set b0. x = RP"
          using d0 by (simp add: scb_decomp_def)
        have iptm: "isPTB_str (flatBT (Trm [pm]))"
        proof -
          have "dfree_BP pm"
            using mmdf by simp
          thus ?thesis using isPTB_str_def by auto
        qed
        have "scb_decomp t' s0 (flatBT (Trm [pm])) b0"
          unfolding scb_decomp_def using t'flat iptm b0rp by simp
        hence "(Trans M, Mark M m) \<in> MarkedB"
          using transM markM unfolding MarkedB_def by auto
        thus ?thesis using mmdf markM by simp
      qed
    qed
  qed
  show ?thesis using transM t'df t'ne markB by auto
qed


text \<open>The (C) multiT branch of the \<open>Trans\<close>/\<open>Mark\<close> value invariant, as a
  dedicated lemma taking the induction hypotheses for the two smaller
  recursion arguments — the diagonal prefix \<open>take (Pcut M) M\<close> and the last
  \<open>P\<close>-component \<open>drop (Pcut M) M\<close>.  \<open>Trans M = Trans A +\<^sub>B (\<dots>)\<close> appends a
  non-empty right summand, and \<open>MarkedB\<close> reduces to that summand
  (@{thm [source] MarkedB_addBT_right}).\<close>

lemma trans_inv_C:
  assumes MR: "M \<in> RT_PS" and mu: "multiT M"
    and dfTA: "dfree_BT (Trans (take (Pcut M) M))"
    and dfTJ: "dfree_BT (Trans (drop (Pcut M) M))"
    and nzTJ: "\<not> zeroT (drop (Pcut M) M) \<Longrightarrow> Trans (drop (Pcut M) M) \<noteq> 0\<^sub>B"
    and IHmkJ: "\<And>m'. (drop (Pcut M) M, m') \<in> Marked
                 \<Longrightarrow> dfree_BT (Mark (drop (Pcut M) M) m')
                   \<and> (Trans (drop (Pcut M) M), Mark (drop (Pcut M) M) m') \<in> MarkedB"
  shows "dfree_BT (Trans M) \<and> Trans M \<noteq> 0\<^sub>B
       \<and> (\<forall>m. (M, m) \<in> Marked
              \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  have nmono: "\<not> monoT M" using mu by (simp add: multiT_def)
  have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
  have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
  let ?A = "take (Pcut M) M"
  let ?PJ = "drop (Pcut M) M"
  \<comment> \<open>identify the def's PJ / j0 / prefix with their \<open>Pcut\<close>-forms\<close>
  have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
    by (rule trans_multiT_last_component(1)[OF MT mu])
  have j0eq: "Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 = Pcut M"
    by (rule trans_multiT_last_component(2)[OF MT mu])
  have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
  \<comment> \<open>seg/offset equalities in \<open>drop\<close>-form (so they apply AFTER @{thm PJeq}
     has rewritten \<open>P M ! \<dots>\<close> to \<open>?PJ\<close>, without simp splitting the inner if)\<close>
  have LdJ: "Lng (drop (Pcut M) M) = Lng M - Pcut M" by simp
  have Aeq2: "seg M 0 (Lng M - 1 - Lng (drop (Pcut M) M) + 1 - 1) = ?A"
  proof -
    have "Lng M - 1 - Lng (drop (Pcut M) M) + 1 - 1 = Pcut M - 1"
      using LdJ cut by linarith
    moreover have "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
      by (rule seg_0_eq_take) (use cut L in linarith)
    moreover have "Suc (Pcut M - 1) = Pcut M" using cut by simp
    ultimately show ?thesis by simp
  qed
  have meq2: "\<And>m. m - (Lng M - 1 - Lng (drop (Pcut M) M) + 1) = m - Pcut M"
  proof -
    fix m
    have "Lng M - 1 - Lng (drop (Pcut M) M) + 1 = Pcut M"
      using LdJ cut by linarith
    thus "m - (Lng M - 1 - Lng (drop (Pcut M) M) + 1) = m - Pcut M" by simp
  qed
  \<comment> \<open>the two recursion values.  Collapse only the OUTER ifs with \<open>simp only\<close>
     (full \<open>simp\<close> pushes the inner if-condition into the branches and rewrites
     \<open>Lng PJ\<close> differently per branch), then rewrite the raw form by \<open>unfolding\<close>
     (no if-splitting) and close with @{thm refl}.\<close>
  have c1: "(M \<notin> RT_PS) = False" using MR by simp
  have c2: "(Lng M - 1 = 0) = False" using L by simp
  have c3: "monoT M = False" using nmono by simp
  have transM: "Trans M = (if ?PJ = [(0, 0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B
                           else Trans ?A +\<^sub>B Trans ?PJ)"
  proof -
    have raw: "Trans M =
        (if P M ! (Lng (P M) - 1) = [(0, 0)]
         then Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                +\<^sub>B Dpt 0 0\<^sub>B
         else Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                +\<^sub>B Trans (P M ! (Lng (P M) - 1)))"
      by (subst Trans.psimps[OF domT]) (simp only: c1 c2 c3 if_False Let_def)
    show ?thesis unfolding raw PJeq Aeq2 ..
  qed
  have markM: "\<And>m. Mark M m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                               else Mark ?PJ (m - Pcut M))"
  proof -
    fix m
    have raw: "Mark M m =
        (if P M ! (Lng (P M) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
         else Mark (P M ! (Lng (P M) - 1))
                (m - (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1)))"
      by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
    show "Mark M m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B else Mark ?PJ (m - Pcut M))"
      unfolding raw PJeq meq2 ..
  qed
  \<comment> \<open>dfree / nonzero of the right-appended term\<close>
  have dfadd: "\<And>a b. dfree_BT a \<Longrightarrow> dfree_BT b \<Longrightarrow> dfree_BT (a +\<^sub>B b)"
  proof -
    fix a b assume da: "dfree_BT a" and db: "dfree_BT b"
    obtain as where a: "a = Trm as" by (cases a)
    obtain bs where b: "b = Trm bs" by (cases b)
    show "dfree_BT (a +\<^sub>B b)" using da db a b by auto
  qed
  have nzadd: "\<And>a b. b \<noteq> 0\<^sub>B \<Longrightarrow> a +\<^sub>B b \<noteq> 0\<^sub>B"
  proof -
    fix a b assume bne: "b \<noteq> 0\<^sub>B"
    obtain as where a: "a = Trm as" by (cases a)
    obtain bs where b: "b = Trm bs" by (cases b)
    have "bs \<noteq> []" using bne b by auto
    thus "a +\<^sub>B b \<noteq> 0\<^sub>B" using a b by auto
  qed
  have dfD0: "dfree_BT (Dpt 0 0\<^sub>B)" by (simp add: zero_enat_def)
  have nzD0: "Dpt 0 0\<^sub>B \<noteq> 0\<^sub>B" by simp
  \<comment> \<open>the last component is reduced and (in the else case) non-zero-term\<close>
  have Pne: "P M \<noteq> []" by (rule P_nonempty)
  have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
  have PJRT: "?PJ \<in> RT_PS"
    using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
  have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
  have nzPJ: "?PJ \<noteq> [(0, 0)] \<Longrightarrow> \<not> zeroT ?PJ"
  proof
    assume ne: "?PJ \<noteq> [(0, 0)]" and z: "zeroT ?PJ"
    have L1: "Lng ?PJ = 1" using z by (simp add: zeroT_def)
    then obtain v where v: "?PJ = [(v, v)]"
      using m_6_6_oneColumn[OF PJT] PJRT by auto
    have "entry ?PJ 1 0 = 0" using z by (simp add: zeroT_def)
    hence "v = 0" using v by (simp add: entry_def)
    thus False using ne v by simp
  qed
  \<comment> \<open>Trans M dfree and nonzero\<close>
  have dfT_nzT: "dfree_BT (Trans M) \<and> Trans M \<noteq> 0\<^sub>B"
  proof (cases "?PJ = [(0, 0)]")
    case True
    have tv: "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM True by simp
    have "dfree_BT (Trans ?A +\<^sub>B Dpt 0 0\<^sub>B)" by (rule dfadd[OF dfTA dfD0])
    moreover have "Trans ?A +\<^sub>B Dpt 0 0\<^sub>B \<noteq> 0\<^sub>B" by (rule nzadd[OF nzD0])
    ultimately show ?thesis using tv by simp
  next
    case False
    have tv: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM False by simp
    have nz: "Trans ?PJ \<noteq> 0\<^sub>B" using nzTJ[OF nzPJ[OF False]] .
    have "dfree_BT (Trans ?A +\<^sub>B Trans ?PJ)" by (rule dfadd[OF dfTA dfTJ])
    moreover have "Trans ?A +\<^sub>B Trans ?PJ \<noteq> 0\<^sub>B" by (rule nzadd[OF nz])
    ultimately show ?thesis using tv by simp
  qed
  \<comment> \<open>the Mark values and MarkedB membership\<close>
  have markB: "\<And>m. (M, m) \<in> Marked
       \<Longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB"
  proof -
    fix m assume mM: "(M, m) \<in> Marked"
    show "dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB"
    proof (cases "?PJ = [(0, 0)]")
      case True
      have kv: "Mark M m = Dpt 0 0\<^sub>B" using markM True by simp
      have tv: "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM True by simp
      have self: "(Dpt 0 0\<^sub>B, Dpt 0 0\<^sub>B) \<in> MarkedB"
      proof -
        have "scb_decomp (Dpt 0 0\<^sub>B) [] (flatBT (Dpt 0 0\<^sub>B)) []"
          by (rule scb_decomp_self) (rule isPTB_str_Dpt, simp_all add: zero_enat_def)
        thus ?thesis unfolding MarkedB_def by auto
      qed
      have "(Trans ?A +\<^sub>B Dpt 0 0\<^sub>B, Dpt 0 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF self nzD0])
      thus ?thesis using kv tv dfD0 by simp
    next
      case False
      have kv: "Mark M m = Mark ?PJ (m - Pcut M)" using markM False by simp
      have tv: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM False by simp
      have mPJ: "(?PJ, m - Pcut M) \<in> Marked"
        by (rule multi_Marked_last_component(2)[OF MT mu mM])
      have ih: "dfree_BT (Mark ?PJ (m - Pcut M))
                \<and> (Trans ?PJ, Mark ?PJ (m - Pcut M)) \<in> MarkedB"
        by (rule IHmkJ[OF mPJ])
      have nz: "Trans ?PJ \<noteq> 0\<^sub>B" using nzTJ[OF nzPJ[OF False]] .
      have "(Trans ?A +\<^sub>B Trans ?PJ, Mark ?PJ (m - Pcut M)) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF conjunct2[OF ih] nz])
      thus ?thesis using kv tv ih by simp
    qed
  qed
  show ?thesis using dfT_nzT markB by blast
qed


section \<open>§7.3 命題（\<open>Trans\<close>の well-defined 性）— the VALUE part:
  \<open>(Trans M, Mark M m) \<in> T\<^sub>B\<^sup>Marked\<close> on \<open>RT\<^sub>PS\<close>\<close>

text \<open>The article's well-definedness side condition (content 2044/2182), the
  simultaneous \<open>Lng\<close>-induction invariant.  Carries the auxiliary nonzero-ness
  \<open>\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<close> needed by the (C) branch (the right summand of
  \<open>+\<^sub>B\<close> must be nonzero for @{thm [source] MarkedB_addBT_right}).  The three
  productive branches are the dedicated lemmas
  @{thm [source] trans_inv_B_hard} / @{thm [source] trans_inv_C} and the
  inline (A)/(B)\<open>t\<^sub>1=0\<close> base cases.\<close>

lemma Trans_Mark_invariant_aux:
  "M \<in> RT_PS \<longrightarrow> dfree_BT (Trans M)
     \<and> (\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<^sub>B)
     \<and> (\<forall>m. (M, m) \<in> Marked
            \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (rule impI)
    assume MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
    show "dfree_BT (Trans M) \<and> (\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<^sub>B)
        \<and> (\<forall>m. (M, m) \<in> Marked
               \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
    proof (cases "Lng M = 1")
      case True
      \<comment> \<open>(A) length 1: \<open>M = [(v,v)]\<close>\<close>
      obtain v where Mv: "M = [(v, v)]"
        using m_6_6_oneColumn[OF MT] MR True by auto
      have tv: "Trans M = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Mv Trans_singleton by simp
      have kv: "\<And>m. Mark M m = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Mv Mark_singleton by simp
      have zc: "zeroT M = (v = 0)" using Mv by (simp add: zeroT_def entry_def)
      have df: "dfree_BT (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)" by simp
      have nzc: "\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<^sub>B"
        using zc tv by simp
      have mb: "((if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B),
                 (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)) \<in> MarkedB"
      proof (cases "v = 0")
        case True
        have "scb_decomp 0\<^sub>B [] (flatBT (0\<^sub>B::BT)) []" by (simp add: scb_decomp_def)
        thus ?thesis using True unfolding MarkedB_def by auto
      next
        case False
        have "scb_decomp (Dpt (enat v) 0\<^sub>B) [] (flatBT (Dpt (enat v) 0\<^sub>B)) []"
          by (rule scb_decomp_self) (rule isPTB_str_Dpt, simp_all)
        thus ?thesis using False unfolding MarkedB_def by auto
      qed
      show ?thesis using tv kv df nzc mb by simp
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      have nzM: "\<not> zeroT M" using notone by (auto simp: zeroT_def)
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        \<comment> \<open>(B) mono branch\<close>
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        have predLng: "Lng (Pred M) < Lng M" using L by (simp add: Pred_def)
        note IHp = less.IH[OF predLng, THEN mp, OF predRT]
        show ?thesis
        proof (cases "Trans (Pred M) = 0\<^sub>B")
          case t1z: True
          \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>\<close>
          let ?b = "entry M 1 (Lng M - 1)"
          have tv: "Trans M = Dpt 0 (Dpt (enat ?b) 0\<^sub>B)"
            using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
          have kv: "\<And>m. Mark M m = (if m = 0 then Dpt 0 (Dpt (enat ?b) 0\<^sub>B)
                                    else Dpt (enat ?b) 0\<^sub>B)"
            using Mark.psimps[OF domK] MR Lgt1 mono t1z by (simp add: Let_def)
          have df: "dfree_BT (Dpt 0 (Dpt (enat ?b) 0\<^sub>B))"
               and df2: "dfree_BT (Dpt (enat ?b) 0\<^sub>B)"
            by (simp_all add: zero_enat_def)
          have nzT: "Trans M \<noteq> 0\<^sub>B" using tv by simp
          have mb1: "(Dpt 0 (Dpt (enat ?b) 0\<^sub>B), Dpt 0 (Dpt (enat ?b) 0\<^sub>B)) \<in> MarkedB"
          proof -
            have "scb_decomp (Dpt 0 (Dpt (enat ?b) 0\<^sub>B)) []
                    (flatBT (Dpt 0 (Dpt (enat ?b) 0\<^sub>B))) []"
              by (rule scb_decomp_self)
                 (rule isPTB_str_Dpt, simp_all add: zero_enat_def)
            thus ?thesis unfolding MarkedB_def by auto
          qed
          have mb2: "(Dpt 0 (Dpt (enat ?b) 0\<^sub>B), Dpt (enat ?b) 0\<^sub>B) \<in> MarkedB"
          proof -
            have "flatBT (Dpt 0 (Dpt (enat ?b) 0\<^sub>B))
                  = [Dsym 0] @ flatBT (Dpt (enat ?b) 0\<^sub>B) @ []" by simp
            hence "scb_decomp (Dpt 0 (Dpt (enat ?b) 0\<^sub>B)) [Dsym 0]
                     (flatBT (Dpt (enat ?b) 0\<^sub>B)) []"
              unfolding scb_decomp_def
              using isPTB_str_Dpt[of "enat ?b" "0\<^sub>B"] by simp
            thus ?thesis unfolding MarkedB_def by auto
          qed
          show ?thesis using tv kv df df2 nzT mb1 mb2 nzM by simp
        next
          case t1ne: False
          \<comment> \<open>(B) \<open>t\<^sub>1 \<noteq> 0\<close>: the dedicated hard-branch lemma\<close>
          have IHt1: "dfree_BT (Trans (Pred M))" using IHp by simp
          have IHmk: "\<And>m'. (Pred M, m') \<in> Marked
                       \<Longrightarrow> dfree_BT (Mark (Pred M) m')
                         \<and> (Trans (Pred M), Mark (Pred M) m') \<in> MarkedB"
            using IHp by simp
          have res: "dfree_BT (Trans M) \<and> Trans M \<noteq> 0\<^sub>B
              \<and> (\<forall>m. (M, m) \<in> Marked
                     \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
            by (rule trans_inv_B_hard[OF MR mono L t1ne IHt1 IHmk])
          show ?thesis using res by blast
        qed
      next
        case nmono: False
        \<comment> \<open>(C) multiT branch: the dedicated lemma\<close>
        have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
        have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
        have Acut_RT: "take (Pcut M) M \<in> RT_PS"
          by (rule trans_multiT_prefix_RT_PS[OF MR muM])
        have LA: "Lng (take (Pcut M) M) < Lng M"
        proof -
          have "Pcut M < Lng M" using cut L by linarith
          thus ?thesis by (simp add: min_def)
        qed
        have PJeq: "P M ! (Lng (P M) - 1) = drop (Pcut M) M"
          by (rule trans_multiT_last_component(1)[OF MT muM])
        have Pne: "P M \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
        have PJ_RT: "drop (Pcut M) M \<in> RT_PS"
          using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
        have LPJ: "Lng (drop (Pcut M) M) < Lng M"
        proof -
          have "Lng (drop (Pcut M) M) = Lng M - Pcut M" by simp
          thus ?thesis using cut L by linarith
        qed
        note IHA = less.IH[OF LA, THEN mp, OF Acut_RT]
        note IHJ = less.IH[OF LPJ, THEN mp, OF PJ_RT]
        have dfTA: "dfree_BT (Trans (take (Pcut M) M))" using IHA by simp
        have dfTJ: "dfree_BT (Trans (drop (Pcut M) M))" using IHJ by simp
        have nzTJ: "\<not> zeroT (drop (Pcut M) M) \<Longrightarrow> Trans (drop (Pcut M) M) \<noteq> 0\<^sub>B"
          using IHJ by simp
        have IHmkJ: "\<And>m'. (drop (Pcut M) M, m') \<in> Marked
                     \<Longrightarrow> dfree_BT (Mark (drop (Pcut M) M) m')
                       \<and> (Trans (drop (Pcut M) M), Mark (drop (Pcut M) M) m')
                          \<in> MarkedB"
          using IHJ by simp
        have res: "dfree_BT (Trans M) \<and> Trans M \<noteq> 0\<^sub>B
            \<and> (\<forall>m. (M, m) \<in> Marked
                   \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
          by (rule trans_inv_C[OF MR muM dfTA dfTJ nzTJ IHmkJ])
        show ?thesis using res by blast
      qed
    qed
  qed
qed

text \<open>The article's well-definedness value-part, as clean corollaries.\<close>

lemma m_7_3_Trans_in_T_B:
  assumes "M \<in> RT_PS"
  shows "Trans M \<in> T_B"
  using Trans_Mark_invariant_aux assms by (simp add: T_B_def)

lemma m_7_3_Mark_in_T_B:
  assumes "M \<in> RT_PS" and "(M, m) \<in> Marked"
  shows "Mark M m \<in> T_B"
  using Trans_Mark_invariant_aux assms by (simp add: T_B_def)

lemma m_7_3_Trans_Mark_MarkedB:
  assumes "M \<in> RT_PS" and "(M, m) \<in> Marked"
  shows "(Trans M, Mark M m) \<in> MarkedB"
  using Trans_Mark_invariant_aux assms by simp


section \<open>§7.3 命題（\<open>Trans\<close>が零項性を保つこと）— content.md 2254\<close>

text \<open>The article states \<open>M \<in> T\<^sub>PS \<Longrightarrow> (zeroT M \<longleftrightarrow> Trans M = 0)\<close>, reducing
  to the reduced case by \<open>Red\<close>-zero-preservation and the \<open>(IncrFirst,Red)\<close>-invariant
  \<open>P\<close>-equivariance.  Since \<open>Trans\<close> is well-defined only on \<open>RT\<^sub>PS\<close> (the A15/A4
  caveat: \<open>Red\<close> idempotency is false on \<open>T\<^sub>PS\<close>), we state it on \<open>RT\<^sub>PS\<close>.
  \<open>\<Longleftarrow>\<close> is the contrapositive of the value invariant's
  \<open>\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<close> conjunct; \<open>\<Longrightarrow>\<close> reduces \<open>M\<close> to \<open>[(0,0)]\<close> via
  @{thm [source] m_6_6_oneColumn} and evaluates @{thm [source] Trans_singleton}.\<close>

lemma m_7_3_Trans_zeroT:
  assumes MR: "M \<in> RT_PS"
  shows "zeroT M \<longleftrightarrow> Trans M = 0\<^sub>B"
proof
  assume z: "zeroT M"
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L1: "Lng M = 1" using z by (simp add: zeroT_def)
  obtain v where Mv: "M = [(v, v)]"
    using m_6_6_oneColumn[OF MT] MR L1 by auto
  have "entry M 1 0 = 0" using z by (simp add: zeroT_def)
  hence "v = 0" using Mv by (simp add: entry_def)
  hence "M = [(0, 0)]" using Mv by simp
  thus "Trans M = 0\<^sub>B" using Trans_singleton[of 0] by simp
next
  assume t: "Trans M = 0\<^sub>B"
  have "\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<^sub>B"
    using Trans_Mark_invariant_aux MR by blast
  thus "zeroT M" using t by blast
qed


section \<open>Term-level \<open>lessBT\<close> facts about \<open>+\<^sub>B\<close> (end-context inequality extension)\<close>

text \<open>The building blocks of the article's 部分表現の不等式の延長性 (content.md 1749)
  for the special case of an \<^emph>\<open>end\<close>-context (\<open>b = ()\<close>): appending on the right of
  a principal-term list.  (E1) appending a non-zero term strictly increases;
  (E2) \<open>+\<^sub>B\<close> is strictly monotone in its right argument.  Both are purely
  lexicographic facts about @{const lessBT} (\<open>+\<^sub>B\<close> = list \<open>@\<close> on the principal
  lists), proved by induction on the common prefix.  Used by the §7.3 \<open>Pred\<close>-on-
  \<open>Trans\<close> descent (the multi-recursion step \<open>Trans M = Trans A +\<^sub>B (\<dots>)\<close>).\<close>

lemma lessBT_addBT_self:
  assumes "c \<noteq> 0\<^sub>B"
  shows "lessBT t (t +\<^sub>B c)"
proof -
  obtain ts where t: "t = Trm ts" by (cases t)
  obtain cs where c: "c = Trm cs" by (cases c)
  have cs: "cs \<noteq> []" using assms c by auto
  have "lessBT (Trm ts) (Trm (ts @ cs))"
    by (induction ts) (simp_all add: cs)
  thus ?thesis using t c by simp
qed

lemma lessBT_addBT_mono_right:
  assumes "lessBT a b"
  shows "lessBT (t +\<^sub>B a) (t +\<^sub>B b)"
proof -
  obtain ts where t: "t = Trm ts" by (cases t)
  obtain as where a: "a = Trm as" by (cases a)
  obtain bs where b: "b = Trm bs" by (cases b)
  have "lessBT (Trm (ts @ as)) (Trm (ts @ bs))"
    using assms a b by (induction ts) simp_all
  thus ?thesis using t a b by simp
qed


section \<open>§7.3 部分表現の不等式の延長性 (scb inequality-extension, content.md 1749)\<close>

text \<open>The join-sweep helper for the strict-order extension: in a \<open>CM\<close>-joined
  component list closed by the outer \<open>RP\<close>, an occurrence of a principal string
  \<open>flatBP cp\<close> with all-\<open>RP\<close> tail \<open>b\<close> lies inside a single component, and only the
  LAST one (boundary-crossing gives a negative \<open>flatinj_dsum\<close> proper prefix,
  contradicting @{thm [source] flatinj_prefix_nonneg_BP}).  Replacing that
  component by a \<open>lessBP\<close>-larger one (supplied by the inductive hypothesis) makes
  the whole join-list \<open>lessBT\<close>-larger.  This mirrors @{thm [source] scbimg_join}
  but carries the strict-order conclusion instead of bare existence.\<close>

lemma scbjoin_lessBT:
  assumes IHr: "\<And>r s b. r \<in> set rs \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                  \<Longrightarrow> \<forall>x \<in> set b. x = RP \<Longrightarrow> lessBP cp cp'
                  \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b \<and> lessBP r r'"
    and eq: "concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = s @ flatBP cp @ b"
    and rb: "\<forall>x \<in> set b. x = RP"
    and lt: "lessBP cp cp'"
  shows "\<exists>rs'. length rs' = length rs
             \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = s @ flatBP cp' @ b
             \<and> lessBT (Trm rs) (Trm rs')"
  using IHr eq rb
proof (induction rs arbitrary: s b)
  case Nil
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?case
    using Nil.prems(2) cpw by (cases s) auto
next
  case (Cons r0 rs)
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  have fchd: "flatBP cp = Dsym w # flatBT cb" using cpw by simp
  have eq0: "CM # flatBP r0 @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
             = s @ flatBP cp @ b"
    using Cons.prems(2) by simp
  have sne: "s \<noteq> []"
  proof
    assume "s = []"
    hence "CM = Dsym w" using eq0 fchd by simp
    thus False by simp
  qed
  then obtain s1 where ss: "s = CM # s1"
    using eq0 by (cases s) auto
  have eq1: "flatBP r0 @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
             = s1 @ flatBP cp @ b"
    using eq0 ss by simp
  from append_eq_append_conv2[THEN iffD1, OF eq1]
  obtain us where split:
      "flatBP r0 = s1 @ us \<and> us @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = flatBP cp @ b
     \<or> flatBP r0 @ us = s1 \<and> concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = us @ flatBP cp @ b" by blast
  show ?case
  proof (cases "flatBP r0 @ us = s1 \<and> concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = us @ flatBP cp @ b")
    case True
    \<comment> \<open>occurrence beyond \<open>r0\<close>: recurse into the tail join; \<open>r0\<close> kept unchanged\<close>
    have IHtail: "\<And>r s b. r \<in> set rs \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                    \<Longrightarrow> \<forall>x \<in> set b. x = RP \<Longrightarrow> lessBP cp cp'
                    \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b \<and> lessBP r r'"
      using Cons.prems(1) by simp
    have tail: "concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = us @ flatBP cp @ b"
      using True by simp
    have "\<exists>rs'. length rs' = length rs
              \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b
              \<and> lessBT (Trm rs) (Trm rs')"
      by (rule Cons.IH[OF IHtail tail Cons.prems(3)])
    then obtain rs' where rs': "length rs' = length rs"
        "concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b"
        "lessBT (Trm rs) (Trm rs')" by blast
    have lentl: "lessBT (Trm (r0 # rs)) (Trm (r0 # rs'))"
      using rs'(3) by simp
    have "concat (map (\<lambda>r. CM # flatBP r) (r0 # rs')) @ [RP]
          = CM # flatBP r0 @ us @ flatBP cp' @ b" using rs'(2) by simp
    also have "\<dots> = s @ flatBP cp' @ b" using ss True by simp
    finally show ?thesis using rs'(1) lentl
      by (intro exI[of _ "r0 # rs'"]) simp
  next
    case False
    with split have inr0: "flatBP r0 = s1 @ us"
        and rest: "us @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = flatBP cp @ b"
      by auto
    from append_eq_append_conv2[THEN iffD1, OF rest[symmetric]]
    obtain vs where split2:
        "flatBP cp = us @ vs \<and> vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
       \<or> flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
      by blast
    show ?thesis
    proof (cases "flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]")
      case True
      \<comment> \<open>occurrence wholly inside \<open>r0\<close>: tail of \<open>b\<close> forces \<open>rs = []\<close>\<close>
      have ball: "\<forall>x \<in> set (vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]). x = RP"
        using True Cons.prems(3) by simp
      have rsnil: "rs = []"
      proof (cases rs)
        case (Cons r1 rs1)
        hence "CM \<in> set (concat (map (\<lambda>r. CM # flatBP r) rs))" by simp
        thus ?thesis using ball by auto
      qed simp
      have vsRP: "\<forall>x \<in> set vs. x = RP" using ball by auto
      have r0eq: "flatBP r0 = s1 @ flatBP cp @ vs" using inr0 True by simp
      obtain r0' where r0': "flatBP r0' = s1 @ flatBP cp' @ vs" "lessBP r0 r0'"
        using Cons.prems(1)[of r0 s1 vs] r0eq vsRP lt by auto
      have "lessBT (Trm [r0]) (Trm [r0'])" using r0'(2) by simp
      hence lentl: "lessBT (Trm (r0 # rs)) (Trm (r0' # rs))" using rsnil by simp
      have "concat (map (\<lambda>r. CM # flatBP r) [r0']) @ [RP]
            = CM # s1 @ flatBP cp' @ vs @ [RP]" using r0'(1) by simp
      also have "\<dots> = s @ flatBP cp' @ b" using ss True rsnil by simp
      finally show ?thesis using rsnil lentl
        by (intro exI[of _ "[r0']"]) simp
    next
      case False
      with split2 have fcsplit: "flatBP cp = us @ vs"
          and vsb: "vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]" by auto
      have vsne: "vs \<noteq> []"
      proof
        assume v0: "vs = []"
        hence "flatBP cp = us" using fcsplit by simp
        hence "b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]" using vsb v0 by simp
        hence "flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
          using fcsplit v0 vsb by simp
        thus False using False by simp
      qed
      show ?thesis
      proof (cases "us = []")
        case True
        have "flatBP cp = vs" using fcsplit True by simp
        hence hd: "hd (vs @ b) = Dsym w" using fchd vsne by (cases vs) auto
        have "hd (concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]) = CM
              \<or> hd (concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]) = RP"
          by (cases rs) auto
        thus ?thesis using vsb hd by auto
      next
        case False
        have dsus_neg: "flatinj_dsum us < 0"
        proof -
          have "flatinj_dsum (flatBP r0) = -1"
            by (rule flatinj_dsum_flatBP)
          moreover have "0 \<le> flatinj_dsum s1"
            using flatinj_prefix_nonneg_BP[OF inr0] False by simp
          moreover have "flatinj_dsum (flatBP r0) = flatinj_dsum s1 + flatinj_dsum us"
            using inr0 by simp
          ultimately show ?thesis by simp
        qed
        have "0 \<le> flatinj_dsum us"
          using flatinj_prefix_nonneg_BP[OF fcsplit] vsne by simp
        thus ?thesis using dsus_neg by simp
      qed
    qed
  qed
qed


text \<open>部分表現の不等式の延長性 (content.md 1749): replacing a principal sub-term
  \<open>cp\<close> (a \<open>BP\<close>) by a \<open>lessBP\<close>-larger principal \<open>cp'\<close> at a fixed scb position
  (common prefix \<open>s\<close>, common all-\<open>RP\<close> tail \<open>b\<close>) is strictly monotone for the
  Buchholz order: the whole terms satisfy \<open>lessBT t t'\<close> / \<open>lessBP p p'\<close>.
  Empirically 0/114,000 mismatches.  Same induction as
  @{thm [source] scbimg_image_BT}, but the comparison target's structure is read
  off the given decomposition via @{thm [source] m_7_flatBT_inj}.\<close>

lemma scbext_lessBT:
  "flatBT t = s @ flatBP cp @ b \<Longrightarrow> flatBT t' = s @ flatBP cp' @ b
   \<Longrightarrow> (\<forall>x \<in> set b. x = RP) \<Longrightarrow> lessBP cp cp' \<Longrightarrow> lessBT t t'"
  and scbext_lessBP:
  "flatBP p = s @ flatBP cp @ b \<Longrightarrow> flatBP p' = s @ flatBP cp' @ b
   \<Longrightarrow> (\<forall>x \<in> set b. x = RP) \<Longrightarrow> lessBP cp cp' \<Longrightarrow> lessBP p p'"
proof (induct t and p arbitrary: s b t' and s b p' rule: flatBT_flatBP.induct)
  case (1 s b t')
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?case using 1(1) cpw by (cases s) auto
next
  case (2 p s b t')
  \<comment> \<open>\<open>flatBT (Trm [p]) = flatBP p\<close>; recover \<open>t' = Trm [p']\<close> from its flat string.\<close>
  have ep: "flatBP p = s @ flatBP cp @ b" using 2(2) by simp
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  obtain pu pa where pp: "p = DB pu pa" by (cases p) auto
  obtain tps where tt': "t' = Trm tps" by (cases t')
  have ftt': "flatBT (Trm tps) = s @ flatBP cp' @ b" using 2(3) tt' by simp
  have tps_ne: "tps \<noteq> []"
  proof
    assume "tps = []"
    hence "[Zsym] = s @ flatBP cp' @ b" using ftt' by simp
    moreover obtain w' cb' where "cp' = DB w' cb'" using 2(5) cpw by (cases cp') auto
    ultimately show False by (cases s) auto
  qed
  show ?case
  proof (cases tps)
    case (Cons p' rest)
    show ?thesis
    proof (cases rest)
      case Nil
      \<comment> \<open>single principal: \<open>flatBT t' = flatBP p'\<close>, apply IH \<open>scbext_lessBP\<close>.\<close>
      have ep': "flatBP p' = s @ flatBP cp' @ b" using ftt' Cons Nil by simp
      have "lessBP p p'" using 2(1)[OF ep ep' 2(4) 2(5)] .
      thus ?thesis using tt' Cons Nil by simp
    next
      case (Cons q' qs')
      \<comment> \<open>tuple \<open>t' = Trm (p' # q' # qs')\<close>: its flat head is \<open>LP\<close>, but the head of
          \<open>s @ flatBP cp' @ b\<close> equals the head of \<open>flatBP p\<close> (\<open>= Dsym pu\<close>): clash.\<close>
      have tps3: "tps = p' # q' # qs'" using \<open>tps = p' # rest\<close> Cons by simp
      have "s @ flatBP cp' @ b = flatBT (Trm (p' # q' # qs'))"
        using ftt' tps3 by simp
      hence hdLP: "hd (s @ flatBP cp' @ b) = LP" by simp
      have "hd (s @ flatBP cp' @ b) \<noteq> LP"
      proof (cases s)
        case Nil
        obtain w' cb' where cp'w: "cp' = DB w' cb'" using 2(5) cpw by (cases cp') auto
        show ?thesis using Nil cp'w by simp
      next
        case (Cons c cs)
        \<comment> \<open>head \<open>= c\<close>, also the head of \<open>flatBP p = s @ flatBP cp @ b\<close>, i.e. \<open>Dsym pu\<close>\<close>
        have "c = Dsym pu" using ep pp Cons by simp
        thus ?thesis using Cons by simp
      qed
      thus ?thesis using hdLP by simp
    qed
  qed (use tps_ne in simp)
next
  case (3 p q ps s b t')
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  have fchd: "flatBP cp = Dsym w # flatBT cb" using cpw by simp
  let ?JOIN = "concat (map (\<lambda>r. CM # flatBP r) (q # ps))"
  have flat3: "flatBT (Trm (p # q # ps)) = LP # (flatBP p @ ?JOIN) @ [RP]" by simp
  have sne: "s \<noteq> []"
  proof
    assume "s = []"
    hence "LP = Dsym w" using 3(3) fchd flat3 by simp
    thus False by simp
  qed
  then obtain s1 where ss: "s = LP # s1" using 3(3) flat3 by (cases s) auto
  have eq1: "flatBP p @ ?JOIN @ [RP] = s1 @ flatBP cp @ b"
    using 3(3) flat3 ss by simp
  from append_eq_append_conv2[THEN iffD1, OF eq1]
  obtain us where split:
      "flatBP p = s1 @ us \<and> us @ ?JOIN @ [RP] = flatBP cp @ b
     \<or> flatBP p @ us = s1 \<and> ?JOIN @ [RP] = us @ flatBP cp @ b" by blast
  show ?case
  proof (cases "flatBP p @ us = s1 \<and> ?JOIN @ [RP] = us @ flatBP cp @ b")
    case True
    \<comment> \<open>occurrence in the join: first component \<open>p\<close> unchanged, replace inside join.\<close>
    have IHr: "\<And>r s b. r \<in> set (q # ps) \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                 \<Longrightarrow> \<forall>x \<in> set b. x = RP \<Longrightarrow> lessBP cp cp'
                 \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b \<and> lessBP r r'"
    proof -
      fix r s b
      assume rin: "r \<in> set (q # ps)" and req: "flatBP r = s @ flatBP cp @ b"
        and rrb: "\<forall>x \<in> set b. x = RP" and rlt: "lessBP cp cp'"
      obtain r' where r': "flatBP r' = s @ flatBP cp' @ b"
        using scbimg_image_BP[OF req rrb] by blast
      have "lessBP r r'" using 3(2)[OF rin req r' rrb rlt] .
      thus "\<exists>r'. flatBP r' = s @ flatBP cp' @ b \<and> lessBP r r'"
        using r' by blast
    qed
    have joineq: "concat (map (\<lambda>r. CM # flatBP r) (q # ps)) @ [RP] = us @ flatBP cp @ b"
      using True by simp
    have "\<exists>rs'. length rs' = length (q # ps)
              \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b
              \<and> lessBT (Trm (q # ps)) (Trm rs')"
      by (rule scbjoin_lessBT[where cp = cp, OF IHr joineq 3(5) 3(6)])
    then obtain rs' where rs': "length rs' = length (q # ps)"
        "concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b"
        "lessBT (Trm (q # ps)) (Trm rs')" by blast
    obtain r1' rest' where rsc: "rs' = r1' # rest'"
      using rs' by (cases rs') auto
    have "flatBT (Trm (p # r1' # rest'))
          = LP # flatBP p @ (concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP])"
      using rsc by simp
    also have "\<dots> = LP # flatBP p @ us @ flatBP cp' @ b" using rs'(2) by simp
    also have "\<dots> = s @ flatBP cp' @ b" using ss True by simp
    also have "\<dots> = flatBT t'" using 3(4) by simp
    finally have eqt': "flatBT (Trm (p # r1' # rest')) = flatBT t'" .
    have "lessBT (Trm (p # q # ps)) (Trm (p # r1' # rest'))"
      using rs'(3) rsc by simp
    moreover have "t' = Trm (p # r1' # rest')"
      using m_7_flatBT_inj[OF eqt'[symmetric]] .
    ultimately show ?thesis by simp
  next
    case False
    with split have inp: "flatBP p = s1 @ us"
        and rest: "us @ ?JOIN @ [RP] = flatBP cp @ b" by auto
    \<comment> \<open>occurrence (purportedly) in the first component: impossible (as in scbimg)\<close>
    from append_eq_append_conv2[THEN iffD1, OF rest]
    obtain vs where split2:
        "us = flatBP cp @ vs \<and> vs @ ?JOIN @ [RP] = b
       \<or> us @ vs = flatBP cp \<and> ?JOIN @ [RP] = vs @ b" by blast
    have False
    proof (cases "us = flatBP cp @ vs \<and> vs @ ?JOIN @ [RP] = b")
      case True
      hence "CM \<in> set b" by auto
      thus False using 3(5) by auto
    next
      case False
      with split2 have fcsplit: "us @ vs = flatBP cp"
          and jrest: "?JOIN @ [RP] = vs @ b" by auto
      show False
      proof (cases "us = []")
        case True
        hence "vs = flatBP cp" using fcsplit by simp
        hence hdD: "hd (vs @ b) = Dsym w" using fchd by simp
        have "vs @ b = CM # flatBP q @ concat (map (\<lambda>r. CM # flatBP r) ps) @ [RP]"
          using jrest by simp
        hence "hd (vs @ b) = CM" by simp
        thus False using hdD by simp
      next
        case usne: False
        have vsne: "vs \<noteq> []"
        proof
          assume v0: "vs = []"
          hence "?JOIN @ [RP] = b" using jrest by simp
          hence "CM \<in> set b" by auto
          thus False using 3(5) by auto
        qed
        have "flatinj_dsum us < 0"
        proof -
          have "flatinj_dsum (flatBP p) = -1" by (rule flatinj_dsum_flatBP)
          moreover have "0 \<le> flatinj_dsum s1"
            using flatinj_prefix_nonneg_BP[OF inp usne] .
          moreover have "flatinj_dsum (flatBP p) = flatinj_dsum s1 + flatinj_dsum us"
            using inp by simp
          ultimately show ?thesis by simp
        qed
        moreover have "0 \<le> flatinj_dsum us"
          using flatinj_prefix_nonneg_BP[OF fcsplit[symmetric] vsne] .
        ultimately show False by simp
      qed
    qed
    thus ?thesis ..
  qed
next
  case (4 u a s b p')
  show ?case
  proof (cases "s = []")
    case True
    \<comment> \<open>\<open>s = []\<close>: \<open>flatBP (DB u a) = flatBP cp @ b\<close>, all-\<open>RP\<close> \<open>b\<close> forces \<open>b = []\<close>,
        \<open>cp = DB u a\<close>; likewise \<open>p' = cp'\<close>; the goal is the given \<open>lessBP cp cp'\<close>.\<close>
    obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
    obtain w' cb' where cpw': "cp' = DB w' cb'" by (cases cp')
    obtain pu' pa' where pp': "p' = DB pu' pa'" by (cases p')
    have e: "flatBP (DB u a) @ [] = flatBP cp @ b" using 4(2) True by simp
    have cpeq: "flatBP (DB u a) = flatBP cp"
      using flatinj_flatBP_cancel[OF e] by blast
    \<comment> \<open>\<open>Dsym u # flatBT a = Dsym w # flatBT cb\<close>: split into head + body\<close>
    have ua: "u = w" and acb: "flatBT a = flatBT cb" using cpeq cpw by auto
    have p1: "DB u a = cp" using ua acb cpw m_7_flatBT_inj by simp
    have e': "flatBP p' @ [] = flatBP cp' @ b" using 4(3) True by simp
    have cpeq': "flatBP p' = flatBP cp'"
      using flatinj_flatBP_cancel[OF e'] by blast
    have ua': "pu' = w'" and acb': "flatBT pa' = flatBT cb'"
      using cpeq' cpw' pp' by auto
    have p2: "p' = cp'" using ua' acb' cpw' pp' m_7_flatBT_inj by simp
    show ?thesis using p1 p2 4(5) by simp
  next
    case False
    have "Dsym u # flatBT a = s @ flatBP cp @ b" using 4(2) by simp
    then obtain s1 where ss: "s = Dsym u # s1" and aeq: "flatBT a = s1 @ flatBP cp @ b"
      using False by (cases s) auto
    obtain pu' pa' where pp': "p' = DB pu' pa'" by (cases p')
    have "Dsym pu' # flatBT pa' = s @ flatBP cp' @ b" using 4(3) pp' by simp
    hence headeq: "Dsym pu' = Dsym u" and aeq': "flatBT pa' = s1 @ flatBP cp' @ b"
      using ss by auto
    have "lessBT a pa'" using 4(1)[OF aeq aeq' 4(4) 4(5)] .
    hence "lessBP (DB u a) (DB u pa')" by simp
    thus ?thesis using pp' headeq by simp
  qed
qed


section \<open>§7.3 \<open>c\<^sub>2\<close> is a single principal term (claim (2) of \<open>p_7_3_c1_c2\<close>)\<close>

text \<open>\<open>transC2 M\<close> is unconditionally of the form \<open>D\<^sub>v(\<dots>)\<close> (every branch of the
  case definition is \<open>Dpt v _\<close>), hence has exactly one principal component.
  This discharges claim (2) of the article's 命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係）
  (content.md 2270) with no hypotheses.\<close>

lemma Lng_PB_Dpt [simp]: "Lng (PB (Dpt v t)) = 1"
  by (simp add: PB_def)

lemma transC2_single_principal: "Lng (PB (transC2 M)) = 1"
  by (simp add: transC2_def Let_def)


section \<open>§7.3 \<open>c\<^sub>1\<close> is a single principal term (claim (1) of \<open>p_7_3_c1_c2\<close>)\<close>

text \<open>A flat string that IS a principal term's flat (\<open>isPTB_str\<close>) has exactly one
  principal component (\<open>c = Trm [p]\<close> by injectivity of @{const flatBT}).\<close>

lemma isPTB_str_imp_Lng_PB_1:
  assumes "isPTB_str (flatBT c)"
  shows "Lng (PB c) = 1"
proof -
  from assms obtain p where p: "flatBT c = flatBP p"
    by (auto simp: isPTB_str_def)
  have "flatBT c = flatBT (Trm [p])" using p by simp
  hence "c = Trm [p]" by (rule m_7_flatBT_inj)
  thus ?thesis by (simp add: PB_def)
qed

text \<open>Claim (1) of 命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係） (content.md 2270): under the
  recursion's branch conditions (\<open>M\<close> reduced \<open>\<and>\<close> mono, \<open>j\<^sub>1 > 0\<close>, \<open>t\<^sub>1 \<noteq> 0\<close>),
  \<open>c\<^sub>1 = Mark(Pred M)(j\<^sub>-\<^sub>1)\<close> is a single principal term.  Article reason
  (content.md 2110): \<open>(t\<^sub>1, c\<^sub>1) \<in> T\<^bsub>B\<^esub>\<^sup>Marked\<close> and \<open>t\<^sub>1 \<noteq> 0\<close> give \<open>c\<^sub>1 \<in> PT\<^bsub>B\<^esub>\<close>.
  Here \<open>(t\<^sub>1, c\<^sub>1) \<in> MarkedB\<close> comes from the value invariant on \<open>Pred M\<close> with the
  \<open>c\<^sub>1\<close>-call membership @{thm [source] Marked_Pred_Adm}, and the scb-decomposition's
  \<open>isPTB_str\<close> side condition (valid since \<open>t\<^sub>1 \<noteq> 0\<^sub>B\<close>) pins \<open>c\<^sub>1\<close> to one principal.\<close>

lemma transC1_single_principal:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
  shows "Lng (PB (transC1 M)) = 1"
proof -
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using J1 by (simp add: transJ1_def)
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  have mkd: "(Pred M, Adm M (parent M 0 (Lng M - 1))) \<in> Marked"
    by (rule Marked_Pred_Adm[OF MT L hp])
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have c1eq: "transC1 M = Mark (Pred M) (Adm M (parent M 0 (Lng M - 1)))"
    by (simp add: transC1_def transJm1_def transJ0_def transJ1_def)
  have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B" using T1 by (simp add: transT1_def)
  have inv: "(Trans (Pred M), Mark (Pred M) (Adm M (parent M 0 (Lng M - 1)))) \<in> MarkedB"
    using Trans_Mark_invariant_aux predRT mkd by blast
  then obtain s b where
    sd: "scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b"
    using c1eq by (auto simp: MarkedB_def)
  have "isPTB_str (flatBT (transC1 M))"
    using sd t1ne by (simp add: scb_decomp_def)
  thus ?thesis by (rule isPTB_str_imp_Lng_PB_1)
qed


section \<open>§7.3 命題（右端第1基点の \<open>Mark\<close> の基本性質）— content.md 2294 (forward)\<close>

text \<open>For a NON-zero reduced pair sequence \<open>M\<close>, the rightmost mark
  \<open>m = j\<^sub>1 = Lng M - 1\<close> is the single principal \<open>D\<^bsub>M\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0\<close>.  Proved by
  \<open>Lng\<close>-strong induction, evaluating \<open>Mark M (Lng M - 1)\<close> by the conditional
  recursion @{thm [source] Mark.psimps} (domain from
  @{thm [source] m_7_3_Mark_welldef}), collapsing only the OUTER ifs to reach
  the wanted branch.  The excluded zero base \<open>[(0,0)]\<close> is the sole counterexample
  (correction A17), hence the \<open>\<not> zeroT M\<close> hypothesis.\<close>

lemma Mark_rightmost1_forward:
  assumes "M \<in> RT_PS" and "\<not> zeroT M" and "(M, Lng M - 1) \<in> Marked"
  shows "Mark M (Lng M - 1) = Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B"
proof -
  have "M \<in> RT_PS \<longrightarrow> \<not> zeroT M \<longrightarrow> (M, Lng M - 1) \<in> Marked
        \<longrightarrow> Mark M (Lng M - 1) = Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B"
  proof (induction M rule: measure_induct_rule[where f=Lng])
    case (less M)
    show ?case
    proof (intro impI)
      assume MR: "M \<in> RT_PS" and nzM: "\<not> zeroT M" and mM: "(M, Lng M - 1) \<in> Marked"
      have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
      have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
      have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
      let ?j1 = "Lng M - 1"
      show "Mark M ?j1 = Dpt (enat (entry M 1 ?j1)) 0\<^sub>B"
      proof (cases "Lng M = 1")
        case True
        \<comment> \<open>(A) base length 1, \<open>j\<^sub>1 = 0\<close>: \<open>M = [(v,v)]\<close> with \<open>v > 0\<close>\<close>
        obtain v where Mv: "M = [(v, v)]"
          using m_6_6_oneColumn[OF MT] MR True by auto
        have v0: "v \<noteq> 0" using nzM Mv by (simp add: zeroT_def entry_def)
        have j10: "?j1 = 0" using True by simp
        have "Mark M ?j1 = Dpt (enat v) 0\<^sub>B" using Mv Mark_singleton v0 j10 by simp
        moreover have "entry M 1 ?j1 = v" using Mv j10 by (simp add: entry_def)
        ultimately show ?thesis by simp
      next
        case notone: False
        have L: "1 < Lng M" using Mne notone by (cases M) auto
        have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
        have j1pos: "0 < ?j1" using L by simp
        show ?thesis
        proof (cases "monoT M")
          case mono: True
          have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
          show ?thesis
          proof (cases "Trans (Pred M) = 0\<^sub>B")
            case t1z: True
            \<comment> \<open>(B) mono, \<open>t\<^sub>1 = 0\<close>: branch yields \<open>Dpt (entry M 1 j\<^sub>1) 0\<close> since \<open>j\<^sub>1 \<noteq> 0\<close>\<close>
            have kv: "Mark M ?j1 = (if ?j1 = 0 then Dpt 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)
                                    else Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
              using Mark.psimps[OF domK] MR Lgt1 mono t1z by (simp add: Let_def)
            show ?thesis using kv j1pos by simp
          next
            case t1ne: False
            \<comment> \<open>(B) mono, \<open>t\<^sub>1 \<noteq> 0\<close>: outer \<open>if m < j\<^sub>1\<close> is False (\<open>m = j\<^sub>1\<close>)\<close>
            have c1: "(M \<notin> RT_PS) = False" using MR by simp
            have c2: "(?j1 = 0) = False" using j1pos by simp
            have c3: "monoT M = True" using mono by simp
            have c4: "(Trans (Pred M) = 0\<^sub>B) = False" using t1ne by simp
            have c5: "(?j1 < ?j1) = False" by simp
            show ?thesis
              by (subst Mark.psimps[OF domK])
                 (simp only: c1 c2 c3 c4 c5 if_False if_True Let_def)
          qed
        next
          case nmono: False
          \<comment> \<open>(C) multiT branch\<close>
          have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
          have cut: "0 < Pcut M \<and> Pcut M \<le> ?j1" using Pcut_le[OF L] by simp
          let ?PJ = "drop (Pcut M) M"
          have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
            by (rule trans_multiT_last_component(1)[OF MT muM])
          have LdJ: "Lng (drop (Pcut M) M) = Lng M - Pcut M" by simp
          have meq2: "\<And>m. m - (?j1 - Lng (drop (Pcut M) M) + 1) = m - Pcut M"
          proof -
            fix m
            have "?j1 - Lng (drop (Pcut M) M) + 1 = Pcut M"
              using LdJ Pcut_le[OF L] by linarith
            thus "m - (?j1 - Lng (drop (Pcut M) M) + 1) = m - Pcut M" by simp
          qed
          have c1: "(M \<notin> RT_PS) = False" using MR by simp
          have c2: "(?j1 = 0) = False" using j1pos by simp
          have c3: "monoT M = False" using nmono by simp
          have markM: "\<And>m. Mark M m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                                        else Mark ?PJ (m - Pcut M))"
          proof -
            fix m
            have raw: "Mark M m =
                (if P M ! (Lng (P M) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
                 else Mark (P M ! (Lng (P M) - 1))
                        (m - (?j1 - Lng (P M ! (Lng (P M) - 1)) + 1)))"
              by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
            show "Mark M m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B else Mark ?PJ (m - Pcut M))"
              unfolding raw PJeq meq2 ..
          qed
          \<comment> \<open>last column of \<open>?PJ\<close> = last column of \<open>M\<close>\<close>
          have LPJ: "Lng ?PJ = Lng M - Pcut M" by simp
          have PJne: "?PJ \<noteq> []" using cut LPJ L by (cases ?PJ) auto
          have lastcol: "entry ?PJ 1 (Lng ?PJ - 1) = entry M 1 ?j1"
          proof -
            have pl: "Pcut M < Lng M" using cut L by linarith
            have idx: "Pcut M + (Lng ?PJ - 1) = ?j1" using LPJ cut pl by linarith
            have "?PJ ! (Lng ?PJ - 1) = M ! (Pcut M + (Lng ?PJ - 1))"
              by (rule nth_drop) (use LPJ cut pl in linarith)
            also have "\<dots> = M ! ?j1" using idx by simp
            finally have "?PJ ! (Lng ?PJ - 1) = M ! ?j1" .
            thus ?thesis by (simp add: entry_def)
          qed
          show ?thesis
          proof (cases "?PJ = [(0, 0)]")
            case True
            \<comment> \<open>last column is \<open>(0,0)\<close>, so \<open>entry M 1 j\<^sub>1 = 0\<close>\<close>
            have "entry ?PJ 1 (Lng ?PJ - 1) = 0" using True by (simp add: entry_def)
            hence e0: "entry M 1 ?j1 = 0" using lastcol by simp
            have "Mark M ?j1 = Dpt 0 0\<^sub>B" using markM True by simp
            thus ?thesis using e0 by (simp add: zero_enat_def)
          next
            case False
            \<comment> \<open>recurse into \<open>?PJ\<close> (smaller \<open>Lng\<close>) via the IH\<close>
            have Pne: "P M \<noteq> []" by (rule P_nonempty)
            have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
            have PJRT: "?PJ \<in> RT_PS"
              using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
            have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
            have nzPJ: "\<not> zeroT ?PJ"
            proof
              assume z: "zeroT ?PJ"
              have L1: "Lng ?PJ = 1" using z by (simp add: zeroT_def)
              then obtain v where v: "?PJ = [(v, v)]"
                using m_6_6_oneColumn[OF PJT] PJRT by auto
              have "entry ?PJ 1 0 = 0" using z by (simp add: zeroT_def)
              hence "v = 0" using v by (simp add: entry_def)
              thus False using False v by simp
            qed
            have LPJlt: "Lng ?PJ < Lng M" using LPJ cut L by linarith
            have mPJ: "(?PJ, Lng ?PJ - 1) \<in> Marked"
            proof -
              have "(?PJ, ?j1 - Pcut M) \<in> Marked"
                by (rule multi_Marked_last_component(2)[OF MT muM mM])
              moreover have "?j1 - Pcut M = Lng ?PJ - 1" using LPJ cut L by linarith
              ultimately show ?thesis by simp
            qed
            have IH: "Mark ?PJ (Lng ?PJ - 1)
                      = Dpt (enat (entry ?PJ 1 (Lng ?PJ - 1))) 0\<^sub>B"
              using less.IH[OF LPJlt] PJRT nzPJ mPJ by blast
            have meq: "?j1 - Pcut M = Lng ?PJ - 1" using LPJ cut L by linarith
            have "Mark M ?j1 = Mark ?PJ (?j1 - Pcut M)" using markM False by simp
            also have "\<dots> = Mark ?PJ (Lng ?PJ - 1)" using meq by simp
            also have "\<dots> = Dpt (enat (entry ?PJ 1 (Lng ?PJ - 1))) 0\<^sub>B" using IH .
            also have "\<dots> = Dpt (enat (entry M 1 ?j1)) 0\<^sub>B" using lastcol by simp
            finally show ?thesis .
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed


section \<open>§7.3 \<open>c\<^sub>1 < c\<^sub>2\<close> (claim (3) of 命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係）, content.md 2270)\<close>

text \<open>Three helpers, then the main strict-inequality lemma.  The hard
  condition-VI sub-fact (\<open>t\<^sub>2 < D\<^bsub>M\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0\<close>) is isolated as the hypothesis
  \<open>VIfact\<close>; every other branch is discharged structurally.\<close>

lemma lessBT_Dpt_same [simp]: "lessBT (Dpt v a) (Dpt v b) = lessBT a b"
  by simp

lemma principal_reconstruct:
  assumes "Lng (PB c) = 1" shows "c = Dpt (bpHeadV c) (bpHeadT c)"
proof -
  obtain ps where cps: "c = Trm ps" by (cases c)
  from assms have "length ps = 1" by (simp add: PB_def cps)
  then obtain p where psp: "ps = [p]" by (cases ps) auto
  obtain w u where pwu: "p = DB w u" by (cases p)
  show ?thesis using cps psp pwu by simp
qed

lemma SigmaB_snoc: "SigmaB (xs @ [x]) = SigmaB xs +\<^sub>B x"
  by (cases x) (simp add: SigmaB_def)

lemma transC1_lessBT_transC2:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and VIfact: "transCondVI M \<Longrightarrow>
                   lessBT (transT2 M) (Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B)"
  shows "lessBT (transC1 M) (transC2 M)"
proof -
  define t2 where "t2 = transT2 M"
  define j1 where "j1 = transJ1 M"
  define jp where "jp = transJ0 M"
  define Dj1 where "Dj1 = Dpt (enat (entry M 1 j1)) 0\<^sub>B"
  have Dj1ne: "Dj1 \<noteq> 0\<^sub>B" by (simp add: Dj1_def)
  \<comment> \<open>1. \<open>c\<^sub>1\<close> is a single principal term\<close>
  have pc1: "Lng (PB (transC1 M)) = 1"
    by (rule transC1_single_principal[OF MR MP J1pos T1])
  \<comment> \<open>2. \<open>c\<^sub>1 = D\<^bsub>v\<^esub> t\<^sub>2\<close>\<close>
  have c1eq: "transC1 M = Dpt (transV M) t2"
    using principal_reconstruct[OF pc1]
    by (simp add: transV_def transT2_def t2_def)
  \<comment> \<open>3. \<open>t\<^sub>2 \<in> T\<^bsub>B\<^esub>\<close>\<close>
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using J1pos by (simp add: transJ1_def)
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  have mkd: "(Pred M, Adm M (parent M 0 (Lng M - 1))) \<in> Marked"
    by (rule Marked_Pred_Adm[OF MT L hp])
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have c1val: "transC1 M = Mark (Pred M) (Adm M (parent M 0 (Lng M - 1)))"
    by (simp add: transC1_def transJm1_def transJ0_def transJ1_def)
  have c1TB: "transC1 M \<in> T_B"
    using m_7_3_Mark_in_T_B[OF predRT mkd] c1val by simp
  have t2TB: "t2 \<in> T_B"
    using c1TB unfolding c1eq by (auto simp: T_B_def)
  \<comment> \<open>4. case split, reducing each branch of \<open>transC2\<close>\<close>
  show ?thesis
  proof (cases "transCondI M \<or> transCondIII M \<or> transCondV M")
    case True
    have c2: "transC2 M = Dpt (transV M) (t2 +\<^sub>B Dj1)"
      using True
      by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def Dj1_def
                    j1_def t2_def)
    have "lessBT t2 (t2 +\<^sub>B Dj1)" by (rule lessBT_addBT_self[OF Dj1ne])
    thus ?thesis using c1eq c2 by simp
  next
    case notA: False
    show ?thesis
    proof (cases "transCondVI M")
      case True
      have c2: "transC2 M = Dpt (transV M) Dj1"
        using notA True
        by (simp add: transC2_def Let_def transV_def transJ1_def Dj1_def j1_def)
      have "lessBT t2 Dj1"
        using VIfact[OF True] by (simp add: t2_def j1_def Dj1_def)
      thus ?thesis using c1eq c2 by simp
    next
      case notVI: False
      show ?thesis
      proof (cases "t2 = 0\<^sub>B")
        case True
        have c2: "transC2 M
                  = Dpt (transV M) (Dpt (enat (entry M 1 jp)) Dj1)"
          using notA notVI True
          by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def
                        transJ0_def Dj1_def j1_def jp_def t2_def)
        have "lessBT t2 (Dpt (enat (entry M 1 jp)) Dj1)"
          using True by simp
        thus ?thesis using c1eq c2 by simp
      next
        case t2ne: False
        define J1 where "J1 = Lng (PB t2) - 1"
        define pj where "pj = PB t2 ! J1"
        \<comment> \<open>\<open>PB t\<^sub>2 \<noteq> []\<close>\<close>
        have lng_ne: "Lng (PB t2) \<noteq> 0"
          using m_7_1_term_components[OF t2TB] t2ne by auto
        have pbne: "PB t2 \<noteq> []" using lng_ne by auto
        \<comment> \<open>split off the last component\<close>
        have splitlast: "PB t2 = take J1 (PB t2) @ [pj]"
        proof -
          have "take J1 (PB t2) = butlast (PB t2)"
            by (simp add: J1_def butlast_conv_take)
          moreover have "pj = last (PB t2)"
            using pbne by (simp add: pj_def J1_def last_conv_nth)
          ultimately show ?thesis
            using append_butlast_last_id[OF pbne] by simp
        qed
        have t2split: "t2 = SigmaB (take J1 (PB t2)) +\<^sub>B pj"
        proof -
          have "t2 = SigmaB (PB t2)" using m_7_1_term_components[OF t2TB] by simp
          also have "\<dots> = SigmaB (take J1 (PB t2) @ [pj])"
            using splitlast by simp
          also have "\<dots> = SigmaB (take J1 (PB t2)) +\<^sub>B pj"
            by (rule SigmaB_snoc)
          finally show ?thesis .
        qed
        \<comment> \<open>\<open>pj\<close> is a single principal term\<close>
        have pjprinc: "Lng (PB pj) = 1"
        proof -
          have Jlt: "J1 < length (untrm t2)"
            using pbne by (simp add: J1_def PB_def)
          have "pj = (map (\<lambda>p. Trm [p]) (untrm t2)) ! J1"
            by (simp add: pj_def PB_def)
          also have "\<dots> = Trm [untrm t2 ! J1]" using Jlt by simp
          finally show ?thesis by (simp add: PB_def)
        qed
        have pjrec: "pj = Dpt (bpHeadV pj) (bpHeadT pj)"
          by (rule principal_reconstruct[OF pjprinc])
        show ?thesis
        proof (cases "bpHeadV pj = enat (entry M 1 jp)")
          case leftDj0: True
          have c2: "transC2 M
                    = Dpt (transV M)
                        (SigmaB (take J1 (PB t2))
                          +\<^sub>B Dpt (enat (entry M 1 jp))
                                (bpHeadT pj +\<^sub>B Dj1))"
            using notA notVI t2ne leftDj0
            by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def
                          transJ0_def Dj1_def j1_def jp_def t2_def J1_def pj_def)
          \<comment> \<open>\<open>pj = D\<^bsub>M\<^bsub>1,jp\<^esub>\<^esub> (bpHeadT pj)\<close>, so \<open>t\<^sub>2 = \<Sigma>(prefix) + pj\<close>\<close>
          have pjval: "pj = Dpt (enat (entry M 1 jp)) (bpHeadT pj)"
            using pjrec leftDj0 by simp
          have t2eq: "t2 = SigmaB (take J1 (PB t2))
                            +\<^sub>B Dpt (enat (entry M 1 jp)) (bpHeadT pj)"
            using t2split pjval by simp
          have inner: "lessBT (Dpt (enat (entry M 1 jp)) (bpHeadT pj))
                              (Dpt (enat (entry M 1 jp)) (bpHeadT pj +\<^sub>B Dj1))"
            using lessBT_addBT_self[OF Dj1ne] by simp
          have "lessBT
                  (SigmaB (take J1 (PB t2))
                    +\<^sub>B Dpt (enat (entry M 1 jp)) (bpHeadT pj))
                  (SigmaB (take J1 (PB t2))
                    +\<^sub>B Dpt (enat (entry M 1 jp)) (bpHeadT pj +\<^sub>B Dj1))"
            by (rule lessBT_addBT_mono_right[OF inner])
          hence "lessBT t2
                  (SigmaB (take J1 (PB t2))
                    +\<^sub>B Dpt (enat (entry M 1 jp)) (bpHeadT pj +\<^sub>B Dj1))"
            using t2eq by simp
          thus ?thesis using c1eq c2 by simp
        next
          case leftDj0: False
          have c2: "transC2 M
                    = Dpt (transV M)
                        (t2 +\<^sub>B Dpt (enat (entry M 1 jp)) (t2 +\<^sub>B Dj1))"
            using notA notVI t2ne leftDj0
            by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def
                          transJ0_def Dj1_def j1_def jp_def t2_def J1_def pj_def)
          have "lessBT t2 (t2 +\<^sub>B Dpt (enat (entry M 1 jp)) (t2 +\<^sub>B Dj1))"
            by (rule lessBT_addBT_self) simp
          thus ?thesis using c1eq c2 by simp
        qed
      qed
    qed
  qed
qed

text \<open>If \<open>t\<close> is a nonzero term whose first principal node-value \<open>bpHeadV t\<close> is
  strictly below \<open>w\<close>, then \<open>t\<close> is \<open>lessBT\<close>-below the single principal \<open>D\<^bsub>w\<^esub> 0\<^bsub>B\<^esub>\<close>:
  the very first principal of \<open>t\<close> already loses on its node value.\<close>

lemma lessBT_bpHeadV_lt:
  assumes "t \<noteq> 0\<^sub>B" and "bpHeadV t < w"
  shows "lessBT t (Dpt w 0\<^sub>B)"
proof -
  obtain ps where t: "t = Trm ps" by (cases t)
  have psne: "ps \<noteq> []" using \<open>t \<noteq> 0\<^sub>B\<close> t by auto
  obtain p ps' where ps: "ps = p # ps'" using psne by (cases ps) auto
  obtain v u where p: "p = DB v u" by (cases p)
  have hv: "bpHeadV t = v" using t ps p by simp
  hence vw: "v < w" using \<open>bpHeadV t < w\<close> by simp
  have "lessBP (DB v u) (DB w 0\<^sub>B)" using vw by simp
  hence "lessBT (Trm (DB v u # ps')) (Trm [DB w 0\<^sub>B])" by simp
  thus ?thesis using t ps p by simp
qed

text \<open>Condition-VI half of \<open>c\<^sub>1 < c\<^sub>2\<close> reduced to its only non-admissible
  sub-case: a Mark second-index bound (\<open>NAbound\<close>).  The admissible sub-case is
  discharged here outright (it forces \<open>transT2 M = 0\<^bsub>B\<^esub>\<close>).\<close>

lemma transC1_lessBT_transC2_modNA:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and NAbound: "transCondVI M \<Longrightarrow> \<not> adm M (transJ0 M) \<Longrightarrow> transT2 M \<noteq> 0\<^sub>B
                    \<Longrightarrow> bpHeadV (transT2 M) < enat (entry M 1 (transJ1 M))"
  shows "lessBT (transC1 M) (transC2 M)"
proof -
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using J1pos by (simp add: transJ1_def)
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have VIfact: "transCondVI M \<Longrightarrow>
                  lessBT (transT2 M) (Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B)"
  proof -
    assume VI: "transCondVI M"
    define Dj1 where "Dj1 = Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B"
    show "lessBT (transT2 M) Dj1"
    proof (cases "transT2 M = 0\<^sub>B")
      case True
      have "lessBT (Trm []) Dj1" by (simp add: Dj1_def)
      thus ?thesis using True by simp
    next
      case t2ne: False
      show ?thesis
      proof (cases "adm M (transJ0 M)")
        case adm: True
        \<comment> \<open>admissible sub-case: \<open>transT2 M = 0\<^bsub>B\<^esub>\<close>, contradicting \<open>t2ne\<close>\<close>
        have j0eq: "transJ0 M = Lng M - 2"
        proof -
          have "parent M 0 (Lng M - 1) + 1 = Lng M - 1"
            using VI by (simp add: transCondVI_def)
          moreover have "transJ0 M = parent M 0 (Lng M - 1)"
            by (simp add: transJ0_def transJ1_def)
          ultimately show ?thesis by simp
        qed
        have jm1eq: "transJm1 M = transJ0 M"
          using adm by (simp add: transJm1_def Adm_def)
        have hp: "hasParent M 0 (Lng M - 1)"
          by (rule monoT_hasParent0_last[OF MT mono L])
        have mkd0: "(Pred M, Adm M (parent M 0 (Lng M - 1))) \<in> Marked"
          by (rule Marked_Pred_Adm[OF MT L hp])
        have parj0: "parent M 0 (Lng M - 1) = transJ0 M"
          by (simp add: transJ0_def transJ1_def)
        have admj0: "Adm M (transJ0 M) = transJ0 M"
          using adm by (simp add: Adm_def)
        have mkd: "(Pred M, transJ0 M) \<in> Marked"
          using mkd0 parj0 admj0 by simp
        have lngPred: "Lng (Pred M) - 1 = transJ0 M"
          using L j0eq by (simp add: Pred_def)
        have mkd': "(Pred M, Lng (Pred M) - 1) \<in> Marked"
          using mkd lngPred by simp
        have nzPred: "\<not> zeroT (Pred M)"
        proof
          assume "zeroT (Pred M)"
          hence "Trans (Pred M) = 0\<^sub>B" using m_7_3_Trans_zeroT[OF predRT] by simp
          thus False using T1 by (simp add: transT1_def)
        qed
        have markval: "Mark (Pred M) (Lng (Pred M) - 1)
                         = Dpt (enat (entry (Pred M) 1 (Lng (Pred M) - 1))) 0\<^sub>B"
          by (rule Mark_rightmost1_forward[OF predRT nzPred mkd'])
        have markj0: "Mark (Pred M) (transJm1 M)
                        = Dpt (enat (entry (Pred M) 1 (Lng (Pred M) - 1))) 0\<^sub>B"
          using markval lngPred jm1eq by simp
        have "transT2 M = bpHeadT (Mark (Pred M) (transJm1 M))"
          by (simp add: transT2_def transC1_def)
        also have "\<dots> = bpHeadT (Dpt (enat (entry (Pred M) 1 (Lng (Pred M) - 1))) 0\<^sub>B)"
          using markj0 by simp
        also have "\<dots> = 0\<^sub>B" by simp
        finally have "transT2 M = 0\<^sub>B" .
        thus ?thesis using t2ne by simp
      next
        case nadm: False
        have hbound: "bpHeadV (transT2 M) < enat (entry M 1 (transJ1 M))"
          by (rule NAbound[OF VI nadm t2ne])
        show ?thesis unfolding Dj1_def
          by (rule lessBT_bpHeadV_lt[OF t2ne hbound])
      qed
    qed
  qed
  show ?thesis by (rule transC1_lessBT_transC2[OF MR MP J1pos T1 VIfact])
qed


section \<open>§7.3 NAbound prerequisite: index-set of a \<open>BT\<close> term (\<open>flatIdx\<close>)\<close>

text \<open>\<open>flatIdx t\<close> = the set of \<open>D\<close>-indices occurring anywhere in \<open>t\<close>, read off the
  flat string (so a substring containment of \<open>flatBT\<close> immediately bounds it).
  The keystone for NAbound is a suffix-max bound on the indices of \<open>Mark N m\<close>.\<close>

definition flatIdx :: "BT \<Rightarrow> enat set" where
  "flatIdx t = {v. Dsym v \<in> set (flatBT t)}"

lemma flatIdx_zero [simp]: "flatIdx 0\<^sub>B = {}"
  by (simp add: flatIdx_def)

text \<open>The \<open>Dsym\<close>-letters of a tuple are the union over its principal components.\<close>

lemma flatIdx_Trm: "flatIdx (Trm xs) = (\<Union>p \<in> set xs. {v. Dsym v \<in> set (flatBP p)})"
proof (cases xs)
  case Nil thus ?thesis by (simp add: flatIdx_def)
next
  case (Cons p rest)
  show ?thesis
  proof (cases rest)
    case Nil thus ?thesis using Cons by (simp add: flatIdx_def)
  next
    case (Cons q ps)
    have "set (flatBT (Trm (p # q # ps)))
          = {LP, RP} \<union> set (flatBP p)
            \<union> (\<Union>r \<in> set (q # ps). insert CM (set (flatBP r)))"
      by auto
    thus ?thesis using \<open>xs = p # rest\<close> \<open>rest = q # ps\<close>
      by (auto simp: flatIdx_def)
  qed
qed

lemma flatIdx_Dpt [simp]: "flatIdx (Dpt v t) = insert v (flatIdx t)"
  by (auto simp: flatIdx_def)

lemma flatIdx_addBT [simp]: "flatIdx (a +\<^sub>B b) = flatIdx a \<union> flatIdx b"
proof -
  obtain as where a: "a = Trm as" by (cases a)
  obtain bs where b: "b = Trm bs" by (cases b)
  have "a +\<^sub>B b = Trm (as @ bs)" using a b by simp
  thus ?thesis using a b by (simp add: flatIdx_Trm)
qed

lemma flatIdx_SigmaB: "flatIdx (SigmaB ts) = (\<Union>t \<in> set ts. flatIdx t)"
proof -
  have "flatIdx (SigmaB ts) = (\<Union>p \<in> set (concat (map untrm ts)). {v. Dsym v \<in> set (flatBP p)})"
    by (simp add: SigmaB_def flatIdx_Trm)
  also have "\<dots> = (\<Union>t \<in> set ts. \<Union>p \<in> set (untrm t). {v. Dsym v \<in> set (flatBP p)})"
    by auto
  also have "\<dots> = (\<Union>t \<in> set ts. flatIdx t)"
  proof -
    have "\<And>t. flatIdx t = (\<Union>p \<in> set (untrm t). {v. Dsym v \<in> set (flatBP p)})"
      by (metis flatIdx_Trm untrm.simps untrm.cases)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

text \<open>The leftmost index \<open>bpHeadV t\<close> occurs in \<open>t\<close>.\<close>

lemma bpHeadV_in_flatIdx:
  assumes "t \<noteq> 0\<^sub>B" shows "bpHeadV t \<in> flatIdx t"
proof -
  obtain ps where t: "t = Trm ps" by (cases t)
  have "ps \<noteq> []" using assms t by auto
  then obtain p ps' where ps: "ps = p # ps'" by (cases ps) auto
  obtain v u where p: "p = DB v u" by (cases p)
  have "bpHeadV t = v" using t ps p by simp
  moreover have "v \<in> flatIdx t"
    using t ps p by (auto simp: flatIdx_Trm)
  ultimately show ?thesis by simp
qed

text \<open>A flat-string containment (all-\<open>RP\<close> tail) bounds \<open>flatIdx\<close>: if
  \<open>flatBT t = s \<frown> flatBT c \<frown> b\<close> with \<open>b\<close> all-\<open>RP\<close> and \<open>s\<close> a prefix of the flat of
  some term \<open>c\<^sub>0\<close>, then every index of \<open>t\<close> lies in \<open>flatIdx c\<^sub>0 \<union> flatIdx c\<close>.\<close>

lemma flatIdx_scb_sub:
  assumes "flatBT t = s @ flatBT c @ b"
    and "flatBT c\<^sub>0 = s @ flatBT c\<^sub>1 @ b\<^sub>0"
    and "\<forall>x \<in> set b. x = RP"
  shows "flatIdx t \<subseteq> flatIdx c\<^sub>0 \<union> flatIdx c"
proof
  fix v assume "v \<in> flatIdx t"
  hence "Dsym v \<in> set (flatBT t)" by (simp add: flatIdx_def)
  hence "Dsym v \<in> set s \<union> set (flatBT c) \<union> set b" using assms(1) by auto
  moreover have "Dsym v \<notin> set b" using assms(3) by auto
  ultimately have "Dsym v \<in> set s \<union> set (flatBT c)" by auto
  moreover have "set s \<subseteq> set (flatBT c\<^sub>0)" using assms(2) by auto
  ultimately show "v \<in> flatIdx c\<^sub>0 \<union> flatIdx c" by (auto simp: flatIdx_def)
qed

text \<open>\<open>bpHeadT t\<close> is a sub-term, so its indices are among \<open>t\<close>'s.\<close>

lemma flatIdx_bpHeadT_sub:
  assumes "t = Trm (p # ps)"
  shows "flatIdx (bpHeadT t) \<subseteq> flatIdx t"
proof -
  obtain v u where p: "p = DB v u" by (cases p)
  have "bpHeadT t = u" using assms p by simp
  moreover have "flatIdx u \<subseteq> flatIdx (Trm (DB v u # ps))"
    by (cases ps) (auto simp: flatIdx_def)
  ultimately show ?thesis using assms p by simp
qed

text \<open>Surgery-position relationships (the mono \<open>m < j\<^sub>1\<close> branch of \<open>Mark\<close>): the
  mark \<open>m\<close> sits at or below the row-0 parent \<open>j\<^sub>p\<close> of \<open>j\<^sub>1\<close> and its
  admissibilization \<open>j\<^sub>-\<^sub>1 = Adm N j\<^sub>p\<close>.\<close>

lemma surg_parent_ge:
  assumes mk: "(N, m) \<in> Marked" and mono: "monoT N" and L: "1 < Lng N"
    and mlt: "m < Lng N - 1"
  shows "m \<le> parent N 0 (Lng N - 1)"
proof -
  have NT: "N \<in> T_PS" using mk by (simp add: Marked_def)
  have hp: "hasParent N 0 (Lng N - 1)" by (rule monoT_hasParent0_last[OF NT mono L])
  have nxt: "nextR N 0 (parent N 0 (Lng N - 1)) (Lng N - 1)"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have le: "leR N 0 m (Lng N - 1)" using mk by (simp add: Marked_def)
  show ?thesis by (rule parent_max[OF hp nxt le mlt])
qed

lemma surg_adm_ge:
  assumes adm: "adm N m" and le: "m \<le> j"
  shows "m \<le> Adm N j"
proof (cases "adm N j")
  case True thus ?thesis using le by (simp add: Adm_def)
next
  case False
  hence Adm: "Adm N j = Max {j'. adm N j' \<and> j' < j}" by (simp add: Adm_def)
  have mlt: "m < j" using le False adm by (cases "m = j") auto
  have fin: "finite {j'. adm N j' \<and> j' < j}"
    by (rule finite_subset[of _ "{0..<j}"]) auto
  have mem: "m \<in> {j'. adm N j' \<and> j' < j}" using adm mlt by simp
  have "m \<le> Max {j'. adm N j' \<and> j' < j}" by (rule Max_ge[OF fin mem])
  thus ?thesis using Adm by simp
qed

text \<open>Every index of \<open>c\<^sub>2 = transC2 N\<close> lies in \<open>c\<^sub>1 = transC1 N\<close> or is one of the two
  explicit row-1 entries \<open>N\<^bsub>1,j\<^sub>1\<^esub>\<close>, \<open>N\<^bsub>1,j\<^sub>p\<^esub>\<close> introduced by the definition.  Every
  branch is \<open>D\<^bsub>v\<^esub>(\<dots>)\<close> with \<open>v = bpHeadV c\<^sub>1\<close>, and the inner term is built from
  \<open>t\<^sub>2 = bpHeadT c\<^sub>1\<close> (or sub-sums/last-principal of it) plus \<open>D\<^bsub>N\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub>\<close>/\<open>D\<^bsub>N\<^sub>1\<^sub>,\<^sub>j\<^sub>p\<^esub>\<close>.\<close>

lemma flatIdx_transC2_sub:
  assumes c1ne: "transC1 N \<noteq> 0\<^sub>B" and t2TB: "transT2 N \<in> T_B"
  shows "flatIdx (transC2 N)
           \<subseteq> flatIdx (transC1 N)
              \<union> {enat (entry N 1 (transJ1 N)), enat (entry N 1 (transJ0 N))}"
proof -
  obtain xs where xs: "transC1 N = Trm xs" by (cases "transC1 N")
  have "xs \<noteq> []" using c1ne xs by auto
  then obtain p ps where "xs = p # ps" by (cases xs) auto
  hence c1form: "transC1 N = Trm (p # ps)" using xs by simp
  \<comment> \<open>\<open>v = transV N = bpHeadV c\<^sub>1 \<in> flatIdx c\<^sub>1\<close>\<close>
  have vin: "transV N \<in> flatIdx (transC1 N)"
    unfolding transV_def by (rule bpHeadV_in_flatIdx[OF c1ne])
  \<comment> \<open>\<open>flatIdx t\<^sub>2 \<subseteq> flatIdx c\<^sub>1\<close>\<close>
  have t2sub: "flatIdx (transT2 N) \<subseteq> flatIdx (transC1 N)"
    unfolding transT2_def using flatIdx_bpHeadT_sub[OF c1form] by simp
  \<comment> \<open>\<open>SigmaB(take k (PB t\<^sub>2))\<close> and any \<open>PB t\<^sub>2 ! k\<close> have indices within \<open>t\<^sub>2\<close>\<close>
  have sigsub: "\<And>k. flatIdx (SigmaB (take k (PB (transT2 N)))) \<subseteq> flatIdx (transT2 N)"
  proof -
    fix k
    have "flatIdx (SigmaB (take k (PB (transT2 N))))
          = (\<Union>t \<in> set (take k (PB (transT2 N))). flatIdx t)" by (rule flatIdx_SigmaB)
    also have "\<dots> \<subseteq> (\<Union>t \<in> set (PB (transT2 N)). flatIdx t)"
      using set_take_subset by fastforce
    also have "\<dots> = flatIdx (SigmaB (PB (transT2 N)))" by (rule flatIdx_SigmaB[symmetric])
    also have "\<dots> = flatIdx (transT2 N)" using m_7_1_term_components[OF t2TB] by simp
    finally show "flatIdx (SigmaB (take k (PB (transT2 N)))) \<subseteq> flatIdx (transT2 N)" .
  qed
  have pjsub: "\<And>k. k < Lng (PB (transT2 N)) \<Longrightarrow> flatIdx (PB (transT2 N) ! k) \<subseteq> flatIdx (transT2 N)"
  proof -
    fix k assume "k < Lng (PB (transT2 N))"
    hence "PB (transT2 N) ! k \<in> set (PB (transT2 N))" by (rule nth_mem)
    hence "flatIdx (PB (transT2 N) ! k) \<subseteq> (\<Union>t \<in> set (PB (transT2 N)). flatIdx t)" by auto
    also have "\<dots> = flatIdx (transT2 N)"
      using flatIdx_SigmaB[symmetric] m_7_1_term_components[OF t2TB] by simp
    finally show "flatIdx (PB (transT2 N) ! k) \<subseteq> flatIdx (transT2 N)" .
  qed
  have bpHeadT_pj: "\<And>k. k < Lng (PB (transT2 N))
        \<Longrightarrow> flatIdx (bpHeadT (PB (transT2 N) ! k)) \<subseteq> flatIdx (transT2 N)"
  proof -
    fix k assume k: "k < Lng (PB (transT2 N))"
    have "PB (transT2 N) ! k \<in> set (PB (transT2 N))" using k by (rule nth_mem)
    then obtain q where q: "PB (transT2 N) ! k = Trm [q]" by (auto simp: PB_def)
    have "flatIdx (bpHeadT (PB (transT2 N) ! k)) \<subseteq> flatIdx (PB (transT2 N) ! k)"
      using flatIdx_bpHeadT_sub[OF q] by simp
    thus "flatIdx (bpHeadT (PB (transT2 N) ! k)) \<subseteq> flatIdx (transT2 N)"
      using pjsub[OF k] by blast
  qed
  \<comment> \<open>now bound \<open>flatIdx (transC2 N)\<close> branch by branch\<close>
  let ?j1 = "enat (entry N 1 (transJ1 N))"  let ?jp = "enat (entry N 1 (transJ0 N))"
  let ?Dj1 = "Dpt (enat (entry N 1 (transJ1 N))) 0\<^sub>B"
  have inner: "flatIdx (transC2 N) \<subseteq> insert (transV N) (flatIdx (transT2 N) \<union> {?j1, ?jp})"
  proof (cases "transCondI N \<or> transCondIII N \<or> transCondV N")
    case True
    hence "transC2 N = Dpt (transV N) (transT2 N +\<^sub>B ?Dj1)"
      by (simp add: transC2_def Let_def)
    thus ?thesis by (auto simp: flatIdx_addBT flatIdx_Dpt)
  next
    case notA: False
    show ?thesis
    proof (cases "transCondVI N")
      case True
      hence "transC2 N = Dpt (transV N) ?Dj1" using notA
        by (simp add: transC2_def Let_def)
      thus ?thesis by (auto simp: flatIdx_Dpt)
    next
      case notVI: False
      show ?thesis
      proof (cases "transT2 N = 0\<^sub>B")
        case True
        hence "transC2 N = Dpt (transV N) (Dpt (enat (entry N 1 (transJ0 N))) ?Dj1)"
          using notA notVI by (simp add: transC2_def Let_def)
        thus ?thesis by (auto simp: flatIdx_Dpt)
      next
        case t2nz: False
        have J1lt: "Lng (PB (transT2 N)) - 1 < Lng (PB (transT2 N))"
          using m_7_1_term_components[OF t2TB] t2nz by (cases "Lng (PB (transT2 N))") auto
        have b1: "flatIdx (SigmaB (take (Lng (PB (transT2 N)) - 1) (PB (transT2 N)))) \<subseteq> flatIdx (transT2 N)"
          by (rule sigsub)
        have b2: "flatIdx (bpHeadT (PB (transT2 N) ! (Lng (PB (transT2 N)) - 1))) \<subseteq> flatIdx (transT2 N)"
          by (rule bpHeadT_pj[OF J1lt])
        show ?thesis
        proof (cases "bpHeadV (PB (transT2 N) ! (Lng (PB (transT2 N)) - 1)) = enat (entry N 1 (transJ0 N))")
          case leftDj0: True
          hence "transC2 N = Dpt (transV N)
                   (SigmaB (take (Lng (PB (transT2 N)) - 1) (PB (transT2 N)))
                    +\<^sub>B Dpt (enat (entry N 1 (transJ0 N)))
                          (bpHeadT (PB (transT2 N) ! (Lng (PB (transT2 N)) - 1)) +\<^sub>B ?Dj1))"
            using notA notVI t2nz by (simp add: transC2_def Let_def)
          thus ?thesis using b1 b2 by (auto simp: flatIdx_addBT flatIdx_Dpt)
        next
          case False
          hence "transC2 N = Dpt (transV N)
                   (transT2 N +\<^sub>B Dpt (enat (entry N 1 (transJ0 N))) (transT2 N +\<^sub>B ?Dj1))"
            using notA notVI t2nz by (simp add: transC2_def Let_def)
          thus ?thesis by (auto simp: flatIdx_addBT flatIdx_Dpt)
        qed
      qed
    qed
  qed
  show ?thesis using inner vin t2sub by auto
qed


text \<open>\<open>transC2 N\<close> is a dfree term whenever \<open>c\<^sub>1 = transC1 N\<close> is a (nonzero) dfree
  principal term: every branch of @{thm [source] transC2_def} is \<open>D\<^bsub>v\<^esub>(\<dots>)\<close> built
  from \<open>v = transV N\<close> (the finite head index of \<open>c\<^sub>1\<close>), \<open>t\<^sub>2 = transT2 N\<close> (the
  dfree tail of \<open>c\<^sub>1\<close>), its sub-sums, and finite \<open>enat\<close> row-1 entries.\<close>

lemma dfree_transC2:
  assumes vne: "transV N \<noteq> \<infinity>" and t2df: "dfree_BT (transT2 N)"
  shows "dfree_BT (transC2 N)"
proof -
  define v where "v = transV N"
  define t2 where "t2 = transT2 N"
  have vne': "v \<noteq> \<infinity>" using vne v_def by simp
  have t2df': "dfree_BT t2" using t2df t2_def by simp
  let ?j1 = "transJ1 N"  let ?jp = "transJ0 N"
  let ?Dj1 = "Dpt (enat (entry N 1 ?j1)) 0\<^sub>B"
  have dfDj1: "dfree_BT ?Dj1" by simp
  show ?thesis
  proof (cases "transCondI N \<or> transCondIII N \<or> transCondV N")
    case True
    have "transC2 N = Dpt v (t2 +\<^sub>B ?Dj1)"
      using True by (simp add: transC2_def Let_def v_def t2_def transT2_def
                                transJ1_def transV_def)
    moreover have "dfree_BT (t2 +\<^sub>B ?Dj1)"
      using t2df' dfDj1 by (cases t2) auto
    ultimately show ?thesis using vne' by simp
  next
    case notA: False
    show ?thesis
    proof (cases "transCondVI N")
      case True
      have "transC2 N = Dpt v ?Dj1"
        using notA True by (simp add: transC2_def Let_def v_def transV_def
                                       transJ1_def)
      thus ?thesis using vne' dfDj1 by simp
    next
      case notVI: False
      show ?thesis
      proof (cases "t2 = 0\<^sub>B")
        case True
        have "transC2 N = Dpt v (Dpt (enat (entry N 1 ?jp)) ?Dj1)"
          using notA notVI True
          by (simp add: transC2_def Let_def v_def t2_def transV_def transT2_def
                        transJ1_def transJ0_def)
        thus ?thesis using vne' dfDj1 by simp
      next
        case t2nz: False
        define J1 where "J1 = Lng (PB t2) - 1"
        define pj where "pj = PB t2 ! J1"
        have df_sig: "dfree_BT (SigmaB (take J1 (PB t2)))"
          using t2df' by (cases t2) (auto simp: SigmaB_def PB_def dest!: in_set_takeD)
        have untrmne: "untrm t2 \<noteq> []" using t2nz by (cases t2) auto
        have J1lt: "J1 < Lng (PB t2)"
          using untrmne by (simp add: J1_def PB_def)
        have df_bphead: "dfree_BT (bpHeadT pj)"
        proof -
          have "pj \<in> set (PB t2)" using pj_def J1lt by simp
          hence "dfree_BT pj" using t2df' by (cases t2) (auto simp: PB_def)
          thus ?thesis by (cases pj rule: bpHeadT.cases) auto
        qed
        show ?thesis
        proof (cases "bpHeadV pj = enat (entry N 1 ?jp)")
          case leftDj0: True
          have "transC2 N = Dpt v
                  (SigmaB (take J1 (PB t2))
                    +\<^sub>B Dpt (enat (entry N 1 ?jp)) (bpHeadT pj +\<^sub>B ?Dj1))"
            using notA notVI t2nz leftDj0
            by (simp add: transC2_def Let_def v_def t2_def transV_def transT2_def
                          transJ1_def transJ0_def J1_def pj_def)
          moreover have "dfree_BT (bpHeadT pj +\<^sub>B ?Dj1)"
            using df_bphead dfDj1 by (cases "bpHeadT pj") auto
          moreover have "dfree_BT (SigmaB (take J1 (PB t2))
                    +\<^sub>B Dpt (enat (entry N 1 ?jp)) (bpHeadT pj +\<^sub>B ?Dj1))"
            using df_sig calculation(2)
            by (cases "SigmaB (take J1 (PB t2))") auto
          ultimately show ?thesis using vne' by simp
        next
          case False
          have "transC2 N = Dpt v
                  (t2 +\<^sub>B Dpt (enat (entry N 1 ?jp)) (t2 +\<^sub>B ?Dj1))"
            using notA notVI t2nz False
            by (simp add: transC2_def Let_def v_def t2_def transV_def transT2_def
                          transJ1_def transJ0_def J1_def pj_def)
          moreover have "dfree_BT (t2 +\<^sub>B ?Dj1)"
            using t2df' dfDj1 by (cases t2) auto
          moreover have "dfree_BT (t2 +\<^sub>B Dpt (enat (entry N 1 ?jp)) (t2 +\<^sub>B ?Dj1))"
            using t2df' calculation(2) by (cases t2) auto
          ultimately show ?thesis using vne' by simp
        qed
      qed
    qed
  qed
qed

text \<open>The \<open>Mark\<close>-index suffix-max bound: every \<open>D\<close>-index occurring in \<open>Mark N m\<close>
  is \<open>\<le>\<close> the maximum row-1 entry of \<open>N\<close> over the suffix columns \<open>{m .. Lng N - 1}\<close>.
  Strong \<open>Lng\<close>-induction, mirroring @{thm [source] Trans_Mark_invariant_aux};
  the surgery branch mirrors @{thm [source] trans_inv_B_hard}, bounding via
  @{thm [source] flatIdx_scb_sub} / @{thm [source] flatIdx_transC2_sub}.
  Empirically 0 violations over 9699 marked cases.\<close>

lemma Mark_flatIdx_bound:
  "(N, m) \<in> Marked \<longrightarrow> N \<in> RT_PS
   \<longrightarrow> (\<forall>v \<in> flatIdx (Mark N m). v \<le> enat (Max ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1})))"
proof (induction N arbitrary: m rule: measure_induct_rule[where f=Lng])
  case (less N)
  show ?case
  proof (intro impI)
    assume mM: "(N, m) \<in> Marked" and NR: "N \<in> RT_PS"
    have NT: "N \<in> T_PS" using NR by (simp add: RT_PS_def)
    have Nne: "N \<noteq> []" using NT by (simp add: T_PS_def)
    have domK: "\<And>m. Trans_Mark_dom (Inr (N, m))" by (rule m_7_3_Mark_welldef[OF NR])
    \<comment> \<open>\<open>m \<le> Lng N - 1\<close> from the \<open>Marked\<close> reach relation\<close>
    have leM: "leR N 0 m (Lng N - 1)" using mM by (simp add: Marked_def)
    have mleN: "m < Lng N" using leM by (simp add: leR_def le0_def)
    have mle: "m \<le> Lng N - 1" using mleN by linarith
    have admN: "adm N m" using mM by (simp add: Marked_def)
    \<comment> \<open>the suffix-max abbreviation and its membership bound\<close>
    let ?B = "\<lambda>N m. enat (Max ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1}))"
    have ble: "\<And>k. m \<le> k \<Longrightarrow> k \<le> Lng N - 1 \<Longrightarrow> enat (entry N 1 k) \<le> ?B N m"
    proof -
      fix k assume "m \<le> k" and "k \<le> Lng N - 1"
      hence "entry N 1 k \<in> (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}" by auto
      hence "entry N 1 k \<le> Max ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1})"
        by (simp add: Max_ge)
      thus "enat (entry N 1 k) \<le> ?B N m" by simp
    qed
    have zle: "(0::enat) \<le> ?B N m" by simp
    show "\<forall>v \<in> flatIdx (Mark N m). v \<le> ?B N m"
    proof (cases "Lng N = 1")
      case True
      \<comment> \<open>(A) length 1: \<open>N = [(v,v)]\<close>, \<open>m = 0\<close>\<close>
      obtain v where Nv: "N = [(v, v)]"
        using m_6_6_oneColumn[OF NT] NR True by auto
      have m0: "m = 0" using mle True by simp
      have kv: "Mark N m = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Nv Mark_singleton by simp
      have ev: "entry N 1 0 = v" using Nv by (simp add: entry_def)
      show ?thesis
      proof
        fix x assume "x \<in> flatIdx (Mark N m)"
        hence "x \<in> {enat v}" using kv by (cases "v = 0") auto
        hence "x = enat v" by simp
        moreover have "enat v \<le> ?B N m"
          using ble[of 0] m0 mle ev True by simp
        ultimately show "x \<le> ?B N m" by simp
      qed
    next
      case notone: False
      have L: "1 < Lng N" using Nne notone by (cases N) auto
      have Lgt1: "\<not> Lng N \<le> Suc 0" using L by simp
      let ?j1 = "Lng N - 1"
      show ?thesis
      proof (cases "monoT N")
        case mono: True
        have predRT: "Pred N \<in> RT_PS" by (rule Pred_RT_PS[OF NR])
        have predb: "Pred N = butlast N" using L by (simp add: Pred_def)
        have LPred: "Lng (Pred N) = Lng N - 1" using predb by simp
        have LPredlt: "Lng (Pred N) < Lng N" using LPred L by simp
        \<comment> \<open>row-1 entries agree on the kept columns\<close>
        have entryP: "\<And>j. j \<le> Lng N - 2 \<Longrightarrow> entry (Pred N) 1 j = entry N 1 j"
        proof -
          fix j assume "j \<le> Lng N - 2"
          hence "j < Lng N - 1" using L by linarith
          hence "j < length (butlast N)" using L by simp
          thus "entry (Pred N) 1 j = entry N 1 j"
            using predb by (simp add: entry_def nth_butlast)
        qed
        show ?thesis
        proof (cases "Trans (Pred N) = 0\<^sub>B")
          case t1z: True
          \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>\<close>
          have kv: "Mark N m = (if m = 0 then Dpt 0 (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)
                                else Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)"
            using Mark.psimps[OF domK] NR Lgt1 mono t1z by (simp add: Let_def)
          show ?thesis
          proof
            fix x assume "x \<in> flatIdx (Mark N m)"
            hence "x \<in> {0, enat (entry N 1 ?j1)} \<or> x \<in> {enat (entry N 1 ?j1)}"
              using kv by (cases "m = 0") (auto simp: flatIdx_Dpt zero_enat_def)
            hence "x = 0 \<or> x = enat (entry N 1 ?j1)" by auto
            thus "x \<le> ?B N m"
              using zle ble[of ?j1] mle by auto
          qed
        next
          case t1ne: False
          \<comment> \<open>(B) \<open>t\<^sub>1 \<noteq> 0\<close>\<close>
          have hp: "hasParent N 0 ?j1" by (rule monoT_hasParent0_last[OF NT mono L])
          let ?bv = "entry N 1 (Lng N - 1)"
          define jp where "jp = parent N 0 (Lng N - 1)"
          define jm1 where "jm1 = Adm N jp"
          \<comment> \<open>identify the def's \<open>c\<^sub>1\<close>/\<open>c\<^sub>2\<close> with the \<open>trans*\<close> components\<close>
          have transJ1eq: "transJ1 N = ?j1" by (simp add: transJ1_def)
          have transJ0eq: "transJ0 N = jp" by (simp add: transJ0_def transJ1_def jp_def)
          have transJm1eq: "transJm1 N = jm1"
            by (simp add: transJm1_def jm1_def transJ0eq)
          \<comment> \<open>the surgery define-chain, mirroring @{thm [source] trans_inv_B_hard}\<close>
          define c1 where "c1 = Mark (Pred N) (Adm N jp)"
          define vv where "vv = bpHeadV c1"
          define tt2 where "tt2 = bpHeadT c1"
          define JJ1 where "JJ1 = Lng (PB tt2) - 1"
          define pj where "pj = PB tt2 ! JJ1"
          define ldj where "ldj = (bpHeadV pj = enat (entry N 1 jp))"
          define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
          define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
          define c2 where "c2 = (if transCondI N \<or> transCondIII N \<or> transCondV N
                         then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                         else if transCondVI N
                         then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                         else if tt2 = 0\<^sub>B
                         then Dpt vv (Dpt (enat (entry N 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                         else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry N 1 jp))
                                            (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
          \<comment> \<open>\<open>c\<^sub>1 = transC1 N\<close>, \<open>c\<^sub>2 = transC2 N\<close>\<close>
          have c1eqT: "c1 = transC1 N"
            by (simp add: c1_def transC1_def transJm1eq jm1_def)
          have c2eqT: "c2 = transC2 N"
            unfolding c2_def transC2_def Let_def
              vv_def tt2_def c1eqT transV_def transT2_def
              JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
            by simp
          have c1eq: "c1 = Mark (Pred N) jm1"
            by (simp add: c1_def jm1_def)
          \<comment> \<open>\<open>(Pred N, jm1) \<in> Marked\<close>; \<open>c\<^sub>1\<close> nonzero and \<open>t\<^sub>2 \<in> T\<^sub>B\<close>\<close>
          have mkjm1: "(Pred N, jm1) \<in> Marked"
            using Marked_Pred_Adm[OF NT L hp] jp_def jm1_def by simp
          have NP: "N \<in> PT_PS" using NT mono by (simp add: PT_PS_def)
          have J1pos: "transJ1 N > 0" using L by (simp add: transJ1_def)
          have T1ne: "transT1 N \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
          have pc1: "Lng (PB (transC1 N)) = 1"
            by (rule transC1_single_principal[OF NR NP J1pos T1ne])
          have c1ne: "transC1 N \<noteq> 0\<^sub>B"
          proof
            assume "transC1 N = 0\<^sub>B"
            thus False using pc1 by (simp add: PB_def)
          qed
          have c1TB: "transC1 N \<in> T_B"
            using m_7_3_Mark_in_T_B[OF predRT mkjm1] c1eq c1eqT by simp
          have c1Dpt: "transC1 N = Dpt (transV N) (transT2 N)"
            using principal_reconstruct[OF pc1]
            by (simp add: transV_def transT2_def)
          have t2TB: "transT2 N \<in> T_B"
            using c1TB unfolding c1Dpt by (auto simp: T_B_def)
          \<comment> \<open>flatIdx of \<open>c\<^sub>2\<close> bound (def brick)\<close>
          have c2sub: "flatIdx c2
              \<subseteq> flatIdx (transC1 N) \<union> {enat (entry N 1 ?j1), enat (entry N 1 jp)}"
            using flatIdx_transC2_sub[OF c1ne t2TB]
            by (simp add: c2eqT transJ1eq transJ0eq)
          \<comment> \<open>position facts: \<open>m \<le> jp \<le> j\<^sub>1\<close> and \<open>m \<le> jm1\<close>\<close>
          have jplt: "jp < ?j1"
          proof -
            have "nextR N 0 jp ?j1"
              using hp unfolding hasParent_def parent_def jp_def by (rule theI')
            thus ?thesis by (simp add: nextR_def nextrel0_def)
          qed
          have jple: "jp \<le> ?j1" using jplt by simp
          \<comment> \<open>the suffix-max for \<open>Pred N\<close> at an index \<open>i \<ge> m\<close> is below \<open>?B N m\<close>\<close>
          have predB_le: "\<And>i. m \<le> i \<Longrightarrow> i \<le> Lng N - 2 \<Longrightarrow> ?B (Pred N) i \<le> ?B N m"
          proof -
            fix i assume mi: "m \<le> i" and iN: "i \<le> Lng N - 2"
            have sub: "{i..Lng (Pred N) - 1} \<subseteq> {m..Lng N - 1}"
              using LPred mi L by auto
            have fin: "finite ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1})" by simp
            have ne: "{i..Lng (Pred N) - 1} \<noteq> {}" using iN LPred L by auto
            have imgeq: "(\<lambda>j. entry (Pred N) 1 j) ` {i..Lng (Pred N) - 1}
                  = (\<lambda>j. entry N 1 j) ` {i..Lng (Pred N) - 1}"
            proof (rule image_cong[OF refl])
              fix j assume "j \<in> {i..Lng (Pred N) - 1}"
              hence "j \<le> Lng (Pred N) - 1" by simp
              hence jb: "j \<le> Lng N - 2" using LPred by linarith
              show "entry (Pred N) 1 j = entry N 1 j" by (rule entryP[OF jb])
            qed
            have "Max ((\<lambda>j. entry (Pred N) 1 j) ` {i..Lng (Pred N) - 1})
                  = Max ((\<lambda>j. entry N 1 j) ` {i..Lng (Pred N) - 1})"
              using imgeq by simp
            also have "\<dots> \<le> Max ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1})"
            proof (rule Max_mono)
              show "(\<lambda>j. entry N 1 j) ` {i..Lng (Pred N) - 1}
                    \<subseteq> (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}"
                using sub by auto
              show "(\<lambda>j. entry N 1 j) ` {i..Lng (Pred N) - 1} \<noteq> {}"
                using ne by auto
              show "finite ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1})" by simp
            qed
            finally show "?B (Pred N) i \<le> ?B N m" by simp
          qed
          \<comment> \<open>IH on \<open>Pred N\<close>\<close>
          have IHpred: "\<And>i. (Pred N, i) \<in> Marked
              \<Longrightarrow> \<forall>v \<in> flatIdx (Mark (Pred N) i). v \<le> ?B (Pred N) i"
            using less.IH[OF LPredlt] predRT by blast
          show ?thesis
          proof (cases "m < ?j1")
            case mlt_false: False
            \<comment> \<open>(B) \<open>m = j\<^sub>1\<close>: \<open>Mark N m = D\<^bsub>N\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0\<close>\<close>
            have kv: "Mark N m = Dpt (enat (entry N 1 ?j1)) 0\<^sub>B"
              using Mark.psimps[OF domK] NR Lgt1 mono t1ne mlt_false
              unfolding Let_def jp_def[symmetric]
              by simp
            show ?thesis
            proof
              fix x assume "x \<in> flatIdx (Mark N m)"
              hence "x = enat (entry N 1 ?j1)" using kv by (simp add: flatIdx_Dpt)
              thus "x \<le> ?B N m" using ble[of ?j1] mle by simp
            qed
          next
            case mlt: True
            \<comment> \<open>(B) surgery branch, \<open>m < j\<^sub>1\<close>\<close>
            define c0 where "c0 = Mark (Pred N) m"
            define sm1 where
              "sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))"
            have mark_val_raw: "Mark N m = (if (Mark (Pred N) m, c1) \<in> MarkedB
                  then unflatBT
                         (fst (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                          (flatBT c1) (snd sb))
                          @ flatBT c2
                          @ snd (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                            (flatBT c1) (snd sb)))
                  else Dpt (enat ?bv) 0\<^sub>B)"
              using Mark.psimps[OF domK] NR Lgt1 mono t1ne mlt
              unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                        tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                        ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                        c2_def[symmetric]
              by simp
            have mark_val: "Mark N m = (if (c0, c1) \<in> MarkedB
                  then unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
                  else Dpt (enat ?bv) 0\<^sub>B)"
              using mark_val_raw by (simp add: c0_def sm1_def)
            show ?thesis
            proof (cases "(c0, c1) \<in> MarkedB")
              case mbc_false: False
              have kv: "Mark N m = Dpt (enat (entry N 1 ?j1)) 0\<^sub>B"
                using mark_val mbc_false by simp
              show ?thesis
              proof
                fix x assume "x \<in> flatIdx (Mark N m)"
                hence "x = enat (entry N 1 ?j1)" using kv by (simp add: flatIdx_Dpt)
                thus "x \<le> ?B N m" using ble[of ?j1] mle by simp
              qed
            next
              case mbc: True
              \<comment> \<open>\<open>(Pred N, m) \<in> Marked\<close> and its \<open>c\<^sub>1\<close>-shape\<close>
              have mPred: "(Pred N, m) \<in> Marked"
                by (rule Marked_Pred[OF NT L mM mlt])
              \<comment> \<open>\<open>c\<^sub>0 = Mark (Pred N) m\<close> is principal\<close>
              have c1form: "transC1 N = Trm [DB (transV N) (transT2 N)]"
                using c1Dpt by simp
              have c1p: "c1 = Trm [DB (transV N) (transT2 N)]"
                using c1form c1eqT by simp
              \<comment> \<open>the \<open>SOME\<close> decomposition of \<open>c\<^sub>0\<close>\<close>
              have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
                using mbc unfolding MarkedB_def by auto
              have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
                unfolding sm1_def by (rule someI_ex[OF exsm])
              \<comment> \<open>\<open>c\<^sub>0\<close> is a single principal term\<close>
              have c1Dsym: "flatBT c1 = Dsym (transV N) # flatBT (transT2 N)"
                using c1eqT c1Dpt by simp
              have c0ne: "c0 \<noteq> 0\<^sub>B"
              proof
                assume z: "c0 = 0\<^sub>B"
                have "flatBT c0 = fst sm1 @ flatBT c1 @ snd sm1"
                  using dsm by (simp add: scb_decomp_def)
                hence "Dsym (transV N) \<in> set (flatBT c0)"
                  using c1Dsym by simp
                thus False using z by simp
              qed
              \<comment> \<open>\<open>c\<^sub>0\<close> is a marked left member of \<open>Trans (Pred N) \<noteq> 0\<close>, hence principal\<close>
              have mb0: "(Trans (Pred N), c0) \<in> MarkedB"
                using m_7_3_Trans_Mark_MarkedB[OF predRT mPred] c0_def by simp
              obtain s0 b0 where d0: "scb_decomp (Trans (Pred N)) s0 (flatBT c0) b0"
                using mb0 by (auto simp: MarkedB_def)
              have t1neT: "Trans (Pred N) \<noteq> Trm []" using t1ne by simp
              have iptc0: "isPTB_str (flatBT c0)"
                using d0 t1neT by (simp add: scb_decomp_def)
              then obtain pc0 where pc0l: "flatBT c0 = flatBP pc0"
                  and pc0d: "dfree_BP pc0"
                by (auto simp: isPTB_str_def)
              have c0p: "c0 = Trm [pc0]"
              proof -
                have "flatBT c0 = flatBT (Trm [pc0])" using pc0l by simp
                thus ?thesis by (rule m_7_flatBT_inj)
              qed
              \<comment> \<open>\<open>c\<^sub>2\<close> is a single principal dfree term, hence \<open>isPTB_str\<close>\<close>
              have vne: "transV N \<noteq> \<infinity>" using c1TB c1Dpt by (auto simp: T_B_def)
              have t2df: "dfree_BT (transT2 N)"
                using c1TB c1Dpt by (auto simp: T_B_def)
              have c2df: "dfree_BT c2"
                using dfree_transC2[OF vne t2df] c2eqT by simp
              have c2pc1: "Lng (PB c2) = 1"
                using transC2_single_principal c2eqT by simp
              have c2recon: "c2 = Dpt (bpHeadV c2) (bpHeadT c2)"
                by (rule principal_reconstruct[OF c2pc1])
              obtain pc2 where c2p: "c2 = Trm [pc2]"
                using c2recon by (metis BT.exhaust untrm.simps)
              have iptc2: "isPTB_str (flatBT (Trm [pc2]))"
              proof -
                have "dfree_BT (Trm [pc2])" using c2df c2p by simp
                then obtain p where "pc2 = p" and "dfree_BP p" by auto
                thus ?thesis by (auto simp: isPTB_str_def)
              qed
              \<comment> \<open>reconstruct the replaced \<open>Mark\<close> value as a principal term\<close>
              have dsm': "scb_decomp (Trm [pc0]) (fst sm1)
                            (flatBT (Trm [DB (transV N) (transT2 N)])) (snd sm1)"
                using dsm c0p c1p by simp
              obtain pm where pmf: "flatBP pm = fst sm1 @ flatBT (Trm [pc2]) @ snd sm1"
                  and pmd: "scb_decomp (Trm [pm]) (fst sm1) (flatBT (Trm [pc2])) (snd sm1)"
                using scb_replace_principal_BP[OF dsm' iptc2] by blast
              have markM: "Mark N m = Trm [pm]"
              proof -
                have "flatBT (Trm [pm]) = fst sm1 @ flatBT c2 @ snd sm1"
                  using pmf c2p by simp
                thus ?thesis
                  using mark_val mbc unflatBT_flat[of "Trm [pm]"] by simp
              qed
              \<comment> \<open>\<open>flatBT (Mark N m) = fst sm1 @ flatBT c2 @ snd sm1\<close>\<close>
              have flatMark: "flatBT (Mark N m) = fst sm1 @ flatBT c2 @ snd sm1"
                using markM pmf c2p by simp
              have flatc0: "flatBT c0 = fst sm1 @ flatBT c1 @ snd sm1"
                using dsm by (simp add: scb_decomp_def)
              have brp: "\<forall>x \<in> set (snd sm1). x = RP"
                using dsm by (simp add: scb_decomp_def)
              \<comment> \<open>the containment bound\<close>
              have fsub: "flatIdx (Mark N m) \<subseteq> flatIdx c0 \<union> flatIdx c2"
                by (rule flatIdx_scb_sub[OF flatMark flatc0 brp])
              \<comment> \<open>bound \<open>flatIdx c0\<close> via the IH on \<open>Pred N\<close>\<close>
              have c0bound: "\<forall>v \<in> flatIdx c0. v \<le> ?B N m"
              proof
                fix v assume "v \<in> flatIdx c0"
                hence "v \<le> ?B (Pred N) m"
                  using IHpred[OF mPred] c0_def by simp
                also have "\<dots> \<le> ?B N m"
                proof -
                  have "m \<le> Lng N - 2" using mlt L by linarith
                  thus ?thesis using predB_le[of m] by simp
                qed
                finally show "v \<le> ?B N m" .
              qed
              \<comment> \<open>bound \<open>flatIdx c2\<close>\<close>
              have mjp: "m \<le> jp"
                using surg_parent_ge[OF mM mono L mlt] jp_def by simp
              have mjm1: "m \<le> jm1"
                using surg_adm_ge[OF admN mjp] jm1_def by simp
              have jm1lt: "jm1 \<le> Lng N - 2"
              proof -
                have "jm1 \<le> jp" using adm_Adm_le jm1_def by simp
                thus ?thesis using jplt by linarith
              qed
              have c1bound: "\<forall>v \<in> flatIdx (transC1 N). v \<le> ?B N m"
              proof
                fix v assume "v \<in> flatIdx (transC1 N)"
                hence "v \<in> flatIdx (Mark (Pred N) jm1)" using c1eq c1eqT by simp
                hence "v \<le> ?B (Pred N) jm1"
                  using IHpred[OF mkjm1] by simp
                also have "\<dots> \<le> ?B N m"
                  using predB_le[of jm1] mjm1 jm1lt by simp
                finally show "v \<le> ?B N m" .
              qed
              have c2bound: "\<forall>v \<in> flatIdx c2. v \<le> ?B N m"
              proof
                fix v assume "v \<in> flatIdx c2"
                hence "v \<in> flatIdx (transC1 N)
                       \<or> v = enat (entry N 1 ?j1) \<or> v = enat (entry N 1 jp)"
                  using c2sub by auto
                thus "v \<le> ?B N m"
                proof (elim disjE)
                  assume "v \<in> flatIdx (transC1 N)"
                  thus ?thesis using c1bound by simp
                next
                  assume "v = enat (entry N 1 ?j1)"
                  thus ?thesis using ble[of ?j1] mle by simp
                next
                  assume "v = enat (entry N 1 jp)"
                  thus ?thesis using ble[of jp] mjp jple by simp
                qed
              qed
              show ?thesis using fsub c0bound c2bound by auto
            qed
          qed
        qed
      next
        case nmono: False
        \<comment> \<open>(C) multiT branch\<close>
        have nzN: "\<not> zeroT N" using notone by (auto simp: zeroT_def)
        have muN: "multiT N" using nzN nmono by (simp add: multiT_def)
        have cut: "0 < Pcut N \<and> Pcut N \<le> ?j1" using Pcut_le[OF L] by simp
        let ?PJ = "drop (Pcut N) N"
        have PJeq: "P N ! (Lng (P N) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF NT muN])
        have Pne: "P N \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P N) - 1 < Lng (P N)" using Pne by (cases "P N") auto
        have PJRT: "?PJ \<in> RT_PS"
          using m_6_6_P_reduced[OF NT] NR J1lt PJeq by auto
        have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
        have LPJ: "Lng ?PJ = Lng N - Pcut N" by simp
        have LPJlt: "Lng ?PJ < Lng N" using LPJ cut L by linarith
        have cmle: "Pcut N \<le> m" by (rule multi_Marked_last_component(1)[OF NT muN mM])
        \<comment> \<open>identify the def's PJ / j0\<close>
        have c1: "(N \<notin> RT_PS) = False" using NR by simp
        have c2: "(?j1 = 0) = False" using L by simp
        have c3: "monoT N = False" using nmono by simp
        have meq2: "m - (?j1 - Lng (drop (Pcut N) N) + 1) = m - Pcut N"
        proof -
          have "?j1 - Lng ?PJ + 1 = Pcut N"
            using LPJ cut by linarith
          thus ?thesis by simp
        qed
        have markM: "Mark N m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                                 else Mark ?PJ (m - Pcut N))"
        proof -
          have raw: "Mark N m =
              (if P N ! (Lng (P N) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
               else Mark (P N ! (Lng (P N) - 1))
                      (m - (?j1 - Lng (P N ! (Lng (P N) - 1)) + 1)))"
            by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
          show ?thesis unfolding raw PJeq meq2 ..
        qed
        \<comment> \<open>row-1 entries: \<open>?PJ\<close> is a suffix of \<open>N\<close>\<close>
        have entryPJ: "\<And>k. k < Lng ?PJ \<Longrightarrow> entry ?PJ 1 k = entry N 1 (Pcut N + k)"
          by (simp add: entry_def)
        show ?thesis
        proof (cases "?PJ = [(0, 0)]")
          case True
          have kv: "Mark N m = Dpt 0 0\<^sub>B" using markM True by simp
          show ?thesis
          proof
            fix x assume "x \<in> flatIdx (Mark N m)"
            hence "x = 0" using kv by (simp add: flatIdx_Dpt zero_enat_def)
            thus "x \<le> ?B N m" using zle by simp
          qed
        next
          case False
          have kv: "Mark N m = Mark ?PJ (m - Pcut N)" using markM False by simp
          have mPJ: "(?PJ, m - Pcut N) \<in> Marked"
            by (rule multi_Marked_last_component(2)[OF NT muN mM])
          have IHJ: "\<forall>v \<in> flatIdx (Mark ?PJ (m - Pcut N)). v \<le> ?B ?PJ (m - Pcut N)"
            using less.IH[OF LPJlt] mPJ PJRT by blast
          \<comment> \<open>\<open>?B ?PJ (m - Pcut N) \<le> ?B N m\<close>\<close>
          have shiftB: "?B ?PJ (m - Pcut N) \<le> ?B N m"
          proof -
            have mPcut: "m - Pcut N \<le> Lng ?PJ - 1"
              using mle LPJ cut by linarith
            have ne: "{m - Pcut N..Lng ?PJ - 1} \<noteq> {}" using mPcut by auto
            have shift_img:
              "(\<lambda>j. entry ?PJ 1 j) ` {m - Pcut N..Lng ?PJ - 1}
               = (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}"
            proof
              show "(\<lambda>j. entry ?PJ 1 j) ` {m - Pcut N..Lng ?PJ - 1}
                    \<subseteq> (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}"
              proof
                fix y assume "y \<in> (\<lambda>j. entry ?PJ 1 j) ` {m - Pcut N..Lng ?PJ - 1}"
                then obtain k where k: "k \<in> {m - Pcut N..Lng ?PJ - 1}"
                    and yk: "y = entry ?PJ 1 k" by auto
                have klt: "k < Lng ?PJ" using k LPJ cut L by auto
                have "y = entry N 1 (Pcut N + k)" using yk entryPJ[OF klt] by simp
                moreover have "Pcut N + k \<in> {m..Lng N - 1}"
                  using k cmle LPJ cut by auto
                ultimately show "y \<in> (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}" by auto
              qed
            next
              show "(\<lambda>j. entry N 1 j) ` {m..Lng N - 1}
                    \<subseteq> (\<lambda>j. entry ?PJ 1 j) ` {m - Pcut N..Lng ?PJ - 1}"
              proof
                fix y assume "y \<in> (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}"
                then obtain j where j: "j \<in> {m..Lng N - 1}" and yj: "y = entry N 1 j"
                  by auto
                have jge: "Pcut N \<le> j" using j cmle by auto
                define k where "k = j - Pcut N"
                have klt: "k < Lng ?PJ" using j LPJ cut k_def by auto
                have "entry ?PJ 1 k = entry N 1 (Pcut N + k)" by (rule entryPJ[OF klt])
                moreover have "Pcut N + k = j" using jge k_def by simp
                ultimately have "entry ?PJ 1 k = y" using yj by simp
                moreover have "k \<in> {m - Pcut N..Lng ?PJ - 1}"
                  using j klt k_def cmle by auto
                ultimately show "y \<in> (\<lambda>j. entry ?PJ 1 j) ` {m - Pcut N..Lng ?PJ - 1}"
                  by auto
              qed
            qed
            show ?thesis using shift_img by simp
          qed
          show ?thesis
          proof
            fix x assume "x \<in> flatIdx (Mark N m)"
            hence "x \<in> flatIdx (Mark ?PJ (m - Pcut N))" using kv by simp
            hence "x \<le> ?B ?PJ (m - Pcut N)" using IHJ by simp
            also have "\<dots> \<le> ?B N m" using shiftB .
            finally show "x \<le> ?B N m" .
          qed
        qed
      qed
    qed
  qed
qed


section \<open>§7.3 NAbound: condition-VI structural bound (Lemma B) and assembly\<close>

text \<open>Lemma B: when \<open>j\<^sub>0\<close> is non-\<open>M\<close>-admissible, the indices in \<open>(Adm M j\<^sub>0, j\<^sub>0]\<close> are
  all non-admissible, so by the \<open>nadm \<Longrightarrow> nextR\<^sub>1 \<Longrightarrow> strict row-1 increase\<close> chain
  row-1 is non-decreasing on \<open>[Adm M j\<^sub>0, j\<^sub>0]\<close>; hence its max there is \<open>M\<^bsub>1,j\<^sub>0\<^esub>\<close>.\<close>

lemma viB_suffix_max:
  assumes nadm0: "\<not> adm M j0" and j0lt: "j0 < Lng M"
  shows "Max ((\<lambda>j. entry M 1 j) ` {Adm M j0 .. j0}) \<le> entry M 1 j0"
proof -
  let ?jm1 = "Adm M j0"
  have admdef: "?jm1 = Max {j'. adm M j' \<and> j' < j0}"
    using nadm0 by (simp add: Adm_def)
  have fin: "finite {j'. adm M j' \<and> j' < j0}"
    by (rule finite_subset[of _ "{0..<j0}"]) auto
  \<comment> \<open>every index strictly above \<open>?jm1\<close> up to \<open>j\<^sub>0\<close> is non-admissible\<close>
  have nonadm_seg: "\<And>j'. ?jm1 < j' \<Longrightarrow> j' \<le> j0 \<Longrightarrow> \<not> adm M j'"
  proof -
    fix j' assume a: "?jm1 < j'" and b: "j' \<le> j0"
    show "\<not> adm M j'"
    proof (cases "j' = j0")
      case True thus ?thesis using nadm0 by simp
    next
      case False
      hence jlt: "j' < j0" using b by simp
      show ?thesis
      proof
        assume "adm M j'"
        hence "j' \<in> {j'. adm M j' \<and> j' < j0}" using jlt by simp
        hence "j' \<le> ?jm1" using fin admdef by simp
        thus False using a by simp
      qed
    qed
  qed
  \<comment> \<open>the strict-increase step\<close>
  have step: "\<And>j. ?jm1 \<le> j \<Longrightarrow> j < j0 \<Longrightarrow> entry M 1 j < entry M 1 (Suc j)"
  proof -
    fix j assume jge: "?jm1 \<le> j" and jlt: "j < j0"
    have "?jm1 < Suc j" using jge by simp
    moreover have "Suc j \<le> j0" using jlt by simp
    ultimately have "\<not> adm M (Suc j)" by (rule nonadm_seg)
    hence nadmS: "nadm M (Suc j)" by (simp add: adm_def)
    have "Suc j \<le> Lng M" using jlt j0lt by simp
    hence "nextR M 1 (Suc j - 1) (Suc j)" using nadmS by (simp add: nadm_def)
    hence "nextrel1 M j (Suc j)" by (simp add: nextR_def)
    thus "entry M 1 j < entry M 1 (Suc j)" by (simp add: nextrel1_def)
  qed
  \<comment> \<open>hence monotone up to \<open>j\<^sub>0\<close>\<close>
  have mono: "\<And>a. ?jm1 \<le> a \<Longrightarrow> a \<le> j0 \<Longrightarrow> entry M 1 a \<le> entry M 1 j0"
  proof -
    fix a assume A: "?jm1 \<le> a" and B: "a \<le> j0"
    from B A show "entry M 1 a \<le> entry M 1 j0"
    proof (induction "j0 - a" arbitrary: a)
      case 0 hence "a = j0" by simp thus ?case by simp
    next
      case (Suc d)
      have alt: "a < j0" using Suc.hyps(2) Suc.prems(1) by linarith
      have "entry M 1 a < entry M 1 (Suc a)" by (rule step[OF Suc.prems(2) alt])
      moreover have "entry M 1 (Suc a) \<le> entry M 1 j0"
      proof (rule Suc.hyps(1))
        show "d = j0 - Suc a" using Suc.hyps(2) by simp
        show "Suc a \<le> j0" using alt by simp
        show "?jm1 \<le> Suc a" using Suc.prems(2) by simp
      qed
      ultimately show ?case by simp
    qed
  qed
  have adm0: "adm M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
  have j0pos: "0 < j0" using nadm0 adm0 by (cases "j0 = 0") auto
  have nemax: "{j'. adm M j' \<and> j' < j0} \<noteq> {}" using adm0 j0pos by auto
  have jm1lt: "?jm1 < j0"
  proof -
    have "Max {j'. adm M j' \<and> j' < j0} \<in> {j'. adm M j' \<and> j' < j0}"
      by (rule Max_in[OF fin nemax])
    thus ?thesis using admdef by simp
  qed
  have fin2: "finite ((\<lambda>j. entry M 1 j) ` {?jm1 .. j0})" by simp
  have ne2: "(\<lambda>j. entry M 1 j) ` {?jm1 .. j0} \<noteq> {}" using jm1lt by auto
  have "\<forall>x \<in> (\<lambda>j. entry M 1 j) ` {?jm1 .. j0}. x \<le> entry M 1 j0"
    using mono by auto
  thus ?thesis using fin2 ne2 by (simp add: Max_le_iff)
qed

text \<open>NAbound: the non-admissible condition-VI Mark second-index bound, discharged
  by the keystone @{thm [source] Mark_flatIdx_bound} (on \<open>Pred M\<close> at \<open>j\<^sub>-\<^sub>1\<close>) and
  Lemma B @{thm [source] viB_suffix_max}.\<close>

lemma NAbound_holds:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and VI: "transCondVI M" and nadm: "\<not> adm M (transJ0 M)" and t2nz: "transT2 M \<noteq> 0\<^sub>B"
  shows "bpHeadV (transT2 M) < enat (entry M 1 (transJ1 M))"
proof -
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have VIc: "entry M 1 (Lng M - 1) > 0
           \<and> entry M 1 (parent M 0 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1)
           \<and> parent M 0 (Lng M - 1) + 1 = Lng M - 1"
    using VI by (simp add: transCondVI_def)
  have L: "1 < Lng M" using VIc by linarith
  let ?j0 = "transJ0 M"  let ?j1 = "transJ1 M"  let ?jm1 = "transJm1 M"
  have j1eq: "?j1 = Lng M - 1" by (simp add: transJ1_def)
  have j0eq: "?j0 = parent M 0 (Lng M - 1)" by (simp add: transJ0_def transJ1_def)
  have jm1eq: "?jm1 = Adm M ?j0" by (simp add: transJm1_def transJ0_def transJ1_def)
  have j0val: "?j0 = Lng M - 2" using VIc j0eq by linarith
  have j0lt: "?j0 < Lng M" using j0val L by simp
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  have mkjm1: "(Pred M, ?jm1) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp] j0eq jm1eq by simp
  have c1eq: "transC1 M = Mark (Pred M) ?jm1" by (simp add: transC1_def transJm1_def)
  \<comment> \<open>\<open>c\<^sub>1 \<noteq> 0\<close> and principal-list form\<close>
  have J1p: "transJ1 M > 0" using L by (simp add: transJ1_def)
  have pc1: "Lng (PB (transC1 M)) = 1" by (rule transC1_single_principal[OF MR MP J1p T1])
  have c1ne: "transC1 M \<noteq> 0\<^sub>B" using pc1 by (auto simp: PB_def)
  obtain p ps where c1form: "transC1 M = Trm (p # ps)"
  proof -
    obtain xs where xs: "transC1 M = Trm xs" by (cases "transC1 M")
    have "xs \<noteq> []" using c1ne xs by auto
    then obtain p ps where "xs = p # ps" by (cases xs) auto
    thus thesis using xs that by simp
  qed
  \<comment> \<open>\<open>bpHeadV t\<^sub>2 \<in> flatIdx c\<^sub>1\<close>\<close>
  have hv_in: "bpHeadV (transT2 M) \<in> flatIdx (transC1 M)"
  proof -
    have "bpHeadV (transT2 M) \<in> flatIdx (transT2 M)" by (rule bpHeadV_in_flatIdx[OF t2nz])
    moreover have "flatIdx (transT2 M) \<subseteq> flatIdx (transC1 M)"
      unfolding transT2_def using flatIdx_bpHeadT_sub[OF c1form] by simp
    ultimately show ?thesis by auto
  qed
  \<comment> \<open>Lemma A on \<open>Pred M\<close> at \<open>?jm1\<close>\<close>
  have LPred: "Lng (Pred M) - 1 = ?j0" using j0val L by (simp add: Pred_def)
  have bound: "\<forall>v \<in> flatIdx (Mark (Pred M) ?jm1).
                  v \<le> enat (Max ((\<lambda>j. entry (Pred M) 1 j) ` {?jm1 .. Lng (Pred M) - 1}))"
    using Mark_flatIdx_bound mkjm1 predRT by blast
  \<comment> \<open>entries of \<open>Pred M\<close> agree with \<open>M\<close> up to \<open>?j0\<close>\<close>
  have entryagree: "\<And>j. j \<le> ?j0 \<Longrightarrow> entry (Pred M) 1 j = entry M 1 j"
  proof -
    fix j assume "j \<le> ?j0"
    hence "j < Lng M - 1" using j0val L by simp
    thus "entry (Pred M) 1 j = entry M 1 j"
      using L by (simp add: Pred_def entry_def nth_butlast)
  qed
  have maxeq: "(\<lambda>j. entry (Pred M) 1 j) ` {?jm1 .. Lng (Pred M) - 1}
             = (\<lambda>j. entry M 1 j) ` {?jm1 .. ?j0}"
    by (rule image_cong) (use LPred entryagree in auto)
  \<comment> \<open>Lemma B\<close>
  have lemB: "Max ((\<lambda>j. entry M 1 j) ` {?jm1 .. ?j0}) \<le> entry M 1 ?j0"
    using viB_suffix_max[OF nadm j0lt] jm1eq by simp
  \<comment> \<open>combine to \<open>\<le> M\<^bsub>1,j\<^sub>0\<^esub>\<close>\<close>
  have step1: "bpHeadV (transT2 M) \<le> enat (entry M 1 ?j0)"
  proof -
    have "bpHeadV (transT2 M)
          \<le> enat (Max ((\<lambda>j. entry (Pred M) 1 j) ` {?jm1 .. Lng (Pred M) - 1}))"
      using hv_in c1eq bound by auto
    also have "\<dots> = enat (Max ((\<lambda>j. entry M 1 j) ` {?jm1 .. ?j0}))" using maxeq by simp
    also have "\<dots> \<le> enat (entry M 1 ?j0)" using lemB by simp
    finally show ?thesis .
  qed
  \<comment> \<open>\<open>M\<^bsub>1,j\<^sub>0\<^esub> < M\<^bsub>1,j\<^sub>1\<^esub>\<close>\<close>
  have lt: "entry M 1 ?j0 < entry M 1 ?j1"
  proof -
    have "entry M 1 ?j0 + 1 = entry M 1 ?j1" using VIc j0eq j1eq by simp
    thus ?thesis by simp
  qed
  show ?thesis using step1 lt by (metis enat_ord_simps(2) le_less_trans)
qed

text \<open>命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係）claim (3), now UNCONDITIONAL: \<open>lessBT c\<^sub>1 c\<^sub>2\<close>.\<close>

lemma transC1_lessBT_transC2_full:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
  shows "lessBT (transC1 M) (transC2 M)"
  by (rule transC1_lessBT_transC2_modNA[OF MR MP J1pos T1 NAbound_holds[OF MR MP T1]])


section \<open>§7.3 命題（\<open>Pred\<close>-on-\<open>Trans\<close> descent）: \<open>lessBT (Trans (Pred M)) (Trans M)\<close>\<close>

text \<open>The multi-term \<open>Pred\<close>-evaluation helper.  For \<open>M \<in> RT\<^sub>PS\<close> multi with a
  non-trivial last \<open>P\<close>-component \<open>PJ = drop (Pcut M) M\<close> (\<open>1 < Lng PJ\<close>), the
  predecessor acts inside that last component: \<open>Pred M = A @ Pred PJ\<close> with
  \<open>A = take (Pcut M) M\<close>, and \<open>Pred M\<close> is itself multi with the SAME cut, prefix
  \<open>A\<close>, last component \<open>Pred PJ\<close>.  Hence \<open>Trans\<close> evaluates the same way:
  \<open>Trans (Pred M) = Trans A +\<^sub>B (if Pred PJ = [(0,0)] then D\<^bsub>0\<^esub> 0 else Trans (Pred PJ))\<close>.
  Built from @{thm [source] pred_P_decomp} + @{thm [source] poper_last_P_multi}.\<close>

lemma Trans_Pred_multi_last:
  assumes MR: "M \<in> RT_PS" and mu: "multiT M"
    and LPJ: "1 < Lng (drop (Pcut M) M)"
  shows "Trans (Pred M)
         = Trans (take (Pcut M) M)
           +\<^sub>B (if Pred (drop (Pcut M) M) = [(0,0)] then Dpt 0 0\<^sub>B
                else Trans (Pred (drop (Pcut M) M)))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  let ?c = "Pcut M"
  let ?A = "take ?c M"
  let ?PJ = "drop ?c M"
  have cut: "0 < ?c \<and> ?c \<le> Lng M - 1" using Pcut_le[OF L] by simp
  have lastPM: "last (P M) = ?PJ" using poper_last_P_multi[OF mu L] by simp
  have LdropPJ: "Lng ?PJ = Lng M - ?c" by simp
  have cltj1: "?c < Lng M - 1"
  proof -
    have "Lng ?PJ = Lng M - ?c" by simp
    thus ?thesis using LPJ cut by linarith
  qed
  have lenlast_gt1: "1 < Lng (last (P M))" using lastPM LPJ by simp
  \<comment> \<open>\<open>Pred M = A @ Pred PJ\<close>\<close>
  have predsplit: "Pred M = ?A @ Pred ?PJ"
    by (rule poper_Pred_split[OF cltj1 L])
  \<comment> \<open>P-decomposition of \<open>Pred M\<close>: butlast (P M) @ [Pred (last (P M))]\<close>
  have Pdec: "P (Pred M) = butlast (P M) @ [Pred (last (P M))]"
    using pred_P_decomp[OF MT mu] lenlast_gt1 by simp
  have Pdec2: "P (Pred M) = P ?A @ [Pred ?PJ]"
  proof -
    have "butlast (P M) = P ?A" using poper_last_P_multi[OF mu L] by simp
    thus ?thesis using Pdec lastPM by simp
  qed
  \<comment> \<open>\<open>Pred M\<close> is reduced, in \<open>T_PS\<close>, and multi (its \<open>P\<close> has \<open>length > 1\<close>)\<close>
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
  have PAne: "P ?A \<noteq> []" by (rule P_nonempty)
  have lenPpred: "1 < length (P (Pred M))"
    using Pdec2 PAne by (cases "P ?A") auto
  have mupred: "multiT (Pred M)"
    using m_6_2_P_components_2[OF predT] lenPpred by simp
  have Lpred: "1 < Lng (Pred M)"
    by (rule multiT_imp_Lng_gt1[OF predT mupred])
  \<comment> \<open>cut of \<open>Pred M\<close>: its last \<open>P\<close>-component is \<open>Pred PJ = drop (Pcut (Pred M)) (Pred M)\<close>\<close>
  let ?cP = "Pcut (Pred M)"
  have lastPpred: "last (P (Pred M)) = drop ?cP (Pred M)
                   \<and> butlast (P (Pred M)) = P (take ?cP (Pred M))"
    by (rule poper_last_P_multi[OF mupred Lpred])
  have lastval: "last (P (Pred M)) = Pred ?PJ"
    using Pdec2 by simp
  have dropPred: "drop ?cP (Pred M) = Pred ?PJ"
    using lastPpred lastval by simp
  \<comment> \<open>\<open>take (Pcut (Pred M)) (Pred M) = A\<close>: from \<open>Pred M = A @ Pred PJ\<close> and the drop\<close>
  have takePred: "take ?cP (Pred M) = ?A"
  proof -
    have "take ?cP (Pred M) @ drop ?cP (Pred M) = Pred M" by simp
    hence "take ?cP (Pred M) @ Pred ?PJ = ?A @ Pred ?PJ"
      using dropPred predsplit by simp
    thus ?thesis by simp
  qed
  \<comment> \<open>evaluate \<open>Trans (Pred M)\<close> via the multi recursion\<close>
  have domTP: "Trans_Mark_dom (Inl (Pred M))" by (rule m_7_3_Trans_welldef[OF predRT])
  have LgtP: "\<not> Lng (Pred M) \<le> Suc 0" using Lpred by simp
  have nmonoP: "\<not> monoT (Pred M)" using mupred by (simp add: multiT_def)
  have PJeqP: "P (Pred M) ! (Lng (P (Pred M)) - 1) = drop ?cP (Pred M)"
    by (rule trans_multiT_last_component(1)[OF predT mupred])
  have j0eqP: "Lng (Pred M) - 1 - Lng (P (Pred M) ! (Lng (P (Pred M)) - 1)) + 1 = ?cP"
    by (rule trans_multiT_last_component(2)[OF predT mupred])
  have c1: "(Pred M \<notin> RT_PS) = False" using predRT by simp
  have c2: "(Lng (Pred M) - 1 = 0) = False" using Lpred by simp
  have c3: "monoT (Pred M) = False" using nmonoP by simp
  have cutP: "0 < ?cP \<and> ?cP \<le> Lng (Pred M) - 1" using Pcut_le[OF Lpred] by simp
  have LdJP: "Lng (drop ?cP (Pred M)) = Lng (Pred M) - ?cP" by simp
  have AeqP: "seg (Pred M) 0 (Lng (Pred M) - 1 - Lng (drop ?cP (Pred M)) + 1 - 1)
              = take ?cP (Pred M)"
  proof -
    have "Lng (Pred M) - 1 - Lng (drop ?cP (Pred M)) + 1 - 1 = ?cP - 1"
      using LdJP cutP by linarith
    moreover have "seg (Pred M) 0 (?cP - 1) = take (Suc (?cP - 1)) (Pred M)"
      by (rule seg_0_eq_take) (use cutP Lpred in linarith)
    moreover have "Suc (?cP - 1) = ?cP" using cutP by simp
    ultimately show ?thesis by simp
  qed
  have transP: "Trans (Pred M)
      = (if drop ?cP (Pred M) = [(0,0)] then Trans (take ?cP (Pred M)) +\<^sub>B Dpt 0 0\<^sub>B
         else Trans (take ?cP (Pred M)) +\<^sub>B Trans (drop ?cP (Pred M)))"
  proof -
    have raw: "Trans (Pred M) =
        (if P (Pred M) ! (Lng (P (Pred M)) - 1) = [(0, 0)]
         then Trans (seg (Pred M) 0
                 (Lng (Pred M) - 1 - Lng (P (Pred M) ! (Lng (P (Pred M)) - 1)) + 1 - 1))
                +\<^sub>B Dpt 0 0\<^sub>B
         else Trans (seg (Pred M) 0
                 (Lng (Pred M) - 1 - Lng (P (Pred M) ! (Lng (P (Pred M)) - 1)) + 1 - 1))
                +\<^sub>B Trans (P (Pred M) ! (Lng (P (Pred M)) - 1)))"
      by (subst Trans.psimps[OF domTP]) (simp only: c1 c2 c3 if_False Let_def)
    show ?thesis unfolding raw PJeqP AeqP ..
  qed
  \<comment> \<open>rewrite using \<open>take = A\<close> and \<open>drop = Pred PJ\<close>; the left guard never fires\<close>
  have notPJ00: "?PJ \<noteq> [(0,0)]"
  proof
    assume "?PJ = [(0,0)]"
    hence "Lng ?PJ = 1" by simp
    thus False using LPJ by simp
  qed
  show ?thesis
    using transP takePred dropPred notPJ00 by simp
qed

text \<open>命題（\<open>Pred\<close>-on-\<open>Trans\<close> descent）: \<open>1 < Lng M \<Longrightarrow> lessBT (Trans (Pred M)) (Trans M)\<close>
  on \<open>RT\<^sub>PS\<close>.  Strong \<open>Lng\<close>-induction; the mono surgery branch mirrors
  @{thm [source] trans_inv_B_hard} (\<open>c\<^sub>1\<close>/\<open>c\<^sub>2\<close> replacement) closed by
  @{thm [source] transC1_lessBT_transC2_full} + @{thm [source] scbext_lessBT};
  the multi branch recurses on the last \<open>P\<close>-component (smaller \<open>Lng\<close>) via
  @{thm [source] Trans_Pred_multi_last} + @{thm [source] lessBT_addBT_mono_right}.
  Empirically 0 failures / 7042 cases.\<close>

lemma m_7_3_Pred_Trans_descend:
  "M \<in> RT_PS \<longrightarrow> 1 < Lng M \<longrightarrow> lessBT (Trans (Pred M)) (Trans M)"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (rule impI)+
    assume MR: "M \<in> RT_PS" and L: "1 < Lng M"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
    have nzM: "\<not> zeroT M" using L by (auto simp: zeroT_def)
    show "lessBT (Trans (Pred M)) (Trans M)"
    proof (cases "monoT M")
      case mono: True
      have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
      have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
      show ?thesis
      proof (cases "Trans (Pred M) = 0\<^sub>B")
        case t1z: True
        let ?b = "entry M 1 (Lng M - 1)"
        have tv: "Trans M = Dpt 0 (Dpt (enat ?b) 0\<^sub>B)"
          using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
        show ?thesis using t1z tv by simp
      next
        case t1ne: False
        \<comment> \<open>(mono) surgery branch, mirroring @{thm [source] trans_inv_B_hard}\<close>
        have IHt1: "dfree_BT (Trans (Pred M))"
          using Trans_Mark_invariant_aux predRT by blast
        have IHmk: "\<And>m'. (Pred M, m') \<in> Marked
                     \<Longrightarrow> (Trans (Pred M), Mark (Pred M) m') \<in> MarkedB"
          using Trans_Mark_invariant_aux predRT by blast
        have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
        let ?t1 = "Trans (Pred M)"
        let ?bv = "entry M 1 (Lng M - 1)"
        define jp where "jp = parent M 0 (Lng M - 1)"
        define c1 where "c1 = Mark (Pred M) (Adm M jp)"
        define vv where "vv = bpHeadV c1"
        define tt2 where "tt2 = bpHeadT c1"
        define JJ1 where "JJ1 = Lng (PB tt2) - 1"
        define pj where "pj = PB tt2 ! JJ1"
        define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
        define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
        define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
        define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                               then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                               else if transCondVI M
                               then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                               else if tt2 = 0\<^sub>B
                               then Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                               else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                                  (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
        define sb1 where "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
        have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
          using Trans.psimps[OF domT] MR Lgt1 mono t1ne
          unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                    tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                    ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                    c2_def[symmetric] sb1_def[symmetric]
          by simp
        \<comment> \<open>identify \<open>c\<^sub>1 = transC1 M\<close>, \<open>c\<^sub>2 = transC2 M\<close>\<close>
        have transJ1eq: "transJ1 M = Lng M - 1" by (simp add: transJ1_def)
        have transJ0eq: "transJ0 M = jp" by (simp add: transJ0_def transJ1_def jp_def)
        have transJm1eq: "transJm1 M = Adm M jp"
          by (simp add: transJm1_def transJ0eq)
        have c1eqT: "c1 = transC1 M"
          by (simp add: c1_def transC1_def transJm1eq)
        have c2eqT: "c2 = transC2 M"
          unfolding c2_def transC2_def Let_def
            vv_def tt2_def c1eqT transV_def transT2_def
            JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
          by simp
        \<comment> \<open>SOME decomposition of \<open>t\<^sub>1\<close> at \<open>flatBT c\<^sub>1\<close>\<close>
        have mkdA: "(Pred M, Adm M jp) \<in> Marked"
          using Marked_Pred_Adm[OF MT L hp] jp_def by simp
        have mb1: "(?t1, c1) \<in> MarkedB" using IHmk[OF mkdA] c1_def by simp
        have t1neT: "?t1 \<noteq> Trm []" using t1ne by simp
        have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
          using mb1 unfolding MarkedB_def by auto
        have dsome: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
          unfolding sb1_def by (rule someI_ex[OF exsb])
        \<comment> \<open>\<open>c\<^sub>1 = Trm [pc]\<close>\<close>
        have iptc1: "isPTB_str (flatBT c1)"
          using dsome t1neT by (simp add: scb_decomp_def)
        then obtain pc where pcf: "dfree_BP pc" and pcl: "flatBT c1 = flatBP pc"
          by (auto simp: isPTB_str_def)
        have c1p: "c1 = Trm [pc]"
        proof -
          have "flatBT c1 = flatBT (Trm [pc])" using pcl by simp
          thus ?thesis by (rule m_7_flatBT_inj)
        qed
        \<comment> \<open>\<open>c\<^sub>2 = Trm [pc2]\<close>, via single-principal reconstruction\<close>
        have NP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
        have J1pos: "transJ1 M > 0" using L by (simp add: transJ1_def)
        have T1ne: "transT1 M \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
        have c2pc1: "Lng (PB (transC2 M)) = 1" by (rule transC2_single_principal)
        have c2recon: "transC2 M = Dpt (bpHeadV (transC2 M)) (bpHeadT (transC2 M))"
          by (rule principal_reconstruct[OF c2pc1])
        obtain pc2 where c2p: "c2 = Trm [pc2]"
          using c2recon c2eqT by (metis BT.exhaust untrm.simps)
        have iptc2: "isPTB_str (flatBT (Trm [pc2]))"
        proof -
          have vne: "transV M \<noteq> \<infinity>"
          proof -
            have pc1: "Lng (PB (transC1 M)) = 1"
              by (rule transC1_single_principal[OF MR NP J1pos T1ne])
            have c1ne: "transC1 M \<noteq> 0\<^sub>B"
            proof
              assume "transC1 M = 0\<^sub>B"
              thus False using pc1 by (simp add: PB_def)
            qed
            have c1TB: "transC1 M \<in> T_B"
              using m_7_3_Mark_in_T_B[OF predRT mkdA] transJm1eq[symmetric]
              by (simp add: transC1_def)
            have c1Dpt: "transC1 M = Dpt (transV M) (transT2 M)"
              using principal_reconstruct[OF pc1]
              by (simp add: transV_def transT2_def)
            thus ?thesis using c1TB unfolding c1Dpt by (auto simp: T_B_def)
          qed
          have t2df: "dfree_BT (transT2 M)"
          proof -
            have pc1: "Lng (PB (transC1 M)) = 1"
              by (rule transC1_single_principal[OF MR NP J1pos T1ne])
            have c1TB: "transC1 M \<in> T_B"
              using m_7_3_Mark_in_T_B[OF predRT mkdA] transJm1eq[symmetric]
              by (simp add: transC1_def)
            have c1Dpt: "transC1 M = Dpt (transV M) (transT2 M)"
              using principal_reconstruct[OF pc1]
              by (simp add: transV_def transT2_def)
            thus ?thesis using c1TB unfolding c1Dpt by (auto simp: T_B_def)
          qed
          have c2df: "dfree_BT c2" using dfree_transC2[OF vne t2df] c2eqT by simp
          have "dfree_BT (Trm [pc2])" using c2df c2p by simp
          then obtain p where "pc2 = p" and "dfree_BP p" by auto
          thus ?thesis by (auto simp: isPTB_str_def)
        qed
        \<comment> \<open>replace the principal \<open>c\<^sub>1\<close> by \<open>c\<^sub>2\<close> to read off \<open>Trans M\<close>\<close>
        have dsome': "scb_decomp ?t1 (fst sb1) (flatBT (Trm [pc])) (snd sb1)"
          using dsome c1p by simp
        obtain t' where t'f: "flatBT t' = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
            and t'd: "scb_decomp t' (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
          using scb_replace_principal[OF dsome' iptc2] by blast
        have transM: "Trans M = t'"
          using trans_val t'f c2p unflatBT_flat[of t'] by simp
        \<comment> \<open>the two flat equalities for \<open>scbext_lessBT\<close>\<close>
        have flat1: "flatBT ?t1 = fst sb1 @ flatBP pc @ snd sb1"
          using dsome c1p by (simp add: scb_decomp_def)
        have flat2: "flatBT (Trans M) = fst sb1 @ flatBP pc2 @ snd sb1"
          using transM t'f by simp
        have brp: "\<forall>x \<in> set (snd sb1). x = RP"
          using dsome by (simp add: scb_decomp_def)
        \<comment> \<open>\<open>lessBP pc pc2\<close> from \<open>lessBT c\<^sub>1 c\<^sub>2\<close>\<close>
        have lbt: "lessBT (transC1 M) (transC2 M)"
          by (rule transC1_lessBT_transC2_full[OF MR NP J1pos T1ne])
        have lbp: "lessBP pc pc2"
        proof -
          have "lessBT (Trm [pc]) (Trm [pc2])" using lbt c1eqT c2eqT c1p c2p by simp
          thus ?thesis by simp
        qed
        show ?thesis
          by (rule scbext_lessBT[OF flat1 flat2 brp lbp])
      qed
    next
      case nmono: False
      \<comment> \<open>(multi) branch: recurse on the last \<open>P\<close>-component\<close>
      have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
      let ?A = "take (Pcut M) M"
      let ?PJ = "drop (Pcut M) M"
      have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
      have AR: "?A \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF MR muM])
      have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
        by (rule trans_multiT_last_component(1)[OF MT muM])
      have Pne: "P M \<noteq> []" by (rule P_nonempty)
      have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
      have PJRT: "?PJ \<in> RT_PS"
        using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
      have LPJ: "Lng ?PJ < Lng M"
      proof -
        have "Lng ?PJ = Lng M - Pcut M" by simp
        thus ?thesis using cut L by linarith
      qed
      \<comment> \<open>\<open>transM\<close> for \<open>M\<close>, mirroring @{thm [source] trans_inv_C}\<close>
      have domTM: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
      have nmono': "\<not> monoT M" using muM by (simp add: multiT_def)
      have j0eqM: "Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 = Pcut M"
        by (rule trans_multiT_last_component(2)[OF MT muM])
      have c1: "(M \<notin> RT_PS) = False" using MR by simp
      have c2: "(Lng M - 1 = 0) = False" using L by simp
      have c3: "monoT M = False" using nmono' by simp
      have LdJ: "Lng ?PJ = Lng M - Pcut M" by simp
      have Aeq2: "seg M 0 (Lng M - 1 - Lng ?PJ + 1 - 1) = ?A"
      proof -
        have "Lng M - 1 - Lng ?PJ + 1 - 1 = Pcut M - 1" using LdJ cut by linarith
        moreover have "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
          by (rule seg_0_eq_take) (use cut L in linarith)
        moreover have "Suc (Pcut M - 1) = Pcut M" using cut by simp
        ultimately show ?thesis by simp
      qed
      have transM: "Trans M = (if ?PJ = [(0, 0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B
                               else Trans ?A +\<^sub>B Trans ?PJ)"
      proof -
        have raw: "Trans M =
            (if P M ! (Lng (P M) - 1) = [(0, 0)]
             then Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                    +\<^sub>B Dpt 0 0\<^sub>B
             else Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                    +\<^sub>B Trans (P M ! (Lng (P M) - 1)))"
          by (subst Trans.psimps[OF domTM]) (simp only: c1 c2 c3 if_False Let_def)
        show ?thesis unfolding raw PJeq Aeq2 ..
      qed
      \<comment> \<open>\<open>PJ \<noteq> [(0,0)]\<close> exactly when \<open>1 < Lng PJ\<close>, but split on \<open>Lng PJ\<close>\<close>
      show ?thesis
      proof (cases "1 < Lng ?PJ")
        case PJ1: False
        \<comment> \<open>\<open>Lng PJ = 1\<close>: \<open>Pcut M = Lng M - 1\<close>, so \<open>Pred M = A\<close>\<close>
        have LPJ1: "Lng ?PJ = 1"
        proof -
          have "Lng ?PJ = Lng M - Pcut M" by simp
          hence "0 < Lng ?PJ" using cut L by linarith
          thus ?thesis using PJ1 by simp
        qed
        have cj1: "Pcut M = Lng M - 1" using LPJ1 LdJ by simp
        have predA: "Pred M = ?A"
        proof -
          have "Pred M = take (Lng M - 1) M" using L by (simp add: Pred_def butlast_conv_take)
          thus ?thesis using cj1 by simp
        qed
        \<comment> \<open>the right summand is nonzero, so \<open>lessBT (Trans A) (Trans A +\<^sub>B nz)\<close>\<close>
        show ?thesis
        proof (cases "?PJ = [(0, 0)]")
          case True
          have tv: "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM True by simp
          have "lessBT (Trans ?A) (Trans ?A +\<^sub>B Dpt 0 0\<^sub>B)"
            by (rule lessBT_addBT_self) simp
          thus ?thesis using tv predA by simp
        next
          case False
          have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
          have nzPJ: "\<not> zeroT ?PJ"
          proof
            assume z: "zeroT ?PJ"
            obtain v where v: "?PJ = [(v, v)]"
              using m_6_6_oneColumn[OF PJT] PJRT LPJ1 by auto
            have "entry ?PJ 1 0 = 0" using z by (simp add: zeroT_def)
            hence "v = 0" using v by (simp add: entry_def)
            thus False using False v by simp
          qed
          have nz: "Trans ?PJ \<noteq> 0\<^sub>B"
            using m_7_3_Trans_zeroT[OF PJRT] nzPJ by simp
          have tv: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM False by simp
          have "lessBT (Trans ?A) (Trans ?A +\<^sub>B Trans ?PJ)"
            by (rule lessBT_addBT_self[OF nz])
          thus ?thesis using tv predA by simp
        qed
      next
        case PJgt1: True
        \<comment> \<open>\<open>1 < Lng PJ\<close>: recurse on \<open>PJ\<close>\<close>
        have notPJ00: "?PJ \<noteq> [(0, 0)]"
        proof
          assume "?PJ = [(0, 0)]"
          hence "Lng ?PJ = 1" by simp
          thus False using PJgt1 by simp
        qed
        have tvM: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM notPJ00 by simp
        \<comment> \<open>helper: \<open>Trans (Pred M) = Trans A +\<^sub>B Z\<close>\<close>
        have tvPred: "Trans (Pred M)
            = Trans ?A +\<^sub>B (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B
                            else Trans (Pred ?PJ))"
          using Trans_Pred_multi_last[OF MR muM PJgt1] by simp
        \<comment> \<open>suffices: \<open>lessBT Z (Trans PJ)\<close>\<close>
        have inner: "lessBT (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Trans (Pred ?PJ))
                            (Trans ?PJ)"
        proof (cases "Pred ?PJ = [(0, 0)]")
          case predzero: True
          \<comment> \<open>\<open>Pred PJ = [(0,0)]\<close> \<Rightarrow> \<open>Lng PJ = 2\<close>, \<open>PJ\<close> mono in \<open>t1z\<close> branch\<close>
          have LPredPJ: "Lng (Pred ?PJ) = 1" using predzero by simp
          have predPJb: "Pred ?PJ = butlast ?PJ" using PJgt1 by (simp add: Pred_def)
          have LPJ2: "Lng ?PJ = 2" using LPredPJ predPJb PJgt1 by simp
          \<comment> \<open>\<open>PJ\<close> is the last ancestor-anchored component, hence mono\<close>
          have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
          have lec: "leR M 0 (Pcut M) (Lng M - 1)"
            using P_add_Pcut_props[OF L] by simp
          have cltj1: "Pcut M < Lng M - 1" using LPJ2 LdJ cut by linarith
          have cL: "Pcut M < Lng M" using cut L by linarith
          have monoPJ: "monoT ?PJ"
          proof -
            have "monoT (seg M (Pcut M) (Lng M - 1))"
              by (rule m_6_2_mono_ancestor_slice[OF MT cltj1 lec])
            thus ?thesis using drop_eq_seg[OF cL] by simp
          qed
          \<comment> \<open>\<open>Trans (Pred PJ) = 0\<close> since \<open>Pred PJ = [(0,0)]\<close>\<close>
          have t1zPJ: "Trans (Pred ?PJ) = 0\<^sub>B"
            using predzero Trans_singleton[of 0] by simp
          \<comment> \<open>\<open>PJ\<close> in mono-\<open>t1z\<close> branch: \<open>Trans PJ = Dpt 0 (Dpt (enat b) 0)\<close>\<close>
          have domPJ: "Trans_Mark_dom (Inl ?PJ)" by (rule m_7_3_Trans_welldef[OF PJRT])
          have LPJgt: "\<not> Lng ?PJ \<le> Suc 0" using PJgt1 by simp
          let ?bPJ = "entry ?PJ 1 (Lng ?PJ - 1)"
          have tvPJ: "Trans ?PJ = Dpt 0 (Dpt (enat ?bPJ) 0\<^sub>B)"
            using Trans.psimps[OF domPJ] PJRT LPJgt monoPJ t1zPJ by (simp add: Let_def)
          show ?thesis using predzero tvPJ by simp
        next
          case predne: False
          \<comment> \<open>IH on \<open>PJ\<close>: smaller \<open>Lng\<close>, reduced, \<open>1 < Lng PJ\<close>\<close>
          have ih: "lessBT (Trans (Pred ?PJ)) (Trans ?PJ)"
            using less.IH[OF LPJ] PJRT PJgt1 by blast
          show ?thesis using predne ih by simp
        qed
        have "lessBT (Trans ?A +\<^sub>B (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B
                                    else Trans (Pred ?PJ)))
                     (Trans ?A +\<^sub>B Trans ?PJ)"
          by (rule lessBT_addBT_mono_right[OF inner])
        thus ?thesis using tvPred tvM by simp
      qed
    qed
  qed
qed


section \<open>§7.3 系（\<open>Mark\<close> の左端の基本性質）— content.md 2310\<close>

text \<open>\<open>Mark N m\<close> is either \<open>0\<close> or a single principal \<open>D\<^bsub>N\<^sub>1\<^sub>,\<^sub>m\<^esub>(\<dots>)\<close> whose
  left index is exactly \<open>entry N 1 m\<close>.  Empirically verified
  (\<open>bpHeadV (Mark N m) = entry N 1 m\<close> over 9699 marked cases, 0 failures).
  Strong \<open>Lng\<close>-induction, mirroring @{thm [source] Mark_rightmost1_forward} and
  the surgery of @{thm [source] Mark_flatIdx_bound}.\<close>

text \<open>Head-symbol bridge: the first symbol of \<open>flatBT (Trm [DB v t])\<close> is
  \<open>Dsym v\<close>, so a single principal term's leading flat symbol fixes its
  \<open>bpHeadV\<close>.\<close>

lemma flatBT_principal_head:
  "flatBT (Trm [DB v t]) = Dsym v # flatBT t"
  by simp

text \<open>The mono, \<open>t\<^sub>1 \<noteq> 0\<close> (surgery) branch of the marked nesting, taking the
  \<open>Pred M\<close> induction hypothesis as an assumption.  Both \<open>Mark M m\<close> and
  \<open>Mark M m'\<close> are the same principal \<open>c\<^sub>2\<close>-replacement performed inside
  \<open>Mark (Pred M) m\<close> resp. \<open>Mark (Pred M) m'\<close>; since the latter two nest (IH),
  the former two nest by \<open>scb\<close>-composition (@{thm [source] m_7_2_scb_compose},
  @{thm [source] m_7_2_scb_unique_sb}).  The \<open>m' = j\<^sub>1\<close> end is handled by the
  rightmost block \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<close> of \<open>c\<^sub>2\<close>.\<close>

lemma Mark_MarkedB_nest_surgery:
  assumes MR: "M \<in> RT_PS" and mono: "monoT M" and L: "1 < Lng M"
    and t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B"
    and mM: "(M, m) \<in> Marked" and mM': "(M, m') \<in> Marked" and mle: "m \<le> m'"
    and IHpred: "\<And>a b. (Pred M, a) \<in> Marked \<Longrightarrow> (Pred M, b) \<in> Marked
                 \<Longrightarrow> a \<le> b \<Longrightarrow> (Mark (Pred M) a, Mark (Pred M) b) \<in> MarkedB"
  shows "(Mark M m, Mark M m') \<in> MarkedB"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  have leM: "leR M 0 m (Lng M - 1)" using mM by (simp add: Marked_def)
  have mleN: "m < Lng M" using leM by (simp add: leR_def le0_def)
  have mle1: "m \<le> Lng M - 1" using mleN by linarith
  have leM': "leR M 0 m' (Lng M - 1)" using mM' by (simp add: Marked_def)
  have m'leN: "m' < Lng M" using leM' by (simp add: leR_def le0_def)
  have m'le1: "m' \<le> Lng M - 1" using m'leN by linarith
  have admN: "adm M m" using mM by (simp add: Marked_def)
  have admN': "adm M m'" using mM' by (simp add: Marked_def)
  have selfMB_bv: "(Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B,
                    Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B) \<in> MarkedB"
  proof -
    have "scb_decomp (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B) []
            (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) []"
      by (rule scb_decomp_self) (rule isPTB_str_Dpt, simp_all)
    thus ?thesis unfolding MarkedB_def by auto
  qed
  let ?t1 = "Trans (Pred M)"
  let ?bv = "entry M 1 (Lng M - 1)"
  let ?j1 = "Lng M - 1"
  define jp where "jp = parent M 0 (Lng M - 1)"
  define jm1 where "jm1 = Adm M jp"
  define c1 where "c1 = Mark (Pred M) (Adm M jp)"
  define vv where "vv = bpHeadV c1"
  define tt2 where "tt2 = bpHeadT c1"
  define JJ1 where "JJ1 = Lng (PB tt2) - 1"
  define pj where "pj = PB tt2 ! JJ1"
  define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
  define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
  define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
  define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                         then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                         else if transCondVI M
                         then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                         else if tt2 = 0\<^sub>B
                         then Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                         else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                            (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
  \<comment> \<open>induction facts for \<open>c\<^sub>1\<close>\<close>
  have mkdA: "(Pred M, Adm M jp) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp] jp_def by simp
  have mb1: "(?t1, c1) \<in> MarkedB"
    using m_7_3_Trans_Mark_MarkedB[OF predRT mkdA] c1_def by simp
  have t1neT: "?t1 \<noteq> Trm []" using t1ne by simp
  define sb1 where "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
  have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
    using mb1 unfolding MarkedB_def by auto
  have dsome: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
    unfolding sb1_def by (rule someI_ex[OF exsb])
  have iptc1: "isPTB_str (flatBT c1)"
    using dsome t1neT by (simp add: scb_decomp_def)
  then obtain pc where pcf: "dfree_BP pc" and pcl: "flatBT c1 = flatBP pc"
    by (auto simp: isPTB_str_def)
  have c1p: "c1 = Trm [pc]"
  proof -
    have "flatBT c1 = flatBT (Trm [pc])" using pcl by simp
    thus ?thesis by (rule m_7_flatBT_inj)
  qed
  obtain wv tb where pcw: "pc = DB wv tb" by (cases pc) auto
  have vvv: "vv = wv" using vv_def c1p pcw by simp
  have tt2v: "tt2 = tb" using tt2_def c1p pcw by simp
  have wvne: "wv \<noteq> \<infinity>" and tbdf: "dfree_BT tb" using pcf pcw by auto
  \<comment> \<open>\<open>c\<^sub>2\<close> is a principal dfree term whose rightmost block is \<open>D\<^bsub>?bv\<^esub> 0\<close>\<close>
  have c2shape: "\<exists>X. c2 = Dpt vv X \<and> dfree_BT X \<and> (X, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
  proof -
    have selfb: "(Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
    proof -
      have "scb_decomp (Dpt (enat ?bv) 0\<^sub>B) [] (flatBT (Dpt (enat ?bv) 0\<^sub>B)) []"
        by (rule scb_decomp_self) (rule isPTB_str_Dpt, simp_all)
      thus ?thesis unfolding MarkedB_def by auto
    qed
    have iptb: "isPTB_str (flatBT (Dpt (enat ?bv) 0\<^sub>B))"
      by (rule isPTB_str_Dpt) simp_all
    have dbne: "Dpt (enat ?bv) 0\<^sub>B \<noteq> 0\<^sub>B" by simp
    consider (A) "transCondI M \<or> transCondIII M \<or> transCondV M"
      | (VI) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "transCondVI M"
      | (Z) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "\<not> transCondVI M"
            "tt2 = 0\<^sub>B"
      | (E) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "\<not> transCondVI M"
            "tt2 \<noteq> 0\<^sub>B"
      by blast
    thus ?thesis
    proof cases
      case A
      have x: "c2 = Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)" using A c2_def by simp
      have df: "dfree_BT (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)"
        using tt2v tbdf by (cases tb) auto
      have mb: "(tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF selfb dbne])
      show ?thesis using x df mb by blast
    next
      case VI
      have x: "c2 = Dpt vv (Dpt (enat ?bv) 0\<^sub>B)" using VI c2_def by simp
      have mb: "(Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB" by (rule selfb)
      show ?thesis using x mb by auto
    next
      case Z
      have x: "c2 = Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))"
        using Z c2_def by simp
      have mb: "(Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B),
                 Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_Dpt_lift[OF selfb iptb])
      show ?thesis using x mb by auto
    next
      case E
      have x: "c2 = Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                   (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B))"
        using E c2_def by simp
      have df3: "dfree_BT tt3"
      proof -
        have "dfree_BT (SigmaB (take JJ1 (PB tb)))"
          using tbdf by (cases tb) (auto simp: SigmaB_def PB_def dest!: in_set_takeD)
        thus ?thesis using tt3_def tt2v tbdf by simp
      qed
      have df4: "dfree_BT tt4"
      proof -
        have tbne: "untrm tb \<noteq> []" using E(3) tt2v by (cases tb) auto
        have inr: "JJ1 < Lng (PB tb)"
          using JJ1_def tt2v tbne by (simp add: PB_def)
        have "pj \<in> set (PB tb)" using pj_def tt2v inr by simp
        hence "dfree_BT pj" using tbdf by (cases tb) (auto simp: PB_def)
        hence "dfree_BT (bpHeadT pj)" by (cases pj rule: bpHeadT.cases) auto
        thus ?thesis using tt4_def tt2v tbdf by simp
      qed
      have dfsum: "dfree_BT (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)"
        using df4 by (cases tt4) auto
      have mbin: "(tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF selfb dbne])
      have mbmid: "(Dpt (enat (entry M 1 jp)) (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B),
                    Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_Dpt_lift[OF mbin iptb])
      have mbout: "(tt3 +\<^sub>B Dpt (enat (entry M 1 jp)) (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B),
                    Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF mbmid]) simp
      have dfall: "dfree_BT (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                    (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B))"
        using df3 dfsum by (cases tt3) auto
      show ?thesis using x mbout dfall by blast
    qed
  qed
  obtain X2 where c2X: "c2 = Dpt vv X2" and X2df: "dfree_BT X2"
      and X2mb: "(X2, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
    using c2shape by blast
  have c2df: "dfree_BT c2" using c2X X2df wvne vvv by simp
  have iptc2: "isPTB_str (flatBT c2)"
    using c2X by (intro isPTB_str_Dpt[of vv X2, folded c2X])
                 (use wvne vvv X2df in simp_all)
  obtain pc2 where c2p: "c2 = Trm [pc2]" using c2X by auto
  have c2mb: "(c2, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
  proof -
    have iptb: "isPTB_str (flatBT (Dpt (enat ?bv) 0\<^sub>B))"
      by (rule isPTB_str_Dpt) simp_all
    show ?thesis using MarkedB_Dpt_lift[OF X2mb iptb] c2X by simp
  qed
  \<comment> \<open>generic evaluation of a surgery \<open>Mark M k\<close> for \<open>k < j\<^sub>1\<close>\<close>
  have mark_surg: "\<And>k. k < ?j1 \<Longrightarrow> (Mark (Pred M) k, c1) \<in> MarkedB
      \<Longrightarrow> Mark M k = unflatBT
            (fst (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb))
             @ flatBT c2
             @ snd (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb)))"
  proof -
    fix k assume klt: "k < ?j1" and kmb: "(Mark (Pred M) k, c1) \<in> MarkedB"
    have "Mark M k = (if (Mark (Pred M) k, c1) \<in> MarkedB
          then unflatBT
                 (fst (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb))
                  @ flatBT c2
                  @ snd (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb)))
          else Dpt (enat ?bv) 0\<^sub>B)"
      using Mark.psimps[OF domK] MR Lgt1 mono t1ne klt
      unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                c2_def[symmetric]
      by simp
    thus "Mark M k = unflatBT
            (fst (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb))
             @ flatBT c2
             @ snd (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb)))"
      using kmb by simp
  qed
  \<comment> \<open>evaluation of \<open>Mark M j\<^sub>1 = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<close>\<close>
  have mark_last: "Mark M ?j1 = Dpt (enat ?bv) 0\<^sub>B"
    using Mark.psimps[OF domK] MR Lgt1 mono t1ne
    unfolding Let_def jp_def[symmetric]
    by simp
  \<comment> \<open>marked-block / principality of a surgery value at \<open>k < j\<^sub>1\<close>\<close>
  have surg_facts: "\<And>k. (M, k) \<in> Marked \<Longrightarrow> k < ?j1 \<Longrightarrow>
        (Mark (Pred M) k, c1) \<in> MarkedB
      \<and> (\<exists>sm. scb_decomp (Mark (Pred M) k) (fst sm) (flatBT c1) (snd sm)
            \<and> Mark M k = unflatBT (fst sm @ flatBT c2 @ snd sm)
            \<and> flatBT (Mark M k) = fst sm @ flatBT c2 @ snd sm
            \<and> isPTB_str (flatBT (Mark M k))
            \<and> Mark M k \<noteq> Trm []
            \<and> scb_decomp (Mark M k) (fst sm) (flatBT c2) (snd sm))"
  proof -
    fix k assume mMk: "(M, k) \<in> Marked" and klt: "k < ?j1"
    have mPk: "(Pred M, k) \<in> Marked" by (rule Marked_Pred[OF MT L mMk klt])
    \<comment> \<open>\<open>k \<le> jm1 = Adm M jp\<close>, so \<open>c\<^sub>1 = Mark (Pred M) jm1\<close> nests in \<open>Mark (Pred M) k\<close>\<close>
    have admMk: "adm M k" using mMk by (simp add: Marked_def)
    have kjp: "k \<le> jp" using surg_parent_ge[OF mMk mono L klt] jp_def by simp
    have kjm1: "k \<le> Adm M jp" using surg_adm_ge[OF admMk kjp] by simp
    have mbk: "(Mark (Pred M) k, c1) \<in> MarkedB"
      using IHpred[OF mPk mkdA kjm1] c1_def by simp
    define sm where "sm = (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb))"
    have exsm: "\<exists>sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb)"
      using mbk unfolding MarkedB_def by auto
    have dsm: "scb_decomp (Mark (Pred M) k) (fst sm) (flatBT c1) (snd sm)"
      unfolding sm_def by (rule someI_ex[OF exsm])
    \<comment> \<open>\<open>Mark (Pred M) k\<close> is a principal term (block of nonzero \<open>Trans (Pred M)\<close>)\<close>
    have mb0: "(?t1, Mark (Pred M) k) \<in> MarkedB"
      by (rule m_7_3_Trans_Mark_MarkedB[OF predRT mPk])
    obtain s0 b0 where d0: "scb_decomp ?t1 s0 (flatBT (Mark (Pred M) k)) b0"
      using mb0 by (auto simp: MarkedB_def)
    have iptc0: "isPTB_str (flatBT (Mark (Pred M) k))"
      using d0 t1neT by (simp add: scb_decomp_def)
    then obtain pc0 where pc0l: "flatBT (Mark (Pred M) k) = flatBP pc0"
      by (auto simp: isPTB_str_def)
    have c0p: "Mark (Pred M) k = Trm [pc0]"
    proof -
      have "flatBT (Mark (Pred M) k) = flatBT (Trm [pc0])" using pc0l by simp
      thus ?thesis by (rule m_7_flatBT_inj)
    qed
    have dsm': "scb_decomp (Trm [pc0]) (fst sm) (flatBT (Trm [pc])) (snd sm)"
      using dsm c0p c1p by simp
    obtain pm where pmf: "flatBP pm = fst sm @ flatBT (Trm [pc2]) @ snd sm"
        and pmd: "scb_decomp (Trm [pm]) (fst sm) (flatBT (Trm [pc2])) (snd sm)"
      using scb_replace_principal_BP[OF dsm' iptc2[unfolded c2p]] by blast
    have markk: "Mark M k = Trm [pm]"
    proof -
      have ev: "Mark M k = unflatBT (fst sm @ flatBT c2 @ snd sm)"
        using mark_surg[OF klt mbk] sm_def by simp
      have "flatBT (Trm [pm]) = fst sm @ flatBT c2 @ snd sm" using pmf c2p by simp
      thus ?thesis using ev unflatBT_flat[of "Trm [pm]"] by simp
    qed
    have flatk: "flatBT (Mark M k) = fst sm @ flatBT c2 @ snd sm"
      using markk pmf c2p by simp
    have brp: "\<forall>x \<in> set (snd sm). x = RP" using dsm by (simp add: scb_decomp_def)
    \<comment> \<open>\<open>Mark (Pred M) k\<close> is \<open>D\<^sub>\<omega>\<close>-free, so its sub-strings are; together with \<open>c\<^sub>2\<close>\<close>
    have c0df: "dfree_BT (Mark (Pred M) k)"
      using m_7_3_Mark_in_T_B[OF predRT mPk] by (simp add: T_B_def)
    have sm_sub: "set (fst sm) \<subseteq> set (flatBT (Mark (Pred M) k))"
        and bm_sub: "set (snd sm) \<subseteq> set (flatBT (Mark (Pred M) k))"
      using dsm by (auto simp: scb_decomp_def)
    have iptk: "isPTB_str (flatBT (Mark M k))"
    proof -
      have "dfree_BT (Trm [pm])"
      proof -
        have "\<And>v'. Dsym v' \<in> set (flatBT (Trm [pm])) \<Longrightarrow> v' \<noteq> \<infinity>"
        proof -
          fix v' assume "Dsym v' \<in> set (flatBT (Trm [pm]))"
          hence "Dsym v' \<in> set (flatBT (Mark (Pred M) k)) \<or> Dsym v' \<in> set (flatBT c2)"
            using pmf c2p sm_sub bm_sub by auto
          thus "v' \<noteq> \<infinity>" using c0df c2df dfree_flat_BT by blast
        qed
        thus ?thesis using dfree_flat_BT by blast
      qed
      thus ?thesis using markk by (auto simp: isPTB_str_def)
    qed
    have knz: "Mark M k \<noteq> Trm []" using markk by simp
    have sdk: "scb_decomp (Mark M k) (fst sm) (flatBT c2) (snd sm)"
      unfolding scb_decomp_def using flatk iptc2 brp by simp
    show "(Mark (Pred M) k, c1) \<in> MarkedB
      \<and> (\<exists>sm. scb_decomp (Mark (Pred M) k) (fst sm) (flatBT c1) (snd sm)
            \<and> Mark M k = unflatBT (fst sm @ flatBT c2 @ snd sm)
            \<and> flatBT (Mark M k) = fst sm @ flatBT c2 @ snd sm
            \<and> isPTB_str (flatBT (Mark M k))
            \<and> Mark M k \<noteq> Trm []
            \<and> scb_decomp (Mark M k) (fst sm) (flatBT c2) (snd sm))"
      using mbk dsm markk[symmetric] flatk iptk knz sdk mark_surg[OF klt mbk] sm_def
      by (intro conjI exI[of _ sm]) (simp_all)
  qed
  \<comment> \<open>the two cases on \<open>m'\<close>\<close>
  show ?thesis
  proof (cases "m' < ?j1")
    case m'lt: True
    have mlt: "m < ?j1" using mle m'lt by simp
    have mPm: "(Pred M, m) \<in> Marked" by (rule Marked_Pred[OF MT L mM mlt])
    have mPm': "(Pred M, m') \<in> Marked" by (rule Marked_Pred[OF MT L mM' m'lt])
    \<comment> \<open>surgery facts at \<open>m\<close> and \<open>m'\<close>\<close>
    from surg_facts[OF mM mlt] obtain sm where
        dsm: "scb_decomp (Mark (Pred M) m) (fst sm) (flatBT c1) (snd sm)"
      and flatm: "flatBT (Mark M m) = fst sm @ flatBT c2 @ snd sm"
      and iptm: "isPTB_str (flatBT (Mark M m))"
      and mnz: "Mark M m \<noteq> Trm []" by blast
    from surg_facts[OF mM' m'lt] obtain sm' where
        dsm': "scb_decomp (Mark (Pred M) m') (fst sm') (flatBT c1) (snd sm')"
      and flatm': "flatBT (Mark M m') = fst sm' @ flatBT c2 @ snd sm'"
      and iptm': "isPTB_str (flatBT (Mark M m'))" by blast
    \<comment> \<open>IH: \<open>Mark (Pred M) m'\<close> nests in \<open>Mark (Pred M) m\<close>\<close>
    have nestpred: "(Mark (Pred M) m, Mark (Pred M) m') \<in> MarkedB"
      by (rule IHpred[OF mPm mPm' mle])
    obtain sA bA where dA: "scb_decomp (Mark (Pred M) m) sA (flatBT (Mark (Pred M) m')) bA"
      using nestpred by (auto simp: MarkedB_def)
    \<comment> \<open>\<open>Mark (Pred M) m'\<close> is principal\<close>
    have mb0': "(?t1, Mark (Pred M) m') \<in> MarkedB"
      by (rule m_7_3_Trans_Mark_MarkedB[OF predRT mPm'])
    obtain s0' b0' where d0': "scb_decomp ?t1 s0' (flatBT (Mark (Pred M) m')) b0'"
      using mb0' by (auto simp: MarkedB_def)
    have iptc0': "isPTB_str (flatBT (Mark (Pred M) m'))"
      using d0' t1neT by (simp add: scb_decomp_def)
    then obtain pc0' where pc0l': "flatBT (Mark (Pred M) m') = flatBP pc0'"
      by (auto simp: isPTB_str_def)
    have c0p': "Mark (Pred M) m' = Trm [pc0']"
    proof -
      have "flatBT (Mark (Pred M) m') = flatBT (Trm [pc0'])" using pc0l' by simp
      thus ?thesis by (rule m_7_flatBT_inj)
    qed
    \<comment> \<open>compose: the \<open>flatBT c\<^sub>1\<close> occurrence inside \<open>Mark (Pred M) m\<close> via \<open>m'\<close> equals \<open>(sm, ...)\<close>\<close>
    have comp: "scb_decomp (Mark (Pred M) m) (sA @ fst sm') (flatBT c1) (snd sm' @ bA)"
      by (rule m_7_2_scb_compose[OF _ dA dsm'])
         (use c0p' in auto)
    have mPredne: "Mark (Pred M) m \<noteq> Trm []"
    proof
      assume z: "Mark (Pred M) m = Trm []"
      have "flatBT (Mark (Pred M) m) = fst sm @ flatBT c1 @ snd sm"
        using dsm by (simp add: scb_decomp_def)
      hence "Dsym wv \<in> set (flatBT (Mark (Pred M) m))"
        using c1p pcw by simp
      thus False using z by simp
    qed
    have coh: "fst sm = sA @ fst sm' \<and> snd sm = snd sm' @ bA"
      by (rule m_7_2_scb_unique_sb[OF dsm comp mPredne])
    \<comment> \<open>hence \<open>flatBT (Mark M m) = sA @ flatBT (Mark M m') @ bA\<close>\<close>
    have flatComp: "flatBT (Mark M m) = sA @ flatBT (Mark M m') @ bA"
      using flatm flatm' coh by simp
    have bArp: "\<forall>x \<in> set bA. x = RP" using dA by (simp add: scb_decomp_def)
    have "scb_decomp (Mark M m) sA (flatBT (Mark M m')) bA"
      unfolding scb_decomp_def using flatComp iptm' bArp by simp
    thus ?thesis unfolding MarkedB_def by auto
  next
    case m'lt_false: False
    have m'j1: "m' = ?j1" using m'lt_false m'le1 by simp
    have markm': "Mark M m' = Dpt (enat ?bv) 0\<^sub>B" using mark_last m'j1 by simp
    show ?thesis
    proof (cases "m < ?j1")
      case mlt: True
      from surg_facts[OF mM mlt] obtain sm where
          flatm: "flatBT (Mark M m) = fst sm @ flatBT c2 @ snd sm"
        and iptm: "isPTB_str (flatBT (Mark M m))"
        and mnz: "Mark M m \<noteq> Trm []"
        and sdk: "scb_decomp (Mark M m) (fst sm) (flatBT c2) (snd sm)" by blast
      \<comment> \<open>\<open>(Mark M m, c\<^sub>2) \<in> MarkedB\<close>, and \<open>(c\<^sub>2, D\<^bsub>?bv\<^esub> 0) \<in> MarkedB\<close>; compose\<close>
      obtain s2 b2 where d2: "scb_decomp c2 s2 (flatBT (Dpt (enat ?bv) 0\<^sub>B)) b2"
        using c2mb by (auto simp: MarkedB_def)
      have comp: "scb_decomp (Mark M m) (fst sm @ s2) (flatBT (Dpt (enat ?bv) 0\<^sub>B)) (b2 @ snd sm)"
        by (rule m_7_2_scb_compose[OF _ sdk d2]) (use c2p in auto)
      hence "(Mark M m, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB" unfolding MarkedB_def by auto
      thus ?thesis using markm' by simp
    next
      case mlt_false: False
      have mj1: "m = ?j1" using mlt_false mle1 by simp
      have "Mark M m = Dpt (enat ?bv) 0\<^sub>B" using mark_last mj1 by simp
      hence "Mark M m = Mark M m'" using markm' by simp
      moreover have "(Mark M m', Mark M m') \<in> MarkedB"
        using markm' selfMB_bv by simp
      ultimately show ?thesis by simp
    qed
  qed
qed

text \<open>Marked nesting: for a reduced \<open>M\<close> and two marked columns \<open>m \<le> m'\<close>, the
  marked image at the later column nests in the one at the earlier column,
  \<open>(Mark M m, Mark M m') \<in> MarkedB\<close>.  Empirically 0/770 failures.  This is the
  structural fact that makes the \<open>(c\<^sub>0,c\<^sub>1) \<notin> MarkedB\<close> default of the \<open>Mark\<close>
  surgery unreachable.\<close>

lemma Mark_MarkedB_nest:
  "(M, m) \<in> Marked \<longrightarrow> (M, m') \<in> Marked \<longrightarrow> m \<le> m' \<longrightarrow> M \<in> RT_PS
   \<longrightarrow> (Mark M m, Mark M m') \<in> MarkedB"
proof (induction M arbitrary: m m' rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (intro impI)
    assume mM: "(M, m) \<in> Marked" and mM': "(M, m') \<in> Marked"
      and mle: "m \<le> m'" and MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
    have leM': "leR M 0 m' (Lng M - 1)" using mM' by (simp add: Marked_def)
    have m'leN: "m' < Lng M" using leM' by (simp add: leR_def le0_def)
    have m'le: "m' \<le> Lng M - 1" using m'leN by linarith
    have mleN: "m < Lng M" using mle m'leN by linarith
    let ?j1 = "Lng M - 1"
    \<comment> \<open>reflexive \<open>MarkedB\<close> for a single principal value\<close>
    have selfMB: "\<And>c. isPTB_str (flatBT c) \<Longrightarrow> (c, c) \<in> MarkedB"
    proof -
      fix c assume "isPTB_str (flatBT c)"
      hence "scb_decomp c [] (flatBT c) []" by (rule scb_decomp_self)
      thus "(c, c) \<in> MarkedB" unfolding MarkedB_def by auto
    qed
    have selfMB0: "(0\<^sub>B, 0\<^sub>B) \<in> MarkedB"
    proof -
      have "scb_decomp 0\<^sub>B [] (flatBT (0\<^sub>B::BT)) []" by (simp add: scb_decomp_def)
      thus ?thesis unfolding MarkedB_def by auto
    qed
    show "(Mark M m, Mark M m') \<in> MarkedB"
    proof (cases "Lng M = 1")
      case True
      \<comment> \<open>(A) length 1: \<open>m = m' = 0\<close>, so reflexive\<close>
      have "m = m'" using mle m'le True by simp
      then obtain v where Mv: "M = [(v, v)]"
        using m_6_6_oneColumn[OF MT] MR True by auto
      have kv: "Mark M m = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Mv Mark_singleton by simp
      show ?thesis
      proof (cases "v = 0")
        case True
        have "Mark M m = 0\<^sub>B" using kv True by simp
        thus ?thesis using \<open>m = m'\<close> selfMB0 by simp
      next
        case False
        have mk: "Mark M m = Dpt (enat v) 0\<^sub>B" using kv False by simp
        have ipt: "isPTB_str (flatBT (Dpt (enat v) 0\<^sub>B))"
          by (rule isPTB_str_Dpt) simp_all
        show ?thesis using mk \<open>m = m'\<close> selfMB[OF ipt] by simp
      qed
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      have j1pos: "0 < ?j1" using L by simp
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
        have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
        have LPred: "Lng (Pred M) = Lng M - 1" using predb by simp
        have LPredlt: "Lng (Pred M) < Lng M" using LPred L by simp
        show ?thesis
        proof (cases "Trans (Pred M) = 0\<^sub>B")
          case t1z: True
          \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>: \<open>Lng M = 2\<close>, \<open>m,m' \<in> {0,1}\<close>\<close>
          have zP: "zeroT (Pred M)" using m_7_3_Trans_zeroT[OF predRT] t1z by simp
          have LP1: "Lng (Pred M) = 1" using zP by (simp add: zeroT_def)
          have L2: "Lng M = 2" using LP1 LPred L by linarith
          have kv: "\<And>k. Mark M k = (if k = 0 then Dpt 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)
                                      else Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
            using Mark.psimps[OF domK] MR Lgt1 mono t1z by (simp add: Let_def)
          let ?Dj = "Dpt (enat (entry M 1 ?j1)) 0\<^sub>B"
          have iptDj: "isPTB_str (flatBT ?Dj)" by (rule isPTB_str_Dpt) simp_all
          show ?thesis
          proof (cases "m' = 0")
            case True
            hence m0: "m = 0" using mle by simp
            have iptD0: "isPTB_str (flatBT (Dpt 0 (?Dj)))"
              by (rule isPTB_str_Dpt) (simp_all add: zero_enat_def)
            have "Mark M m = Dpt 0 (?Dj)" using kv m0 by simp
            moreover have "Mark M m' = Dpt 0 (?Dj)" using kv True by simp
            ultimately show ?thesis using selfMB[OF iptD0] by simp
          next
            case m'ne: False
            have mk': "Mark M m' = ?Dj" using kv m'ne by simp
            show ?thesis
            proof (cases "m = 0")
              case True
              have mk: "Mark M m = Dpt 0 (?Dj)" using kv True by simp
              \<comment> \<open>\<open>?Dj\<close> nests in \<open>Dpt 0 ?Dj\<close> (drop the head \<open>Dsym 0\<close>)\<close>
              have "scb_decomp (Dpt 0 ?Dj) [Dsym 0] (flatBT ?Dj) []"
                using iptDj by (simp add: scb_decomp_def)
              hence "(Dpt 0 ?Dj, ?Dj) \<in> MarkedB" unfolding MarkedB_def by auto
              thus ?thesis using mk mk' by simp
            next
              case False
              have mk: "Mark M m = ?Dj" using kv False by simp
              show ?thesis using mk mk' selfMB[OF iptDj] by simp
            qed
          qed
        next
          case t1ne: False
          \<comment> \<open>(B) \<open>t\<^sub>1 \<noteq> 0\<close> surgery; deferred to a dedicated argument\<close>
          have IHpred: "\<And>a b. (Pred M, a) \<in> Marked \<Longrightarrow> (Pred M, b) \<in> Marked
                 \<Longrightarrow> a \<le> b \<Longrightarrow> (Mark (Pred M) a, Mark (Pred M) b) \<in> MarkedB"
            using less.IH[OF LPredlt] predRT by blast
          show ?thesis
            by (rule Mark_MarkedB_nest_surgery[OF MR mono L t1ne mM mM' mle IHpred])
        qed
      next
        case nmono: False
        \<comment> \<open>(C) multiT branch: both reduce to the same last \<open>P\<close>-component \<open>PJ\<close>\<close>
        have nzM: "\<not> zeroT M" using notone by (auto simp: zeroT_def)
        have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
        have cut: "0 < Pcut M \<and> Pcut M \<le> ?j1" using Pcut_le[OF L] by simp
        let ?PJ = "drop (Pcut M) M"
        have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF MT muM])
        have Pne: "P M \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
        have PJRT: "?PJ \<in> RT_PS"
          using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
        have LPJ: "Lng ?PJ = Lng M - Pcut M" by simp
        have LPJlt: "Lng ?PJ < Lng M" using LPJ cut L by linarith
        have cmle: "Pcut M \<le> m" by (rule multi_Marked_last_component(1)[OF MT muM mM])
        have cmle': "Pcut M \<le> m'" by (rule multi_Marked_last_component(1)[OF MT muM mM'])
        have c1: "(M \<notin> RT_PS) = False" using MR by simp
        have c2: "(?j1 = 0) = False" using L by simp
        have c3: "monoT M = False" using nmono by simp
        have meq2: "\<And>k. k - (?j1 - Lng (drop (Pcut M) M) + 1) = k - Pcut M"
        proof -
          fix k
          have "?j1 - Lng ?PJ + 1 = Pcut M" using LPJ cut by linarith
          thus "k - (?j1 - Lng (drop (Pcut M) M) + 1) = k - Pcut M" by simp
        qed
        have markM: "\<And>k. Mark M k = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                                      else Mark ?PJ (k - Pcut M))"
        proof -
          fix k
          have raw: "Mark M k =
              (if P M ! (Lng (P M) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
               else Mark (P M ! (Lng (P M) - 1))
                      (k - (?j1 - Lng (P M ! (Lng (P M) - 1)) + 1)))"
            by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
          show "Mark M k = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B else Mark ?PJ (k - Pcut M))"
            unfolding raw PJeq meq2 ..
        qed
        show ?thesis
        proof (cases "?PJ = [(0, 0)]")
          case True
          have "Mark M m = Dpt 0 0\<^sub>B" and "Mark M m' = Dpt 0 0\<^sub>B"
            using markM True by simp_all
          moreover have "isPTB_str (flatBT (Dpt 0 0\<^sub>B))" by (rule isPTB_str_Dpt) simp_all
          ultimately show ?thesis using selfMB[of "Dpt 0 0\<^sub>B"] by simp
        next
          case False
          have kvm: "Mark M m = Mark ?PJ (m - Pcut M)" using markM False by simp
          have kvm': "Mark M m' = Mark ?PJ (m' - Pcut M)" using markM False by simp
          have mPJ: "(?PJ, m - Pcut M) \<in> Marked"
            by (rule multi_Marked_last_component(2)[OF MT muM mM])
          have mPJ': "(?PJ, m' - Pcut M) \<in> Marked"
            by (rule multi_Marked_last_component(2)[OF MT muM mM'])
          have mlePJ: "m - Pcut M \<le> m' - Pcut M" using mle by simp
          have "(Mark ?PJ (m - Pcut M), Mark ?PJ (m' - Pcut M)) \<in> MarkedB"
            using less.IH[OF LPJlt] mPJ mPJ' mlePJ PJRT by blast
          thus ?thesis using kvm kvm' by simp
        qed
      qed
    qed
  qed
qed

lemma Mark_leftend_form:
  "(N, m) \<in> Marked \<longrightarrow> N \<in> RT_PS
   \<longrightarrow> (Mark N m = 0\<^sub>B \<or> (\<exists>t. Mark N m = Dpt (enat (entry N 1 m)) t))"
proof (induction N arbitrary: m rule: measure_induct_rule[where f=Lng])
  case (less N)
  show ?case
  proof (intro impI)
    assume mM: "(N, m) \<in> Marked" and NR: "N \<in> RT_PS"
    have NT: "N \<in> T_PS" using NR by (simp add: RT_PS_def)
    have Nne: "N \<noteq> []" using NT by (simp add: T_PS_def)
    have domK: "\<And>m. Trans_Mark_dom (Inr (N, m))" by (rule m_7_3_Mark_welldef[OF NR])
    have leM: "leR N 0 m (Lng N - 1)" using mM by (simp add: Marked_def)
    have mleN: "m < Lng N" using leM by (simp add: leR_def le0_def)
    have mle: "m \<le> Lng N - 1" using mleN by linarith
    let ?j1 = "Lng N - 1"
    show "Mark N m = 0\<^sub>B \<or> (\<exists>t. Mark N m = Dpt (enat (entry N 1 m)) t)"
    proof (cases "Lng N = 1")
      case True
      \<comment> \<open>(A) length 1: \<open>N = [(v,v)]\<close>, \<open>m = 0\<close>\<close>
      obtain v where Nv: "N = [(v, v)]"
        using m_6_6_oneColumn[OF NT] NR True by auto
      have m0: "m = 0" using mle True by simp
      have kv: "Mark N m = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Nv Mark_singleton by simp
      have ev: "entry N 1 m = v" using Nv m0 by (simp add: entry_def)
      show ?thesis
      proof (cases "v = 0")
        case True thus ?thesis using kv by simp
      next
        case False
        have "Mark N m = Dpt (enat (entry N 1 m)) 0\<^sub>B" using kv False ev by simp
        thus ?thesis by blast
      qed
    next
      case notone: False
      have L: "1 < Lng N" using Nne notone by (cases N) auto
      have Lgt1: "\<not> Lng N \<le> Suc 0" using L by simp
      have j1pos: "0 < ?j1" using L by simp
      show ?thesis
      proof (cases "monoT N")
        case mono: True
        have predRT: "Pred N \<in> RT_PS" by (rule Pred_RT_PS[OF NR])
        have predb: "Pred N = butlast N" using L by (simp add: Pred_def)
        have LPred: "Lng (Pred N) = Lng N - 1" using predb by simp
        have LPredlt: "Lng (Pred N) < Lng N" using LPred L by simp
        \<comment> \<open>row-1 entries agree on the kept columns\<close>
        have entryP: "\<And>j. j \<le> Lng N - 2 \<Longrightarrow> entry (Pred N) 1 j = entry N 1 j"
        proof -
          fix j assume "j \<le> Lng N - 2"
          hence "j < Lng N - 1" using L by linarith
          hence "j < length (butlast N)" using L by simp
          thus "entry (Pred N) 1 j = entry N 1 j"
            using predb by (simp add: entry_def nth_butlast)
        qed
        show ?thesis
        proof (cases "Trans (Pred N) = 0\<^sub>B")
          case t1z: True
          \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>: here \<open>Pred N = [(0,0)]\<close>, \<open>Lng N = 2\<close>, \<open>m \<in> {0,1}\<close>\<close>
          have kv: "Mark N m = (if m = 0 then Dpt 0 (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)
                                else Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)"
            using Mark.psimps[OF domK] NR Lgt1 mono t1z by (simp add: Let_def)
          have predT: "Pred N \<in> T_PS" using predRT by (simp add: RT_PS_def)
          have zP: "zeroT (Pred N)" using m_7_3_Trans_zeroT[OF predRT] t1z by simp
          have LP1: "Lng (Pred N) = 1" using zP by (simp add: zeroT_def)
          have L2: "Lng N = 2" using LP1 LPred L by linarith
          obtain w where Pw: "Pred N = [(w, w)]"
            using m_6_6_oneColumn[OF predT] predRT LP1 by auto
          have w0: "w = 0" using zP Pw by (simp add: zeroT_def entry_def)
          have e0: "entry N 1 0 = 0"
          proof -
            have "entry (Pred N) 1 0 = entry N 1 0" using entryP[of 0] L2 by simp
            moreover have "entry (Pred N) 1 0 = 0" using Pw w0 by (simp add: entry_def)
            ultimately show ?thesis by simp
          qed
          show ?thesis
          proof (cases "m = 0")
            case True
            have "Mark N m = Dpt 0 (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)" using kv True by simp
            also have "\<dots> = Dpt (enat (entry N 1 m)) (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)"
              using True e0 by (simp add: zero_enat_def)
            finally show ?thesis by blast
          next
            case False
            have mj1: "m = ?j1" using False mle L2 by simp
            have "Mark N m = Dpt (enat (entry N 1 ?j1)) 0\<^sub>B" using kv False by simp
            hence "Mark N m = Dpt (enat (entry N 1 m)) 0\<^sub>B" using mj1 by simp
            thus ?thesis by blast
          qed
        next
          case t1ne: False
          \<comment> \<open>(B) \<open>t\<^sub>1 \<noteq> 0\<close>\<close>
          have hp: "hasParent N 0 ?j1" by (rule monoT_hasParent0_last[OF NT mono L])
          let ?bv = "entry N 1 (Lng N - 1)"
          define jp where "jp = parent N 0 (Lng N - 1)"
          define jm1 where "jm1 = Adm N jp"
          have transJ1eq: "transJ1 N = ?j1" by (simp add: transJ1_def)
          have transJ0eq: "transJ0 N = jp" by (simp add: transJ0_def transJ1_def jp_def)
          have transJm1eq: "transJm1 N = jm1"
            by (simp add: transJm1_def jm1_def transJ0eq)
          define c1 where "c1 = Mark (Pred N) (Adm N jp)"
          define vv where "vv = bpHeadV c1"
          define tt2 where "tt2 = bpHeadT c1"
          define JJ1 where "JJ1 = Lng (PB tt2) - 1"
          define pj where "pj = PB tt2 ! JJ1"
          define ldj where "ldj = (bpHeadV pj = enat (entry N 1 jp))"
          define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
          define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
          define c2 where "c2 = (if transCondI N \<or> transCondIII N \<or> transCondV N
                         then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                         else if transCondVI N
                         then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                         else if tt2 = 0\<^sub>B
                         then Dpt vv (Dpt (enat (entry N 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                         else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry N 1 jp))
                                            (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
          have c1eqT: "c1 = transC1 N"
            by (simp add: c1_def transC1_def transJm1eq jm1_def)
          have c2eqT: "c2 = transC2 N"
            unfolding c2_def transC2_def Let_def
              vv_def tt2_def c1eqT transV_def transT2_def
              JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
            by simp
          have c1eq: "c1 = Mark (Pred N) jm1"
            by (simp add: c1_def jm1_def)
          have mkjm1: "(Pred N, jm1) \<in> Marked"
            using Marked_Pred_Adm[OF NT L hp] jp_def jm1_def by simp
          have NP: "N \<in> PT_PS" using NT mono by (simp add: PT_PS_def)
          have J1pos: "transJ1 N > 0" using L by (simp add: transJ1_def)
          have T1ne: "transT1 N \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
          have pc1: "Lng (PB (transC1 N)) = 1"
            by (rule transC1_single_principal[OF NR NP J1pos T1ne])
          have c1ne: "transC1 N \<noteq> 0\<^sub>B"
          proof
            assume "transC1 N = 0\<^sub>B"
            thus False using pc1 by (simp add: PB_def)
          qed
          have c1TB: "transC1 N \<in> T_B"
            using m_7_3_Mark_in_T_B[OF predRT mkjm1] c1eq c1eqT by simp
          have c1Dpt: "transC1 N = Dpt (transV N) (transT2 N)"
            using principal_reconstruct[OF pc1]
            by (simp add: transV_def transT2_def)
          have t2TB: "transT2 N \<in> T_B"
            using c1TB unfolding c1Dpt by (auto simp: T_B_def)
          have c1Dsym: "flatBT c1 = Dsym (transV N) # flatBT (transT2 N)"
            using c1eqT c1Dpt by simp
          \<comment> \<open>\<open>bpHeadV c\<^sub>2 = transV N\<close>\<close>
          have bpc2: "bpHeadV c2 = transV N"
          proof -
            have "bpHeadV c2 = vv"
              by (simp add: c2_def)
            also have "vv = transV N"
              by (simp add: vv_def transV_def c1eqT)
            finally show ?thesis .
          qed
          have c2pc1: "Lng (PB c2) = 1"
            using transC2_single_principal c2eqT by simp
          have c2Dpt: "c2 = Dpt (transV N) (bpHeadT c2)"
            using principal_reconstruct[OF c2pc1] bpc2 by simp
          have c2Dsym: "flatBT c2 = Dsym (transV N) # flatBT (bpHeadT c2)"
            by (subst c2Dpt) (rule flatBT_principal_head)
          show ?thesis
          proof (cases "m < ?j1")
            case mlt_false: False
            \<comment> \<open>(B) \<open>m = j\<^sub>1\<close>: \<open>Mark N m = D\<^bsub>N\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0\<close>\<close>
            have mj1: "m = ?j1" using mlt_false mle by simp
            have kv: "Mark N m = Dpt (enat (entry N 1 ?j1)) 0\<^sub>B"
              using Mark.psimps[OF domK] NR Lgt1 mono t1ne mlt_false
              unfolding Let_def jp_def[symmetric]
              by simp
            hence "Mark N m = Dpt (enat (entry N 1 m)) 0\<^sub>B" using mj1 by simp
            thus ?thesis by blast
          next
            case mlt: True
            \<comment> \<open>(B) surgery branch, \<open>m < j\<^sub>1\<close>\<close>
            have mPred: "(Pred N, m) \<in> Marked"
              by (rule Marked_Pred[OF NT L mM mlt])
            have mle2: "m \<le> Lng N - 2" using mlt L by linarith
            have entryPm: "entry (Pred N) 1 m = entry N 1 m" by (rule entryP[OF mle2])
            define c0 where "c0 = Mark (Pred N) m"
            define sm1 where
              "sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))"
            have mark_val_raw: "Mark N m = (if (Mark (Pred N) m, c1) \<in> MarkedB
                  then unflatBT
                         (fst (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                          (flatBT c1) (snd sb))
                          @ flatBT c2
                          @ snd (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                            (flatBT c1) (snd sb)))
                  else Dpt (enat ?bv) 0\<^sub>B)"
              using Mark.psimps[OF domK] NR Lgt1 mono t1ne mlt
              unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                        tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                        ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                        c2_def[symmetric]
              by simp
            have mark_val: "Mark N m = (if (c0, c1) \<in> MarkedB
                  then unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
                  else Dpt (enat ?bv) 0\<^sub>B)"
              using mark_val_raw by (simp add: c0_def sm1_def)
            \<comment> \<open>\<open>c\<^sub>0 = Mark (Pred N) m\<close> is marked, so by IH it is \<open>0\<close> or principal\<close>
            have IH0: "c0 = 0\<^sub>B \<or> (\<exists>t. c0 = Dpt (enat (entry (Pred N) 1 m)) t)"
              using less.IH[OF LPredlt] mPred predRT c0_def by blast
            show ?thesis
            proof (cases "(c0, c1) \<in> MarkedB")
              case mbc_false: False
              \<comment> \<open>Unreachable for \<open>m < j\<^sub>1\<close>: \<open>c\<^sub>1 = Mark (Pred N) jm1\<close> with \<open>m \<le> jm1\<close>,
                 so by the marked nesting \<open>(Mark (Pred N) m, Mark (Pred N) jm1) \<in>
                 MarkedB\<close>, i.e. \<open>(c\<^sub>0, c\<^sub>1) \<in> MarkedB\<close>; contradiction.  Empirically the
                 \<open>(c\<^sub>0,c\<^sub>1) \<notin> MarkedB\<close> default never fires (0/510 marked cases).\<close>
              have admN: "adm N m" using mM by (simp add: Marked_def)
              have mjp: "m \<le> jp"
                using surg_parent_ge[OF mM mono L mlt] jp_def by simp
              have mjm1: "m \<le> jm1"
                using surg_adm_ge[OF admN mjp] jm1_def by simp
              have "(Mark (Pred N) m, Mark (Pred N) jm1) \<in> MarkedB"
                using Mark_MarkedB_nest mPred mkjm1 mjm1 predRT by blast
              hence "(c0, c1) \<in> MarkedB" using c0_def c1eq by simp
              thus ?thesis using mbc_false by simp
            next
              case mbc: True
              \<comment> \<open>the surgery proper: \<open>Mark N m\<close> is principal with head \<open>bpHeadV c\<^sub>0\<close>\<close>
              have c1form: "transC1 N = Trm [DB (transV N) (transT2 N)]"
                using c1Dpt by simp
              have c1p: "c1 = Trm [DB (transV N) (transT2 N)]"
                using c1form c1eqT by simp
              have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
                using mbc unfolding MarkedB_def by auto
              have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
                unfolding sm1_def by (rule someI_ex[OF exsm])
              have c1Dsym2: "flatBT c1 = Dsym (transV N) # flatBT (transT2 N)"
                using c1eqT c1Dpt by simp
              have c0ne: "c0 \<noteq> 0\<^sub>B"
              proof
                assume z: "c0 = 0\<^sub>B"
                have "flatBT c0 = fst sm1 @ flatBT c1 @ snd sm1"
                  using dsm by (simp add: scb_decomp_def)
                hence "Dsym (transV N) \<in> set (flatBT c0)"
                  using c1Dsym2 by simp
                thus False using z by simp
              qed
              \<comment> \<open>by IH, \<open>c\<^sub>0 = Dpt (enat (entry (Pred N) 1 m)) tc0 = Dpt (enat (entry N 1 m)) tc0\<close>\<close>
              obtain tc0 where c0d: "c0 = Dpt (enat (entry (Pred N) 1 m)) tc0"
                using IH0 c0ne by blast
              have c0dN: "c0 = Dpt (enat (entry N 1 m)) tc0"
                using c0d entryPm by simp
              have c0Dsym: "flatBT c0 = Dsym (enat (entry N 1 m)) # flatBT tc0"
                using c0dN by simp
              \<comment> \<open>\<open>Mark N m\<close> is a single principal term (the surgery preserves principality)\<close>
              have c2df: "dfree_BT c2"
              proof -
                have vne: "transV N \<noteq> \<infinity>" using c1TB c1Dpt by (auto simp: T_B_def)
                have t2df: "dfree_BT (transT2 N)"
                  using c1TB c1Dpt by (auto simp: T_B_def)
                show ?thesis using dfree_transC2[OF vne t2df] c2eqT by simp
              qed
              obtain pc2 where c2p: "c2 = Trm [pc2]"
                using principal_reconstruct[OF c2pc1] by (metis BT.exhaust untrm.simps)
              have iptc2: "isPTB_str (flatBT (Trm [pc2]))"
              proof -
                have "dfree_BT (Trm [pc2])" using c2df c2p by simp
                then obtain p where "pc2 = p" and "dfree_BP p" by auto
                thus ?thesis by (auto simp: isPTB_str_def)
              qed
              obtain pc0 where c0p2: "c0 = Trm [pc0]" using c0dN by simp
              have dsm': "scb_decomp (Trm [pc0]) (fst sm1)
                            (flatBT (Trm [DB (transV N) (transT2 N)])) (snd sm1)"
                using dsm c0p2 c1p by simp
              obtain pm where pmf: "flatBP pm = fst sm1 @ flatBT (Trm [pc2]) @ snd sm1"
                  and pmd: "scb_decomp (Trm [pm]) (fst sm1) (flatBT (Trm [pc2])) (snd sm1)"
                using scb_replace_principal_BP[OF dsm' iptc2] by blast
              have markM: "Mark N m = Trm [pm]"
              proof -
                have "flatBT (Trm [pm]) = fst sm1 @ flatBT c2 @ snd sm1"
                  using pmf c2p by simp
                thus ?thesis
                  using mark_val mbc unflatBT_flat[of "Trm [pm]"] by simp
              qed
              \<comment> \<open>the leading flat symbol of \<open>Mark N m\<close> equals that of \<open>c\<^sub>0\<close>\<close>
              have flatMark: "flatBT (Mark N m) = fst sm1 @ flatBT c2 @ snd sm1"
                using markM pmf c2p by simp
              have flatc0: "flatBT c0 = fst sm1 @ flatBT c1 @ snd sm1"
                using dsm by (simp add: scb_decomp_def)
              \<comment> \<open>both \<open>flatBT c\<^sub>1\<close> and \<open>flatBT c\<^sub>2\<close> start with \<open>Dsym (transV N)\<close>, hence
                 \<open>flatBT (Mark N m)\<close> and \<open>flatBT c\<^sub>0\<close> agree on their head\<close>
              have headEq: "hd (flatBT (Mark N m)) = hd (flatBT c0)"
              proof (cases "fst sm1 = []")
                case True
                have "hd (flatBT (Mark N m)) = Dsym (transV N)"
                  using flatMark True c2Dsym by simp
                moreover have "hd (flatBT c0) = Dsym (transV N)"
                  using flatc0 True c1Dsym2 by simp
                ultimately show ?thesis by simp
              next
                case False
                have "hd (flatBT (Mark N m)) = hd (fst sm1)"
                  using flatMark False by simp
                moreover have "hd (flatBT c0) = hd (fst sm1)"
                  using flatc0 False by simp
                ultimately show ?thesis by simp
              qed
              \<comment> \<open>read off \<open>bpHeadV\<close> from the heads\<close>
              have headM: "hd (flatBT (Mark N m)) = Dsym (entry N 1 m)"
              proof -
                have "hd (flatBT c0) = Dsym (enat (entry N 1 m))"
                  using c0Dsym by simp
                thus ?thesis using headEq by simp
              qed
              obtain pm0 where pmDB: "pm = DB (bpHeadV (Trm [pm])) (bpHeadT (Trm [pm]))"
                by (cases pm) auto
              have markDpt: "Mark N m = Dpt (bpHeadV (Mark N m)) (bpHeadT (Mark N m))"
                using markM pmDB by (cases pm) simp
              have flatMarkDsym: "flatBT (Mark N m) = Dsym (bpHeadV (Mark N m)) # flatBT (bpHeadT (Mark N m))"
                by (subst markDpt) (rule flatBT_principal_head)
              have "Dsym (bpHeadV (Mark N m)) = Dsym (enat (entry N 1 m))"
                using flatMarkDsym headM by simp
              hence vEq: "bpHeadV (Mark N m) = enat (entry N 1 m)" by simp
              have "Mark N m = Dpt (enat (entry N 1 m)) (bpHeadT (Mark N m))"
                using markDpt vEq by simp
              thus ?thesis by blast
            qed
          qed
        qed
      next
        case nmono: False
        \<comment> \<open>(C) multiT branch\<close>
        have nzN: "\<not> zeroT N" using notone by (auto simp: zeroT_def)
        have muN: "multiT N" using nzN nmono by (simp add: multiT_def)
        have cut: "0 < Pcut N \<and> Pcut N \<le> ?j1" using Pcut_le[OF L] by simp
        let ?PJ = "drop (Pcut N) N"
        have PJeq: "P N ! (Lng (P N) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF NT muN])
        have Pne: "P N \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P N) - 1 < Lng (P N)" using Pne by (cases "P N") auto
        have PJRT: "?PJ \<in> RT_PS"
          using m_6_6_P_reduced[OF NT] NR J1lt PJeq by auto
        have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
        have LPJ: "Lng ?PJ = Lng N - Pcut N" by simp
        have LPJlt: "Lng ?PJ < Lng N" using LPJ cut L by linarith
        have cmle: "Pcut N \<le> m" by (rule multi_Marked_last_component(1)[OF NT muN mM])
        have c1: "(N \<notin> RT_PS) = False" using NR by simp
        have c2: "(?j1 = 0) = False" using L by simp
        have c3: "monoT N = False" using nmono by simp
        have meq2: "m - (?j1 - Lng (drop (Pcut N) N) + 1) = m - Pcut N"
        proof -
          have "?j1 - Lng ?PJ + 1 = Pcut N"
            using LPJ cut by linarith
          thus ?thesis by simp
        qed
        have markM: "Mark N m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                                 else Mark ?PJ (m - Pcut N))"
        proof -
          have raw: "Mark N m =
              (if P N ! (Lng (P N) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
               else Mark (P N ! (Lng (P N) - 1))
                      (m - (?j1 - Lng (P N ! (Lng (P N) - 1)) + 1)))"
            by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
          show ?thesis unfolding raw PJeq meq2 ..
        qed
        have entryPJ: "\<And>k. k < Lng ?PJ \<Longrightarrow> entry ?PJ 1 k = entry N 1 (Pcut N + k)"
          by (simp add: entry_def)
        have eShift: "entry ?PJ 1 (m - Pcut N) = entry N 1 m"
        proof -
          have mlt: "m - Pcut N < Lng ?PJ" using mle LPJ cut by linarith
          have "entry ?PJ 1 (m - Pcut N) = entry N 1 (Pcut N + (m - Pcut N))"
            by (rule entryPJ[OF mlt])
          also have "Pcut N + (m - Pcut N) = m" using cmle by simp
          finally show ?thesis .
        qed
        show ?thesis
        proof (cases "?PJ = [(0, 0)]")
          case True
          \<comment> \<open>last column is \<open>(0,0)\<close>, so \<open>entry N 1 m = 0\<close>\<close>
          have m_last: "m = ?j1" using multi_Marked_last_component(1)[OF NT muN mM]
            cmle mle LPJ True cut by simp
          have eN0: "entry N 1 m = 0"
          proof -
            have "entry ?PJ 1 (m - Pcut N) = 0"
            proof -
              have "m - Pcut N = 0 \<or> m - Pcut N \<ge> 1" by linarith
              moreover have "Lng ?PJ = 1" using True by simp
              ultimately have "m - Pcut N = 0" using mle LPJ cut cmle by linarith
              thus ?thesis using True by (simp add: entry_def)
            qed
            thus ?thesis using eShift by simp
          qed
          have "Mark N m = Dpt 0 0\<^sub>B" using markM True by simp
          hence "Mark N m = Dpt (enat (entry N 1 m)) 0\<^sub>B" using eN0 by (simp add: zero_enat_def)
          thus ?thesis by blast
        next
          case False
          have kv: "Mark N m = Mark ?PJ (m - Pcut N)" using markM False by simp
          have mPJ: "(?PJ, m - Pcut N) \<in> Marked"
            by (rule multi_Marked_last_component(2)[OF NT muN mM])
          have IHJ: "Mark ?PJ (m - Pcut N) = 0\<^sub>B
                     \<or> (\<exists>t. Mark ?PJ (m - Pcut N) = Dpt (enat (entry ?PJ 1 (m - Pcut N))) t)"
            using less.IH[OF LPJlt] mPJ PJRT by blast
          show ?thesis
          proof (cases "Mark ?PJ (m - Pcut N) = 0\<^sub>B")
            case True
            thus ?thesis using kv by simp
          next
            case Pne2: False
            obtain t where "Mark ?PJ (m - Pcut N) = Dpt (enat (entry ?PJ 1 (m - Pcut N))) t"
              using IHJ Pne2 by blast
            hence "Mark N m = Dpt (enat (entry N 1 m)) t" using kv eShift by simp
            thus ?thesis by blast
          qed
        qed
      qed
    qed
  qed
qed


text \<open>Helper for §7.3 命題（右端第1基点の Mark の基本性質）: every branch of
  @{thm [source] transC2_def} is \<open>D\<^bsub>v\<^esub> X\<close> with \<open>X \<noteq> 0\<^bsub>B\<^esub>\<close>, so the tail
  \<open>bpHeadT (transC2 M)\<close> is non-zero.\<close>

lemma transC2_inner_nonzero: "bpHeadT (transC2 M) \<noteq> 0\<^sub>B"
proof -
  let ?j1 = "transJ1 M"
  let ?jp = "transJ0 M"
  let ?v  = "transV M"
  let ?t2 = "transT2 M"
  let ?J1 = "Lng (PB ?t2) - 1"
  let ?pj = "PB ?t2 ! ?J1"
  let ?ldj = "(bpHeadV ?pj = enat (entry M 1 ?jp))"
  let ?t3 = "(if ?ldj then SigmaB (take ?J1 (PB ?t2)) else ?t2)"
  let ?t4 = "(if ?ldj then bpHeadT ?pj else ?t2)"
  show ?thesis
  proof (cases "transCondI M \<or> transCondIII M \<or> transCondV M")
    case True
    have "transC2 M = Dpt ?v (?t2 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
      using True by (simp add: transC2_def Let_def)
    hence "bpHeadT (transC2 M) = ?t2 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B" by simp
    moreover have "?t2 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B \<noteq> 0\<^sub>B"
      by (cases ?t2) simp
    ultimately show ?thesis by simp
  next
    case notA: False
    show ?thesis
    proof (cases "transCondVI M")
      case True
      have "transC2 M = Dpt ?v (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
        using notA True by (simp add: transC2_def Let_def)
      thus ?thesis by simp
    next
      case notVI: False
      show ?thesis
      proof (cases "?t2 = 0\<^sub>B")
        case True
        have "transC2 M = Dpt ?v (Dpt (enat (entry M 1 ?jp))
                                       (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B))"
          using notA notVI True by (simp add: transC2_def Let_def)
        thus ?thesis by simp
      next
        case t2nz: False
        have "transC2 M = Dpt ?v (?t3 +\<^sub>B Dpt (enat (entry M 1 ?jp))
                                          (?t4 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B))"
          using notA notVI t2nz by (simp add: transC2_def Let_def)
        hence "bpHeadT (transC2 M)
                 = ?t3 +\<^sub>B Dpt (enat (entry M 1 ?jp))
                              (?t4 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)" by simp
        moreover have "?t3 +\<^sub>B Dpt (enat (entry M 1 ?jp))
                              (?t4 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B) \<noteq> 0\<^sub>B"
          by (cases ?t3) simp
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>\<open>flatBT\<close> never produces the empty string.\<close>

lemma flatBT_nonempty: "flatBT t \<noteq> []"
proof -
  obtain ps where tps: "t = Trm ps" by (cases t)
  show ?thesis
  proof (cases ps)
    case Nil thus ?thesis using tps by simp
  next
    case (Cons p qs)
    show ?thesis
    proof (cases qs)
      case Nil
      obtain u a where "p = DB u a" by (cases p)
      thus ?thesis using tps Cons Nil by simp
    next
      case (Cons q rs)
      thus ?thesis using tps \<open>ps = p # qs\<close> by simp
    qed
  qed
qed

text \<open>A non-zero \<open>BT\<close> flattens to a string of length at least \<open>2\<close>
  (\<open>0\<^bsub>B\<^esub>\<close> alone flattens to the single letter \<open>"0"\<close>).\<close>

lemma flatBT_len_ge2:
  assumes "t \<noteq> 0\<^sub>B" shows "2 \<le> length (flatBT t)"
proof -
  obtain ps where tps: "t = Trm ps" by (cases t)
  have psne: "ps \<noteq> []" using assms tps by auto
  show ?thesis
  proof (cases ps)
    case Nil thus ?thesis using psne by simp
  next
    case (Cons p qs)
    show ?thesis
    proof (cases qs)
      case Nil
      obtain u a where pua: "p = DB u a" by (cases p)
      have "flatBT a \<noteq> []" by (rule flatBT_nonempty)
      hence "1 \<le> length (flatBT a)" by (cases "flatBT a") auto
      thus ?thesis using tps Cons Nil pua by simp
    next
      case (Cons q rs)
      thus ?thesis using tps \<open>ps = p # qs\<close> by simp
    qed
  qed
qed

text \<open>命題（右端第1基点の Mark の基本性質） helper (content.md 2294): for
  \<open>m < j\<^sub>1\<close> the tail of \<open>Mark M m\<close> is non-empty, i.e. \<open>Mark M m \<noteq> D\<^bsub>M\<^bsub>1,m\<^esub>\<^esub> 0\<^bsub>B\<^esub>\<close>.
  Strong \<open>Lng\<close>-induction mirroring @{thm [source] Mark_leftend_form}; the mono
  surgery sub-case is closed by a flat-length count
  (\<open>flatBT (transC2 M)\<close> contributes \<open>\<ge> 3\<close> letters, while \<open>D\<^bsub>v\<^esub> 0\<^bsub>B\<^esub>\<close> flattens
  to exactly \<open>2\<close>).\<close>

lemma Mark_tail_nonzero:
  "(M, m) \<in> Marked \<longrightarrow> M \<in> RT_PS \<longrightarrow> m < Lng M - 1
   \<longrightarrow> Mark M m \<noteq> Dpt (enat (entry M 1 m)) 0\<^sub>B"
proof (induction M arbitrary: m rule: measure_induct_rule[where f=Lng])
  case (less N)
  show ?case
  proof (intro impI)
    assume mM: "(N, m) \<in> Marked" and NR: "N \<in> RT_PS" and msmall: "m < Lng N - 1"
    have NT: "N \<in> T_PS" using NR by (simp add: RT_PS_def)
    have Nne: "N \<noteq> []" using NT by (simp add: T_PS_def)
    have domK: "\<And>m. Trans_Mark_dom (Inr (N, m))" by (rule m_7_3_Mark_welldef[OF NR])
    have leM: "leR N 0 m (Lng N - 1)" using mM by (simp add: Marked_def)
    have mleN: "m < Lng N" using leM by (simp add: leR_def le0_def)
    have mle: "m \<le> Lng N - 1" using mleN by linarith
    let ?j1 = "Lng N - 1"
    have L: "1 < Lng N" using msmall by linarith
    have Lgt1: "\<not> Lng N \<le> Suc 0" using L by simp
    have j1pos: "0 < ?j1" using L by simp
    have mlt: "m < ?j1" using msmall by simp
    show "Mark N m \<noteq> Dpt (enat (entry N 1 m)) 0\<^sub>B"
    proof (cases "monoT N")
      case mono: True
      have predRT: "Pred N \<in> RT_PS" by (rule Pred_RT_PS[OF NR])
      show ?thesis
      proof (cases "Trans (Pred N) = 0\<^sub>B")
        case t1z: True
        \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>, \<open>Lng N = 2\<close>, \<open>m < j\<^sub>1 = 1 \<Longrightarrow> m = 0\<close>;
            \<open>Mark N 0 = D\<^sub>0 (D\<^bsub>N\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0)\<close> has a non-trivial tail.\<close>
        have kv: "Mark N m = (if m = 0 then Dpt 0 (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)
                              else Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)"
          using Mark.psimps[OF domK] NR Lgt1 mono t1z by (simp add: Let_def)
        have predRTt: "Pred N \<in> RT_PS" by (rule Pred_RT_PS[OF NR])
        have zP: "zeroT (Pred N)" using m_7_3_Trans_zeroT[OF predRTt] t1z by simp
        have predb: "Pred N = butlast N" using L by (simp add: Pred_def)
        have LPred: "Lng (Pred N) = Lng N - 1" using predb by simp
        have LP1: "Lng (Pred N) = 1" using zP by (simp add: zeroT_def)
        have L2: "Lng N = 2" using LP1 LPred L by linarith
        have m0: "m = 0" using mlt L2 by simp
        have "Mark N m = Dpt 0 (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)" using kv m0 by simp
        thus ?thesis by simp
      next
        case t1ne: False
        have hp: "hasParent N 0 ?j1" by (rule monoT_hasParent0_last[OF NT mono L])
        let ?bv = "entry N 1 (Lng N - 1)"
        define jp where "jp = parent N 0 (Lng N - 1)"
        define jm1 where "jm1 = Adm N jp"
        define c1 where "c1 = Mark (Pred N) (Adm N jp)"
        define vv where "vv = bpHeadV c1"
        define tt2 where "tt2 = bpHeadT c1"
        define JJ1 where "JJ1 = Lng (PB tt2) - 1"
        define pj where "pj = PB tt2 ! JJ1"
        define ldj where "ldj = (bpHeadV pj = enat (entry N 1 jp))"
        define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
        define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
        define c2 where "c2 = (if transCondI N \<or> transCondIII N \<or> transCondV N
                       then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                       else if transCondVI N
                       then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                       else if tt2 = 0\<^sub>B
                       then Dpt vv (Dpt (enat (entry N 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                       else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry N 1 jp))
                                          (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
        have transJ1eq: "transJ1 N = ?j1" by (simp add: transJ1_def)
        have transJ0eq: "transJ0 N = jp" by (simp add: transJ0_def transJ1_def jp_def)
        have transJm1eq: "transJm1 N = jm1"
          by (simp add: transJm1_def jm1_def transJ0eq)
        have c1eqT: "c1 = transC1 N"
          by (simp add: c1_def transC1_def transJm1eq jm1_def)
        have c2eqT: "c2 = transC2 N"
          unfolding c2_def transC2_def Let_def
            vv_def tt2_def c1eqT transV_def transT2_def
            JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
          by simp
        have c1eq: "c1 = Mark (Pred N) jm1"
          by (simp add: c1_def jm1_def)
        have mkjm1: "(Pred N, jm1) \<in> Marked"
          using Marked_Pred_Adm[OF NT L hp] jp_def jm1_def by simp
        \<comment> \<open>\<open>bpHeadT c\<^sub>2 = bpHeadT (transC2 N) \<noteq> 0\<close>, so \<open>flatBT c\<^sub>2\<close> is long\<close>
        have c2pc1: "Lng (PB c2) = 1"
          using transC2_single_principal c2eqT by simp
        have c2Dpt: "c2 = Dpt (bpHeadV c2) (bpHeadT c2)"
          using principal_reconstruct[OF c2pc1] by simp
        have c2tail_ne: "bpHeadT c2 \<noteq> 0\<^sub>B"
          using transC2_inner_nonzero[of N] c2eqT by simp
        have c2Dsym: "flatBT c2 = Dsym (bpHeadV c2) # flatBT (bpHeadT c2)"
          by (subst c2Dpt) (rule flatBT_principal_head)
        have lenc2: "3 \<le> length (flatBT c2)"
        proof -
          have "2 \<le> length (flatBT (bpHeadT c2))"
            by (rule flatBT_len_ge2[OF c2tail_ne])
          thus ?thesis using c2Dsym by simp
        qed
        \<comment> \<open>the surgery, \<open>m < j\<^sub>1\<close>\<close>
        have mPred: "(Pred N, m) \<in> Marked"
          by (rule Marked_Pred[OF NT L mM mlt])
        define c0 where "c0 = Mark (Pred N) m"
        define sm1 where
          "sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))"
        have mark_val_raw: "Mark N m = (if (Mark (Pred N) m, c1) \<in> MarkedB
              then unflatBT
                     (fst (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                      (flatBT c1) (snd sb))
                      @ flatBT c2
                      @ snd (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                        (flatBT c1) (snd sb)))
              else Dpt (enat ?bv) 0\<^sub>B)"
          using Mark.psimps[OF domK] NR Lgt1 mono t1ne mlt
          unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                    tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                    ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                    c2_def[symmetric]
          by simp
        have mark_val: "Mark N m = (if (c0, c1) \<in> MarkedB
              then unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
              else Dpt (enat ?bv) 0\<^sub>B)"
          using mark_val_raw by (simp add: c0_def sm1_def)
        show ?thesis
        proof (cases "(c0, c1) \<in> MarkedB")
          case mbc_false: False
          \<comment> \<open>unreachable for \<open>m < j\<^sub>1\<close> (as in @{thm [source] Mark_leftend_form})\<close>
          have admN: "adm N m" using mM by (simp add: Marked_def)
          have mjp: "m \<le> jp"
            using surg_parent_ge[OF mM mono L mlt] jp_def by simp
          have mjm1: "m \<le> jm1"
            using surg_adm_ge[OF admN mjp] jm1_def by simp
          have "(Mark (Pred N) m, Mark (Pred N) jm1) \<in> MarkedB"
            using Mark_MarkedB_nest mPred mkjm1 mjm1 predRT by blast
          hence "(c0, c1) \<in> MarkedB" using c0_def c1eq by simp
          thus ?thesis using mbc_false by simp
        next
          case mbc: True
          \<comment> \<open>the surgery proper: \<open>Mark N m\<close> is one principal term whose flat
             string contains \<open>flatBT c\<^sub>2\<close> as an infix, hence has length \<open>\<ge> 3\<close>\<close>
          have c1form: "transC1 N = Dpt (transV N) (transT2 N)"
          proof -
            have pc1: "Lng (PB (transC1 N)) = 1"
            proof -
              have NP: "N \<in> PT_PS" using NT mono by (simp add: PT_PS_def)
              have J1pos: "transJ1 N > 0" using L by (simp add: transJ1_def)
              have T1ne: "transT1 N \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
              show ?thesis by (rule transC1_single_principal[OF NR NP J1pos T1ne])
            qed
            show ?thesis using principal_reconstruct[OF pc1]
              by (simp add: transV_def transT2_def)
          qed
          have c1p: "c1 = Trm [DB (transV N) (transT2 N)]"
            using c1form c1eqT by simp
          obtain pc2 where c2p: "c2 = Trm [pc2]"
            using principal_reconstruct[OF c2pc1] by (metis BT.exhaust untrm.simps)
          have c2df: "dfree_BT c2"
          proof -
            have NP: "N \<in> PT_PS" using NT mono by (simp add: PT_PS_def)
            have J1pos: "transJ1 N > 0" using L by (simp add: transJ1_def)
            have T1ne: "transT1 N \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
            have c1TB: "transC1 N \<in> T_B"
              using m_7_3_Mark_in_T_B[OF predRT mkjm1] c1eq c1eqT by simp
            have vne: "transV N \<noteq> \<infinity>" using c1TB c1form by (auto simp: T_B_def)
            have t2df: "dfree_BT (transT2 N)"
              using c1TB c1form by (auto simp: T_B_def)
            show ?thesis using dfree_transC2[OF vne t2df] c2eqT by simp
          qed
          have iptc2: "isPTB_str (flatBT (Trm [pc2]))"
          proof -
            have "dfree_BT (Trm [pc2])" using c2df c2p by simp
            then obtain p where "pc2 = p" and "dfree_BP p" by auto
            thus ?thesis by (auto simp: isPTB_str_def)
          qed
          have IH0: "c0 = 0\<^sub>B \<or> (\<exists>t. c0 = Dpt (enat (entry (Pred N) 1 m)) t)"
            using Mark_leftend_form mPred predRT c0_def by blast
          have c0ne: "c0 \<noteq> 0\<^sub>B"
          proof -
            have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
              using mbc unfolding MarkedB_def by auto
            have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
              unfolding sm1_def by (rule someI_ex[OF exsm])
            have c1Dsym2: "flatBT c1 = Dsym (transV N) # flatBT (transT2 N)"
              using c1eqT c1form by simp
            show ?thesis
            proof
              assume z: "c0 = 0\<^sub>B"
              have "flatBT c0 = fst sm1 @ flatBT c1 @ snd sm1"
                using dsm by (simp add: scb_decomp_def)
              hence "Dsym (transV N) \<in> set (flatBT c0)"
                using c1Dsym2 by simp
              thus False using z by simp
            qed
          qed
          obtain pc0 where c0p2: "c0 = Trm [pc0]" using IH0 c0ne by auto
          have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
            using mbc unfolding MarkedB_def by auto
          have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
            unfolding sm1_def by (rule someI_ex[OF exsm])
          have dsm': "scb_decomp (Trm [pc0]) (fst sm1)
                        (flatBT (Trm [DB (transV N) (transT2 N)])) (snd sm1)"
            using dsm c0p2 c1p by simp
          obtain pm where pmf: "flatBP pm = fst sm1 @ flatBT (Trm [pc2]) @ snd sm1"
              and pmd: "scb_decomp (Trm [pm]) (fst sm1) (flatBT (Trm [pc2])) (snd sm1)"
            using scb_replace_principal_BP[OF dsm' iptc2] by blast
          have markM: "Mark N m = Trm [pm]"
          proof -
            have "flatBT (Trm [pm]) = fst sm1 @ flatBT c2 @ snd sm1"
              using pmf c2p by simp
            thus ?thesis
              using mark_val mbc unflatBT_flat[of "Trm [pm]"] by simp
          qed
          \<comment> \<open>flat length: \<open>flatBT c\<^sub>2\<close> (length \<open>\<ge> 3\<close>) is an infix\<close>
          have flatMark: "flatBT (Mark N m) = fst sm1 @ flatBT c2 @ snd sm1"
            using markM pmf c2p by simp
          have lenMark: "3 \<le> length (flatBT (Mark N m))"
            using flatMark lenc2 by simp
          show ?thesis
          proof
            assume eq: "Mark N m = Dpt (enat (entry N 1 m)) 0\<^sub>B"
            have "flatBT (Mark N m) = [Dsym (enat (entry N 1 m)), Zsym]"
              by (simp add: eq)
            thus False using lenMark by simp
          qed
        qed
      qed
    next
      case nmono: False
      \<comment> \<open>(C) multiT branch: recurse into the last component \<open>?PJ\<close>\<close>
      have nzN: "\<not> zeroT N" using L by (auto simp: zeroT_def)
      have muN: "multiT N" using nzN nmono by (simp add: multiT_def)
      have cut: "0 < Pcut N \<and> Pcut N \<le> ?j1" using Pcut_le[OF L] by simp
      let ?PJ = "drop (Pcut N) N"
      have PJeq: "P N ! (Lng (P N) - 1) = ?PJ"
        by (rule trans_multiT_last_component(1)[OF NT muN])
      have Pne: "P N \<noteq> []" by (rule P_nonempty)
      have J1lt: "Lng (P N) - 1 < Lng (P N)" using Pne by (cases "P N") auto
      have PJRT: "?PJ \<in> RT_PS"
        using m_6_6_P_reduced[OF NT] NR J1lt PJeq by auto
      have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
      have LPJ: "Lng ?PJ = Lng N - Pcut N" by simp
      have LPJlt: "Lng ?PJ < Lng N" using LPJ cut L by linarith
      have cmle: "Pcut N \<le> m" by (rule multi_Marked_last_component(1)[OF NT muN mM])
      have c1: "(N \<notin> RT_PS) = False" using NR by simp
      have c2: "(?j1 = 0) = False" using L by simp
      have c3: "monoT N = False" using nmono by simp
      have meq2: "m - (?j1 - Lng (drop (Pcut N) N) + 1) = m - Pcut N"
      proof -
        have "?j1 - Lng ?PJ + 1 = Pcut N" using LPJ cut by linarith
        thus ?thesis by simp
      qed
      have markM: "Mark N m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                               else Mark ?PJ (m - Pcut N))"
      proof -
        have raw: "Mark N m =
            (if P N ! (Lng (P N) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
             else Mark (P N ! (Lng (P N) - 1))
                    (m - (?j1 - Lng (P N ! (Lng (P N) - 1)) + 1)))"
          by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
        show ?thesis unfolding raw PJeq meq2 ..
      qed
      have entryPJ: "\<And>k. k < Lng ?PJ \<Longrightarrow> entry ?PJ 1 k = entry N 1 (Pcut N + k)"
        by (simp add: entry_def)
      have eShift: "entry ?PJ 1 (m - Pcut N) = entry N 1 m"
      proof -
        have mltJ: "m - Pcut N < Lng ?PJ" using mle LPJ cut by linarith
        have "entry ?PJ 1 (m - Pcut N) = entry N 1 (Pcut N + (m - Pcut N))"
          by (rule entryPJ[OF mltJ])
        also have "Pcut N + (m - Pcut N) = m" using cmle by simp
        finally show ?thesis .
      qed
      show ?thesis
      proof (cases "?PJ = [(0, 0)]")
        case True
        \<comment> \<open>then \<open>m\<close> is forced to be the last index \<open>j\<^sub>1\<close>, contradicting \<open>m < j\<^sub>1\<close>\<close>
        have m_last: "m = ?j1" using multi_Marked_last_component(1)[OF NT muN mM]
          cmle mle LPJ True cut by simp
        thus ?thesis using mlt by simp
      next
        case PJne: False
        have kv: "Mark N m = Mark ?PJ (m - Pcut N)" using markM PJne by simp
        have mPJ: "(?PJ, m - Pcut N) \<in> Marked"
          by (rule multi_Marked_last_component(2)[OF NT muN mM])
        have mltJ: "m - Pcut N < Lng ?PJ - 1"
        proof -
          have "m - Pcut N < ?j1 - Pcut N" using mlt cmle cut by linarith
          moreover have "?j1 - Pcut N = Lng ?PJ - 1" using LPJ cut L by linarith
          ultimately show ?thesis by simp
        qed
        have IHJ: "Mark ?PJ (m - Pcut N) \<noteq> Dpt (enat (entry ?PJ 1 (m - Pcut N))) 0\<^sub>B"
          using less.IH[OF LPJlt] mPJ PJRT mltJ by blast
        show ?thesis using kv IHJ eShift by simp
      qed
    qed
  qed
qed

text \<open>命題（右端第1基点の Mark の基本性質）(content.md 2294), with the
  correction A17 (\<open>\<not> zeroT M\<close> excludes the degenerate zero base \<open>[(0,0)]\<close> on
  which the verbatim article form fails).  Forward direction reuses
  @{thm [source] Mark_rightmost1_forward}; the reverse is the contrapositive
  via @{thm [source] Mark_leftend_form} and @{thm [source] Mark_tail_nonzero}.\<close>

lemma m_7_3_Mark_rightmost1:
  assumes "(M, m) \<in> Marked" and "M \<in> RT_PS" and "\<not> zeroT M"
  shows "(m = Lng M - 1) \<longleftrightarrow> (Mark M m = Dpt (enat (entry M 1 m)) 0\<^sub>B)"
proof
  assume mj1: "m = Lng M - 1"
  have "Mark M (Lng M - 1) = Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B"
    using Mark_rightmost1_forward[OF assms(2) assms(3)] assms(1) mj1 by simp
  thus "Mark M m = Dpt (enat (entry M 1 m)) 0\<^sub>B" using mj1 by simp
next
  assume eq: "Mark M m = Dpt (enat (entry M 1 m)) 0\<^sub>B"
  show "m = Lng M - 1"
  proof (rule ccontr)
    assume "m \<noteq> Lng M - 1"
    moreover have "m < Lng M"
    proof -
      have "leR M 0 m (Lng M - 1)" using assms(1) by (simp add: Marked_def)
      thus ?thesis by (simp add: leR_def le0_def)
    qed
    ultimately have mlt: "m < Lng M - 1" by linarith
    have "Mark M m \<noteq> Dpt (enat (entry M 1 m)) 0\<^sub>B"
      using Mark_tail_nonzero assms(1) assms(2) mlt by blast
    thus False using eq by simp
  qed
qed


section \<open>§7.3 命題（右端第2基点の \<open>Mark\<close> の基本性質）— content.md 2334\<close>

text \<open>At the second basepoint \<open>m = j\<^sub>-\<^sub>1 = transJm1 M = Adm M (transJ0 M)\<close>, the
  marked value equals \<open>c\<^sub>2 = transC2 M\<close>.  This is the surgery (\<open>m < j\<^sub>1\<close>) branch of
  @{thm [source] Mark.psimps} (domain from @{thm [source] m_7_3_Mark_welldef}) in
  the mono, \<open>t\<^sub>1 \<noteq> 0\<close> case, but at the basepoint \<open>m = j\<^sub>-\<^sub>1\<close> the replaced
  component \<open>c\<^sub>0 = Mark (Pred M) m\<close> coincides with the \<open>c\<^sub>1\<close> being matched, so the
  scb-decomposition is the trivial self-decomposition \<open>([],[])\<close>
  (@{thm [source] scb_SOME_self}, uniqueness @{thm [source] m_7_2_scb_unique_sb}),
  and the surgery delivers \<open>c\<^sub>2\<close> verbatim.\<close>

lemma m_7_3_Mark_rightmost2:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
  shows "Mark M (transJm1 M) = transC2 M"
proof -
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using J1pos by (simp add: transJ1_def)
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B" using T1 by (simp add: transT1_def)
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  let ?j1 = "Lng M - 1"
  let ?bv = "entry M 1 (Lng M - 1)"
  define jp where "jp = parent M 0 (Lng M - 1)"
  define jm1 where "jm1 = Adm M jp"
  define m where "m = transJm1 M"
  have transJ0eq: "transJ0 M = jp" by (simp add: transJ0_def transJ1_def jp_def)
  have meq: "m = jm1" by (simp add: m_def transJm1_def jm1_def transJ0eq)
  \<comment> \<open>the surgery define-chain, mirroring @{thm [source] Mark_flatIdx_bound}\<close>
  define c1 where "c1 = Mark (Pred M) (Adm M jp)"
  define vv where "vv = bpHeadV c1"
  define tt2 where "tt2 = bpHeadT c1"
  define JJ1 where "JJ1 = Lng (PB tt2) - 1"
  define pj where "pj = PB tt2 ! JJ1"
  define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
  define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
  define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
  define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                 then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                 else if transCondVI M
                 then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                 else if tt2 = 0\<^sub>B
                 then Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                 else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                    (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
  \<comment> \<open>\<open>c\<^sub>1 = transC1 M\<close>, \<open>c\<^sub>2 = transC2 M\<close>\<close>
  have c1eqT: "c1 = transC1 M"
    by (simp add: c1_def transC1_def transJm1_def transJ0eq)
  have c2eqT: "c2 = transC2 M"
    unfolding c2_def transC2_def Let_def
      vv_def tt2_def c1eqT transV_def transT2_def
      JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
    by simp
  \<comment> \<open>at the basepoint, \<open>c\<^sub>0 = Mark (Pred M) m\<close> is exactly \<open>c\<^sub>1\<close>\<close>
  have c1eq: "c1 = Mark (Pred M) m" by (simp add: c1_def meq jm1_def)
  \<comment> \<open>\<open>c\<^sub>1\<close> is a single principal term\<close>
  have pc1: "Lng (PB (transC1 M)) = 1"
    by (rule transC1_single_principal[OF MR MP J1pos T1])
  have c1Dpt: "transC1 M = Dpt (transV M) (transT2 M)"
    using principal_reconstruct[OF pc1]
    by (simp add: transV_def transT2_def)
  have mkjm1: "(Pred M, jm1) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp] jp_def jm1_def by simp
  have c1TB: "transC1 M \<in> T_B"
    using m_7_3_Mark_in_T_B[OF predRT mkjm1] c1eq c1eqT meq by simp
  have vne: "transV M \<noteq> \<infinity>" using c1TB c1Dpt by (auto simp: T_B_def)
  have t2df: "dfree_BT (transT2 M)" using c1TB c1Dpt by (auto simp: T_B_def)
  have c1p: "c1 = Trm [DB (transV M) (transT2 M)]"
    using c1eqT c1Dpt by simp
  \<comment> \<open>\<open>c\<^sub>1\<close> is its own scb-self-decomposition, hence \<open>(c\<^sub>1, c\<^sub>1) \<in> MarkedB\<close>\<close>
  have iptc1: "isPTB_str (flatBT c1)"
  proof -
    have "dfree_BP (DB (transV M) (transT2 M))" using vne t2df by simp
    moreover have "flatBT c1 = flatBP (DB (transV M) (transT2 M))" using c1p by simp
    ultimately show ?thesis unfolding isPTB_str_def by blast
  qed
  have c1ne: "c1 \<noteq> Trm []" using c1p by simp
  have mbc: "(c1, c1) \<in> MarkedB"
    using scb_decomp_self[OF iptc1] unfolding MarkedB_def by auto
  \<comment> \<open>positions: \<open>m = jm1 \<le> jp < j\<^sub>1\<close>, hence \<open>m < j\<^sub>1\<close>\<close>
  have jplt: "jp < ?j1"
  proof -
    have "nextR M 0 jp ?j1"
      using hp unfolding hasParent_def parent_def jp_def by (rule theI')
    thus ?thesis by (simp add: nextR_def nextrel0_def)
  qed
  have mlt: "m < ?j1"
  proof -
    have "m \<le> jp" using adm_Adm_le meq jm1_def by simp
    thus ?thesis using jplt by linarith
  qed
  \<comment> \<open>evaluate the surgery branch of \<open>Mark M m\<close>\<close>
  define sm1 where
    "sm1 = (SOME sb. scb_decomp c1 (fst sb) (flatBT c1) (snd sb))"
  have mark_val_raw: "Mark M m = (if (Mark (Pred M) m, c1) \<in> MarkedB
        then unflatBT
               (fst (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                (flatBT c1) (snd sb))
                @ flatBT c2
                @ snd (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                  (flatBT c1) (snd sb)))
        else Dpt (enat ?bv) 0\<^sub>B)"
    using Mark.psimps[OF domK] MR Lgt1 mono t1ne mlt
    unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
              tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
              ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
              c2_def[symmetric]
    by simp
  have mark_val: "Mark M m = unflatBT (fst sm1 @ flatBT c2 @ snd sm1)"
    using mark_val_raw mbc c1eq[symmetric] by (simp add: sm1_def)
  \<comment> \<open>the scb-self-decomposition is the unique witness \<open>([],[])\<close>\<close>
  have sm1eq: "sm1 = ([], [])"
    unfolding sm1_def by (rule scb_SOME_self[OF iptc1 c1ne])
  have "Mark M m = unflatBT (flatBT c2)" using mark_val sm1eq by simp
  also have "\<dots> = c2" by (rule unflatBT_flat)
  also have "\<dots> = transC2 M" by (rule c2eqT)
  finally show ?thesis using m_def by simp
qed


text \<open>Helper: \<open>find\<close> distributes over append (local copy, name-independent).\<close>

lemma find_append_local:
  "find Q (xs @ ys) = (case find Q xs of None \<Rightarrow> find Q ys | Some r \<Rightarrow> Some r)"
  by (induction xs) auto

text \<open>Helper: the first \<open>D\<close>-symbol of a nonzero term's flat string carries its
  leftmost principal value \<open>bpHeadV\<close>.  (Single principal: the string starts with
  that \<open>Dsym\<close>; multi principal: it starts \<open>LP\<close> then that \<open>Dsym\<close>.)\<close>

lemma bpHeadV_find_Dsym:
  assumes "t \<noteq> 0\<^sub>B"
  shows "find (\<lambda>x. \<exists>v. x = Dsym v) (flatBT t) = Some (Dsym (bpHeadV t))"
proof -
  obtain ps where t: "t = Trm ps" by (cases t)
  have psne: "ps \<noteq> []" using assms t by auto
  obtain p qs where psc: "ps = p # qs" using psne by (cases ps) auto
  obtain w u where pwu: "p = DB w u" by (cases p)
  have bh: "bpHeadV t = w" using t psc pwu by simp
  show ?thesis
  proof (cases qs)
    case Nil
    have "flatBT t = Dsym w # flatBT u" using t psc pwu Nil by simp
    thus ?thesis using bh by simp
  next
    case (Cons q qs')
    have "flatBT t = LP # (Dsym w # flatBT u
                           @ concat (map (\<lambda>r. CM # flatBP r) (q # qs'))) @ [RP]"
      using t psc pwu Cons by simp
    hence "flatBT t = LP # Dsym w # (flatBT u
                           @ concat (map (\<lambda>r. CM # flatBP r) (q # qs')) @ [RP])"
      by simp
    thus ?thesis using bh by simp
  qed
qed

section \<open>§7.3 命題（\<open>Trans\<close> の最左単項成分の左端の基本性質）— content.md 2339\<close>

text \<open>Helper: a reduced pair sequence whose row-0 left end is \<open>0\<close> has its row-1
  left end \<open>0\<close> as well.  By strong \<open>Lng\<close>-induction: zero is \<open>[(0,0)]\<close>; mono uses
  @{thm [source] kfwd_reduced_monoT_diag00} (\<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0\<close>); multi recurses into
  the reduced prefix \<open>take (Pcut M) M\<close>, which shares the left column.\<close>

lemma reduced_e10_zero:
  "M \<in> RT_PS \<longrightarrow> entry M 0 0 = 0 \<longrightarrow> entry M 1 0 = 0"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (intro impI)
    assume MR: "M \<in> RT_PS" and e00: "entry M 0 0 = 0"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    show "entry M 1 0 = 0"
    proof (cases "zeroT M")
      case True
      thus ?thesis by (simp add: zeroT_def)
    next
      case nz: False
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        have "entry M 0 0 = entry M 1 0"
          by (rule kfwd_reduced_monoT_diag00[OF MR mono])
        thus ?thesis using e00 by simp
      next
        case nmono: False
        have muM: "multiT M" using nz nmono by (simp add: multiT_def)
        have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT muM])
        have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
        let ?A = "take (Pcut M) M"
        have Acut_RT: "?A \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF MR muM])
        have LA: "Lng ?A < Lng M"
        proof -
          have "Pcut M < Lng M" using cut L by linarith
          thus ?thesis by (simp add: min_def)
        qed
        have eA00: "entry ?A 0 0 = entry M 0 0"
        proof -
          have "(0::nat) < Pcut M" using cut by simp
          thus ?thesis by (simp add: entry_def)
        qed
        have eA10: "entry ?A 1 0 = entry M 1 0"
        proof -
          have "(0::nat) < Pcut M" using cut by simp
          thus ?thesis by (simp add: entry_def)
        qed
        have "entry ?A 1 0 = 0"
          using less.IH[OF LA] Acut_RT eA00 e00 by simp
        thus ?thesis using eA10 by simp
      qed
    qed
  qed
qed

text \<open>The leftmost index of \<open>Trans M\<close> is \<open>M\<^bsub>1,0\<^esub>\<close> (it is \<open>0\<close> when
  \<open>Trans M = 0\<^sub>B\<close>, which coincides with \<open>entry M 1 0 = 0\<close> there).  Proved by
  strong \<open>Lng\<close>-induction.  The mono surgery branch reuses the
  @{thm [source] trans_inv_B_hard} setup and the @{thm [source] Mark_leftend_form}
  head-preservation argument; the multi branch reuses @{thm [source] trans_inv_C}
  and (in the \<open>Trans (take (Pcut M) M) = 0\<close> sub-case)
  @{thm [source] P_add_Pcut_left_min} + @{thm [source] reduced_e10_zero} to read
  off the leading \<open>0\<close>.\<close>

lemma m_7_3_Trans_leftend:
  "M \<in> RT_PS \<longrightarrow> bpHeadV (Trans M) = enat (entry M 1 0)"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (rule impI)
    assume MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
    \<comment> \<open>small fact: \<open>bpHeadV\<close> of an \<open>+\<^sub>B\<close>-append\<close>
    have headAdd: "\<And>a b. bpHeadV (a +\<^sub>B b)
                          = (if a = 0\<^sub>B then bpHeadV b else bpHeadV a)"
    proof -
      fix a b :: BT
      obtain as where a: "a = Trm as" by (cases a)
      obtain bs where b: "b = Trm bs" by (cases b)
      show "bpHeadV (a +\<^sub>B b) = (if a = 0\<^sub>B then bpHeadV b else bpHeadV a)"
      proof (cases as)
        case Nil
        thus ?thesis using a b by simp
      next
        case (Cons p ps)
        obtain w u where "p = DB w u" by (cases p)
        thus ?thesis using a b Cons by simp
      qed
    qed
    show "bpHeadV (Trans M) = enat (entry M 1 0)"
    proof (cases "Lng M = 1")
      case True
      \<comment> \<open>(A) length 1: \<open>M = [(v,v)]\<close>\<close>
      obtain v where Mv: "M = [(v, v)]"
        using m_6_6_oneColumn[OF MT] MR True by auto
      have tv: "Trans M = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Mv Trans_singleton by simp
      have ev: "entry M 1 0 = v" using Mv by (simp add: entry_def)
      show ?thesis
      proof (cases "v = 0")
        case True thus ?thesis using tv ev by (simp add: zero_enat_def)
      next
        case False thus ?thesis using tv ev by simp
      qed
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      have nzM: "\<not> zeroT M" using notone by (auto simp: zeroT_def)
      let ?j1 = "Lng M - 1"
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        \<comment> \<open>(B) mono branch\<close>
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
        have predLng: "Lng (Pred M) < Lng M" using L by (simp add: Pred_def)
        have predPos: "0 < Lng (Pred M)" using L predb by simp
        note IHp = less.IH[OF predLng, THEN mp, OF predRT]
        have entry0: "entry (Pred M) 1 0 = entry M 1 0"
        proof -
          have "(0::nat) < length (butlast M)" using predb predPos by simp
          thus ?thesis using predb by (simp add: entry_def nth_butlast)
        qed
        show ?thesis
        proof (cases "Trans (Pred M) = 0\<^sub>B")
          case t1z: True
          \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>: \<open>Trans M = D\<^bsub>0\<^esub>(D\<^bsub>M\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0)\<close>, head \<open>0\<close>\<close>
          let ?b = "entry M 1 ?j1"
          have tv: "Trans M = Dpt 0 (Dpt (enat ?b) 0\<^sub>B)"
            using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
          have bp0: "bpHeadV (Trans M) = 0" using tv by (simp add: zero_enat_def)
          have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
          have zP: "zeroT (Pred M)" using m_7_3_Trans_zeroT[OF predRT] t1z by simp
          have LP1: "Lng (Pred M) = 1" using zP by (simp add: zeroT_def)
          obtain w where Pw: "Pred M = [(w, w)]"
            using m_6_6_oneColumn[OF predT] predRT LP1 by auto
          have w0: "w = 0" using zP Pw by (simp add: zeroT_def entry_def)
          have e0: "entry M 1 0 = 0"
          proof -
            have "entry (Pred M) 1 0 = 0" using Pw w0 by (simp add: entry_def)
            thus ?thesis using entry0 by simp
          qed
          show ?thesis using bp0 e0 by (simp add: zero_enat_def)
        next
          case t1ne: False
          \<comment> \<open>(B) \<open>t\<^sub>1 \<noteq> 0\<close>: surgery branch\<close>
          have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L])
          let ?bv = "entry M 1 (Lng M - 1)"
          define jp where "jp = parent M 0 (Lng M - 1)"
          let ?t1 = "Trans (Pred M)"
          define c1 where "c1 = Mark (Pred M) (Adm M jp)"
          define vv where "vv = bpHeadV c1"
          define tt2 where "tt2 = bpHeadT c1"
          define JJ1 where "JJ1 = Lng (PB tt2) - 1"
          define pj where "pj = PB tt2 ! JJ1"
          define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
          define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
          define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
          define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                                 then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                                 else if transCondVI M
                                 then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                                 else if tt2 = 0\<^sub>B
                                 then Dpt vv (Dpt (enat (entry M 1 jp))
                                              (Dpt (enat ?bv) 0\<^sub>B))
                                 else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                                    (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
          define sb1 where
            "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
          have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
            using Trans.psimps[OF domT] MR Lgt1 mono t1ne
            unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                      tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                      ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                      c2_def[symmetric] sb1_def[symmetric]
            by simp
          have transJ1eq: "transJ1 M = ?j1" by (simp add: transJ1_def)
          have transJ0eq: "transJ0 M = jp"
            by (simp add: transJ0_def transJ1_def jp_def)
          have transJm1eq: "transJm1 M = Adm M jp"
            by (simp add: transJm1_def transJ0eq)
          have c1eqT: "c1 = transC1 M"
            by (simp add: c1_def transC1_def transJm1eq)
          have c2eqT: "c2 = transC2 M"
            unfolding c2_def transC2_def Let_def
              vv_def tt2_def c1eqT transV_def transT2_def
              JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
            by simp
          have mkjm1: "(Pred M, Adm M jp) \<in> Marked"
            using Marked_Pred_Adm[OF MT L hp] jp_def by simp
          have NP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
          have J1pos: "transJ1 M > 0" using L by (simp add: transJ1_def)
          have T1ne: "transT1 M \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
          have pc1: "Lng (PB (transC1 M)) = 1"
            by (rule transC1_single_principal[OF MR NP J1pos T1ne])
          have c1ne: "transC1 M \<noteq> 0\<^sub>B"
          proof
            assume "transC1 M = 0\<^sub>B"
            thus False using pc1 by (simp add: PB_def)
          qed
          have c1TB: "transC1 M \<in> T_B"
            using m_7_3_Mark_in_T_B[OF predRT mkjm1]
                  c1eqT[symmetric] c1_def by simp
          have c1Dpt: "transC1 M = Dpt (transV M) (transT2 M)"
            using principal_reconstruct[OF pc1] by (simp add: transV_def transT2_def)
          have c1Dsym: "flatBT c1 = Dsym (transV M) # flatBT (transT2 M)"
            using c1eqT c1Dpt by simp
          have vvT: "vv = transV M" by (simp add: vv_def transV_def c1eqT)
          have bpc2: "bpHeadV c2 = transV M"
          proof -
            have "bpHeadV c2 = vv" by (simp add: c2_def)
            thus ?thesis using vvT by simp
          qed
          have c2pc1: "Lng (PB c2) = 1"
            using transC2_single_principal c2eqT by simp
          have c2Dpt: "c2 = Dpt (transV M) (bpHeadT c2)"
            using principal_reconstruct[OF c2pc1] bpc2 by simp
          have c2Dsym: "flatBT c2 = Dsym (transV M) # flatBT (bpHeadT c2)"
            by (subst c2Dpt) (rule flatBT_principal_head)
          \<comment> \<open>the SOME decomposition of \<open>?t\<^sub>1\<close>\<close>
          have inv1: "(Trans (Pred M), c1) \<in> MarkedB"
            using m_7_3_Trans_Mark_MarkedB[OF predRT mkjm1] c1_def by simp
          have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
            using inv1 unfolding MarkedB_def by auto
          have dsb: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
            unfolding sb1_def by (rule someI_ex[OF exsb])
          have flatt1: "flatBT (Trans (Pred M)) = fst sb1 @ flatBT c1 @ snd sb1"
            using dsb by (simp add: scb_decomp_def)
          \<comment> \<open>the surgery output \<open>Trans M\<close> is the \<open>c\<^sub>2\<close>-replacement, principal\<close>
          have c2df: "dfree_BT c2"
          proof -
            have vne: "transV M \<noteq> \<infinity>" using c1TB c1Dpt by (auto simp: T_B_def)
            have t2df: "dfree_BT (transT2 M)" using c1TB c1Dpt by (auto simp: T_B_def)
            show ?thesis using dfree_transC2[OF vne t2df] c2eqT by simp
          qed
          obtain pc2 where c2p: "c2 = Trm [pc2]"
            using principal_reconstruct[OF c2pc1] by (metis BT.exhaust untrm.simps)
          have iptc2': "isPTB_str (flatBT (Trm [pc2]))"
          proof -
            have "dfree_BT (Trm [pc2])" using c2df c2p by simp
            then obtain p where "pc2 = p" and "dfree_BP p" by auto
            thus ?thesis by (auto simp: isPTB_str_def)
          qed
          obtain pc1' where c1p: "c1 = Trm [pc1']"
            using principal_reconstruct[OF pc1] c1eqT by (metis BT.exhaust untrm.simps)
          have dsb': "scb_decomp ?t1 (fst sb1) (flatBT (Trm [pc1'])) (snd sb1)"
            using dsb c1p by simp
          obtain t' where t'f: "flatBT t' = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
              and t'd: "scb_decomp t' (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
            using scb_replace_principal[OF dsb' iptc2'] by blast
          have transMp: "Trans M = t'"
            using trans_val t'f c2p unflatBT_flat[of t'] by simp
          have flatTM: "flatBT (Trans M) = fst sb1 @ flatBT c2 @ snd sb1"
            using transMp t'f c2p by simp
          \<comment> \<open>both \<open>Trans M\<close> and \<open>Trans (Pred M)\<close> flatten to \<open>fst sb1 @ Dsym (transV M) # _\<close>\<close>
          have flatTMv: "flatBT (Trans M)
                          = fst sb1 @ Dsym (transV M) # (flatBT (bpHeadT c2) @ snd sb1)"
            using flatTM c2Dsym by simp
          have flatt1v: "flatBT (Trans (Pred M))
                          = fst sb1 @ Dsym (transV M) # (flatBT (transT2 M) @ snd sb1)"
            using flatt1 c1Dsym by simp
          have tMne: "Trans M \<noteq> 0\<^sub>B"
          proof
            assume z: "Trans M = 0\<^sub>B"
            hence "flatBT (Trans M) = [Zsym]" by simp
            moreover have "Dsym (transV M) \<in> set (flatBT (Trans M))"
              using flatTMv by simp
            ultimately show False by simp
          qed
          \<comment> \<open>read \<open>bpHeadV\<close> off the first \<open>Dsym\<close> of each flat string\<close>
          let ?P = "\<lambda>x. \<exists>v. x = Dsym v"
          have findM: "find ?P (flatBT (Trans M)) = Some (Dsym (bpHeadV (Trans M)))"
            by (rule bpHeadV_find_Dsym[OF tMne])
          have findt1: "find ?P (flatBT (Trans (Pred M)))
                          = Some (Dsym (bpHeadV (Trans (Pred M))))"
            by (rule bpHeadV_find_Dsym[OF t1ne])
          have findEq: "find ?P (flatBT (Trans M))
                          = find ?P (flatBT (Trans (Pred M)))"
          proof (cases "find ?P (fst sb1)")
            case None
            have "find ?P (flatBT (Trans M))
                    = find ?P (Dsym (transV M) # (flatBT (bpHeadT c2) @ snd sb1))"
              using flatTMv None by (simp add: find_append_local)
            moreover have "find ?P (flatBT (Trans (Pred M)))
                    = find ?P (Dsym (transV M) # (flatBT (transT2 M) @ snd sb1))"
              using flatt1v None by (simp add: find_append_local)
            ultimately show ?thesis by simp
          next
            case (Some r)
            have "find ?P (flatBT (Trans M)) = Some r"
              using flatTMv Some by (simp add: find_append_local)
            moreover have "find ?P (flatBT (Trans (Pred M))) = Some r"
              using flatt1v Some by (simp add: find_append_local)
            ultimately show ?thesis by simp
          qed
          have "Dsym (bpHeadV (Trans M)) = Dsym (bpHeadV (Trans (Pred M)))"
            using findM findt1 findEq by simp
          hence "bpHeadV (Trans M) = bpHeadV (Trans (Pred M))" by simp
          also have "\<dots> = enat (entry (Pred M) 1 0)" using IHp .
          also have "\<dots> = enat (entry M 1 0)" using entry0 by simp
          finally show ?thesis .
        qed
      next
        case nmono: False
        \<comment> \<open>(C) multiT branch\<close>
        have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
        have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
        let ?A = "take (Pcut M) M"
        let ?PJ = "drop (Pcut M) M"
        have Acut_RT: "?A \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF MR muM])
        have LA: "Lng ?A < Lng M"
        proof -
          have "Pcut M < Lng M" using cut L by linarith
          thus ?thesis by (simp add: min_def)
        qed
        have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF MT muM])
        have Pne: "P M \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
        have PJ_RT: "?PJ \<in> RT_PS"
          using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
        have PJT: "?PJ \<in> T_PS" using PJ_RT by (simp add: RT_PS_def)
        have LPJ: "Lng ?PJ < Lng M"
        proof -
          have "Lng ?PJ = Lng M - Pcut M" by simp
          thus ?thesis using cut L by linarith
        qed
        note IHA = less.IH[OF LA, THEN mp, OF Acut_RT]
        note IHJ = less.IH[OF LPJ, THEN mp, OF PJ_RT]
        \<comment> \<open>the recursion value (copy from @{thm [source] trans_inv_C})\<close>
        have nmono': "\<not> monoT M" using muM by (simp add: multiT_def)
        have j0eq: "Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 = Pcut M"
          by (rule trans_multiT_last_component(2)[OF MT muM])
        have LdJ: "Lng ?PJ = Lng M - Pcut M" by simp
        have Aeq2: "seg M 0 (Lng M - 1 - Lng ?PJ + 1 - 1) = ?A"
        proof -
          have "Lng M - 1 - Lng ?PJ + 1 - 1 = Pcut M - 1"
            using LdJ cut by linarith
          moreover have "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
            by (rule seg_0_eq_take) (use cut L in linarith)
          moreover have "Suc (Pcut M - 1) = Pcut M" using cut by simp
          ultimately show ?thesis by simp
        qed
        have c1f: "(M \<notin> RT_PS) = False" using MR by simp
        have c2f: "(Lng M - 1 = 0) = False" using L by simp
        have c3f: "monoT M = False" using nmono' by simp
        have transM: "Trans M = (if ?PJ = [(0, 0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B
                                 else Trans ?A +\<^sub>B Trans ?PJ)"
        proof -
          have raw: "Trans M =
              (if P M ! (Lng (P M) - 1) = [(0, 0)]
               then Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                      +\<^sub>B Dpt 0 0\<^sub>B
               else Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                      +\<^sub>B Trans (P M ! (Lng (P M) - 1)))"
            by (subst Trans.psimps[OF domT]) (simp only: c1f c2f c3f if_False Let_def)
          show ?thesis unfolding raw PJeq Aeq2 ..
        qed
        have entryA: "entry ?A 1 0 = entry M 1 0"
        proof -
          have "(0::nat) < Pcut M" using cut by simp
          thus ?thesis by (simp add: entry_def)
        qed
        show ?thesis
        proof (cases "Trans ?A = 0\<^sub>B")
          case TA0: False
          have bpA: "bpHeadV (Trans ?A) = enat (entry ?A 1 0)" using IHA .
          show ?thesis
          proof (cases "?PJ = [(0, 0)]")
            case True
            have "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM True by simp
            hence "bpHeadV (Trans M) = bpHeadV (Trans ?A)"
              using headAdd[of "Trans ?A" "Dpt 0 0\<^sub>B"] TA0 by simp
            thus ?thesis using bpA entryA by simp
          next
            case False
            have "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM False by simp
            hence "bpHeadV (Trans M) = bpHeadV (Trans ?A)"
              using headAdd[of "Trans ?A" "Trans ?PJ"] TA0 by simp
            thus ?thesis using bpA entryA by simp
          qed
        next
          case TA0: True
          \<comment> \<open>\<open>Trans ?A = 0\<close> so \<open>zeroT ?A\<close>, giving \<open>entry M 1 0 = 0\<close> and
             (via the cut left-minimality + reducedness of \<open>?PJ\<close>)
             \<open>entry ?PJ 1 0 = 0\<close>.\<close>
          have zA: "zeroT ?A" using m_7_3_Trans_zeroT[OF Acut_RT] TA0 by simp
          have LA1: "Lng ?A = 1" using zA by (simp add: zeroT_def)
          have eA10: "entry ?A 1 0 = 0" using zA by (simp add: zeroT_def)
          have eM10: "entry M 1 0 = 0" using eA10 entryA by simp
          \<comment> \<open>row-0 of column 0 is also 0 (since \<open>?A = [(0,0)]\<close>)\<close>
          have AT: "?A \<in> T_PS" using Acut_RT by (simp add: RT_PS_def)
          have eA00: "entry ?A 0 0 = 0"
          proof -
            obtain v where Av: "?A = [(v, v)]"
              using m_6_6_oneColumn[OF AT] Acut_RT LA1 by auto
            have "entry ?A 1 0 = v" using Av by (simp add: entry_def)
            hence "v = 0" using eA10 by simp
            thus ?thesis using Av by (simp add: entry_def)
          qed
          have eM00: "entry M 0 0 = 0"
          proof -
            have "(0::nat) < Pcut M" using cut by simp
            hence "entry ?A 0 0 = entry M 0 0" by (simp add: entry_def)
            thus ?thesis using eA00 by simp
          qed
          \<comment> \<open>row-0 of column \<open>Pcut M\<close> is 0 by left-minimality of the cut\<close>
          have ePcut00: "entry M 0 (Pcut M) = 0"
          proof -
            have "entry M 0 0 \<ge> entry M 0 (Pcut M)"
              using P_add_Pcut_left_min[OF MT muM L, of 0] cut by simp
            thus ?thesis using eM00 by simp
          qed
          have ePJ00: "entry ?PJ 0 0 = 0"
          proof -
            have "(0::nat) < Lng ?PJ" using cut L LdJ by linarith
            hence "entry ?PJ 0 0 = entry M 0 (Pcut M)" by (simp add: entry_def)
            thus ?thesis using ePcut00 by simp
          qed
          \<comment> \<open>and hence row-1 of column \<open>Pcut M\<close> (left end of \<open>?PJ\<close>) is 0\<close>
          have ePJ10: "entry ?PJ 1 0 = 0"
            using reduced_e10_zero PJ_RT ePJ00 by blast
          show ?thesis
          proof (cases "?PJ = [(0, 0)]")
            case True
            have "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM True by simp
            hence "bpHeadV (Trans M) = bpHeadV (Dpt 0 0\<^sub>B)"
              using headAdd[of "Trans ?A" "Dpt 0 0\<^sub>B"] TA0 by simp
            hence "bpHeadV (Trans M) = 0" by (simp add: zero_enat_def)
            thus ?thesis using eM10 by (simp add: zero_enat_def)
          next
            case False
            have tv: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM False by simp
            have bpM: "bpHeadV (Trans M) = bpHeadV (Trans ?PJ)"
              using tv headAdd[of "Trans ?A" "Trans ?PJ"] TA0 by simp
            have bpJ: "bpHeadV (Trans ?PJ) = enat (entry ?PJ 1 0)" using IHJ .
            have "bpHeadV (Trans M) = 0"
              using bpM bpJ ePJ10 by (simp add: zero_enat_def)
            thus ?thesis using eM10 by (simp add: zero_enat_def)
          qed
        qed
      qed
    qed
  qed
qed

text \<open>§7.4 join-lift: if \<open>(s,c,b)\<close> is an scb-decomposition of a single-principal
  \<open>X\<close> around the principal block \<open>c\<close>, then prefixing \<open>X\<close> by \<open>Y\<close> via \<open>+\<^sub>B\<close>
  (which concatenates the principal lists) yields a deterministic
  scb-decomposition of \<open>Y +\<^sub>B X\<close> around the SAME \<open>c\<close>, obtained by re-bracketing
  the leading \<open>Y\<close>-part into the join.  The multi-component bridge transporting the
  \<open>m\<close>-basepoint position from the last \<open>P\<close>-component up to \<open>M\<close> (and identically for
  \<open>Pred M\<close>, since both share the \<open>Trans (take (Pcut M) M)\<close> prefix).\<close>

definition liftS :: "BT \<Rightarrow> Sym list \<Rightarrow> Sym list" where
  "liftS Y s = LP # flatBP (hd (untrm Y))
                  @ concat (map (\<lambda>r. CM # flatBP r) (tl (untrm Y))) @ CM # s"

text \<open>The \<open>Mark\<close>-analogue of @{thm [source] Trans_Pred_multi_last}: for a multi
  \<open>M \<in> RT\<^sub>PS\<close> with non-trivial last \<open>P\<close>-component \<open>PJ = drop (Pcut M) M\<close>, the
  predecessor's mark acts inside the last component (using that \<open>Pred M\<close> is
  itself multi with the same cut and last component \<open>Pred PJ\<close>).\<close>

lemma Mark_Pred_multi_last:
  assumes MR: "M \<in> RT_PS" and mu: "multiT M"
    and LPJ: "1 < Lng (drop (Pcut M) M)"
  shows "Mark (Pred M) m
         = (if Pred (drop (Pcut M) M) = [(0,0)] then Dpt 0 0\<^sub>B
            else Mark (Pred (drop (Pcut M) M)) (m - Pcut M))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  let ?c = "Pcut M"
  let ?A = "take ?c M"
  let ?PJ = "drop ?c M"
  have cut: "0 < ?c \<and> ?c \<le> Lng M - 1" using Pcut_le[OF L] by simp
  have LdropPJ: "Lng ?PJ = Lng M - ?c" by simp
  have cltj1: "?c < Lng M - 1"
  proof -
    have "Lng ?PJ = Lng M - ?c" by simp
    thus ?thesis using LPJ cut by linarith
  qed
  have lenlast_gt1: "1 < Lng (last (P M))"
    using poper_last_P_multi[OF mu L] LPJ by simp
  have predsplit: "Pred M = ?A @ Pred ?PJ"
    by (rule poper_Pred_split[OF cltj1 L])
  have Pdec: "P (Pred M) = butlast (P M) @ [Pred (last (P M))]"
    using pred_P_decomp[OF MT mu] lenlast_gt1 by simp
  have Pdec2: "P (Pred M) = P ?A @ [Pred ?PJ]"
  proof -
    have "butlast (P M) = P ?A" using poper_last_P_multi[OF mu L] by simp
    moreover have "last (P M) = ?PJ" using poper_last_P_multi[OF mu L] by simp
    ultimately show ?thesis using Pdec by simp
  qed
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
  have PAne: "P ?A \<noteq> []" by (rule P_nonempty)
  have lenPpred: "1 < length (P (Pred M))"
    using Pdec2 PAne by (cases "P ?A") auto
  have mupred: "multiT (Pred M)"
    using m_6_2_P_components_2[OF predT] lenPpred by simp
  have Lpred: "1 < Lng (Pred M)"
    by (rule multiT_imp_Lng_gt1[OF predT mupred])
  let ?cP = "Pcut (Pred M)"
  have lastPpred: "last (P (Pred M)) = drop ?cP (Pred M)
                   \<and> butlast (P (Pred M)) = P (take ?cP (Pred M))"
    by (rule poper_last_P_multi[OF mupred Lpred])
  have lastval: "last (P (Pred M)) = Pred ?PJ" using Pdec2 by simp
  have dropPred: "drop ?cP (Pred M) = Pred ?PJ"
    using lastPpred lastval by simp
  have takePred: "take ?cP (Pred M) = ?A"
  proof -
    have "take ?cP (Pred M) @ drop ?cP (Pred M) = Pred M" by simp
    hence "take ?cP (Pred M) @ Pred ?PJ = ?A @ Pred ?PJ"
      using dropPred predsplit by simp
    thus ?thesis by simp
  qed
  have LAc: "Lng ?A = ?c"
  proof -
    have "?c \<le> Lng M" using cut L by linarith
    thus ?thesis by simp
  qed
  have PcutEq: "?cP = ?c"
  proof -
    have "Lng (take ?cP (Pred M)) = Lng ?A" using takePred by simp
    moreover have "Lng (take ?cP (Pred M)) = min ?cP (Lng (Pred M))" by simp
    ultimately have "min ?cP (Lng (Pred M)) = ?c" using LAc by simp
    moreover have "?cP \<le> Lng (Pred M)" using Pcut_le[OF Lpred] by linarith
    ultimately show ?thesis by (simp add: min_def)
  qed
  have domKP: "\<And>k. Trans_Mark_dom (Inr (Pred M, k))"
    by (rule m_7_3_Mark_welldef[OF predRT])
  have LgtP: "\<not> Lng (Pred M) \<le> Suc 0" using Lpred by simp
  have nmonoP: "\<not> monoT (Pred M)" using mupred by (simp add: multiT_def)
  have PJeqP: "P (Pred M) ! (Lng (P (Pred M)) - 1) = drop ?cP (Pred M)"
    by (rule trans_multiT_last_component(1)[OF predT mupred])
  have c1: "(Pred M \<notin> RT_PS) = False" using predRT by simp
  have c2: "(Lng (Pred M) - 1 = 0) = False" using Lpred by simp
  have c3: "monoT (Pred M) = False" using nmonoP by simp
  have cutP: "0 < ?cP \<and> ?cP \<le> Lng (Pred M) - 1" using Pcut_le[OF Lpred] by simp
  have LdJP: "Lng (drop ?cP (Pred M)) = Lng (Pred M) - ?cP" by simp
  have meq2P: "Lng (Pred M) - 1 - Lng (drop ?cP (Pred M)) + 1 = ?cP"
    using LdJP cutP by linarith
  have markP: "Mark (Pred M) m =
      (if drop ?cP (Pred M) = [(0,0)] then Dpt 0 0\<^sub>B
       else Mark (drop ?cP (Pred M)) (m - ?cP))"
  proof -
    have raw: "Mark (Pred M) m =
        (if P (Pred M) ! (Lng (P (Pred M)) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
         else Mark (P (Pred M) ! (Lng (P (Pred M)) - 1))
                (m - (Lng (Pred M) - 1 - Lng (P (Pred M) ! (Lng (P (Pred M)) - 1)) + 1)))"
      by (subst Mark.psimps[OF domKP]) (simp only: c1 c2 c3 if_False Let_def)
    show ?thesis unfolding raw PJeqP using meq2P by simp
  qed
  show ?thesis using markP dropPred takePred PcutEq by simp
qed

lemma scb_addBT_left:
  assumes d: "scb_decomp X s c b"
    and X1: "length (untrm X) = 1"
    and Yne: "untrm Y \<noteq> []"
  shows "scb_decomp (Y +\<^sub>B X) (liftS Y s) c (b @ [RP])"
proof -
  obtain x0 where xs: "untrm X = [x0]" using X1 by (cases "untrm X") auto
  obtain ys where ysd: "untrm Y = ys" by simp
  have ysne: "ys \<noteq> []" using Yne ysd by simp
  have Xne: "X \<noteq> Trm []" using xs by (cases X) auto
  have flatX: "flatBT X = flatBP x0" using xs by (cases X) simp
  from d have eq: "flatBT X = s @ c @ b"
    and ptc: "isPTB_str c" and rb: "\<forall>z \<in> set b. z = RP"
    using Xne by (auto simp: scb_decomp_def)
  have eqX: "flatBP x0 = s @ c @ b" using eq flatX by simp
  obtain p ps where ysc: "ys = p # ps"
    using ysne by (cases ys) auto
  have yx: "Y +\<^sub>B X = Trm (ys @ [x0])"
    using xs ysd by (cases X; cases Y) auto
  obtain q qs where qqs: "ps @ [x0] = q # qs" by (cases ps) auto
  have lst: "ys @ [x0] = p # q # qs" using ysc qqs by simp
  have flatYX: "flatBT (Y +\<^sub>B X)
      = LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (ps @ [x0]))) @ [RP]"
    using yx lst qqs by simp
  have concEq: "concat (map (\<lambda>r. CM # flatBP r) (ps @ [x0]))
      = concat (map (\<lambda>r. CM # flatBP r) ps) @ CM # flatBP x0" by simp
  let ?yf = "flatBP p @ concat (map (\<lambda>r. CM # flatBP r) ps)"
  have flatYX2: "flatBT (Y +\<^sub>B X) = (LP # ?yf @ CM # s) @ c @ (b @ [RP])"
    using flatYX concEq eqX by simp
  have liftSeq: "liftS Y s = LP # ?yf @ CM # s"
    using ysd ysc by (simp add: liftS_def)
  have rb': "\<forall>z \<in> set (b @ [RP]). z = RP" using rb by simp
  show ?thesis
    unfolding scb_decomp_def
    using flatYX2 liftSeq ptc rb' by simp
qed

text \<open>\<open>Trans\<close> of a (reduced) monotone / principal sequence is a single principal
  term (\<open>length (untrm \<dots>) = 1\<close>) when it is nonzero.  By cases on the \<open>Trans\<close>
  recursion: \<open>Lng = 1\<close> gives \<open>D\<^bsub>v\<^esub> 0\<close>; the mono surgery output is \<open>transC2 M\<close>
  (single principal, @{thm [source] transC2_single_principal}); the \<open>t\<^sub>1 = 0\<close>
  branch is \<open>D\<^bsub>0\<^esub>(\<dots>)\<close>.\<close>

lemma Trans_PT_single:
  "M \<in> RT_PS \<longrightarrow> monoT M \<longrightarrow> Trans M \<noteq> 0\<^sub>B \<longrightarrow> (\<exists>p. Trans M = Trm [p])"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (intro impI)
    assume MR: "M \<in> RT_PS" and mono: "monoT M" and tne: "Trans M \<noteq> 0\<^sub>B"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    show "\<exists>p. Trans M = Trm [p]"
    proof (cases "Lng M = 1")
      case True
      obtain v where Mv: "M = [(v, v)]"
        using m_6_6_oneColumn[OF MT] MR True by auto
      have "Trans M = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Mv Trans_singleton by simp
      hence "Trans M = Dpt (enat v) 0\<^sub>B" using tne by (cases "v = 0") auto
      thus ?thesis by auto
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      let ?j1 = "Lng M - 1"
      show ?thesis
      proof (cases "Trans (Pred M) = 0\<^sub>B")
        case t1z: True
        have "Trans M = Dpt 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
          using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
        thus ?thesis by auto
      next
        case t1ne: False
        have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L])
        let ?t1 = "Trans (Pred M)"
        let ?bv = "entry M 1 ?j1"
        define jp where "jp = parent M 0 (Lng M - 1)"
        define c1 where "c1 = Mark (Pred M) (Adm M jp)"
        define vv where "vv = bpHeadV c1"
        define tt2 where "tt2 = bpHeadT c1"
        define JJ1 where "JJ1 = Lng (PB tt2) - 1"
        define pj where "pj = PB tt2 ! JJ1"
        define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
        define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
        define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
        define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                               then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                               else if transCondVI M
                               then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                               else if tt2 = 0\<^sub>B
                               then Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                               else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                                  (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
        define sb1 where "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
        have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
          using Trans.psimps[OF domT] MR Lgt1 mono t1ne
          unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                    tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                    ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                    c2_def[symmetric] sb1_def[symmetric]
          by simp
        have c2eqT: "c2 = transC2 M"
          unfolding c2_def transC2_def Let_def
            vv_def tt2_def c1_def transV_def transT2_def transC1_def transJm1_def
            JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0_def jp_def
          by simp
        have c2pc1: "Lng (PB (transC2 M)) = 1" by (rule transC2_single_principal)
        obtain pc2 where c2p: "c2 = Trm [pc2]"
          using c2pc1 c2eqT by (cases "transC2 M") (auto simp: PB_def length_Suc_conv)
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        have mkdA: "(Pred M, Adm M jp) \<in> Marked"
          using Marked_Pred_Adm[OF MT L hp] jp_def by simp
        have mb1: "(?t1, c1) \<in> MarkedB"
          using m_7_3_Trans_Mark_MarkedB[OF predRT mkdA] c1_def by simp
        have t1neT: "?t1 \<noteq> Trm []" using t1ne by simp
        have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
          using mb1 unfolding MarkedB_def by auto
        have dsome: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
          unfolding sb1_def by (rule someI_ex[OF exsb])
        have iptc1: "isPTB_str (flatBT c1)"
          using dsome t1neT by (simp add: scb_decomp_def)
        then obtain pc where pcl: "flatBT c1 = flatBP pc" by (auto simp: isPTB_str_def)
        have c1p: "c1 = Trm [pc]"
          by (metis pcl flatBT.simps(2) m_7_flatBT_inj)
        have c1TB: "c1 \<in> T_B" using m_7_3_Mark_in_T_B[OF predRT mkdA] c1_def by simp
        obtain wv tb where pcw: "pc = DB wv tb" by (cases pc) auto
        have iptc2': "isPTB_str (flatBT (Trm [pc2]))"
        proof -
          have vne: "transV M \<noteq> \<infinity>"
          proof -
            have "transV M = bpHeadV c1" by (simp add: transV_def transC1_def transJm1_def
                  transJ0_def transJ1_def jp_def c1_def)
            also have "\<dots> = wv" using c1p pcw by simp
            finally show ?thesis using c1TB c1p pcw by (auto simp: T_B_def)
          qed
          have t2df: "dfree_BT (transT2 M)"
          proof -
            have "transT2 M = bpHeadT c1" by (simp add: transT2_def transC1_def transJm1_def
                  transJ0_def transJ1_def jp_def c1_def)
            also have "\<dots> = tb" using c1p pcw by simp
            finally show ?thesis using c1TB c1p pcw by (auto simp: T_B_def)
          qed
          have c2df: "dfree_BT c2" using dfree_transC2[OF vne t2df] c2eqT by simp
          show ?thesis using c2df c2p by (auto simp: isPTB_str_def)
        qed
        \<comment> \<open>IH: \<open>Trans (Pred M)\<close> is single-principal (mono, nonzero)\<close>
        have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
        have predLng: "Lng (Pred M) < Lng M" using L predb by simp
        have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
        have predmono: "monoT (Pred M)"
        proof (cases "Lng (Pred M) = 1")
          case True
          obtain v where Pv: "Pred M = [(v, v)]"
            using m_6_6_oneColumn[OF predT] predRT True by auto
          have "Trans (Pred M) = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
            using Pv Trans_singleton[of v] by simp
          hence vnz: "v \<noteq> 0" using t1ne by (cases "v = 0") auto
          have nz: "\<not> zeroT (Pred M)" using Pv vnz by (simp add: zeroT_def entry_def)
          have "leR (Pred M) 0 0 (Lng (Pred M) - 1)"
            using True by (simp add: leR_def le0_def)
          thus ?thesis using nz by (simp add: monoT_def)
        next
          case False
          have NP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
          have L2: "1 < Lng M - 1" using L False predb by simp
          have j0pos: "0 < Lng M - 2" using L2 by simp
          have j0lt: "Lng M - 2 < Lng M" using L by simp
          have mp: "monoT (seg M 0 (Lng M - 2))"
            by (rule m_6_2_mono_prefix[OF NP j0pos j0lt])
          have "seg M 0 (Lng M - 2) = butlast M"
          proof -
            have suc: "Suc (Lng M - 2) \<le> Lng M" using L2 by simp
            have "seg M 0 (Lng M - 2) = take (Suc (Lng M - 2)) M"
              by (rule seg_0_eq_take[OF suc])
            also have "Suc (Lng M - 2) = Lng M - 1" using L2 by simp
            also have "take (Lng M - 1) M = butlast M" by (simp add: butlast_conv_take)
            finally show ?thesis .
          qed
          thus ?thesis using mp predb by simp
        qed
        obtain pcc where t1p: "Trans (Pred M) = Trm [pcc]"
          using less.IH[OF predLng] predRT predmono t1ne by blast
        \<comment> \<open>\<open>sb1\<close> decomposes the single principal \<open>Trm [pcc]\<close>; \<open>scb_replace_principal_BP\<close>\<close>
        have dsome'': "scb_decomp (Trm [pcc]) (fst sb1) (flatBT (Trm [pc])) (snd sb1)"
          using dsome t1p c1p by simp
        obtain pm where pmf: "flatBP pm = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
            and pmd: "scb_decomp (Trm [pm]) (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
          using scb_replace_principal_BP[OF dsome'' iptc2'] by blast
        have "flatBT (Trm [pm]) = fst sb1 @ flatBT c2 @ snd sb1"
          using pmf c2p by simp
        hence "Trans M = Trm [pm]"
          using trans_val unflatBT_flat[of "Trm [pm]"] by simp
        thus ?thesis by blast
      qed
    qed
  qed
qed

text \<open>§7.4 命題（\<open>Mark\<close> の \<open>Trans\<close> による表示） / \<open>p_7_4_Trans_Mark_Pred\<close>
  (content.md 2490).  For a reduced \<open>M\<close> and a marked column \<open>m < Lng M - 1\<close>, the
  \<open>m\<close>-basepoint sits at the SAME scb-position \<open>(s\<^sub>0,b\<^sub>0)\<close> in \<open>Trans (Pred M)\<close>
  (around \<open>Mark (Pred M) m\<close>) and in \<open>Trans M\<close> (around \<open>Mark M m\<close>).  Strong
  \<open>Lng\<close>-induction.  Uniqueness is pinned by the \<open>Trans (Pred M)\<close>-conjunct
  (@{thm [source] m_7_2_scb_unique_sb}, with the degenerate \<open>Trans (Pred M) = 0\<^sub>B\<close>
  sub-case forcing \<open>([],[])\<close>).  Existence: the mono surgery branch transports the
  \<open>Pred\<close>-side witness through the \<open>c\<^sub>1 \<rightarrow> c\<^sub>2\<close> replacement (cf.
  @{thm [source] trans_inv_B_hard}); the multi branch recurses to the last
  \<open>P\<close>-component and lifts both sides through the SAME \<open>Trans (take (Pcut M) M) +\<^sub>B _\<close>
  prefix (@{thm [source] scb_addBT_left}, @{thm [source] Trans_Pred_multi_last},
  @{thm [source] Mark_Pred_multi_last}).\<close>

lemma addBT_zero_left: "0\<^sub>B +\<^sub>B Y = Y" by (cases Y) simp

lemma m_7_4_Trans_Mark_Pred:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mlt: "m < Lng M - 1"
  shows "\<exists>!sb. scb_decomp (Trans (Pred M)) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)
            \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
proof -
  have ex: "M \<in> RT_PS \<longrightarrow> (\<forall>m. (M, m) \<in> Marked \<longrightarrow> m < Lng M - 1 \<longrightarrow>
       (\<exists>s0 b0.
          scb_decomp (Trans (Pred M)) s0 (flatBT (Mark (Pred M) m)) b0
        \<and> scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0))"
  proof (induction M rule: measure_induct_rule[where f=Lng])
    case (less M)
    show ?case
    proof (intro impI allI)
      fix m
      assume MR: "M \<in> RT_PS" and mM: "(M, m) \<in> Marked" and mlt: "m < Lng M - 1"
      have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
      have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
      have L: "1 < Lng M" using mlt by linarith
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
      have domK: "\<And>k. Trans_Mark_dom (Inr (M, k))" by (rule m_7_3_Mark_welldef[OF MR])
      let ?j1 = "Lng M - 1"
      have nzM: "\<not> zeroT M" using L by (auto simp: zeroT_def)
      show "\<exists>s0 b0. scb_decomp (Trans (Pred M)) s0 (flatBT (Mark (Pred M) m)) b0
                  \<and> scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
      proof (cases "monoT M")
        case mono: True
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
        have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
        have LPred: "Lng (Pred M) = Lng M - 1" using predb by simp
        have mPred: "(Pred M, m) \<in> Marked" by (rule Marked_Pred[OF MT L mM mlt])
        have invP: "(Trans (Pred M), Mark (Pred M) m) \<in> MarkedB"
          by (rule m_7_3_Trans_Mark_MarkedB[OF predRT mPred])
        obtain s0 b0 where d0: "scb_decomp (Trans (Pred M)) s0 (flatBT (Mark (Pred M) m)) b0"
          using invP by (auto simp: MarkedB_def)
        show ?thesis
        proof (cases "Trans (Pred M) = 0\<^sub>B")
          case t1z: True
          have zP: "zeroT (Pred M)" using m_7_3_Trans_zeroT[OF predRT] t1z by simp
          have LP1: "Lng (Pred M) = 1" using zP by (simp add: zeroT_def)
          have L2: "Lng M = 2" using LP1 LPred L by linarith
          have m0: "m = 0" using mlt L2 by simp
          obtain w where Pw: "Pred M = [(w, w)]"
            using m_6_6_oneColumn[OF predT] predRT LP1 by auto
          have w0: "w = 0" using zP Pw by (simp add: zeroT_def entry_def)
          have kP0: "Mark (Pred M) m = 0\<^sub>B"
            using Pw w0 Mark_singleton m0 by simp
          have s0b0: "s0 = [] \<and> b0 = []"
          proof -
            have "flatBT (Trans (Pred M)) = s0 @ flatBT (Mark (Pred M) m) @ b0"
              using d0 by (simp add: scb_decomp_def)
            hence "[Zsym] = s0 @ [Zsym] @ b0" using t1z kP0 by simp
            thus ?thesis by (cases s0) auto
          qed
          let ?bv = "entry M 1 ?j1"
          have tv: "Trans M = Dpt 0 (Dpt (enat ?bv) 0\<^sub>B)"
            using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
          have kv: "Mark M m = Dpt 0 (Dpt (enat ?bv) 0\<^sub>B)"
            using Mark.psimps[OF domK] MR Lgt1 mono t1z m0 by (simp add: Let_def)
          have iptM: "isPTB_str (flatBT (Trans M))"
          proof -
            have "isPTB_str (flatBT (Dpt 0 (Dpt (enat ?bv) 0\<^sub>B)))"
              by (rule isPTB_str_Dpt) (simp_all add: zero_enat_def)
            thus ?thesis using tv by simp
          qed
          have "scb_decomp (Trans M) [] (flatBT (Mark M m)) []"
            using tv kv iptM by (simp add: scb_decomp_def)
          thus ?thesis using d0 s0b0 by auto
        next
          case t1ne: False
          have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L])
          let ?t1 = "Trans (Pred M)"
          let ?bv = "entry M 1 ?j1"
          define jp where "jp = parent M 0 (Lng M - 1)"
          define c1 where "c1 = Mark (Pred M) (Adm M jp)"
          define vv where "vv = bpHeadV c1"
          define tt2 where "tt2 = bpHeadT c1"
          define JJ1 where "JJ1 = Lng (PB tt2) - 1"
          define pj where "pj = PB tt2 ! JJ1"
          define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
          define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
          define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
          define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                                 then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                                 else if transCondVI M
                                 then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                                 else if tt2 = 0\<^sub>B
                                 then Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                                 else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                                    (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
          define sb1 where "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
          have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
            using Trans.psimps[OF domT] MR Lgt1 mono t1ne
            unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                      tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                      ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                      c2_def[symmetric] sb1_def[symmetric]
            by simp
          have mkdA: "(Pred M, Adm M jp) \<in> Marked"
            using Marked_Pred_Adm[OF MT L hp] jp_def by simp
          have mb1: "(?t1, c1) \<in> MarkedB"
            using m_7_3_Trans_Mark_MarkedB[OF predRT mkdA] c1_def by simp
          have t1neT: "?t1 \<noteq> Trm []" using t1ne by simp
          have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
            using mb1 unfolding MarkedB_def by auto
          have dsome: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
            unfolding sb1_def by (rule someI_ex[OF exsb])
          have iptc1: "isPTB_str (flatBT c1)"
            using dsome t1neT by (simp add: scb_decomp_def)
          then obtain pc where pcl: "flatBT c1 = flatBP pc"
            by (auto simp: isPTB_str_def)
          have c1p: "c1 = Trm [pc]"
          proof -
            have "flatBT c1 = flatBT (Trm [pc])" using pcl by simp
            thus ?thesis by (rule m_7_flatBT_inj)
          qed
          obtain wv tb where pcw: "pc = DB wv tb" by (cases pc) auto
          have vvv: "vv = wv" using vv_def c1p pcw by simp
          have tt2v: "tt2 = tb" using tt2_def c1p pcw by simp
          have c1TB: "c1 \<in> T_B" using m_7_3_Mark_in_T_B[OF predRT mkdA] c1_def by simp
          have wvne: "wv \<noteq> \<infinity>" and tbdf: "dfree_BT tb"
            using c1TB c1p pcw by (auto simp: T_B_def)
          have c2shape: "\<exists>X. c2 = Dpt vv X \<and> dfree_BT X"
          proof -
            consider (A) "transCondI M \<or> transCondIII M \<or> transCondV M"
              | (VI) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "transCondVI M"
              | (Z) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "\<not> transCondVI M"
                    "tt2 = 0\<^sub>B"
              | (E) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "\<not> transCondVI M"
                    "tt2 \<noteq> 0\<^sub>B"
              by blast
            thus ?thesis
            proof cases
              case A
              have x: "c2 = Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)" using A c2_def by simp
              have df: "dfree_BT (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)"
                using tt2v tbdf by (cases tb) auto
              show ?thesis using x df by blast
            next
              case VI
              have x: "c2 = Dpt vv (Dpt (enat ?bv) 0\<^sub>B)" using VI c2_def by simp
              show ?thesis using x by auto
            next
              case Z
              have x: "c2 = Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))"
                using Z c2_def by simp
              show ?thesis using x by auto
            next
              case E
              have x: "c2 = Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                           (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B))"
                using E c2_def by simp
              have df3: "dfree_BT tt3"
              proof -
                have "dfree_BT (SigmaB (take JJ1 (PB tb)))"
                  using tbdf by (cases tb) (auto simp: SigmaB_def PB_def dest!: in_set_takeD)
                thus ?thesis using tt3_def tt2v tbdf by simp
              qed
              have df4: "dfree_BT tt4"
              proof -
                have tbne: "untrm tb \<noteq> []" using E(3) tt2v by (cases tb) auto
                have inr: "JJ1 < Lng (PB tb)"
                  using JJ1_def tt2v tbne by (simp add: PB_def)
                have "pj \<in> set (PB tb)" using pj_def tt2v inr by simp
                hence "dfree_BT pj" using tbdf by (cases tb) (auto simp: PB_def)
                hence "dfree_BT (bpHeadT pj)" by (cases pj rule: bpHeadT.cases) auto
                thus ?thesis using tt4_def tt2v tbdf by simp
              qed
              have dfsum: "dfree_BT (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)"
                using df4 by (cases tt4) auto
              have dfall: "dfree_BT (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                            (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B))"
                using df3 dfsum by (cases tt3) auto
              show ?thesis using x dfall by blast
            qed
          qed
          obtain X2 where c2X: "c2 = Dpt vv X2" and X2df: "dfree_BT X2"
            using c2shape by blast
          have c2df: "dfree_BT c2" using c2X X2df wvne vvv by simp
          have iptc2: "isPTB_str (flatBT c2)"
            using c2X by (intro isPTB_str_Dpt[of vv X2, folded c2X])
                         (use wvne vvv X2df in simp_all)
          obtain pc2 where c2p: "c2 = Trm [pc2]" using c2X by auto
          have iptc2': "isPTB_str (flatBT (Trm [pc2]))" using iptc2 c2p by simp
          have dsome': "scb_decomp ?t1 (fst sb1) (flatBT (Trm [pc])) (snd sb1)"
            using dsome c1p by simp
          obtain t' where t'f: "flatBT t' = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
              and t'd: "scb_decomp t' (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
            using scb_replace_principal[OF dsome' iptc2'] by blast
          have transM: "Trans M = t'"
            using trans_val t'f c2p unflatBT_flat[of t'] by simp
          define c0 where "c0 = Mark (Pred M) m"
          define sm1 where "sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))"
          have mark_val: "Mark M m = (if (c0, c1) \<in> MarkedB
                then unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
                else Dpt (enat ?bv) 0\<^sub>B)"
          proof -
            have raw: "Mark M m = (if (Mark (Pred M) m, c1) \<in> MarkedB
                  then unflatBT
                         (fst (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                          (flatBT c1) (snd sb))
                          @ flatBT c2
                          @ snd (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                            (flatBT c1) (snd sb)))
                  else Dpt (enat ?bv) 0\<^sub>B)"
              using Mark.psimps[OF domK] MR Lgt1 mono t1ne mlt
              unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                        tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                        ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                        c2_def[symmetric]
              by simp
            thus ?thesis by (simp add: c0_def sm1_def)
          qed
          have c0df: "dfree_BT c0"
            using m_7_3_Mark_in_T_B[OF predRT mPred] c0_def by (simp add: T_B_def)
          have d0': "scb_decomp ?t1 s0 (flatBT c0) b0" using d0 c0_def by simp
          have iptc0: "isPTB_str (flatBT c0)"
            using d0' t1neT by (simp add: scb_decomp_def)
          then obtain pc0 where pc0l: "flatBT c0 = flatBP pc0"
            by (auto simp: isPTB_str_def)
          have c0p: "c0 = Trm [pc0]"
          proof -
            have "flatBT c0 = flatBT (Trm [pc0])" using pc0l by simp
            thus ?thesis by (rule m_7_flatBT_inj)
          qed
          have mbc: "(c0, c1) \<in> MarkedB"
          proof -
            have admMm: "adm M m" using mM by (simp add: Marked_def)
            have mjp: "m \<le> jp" using surg_parent_ge[OF mM mono L mlt] jp_def by simp
            have mjm1: "m \<le> Adm M jp" using surg_adm_ge[OF admMm mjp] by simp
            have nest: "(Mark (Pred M) m, Mark (Pred M) (Adm M jp)) \<in> MarkedB"
              using Mark_MarkedB_nest mPred mkdA mjm1 predRT by blast
            thus ?thesis using c0_def c1_def by simp
          qed
          have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
            using mbc unfolding MarkedB_def by auto
          have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
            unfolding sm1_def by (rule someI_ex[OF exsm])
          have dsm': "scb_decomp (Trm [pc0]) (fst sm1) (flatBT (Trm [pc])) (snd sm1)"
            using dsm c0p c1p by simp
          obtain pm where pmf: "flatBP pm = fst sm1 @ flatBT (Trm [pc2]) @ snd sm1"
              and pmd: "scb_decomp (Trm [pm]) (fst sm1) (flatBT (Trm [pc2])) (snd sm1)"
            using scb_replace_principal_BP[OF dsm' iptc2'] by blast
          have markM: "Mark M m = Trm [pm]"
          proof -
            have "flatBT (Trm [pm]) = fst sm1 @ flatBT c2 @ snd sm1"
              using pmf c2p by simp
            thus ?thesis
              using mark_val mbc unflatBT_flat[of "Trm [pm]"] by simp
          qed
          have comp: "scb_decomp ?t1 (s0 @ fst sm1) (flatBT c1) (snd sm1 @ b0)"
            by (rule m_7_2_scb_compose[OF _ _ dsm]) (use c0p d0' in auto)
          have coh: "fst sb1 = s0 @ fst sm1 \<and> snd sb1 = snd sm1 @ b0"
            by (rule m_7_2_scb_unique_sb[OF dsome comp t1neT])
          have t'flat: "flatBT t' = s0 @ flatBT (Trm [pm]) @ b0"
            using t'f coh pmf c2p by simp
          have b0rp: "\<forall>x \<in> set b0. x = RP" using d0' by (simp add: scb_decomp_def)
          have sm_sub: "set (fst sm1) \<subseteq> set (flatBT c0)"
              and bm_sub: "set (snd sm1) \<subseteq> set (flatBT c0)"
            using dsm by (auto simp: scb_decomp_def)
          have mmdf: "dfree_BT (Trm [pm])"
          proof -
            have "\<And>v'. Dsym v' \<in> set (flatBT (Trm [pm])) \<Longrightarrow> v' \<noteq> \<infinity>"
            proof -
              fix v' assume "Dsym v' \<in> set (flatBT (Trm [pm]))"
              hence "Dsym v' \<in> set (flatBT c0) \<or> Dsym v' \<in> set (flatBT c2)"
                using pmf c2p sm_sub bm_sub by auto
              thus "v' \<noteq> \<infinity>" using c0df c2df dfree_flat_BT by blast
            qed
            thus ?thesis using dfree_flat_BT by blast
          qed
          have iptm: "isPTB_str (flatBT (Trm [pm]))"
            using mmdf by (auto simp: isPTB_str_def)
          have "scb_decomp t' s0 (flatBT (Trm [pm])) b0"
            unfolding scb_decomp_def using t'flat iptm b0rp by simp
          hence "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
            using transM markM by simp
          thus ?thesis using d0 by blast
        qed
      next
        case nmono: False
        have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
        have cut: "0 < Pcut M \<and> Pcut M \<le> ?j1" using Pcut_le[OF L] by simp
        let ?A = "take (Pcut M) M"
        let ?PJ = "drop (Pcut M) M"
        have ARTS: "?A \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF MR muM])
        have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF MT muM])
        have Pne: "P M \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
        have PJRT: "?PJ \<in> RT_PS"
          using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
        have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
        have LPJ: "Lng ?PJ = Lng M - Pcut M" by simp
        have LPJlt: "Lng ?PJ < Lng M" using LPJ cut L by linarith
        have cmle: "Pcut M \<le> m" by (rule multi_Marked_last_component(1)[OF MT muM mM])
        have mPJ: "(?PJ, m - Pcut M) \<in> Marked"
          by (rule multi_Marked_last_component(2)[OF MT muM mM])
        have PJj1: "Pcut M < ?j1" using mlt cmle by linarith
        have LPJg1: "1 < Lng ?PJ" using LPJ PJj1 cut L by linarith
        have notPJ00: "?PJ \<noteq> [(0,0)]"
        proof
          assume "?PJ = [(0,0)]"
          hence "Lng ?PJ = 1" by simp
          thus False using LPJg1 by simp
        qed
        have mPJlt: "m - Pcut M < Lng ?PJ - 1" using mlt cmle LPJ cut by linarith
        \<comment> \<open>\<open>PJ\<close> is mono (a non-zero \<open>P\<close>-component)\<close>
        have PJmono: "monoT ?PJ"
        proof -
          have "?PJ \<in> set (P M)" using PJeq Pne J1lt nth_mem by metis
          hence "zeroT ?PJ \<or> monoT ?PJ" using m_6_2_P_components_1[OF MT] by blast
          moreover have "\<not> zeroT ?PJ" using LPJg1 by (auto simp: zeroT_def)
          ultimately show ?thesis by blast
        qed
        have c1f: "(M \<notin> RT_PS) = False" using MR by simp
        have c2f: "(?j1 = 0) = False" using L by simp
        have c3f: "monoT M = False" using nmono by simp
        have Aeq2: "seg M 0 (?j1 - Lng ?PJ + 1 - 1) = ?A"
        proof -
          have "?j1 - Lng ?PJ + 1 - 1 = Pcut M - 1" using LPJ cut by linarith
          moreover have "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
            by (rule seg_0_eq_take) (use cut L in linarith)
          moreover have "Suc (Pcut M - 1) = Pcut M" using cut by simp
          ultimately show ?thesis by simp
        qed
        have transM: "Trans M = Trans ?A +\<^sub>B Trans ?PJ"
        proof -
          have raw: "Trans M =
              (if P M ! (Lng (P M) - 1) = [(0, 0)]
               then Trans (seg M 0 (?j1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1)) +\<^sub>B Dpt 0 0\<^sub>B
               else Trans (seg M 0 (?j1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                      +\<^sub>B Trans (P M ! (Lng (P M) - 1)))"
            by (subst Trans.psimps[OF domT]) (simp only: c1f c2f c3f if_False Let_def)
          have "Trans M = (if ?PJ = [(0, 0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B
                           else Trans ?A +\<^sub>B Trans ?PJ)"
            unfolding raw PJeq Aeq2 ..
          thus ?thesis using notPJ00 by simp
        qed
        have markM_eval: "Mark M m = Mark ?PJ (m - Pcut M)"
        proof -
          have meq2: "m - (?j1 - Lng ?PJ + 1) = m - Pcut M"
          proof -
            have "?j1 - Lng ?PJ + 1 = Pcut M" using LPJ cut by linarith
            thus ?thesis by simp
          qed
          have raw: "Mark M m =
              (if P M ! (Lng (P M) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
               else Mark (P M ! (Lng (P M) - 1)) (m - (?j1 - Lng (P M ! (Lng (P M) - 1)) + 1)))"
            by (subst Mark.psimps[OF domK]) (simp only: c1f c2f c3f if_False Let_def)
          have "Mark M m = (if ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Mark ?PJ (m - Pcut M))"
            unfolding raw PJeq meq2 ..
          thus ?thesis using notPJ00 by simp
        qed
        from less.IH[OF LPJlt] PJRT mPJ mPJlt
        obtain s0 b0 where
          dP_J: "scb_decomp (Trans (Pred ?PJ)) s0 (flatBT (Mark (Pred ?PJ) (m - Pcut M))) b0"
          and dM_J: "scb_decomp (Trans ?PJ) s0 (flatBT (Mark ?PJ (m - Pcut M))) b0"
          by blast
        have tPJne: "Trans ?PJ \<noteq> 0\<^sub>B"
        proof -
          have "\<not> zeroT ?PJ" using LPJg1 by (auto simp: zeroT_def)
          thus ?thesis using m_7_3_Trans_zeroT[OF PJRT] by blast
        qed
        have X1_PJ: "length (untrm (Trans ?PJ)) = 1"
        proof -
          obtain p where "Trans ?PJ = Trm [p]"
            using Trans_PT_single PJRT PJmono tPJne by blast
          thus ?thesis by simp
        qed
        show ?thesis
        proof (cases "Trans ?A = 0\<^sub>B")
          case TA0: True
          have transM': "Trans M = Trans ?PJ" using transM TA0 addBT_zero_left by simp
          have transPM: "Trans (Pred M)
                = Trans ?A +\<^sub>B (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Trans (Pred ?PJ))"
            by (rule Trans_Pred_multi_last[OF MR muM LPJg1])
          have markPM: "Mark (Pred M) m
                = (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Mark (Pred ?PJ) (m - Pcut M))"
            by (rule Mark_Pred_multi_last[OF MR muM LPJg1])
          show ?thesis
          proof (cases "Pred ?PJ = [(0,0)]")
            case PP0: True
            have tPP0: "Trans (Pred ?PJ) = 0\<^sub>B" using PP0 Trans_singleton[of 0] by simp
            have kPP0: "Mark (Pred ?PJ) (m - Pcut M) = 0\<^sub>B"
            proof -
              have "Lng (Pred ?PJ) = 1" using PP0 by simp
              hence "Lng ?PJ = 2" using LPJg1 by (simp add: Pred_def)
              hence "m - Pcut M = 0" using mPJlt by simp
              thus ?thesis using PP0 Mark_singleton[of 0] by simp
            qed
            have markPM0: "Mark (Pred M) m = Dpt 0 0\<^sub>B" using markPM PP0 by simp
            have transPM0: "Trans (Pred M) = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transPM PP0 by simp
            have transPM0': "Trans (Pred M) = Dpt 0 0\<^sub>B" using transPM0 TA0 addBT_zero_left by simp
            have iptD0: "isPTB_str (flatBT (Dpt 0 0\<^sub>B))"
              by (rule isPTB_str_Dpt) (simp_all add: zero_enat_def)
            have dP: "scb_decomp (Trans (Pred M)) [] (flatBT (Mark (Pred M) m)) []"
              using transPM0' markPM0 iptD0 by (simp add: scb_decomp_def)
            have s0b0: "s0 = [] \<and> b0 = []"
            proof -
              have "flatBT (Trans (Pred ?PJ)) = s0 @ flatBT (Mark (Pred ?PJ) (m - Pcut M)) @ b0"
                using dP_J by (simp add: scb_decomp_def)
              hence "[Zsym] = s0 @ [Zsym] @ b0" using tPP0 kPP0 by simp
              thus ?thesis by (cases s0) auto
            qed
            have dM: "scb_decomp (Trans M) [] (flatBT (Mark M m)) []"
              using dM_J s0b0 transM' markM_eval by simp
            show ?thesis using dP dM by blast
          next
            case PPne: False
            have predPJRT: "Pred ?PJ \<in> RT_PS" by (rule Pred_RT_PS[OF PJRT])
            have transM'': "Trans M = Trans ?PJ" using transM TA0 addBT_zero_left by simp
            have transPM': "Trans (Pred M) = Trans (Pred ?PJ)"
              using transPM PPne TA0 addBT_zero_left by simp
            have markPM': "Mark (Pred M) m = Mark (Pred ?PJ) (m - Pcut M)"
              using markPM PPne by simp
            have dP: "scb_decomp (Trans (Pred M)) s0 (flatBT (Mark (Pred M) m)) b0"
              using dP_J transPM' markPM' by simp
            have dM: "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
              using dM_J transM'' markM_eval by simp
            show ?thesis using dP dM by blast
          qed
        next
          case TAne: False
          have Yne: "untrm (Trans ?A) \<noteq> []" using TAne by (cases "Trans ?A") auto
          have transPM: "Trans (Pred M)
                = Trans ?A +\<^sub>B (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Trans (Pred ?PJ))"
            by (rule Trans_Pred_multi_last[OF MR muM LPJg1])
          have markPM: "Mark (Pred M) m
                = (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Mark (Pred ?PJ) (m - Pcut M))"
            by (rule Mark_Pred_multi_last[OF MR muM LPJg1])
          have liftM: "scb_decomp (Trans ?A +\<^sub>B Trans ?PJ) (liftS (Trans ?A) s0)
                          (flatBT (Mark ?PJ (m - Pcut M))) (b0 @ [RP])"
            by (rule scb_addBT_left[OF dM_J X1_PJ Yne])
          have dM: "scb_decomp (Trans M) (liftS (Trans ?A) s0) (flatBT (Mark M m)) (b0 @ [RP])"
            using liftM transM markM_eval by simp
          show ?thesis
          proof (cases "Pred ?PJ = [(0,0)]")
            case PP0: True
            have kPP0: "Mark (Pred ?PJ) (m - Pcut M) = 0\<^sub>B"
            proof -
              have "Lng (Pred ?PJ) = 1" using PP0 by simp
              hence "Lng ?PJ = 2" using LPJg1 by (simp add: Pred_def)
              hence "m - Pcut M = 0" using mPJlt by simp
              thus ?thesis using PP0 Mark_singleton[of 0] by simp
            qed
            have tPP0: "Trans (Pred ?PJ) = 0\<^sub>B" using PP0 Trans_singleton[of 0] by simp
            have s0b0: "s0 = [] \<and> b0 = []"
            proof -
              have "flatBT (Trans (Pred ?PJ)) = s0 @ flatBT (Mark (Pred ?PJ) (m - Pcut M)) @ b0"
                using dP_J by (simp add: scb_decomp_def)
              hence "[Zsym] = s0 @ [Zsym] @ b0" using tPP0 kPP0 by simp
              thus ?thesis by (cases s0) auto
            qed
            have markPM0: "Mark (Pred M) m = Dpt 0 0\<^sub>B" using markPM PP0 by simp
            have transPM0: "Trans (Pred M) = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transPM PP0 by simp
            have iptD0: "isPTB_str (flatBT (Dpt 0 0\<^sub>B))"
              by (rule isPTB_str_Dpt) (simp_all add: zero_enat_def)
            have selfD0: "scb_decomp (Dpt 0 0\<^sub>B) [] (flatBT (Dpt 0 0\<^sub>B)) []"
              using iptD0 by (rule scb_decomp_self)
            have X1D0: "length (untrm (Dpt 0 0\<^sub>B)) = 1" by simp
            have liftP: "scb_decomp (Trans ?A +\<^sub>B Dpt 0 0\<^sub>B) (liftS (Trans ?A) [])
                            (flatBT (Dpt 0 0\<^sub>B)) ([] @ [RP])"
              by (rule scb_addBT_left[OF selfD0 X1D0 Yne])
            have dP: "scb_decomp (Trans (Pred M)) (liftS (Trans ?A) [])
                          (flatBT (Mark (Pred M) m)) ([] @ [RP])"
              using liftP transPM0 markPM0 by simp
            have dMm: "scb_decomp (Trans M) (liftS (Trans ?A) [])
                          (flatBT (Mark M m)) ([] @ [RP])"
              using dM s0b0 by simp
            show ?thesis using dP dMm by blast
          next
            case PPne: False
            have predPJRT: "Pred ?PJ \<in> RT_PS" by (rule Pred_RT_PS[OF PJRT])
            have predPJT: "Pred ?PJ \<in> T_PS" using predPJRT by (simp add: RT_PS_def)
            have LPP: "0 < Lng (Pred ?PJ)" using LPJg1 by (simp add: Pred_def)
            have tPP_ne: "Trans (Pred ?PJ) \<noteq> 0\<^sub>B"
            proof -
              have "\<not> zeroT (Pred ?PJ)"
              proof
                assume z: "zeroT (Pred ?PJ)"
                hence "Lng (Pred ?PJ) = 1" by (simp add: zeroT_def)
                obtain v where Pv: "Pred ?PJ = [(v,v)]"
                  using m_6_6_oneColumn[OF predPJT] predPJRT \<open>Lng (Pred ?PJ) = 1\<close> by auto
                have "v = 0" using z Pv by (simp add: zeroT_def entry_def)
                thus False using PPne Pv by simp
              qed
              thus ?thesis using m_7_3_Trans_zeroT[OF predPJRT] by blast
            qed
            \<comment> \<open>\<open>Pred PJ\<close> is mono or single-column; its \<open>Trans\<close> is single-principal\<close>
            have X1_PPJ: "length (untrm (Trans (Pred ?PJ))) = 1"
            proof (cases "Lng (Pred ?PJ) = 1")
              case True
              obtain v where Pv: "Pred ?PJ = [(v,v)]"
                using m_6_6_oneColumn[OF predPJT] predPJRT True by auto
              have tv: "Trans (Pred ?PJ) = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
                using Pv Trans_singleton[of v] by simp
              hence "v \<noteq> 0" using tPP_ne by (cases "v = 0") auto
              hence "Trans (Pred ?PJ) = Dpt (enat v) 0\<^sub>B" using tv by simp
              thus ?thesis by simp
            next
              case False
              have LPP1: "1 < Lng (Pred ?PJ)" using LPP False by linarith
              have LPJ3: "1 < Lng ?PJ - 1"
                using LPP1 LPJg1 by (simp add: Pred_def)
              \<comment> \<open>\<open>Pred PJ = butlast PJ = seg PJ 0 (Lng PJ - 2)\<close>, a mono prefix of mono \<open>PJ\<close>\<close>
              have predPJmono: "monoT (Pred ?PJ)"
              proof -
                have PJPT: "?PJ \<in> PT_PS" using PJT PJmono by (simp add: PT_PS_def)
                have j0pos: "0 < Lng ?PJ - 2" using LPJ3 by simp
                have j0lt: "Lng ?PJ - 2 < Lng ?PJ" using LPJg1 by simp
                have mp: "monoT (seg ?PJ 0 (Lng ?PJ - 2))"
                  by (rule m_6_2_mono_prefix[OF PJPT j0pos j0lt])
                have segbl: "seg ?PJ 0 (Lng ?PJ - 2) = butlast ?PJ"
                proof -
                  have suc: "Suc (Lng ?PJ - 2) \<le> Lng ?PJ" using LPJ3 by simp
                  have "seg ?PJ 0 (Lng ?PJ - 2) = take (Suc (Lng ?PJ - 2)) ?PJ"
                    by (rule seg_0_eq_take[OF suc])
                  also have "Suc (Lng ?PJ - 2) = Lng ?PJ - 1" using LPJ3 by simp
                  also have "take (Lng ?PJ - 1) ?PJ = butlast ?PJ"
                    by (simp add: butlast_conv_take)
                  finally show ?thesis .
                qed
                have "Pred ?PJ = butlast ?PJ" using LPJg1 by (simp add: Pred_def)
                thus ?thesis using mp segbl by simp
              qed
              obtain p where "Trans (Pred ?PJ) = Trm [p]"
                using Trans_PT_single predPJRT predPJmono tPP_ne by blast
              thus ?thesis by simp
            qed
            have transPM': "Trans (Pred M) = Trans ?A +\<^sub>B Trans (Pred ?PJ)"
              using transPM PPne by simp
            have markPM': "Mark (Pred M) m = Mark (Pred ?PJ) (m - Pcut M)"
              using markPM PPne by simp
            have liftP: "scb_decomp (Trans ?A +\<^sub>B Trans (Pred ?PJ)) (liftS (Trans ?A) s0)
                            (flatBT (Mark (Pred ?PJ) (m - Pcut M))) (b0 @ [RP])"
              by (rule scb_addBT_left[OF dP_J X1_PPJ Yne])
            have dP: "scb_decomp (Trans (Pred M)) (liftS (Trans ?A) s0)
                          (flatBT (Mark (Pred M) m)) (b0 @ [RP])"
              using liftP transPM' markPM' by simp
            show ?thesis using dP dM by blast
          qed
        qed
      qed
    qed
  qed
  obtain s0 b0 where
    H0: "scb_decomp (Trans (Pred M)) s0 (flatBT (Mark (Pred M) m)) b0"
        "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
    using ex MR mM mlt by blast
  show ?thesis
  proof (rule ex1I[of _ "(s0, b0)"])
    show "scb_decomp (Trans (Pred M)) (fst (s0, b0)) (flatBT (Mark (Pred M) m)) (snd (s0, b0))
        \<and> scb_decomp (Trans M) (fst (s0, b0)) (flatBT (Mark M m)) (snd (s0, b0))"
      using H0 by simp
  next
    fix sb
    assume A: "scb_decomp (Trans (Pred M)) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)
             \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
    have dP_sb: "scb_decomp (Trans (Pred M)) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)"
      using A by simp
    show "sb = (s0, b0)"
    proof (cases "Trans (Pred M) = Trm []")
      case t1z: True
      have knil: "flatBT (Mark (Pred M) m) \<noteq> []"
      proof (cases "Mark (Pred M) m")
        case (Trm xs)
        show ?thesis
        proof (cases xs)
          case Nil thus ?thesis using Trm by simp
        next
          case (Cons a as)
          obtain u t' where "a = DB u t'" by (cases a)
          thus ?thesis using Trm Cons by (cases as) auto
        qed
      qed
      have e: "[Zsym] = (fst sb) @ flatBT (Mark (Pred M) m) @ (snd sb)"
        using dP_sb t1z by (simp add: scb_decomp_def)
      have sb0: "fst sb = [] \<and> snd sb = []"
        using e knil by (cases "fst sb"; cases "snd sb" rule: rev_cases) auto
      have e2: "[Zsym] = s0 @ flatBT (Mark (Pred M) m) @ b0"
        using H0(1) t1z by (simp add: scb_decomp_def)
      have s0b0: "s0 = [] \<and> b0 = []"
        using e2 knil by (cases s0; cases b0 rule: rev_cases) auto
      show ?thesis using sb0 s0b0 by (cases sb) auto
    next
      case t1ne: False
      have "fst sb = s0 \<and> snd sb = b0"
        by (rule m_7_2_scb_unique_sb[OF dP_sb H0(1) t1ne])
      thus ?thesis by (cases sb) auto
    qed
  qed
qed

text \<open>§7.4 系（\<open>Trans\<close> の \<open>Mark\<close> と切片による表示）— content.md 2646.
  Corollary of @{thm [source] m_7_4_Trans_Mark_Pred}: the same scb position
  \<open>(s\<^sub>0,b\<^sub>0)\<close> inserts \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> 0\<close> into \<open>Trans (seg M 0 m)\<close> and \<open>Mark M m\<close>
  into \<open>Trans M\<close>.  Proof by \<open>Lng\<close>-induction collapsing \<open>M\<close> to \<open>Pred M\<close>:
  on the slice \<open>m \<le> Lng M - 2\<close> so \<open>seg M 0 m = seg (Pred M) 0 m\<close>; the base
  \<open>m = Lng (Pred M) - 1\<close> uses @{thm [source] Mark_rightmost1_forward}
  (\<open>Mark (Pred M) m = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> 0\<close>) with \<open>seg M 0 m = Pred M\<close>; the recursive
  step \<open>m < Lng (Pred M) - 1\<close> applies the IH to \<open>Pred M\<close> and aligns positions
  via @{thm [source] m_7_2_scb_unique_sb} on \<open>Trans (Pred M)\<close>.\<close>

lemma m_7_4_Trans_Mark_seg:
  assumes mM0: "(M, m) \<in> Marked" and MR0: "M \<in> RT_PS"
    and mpos0: "0 < m" and mlt0: "m < Lng M - 1"
  shows "\<exists>!sb. scb_decomp (Trans (seg M 0 m))
                  (fst sb) (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) (snd sb)
            \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
proof -
  have ex: "M \<in> RT_PS \<longrightarrow> (\<forall>m. (M, m) \<in> Marked \<longrightarrow> 0 < m \<longrightarrow> m < Lng M - 1 \<longrightarrow>
       (\<exists>s0 b0.
          scb_decomp (Trans (seg M 0 m)) s0 (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) b0
        \<and> scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0))"
  proof (induction M rule: measure_induct_rule[where f=Lng])
    case (less M)
    show ?case
    proof (intro impI allI)
      fix m
      assume MR: "M \<in> RT_PS" and mM: "(M, m) \<in> Marked"
        and mpos: "0 < m" and mlt: "m < Lng M - 1"
      have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
      have L: "1 < Lng M" using mlt mpos by linarith
      \<comment> \<open>collapse to \<open>P = Pred M\<close>; positions and the slice agree\<close>
      define P where "P = Pred M"
      have predRT: "P \<in> RT_PS" using Pred_RT_PS[OF MR] P_def by simp
      have predb: "P = butlast M" using L P_def by (simp add: Pred_def)
      have LP: "Lng P = Lng M - 1" using predb by simp
      have mPred: "(P, m) \<in> Marked" using Marked_Pred[OF MT L mM mlt] P_def by simp
      have mltP: "m \<le> Lng P - 1" using mlt LP by linarith
      \<comment> \<open>the slice agrees: \<open>seg M 0 m = seg P 0 m\<close>\<close>
      have segeq: "seg M 0 m = seg P 0 m"
      proof -
        have sM: "seg M 0 m = take (Suc m) M"
          by (rule seg_0_eq_take) (use mlt L in linarith)
        have sP: "seg P 0 m = take (Suc m) P"
          by (rule seg_0_eq_take) (use mltP LP L in linarith)
        have "take (Suc m) P = take (Suc m) M"
        proof -
          have "P = take (Lng M - 1) M" using predb by (simp add: butlast_conv_take)
          hence "take (Suc m) P = take (min (Suc m) (Lng M - 1)) M" by (simp add: take_take)
          also have "min (Suc m) (Lng M - 1) = Suc m" using mlt by simp
          finally show ?thesis .
        qed
        thus ?thesis using sM sP by simp
      qed
      \<comment> \<open>row-1 entry agrees on the slice\<close>
      have entryeq: "entry P 1 m = entry M 1 m"
      proof -
        have "m < length (butlast M)" using mlt by simp
        thus ?thesis using predb by (simp add: entry_def nth_butlast)
      qed
      \<comment> \<open>the \<open>Pred\<close>-corollary supplies the position \<open>(s0,b0)\<close>\<close>
      have exP: "\<exists>sb. scb_decomp (Trans (Pred M)) (fst sb)
                          (flatBT (Mark (Pred M) m)) (snd sb)
                      \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
        using m_7_4_Trans_Mark_Pred[OF mM MR mlt] by (rule ex1_implies_ex)
      obtain sbP where
        HP: "scb_decomp (Trans P) (fst sbP) (flatBT (Mark P m)) (snd sbP)"
            "scb_decomp (Trans M) (fst sbP) (flatBT (Mark M m)) (snd sbP)"
        using exP P_def by auto
      define s0 where "s0 = fst sbP"
      define b0 where "b0 = snd sbP"
      have H0: "scb_decomp (Trans P) s0 (flatBT (Mark P m)) b0"
               "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
        using HP s0_def b0_def by simp_all
      have dM: "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0" using H0(2) .
      \<comment> \<open>now match the slice scb at the same position\<close>
      have dseg: "scb_decomp (Trans (seg M 0 m)) s0
                     (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) b0"
      proof (cases "m = Lng P - 1")
        case base: True
        \<comment> \<open>\<open>m\<close> is the last index of \<open>P\<close>: \<open>Mark P m = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> 0\<close> and \<open>seg M 0 m = P\<close>\<close>
        have nzP: "\<not> zeroT P"
        proof
          assume "zeroT P"
          hence "Lng P = 1" by (simp add: zeroT_def)
          thus False using base mpos by simp
        qed
        have markP: "Mark P m = Dpt (enat (entry P 1 m)) 0\<^sub>B"
          using Mark_rightmost1_forward[OF predRT nzP] mPred base by simp
        have markP': "Mark P m = Dpt (enat (entry M 1 m)) 0\<^sub>B"
          using markP entryeq by simp
        have segP: "seg M 0 m = P"
        proof -
          have "seg P 0 m = take (Suc m) P"
            by (rule seg_0_eq_take) (use mltP LP L in linarith)
          also have "Suc m = Lng P" using base LP L by linarith
          also have "take (Lng P) P = P" by simp
          finally show ?thesis using segeq by simp
        qed
        show ?thesis using H0(1) markP' segP by simp
      next
        case rec: False
        have mltP': "m < Lng P - 1" using mltP rec by simp
        have LPlt: "Lng P < Lng M" using LP L by simp
        \<comment> \<open>IH on the smaller \<open>P\<close>\<close>
        from less.IH[OF LPlt] predRT mPred mpos mltP'
        obtain s0' b0' where
          G0: "scb_decomp (Trans (seg P 0 m)) s0'
                  (flatBT (Dpt (enat (entry P 1 m)) 0\<^sub>B)) b0'"
              "scb_decomp (Trans P) s0' (flatBT (Mark P m)) b0'"
          by blast
        \<comment> \<open>\<open>Trans P \<noteq> Trm []\<close>: \<open>m < Lng P - 1\<close> forces \<open>Lng P > 1\<close>, so \<open>\<not> zeroT P\<close>\<close>
        have nzP: "\<not> zeroT P"
        proof
          assume "zeroT P"
          hence "Lng P = 1" by (simp add: zeroT_def)
          thus False using mltP' by simp
        qed
        have tPne: "Trans P \<noteq> Trm []"
          using m_7_3_Trans_zeroT[OF predRT] nzP by auto
        have coh: "s0' = s0 \<and> b0' = b0"
          by (rule m_7_2_scb_unique_sb[OF G0(2) H0(1) tPne])
        have "scb_decomp (Trans (seg P 0 m)) s0
                  (flatBT (Dpt (enat (entry P 1 m)) 0\<^sub>B)) b0"
          using G0(1) coh by simp
        thus ?thesis using segeq entryeq by simp
      qed
      show "\<exists>s0 b0. scb_decomp (Trans (seg M 0 m)) s0
                       (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) b0
                  \<and> scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
        using dseg dM by blast
    qed
  qed
  obtain s0 b0 where
    H: "scb_decomp (Trans (seg M 0 m)) s0 (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) b0"
       "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
    using ex MR0 mM0 mpos0 mlt0 by blast
  \<comment> \<open>uniqueness via \<open>Trans M \<noteq> Trm []\<close>\<close>
  have MT0: "M \<in> T_PS" using MR0 by (simp add: RT_PS_def)
  have L0: "1 < Lng M" using mlt0 mpos0 by linarith
  have nzM: "\<not> zeroT M" using L0 by (auto simp: zeroT_def)
  have tMne: "Trans M \<noteq> Trm []"
    using m_7_3_Trans_zeroT[OF MR0] nzM by auto
  show ?thesis
  proof (rule ex1I[of _ "(s0, b0)"])
    show "scb_decomp (Trans (seg M 0 m)) (fst (s0, b0))
              (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) (snd (s0, b0))
        \<and> scb_decomp (Trans M) (fst (s0, b0)) (flatBT (Mark M m)) (snd (s0, b0))"
      using H by simp
  next
    fix sb
    assume A: "scb_decomp (Trans (seg M 0 m)) (fst sb)
                  (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) (snd sb)
             \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
    have dM_sb: "scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
      using A by simp
    have "fst sb = s0 \<and> snd sb = b0"
      by (rule m_7_2_scb_unique_sb[OF dM_sb H(2) tMne])
    thus "sb = (s0, b0)" by (cases sb) auto
  qed
qed


section \<open>§7.4 系（\<open>RightNodes\<close> と \<open>Mark\<close> の関係） — m_7_4_RightNodes_Mark\<close>

text \<open>Helper: an iterated \<open>Pred\<close> on a reduced sequence stays reduced
  (@{thm [source] Pred_RT_PS} iterated).\<close>

lemma Pred_pow_RT_PS:
  assumes "M \<in> RT_PS"
  shows "(Pred ^^ k) M \<in> RT_PS"
proof (induction k)
  case 0
  thus ?case using assms by simp
next
  case (Suc k)
  have step: "(Pred ^^ Suc k) M = Pred ((Pred ^^ k) M)"
    by (simp only: funpow.simps o_apply)
  show ?case unfolding step by (rule Pred_RT_PS[OF Suc.IH])
qed

text \<open>Helper: a trunk-anchored initial slice \<open>seg M 0 m\<close> (\<open>m \<le> Lng M - 1\<close>) of a
  reduced \<open>M\<close> is reduced.  This is @{thm [source] herd_6_6_reduced_slice} without
  its \<open>TrMax M \<le> m\<close> hypothesis (empirically unneeded): \<open>seg M 0 m = (Pred ^^ k) M\<close>
  for \<open>k = Lng M - 1 - m\<close> (@{thm [source] herd_Pred_pow_take}), and iterated
  \<open>Pred\<close> preserves reducedness (@{thm [source] Pred_pow_RT_PS}).\<close>

lemma seg_0_RT_PS:
  assumes M: "M \<in> RT_PS" and hi: "m \<le> Lng M - 1"
  shows "seg M 0 m \<in> RT_PS"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  let ?k = "Lng M - 1 - m"
  have kLt: "?k < Lng M" using LMpos by linarith
  have LmkE: "Lng M - ?k = Suc m" using hi LMpos by linarith
  have segtake: "seg M 0 m = take (Suc m) M"
    by (rule seg_0_eq_take) (use hi LMpos in linarith)
  have segpow: "seg M 0 m = (Pred ^^ ?k) M"
  proof -
    have "(Pred ^^ ?k) M = take (Lng M - ?k) M" by (rule herd_Pred_pow_take[OF kLt])
    also have "\<dots> = take (Suc m) M" using LmkE by simp
    finally show ?thesis using segtake by simp
  qed
  show ?thesis using segpow Pred_pow_RT_PS[OF M, of ?k] by simp
qed

text \<open>Helper: the §7.2 \<open>RightNodes\<close>-subexpression engine
  (@{thm [source] m_7_2_RightNodes_subexpr}) without its \<open>t \<in> PT\<^bsub>B\<^esub>\<close>
  (\<open>\<exists>p. t = Trm [p]\<close>) hypothesis.  The principality of the substituted body \<open>t\<close>
  is never used in the engine's proof (only \<open>t \<in> T\<^bsub>B\<^esub>\<close> via the spine
  substitution bricks @{thm [source] rnsub_flat_main},
  @{thm [source] rnsub_RightNodes_spineSub}, @{thm [source] rnsub_RightNodes_t0_lastv}),
  but it is needed here because the body of \<open>Mark M m\<close> is in general a multi
  term (empirically 47/140 marked cases), not principal.\<close>

lemma m_7_4_RightNodes_subexpr_gen:
  fixes v :: nat
  assumes tTB: "t \<in> T_B"
    and bRP: "\<forall>x \<in> set b. x = RP"
    and t0TB: "t\<^sub>0 \<in> T_B" and flat0: "flatBT t\<^sub>0 = s @ flatBT (Dpt (enat v) 0\<^sub>B) @ b"
  shows "\<exists>!aa. RightNodes (spineSub t\<^sub>0 t) = fst aa @ [v] @ snd aa
            \<and> RightNodes t\<^sub>0 = fst aa @ [v]
            \<and> RightNodes (Dpt (enat v) t) = [v] @ snd aa"
proof -
  have Hf: "flatBT t\<^sub>0 = s @ Dsym (enat v) # Zsym # b"
    using flat0 by simp
  have t0_ne: "t\<^sub>0 \<noteq> Trm []"
  proof
    assume "t\<^sub>0 = Trm []"
    hence "flatBT t\<^sub>0 = [Zsym]" by simp
    thus False using flat0 by (cases s) auto
  qed
  have rn1: "RightNodes (spineSub t\<^sub>0 t) = RightNodes t\<^sub>0 @ RightNodes t"
    using rnsub_RightNodes_spineSub[OF t0_ne] by blast
  have rn0_last: "\<exists>a0. RightNodes t\<^sub>0 = a0 @ [v]"
    using rnsub_RightNodes_t0_lastv Hf bRP t0TB by blast
  then obtain a0 where rn0: "RightNodes t\<^sub>0 = a0 @ [v]" by blast
  define a1 where "a1 = RightNodes t"
  have rnDvt: "RightNodes (Dpt (enat v) t) = [v] @ a1"
    unfolding a1_def by simp
  have rnt1: "RightNodes (spineSub t\<^sub>0 t) = a0 @ [v] @ a1"
    using rn1 rn0 unfolding a1_def by simp
  show "\<exists>!aa. RightNodes (spineSub t\<^sub>0 t) = fst aa @ [v] @ snd aa
            \<and> RightNodes t\<^sub>0 = fst aa @ [v]
            \<and> RightNodes (Dpt (enat v) t) = [v] @ snd aa"
  proof (rule ex1I[of _ "(a0, a1)"])
    show "RightNodes (spineSub t\<^sub>0 t) = fst (a0,a1) @ [v] @ snd (a0,a1)
        \<and> RightNodes t\<^sub>0 = fst (a0,a1) @ [v]
        \<and> RightNodes (Dpt (enat v) t) = [v] @ snd (a0,a1)"
      using rnt1 rn0 rnDvt by simp
  next
    fix aa
    assume "RightNodes (spineSub t\<^sub>0 t) = fst aa @ [v] @ snd aa
          \<and> RightNodes t\<^sub>0 = fst aa @ [v]
          \<and> RightNodes (Dpt (enat v) t) = [v] @ snd aa"
    hence f0: "RightNodes t\<^sub>0 = fst aa @ [v]"
      and fD: "RightNodes (Dpt (enat v) t) = [v] @ snd aa" by auto
    have "fst aa = a0" using f0 rn0 by simp
    moreover have "snd aa = a1" using fD rnDvt by simp
    ultimately show "aa = (a0, a1)" by (cases aa) simp
  qed
qed

text \<open>系（\<open>RightNodes\<close> と \<open>Mark\<close> の関係） (§7.4, content.md 2691): for a marked
  reduced \<open>(M,m)\<close> with \<open>0 < m < Lng M - 1\<close>, the marked value \<open>Mark M m\<close> sits as a
  common subexpression splitting \<open>RightNodes (Trans M)\<close> at the row-1 entry
  \<open>M\<^bsub>1,m\<^esub>\<close>.  Article: immediate from @{thm [source] m_7_4_Trans_Mark_seg} (the
  common scb position), @{thm [source] Mark_leftend_form} (left end of \<open>Mark M m\<close>
  is \<open>D\<^bsub>M\<^bsub>1,m\<^esub>\<^esub>\<close>), and the \<open>RightNodes\<close>-subexpression engine
  (@{thm [source] m_7_4_RightNodes_subexpr_gen}).\<close>

lemma m_7_4_RightNodes_Mark:
  assumes "(M, m) \<in> Marked" and "M \<in> RT_PS" and "0 < m" and "m < Lng M - 1"
  shows "\<exists>a0 a1. RightNodes (Trans M) = a0 @ [entry M 1 m] @ a1
              \<and> RightNodes (Trans (seg M 0 m)) = a0 @ [entry M 1 m]
              \<and> RightNodes (Mark M m) = [entry M 1 m] @ a1"
proof -
  let ?v = "entry M 1 m"
  have MT: "M \<in> T_PS" using assms(2) by (simp add: RT_PS_def)
  have L0: "1 < Lng M" using assms(3) assms(4) by linarith
  \<comment> \<open>the common scb position \<open>(s,b)\<close> from \<open>m_7_4_Trans_Mark_seg\<close>\<close>
  have exSB: "\<exists>sb. scb_decomp (Trans (seg M 0 m)) (fst sb)
                  (flatBT (Dpt (enat ?v) 0\<^sub>B)) (snd sb)
              \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
    using m_7_4_Trans_Mark_seg[OF assms(1) assms(2) assms(3) assms(4)]
    by (rule ex1_implies_ex)
  obtain sb where
    SB: "scb_decomp (Trans (seg M 0 m)) (fst sb)
            (flatBT (Dpt (enat ?v) 0\<^sub>B)) (snd sb)"
        "scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
    using exSB by blast
  define s where "s = fst sb"
  define b where "b = snd sb"
  have Dseg: "scb_decomp (Trans (seg M 0 m)) s (flatBT (Dpt (enat ?v) 0\<^sub>B)) b"
    using SB(1) s_def b_def by simp
  have DM: "scb_decomp (Trans M) s (flatBT (Mark M m)) b"
    using SB(2) s_def b_def by simp
  have flat0: "flatBT (Trans (seg M 0 m)) = s @ flatBT (Dpt (enat ?v) 0\<^sub>B) @ b"
    using Dseg by (simp add: scb_decomp_def)
  have bRP: "\<forall>x \<in> set b. x = RP"
    using Dseg by (simp add: scb_decomp_def)
  have flatM: "flatBT (Trans M) = s @ flatBT (Mark M m) @ b"
    using DM by (simp add: scb_decomp_def)
  \<comment> \<open>\<open>Trans M \<noteq> Trm []\<close> (else its flat would be \<open>[Zsym]\<close>, no \<open>Dsym\<close>)\<close>
  have nzM: "\<not> zeroT M" using L0 by (auto simp: zeroT_def)
  have tMne: "Trans M \<noteq> Trm []"
    using m_7_3_Trans_zeroT[OF assms(2)] nzM by auto
  \<comment> \<open>so the scb middle \<open>flatBT (Mark M m)\<close> is a principal-term string\<close>
  have iptM: "isPTB_str (flatBT (Mark M m))"
    using DM tMne by (simp add: scb_decomp_def)
  \<comment> \<open>hence \<open>Mark M m \<noteq> 0\<^sub>B\<close>: its flat is not \<open>[Zsym]\<close>\<close>
  have markNZ: "Mark M m \<noteq> 0\<^sub>B"
  proof
    assume z: "Mark M m = 0\<^sub>B"
    have "isPTB_str [Zsym]" using iptM z by simp
    then obtain p where "flatBP p = [Zsym]" unfolding isPTB_str_def by auto
    thus False by (cases p) simp
  qed
  \<comment> \<open>left end of \<open>Mark M m\<close> is \<open>D\<^bsub>v\<^esub>\<close>: \<open>Mark M m = Dpt (enat v) t'\<close>\<close>
  obtain t' where markform: "Mark M m = Dpt (enat ?v) t'"
    using Mark_leftend_form assms(1) assms(2) markNZ by blast
  have markeq: "Dpt (enat ?v) t' = Mark M m" using markform by simp
  \<comment> \<open>body \<open>t' \<in> T\<^bsub>B\<^esub>\<close> (from \<open>Mark M m \<in> T\<^bsub>B\<^esub>\<close>)\<close>
  have markTB: "Mark M m \<in> T_B"
    by (rule m_7_3_Mark_in_T_B[OF assms(2) assms(1)])
  have t'TB: "t' \<in> T_B"
    using markTB markform by (simp add: T_B_def)
  \<comment> \<open>\<open>Trans (seg M 0 m) \<in> T\<^bsub>B\<^esub>\<close>: the slice is reduced\<close>
  have segRT: "seg M 0 m \<in> RT_PS"
    by (rule seg_0_RT_PS[OF assms(2)]) (use assms(4) in linarith)
  have segTB: "Trans (seg M 0 m) \<in> T_B"
    by (rule m_7_3_Trans_in_T_B[OF segRT])
  \<comment> \<open>apply the (principality-free) subexpression engine with \<open>t := t'\<close>\<close>
  have exUA: "\<exists>aa. RightNodes (spineSub (Trans (seg M 0 m)) t') = fst aa @ [?v] @ snd aa
                 \<and> RightNodes (Trans (seg M 0 m)) = fst aa @ [?v]
                 \<and> RightNodes (Dpt (enat ?v) t') = [?v] @ snd aa"
    using m_7_4_RightNodes_subexpr_gen[OF t'TB bRP segTB flat0]
    by (rule ex1_implies_ex)
  obtain aa where
    UA: "RightNodes (spineSub (Trans (seg M 0 m)) t') = fst aa @ [?v] @ snd aa"
        "RightNodes (Trans (seg M 0 m)) = fst aa @ [?v]"
        "RightNodes (Dpt (enat ?v) t') = [?v] @ snd aa"
    using exUA by blast
  define a0 where "a0 = fst aa"
  define a1 where "a1 = snd aa"
  have rnSeg: "RightNodes (Trans (seg M 0 m)) = a0 @ [?v]"
    using UA(2) a0_def by simp
  have rnMark: "RightNodes (Mark M m) = [?v] @ a1"
  proof -
    have "RightNodes (Mark M m) = RightNodes (Dpt (enat ?v) t')"
      using markform by simp
    also have "\<dots> = [?v] @ snd aa" using UA(3) .
    finally show ?thesis using a1_def by simp
  qed
  \<comment> \<open>the substituted term \<open>spineSub (Trans (seg M 0 m)) t'\<close> is \<open>Trans M\<close>,
      by \<open>flatBT\<close> injectivity\<close>
  have flatSub: "flatBT (spineSub (Trans (seg M 0 m)) t')
               = s @ Dsym (enat ?v) # flatBT t' @ b"
  proof -
    have Hf: "flatBT (Trans (seg M 0 m)) = s @ Dsym (enat ?v) # Zsym # b"
      using flat0 by simp
    have "flatBT (spineSub (Trans (seg M 0 m)) t')
            = s @ Dsym (enat ?v) # flatBT t' @ b \<and> spineSub (Trans (seg M 0 m)) t' \<in> T_B"
      using rnsub_flat_main Hf bRP segTB t'TB by blast
    thus ?thesis by simp
  qed
  have flatSub2: "flatBT (spineSub (Trans (seg M 0 m)) t') = flatBT (Trans M)"
  proof -
    have "flatBT (Trans M) = s @ flatBT (Mark M m) @ b" using flatM .
    also have "flatBT (Mark M m) = flatBT (Dpt (enat ?v) t')"
      using markform by simp
    also have "\<dots> = Dsym (enat ?v) # flatBT t'" by simp
    finally have "flatBT (Trans M) = s @ Dsym (enat ?v) # flatBT t' @ b" by simp
    thus ?thesis using flatSub by simp
  qed
  have subEq: "spineSub (Trans (seg M 0 m)) t' = Trans M"
    using flatSub2 by (rule m_7_flatBT_inj)
  have rnTrans: "RightNodes (Trans M) = a0 @ [?v] @ a1"
    using UA(1) subEq a0_def a1_def by simp
  show ?thesis using rnTrans rnSeg rnMark by blast
qed


section \<open>§7.4 命題（\<open>RightNodes\<close> と \<open>RightAnces\<close> の一致） — m_7_4_RightAnces_RightNodes\<close>

text \<open>Step 1: domain totality of \<open>RightAnces\<close> on \<open>RT\<^bsub>PS\<^esub>\<close>, by strong \<open>Lng\<close>
  induction, mirroring @{thm [source] Trans_Mark_dom_RT_PS_aux}.  The recursive
  calls are: \<open>Red M\<close> (guarded \<open>M \<notin> RT_PS\<close>, vacuous here), \<open>seg M 0 jm1\<close>
  (\<open>jm1 = Adm M (parent M 0 (Lng M-1)) < Lng M - 1\<close>), and \<open>PJ = P M ! (Lng (P M)-1)
  = drop (Pcut M) M\<close> on the multi branch.\<close>

lemma RightAnces_dom_RT:
  "M \<in> RT_PS \<longrightarrow> RightAnces_dom M"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (rule impI)
    assume MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    \<comment> \<open>seg discharger: the \<open>seg M 0 jm1\<close> call has smaller \<open>Lng\<close> and stays reduced\<close>
    have segD: "\<not> Lng M - Suc 0 = 0 \<Longrightarrow> monoT M
        \<Longrightarrow> RightAnces_dom (seg M 0 (Adm M (parent M 0 (Lng M - Suc 0))))"
    proof -
      assume j1: "\<not> Lng M - Suc 0 = 0" and mono: "monoT M"
      have L: "1 < Lng M" using j1 by linarith
      let ?j1 = "Lng M - Suc 0"
      have j1eq: "Lng M - Suc 0 = Lng M - 1" by simp
      have hp: "hasParent M 0 (Lng M - 1)"
        by (rule monoT_hasParent0_last[OF MT mono L])
      have parR: "nextR M 0 (parent M 0 ?j1) ?j1"
        using hp unfolding j1eq hasParent_def parent_def by (rule theI')
      have jplt: "parent M 0 ?j1 < ?j1"
        using parR by (simp add: nextR_def nextrel0_def)
      have aLe: "Adm M (parent M 0 ?j1) \<le> parent M 0 ?j1" by (rule adm_Adm_le)
      have alt: "Adm M (parent M 0 ?j1) < ?j1" using aLe jplt by linarith
      have ale1: "Adm M (parent M 0 ?j1) \<le> Lng M - 1" using alt by simp
      have segRT: "seg M 0 (Adm M (parent M 0 ?j1)) \<in> RT_PS"
        by (rule seg_0_RT_PS[OF MR ale1])
      have segtake: "seg M 0 (Adm M (parent M 0 ?j1))
                     = take (Suc (Adm M (parent M 0 ?j1))) M"
        by (rule seg_0_eq_take) (use alt L in linarith)
      have "Suc (Adm M (parent M 0 ?j1)) < Lng M" using alt L by linarith
      hence "Lng (seg M 0 (Adm M (parent M 0 ?j1))) < Lng M"
        using segtake by (simp add: min_def)
      thus "RightAnces_dom (seg M 0 (Adm M (parent M 0 ?j1)))"
        using less.IH segRT by blast
    qed
    \<comment> \<open>multi discharger: the \<open>PJ\<close> call (= last \<open>P\<close>-component = \<open>drop (Pcut M) M\<close>)\<close>
    have multiD: "\<not> Lng M - Suc 0 = 0 \<Longrightarrow> \<not> monoT M
        \<Longrightarrow> RightAnces_dom (P M ! (Lng (P M) - 1))"
    proof -
      assume j1: "\<not> Lng M - Suc 0 = 0" and nm: "\<not> monoT M"
      have L: "1 < Lng M" using j1 by linarith
      have mu: "multiT M"
      proof -
        have "\<not> zeroT M" using L by (simp add: zeroT_def)
        thus ?thesis using nm by (simp add: multiT_def)
      qed
      have nth_last: "P M ! (Lng (P M) - 1) = drop (Pcut M) M"
        by (rule trans_multiT_last_component(1)[OF MT mu])
      have J1lt: "Lng (P M) - 1 < Lng (P M)"
        using P_nonempty[of M] by (cases "P M") auto
      have PJRT: "P M ! (Lng (P M) - 1) \<in> RT_PS"
        using m_6_6_P_reduced[OF MT] MR J1lt by blast
      have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
      have lpj: "Lng (P M ! (Lng (P M) - 1)) = Lng M - Pcut M"
        using nth_last by simp
      have "Lng (P M ! (Lng (P M) - 1)) < Lng M"
        using lpj cut L by linarith
      thus "RightAnces_dom (P M ! (Lng (P M) - 1))"
        using less.IH PJRT by blast
    qed
    have segD2: "\<not> Lng M \<le> Suc 0 \<Longrightarrow> monoT M
        \<Longrightarrow> RightAnces_dom (seg M 0 (Adm M (parent M 0 (Lng M - Suc 0))))"
    proof -
      assume L: "\<not> Lng M \<le> Suc 0" and mono: "monoT M"
      have "Lng M - Suc 0 \<noteq> 0" using L by linarith
      thus "RightAnces_dom (seg M 0 (Adm M (parent M 0 (Lng M - Suc 0))))"
        using segD mono by blast
    qed
    have multiD2: "\<not> Lng M \<le> Suc 0 \<Longrightarrow> \<not> monoT M \<Longrightarrow> multiT M
        \<Longrightarrow> RightAnces_dom (drop (Pcut M) M)"
    proof -
      assume L: "\<not> Lng M \<le> Suc 0" and nm: "\<not> monoT M" and mu: "multiT M"
      have j1: "Lng M - Suc 0 \<noteq> 0" using L by linarith
      have pjeq: "P M ! (Lng (P M) - 1) = drop (Pcut M) M"
        by (rule trans_multiT_last_component(1)[OF MT mu])
      have "RightAnces_dom (P M ! (Lng (P M) - 1))" using multiD nm j1 by blast
      thus "RightAnces_dom (drop (Pcut M) M)" using pjeq by simp
    qed
    have vacD: "\<not> Lng M \<le> Suc 0 \<Longrightarrow> \<not> monoT M \<Longrightarrow> \<not> multiT M \<Longrightarrow> RightAnces_dom M"
    proof -
      assume L: "\<not> Lng M \<le> Suc 0" and nm: "\<not> monoT M" and nmu: "\<not> multiT M"
      have "zeroT M" using nm nmu by (simp add: multiT_def)
      hence "Lng M = 1" by (simp add: zeroT_def)
      thus "RightAnces_dom M" using L by simp
    qed
    show "RightAnces_dom M"
      apply (rule RightAnces.domintros)
      subgoal using MR by simp
      subgoal using segD2 by blast
      subgoal using multiD2 by blast
      subgoal using vacD by blast
      done
  qed
qed

text \<open>probe: shapes of the domintros / psimps\<close>
lemma RA_probe: "True"
proof -
  note RightAnces.domintros
  note RightAnces.psimps[OF RightAnces_dom_RT[rule_format]]
  show ?thesis ..
qed


text \<open>Helper: at the leftmost basepoint \<open>m = 0\<close>, \<open>Mark M 0\<close> coincides with
  \<open>Trans M\<close>.  Strong \<open>Lng\<close>-induction mirroring the \<open>Trans\<close>/\<open>Mark\<close> recursion:
  base \<open>Lng M = 1\<close> identical; \<open>monoT\<close>/\<open>t\<^sub>1 = 0\<close> identical (\<open>m = 0\<close> branch of
  \<open>Mark\<close>); \<open>monoT\<close>/\<open>t\<^sub>1 \<noteq> 0\<close> uses the IH \<open>Mark (Pred M) 0 = Trans (Pred M) = t\<^sub>1\<close>
  so the surgery's replaced component \<open>c\<^sub>0 = Mark (Pred M) 0\<close> equals \<open>t\<^sub>1\<close> and the
  surgery reproduces the \<open>Trans\<close> value at the SAME scb-position \<open>sb\<^sub>1\<close>; the multi
  case is excluded because \<open>(M, 0) \<in> Marked\<close> forces \<open>monoT M\<close> (column \<open>0\<close> would
  not be \<open>\<le>\<^bsub>R\<^esub>\<close> the last column of a multi term).\<close>

lemma ra_Mark0_eq_Trans:
  "(M, 0) \<in> Marked \<longrightarrow> M \<in> RT_PS \<longrightarrow> Mark M 0 = Trans M"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (intro impI)
    assume m0M: "(M, 0) \<in> Marked" and MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
    show "Mark M 0 = Trans M"
    proof (cases "Lng M = 1")
      case True
      have c1: "(M \<notin> RT_PS) = False" using MR by simp
      have c2: "(Lng M - 1 = 0) = True" using True by simp
      have mk: "Mark M 0 = (if (M::pairseq) ! 0 = (0,0) then 0\<^sub>B
                            else Dpt (enat (entry M 1 0)) 0\<^sub>B)"
        by (subst Mark.psimps[OF domK]) (simp only: c1 c2 if_False if_True Let_def)
      have tr: "Trans M = (if (M::pairseq) ! 0 = (0,0) then 0\<^sub>B
                           else Dpt (enat (entry M 1 0)) 0\<^sub>B)"
        by (subst Trans.psimps[OF domT]) (simp only: c1 c2 if_False if_True Let_def)
      show ?thesis using mk tr by simp
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      \<comment> \<open>\<open>(M,0) \<in> Marked\<close> forces \<open>monoT M\<close>\<close>
      have mono: "monoT M"
      proof (rule ccontr)
        assume nm: "\<not> monoT M"
        have nz: "\<not> zeroT M" using L by (simp add: zeroT_def)
        have mu: "multiT M" using nm nz by (simp add: multiT_def)
        have "Pcut M \<le> 0" using multi_Marked_last_component(1)[OF MT mu m0M] .
        moreover have "0 < Pcut M" using Pcut_le[OF L] by simp
        ultimately show False by simp
      qed
      have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
      have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
      have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
      have LPlt: "Lng (Pred M) < Lng M" using predb L by simp
      \<comment> \<open>\<open>(Pred M, 0) \<in> Marked\<close> (column \<open>0\<close> survives \<open>Pred\<close>)\<close>
      have m0P: "(Pred M, 0) \<in> Marked"
        by (rule Marked_Pred[OF MT L m0M]) (use L in linarith)
      let ?j1 = "Lng M - 1"
      let ?bv = "entry M 1 (Lng M - 1)"
      define jp where "jp = parent M 0 (Lng M - 1)"
      define c1 where "c1 = Mark (Pred M) (Adm M jp)"
      define vv where "vv = bpHeadV c1"
      define tt2 where "tt2 = bpHeadT c1"
      define JJ1 where "JJ1 = Lng (PB tt2) - 1"
      define pj where "pj = PB tt2 ! JJ1"
      define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
      define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
      define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
      define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                             then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                             else if transCondVI M
                             then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                             else if tt2 = 0\<^sub>B
                             then Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                             else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                                (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
      show ?thesis
      proof (cases "Trans (Pred M) = 0\<^sub>B")
        case t1z: True
        have mk: "Mark M 0 = Dpt 0 (Dpt (enat ?bv) 0\<^sub>B)"
          using Mark.psimps[OF domK] MR Lgt1 mono t1z
          by (simp add: Let_def)
        have tr: "Trans M = Dpt 0 (Dpt (enat ?bv) 0\<^sub>B)"
          using Trans.psimps[OF domT] MR Lgt1 mono t1z
          by (simp add: Let_def)
        show ?thesis using mk tr by simp
      next
        case t1ne: False
        \<comment> \<open>\<open>Trans M\<close> at the scb-position \<open>sb\<^sub>1\<close> of \<open>c\<^sub>1\<close> in \<open>t\<^sub>1\<close>\<close>
        let ?t1 = "Trans (Pred M)"
        define sb1 where "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
        have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
          using Trans.psimps[OF domT] MR Lgt1 mono t1ne
          unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                    tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                    ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                    c2_def[symmetric] sb1_def[symmetric]
          by simp
        \<comment> \<open>IH: \<open>Mark (Pred M) 0 = Trans (Pred M) = t\<^sub>1\<close>\<close>
        have markPred0: "Mark (Pred M) 0 = ?t1"
          using less.IH[OF LPlt] m0P predRT by simp
        \<comment> \<open>\<open>(t\<^sub>1, c\<^sub>1) \<in> MarkedB\<close> so the SOME decomposition exists\<close>
        have mkdA: "(Pred M, Adm M jp) \<in> Marked"
          using Marked_Pred_Adm[OF MT L hp] jp_def by simp
        have mb1: "(?t1, c1) \<in> MarkedB"
          using Trans_Mark_invariant_aux[of "Pred M"] predRT mkdA
          unfolding c1_def by blast
        \<comment> \<open>evaluate \<open>Mark M 0\<close> (surgery branch, \<open>0 < j\<^sub>1\<close>)\<close>
        have mlt: "(0::nat) < Lng M - 1" using L by linarith
        have mark_val_raw: "Mark M 0 = (if (Mark (Pred M) 0, c1) \<in> MarkedB
              then unflatBT
                     (fst (SOME sb. scb_decomp (Mark (Pred M) 0) (fst sb)
                                      (flatBT c1) (snd sb))
                      @ flatBT c2
                      @ snd (SOME sb. scb_decomp (Mark (Pred M) 0) (fst sb)
                                        (flatBT c1) (snd sb)))
              else Dpt (enat ?bv) 0\<^sub>B)"
          using Mark.psimps[OF domK] MR Lgt1 mono t1ne mlt
          unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                    tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                    ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                    c2_def[symmetric]
          by simp
        have mb0: "(Mark (Pred M) 0, c1) \<in> MarkedB" using markPred0 mb1 by simp
        have someEq: "(SOME sb. scb_decomp (Mark (Pred M) 0) (fst sb)
                                  (flatBT c1) (snd sb))
                    = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
          using markPred0 by simp
        have mark_val: "Mark M 0 = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
          using mark_val_raw mb0 someEq by (simp add: sb1_def)
        show ?thesis using mark_val trans_val by simp
      qed
    qed
  qed
qed


text \<open>Helper: \<open>RightNodes\<close> ignores the left summand of \<open>+\<^sub>B\<close> when the right
  summand is a non-zero term (\<open>RightNodes\<close> depends only on the last principal
  component, and \<open>a +\<^sub>B b = Trm (untrm a @ untrm b)\<close> has the same last
  component as \<open>b\<close>).\<close>

lemma ra_RightNodes_addBT_right:
  assumes "b \<noteq> 0\<^sub>B"
  shows "RightNodes (a +\<^sub>B b) = RightNodes b"
proof -
  obtain as where a: "a = Trm as" by (cases a)
  obtain bs where b: "b = Trm bs" by (cases b)
  have bne: "bs \<noteq> []" using assms b by auto
  have add: "a +\<^sub>B b = Trm (as @ bs)" using a b by simp
  have nemp: "as @ bs \<noteq> []" using bne by simp
  have lasteq: "last (as @ bs) = last bs" using bne by simp
  have "RightNodes (Trm (as @ bs)) = RightNodes (Trm [last (as @ bs)])"
    by (rule rnsub_RightNodes_last[OF nemp])
  also have "\<dots> = RightNodes (Trm [last bs])" using lasteq by simp
  also have "\<dots> = RightNodes (Trm bs)"
    by (rule rnsub_RightNodes_last[OF bne, symmetric])
  finally show ?thesis using add b by simp
qed

text \<open>Helper: \<open>RightNodes\<close> of a \<open>Dpt\<close> head (any enat index).\<close>

lemma ra_RightNodes_Dpt_gen:
  "RightNodes (Dpt w t) = the_enat w # RightNodes t"
  by simp

text \<open>Helper: the tail of \<open>RightNodes (transC2 M)\<close> for a mono, \<open>t\<^sub>1 \<noteq> 0\<close>,
  \<open>j\<^sub>1 > 0\<close> sequence.  Mirrors the four \<open>c\<^sub>2\<close>-branches of @{thm [source]
  transC2_def}; in every branch the last principal component is
  \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<close> (conds I/III/V/VI) or \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub>(\<dots> D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0)\<close>
  (conds II/IV), so \<open>RightNodes\<close> reduces to the RightAnces tail.\<close>

lemma ra_RightNodes_transC2_tail:
  "RightNodes (transC2 M) = the_enat (transV M) #
     (if transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M
      then [entry M 1 (transJ1 M)]
      else [entry M 1 (transJ0 M), entry M 1 (transJ1 M)])"
proof -
  let ?j1 = "transJ1 M"
  let ?jp = "transJ0 M"
  let ?v = "transV M"
  let ?t2 = "transT2 M"
  let ?Dj1 = "Dpt (enat (entry M 1 ?j1)) 0\<^sub>B"
  define J1 where "J1 = Lng (PB ?t2) - 1"
  define pj where "pj = PB ?t2 ! J1"
  define leftDj0 where "leftDj0 = (bpHeadV pj = enat (entry M 1 ?jp))"
  define t3 where "t3 = (if leftDj0 then SigmaB (take J1 (PB ?t2)) else ?t2)"
  define t4 where "t4 = (if leftDj0 then bpHeadT pj else ?t2)"
  have nzDj1: "?Dj1 \<noteq> 0\<^sub>B" by simp
  show ?thesis
  proof (cases "transCondI M \<or> transCondIII M \<or> transCondV M")
    case I135: True
    have c2: "transC2 M = Dpt ?v (?t2 +\<^sub>B ?Dj1)"
      using I135
      by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def)
    have "RightNodes (?t2 +\<^sub>B ?Dj1) = RightNodes ?Dj1"
      by (rule ra_RightNodes_addBT_right[OF nzDj1])
    hence rn: "RightNodes (?t2 +\<^sub>B ?Dj1) = [entry M 1 ?j1]" by simp
    have cond4: "transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M"
      using I135 by blast
    show ?thesis using c2 rn cond4 by simp
  next
    case notI135: False
    show ?thesis
    proof (cases "transCondVI M")
      case VI: True
      have c2: "transC2 M = Dpt ?v ?Dj1"
        using notI135 VI
        by (simp add: transC2_def Let_def transV_def transJ1_def)
      have cond4: "transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M"
        using VI by blast
      show ?thesis using c2 cond4 by simp
    next
      case notVI: False
      show ?thesis
      proof (cases "?t2 = 0\<^sub>B")
        case t2z: True
        have c2: "transC2 M = Dpt ?v (Dpt (enat (entry M 1 ?jp)) ?Dj1)"
          using notI135 notVI t2z
          by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def
                        transJ0_def)
        have notany: "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M)"
          using notI135 notVI by simp
        show ?thesis using c2 notany by simp
      next
        case t2nz: False
        have c2: "transC2 M
                = Dpt ?v (t3 +\<^sub>B Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1))"
          using notI135 notVI t2nz
          by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def
                        transJ0_def J1_def pj_def leftDj0_def t3_def t4_def)
        have nzInner: "Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1) \<noteq> 0\<^sub>B" by simp
        have rnInner: "RightNodes (Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1))
                     = entry M 1 ?jp # RightNodes (t4 +\<^sub>B ?Dj1)" by simp
        have rnt4: "RightNodes (t4 +\<^sub>B ?Dj1) = [entry M 1 ?j1]"
          using ra_RightNodes_addBT_right[OF nzDj1] by simp
        have "RightNodes (t3 +\<^sub>B Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1))
            = RightNodes (Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1))"
          by (rule ra_RightNodes_addBT_right[OF nzInner])
        also have "\<dots> = [entry M 1 ?jp, entry M 1 ?j1]"
          using rnInner rnt4 by simp
        finally have rnRest: "RightNodes (t3 +\<^sub>B Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1))
            = [entry M 1 ?jp, entry M 1 ?j1]" .
        have notany: "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M)"
          using notI135 notVI by simp
        show ?thesis using c2 rnRest notany by simp
      qed
    qed
  qed
qed


text \<open>§7.4 命題（\<open>RightNodes\<close> と \<open>RightAnces\<close> の一致）/ \<open>p_7_4_RightAnces_RightNodes\<close>
  (content.md 2745).  First the \<open>RT\<^bsub>PS\<^esub>\<close>-restricted version by strong
  \<open>Lng\<close>-induction (mirroring the \<open>RightAnces\<close>/\<open>Trans\<close> recursion), then lift to
  \<open>T\<^bsub>PS\<^esub>\<close> via \<open>Red\<close> (both \<open>RightAnces\<close> and \<open>Trans\<close> factor through \<open>Red\<close>).\<close>

lemma ra_RightAnces_RightNodes_RT:
  "M \<in> RT_PS \<longrightarrow> RightAnces M = RightNodes (Trans M)"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (rule impI)
    assume MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    have raM: "RightAnces M =
        (let j1 = Lng M - 1 in
          if j1 = 0 then (if (M::pairseq) ! 0 = (0,0) then [] else [entry M 1 0])
          else if monoT M then
            (if zeroT (Pred M) then [0, entry M 1 j1]
             else let jp = parent M 0 j1;  jm1 = Adm M jp;
                      a = (if zeroT (seg M 0 jm1) then [0] else RightAnces (seg M 0 jm1)) in
                  if transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M
                  then a @ [entry M 1 j1]
                  else a @ [entry M 1 jp, entry M 1 j1])
          else
            (let J1 = Lng (P M) - 1;  PJ = P M ! J1 in
             if PJ = [(0,0)] then [0] else RightAnces PJ))"
      by (subst RightAnces.psimps[OF RightAnces_dom_RT[rule_format, OF MR]])
         (simp only: if_not_P[OF iffD2[OF not_not refl]] MR Let_def, simp add: MR)
    show "RightAnces M = RightNodes (Trans M)"
    proof (cases "Lng M = 1")
      case True
      \<comment> \<open>base: \<open>j\<^sub>1 = 0\<close>\<close>
      have j1z: "Lng M - 1 = 0" using True by simp
      have ra: "RightAnces M = (if (M::pairseq) ! 0 = (0,0) then [] else [entry M 1 0])"
        using raM j1z by (simp add: Let_def)
      have tr: "Trans M = (if (M::pairseq) ! 0 = (0,0) then 0\<^sub>B else Dpt (enat (entry M 1 0)) 0\<^sub>B)"
        using Trans.psimps[OF domT] MR j1z by (simp add: Let_def)
      show ?thesis
      proof (cases "(M::pairseq) ! 0 = (0,0)")
        case True
        have "RightNodes (Trans M) = RightNodes (0\<^sub>B::BT)" using tr True by simp
        thus ?thesis using ra True by simp
      next
        case False
        have "RightNodes (Trans M) = RightNodes (Dpt (enat (entry M 1 0)) 0\<^sub>B)"
          using tr False by simp
        also have "\<dots> = [entry M 1 0]" by simp
        finally show ?thesis using ra False by simp
      qed
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      have j1ne: "Lng M - 1 \<noteq> 0" using L by simp
      let ?j1 = "Lng M - 1"
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        have MP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
        have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L])
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        show ?thesis
        proof (cases "zeroT (Pred M)")
          case predz: True
          \<comment> \<open>\<open>t\<^sub>1 = Trans (Pred M) = 0\<close>; both sides \<open>[0, M\<^bsub>1,j\<^sub>1\<^esub>]\<close>\<close>
          have ra: "RightAnces M = [0, entry M 1 ?j1]"
            using raM j1ne mono predz by (simp add: Let_def)
          have t1z: "Trans (Pred M) = 0\<^sub>B"
            using m_7_3_Trans_zeroT[OF predRT] predz by simp
          have tr: "Trans M = Dpt 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
            using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
          have "RightNodes (Trans M) = the_enat (0::enat) # [entry M 1 ?j1]"
            using tr by simp
          also have "\<dots> = [0, entry M 1 ?j1]" by (simp add: zero_enat_def)
          finally show ?thesis using ra by simp
        next
          case prednz: False
          \<comment> \<open>the main mono branch: \<open>t\<^sub>1 \<noteq> 0\<close>\<close>
          have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B"
            using m_7_3_Trans_zeroT[OF predRT] prednz by blast
          define jp where "jp = parent M 0 ?j1"
          define jm1 where "jm1 = Adm M jp"
          have transJ1eq: "transJ1 M = ?j1" by (simp add: transJ1_def)
          have transJ0eq: "transJ0 M = jp" by (simp add: transJ0_def transJ1_def jp_def)
          have transJm1eq: "transJm1 M = jm1"
            by (simp add: transJm1_def transJ0eq jm1_def)
          have J1pos: "transJ1 M > 0" using L by (simp add: transJ1_def)
          have T1ne: "transT1 M \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
          \<comment> \<open>\<open>Mark M jm1 = c\<^sub>2\<close>, \<open>RightNodes c\<^sub>2 = transV # tail\<close>\<close>
          have markc2: "Mark M jm1 = transC2 M"
            using m_7_3_Mark_rightmost2[OF MR MP J1pos T1ne] transJm1eq by simp
          define tail where
            "tail = (if transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M
                     then [entry M 1 ?j1] else [entry M 1 jp, entry M 1 ?j1])"
          have rnc2: "RightNodes (transC2 M) = the_enat (transV M) # tail"
            using ra_RightNodes_transC2_tail[of M] transJ1eq transJ0eq tail_def by simp
          \<comment> \<open>the RightAnces value (mono, \<open>\<not> zeroT (Pred M)\<close> branch)\<close>
          have raMono: "RightAnces M =
              (if zeroT (seg M 0 jm1) then [0] else RightAnces (seg M 0 jm1)) @ tail"
            using raM j1ne mono prednz
            by (simp add: Let_def jp_def jm1_def tail_def)
          \<comment> \<open>positions: \<open>jm1 \<le> jp < j\<^sub>1\<close>\<close>
          have parR: "nextR M 0 jp ?j1"
            using hp unfolding hasParent_def parent_def jp_def by (rule theI')
          have jplt: "jp < ?j1" using parR by (simp add: nextR_def nextrel0_def)
          have jm1le: "jm1 \<le> jp" using adm_Adm_le jm1_def by simp
          have jm1lt: "jm1 < ?j1" using jm1le jplt by linarith
          have jm1lej1: "jm1 \<le> ?j1" using jm1lt by linarith
          have segRT: "seg M 0 jm1 \<in> RT_PS"
            by (rule seg_0_RT_PS[OF MR jm1lej1])
          have segtake: "seg M 0 jm1 = take (Suc jm1) M"
            by (rule seg_0_eq_take) (use jm1lt L in linarith)
          have segLng: "Lng (seg M 0 jm1) = Suc jm1" using jm1lt L by simp
          have segLnglt: "Lng (seg M 0 jm1) < Lng M" using segLng jm1lt L by linarith
          \<comment> \<open>\<open>entry (seg M 0 jm1) 1 jm1 = entry M 1 jm1\<close>\<close>
          have entseg: "entry (seg M 0 jm1) 1 jm1 = entry M 1 jm1"
            using entry_seg[of jm1 M 0 jm1 1] segLng by simp
          show ?thesis
          proof (cases "zeroT (seg M 0 jm1)")
            case segz: True
            \<comment> \<open>\<open>jm1 = 0\<close>, \<open>entry M 1 0 = 0\<close>, \<open>Trans M = Mark M 0 = c\<^sub>2\<close>\<close>
            have jm1z: "jm1 = 0"
            proof -
              have "Lng (seg M 0 jm1) = 1" using segz by (simp add: zeroT_def)
              thus ?thesis using segLng by simp
            qed
            have e10z: "entry M 1 0 = 0"
            proof -
              have a: "entry (seg M 0 0) 1 0 = 0" using segz jm1z by (simp add: zeroT_def)
              have b: "entry (seg M 0 0) 1 0 = entry M 1 0"
                using entseg jm1z by simp
              show ?thesis using a b by simp
            qed
            \<comment> \<open>\<open>(M, 0) \<in> Marked\<close>, hence \<open>Mark M 0 = Trans M\<close>\<close>
            have leM0: "leR M 0 0 ?j1" using mono by (simp add: monoT_def)
            have adm0: "adm M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
            have m0M: "(M, 0) \<in> Marked"
              using MT leM0 adm0 by (simp add: Marked_def)
            have markTrans: "Mark M 0 = Trans M"
              using ra_Mark0_eq_Trans m0M MR by blast
            have transM_c2: "Trans M = transC2 M"
              using markTrans markc2 jm1z by simp
            \<comment> \<open>\<open>the_enat (transV M) = 0\<close> (left index of \<open>Mark M 0\<close>)\<close>
            have vz: "the_enat (transV M) = 0"
            proof -
              have c1eq: "transC1 M = Mark (Pred M) 0"
                using transJm1eq jm1z by (simp add: transC1_def)
              have mkdA: "(Pred M, 0) \<in> Marked"
                using Marked_Pred_Adm[OF MT L hp] jp_def jm1_def jm1z by simp
              have e10Pz: "entry (Pred M) 1 0 = 0"
              proof -
                have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
                have "0 < length (butlast M)" using L by simp
                thus ?thesis using pb e10z by (simp add: entry_def nth_butlast)
              qed
              have "Mark (Pred M) 0 = 0\<^sub>B
                    \<or> (\<exists>t. Mark (Pred M) 0 = Dpt (enat (entry (Pred M) 1 0)) t)"
                using Mark_leftend_form mkdA predRT by blast
              thus ?thesis
              proof
                assume "Mark (Pred M) 0 = 0\<^sub>B"
                hence "transV M = bpHeadV 0\<^sub>B" using c1eq by (simp add: transV_def)
                thus ?thesis by (simp add: zero_enat_def)
              next
                assume "\<exists>t. Mark (Pred M) 0 = Dpt (enat (entry (Pred M) 1 0)) t"
                then obtain t where
                  "Mark (Pred M) 0 = Dpt (enat (entry (Pred M) 1 0)) t" by blast
                hence "transV M = enat (entry (Pred M) 1 0)"
                  using c1eq by (simp add: transV_def)
                thus ?thesis using e10Pz by simp
              qed
            qed
            have ra: "RightAnces M = [0] @ tail" using raMono segz by simp
            have "RightNodes (Trans M) = RightNodes (transC2 M)" using transM_c2 by simp
            also have "\<dots> = the_enat (transV M) # tail" using rnc2 .
            also have "\<dots> = 0 # tail" using vz by simp
            finally show ?thesis using ra by simp
          next
            case segnz: False
            \<comment> \<open>\<open>jm1\<close>-basepoint mark splits \<open>RightNodes (Trans M)\<close>; IH on the slice\<close>
            have raN: "RightAnces M = RightAnces (seg M 0 jm1) @ tail"
              using raMono segnz by simp
            have IHN: "RightAnces (seg M 0 jm1) = RightNodes (Trans (seg M 0 jm1))"
              using less.IH[OF segLnglt] segRT by blast
            show ?thesis
            proof (cases "jm1 = 0")
              case jm1z: True
              \<comment> \<open>boundary: \<open>Trans M = c\<^sub>2\<close>, slice \<open>= [M\<^bsub>0\<^esub>]\<close> with \<open>RightNodes = [transV]\<close>\<close>
              have leM0: "leR M 0 0 ?j1" using mono by (simp add: monoT_def)
              have adm0: "adm M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
              have m0M: "(M, 0) \<in> Marked"
                using MT leM0 adm0 by (simp add: Marked_def)
              have markTrans: "Mark M 0 = Trans M"
                using ra_Mark0_eq_Trans m0M MR by blast
              have transM_c2: "Trans M = transC2 M"
                using markTrans markc2 jm1z by simp
              \<comment> \<open>slice \<open>N = seg M 0 0 = [M\<^bsub>0\<^esub>]\<close> reduced one-column, \<open>\<not> zeroT\<close>\<close>
              have NsegRT: "seg M 0 0 \<in> RT_PS" using segRT jm1z by simp
              have NsegT: "seg M 0 0 \<in> T_PS" using NsegRT by (simp add: RT_PS_def)
              have Nseglng: "Lng (seg M 0 0) = 1" by simp
              obtain w where Nw: "seg M 0 0 = [(w, w)]"
                using m_6_6_oneColumn[OF NsegT] NsegRT Nseglng by auto
              have nzN: "\<not> zeroT (seg M 0 0)" using segnz jm1z by simp
              have wne: "w \<noteq> 0"
              proof -
                have "entry (seg M 0 0) 1 0 \<noteq> 0" using nzN by (simp add: zeroT_def)
                thus ?thesis using Nw by (simp add: entry_def)
              qed
              have transN: "Trans (seg M 0 0) = Dpt (enat w) 0\<^sub>B"
                using Nw Trans_singleton wne by simp
              have rnN: "RightNodes (Trans (seg M 0 0)) = [w]"
                using transN by simp
              \<comment> \<open>\<open>w = the_enat (transV M)\<close> via \<open>entry M 1 0\<close>\<close>
              have e10w: "entry M 1 0 = w"
              proof -
                have "entry (seg M 0 0) 1 0 = entry M 1 0"
                  using entry_seg[of 0 M 0 0 1] by simp
                thus ?thesis using Nw by (simp add: entry_def)
              qed
              have veq: "the_enat (transV M) = w"
              proof -
                have c1eq: "transC1 M = Mark (Pred M) 0"
                  using transJm1eq jm1z by (simp add: transC1_def)
                have mkdA: "(Pred M, 0) \<in> Marked"
                  using Marked_Pred_Adm[OF MT L hp] jp_def jm1_def jm1z by simp
                have e10P: "entry (Pred M) 1 0 = w"
                proof -
                  have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
                  have "0 < length (butlast M)" using L by simp
                  thus ?thesis using pb e10w by (simp add: entry_def nth_butlast)
                qed
                have markPnz: "Mark (Pred M) 0 \<noteq> 0\<^sub>B"
                proof -
                  have "transC1 M \<noteq> 0\<^sub>B"
                  proof -
                    have "Lng (PB (transC1 M)) = 1"
                      by (rule transC1_single_principal[OF MR MP J1pos T1ne])
                    thus ?thesis by (auto simp: PB_def)
                  qed
                  thus ?thesis using c1eq by simp
                qed
                obtain t where
                  mkform: "Mark (Pred M) 0 = Dpt (enat (entry (Pred M) 1 0)) t"
                  using Mark_leftend_form mkdA predRT markPnz by blast
                have "transV M = enat (entry (Pred M) 1 0)"
                  using c1eq mkform by (simp add: transV_def)
                thus ?thesis using e10P by simp
              qed
              have chain: "RightNodes (Trans M) = RightAnces (seg M 0 0) @ tail"
              proof -
                have "RightNodes (Trans M) = RightNodes (transC2 M)" using transM_c2 by simp
                also have "\<dots> = the_enat (transV M) # tail" using rnc2 .
                also have "\<dots> = w # tail" using veq by simp
                also have "\<dots> = [w] @ tail" by simp
                also have "\<dots> = RightNodes (Trans (seg M 0 0)) @ tail" using rnN by simp
                also have "\<dots> = RightAnces (seg M 0 0) @ tail" using IHN jm1z by simp
                finally show ?thesis .
              qed
              have raeq: "RightAnces M = RightAnces (seg M 0 0) @ tail"
                using raN jm1z by simp
              show ?thesis using raeq chain by simp
            next
              case jm1pos: False
              have jm1g0: "0 < jm1" using jm1pos by simp
              \<comment> \<open>\<open>(M, jm1) \<in> Marked\<close> with \<open>0 < jm1 < Lng M - 1\<close>\<close>
              have admA: "adm M jm1" using jm1_def by (simp add: adm_Adm_adm)
              have jpb: "jp \<le> Lng M - 1" using jplt by simp
              have le1a: "leR M 1 jm1 jp"
                using adm_row1_ancestry[OF MT jpb] jm1_def by simp
              have le0a: "leR M 0 jm1 jp" by (rule m_le1_imp_le0[OF le1a])
              have leMa: "leR M 0 jm1 ?j1"
              proof -
                have st: "nextrel0 M jp ?j1" using parR by (simp add: nextR_def)
                have "(nextrel0 M)\<^sup>*\<^sup>* jm1 jp" using le0a by (simp add: leR_def le0_def)
                hence "(nextrel0 M)\<^sup>*\<^sup>* jm1 ?j1" using st by (rule rtranclp.rtrancl_into_rtrancl)
                moreover have "jm1 < Lng M" using jm1lt L by linarith
                moreover have "?j1 < Lng M" using L by linarith
                ultimately show ?thesis by (simp add: leR_def le0_def)
              qed
              have mMjm1: "(M, jm1) \<in> Marked"
                using MT admA leMa by (simp add: Marked_def)
              \<comment> \<open>the \<open>RightNodes/Mark\<close> split at \<open>jm1\<close>\<close>
              obtain a0 a1 where
                splitT: "RightNodes (Trans M) = a0 @ [entry M 1 jm1] @ a1"
                and splitSeg: "RightNodes (Trans (seg M 0 jm1)) = a0 @ [entry M 1 jm1]"
                and splitMark: "RightNodes (Mark M jm1) = [entry M 1 jm1] @ a1"
                using m_7_4_RightNodes_Mark[OF mMjm1 MR jm1g0 jm1lt] by blast
              \<comment> \<open>\<open>RightNodes (Mark M jm1) = transV # tail = entry M 1 jm1 # tail\<close>\<close>
              have rnMarkc2: "RightNodes (Mark M jm1) = the_enat (transV M) # tail"
                using markc2 rnc2 by simp
              \<comment> \<open>so \<open>a1 = tail\<close>\<close>
              have a1tail: "a1 = tail"
                using splitMark rnMarkc2 by simp
              \<comment> \<open>combine: \<open>RightNodes (Trans M) = RightNodes (Trans (seg M 0 jm1)) @ tail\<close>\<close>
              have "RightNodes (Trans M) = (a0 @ [entry M 1 jm1]) @ a1"
                using splitT by simp
              also have "\<dots> = RightNodes (Trans (seg M 0 jm1)) @ tail"
                using splitSeg a1tail by simp
              also have "\<dots> = RightAnces (seg M 0 jm1) @ tail" using IHN by simp
              finally show ?thesis using raN by simp
            qed
          qed
        qed
      next
        case nmono: False
        \<comment> \<open>multi branch: \<open>RightNodes (Trans M)\<close> depends only on the last component\<close>
        have nz: "\<not> zeroT M" using L by (simp add: zeroT_def)
        have mu: "multiT M" using nmono nz by (simp add: multiT_def)
        let ?A = "take (Pcut M) M"
        let ?PJ = "drop (Pcut M) M"
        have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF MT mu])
        have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
        have Pne: "P M \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
        have PJRT: "?PJ \<in> RT_PS" using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
        have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
        have LPJlt: "Lng ?PJ < Lng M"
        proof -
          have "Lng ?PJ = Lng M - Pcut M" by simp
          thus ?thesis using cut L by linarith
        qed
        \<comment> \<open>RightAnces value\<close>
        have raMulti: "RightAnces M = (if ?PJ = [(0,0)] then [0] else RightAnces ?PJ)"
          using raM j1ne nmono PJeq by (simp add: Let_def)
        \<comment> \<open>Trans value\<close>
        have c1: "(M \<notin> RT_PS) = False" using MR by simp
        have c2: "(Lng M - 1 = 0) = False" using L by simp
        have c3: "monoT M = False" using nmono by simp
        have Aeq2: "seg M 0 (Lng M - 1 - Lng (drop (Pcut M) M) + 1 - 1) = ?A"
        proof -
          have LdJ: "Lng (drop (Pcut M) M) = Lng M - Pcut M" by simp
          have "Lng M - 1 - Lng (drop (Pcut M) M) + 1 - 1 = Pcut M - 1"
            using LdJ cut by linarith
          moreover have "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
            by (rule seg_0_eq_take) (use cut L in linarith)
          moreover have "Suc (Pcut M - 1) = Pcut M" using cut by simp
          ultimately show ?thesis by simp
        qed
        have transM: "Trans M = (if ?PJ = [(0, 0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B
                                 else Trans ?A +\<^sub>B Trans ?PJ)"
        proof -
          have raw: "Trans M =
              (if P M ! (Lng (P M) - 1) = [(0, 0)]
               then Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                      +\<^sub>B Dpt 0 0\<^sub>B
               else Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                      +\<^sub>B Trans (P M ! (Lng (P M) - 1)))"
            by (subst Trans.psimps[OF domT]) (simp only: c1 c2 c3 if_False Let_def)
          show ?thesis unfolding raw PJeq Aeq2 ..
        qed
        show ?thesis
        proof (cases "?PJ = [(0, 0)]")
          case PJz: True
          have ra: "RightAnces M = [0]" using raMulti PJz by simp
          have tv: "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM PJz by simp
          have nzD0: "Dpt 0 0\<^sub>B \<noteq> 0\<^sub>B" by simp
          have "RightNodes (Trans M) = RightNodes (Dpt 0 0\<^sub>B)"
            using tv ra_RightNodes_addBT_right[OF nzD0] by simp
          also have "\<dots> = [0]" by (simp add: zero_enat_def)
          finally show ?thesis using ra by simp
        next
          case PJnz: False
          have ra: "RightAnces M = RightAnces ?PJ" using raMulti PJnz by simp
          have tv: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM PJnz by simp
          \<comment> \<open>\<open>?PJ\<close> not zero (reduced, \<open>\<noteq> [(0,0)]\<close>)\<close>
          have nzPJ: "\<not> zeroT ?PJ"
          proof
            assume z: "zeroT ?PJ"
            have L1: "Lng ?PJ = 1" using z by (simp add: zeroT_def)
            then obtain v where v: "?PJ = [(v, v)]"
              using m_6_6_oneColumn[OF PJT] PJRT by auto
            have "entry ?PJ 1 0 = 0" using z by (simp add: zeroT_def)
            hence "v = 0" using v by (simp add: entry_def)
            thus False using PJnz v by simp
          qed
          have tPJnz: "Trans ?PJ \<noteq> 0\<^sub>B"
            using m_7_3_Trans_zeroT[OF PJRT] nzPJ by blast
          have IHPJ: "RightAnces ?PJ = RightNodes (Trans ?PJ)"
            using less.IH[OF LPJlt] PJRT by blast
          have "RightNodes (Trans M) = RightNodes (Trans ?PJ)"
            using tv ra_RightNodes_addBT_right[OF tPJnz] by simp
          also have "\<dots> = RightAnces ?PJ" using IHPJ by simp
          finally show ?thesis using ra by simp
        qed
      qed
    qed
  qed
qed

text \<open>Within-block left-minimum of the reduced blocks: every row-0 value of
  \<open>Red (P M ! I)\<close> is \<open>\<ge>\<close> its left end.  For \<open>monoT\<close> blocks this is
  @{thm [source] m_6_5_Red_leftend_row0_min}; for the \<open>zeroT\<close> block
  \<open>Red \<dots> = [(0,0)]\<close> is a singleton.\<close>

lemma ra_Red_block_within_min:
  assumes BT: "B \<in> T_PS" and zm: "zeroT B \<or> monoT B" and k: "k < Lng (Red B)"
  shows "entry (Red B) 0 0 \<le> entry (Red B) 0 k"
proof (cases "monoT B")
  case True
  show ?thesis using m_6_5_Red_leftend_row0_min[OF BT True] k by blast
next
  case False
  hence z: "zeroT B" using zm by simp
  have "Red B = [(0,0)]"
    using Red.psimps[OF m_6_5_Red_welldef[OF BT]] z by simp
  hence "Lng (Red B) = 1" by simp
  hence "k = 0" using k by simp
  thus ?thesis by simp
qed

text \<open>The cross-block row-0 head ordering needed by
  @{thm [source] if2_P_concat_blocks}, reduced to the within-block left-minimum
  (@{thm [source] ra_Red_block_within_min}) plus the cross-block left-end
  antitonicity \<open>I \<le> J \<Longrightarrow> entry (Red (P M ! J)) 0 0 \<le> entry (Red (P M ! I)) 0 0\<close>.\<close>

lemma ra_P_Red_blocks_row0_min:
  assumes MT: "M \<in> T_PS" and mu: "multiT M"
    and anti: "\<And>I J. I \<le> J \<Longrightarrow> J < length (P M)
                 \<Longrightarrow> entry (Red (P M ! J)) 0 0 \<le> entry (Red (P M ! I)) 0 0"
  shows "\<forall>J < length (map Red (P M)). \<forall>I \<le> J. \<forall>k < Lng (map Red (P M) ! I).
           entry (map Red (P M) ! J) 0 0 \<le> entry (map Red (P M) ! I) 0 k"
proof (intro allI impI)
  fix J I k
  assume J: "J < length (map Red (P M))" and IJ: "I \<le> J"
    and k: "k < Lng (map Red (P M) ! I)"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have J': "J < length (P M)" using J by simp
  have I': "I < length (P M)" using IJ J' by linarith
  have nthJ: "map Red (P M) ! J = Red (P M ! J)" using J' by simp
  have nthI: "map Red (P M) ! I = Red (P M ! I)" using I' by simp
  have BIT: "P M ! I \<in> T_PS"
    using P_blocks_nonempty[OF Mne] I' by (auto simp: T_PS_def)
  have zmI: "zeroT (P M ! I) \<or> monoT (P M ! I)"
    using m_6_2_P_components_1[OF MT] I' by simp
  have kI: "k < Lng (Red (P M ! I))" using k nthI by simp
  have within: "entry (Red (P M ! I)) 0 0 \<le> entry (Red (P M ! I)) 0 k"
    by (rule ra_Red_block_within_min[OF BIT zmI kI])
  have cross: "entry (Red (P M ! J)) 0 0 \<le> entry (Red (P M ! I)) 0 0"
    by (rule anti[OF IJ J'])
  show "entry (map Red (P M) ! J) 0 0 \<le> entry (map Red (P M) ! I) 0 k"
    using within cross nthJ nthI by simp
qed

text \<open>命題（\<open>RightNodes\<close>と\<open>RightAnces\<close>の関係） (§7.4, 2745), discharging
  @{thm [source] p_7_4_RightAnces_RightNodes}.  Stated on \<open>RT\<^bsub>PS\<^esub>\<close> (the domain
  the rest of §7/§8 uses, matching @{thm [source] m_7_3_Trans_Red}).  The article's
  \<open>M \<in> T\<^bsub>PS\<^esub>\<close> form lifts through \<open>Red\<close> once general \<open>Red\<close>-idempotency on
  multi terms (\<open>Red M \<in> RT\<^bsub>PS\<^esub>\<close>, the deferred §6 P-Red-equivariance blocker;
  @{thm [source] p_6_5_Red_idem} is proved only on \<open>anchored_slice\<close>) is available:
  the lift is \<open>RightAnces M = RightAnces (Red M) = RightNodes (Trans (Red M))
  = RightNodes (Trans M)\<close> via \<open>RightAnces.psimps\<close> and @{thm [source] m_7_3_Trans_Red}.\<close>

lemma m_7_4_RightAnces_RightNodes:
  assumes "M \<in> RT_PS"
  shows "RightAnces M = RightNodes (Trans M)"
  by (rule ra_RightAnces_RightNodes_RT[rule_format, OF assms])


text \<open>\<open>RightNodes\<close> of a term is empty iff the term is \<open>0\<close>: a non-empty principal
  list has a \<open>DB\<close>-headed last component, contributing a head node.\<close>

lemma rnsub_RightNodes_empty_iff: "RightNodes t = [] \<longleftrightarrow> t = 0\<^sub>B"
proof
  assume h: "RightNodes t = []"
  obtain xs where t: "t = Trm xs" by (cases t)
  show "t = 0\<^sub>B"
  proof (cases xs)
    case Nil thus ?thesis using t by simp
  next
    case (Cons a as)
    hence ne: "xs \<noteq> []" by simp
    obtain u b where lb: "last xs = DB u b" by (cases "last xs") auto
    have "RightNodes (Trm xs) = RightNodes (Trm [last xs])"
      using ne by (rule rnsub_RightNodes_last)
    also have "\<dots> = the_enat u # RightNodes b" by (simp add: lb)
    finally have "RightNodes (Trm xs) = the_enat u # RightNodes b" .
    hence False using h t by simp
    thus ?thesis ..
  qed
next
  assume "t = 0\<^sub>B" thus "RightNodes t = []" by simp
qed

text \<open>系（非零項の \<open>RightAnces\<close> が非空であること） (§7.4, 2809), discharging
  @{thm [source] p_7_4_RightAnces_zeroT}.  On \<open>RT\<^bsub>PS\<^esub>\<close> (cf.
  @{thm [source] m_7_4_RightAnces_RightNodes}): immediate from the
  \<open>RightAnces\<close>=\<open>RightNodes\<circ>Trans\<close> correspondence, the empty-\<open>RightNodes\<close>
  characterisation, and @{thm [source] m_7_3_Trans_zeroT}.\<close>

lemma m_7_4_RightAnces_zeroT:
  assumes "M \<in> RT_PS"
  shows "zeroT M \<longleftrightarrow> RightAnces M = []"
proof -
  have "RightAnces M = RightNodes (Trans M)"
    by (rule m_7_4_RightAnces_RightNodes[OF assms])
  moreover have "RightNodes (Trans M) = [] \<longleftrightarrow> Trans M = 0\<^sub>B"
    by (rule rnsub_RightNodes_empty_iff)
  moreover have "Trans M = 0\<^sub>B \<longleftrightarrow> zeroT M"
    using m_7_3_Trans_zeroT[OF assms] by blast
  ultimately show ?thesis by simp
qed


text \<open>§7.4 keystone (towards "Mark preserves order"): a \<open>monoT\<close> reduced sequence
  of length \<open>> 1\<close> has \<open>RightNodes (Trans M)\<close> of length \<open>\<ge> 2\<close>.  \<open>Trans M\<close> is a
  single principal \<open>Trm [DB u a]\<close> (@{thm [source] Trans_PT_single}); its
  right-spine has length \<open>1 + length (RightNodes a)\<close>, so it suffices to show the
  inner argument \<open>a \<noteq> 0\<^bsub>B\<^esub>\<close>.  In the \<open>t\<^sub>1 = 0\<close> branch \<open>Trans M = D\<^bsub>0\<^esub>(D\<^bsub>bv\<^esub> 0)\<close>
  has inner \<open>D\<^bsub>bv\<^esub> 0 \<noteq> 0\<close>; in the \<open>t\<^sub>1 \<noteq> 0\<close> (surgery) branch \<open>flatBT (Trans M)\<close>
  embeds \<open>flatBT (transC2 M)\<close> (length \<open>\<ge> 3\<close>), forcing \<open>length (flatBT a) \<ge> 2\<close>,
  hence \<open>a \<noteq> 0\<close>.\<close>

lemma Trans_mono_RN_ge2:
  assumes MR: "M \<in> RT_PS" and mono: "monoT M" and L: "1 < Lng M"
  shows "2 \<le> length (RightNodes (Trans M))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have nzM: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have tMne: "Trans M \<noteq> 0\<^sub>B" using m_7_3_Trans_zeroT[OF MR] nzM by blast
  \<comment> \<open>\<open>Trans M\<close> is a single principal \<open>Trm [DB u a]\<close>\<close>
  obtain p where Tp: "Trans M = Trm [p]"
    using Trans_PT_single[THEN mp, THEN mp, THEN mp, OF MR mono tMne] by blast
  obtain u a where pua: "p = DB u a" by (cases p)
  have TM: "Trans M = Trm [DB u a]" using Tp pua by simp
  have rnM: "RightNodes (Trans M) = the_enat u # RightNodes a"
    using TM by simp
  \<comment> \<open>suffices: the inner argument \<open>a\<close> is nonzero\<close>
  have suff: "a \<noteq> 0\<^sub>B \<Longrightarrow> 2 \<le> length (RightNodes (Trans M))"
  proof -
    assume "a \<noteq> 0\<^sub>B"
    hence "RightNodes a \<noteq> []" by (simp add: rnsub_RightNodes_empty_iff)
    thus ?thesis using rnM by (cases "RightNodes a") auto
  qed
  have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  let ?j1 = "Lng M - 1"
  show ?thesis
  proof (cases "Trans (Pred M) = 0\<^sub>B")
    case t1z: True
    \<comment> \<open>\<open>Trans M = D\<^bsub>0\<^esub>(D\<^bsub>bv\<^esub> 0)\<close>, inner \<open>= D\<^bsub>bv\<^esub> 0 \<noteq> 0\<close>\<close>
    have tv: "Trans M = Dpt 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
      using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
    have "Trm [DB u a] = Trm [DB 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)]"
      using TM tv by simp
    hence "a = Dpt (enat (entry M 1 ?j1)) 0\<^sub>B" by simp
    hence "a \<noteq> 0\<^sub>B" by simp
    thus ?thesis by (rule suff)
  next
    case t1ne: False
    \<comment> \<open>surgery branch: replicate the \<open>flatBT (Trans M)\<close> = \<open>fst sb1 @ flatBT c2 @ snd sb1\<close> derivation\<close>
    have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
    have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L])
    let ?t1 = "Trans (Pred M)"
    let ?bv = "entry M 1 (Lng M - 1)"
    define jp where "jp = parent M 0 (Lng M - 1)"
    define c1 where "c1 = Mark (Pred M) (Adm M jp)"
    define vv where "vv = bpHeadV c1"
    define tt2 where "tt2 = bpHeadT c1"
    define JJ1 where "JJ1 = Lng (PB tt2) - 1"
    define pj where "pj = PB tt2 ! JJ1"
    define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
    define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
    define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
    define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                           then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                           else if transCondVI M
                           then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                           else if tt2 = 0\<^sub>B
                           then Dpt vv (Dpt (enat (entry M 1 jp))
                                        (Dpt (enat ?bv) 0\<^sub>B))
                           else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                              (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
    define sb1 where
      "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
    have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
      using Trans.psimps[OF domT] MR Lgt1 mono t1ne
      unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                c2_def[symmetric] sb1_def[symmetric]
      by simp
    have transJ1eq: "transJ1 M = ?j1" by (simp add: transJ1_def)
    have transJ0eq: "transJ0 M = jp"
      by (simp add: transJ0_def transJ1_def jp_def)
    have transJm1eq: "transJm1 M = Adm M jp"
      by (simp add: transJm1_def transJ0eq)
    have c1eqT: "c1 = transC1 M"
      by (simp add: c1_def transC1_def transJm1eq)
    have c2eqT: "c2 = transC2 M"
      unfolding c2_def transC2_def Let_def
        vv_def tt2_def c1eqT transV_def transT2_def
        JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
      by simp
    have mkjm1: "(Pred M, Adm M jp) \<in> Marked"
      using Marked_Pred_Adm[OF MT L hp] jp_def by simp
    have NP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
    have J1pos: "transJ1 M > 0" using L by (simp add: transJ1_def)
    have T1ne: "transT1 M \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
    have pc1: "Lng (PB (transC1 M)) = 1"
      by (rule transC1_single_principal[OF MR NP J1pos T1ne])
    have c1ne: "transC1 M \<noteq> 0\<^sub>B"
    proof
      assume "transC1 M = 0\<^sub>B"
      thus False using pc1 by (simp add: PB_def)
    qed
    have c1TB: "transC1 M \<in> T_B"
      using m_7_3_Mark_in_T_B[OF predRT mkjm1]
            c1eqT[symmetric] c1_def by simp
    have c1Dpt: "transC1 M = Dpt (transV M) (transT2 M)"
      using principal_reconstruct[OF pc1] by (simp add: transV_def transT2_def)
    have c1Dsym: "flatBT c1 = Dsym (transV M) # flatBT (transT2 M)"
      using c1eqT c1Dpt by simp
    have vvT: "vv = transV M" by (simp add: vv_def transV_def c1eqT)
    have bpc2: "bpHeadV c2 = transV M"
    proof -
      have "bpHeadV c2 = vv" by (simp add: c2_def)
      thus ?thesis using vvT by simp
    qed
    have c2pc1: "Lng (PB c2) = 1"
      using transC2_single_principal c2eqT by simp
    have c2Dpt: "c2 = Dpt (transV M) (bpHeadT c2)"
      using principal_reconstruct[OF c2pc1] bpc2 by simp
    have c2Dsym: "flatBT c2 = Dsym (transV M) # flatBT (bpHeadT c2)"
      by (subst c2Dpt) (rule flatBT_principal_head)
    \<comment> \<open>\<open>flatBT (transC2 M)\<close> has length \<open>\<ge> 3\<close> (inner \<open>bpHeadT c2 \<noteq> 0\<close>)\<close>
    have c2tail_ne: "bpHeadT c2 \<noteq> 0\<^sub>B"
      using transC2_inner_nonzero[of M] c2eqT by simp
    have lenc2: "3 \<le> length (flatBT c2)"
    proof -
      have "2 \<le> length (flatBT (bpHeadT c2))"
        by (rule flatBT_len_ge2[OF c2tail_ne])
      thus ?thesis using c2Dsym by simp
    qed
    \<comment> \<open>the surgery output flattens to \<open>fst sb1 @ flatBT c2 @ snd sb1\<close>\<close>
    have inv1: "(Trans (Pred M), c1) \<in> MarkedB"
      using m_7_3_Trans_Mark_MarkedB[OF predRT mkjm1] c1_def by simp
    have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
      using inv1 unfolding MarkedB_def by auto
    have dsb: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
      unfolding sb1_def by (rule someI_ex[OF exsb])
    have c2df: "dfree_BT c2"
    proof -
      have vne: "transV M \<noteq> \<infinity>" using c1TB c1Dpt by (auto simp: T_B_def)
      have t2df: "dfree_BT (transT2 M)" using c1TB c1Dpt by (auto simp: T_B_def)
      show ?thesis using dfree_transC2[OF vne t2df] c2eqT by simp
    qed
    obtain pc2 where c2p: "c2 = Trm [pc2]"
      using principal_reconstruct[OF c2pc1] by (metis BT.exhaust untrm.simps)
    have iptc2': "isPTB_str (flatBT (Trm [pc2]))"
    proof -
      have "dfree_BT (Trm [pc2])" using c2df c2p by simp
      then obtain q where "pc2 = q" and "dfree_BP q" by auto
      thus ?thesis by (auto simp: isPTB_str_def)
    qed
    obtain pc1' where c1p: "c1 = Trm [pc1']"
      using principal_reconstruct[OF pc1] c1eqT by (metis BT.exhaust untrm.simps)
    have dsb': "scb_decomp ?t1 (fst sb1) (flatBT (Trm [pc1'])) (snd sb1)"
      using dsb c1p by simp
    obtain t' where t'f: "flatBT t' = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
        and t'd: "scb_decomp t' (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
      using scb_replace_principal[OF dsb' iptc2'] by blast
    have transMp: "Trans M = t'"
      using trans_val t'f c2p unflatBT_flat[of t'] by simp
    have flatTM: "flatBT (Trans M) = fst sb1 @ flatBT c2 @ snd sb1"
      using transMp t'f c2p by simp
    \<comment> \<open>\<open>length (flatBT (Trans M)) \<ge> 3\<close>, and \<open>flatBT (Trans M) = Dsym u # flatBT a\<close>\<close>
    have flatlen3: "3 \<le> length (flatBT (Trans M))"
      using flatTM lenc2 by simp
    have flatTMua: "flatBT (Trans M) = Dsym u # flatBT a"
      using TM by simp
    have "2 \<le> length (flatBT a)"
      using flatlen3 flatTMua by simp
    hence "flatBT a \<noteq> [Zsym]" by auto
    hence "a \<noteq> 0\<^sub>B" by auto
    thus ?thesis by (rule suff)
  qed
qed


text \<open>命題（\<open>Trans\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） (§7.4), discharging
  @{thm [source] p_7_4_Trans_nextAdm}.  On \<open>RT\<^bsub>PS\<^esub>\<close> (cf.
  @{thm [source] m_7_4_Trans_Mark_Pred}): the unique NextAdm-parent \<open>j\<^sub>0\<close> of
  \<open>j\<^sub>1 = Lng M - 1\<close> satisfies \<open>(M, j\<^sub>0) \<in> Marked\<close> (it is \<open>M\<close>-admissible and an
  ancestor of \<open>j\<^sub>1\<close>) and \<open>j\<^sub>0 < j\<^sub>1\<close>, so the claim is exactly
  @{thm [source] m_7_4_Trans_Mark_Pred} at \<open>m = j\<^sub>0\<close>.\<close>

lemma m_7_4_Trans_nextAdm:
  assumes MR: "M \<in> RT_PS"
    and uniq: "\<exists>!j0. nextAdm M 0 j0 (Lng M - 1)"
  shows "\<exists>!sb. scb_decomp (Trans (Pred M))
                  (fst sb) (flatBT (Mark (Pred M) (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
            \<and> scb_decomp (Trans M)
                  (fst sb) (flatBT (Mark M (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)"
proof -
  let ?m = "THE j0. nextAdm M 0 j0 (Lng M - 1)"
  have na: "nextAdm M 0 ?m (Lng M - 1)" by (rule theI'[OF uniq])
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have leRm: "leR M 0 ?m (Lng M - 1)" using na unfolding nextAdm_def by blast
  have mlt: "?m < Lng M - 1" using na unfolding nextAdm_def by blast
  have admm: "adm M ?m" using na unfolding nextAdm_def by blast
  have mM: "(M, ?m) \<in> Marked" using MT admm leRm by (simp add: Marked_def)
  show ?thesis by (rule m_7_4_Trans_Mark_Pred[OF mM MR mlt])
qed


section \<open>§7.4 系（\<open>Mark\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） — m_7_4_Mark_nextAdm\<close>

text \<open>Helper: a marked image \<open>Mark M m\<close> of a reduced \<open>M\<close> with \<open>Trans M \<noteq> Trm []\<close>
  is a single principal term, hence \<open>\<noteq> Trm []\<close> and \<open>isPTB_str\<close>.  It is the
  marked block of the (nonzero) \<open>Trans M\<close>, recovered from the
  \<open>(Trans M, Mark M m) \<in> MarkedB\<close> invariant.\<close>

lemma mark_marked_principal:
  assumes MR: "M \<in> RT_PS" and mM: "(M, m) \<in> Marked" and tne: "Trans M \<noteq> Trm []"
  shows "\<exists>p. Mark M m = Trm [p]" and "Mark M m \<noteq> Trm []"
    and "isPTB_str (flatBT (Mark M m))"
proof -
  have mb: "(Trans M, Mark M m) \<in> MarkedB"
    by (rule m_7_3_Trans_Mark_MarkedB[OF MR mM])
  obtain s b where d: "scb_decomp (Trans M) s (flatBT (Mark M m)) b"
    using mb by (auto simp: MarkedB_def)
  show ipt: "isPTB_str (flatBT (Mark M m))"
    using d tne by (simp add: scb_decomp_def)
  then obtain pc where pcl: "flatBT (Mark M m) = flatBP pc"
    by (auto simp: isPTB_str_def)
  show "\<exists>p. Mark M m = Trm [p]"
  proof -
    have "flatBT (Mark M m) = flatBT (Trm [pc])" using pcl by simp
    hence "Mark M m = Trm [pc]" by (rule m_7_flatBT_inj)
    thus ?thesis by blast
  qed
  then obtain p where "Mark M m = Trm [p]" by blast
  thus "Mark M m \<noteq> Trm []" by simp
qed

text \<open>Helper (marked case): for a reduced \<open>M\<close> and marked columns \<open>m \<le> m'\<close> with
  \<open>m' < Lng M - 1\<close>, there is a UNIQUE common scb-position \<open>(s\<^sub>0,b\<^sub>0)\<close> with
  \<open>(s\<^sub>0, Mark(Pred M, m'), b\<^sub>0)\<close> an scb-decomposition of \<open>Mark(Pred M, m)\<close> and
  \<open>(s\<^sub>0, Mark(M, m'), b\<^sub>0)\<close> one of \<open>Mark(M, m)\<close>.  Proof by the composition rule
  on \<open>Trans\<close>: by @{thm [source] m_7_4_Trans_Mark_Pred} both \<open>Mark _ m\<close> and
  \<open>Mark _ m'\<close> sit in \<open>Trans _\<close> at common positions \<open>(s\<^sub>m,b\<^sub>m)\<close> resp. \<open>(s\<^sub>m\<^sub>'\<^sub>,b\<^sub>m\<^sub>'\<^sub>)\<close>;
  by @{thm [source] Mark_MarkedB_nest} \<open>Mark _ m'\<close> nests in \<open>Mark _ m\<close>; composing
  and using @{thm [source] m_7_2_scb_unique_sb} pins the nest position to the
  SAME \<open>(s\<^sub>0,b\<^sub>0)\<close> for both \<open>Pred M\<close> and \<open>M\<close>.\<close>

lemma Mark_nest_common_marked:
  assumes MR: "M \<in> RT_PS"
    and mM: "(M, m) \<in> Marked" and mM': "(M, m') \<in> Marked"
    and mle: "m \<le> m'" and m'lt: "m' < Lng M - 1"
  shows "\<exists>!sb. scb_decomp (Mark (Pred M) m) (fst sb) (flatBT (Mark (Pred M) m')) (snd sb)
            \<and> scb_decomp (Mark M m) (fst sb) (flatBT (Mark M m')) (snd sb)"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have mlt: "m < Lng M - 1" using mle m'lt by simp
  have L: "1 < Lng M" using m'lt by linarith
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
  have mP: "(Pred M, m) \<in> Marked" by (rule Marked_Pred[OF MT L mM mlt])
  have mP': "(Pred M, m') \<in> Marked" by (rule Marked_Pred[OF MT L mM' m'lt])
  show ?thesis
  proof (cases "m = m'")
    case eq: True
    \<comment> \<open>reflexive: the core equals the whole term, position \<open>([],[])\<close>\<close>
    have selfdecomp: "\<And>t::BT. scb_decomp t [] (flatBT t) []
                        \<longleftrightarrow> (t \<noteq> Trm [] \<longrightarrow> isPTB_str (flatBT t))"
      by (auto simp: scb_decomp_def)
    \<comment> \<open>generic: a marked block is principal (\<open>isPTB_str\<close>) or empty\<close>
    have ipt_gen: "\<And>N k. N \<in> RT_PS \<Longrightarrow> (N, k) \<in> Marked
        \<Longrightarrow> Mark N k \<noteq> Trm [] \<longrightarrow> isPTB_str (flatBT (Mark N k))"
    proof -
      fix N k assume NR: "N \<in> RT_PS" and kN: "(N, k) \<in> Marked"
      show "Mark N k \<noteq> Trm [] \<longrightarrow> isPTB_str (flatBT (Mark N k))"
      proof
        assume kne: "Mark N k \<noteq> Trm []"
        have mb: "(Trans N, Mark N k) \<in> MarkedB"
          by (rule m_7_3_Trans_Mark_MarkedB[OF NR kN])
        obtain s b where d: "scb_decomp (Trans N) s (flatBT (Mark N k)) b"
          using mb by (auto simp: MarkedB_def)
        \<comment> \<open>\<open>flatBT (Mark N k)\<close> is nonempty and does not equal \<open>[Zsym]\<close>
            (a nonempty \<open>Trm\<close> flattens to a list whose head is \<open>Dsym\<close> or \<open>LP\<close>)\<close>
        have knhd: "flatBT (Mark N k) \<noteq> [] \<and> flatBT (Mark N k) \<noteq> [Zsym]"
        proof (cases "Mark N k")
          case (Trm xs)
          show ?thesis
          proof (cases xs)
            case Nil thus ?thesis using Trm kne by simp
          next
            case (Cons a as)
            obtain u t' where a: "a = DB u t'" by (cases a)
            show ?thesis
            proof (cases as)
              case Nil thus ?thesis using Trm Cons a by simp
            next
              case (Cons b bs) thus ?thesis using Trm \<open>xs = a # as\<close> by simp
            qed
          qed
        qed
        have tNne: "Trans N \<noteq> Trm []"
        proof
          assume z: "Trans N = Trm []"
          have "[Zsym] = s @ flatBT (Mark N k) @ b" using d z by (simp add: scb_decomp_def)
          thus False using knhd
            by (cases s; cases b rule: rev_cases) auto
        qed
        show "isPTB_str (flatBT (Mark N k))" using d tNne by (simp add: scb_decomp_def)
      qed
    qed
    have iptP: "Mark (Pred M) m \<noteq> Trm [] \<longrightarrow> isPTB_str (flatBT (Mark (Pred M) m))"
      by (rule ipt_gen[OF predRT mP])
    have iptM: "Mark M m \<noteq> Trm [] \<longrightarrow> isPTB_str (flatBT (Mark M m))"
      by (rule ipt_gen[OF MR mM])
    have dP0: "scb_decomp (Mark (Pred M) m) [] (flatBT (Mark (Pred M) m')) []"
      using selfdecomp[of "Mark (Pred M) m"] iptP eq by simp
    have dM0: "scb_decomp (Mark M m) [] (flatBT (Mark M m')) []"
      using selfdecomp[of "Mark M m"] iptM eq by simp
    show ?thesis
    proof (rule ex1I[of _ "([], [])"])
      show "scb_decomp (Mark (Pred M) m) (fst ([]::Sym list,[]::Sym list))
               (flatBT (Mark (Pred M) m')) (snd ([],[]))
          \<and> scb_decomp (Mark M m) (fst ([]::Sym list,[]::Sym list))
               (flatBT (Mark M m')) (snd ([],[]))"
        using dP0 dM0 by simp
    next
      fix sb
      assume A: "scb_decomp (Mark (Pred M) m) (fst sb) (flatBT (Mark (Pred M) m')) (snd sb)
               \<and> scb_decomp (Mark M m) (fst sb) (flatBT (Mark M m')) (snd sb)"
      have dsb: "scb_decomp (Mark (Pred M) m) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)"
        using A eq by simp
      have e: "flatBT (Mark (Pred M) m) = fst sb @ flatBT (Mark (Pred M) m) @ snd sb"
        using dsb by (simp add: scb_decomp_def)
      have "length (flatBT (Mark (Pred M) m))
            = length (fst sb) + length (flatBT (Mark (Pred M) m)) + length (snd sb)"
        using arg_cong[OF e, of length] by simp
      hence "length (fst sb) = 0 \<and> length (snd sb) = 0" by simp
      hence "fst sb = [] \<and> snd sb = []" by simp
      thus "sb = ([], [])" by (cases sb) auto
    qed
  next
    case neq: False
    have mltm': "m < m'" using mle neq by simp
  \<comment> \<open>Trans-positions of \<open>Mark _ m\<close> and \<open>Mark _ m'\<close> (common to \<open>Pred M\<close> and \<open>M\<close>)\<close>
  obtain sm bm where
    Pm: "scb_decomp (Trans (Pred M)) sm (flatBT (Mark (Pred M) m)) bm"
    and Mm: "scb_decomp (Trans M) sm (flatBT (Mark M m)) bm"
    using m_7_4_Trans_Mark_Pred[OF mM MR mlt] ex1_implies_ex by force
  obtain sm' bm' where
    Pm': "scb_decomp (Trans (Pred M)) sm' (flatBT (Mark (Pred M) m')) bm'"
    and Mm': "scb_decomp (Trans M) sm' (flatBT (Mark M m')) bm'"
    using m_7_4_Trans_Mark_Pred[OF mM' MR m'lt] ex1_implies_ex by force
  \<comment> \<open>\<open>Mark _ m'\<close> nests in \<open>Mark _ m\<close> (order preservation)\<close>
  have nestP: "(Mark (Pred M) m, Mark (Pred M) m') \<in> MarkedB"
    using Mark_MarkedB_nest mP mP' mle predRT by blast
  have nestM: "(Mark M m, Mark M m') \<in> MarkedB"
    using Mark_MarkedB_nest mM mM' mle MR by blast
  obtain sP bP where dP: "scb_decomp (Mark (Pred M) m) sP (flatBT (Mark (Pred M) m')) bP"
    using nestP by (auto simp: MarkedB_def)
  obtain sM bM where dM: "scb_decomp (Mark M m) sM (flatBT (Mark M m')) bM"
    using nestM by (auto simp: MarkedB_def)
  \<comment> \<open>principality and non-emptiness of the cores\<close>
  have tPne: "Trans (Pred M) \<noteq> Trm []"
  proof -
    have nzP: "\<not> zeroT (Pred M)"
    proof
      assume "zeroT (Pred M)"
      hence "Lng (Pred M) = 1" by (simp add: zeroT_def)
      moreover have "Lng (Pred M) = Lng M - 1" using L by (simp add: Pred_def)
      ultimately have "Lng M = 2" using L by linarith
      thus False using m'lt mltm' by simp
    qed
    show ?thesis using m_7_3_Trans_zeroT[OF predRT] nzP by auto
  qed
  have tMne: "Trans M \<noteq> Trm []"
  proof -
    have "\<not> zeroT M" using L by (auto simp: zeroT_def)
    thus ?thesis using m_7_3_Trans_zeroT[OF MR] by auto
  qed
  have prinPm: "\<exists>p. Mark (Pred M) m = Trm [p]"
    by (rule mark_marked_principal(1)[OF predRT mP tPne])
  have prinMm: "\<exists>p. Mark M m = Trm [p]"
    by (rule mark_marked_principal(1)[OF MR mM tMne])
  have mPmne: "Mark (Pred M) m \<noteq> Trm []"
    by (rule mark_marked_principal(2)[OF predRT mP tPne])
  have mMmne: "Mark M m \<noteq> Trm []"
    by (rule mark_marked_principal(2)[OF MR mM tMne])
  \<comment> \<open>compose: position of \<open>Mark _ m'\<close> in \<open>Trans _\<close> via \<open>Mark _ m\<close>; uniqueness pins it\<close>
  have compP: "scb_decomp (Trans (Pred M)) (sm @ sP) (flatBT (Mark (Pred M) m')) (bP @ bm)"
    by (rule m_7_2_scb_compose[OF prinPm Pm dP])
  have cohP: "sm @ sP = sm' \<and> bP @ bm = bm'"
    by (rule m_7_2_scb_unique_sb[OF compP Pm' tPne])
  have compM: "scb_decomp (Trans M) (sm @ sM) (flatBT (Mark M m')) (bM @ bm)"
    by (rule m_7_2_scb_compose[OF prinMm Mm dM])
  have cohM: "sm @ sM = sm' \<and> bM @ bm = bm'"
    by (rule m_7_2_scb_unique_sb[OF compM Mm' tMne])
  \<comment> \<open>hence \<open>sP = sM\<close> and \<open>bP = bM\<close>: the common position\<close>
  have sEq: "sP = sM"
  proof -
    have "sm @ sP = sm @ sM" using cohP cohM by simp
    thus ?thesis by simp
  qed
  have bEq: "bP = bM"
  proof -
    have "bP @ bm = bM @ bm" using cohP cohM by simp
    thus ?thesis by simp
  qed
  have dM': "scb_decomp (Mark M m) sP (flatBT (Mark M m')) bP"
    using dM sEq bEq by simp
  show ?thesis
  proof (rule ex1I[of _ "(sP, bP)"])
    show "scb_decomp (Mark (Pred M) m) (fst (sP,bP)) (flatBT (Mark (Pred M) m')) (snd (sP,bP))
        \<and> scb_decomp (Mark M m) (fst (sP,bP)) (flatBT (Mark M m')) (snd (sP,bP))"
      using dP dM' by simp
  next
    fix sb
    assume A: "scb_decomp (Mark (Pred M) m) (fst sb) (flatBT (Mark (Pred M) m')) (snd sb)
             \<and> scb_decomp (Mark M m) (fst sb) (flatBT (Mark M m')) (snd sb)"
    have "scb_decomp (Mark (Pred M) m) (fst sb) (flatBT (Mark (Pred M) m')) (snd sb)"
      using A by simp
    hence "fst sb = sP \<and> snd sb = bP"
      by (rule m_7_2_scb_unique_sb[OF _ dP mPmne])
    thus "sb = (sP, bP)" by (cases sb) auto
  qed
  qed
qed

text \<open>命題（\<open>Mark\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） (§7.4), discharging
  @{thm [source] p_7_4_Mark_nextAdm}.  Stated on \<open>RT\<^bsub>PS\<^esub>\<close> with correction A18:
  the article's \<open>(0,j) \<le>\<^sub>M (0,j\<^sub>0)\<close> ranges over \<^emph>\<open>marked\<close> columns \<open>j\<close> (the domain
  of \<open>Mark\<close> is \<open>RT\<^bsub>PS\<^esub>\<^sup>Marked\<close>), so \<open>(M,j) \<in> Marked\<close> is needed: empirically there
  are reduced \<open>M\<close> with a unique NextAdm-parent \<open>j\<^sub>0\<close> and a row-0 ancestor
  \<open>j \<le>\<^sub>M j\<^sub>0\<close> that is NOT \<open>M\<close>-admissible (e.g. \<open>(0,0)(1,1)(2,2)(3,1)\<close>, \<open>j\<^sub>0=2\<close>,
  \<open>j=1\<close>).  Given marked \<open>j\<close>, this is @{thm [source] Mark_nest_common_marked} at
  \<open>m=j\<close>, \<open>m'=j\<^sub>0\<close> (\<open>j \<le> j\<^sub>0\<close> from the \<open>le0\<close> ancestor relation, \<open>j\<^sub>0 < Lng M-1\<close>
  from \<open>nextAdm\<close>).\<close>

lemma m_7_4_Mark_nextAdm:
  assumes MR: "M \<in> RT_PS"
    and uniq: "\<exists>!j0. nextAdm M 0 j0 (Lng M - 1)"
    and jM: "(M, j) \<in> Marked"
    and jle: "leR M 0 j (THE j0. nextAdm M 0 j0 (Lng M - 1))"
  shows "\<exists>!sb. scb_decomp (Mark (Pred M) j)
                  (fst sb) (flatBT (Mark (Pred M) (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
            \<and> scb_decomp (Mark M j)
                  (fst sb) (flatBT (Mark M (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)"
proof -
  let ?j0 = "THE j0. nextAdm M 0 j0 (Lng M - 1)"
  have na: "nextAdm M 0 ?j0 (Lng M - 1)" by (rule theI'[OF uniq])
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have leR0: "leR M 0 ?j0 (Lng M - 1)" using na unfolding nextAdm_def by blast
  have j0lt: "?j0 < Lng M - 1" using na unfolding nextAdm_def by blast
  have adm0: "adm M ?j0" using na unfolding nextAdm_def by blast
  have j0M: "(M, ?j0) \<in> Marked" using MT adm0 leR0 by (simp add: Marked_def)
  have jle0: "j \<le> ?j0"
  proof -
    have "(nextrel0 M)\<^sup>*\<^sup>* j ?j0" using jle by (simp add: leR_def le0_def)
    thus ?thesis by (rule nextrel0_rtrancl_mono)
  qed
  show ?thesis by (rule Mark_nest_common_marked[OF MR jM j0M jle0 j0lt])
qed


text \<open>\<open>MarkedB\<close> is antisymmetric: a Buchholz term and a marked block of it that
  each contain the other as a marked block must coincide (length count forces the
  surrounding scb-strings empty, then \<open>flatBT\<close> injectivity).  Used for the (2)\<Rightarrow>(1)
  direction of "Mark preserves order".\<close>

lemma MarkedB_antisym:
  assumes A1: "(t, c) \<in> MarkedB" and A2: "(c, t) \<in> MarkedB"
  shows "t = c"
proof -
  from A1 obtain s b where d1: "scb_decomp t s (flatBT c) b" by (auto simp: MarkedB_def)
  from A2 obtain s' b' where d2: "scb_decomp c s' (flatBT t) b'" by (auto simp: MarkedB_def)
  have e1: "flatBT t = s @ flatBT c @ b" using d1 by (simp add: scb_decomp_def)
  have e2: "flatBT c = s' @ flatBT t @ b'" using d2 by (simp add: scb_decomp_def)
  have l1: "length (flatBT t) = length s + length (flatBT c) + length b"
    using arg_cong[OF e1, of length] by simp
  have l2: "length (flatBT c) = length s' + length (flatBT t) + length b'"
    using arg_cong[OF e2, of length] by simp
  have ls: "length s = 0" using l1 l2 by linarith
  have lb: "length b = 0" using l1 l2 by linarith
  have "flatBT t = flatBT c" using e1 ls lb by simp
  thus "t = c" by (rule m_7_flatBT_inj)
qed


text \<open>Key length-monotonicity for "Mark preserves order": the right-spine of
  \<open>Trans\<close> of a longer marked prefix is strictly longer.  Apply
  @{thm [source] m_7_4_RightNodes_Mark} to \<open>N = seg M 0 m1\<close> at column \<open>m0\<close>:
  \<open>RightNodes(Trans(seg M 0 m0))\<close> is a proper prefix of \<open>RightNodes(Trans(seg M 0 m1))\<close>,
  the extra suffix \<open>a1\<close> being nonempty because \<open>m0 < Lng N - 1\<close> makes
  \<open>Mark N m0\<close> have a nonzero tail (@{thm [source] Mark_tail_nonzero}).\<close>

lemma RightNodes_seg_len_strict_mono:
  assumes MR: "M \<in> RT_PS" and m0M: "(M, m0) \<in> Marked"
    and pos: "0 < m0" and lt: "m0 < m1" and m1le: "m1 \<le> Lng M - 1"
  shows "length (RightNodes (Trans (seg M 0 m0)))
       < length (RightNodes (Trans (seg M 0 m1)))"
proof -
  let ?N = "seg M 0 m1"
  have L1: "1 < Lng M" using pos lt m1le by linarith
  have m1ltM: "m1 < Lng M" using m1le L1 by linarith
  have NR: "?N \<in> RT_PS" by (rule seg_0_RT_PS[OF MR m1le])
  have LN: "Lng ?N = Suc m1" by simp
  have Nm0: "(?N, m0) \<in> Marked"
  proof -
    have "(seg M 0 m1, m0 - 0) \<in> Marked"
      by (rule m_6_3_marked_slice[OF m0M]) (use pos lt m1le in auto)
    thus ?thesis by simp
  qed
  have m0ltN: "m0 < Lng ?N - 1" using lt LN by simp
  obtain a0 a1 where
        RT: "RightNodes (Trans ?N) = a0 @ [entry ?N 1 m0] @ a1"
    and Rseg: "RightNodes (Trans (seg ?N 0 m0)) = a0 @ [entry ?N 1 m0]"
    and RMark: "RightNodes (Mark ?N m0) = [entry ?N 1 m0] @ a1"
    using m_7_4_RightNodes_Mark[OF Nm0 NR pos m0ltN] by blast
  have segeq: "seg ?N 0 m0 = seg M 0 m0"
  proof -
    have nN: "?N = take (Suc m1) M" by (rule seg_0_eq_take) (use m1ltM in linarith)
    have "seg ?N 0 m0 = take (Suc m0) ?N"
      by (rule seg_0_eq_take) (use m0ltN LN in linarith)
    also have "\<dots> = take (Suc m0) (take (Suc m1) M)" using nN by simp
    also have "\<dots> = take (Suc m0) M" using lt by (simp add: take_take min_def)
    also have "\<dots> = seg M 0 m0" by (rule seg_0_eq_take[symmetric]) (use m1ltM lt in linarith)
    finally show ?thesis .
  qed
  have a1ne: "a1 \<noteq> []"
  proof -
    have tne: "Mark ?N m0 \<noteq> Dpt (enat (entry ?N 1 m0)) 0\<^sub>B"
      using Mark_tail_nonzero Nm0 NR m0ltN by blast
    have disj: "Mark ?N m0 = 0\<^sub>B \<or> (\<exists>t. Mark ?N m0 = Dpt (enat (entry ?N 1 m0)) t)"
      using Mark_leftend_form Nm0 NR by blast
    have notz: "Mark ?N m0 \<noteq> 0\<^sub>B"
    proof
      assume "Mark ?N m0 = 0\<^sub>B"
      hence "RightNodes (Mark ?N m0) = []" by simp
      thus False using RMark by simp
    qed
    from notz disj obtain t where mk: "Mark ?N m0 = Dpt (enat (entry ?N 1 m0)) t" by blast
    have tne0: "t \<noteq> 0\<^sub>B" using tne mk by auto
    have "RightNodes (Mark ?N m0) = entry ?N 1 m0 # RightNodes t"
      using mk by (simp add: rnsub_RightNodes_Dpt)
    hence "a1 = RightNodes t" using RMark by simp
    moreover have "RightNodes t \<noteq> []" using tne0 by (simp add: rnsub_RightNodes_empty_iff)
    ultimately show ?thesis by simp
  qed
  have e1: "RightNodes (Trans (seg M 0 m0)) = a0 @ [entry ?N 1 m0]"
    using Rseg segeq by simp
  have "length (RightNodes (Trans (seg M 0 m0))) = length a0 + 1" using e1 by simp
  moreover have "length (RightNodes (Trans ?N)) = length a0 + 1 + length a1"
    using RT by simp
  ultimately show ?thesis using a1ne by simp
qed


text \<open>An interior marked image has right-spine length \<open>\<ge> 2\<close> (its tail is
  nonzero by @{thm [source] Mark_tail_nonzero}).\<close>

lemma Mark_interior_RN_ge2:
  assumes MR: "M \<in> RT_PS" and mM: "(M, m) \<in> Marked"
    and pos: "0 < m" and lt: "m < Lng M - 1"
  shows "2 \<le> length (RightNodes (Mark M m))"
proof -
  obtain a0 a1 where RMark: "RightNodes (Mark M m) = [entry M 1 m] @ a1"
    using m_7_4_RightNodes_Mark[OF mM MR pos lt] by blast
  have tne: "Mark M m \<noteq> Dpt (enat (entry M 1 m)) 0\<^sub>B"
    using Mark_tail_nonzero mM MR lt by blast
  have disj: "Mark M m = 0\<^sub>B \<or> (\<exists>t. Mark M m = Dpt (enat (entry M 1 m)) t)"
    using Mark_leftend_form mM MR by blast
  have notz: "Mark M m \<noteq> 0\<^sub>B"
  proof
    assume "Mark M m = 0\<^sub>B"
    hence "RightNodes (Mark M m) = []" by simp
    thus False using RMark by simp
  qed
  from notz disj obtain t where mk: "Mark M m = Dpt (enat (entry M 1 m)) t" by blast
  have tne0: "t \<noteq> 0\<^sub>B" using tne mk by auto
  have "RightNodes (Mark M m) = entry M 1 m # RightNodes t"
    using mk by (simp add: rnsub_RightNodes_Dpt)
  moreover have "RightNodes t \<noteq> []" using tne0 by (simp add: rnsub_RightNodes_empty_iff)
  ultimately show ?thesis by (cases "RightNodes t") auto
qed

text \<open>\<open>Mark\<close> is injective on marked columns \<open>> 0\<close>: for \<open>0 < m0 < m1\<close> the
  right-spine of \<open>Mark M m0\<close> is strictly longer than that of \<open>Mark M m1\<close>
  (interior case by @{thm [source] RightNodes_seg_len_strict_mono}; the
  rightmost case by length \<open>1\<close> vs \<open>\<ge> 2\<close>).\<close>

lemma Mark_distinct:
  assumes MR: "M \<in> RT_PS" and m0M: "(M, m0) \<in> Marked" and m1M: "(M, m1) \<in> Marked"
    and pos: "0 < m0" and lt: "m0 < m1" and m1le: "m1 \<le> Lng M - 1"
  shows "Mark M m0 \<noteq> Mark M m1"
proof -
  have m0lt: "m0 < Lng M - 1" using lt m1le by simp
  have m1pos: "0 < m1" using pos lt by simp
  show ?thesis
  proof (cases "m1 < Lng M - 1")
    case True
    obtain b0 c0 where S0: "RightNodes (Trans (seg M 0 m0)) = b0 @ [entry M 1 m0]"
      and T0: "RightNodes (Trans M) = b0 @ [entry M 1 m0] @ c0"
      and R0: "RightNodes (Mark M m0) = [entry M 1 m0] @ c0"
      using m_7_4_RightNodes_Mark[OF m0M MR pos m0lt] by blast
    obtain b1 c1 where S1: "RightNodes (Trans (seg M 0 m1)) = b1 @ [entry M 1 m1]"
      and T1: "RightNodes (Trans M) = b1 @ [entry M 1 m1] @ c1"
      and R1: "RightNodes (Mark M m1) = [entry M 1 m1] @ c1"
      using m_7_4_RightNodes_Mark[OF m1M MR m1pos True] by blast
    have g: "length (RightNodes (Trans (seg M 0 m0)))
           < length (RightNodes (Trans (seg M 0 m1)))"
      by (rule RightNodes_seg_len_strict_mono[OF MR m0M pos lt m1le])
    have lb: "length b0 < length b1" using g S0 S1 by simp
    have q0: "length (RightNodes (Trans M)) = length b0 + 1 + length c0" using T0 by simp
    have q1: "length (RightNodes (Trans M)) = length b1 + 1 + length c1" using T1 by simp
    have "length c1 < length c0" using q0 q1 lb by linarith
    hence "length (RightNodes (Mark M m1)) < length (RightNodes (Mark M m0))"
      using R0 R1 by simp
    thus ?thesis by auto
  next
    case False
    hence m1eq: "m1 = Lng M - 1" using m1le by simp
    have L1: "1 < Lng M" using m0lt by simp
    have nz: "\<not> zeroT M" using L1 by (auto simp: zeroT_def)
    have "Mark M m1 = Dpt (enat (entry M 1 m1)) 0\<^sub>B"
      using m_7_3_Mark_rightmost1[OF m1M MR nz] m1eq by simp
    hence "length (RightNodes (Mark M m1)) = 1" by (simp add: rnsub_RightNodes_Dpt)
    moreover have "2 \<le> length (RightNodes (Mark M m0))"
      by (rule Mark_interior_RN_ge2[OF MR m0M pos m0lt])
    ultimately show ?thesis by auto
  qed
qed


text \<open>The marked image at a positive column \<open>m > 0\<close> differs from the marked image
  at column \<open>0\<close> (which is \<open>Trans M\<close>, @{thm [source] ra_Mark0_eq_Trans}).  At
  column \<open>0\<close> the sequence is \<open>monoT\<close>, so \<open>RightNodes (Trans M)\<close> has length \<open>\<ge> 2\<close>
  (@{thm [source] Trans_mono_RN_ge2}); for \<open>0 < m\<close> the interior case strictly
  shrinks the right-spine and the rightmost case has length \<open>1\<close>, so they cannot
  coincide.\<close>

lemma Mark0_ne_Mark:
  assumes MR: "M \<in> RT_PS" and m0M: "(M, 0) \<in> Marked" and mM: "(M, m) \<in> Marked"
    and pos: "0 < m"
  shows "Mark M m \<noteq> Trans M"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have le00: "leR M 0 0 (Lng M - 1)" using m0M by (simp add: Marked_def)
  have lem: "leR M 0 m (Lng M - 1)" using mM by (simp add: Marked_def)
  have mlt: "m < Lng M" using lem by (simp add: leR_def le0_def)
  have mle: "m \<le> Lng M - 1" using mlt by linarith
  have L: "1 < Lng M" using pos mlt by linarith
  have nzM: "\<not> zeroT M" using L by (auto simp: zeroT_def)
  have monoM: "monoT M" using nzM le00 by (simp add: monoT_def)
  \<comment> \<open>\<open>Mark M 0 = Trans M\<close>\<close>
  have mk0: "Mark M 0 = Trans M"
    using ra_Mark0_eq_Trans[THEN mp, THEN mp, OF m0M MR] .
  have rnTM: "2 \<le> length (RightNodes (Trans M))"
    by (rule Trans_mono_RN_ge2[OF MR monoM L])
  show ?thesis
  proof (cases "m < Lng M - 1")
    case True
    \<comment> \<open>interior: \<open>RightNodes (Mark M m)\<close> shorter than \<open>RightNodes (Trans M)\<close>\<close>
    obtain a0 a1 where
          RT: "RightNodes (Trans M) = a0 @ [entry M 1 m] @ a1"
      and Sseg: "RightNodes (Trans (seg M 0 m)) = a0 @ [entry M 1 m]"
      and RMark: "RightNodes (Mark M m) = [entry M 1 m] @ a1"
      using m_7_4_RightNodes_Mark[OF mM MR pos True] by blast
    \<comment> \<open>\<open>seg M 0 m\<close> is mono reduced of length \<open>m+1 \<ge> 2\<close>, so its \<open>Trans\<close> has \<open>RightNodes \<ge> 2\<close>\<close>
    have segRT: "seg M 0 m \<in> RT_PS" by (rule seg_0_RT_PS[OF MR mle])
    have segm0: "(seg M 0 m, 0) \<in> Marked"
    proof -
      have "(seg M 0 m, (0::nat) - 0) \<in> Marked"
        by (rule m_6_3_marked_slice[OF m0M]) (use pos mle in auto)
      thus ?thesis by simp
    qed
    have Lseg: "Lng (seg M 0 m) = Suc m" using mlt by simp
    have segL: "1 < Lng (seg M 0 m)" using pos Lseg by simp
    have segnz: "\<not> zeroT (seg M 0 m)" using segL by (auto simp: zeroT_def)
    have segle00: "leR (seg M 0 m) 0 0 (Lng (seg M 0 m) - 1)"
      using segm0 by (simp add: Marked_def)
    have segmono: "monoT (seg M 0 m)" using segnz segle00 by (simp add: monoT_def)
    have rnseg: "2 \<le> length (RightNodes (Trans (seg M 0 m)))"
      by (rule Trans_mono_RN_ge2[OF segRT segmono segL])
    \<comment> \<open>\<open>RightNodes (Trans (seg M 0 m)) = a0 @ [entry M 1 m]\<close>, so \<open>a0 \<noteq> []\<close>\<close>
    have a0ne: "a0 \<noteq> []"
    proof
      assume "a0 = []"
      hence "RightNodes (Trans (seg M 0 m)) = [entry M 1 m]" using Sseg by simp
      thus False using rnseg by simp
    qed
    have lenTM: "length (RightNodes (Trans M)) = length a0 + 1 + length a1"
      using RT by simp
    have lenMark: "length (RightNodes (Mark M m)) = 1 + length a1"
      using RMark by simp
    have "length (RightNodes (Mark M m)) < length (RightNodes (Trans M))"
      using lenTM lenMark a0ne by (cases a0) auto
    thus ?thesis by auto
  next
    case False
    hence meq: "m = Lng M - 1" using mle by simp
    have "Mark M m = Dpt (enat (entry M 1 m)) 0\<^sub>B"
      using m_7_3_Mark_rightmost1[OF mM MR nzM] meq by simp
    hence "length (RightNodes (Mark M m)) = 1" by (simp add: rnsub_RightNodes_Dpt)
    thus ?thesis using rnTM by auto
  qed
qed


text \<open>命題 (§7.4, 訂正 A19): \<open>Mark\<close> preserves the column order.  For marked
  columns \<open>m\<^sub>0, m\<^sub>1\<close>, \<open>m\<^sub>0 < m\<^sub>1\<close> iff the marked images differ and \<open>Mark M m\<^sub>0\<close>
  nests \<open>Mark M m\<^sub>1\<close> in \<open>MarkedB\<close> (pair order \<open>(Mark M m\<^sub>0, Mark M m\<^sub>1)\<close>).\<close>

lemma m_7_4_Mark_order:
  assumes MR: "M \<in> RT_PS" and m0M: "(M, m0) \<in> Marked" and m1M: "(M, m1) \<in> Marked"
  shows "(m0 < m1) \<longleftrightarrow> (Mark M m1 \<noteq> Mark M m0 \<and> (Mark M m0, Mark M m1) \<in> MarkedB)"
proof
  assume lt: "m0 < m1"
  have m0le: "m0 \<le> m1" using lt by simp
  have nest: "(Mark M m0, Mark M m1) \<in> MarkedB"
    using Mark_MarkedB_nest[THEN mp, THEN mp, THEN mp, THEN mp, OF m0M m1M m0le MR] .
  have m1le: "m1 \<le> Lng M - 1"
  proof -
    have "leR M 0 m1 (Lng M - 1)" using m1M by (simp add: Marked_def)
    hence "m1 < Lng M" by (simp add: leR_def le0_def)
    thus ?thesis by linarith
  qed
  have distinct: "Mark M m1 \<noteq> Mark M m0"
  proof (cases "0 < m0")
    case True
    show ?thesis using Mark_distinct[OF MR m0M m1M True lt m1le] by auto
  next
    case False
    hence m00: "m0 = 0" by simp
    have m1pos: "0 < m1" using lt m00 by simp
    have "Mark M m1 \<noteq> Trans M"
      using Mark0_ne_Mark[OF MR _ m1M m1pos] m0M m00 by simp
    moreover have "Mark M m0 = Trans M"
      using ra_Mark0_eq_Trans[THEN mp, THEN mp, OF _ MR] m0M m00 by simp
    ultimately show ?thesis by simp
  qed
  show "Mark M m1 \<noteq> Mark M m0 \<and> (Mark M m0, Mark M m1) \<in> MarkedB"
    using distinct nest by simp
next
  assume H: "Mark M m1 \<noteq> Mark M m0 \<and> (Mark M m0, Mark M m1) \<in> MarkedB"
  have neM: "Mark M m1 \<noteq> Mark M m0" using H by simp
  have nest01: "(Mark M m0, Mark M m1) \<in> MarkedB" using H by simp
  show "m0 < m1"
  proof (rule ccontr)
    assume "\<not> m0 < m1"
    hence m1le0: "m1 \<le> m0" by simp
    have nest10: "(Mark M m1, Mark M m0) \<in> MarkedB"
      using Mark_MarkedB_nest[THEN mp, THEN mp, THEN mp, THEN mp, OF m1M m0M m1le0 MR] .
    have "Mark M m0 = Mark M m1"
      by (rule MarkedB_antisym[OF nest01 nest10])
    thus False using neM by simp
  qed
qed


section \<open>§8.1 補題（公差\<open>(1,1)\<close>のペア数列の\<open>Trans\<close>）, article 2837\<close>

text \<open>Helper: a diagonal segment \<open>diagSeq u v\<close> with \<open>u < v\<close> is mono (\<open>\<not> zeroT\<close>
  and \<open>(0,0) \<le>\<^bsub>M\<^esub> (0, Lng-1)\<close> by row-0 reachability along consecutive steps).\<close>

lemma monoT_diagSeq_lt:
  assumes uv: "u < v"
  shows "monoT (diagSeq u v)"
proof -
  let ?M = "diagSeq u v"
  have L: "Lng ?M = Suc v - u" by simp
  have Lgt1: "1 < Lng ?M" using uv L by simp
  have nz: "\<not> zeroT ?M" using Lgt1 by (simp add: zeroT_def)
  have j1lt: "Lng ?M - 1 < Lng ?M" using Lgt1 by simp
  have j1lt': "Lng ?M - 1 < Suc v - u" using j1lt L by simp
  have rt: "(nextrel0 ?M)\<^sup>*\<^sup>* 0 (Lng ?M - 1)"
    by (rule nextrel0_diagSeq_rtrancl[OF j1lt']) simp
  have "le0 ?M 0 (Lng ?M - 1)" using rt j1lt by (simp add: le0_def)
  hence "leR ?M 0 0 (Lng ?M - 1)" by (simp add: leR_def)
  thus ?thesis using nz by (simp add: monoT_def)
qed

text \<open>Helper: on a diagonal segment, an interior index \<open>0 < j < Lng-1\<close> is
  non-admissible (the row-1 chain links both \<open>j-1 \<to> j\<close> and \<open>j \<to> j+1\<close>).\<close>

lemma nadm_diagSeq_interior:
  assumes j0: "0 < j" and jlt: "j < Lng (diagSeq u v) - 1"
  shows "nadm (diagSeq u v) j"
proof -
  let ?M = "diagSeq u v"
  have L: "Lng ?M = Suc v - u" by simp
  have sjlt: "Suc j < Suc v - u" using jlt L by simp
  have pjlt: "Suc (j - 1) < Suc v - u" using j0 sjlt by simp
  have nx1: "nextR ?M 1 (j - 1) j"
    using nextR1_diagSeq[OF pjlt] j0 by simp
  have nx2: "nextR ?M 1 j (Suc j)" by (rule nextR1_diagSeq[OF sjlt])
  show ?thesis unfolding nadm_def using nx1 nx2 by simp
qed

text \<open>Helper: on a diagonal segment with \<open>u < v\<close>, the row-0 parent of the last
  index \<open>j\<^sub>1 = Lng-1\<close> is \<open>j\<^sub>1 - 1\<close> (the consecutive predecessor).\<close>

lemma parent0_last_diagSeq:
  assumes uv: "u < v"
  shows "parent (diagSeq u v) 0 (Lng (diagSeq u v) - 1) = Lng (diagSeq u v) - 1 - 1"
proof -
  let ?M = "diagSeq u v"
  let ?j1 = "Lng ?M - 1"
  have L: "Lng ?M = Suc v - u" by simp
  have Lgt1: "1 < Lng ?M" using uv L by simp
  have sucj1: "Suc (?j1 - 1) = ?j1" using Lgt1 by simp
  have step: "Suc (?j1 - 1) < Suc v - u" using sucj1 Lgt1 L by simp
  have nr: "nextrel0 ?M (?j1 - 1) ?j1"
    using nextrel0_diagSeq_step[OF step] sucj1 by simp
  have j1lt: "?j1 < Suc v - u" using Lgt1 L by simp
  have uniq: "\<And>j. nextR ?M 0 j ?j1 \<Longrightarrow> j = ?j1 - 1"
  proof -
    fix j assume "nextR ?M 0 j ?j1"
    hence nrj: "nextrel0 ?M j ?j1" by (simp add: nextR_def)
    hence jlt1: "j < ?j1" and jLng: "j < Lng ?M"
      by (auto simp: nextrel0_def)
    show "j = ?j1 - 1"
    proof (rule ccontr)
      assume "j \<noteq> ?j1 - 1"
      hence "j < ?j1 - 1" using jlt1 by simp
      hence mid: "j < ?j1 - 1 \<and> ?j1 - 1 < ?j1" using sucj1 by simp
      \<comment> \<open>\<open>?j1-1\<close> is a strictly-interior index, so the gap-min condition fails\<close>
      have lt: "?j1 - 1 < Suc v - u" using sucj1 j1lt by simp
      have e_mid: "entry ?M 0 (?j1 - 1) = u + (?j1 - 1)"
        using entry_diagSeq[OF lt] by simp
      have e_j1: "entry ?M 0 ?j1 = u + ?j1"
        using entry_diagSeq[OF j1lt] by simp
      have "entry ?M 0 (?j1 - 1) < entry ?M 0 ?j1"
        using e_mid e_j1 sucj1 by simp
      moreover have "entry ?M 0 (?j1 - 1) \<ge> entry ?M 0 ?j1"
        using nrj mid by (simp add: nextrel0_def)
      ultimately show False by simp
    qed
  qed
  have nrR: "nextR ?M 0 (?j1 - 1) ?j1" using nr by (simp add: nextR_def)
  have ex1: "\<exists>!j. nextR ?M 0 j ?j1"
  proof (rule ex1I)
    show "nextR ?M 0 (?j1 - 1) ?j1" by (rule nrR)
  next
    fix j assume "nextR ?M 0 j ?j1"
    thus "j = ?j1 - 1" by (rule uniq)
  qed
  show ?thesis unfolding parent_def
    by (rule the1_equality[OF ex1 nrR])
qed

text \<open>Helper: on a diagonal segment with \<open>u < v\<close>, admissibilizing the parent of
  the last index lands at \<open>0\<close> (\<open>j\<^sub>-\<^sub>1 = 0\<close>): the only admissible index strictly
  below \<open>j\<^sub>1 - 1\<close> is \<open>0\<close> (all interior indices are non-admissible).\<close>

lemma Adm_parent0_last_diagSeq:
  assumes uv: "u < v"
  shows "Adm (diagSeq u v) (Lng (diagSeq u v) - 1 - 1) = 0"
proof -
  let ?M = "diagSeq u v"
  let ?j0 = "Lng ?M - 1 - 1"
  have L: "Lng ?M = Suc v - u" by simp
  have Lgt1: "1 < Lng ?M" using uv L by simp
  have adm0: "adm ?M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
  show ?thesis
  proof (cases "?j0 = 0")
    case True
    show ?thesis using True adm0 by (simp add: Adm_def)
  next
    case False
    hence j0pos: "0 < ?j0" by simp
    have j0lt: "?j0 < Lng ?M - 1" using Lgt1 by simp
    have nadm0: "\<not> adm ?M ?j0"
      using nadm_diagSeq_interior[OF j0pos j0lt] by (simp add: adm_def)
    have Admd: "Adm ?M ?j0 = Max {j'. adm ?M j' \<and> j' < ?j0}"
      using nadm0 by (simp add: Adm_def)
    have fin: "finite {j'. adm ?M j' \<and> j' < ?j0}"
      by (rule finite_subset[of _ "{0..<?j0}"]) auto
    \<comment> \<open>only \<open>0\<close> is admissible below \<open>?j0\<close>: any \<open>0 < j' < ?j0\<close> is interior, hence nadm\<close>
    have only0: "{j'. adm ?M j' \<and> j' < ?j0} = {0}"
    proof (rule set_eqI, rule iffI)
      fix j' assume "j' \<in> {j'. adm ?M j' \<and> j' < ?j0}"
      hence aj: "adm ?M j'" and jl: "j' < ?j0" by auto
      show "j' \<in> {0}"
      proof (rule ccontr)
        assume "j' \<notin> {0}"
        hence j'pos: "0 < j'" by simp
        have "j' < Lng ?M - 1" using jl j0lt by simp
        hence "nadm ?M j'" using nadm_diagSeq_interior[OF j'pos] by simp
        thus False using aj by (simp add: adm_def)
      qed
    next
      fix j' assume "j' \<in> {0::nat}"
      hence "j' = 0" by simp
      thus "j' \<in> {j'. adm ?M j' \<and> j' < ?j0}" using adm0 j0pos by simp
    qed
    show ?thesis using Admd only0 by simp
  qed
qed

text \<open>補題（公差\<open>(1,1)\<close>のペア数列の\<open>Trans\<close>） (§8.1, article 2837): for every
  \<open>u < v\<close>, \<open>Trans (((j,j))\<^bsub>j=u\<^esub>\<^bsup>v\<^esup>) = D\<^sub>u D\<^sub>v 0\<close> \<open>-\<close> independent of \<open>v - u\<close>.
  Induction on \<open>v\<close>; base \<open>v = Suc u\<close> is the two-column case
  (@{thm [source] m_7_3_twoColumn_Trans}); step unfolds the mono branch of
  \<open>Trans\<close> at \<open>j\<^sub>-\<^sub>1 = 0\<close> (so \<open>c\<^sub>1 = Mark (Pred M) 0 = Trans (Pred M)\<close>, the trivial
  scb \<open>s\<^sub>1 = b\<^sub>1 = ()\<close>) under condition (VI), where \<open>c\<^sub>2 = D\<^bsub>v\<^esub>\<^bsup>M\<^esup> D\<^bsub>M\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0
  = D\<^sub>u D\<^sub>v 0\<close>.\<close>

lemma m_8_1_diagSeq_Trans:
  assumes "u < v"
  shows "Trans (diagSeq u v) = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)"
  using assms
proof (induction v)
  case 0
  thus ?case by simp
next
  case (Suc v)
  show ?case
  proof (cases "u = v")
    case True
    \<comment> \<open>base case: \<open>diagSeq u (Suc u)\<close>, a two-column sequence\<close>
    let ?M = "diagSeq u (Suc u)"
    have uSu: "u \<le> Suc u" by simp
    have MR: "?M \<in> RT_PS" by (rule bf_diagSeq_reduced[OF uSu])
    have mono: "monoT ?M" by (rule monoT_diagSeq_lt) simp
    have L2: "Lng ?M = 2" by simp
    have e10: "entry ?M 1 0 = u" by (simp add: entry_diagSeq)
    have e11: "entry ?M 1 1 = Suc u" by (simp add: entry_diagSeq)
    have "Trans ?M = Dpt (enat (entry ?M 1 0)) (Dpt (enat (entry ?M 1 1)) 0\<^sub>B)"
      by (rule m_7_3_twoColumn_Trans[OF MR mono L2])
    thus ?thesis using True e10 e11 by simp
  next
    case False
    hence uv: "u < v" using Suc.prems by simp
    let ?M = "diagSeq u (Suc v)"
    let ?j1 = "Lng ?M - 1"
    have L: "Lng ?M = Suc (Suc v) - u" by simp
    have Lgt1: "1 < Lng ?M" using Suc.prems L by simp
    have Lgt1': "\<not> Lng ?M \<le> Suc 0" using Lgt1 by simp
    have MR: "?M \<in> RT_PS" using uv by (intro bf_diagSeq_reduced) simp
    have MT: "?M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have mono: "monoT ?M" by (rule monoT_diagSeq_lt[OF Suc.prems])
    have domT: "Trans_Mark_dom (Inl ?M)" by (rule m_7_3_Trans_welldef[OF MR])
    \<comment> \<open>\<open>Pred ?M = diagSeq u v\<close>; IH gives \<open>t\<^sub>1 = Trans (Pred ?M) = D\<^sub>u D\<^sub>v 0\<close>\<close>
    have predM: "Pred ?M = diagSeq u v" using uv by (intro Pred_diagSeq_Suc) simp
    have PR: "diagSeq u v \<in> RT_PS" by (rule bf_diagSeq_reduced) (use uv in simp)
    have t1v: "Trans (Pred ?M) = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)"
      using predM Suc.IH[OF uv] by simp
    have t1ne: "Trans (Pred ?M) \<noteq> 0\<^sub>B" using t1v by simp
    \<comment> \<open>structural indices: \<open>j\<^sub>1 = Lng-1\<close>, \<open>j\<^sub>0 = parent = j\<^sub>1-1\<close>, \<open>j\<^sub>-\<^sub>1 = Adm j\<^sub>0 = 0\<close>\<close>
    have jp: "parent ?M 0 ?j1 = ?j1 - 1" by (rule parent0_last_diagSeq[OF Suc.prems])
    have admjp: "Adm ?M (parent ?M 0 ?j1) = 0"
      using jp Adm_parent0_last_diagSeq[OF Suc.prems] by simp
    \<comment> \<open>\<open>c\<^sub>1 = Mark (Pred ?M) 0 = Trans (Pred ?M) = D\<^sub>u D\<^sub>v 0\<close>\<close>
    have predMarked0: "(Pred ?M, 0) \<in> Marked"
    proof -
      have PT: "diagSeq u v \<in> T_PS" using PR by (simp add: RT_PS_def)
      have padm0: "adm (diagSeq u v) 0"
        by (simp add: adm_def nadm_def nextR_def nextrel1_def)
      have pmono: "monoT (diagSeq u v)" by (rule monoT_diagSeq_lt[OF uv])
      have ple: "leR (diagSeq u v) 0 0 (Lng (diagSeq u v) - 1)"
        using pmono by (simp add: monoT_def)
      show ?thesis using PT padm0 ple predM by (simp add: Marked_def)
    qed
    have c1v: "Mark (Pred ?M) (Adm ?M (parent ?M 0 ?j1)) = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)"
    proof -
      have "Mark (Pred ?M) 0 = Trans (Pred ?M)"
        using ra_Mark0_eq_Trans[THEN mp, THEN mp, OF predMarked0] predM PR by simp
      thus ?thesis using admjp t1v by simp
    qed
    \<comment> \<open>scb is trivial: \<open>s\<^sub>1 = b\<^sub>1 = ()\<close> since \<open>c\<^sub>1 = t\<^sub>1\<close>\<close>
    have somev: "(SOME sb. scb_decomp (Trans (Pred ?M)) (fst sb)
                    (flatBT (Dpt (enat u) (Dpt (enat v) 0\<^sub>B))) (snd sb)) = ([], [])"
    proof -
      have pt: "isPTB_str (flatBT (Dpt (enat u) (Dpt (enat v) (0\<^sub>B))))"
        by (rule isPTB_str_Dpt) simp_all
      show ?thesis using scb_SOME_self[OF pt] t1v by simp
    qed
    \<comment> \<open>row-1 entries at \<open>j\<^sub>1\<close> and \<open>j\<^sub>0\<close>\<close>
    have e1j1: "entry ?M 1 ?j1 = Suc v"
      using Lgt1 by (simp add: entry_diagSeq)
    have e1jp: "entry ?M 1 (?j1 - 1) = v"
      using Lgt1 L by (simp add: entry_diagSeq)
    \<comment> \<open>condition (VI) fires: \<open>M\<^bsub>1,j\<^sub>1\<^esub> = Suc v > 0\<close>, \<open>M\<^bsub>1,j\<^sub>0\<^esub>+1 = v+1 = Suc v\<close>,
        and \<open>j\<^sub>0 + 1 = j\<^sub>1\<close>\<close>
    have condVI: "transCondVI ?M"
    proof -
      have a: "entry ?M 1 ?j1 > 0" using e1j1 by simp
      have b: "entry ?M 1 (parent ?M 0 ?j1) + 1 = entry ?M 1 ?j1"
        using jp e1jp e1j1 by simp
      have c: "parent ?M 0 ?j1 + 1 = ?j1" using jp Lgt1 by simp
      show ?thesis unfolding transCondVI_def using a b c by simp
    qed
    have notI: "\<not> (transCondI ?M \<or> transCondIII ?M \<or> transCondV ?M)"
    proof -
      have "\<not> transCondI ?M" using e1j1 by (simp add: transCondI_def)
      moreover have "\<not> transCondV ?M"
        using condVI by (simp add: transCondV_def transCondVI_def)
      moreover have "\<not> transCondIII ?M"
      proof -
        have "entry ?M 1 (parent ?M 0 ?j1) < entry ?M 1 ?j1"
          using jp e1jp e1j1 by simp
        thus ?thesis by (simp add: transCondIII_def)
      qed
      ultimately show ?thesis by blast
    qed
    \<comment> \<open>\<open>v\<^bsup>M\<^esup> = bpHeadV c\<^sub>1 = u\<close>; under (VI) the body \<open>t\<^sub>2\<close> is irrelevant\<close>
    have bvc1: "bpHeadV (Mark (Pred ?M) (Adm ?M (parent ?M 0 ?j1))) = enat u"
      using c1v by simp
    \<comment> \<open>the \<open>j\<^sub>1 = 0\<close> guard is false: \<open>?j\<^sub>1 = Suc v - u > 0\<close>\<close>
    have j1pos: "Lng ?M - 1 \<noteq> 0" using Lgt1 by simp
    have notle: "\<not> Suc v \<le> u" using Suc.prems by simp
    \<comment> \<open>unfold the mono branch of \<open>Trans\<close> via @{thm Trans.psimps}\<close>
    have trans_val: "Trans ?M = unflatBT (flatBT (Dpt (enat u) (Dpt (enat (Suc v)) 0\<^sub>B)))"
      using Trans.psimps[OF domT] MR Lgt1' j1pos notle mono t1ne t1v c1v somev notI condVI
            jp admjp bvc1 e1j1
      by (simp add: Let_def)
    have ufl: "unflatBT (flatBT (Dpt (enat u) (Dpt (enat (Suc v)) 0\<^sub>B)))
               = Dpt (enat u) (Dpt (enat (Suc v)) 0\<^sub>B)"
      by (rule unflatBT_flat)
    show ?thesis using trans_val ufl by simp
  qed
qed


section \<open>§8.1 系（\<open>Pred\<close>が公差\<open>(1,1)\<close>のペア数列の\<open>Trans\<close>）— content.md 2871\<close>

text \<open>Helpers for \<open>M = diagSeq u v @ [(w',w)]\<close> (the article's
  \<open>((j,j))\<^bsub>j=u\<^esub>\<^bsup>v\<^esup> \<oplus> (w',w)\<close>).  \<open>Lng M = Suc v - u + 1\<close>; the diagonal prefix
  carries \<open>entry M i j = u + j\<close> for \<open>j \<le> v - u\<close>, and the appended last column
  \<open>j\<^sub>1 = v - u + 1\<close> has \<open>entry M 0 j\<^sub>1 = w'\<close>, \<open>entry M 1 j\<^sub>1 = w\<close>.\<close>

lemma Lng_diagApp:
  assumes uv: "u \<le> v"
  shows "Lng (diagSeq u v @ [(w', w)]) = Suc v - u + 1"
  using uv by simp

lemma entry_diagApp_lo:
  assumes "j \<le> v - u" and uv: "u \<le> v"
  shows "entry (diagSeq u v @ [(w', w)]) i j = u + j"
proof -
  let ?D = "diagSeq u v"
  have lt: "j < length ?D" using assms by simp
  have aj: "j < Suc v - u" using assms by simp
  have "(?D @ [(w', w)]) ! j = ?D ! j" using lt by (simp add: nth_append)
  also have "\<dots> = (u + j, u + j)" using diagSeq_nth[OF aj] by simp
  finally show ?thesis by (simp add: entry_def)
qed

lemma entry_diagApp_last0:
  assumes uv: "u \<le> v"
  shows "entry (diagSeq u v @ [(w', w)]) 0 (Suc v - u) = w'"
proof -
  let ?D = "diagSeq u v"
  have L: "length ?D = Suc v - u" by simp
  have "(?D @ [(w', w)]) ! (Suc v - u) = [(w', w)] ! 0"
    using L by (simp add: nth_append)
  thus ?thesis by (simp add: entry_def)
qed

lemma entry_diagApp_last1:
  assumes uv: "u \<le> v"
  shows "entry (diagSeq u v @ [(w', w)]) 1 (Suc v - u) = w"
proof -
  let ?D = "diagSeq u v"
  have L: "length ?D = Suc v - u" by simp
  have "(?D @ [(w', w)]) ! (Suc v - u) = [(w', w)] ! 0"
    using L by (simp add: nth_append)
  thus ?thesis by (simp add: entry_def)
qed

lemma Pred_diagApp:
  assumes uv: "u \<le> v"
  shows "Pred (diagSeq u v @ [(w', w)]) = diagSeq u v"
proof -
  have L: "1 < Lng (diagSeq u v @ [(w', w)])" using uv by simp
  have "Pred (diagSeq u v @ [(w', w)]) = butlast (diagSeq u v @ [(w', w)])"
    using L by (simp add: Pred_def)
  thus ?thesis by simp
qed

text \<open>The row-0 nearest ancestor of the last index \<open>j\<^sub>1 = Suc v - u\<close> of
  \<open>M = diagSeq u v @ [(w',w)]\<close> is \<open>w' - u - 1\<close>, uniformly for \<open>u < w' \<le> Suc v\<close>
  (covers all four cases: \<open>w' = v+1\<close> gives \<open>v - u\<close>; \<open>w' \<le> v\<close> gives the prefix
  index whose row-0 value \<open>w'-1\<close> directly precedes \<open>w'\<close>).\<close>

lemma nextrel0_diagApp_parent:
  assumes uv: "u < v" and wlo: "u < w'" and whi: "w' \<le> Suc v"
  shows "nextrel0 (diagSeq u v @ [(w', w)]) (w' - u - 1) (Suc v - u)"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  let ?jp = "w' - u - 1"
  let ?j1 = "Suc v - u"
  have uvle: "u \<le> v" using uv by simp
  have L: "Lng ?M = Suc v - u + 1" using uvle by (rule Lng_diagApp)
  have jplev: "?jp \<le> v - u" using wlo whi by simp
  have jpL: "?jp < Lng ?M" using L jplev by simp
  have j1L: "?j1 < Lng ?M" using L by simp
  have jplt: "?jp < ?j1" using wlo whi by simp
  have e_jp: "entry ?M 0 ?jp = u + ?jp" using jplev uvle by (rule entry_diagApp_lo)
  have e_jp': "entry ?M 0 ?jp = w' - 1" using e_jp wlo by simp
  have e_j1: "entry ?M 0 ?j1 = w'" using uvle entry_diagApp_last0 by simp
  have lt: "entry ?M 0 ?jp < entry ?M 0 ?j1" using e_jp' e_j1 wlo by simp
  have gap: "\<forall>j. ?jp < j \<and> j < ?j1 \<longrightarrow> entry ?M 0 j \<ge> entry ?M 0 ?j1"
  proof (intro allI impI)
    fix j assume jj: "?jp < j \<and> j < ?j1"
    hence jlev: "j \<le> v - u" using uvle by linarith
    have "entry ?M 0 j = u + j" using jlev uvle by (rule entry_diagApp_lo)
    moreover have "u + j \<ge> w'" using jj wlo by linarith
    ultimately show "entry ?M 0 j \<ge> entry ?M 0 ?j1" using e_j1 by simp
  qed
  show ?thesis unfolding nextrel0_def using jpL j1L jplt lt gap by simp
qed

lemma nextR0_diagApp_last_unique:
  assumes uv: "u < v" and wlo: "u < w'" and whi: "w' \<le> Suc v"
    and hp: "nextR (diagSeq u v @ [(w', w)]) 0 j (Suc v - u)"
  shows "j = w' - u - 1"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  let ?jp = "w' - u - 1"
  let ?j1 = "Suc v - u"
  have uvle: "u \<le> v" using uv by simp
  have e_j1: "entry ?M 0 ?j1 = w'" using uvle entry_diagApp_last0 by simp
  have nrj: "nextrel0 ?M j ?j1" using hp by (simp add: nextR_def)
  hence jlt1: "j < ?j1" and elt: "entry ?M 0 j < entry ?M 0 ?j1"
    and noint: "\<forall>j'. j < j' \<and> j' < ?j1 \<longrightarrow> entry ?M 0 j' \<ge> entry ?M 0 ?j1"
    by (auto simp: nextrel0_def)
  have jlev: "j \<le> v - u" using jlt1 uvle by simp
  have ej: "entry ?M 0 j = u + j" using jlev uvle by (rule entry_diagApp_lo)
  have jw: "u + j < w'" using ej elt e_j1 by simp
  show "j = ?jp"
  proof (rule ccontr)
    assume "j \<noteq> ?jp"
    hence "j < ?jp" using jw wlo by simp
    hence mid: "j < ?jp \<and> ?jp < ?j1" using wlo whi by simp
    have jplev: "?jp \<le> v - u" using wlo whi by simp
    have ejp: "entry ?M 0 ?jp = w' - 1"
      using entry_diagApp_lo[where i=0, OF jplev uvle] wlo by simp
    have "entry ?M 0 ?jp < entry ?M 0 ?j1" using ejp e_j1 wlo by simp
    moreover have "entry ?M 0 ?jp \<ge> entry ?M 0 ?j1" using noint mid by simp
    ultimately show False by simp
  qed
qed

lemma parent0_diagApp:
  assumes uv: "u < v" and wlo: "u < w'" and whi: "w' \<le> Suc v"
  shows "parent (diagSeq u v @ [(w', w)]) 0 (Suc v - u) = w' - u - 1"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  let ?jp = "w' - u - 1"
  let ?j1 = "Suc v - u"
  have nr: "nextrel0 ?M ?jp ?j1" by (rule nextrel0_diagApp_parent[OF uv wlo whi])
  have nrR: "nextR ?M 0 ?jp ?j1" using nr by (simp add: nextR_def)
  have ex1: "\<exists>!j. nextR ?M 0 j ?j1"
  proof (rule ex1I)
    show "nextR ?M 0 ?jp ?j1" by (rule nrR)
  next
    fix j assume "nextR ?M 0 j ?j1"
    thus "j = ?jp" by (rule nextR0_diagApp_last_unique[OF uv wlo whi])
  qed
  show ?thesis unfolding parent_def by (rule the1_equality[OF ex1 nrR])
qed

text \<open>Spine row-0 reachability for the append: prefix indices \<open>a \<le> b \<le> v-u\<close> are
  le0-related (the diagonal prefix carries consecutive nextrel0 steps).\<close>

lemma nextrel0_diagApp_step:
  assumes "j < v - u" and uv: "u \<le> v"
  shows "nextrel0 (diagSeq u v @ [(w', w)]) j (Suc j)"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  have L: "Lng ?M = Suc v - u + 1" using uv by (rule Lng_diagApp)
  have sjlt: "Suc j < Lng ?M" using assms L by simp
  have jlt: "j < Lng ?M" using assms L by simp
  have jlev: "j \<le> v - u" using assms by simp
  have sjlev: "Suc j \<le> v - u" using assms by simp
  have ej: "entry ?M 0 j = u + j" using jlev uv by (rule entry_diagApp_lo)
  have esj: "entry ?M 0 (Suc j) = u + Suc j" using sjlev uv by (rule entry_diagApp_lo)
  have noint: "\<forall>j'. j < j' \<and> j' < Suc j \<longrightarrow> entry ?M 0 j' \<ge> entry ?M 0 (Suc j)" by auto
  show ?thesis unfolding nextrel0_def using sjlt jlt ej esj noint by simp
qed

lemma le0_diagApp_prefix:
  assumes ab: "a \<le> b" and bv: "b \<le> v - u" and uv: "u \<le> v"
  shows "le0 (diagSeq u v @ [(w', w)]) a b"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  have L: "Lng ?M = Suc v - u + 1" using uv by (rule Lng_diagApp)
  from ab obtain d where d: "b = a + d" using le_Suc_ex by blast
  have "a + d \<le> v - u \<Longrightarrow> (nextrel0 ?M)\<^sup>*\<^sup>* a (a + d)"
  proof (induction d)
    case 0 show ?case by simp
  next
    case (Suc d)
    have le: "a + d \<le> v - u" using Suc.prems by simp
    have rt: "(nextrel0 ?M)\<^sup>*\<^sup>* a (a + d)" using Suc.IH le by simp
    have lt: "a + d < v - u" using Suc.prems by simp
    have step: "nextrel0 ?M (a + d) (Suc (a + d))"
      using lt uv by (rule nextrel0_diagApp_step)
    show ?case using rt step by (simp add: rtranclp.rtrancl_into_rtrancl)
  qed
  hence rt: "(nextrel0 ?M)\<^sup>*\<^sup>* a b" using bv d by simp
  have aL: "a < Lng ?M" using ab bv L by simp
  have bL: "b < Lng ?M" using bv L by simp
  show ?thesis unfolding le0_def using aL bL rt by simp
qed

text \<open>Confinement of \<open>le0\<close>-predecessors of the last index \<open>j\<^sub>1 = Suc v - u\<close>:
  any \<open>j\<close> with \<open>le0 M j j\<^sub>1\<close> is either \<open>j\<^sub>1\<close> itself or lies on the spine
  (\<open>j \<le> j\<^sub>p = w'-u-1\<close>), since \<open>j\<^sub>p\<close> is the unique immediate row-0 predecessor.\<close>

lemma le0_diagApp_pred_confine:
  assumes uv: "u < v" and wlo: "u < w'" and whi: "w' \<le> Suc v"
    and h: "le0 (diagSeq u v @ [(w', w)]) j (Suc v - u)"
  shows "j \<le> w' - u - 1 \<or> j = Suc v - u"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  let ?jp = "w' - u - 1"
  let ?j1 = "Suc v - u"
  have rt: "(nextrel0 ?M)\<^sup>*\<^sup>* j ?j1" using h by (simp add: le0_def)
  show ?thesis
  proof (cases "j = ?j1")
    case True thus ?thesis by simp
  next
    case False
    \<comment> \<open>strip the last step \<open>a \<rightarrow> j\<^sub>1\<close>; that \<open>a\<close> is the unique parent \<open>j\<^sub>p\<close>\<close>
    from rt show ?thesis
    proof (cases rule: rtranclp.cases)
      case rtrancl_refl
      thus ?thesis using False by simp
    next
      case (rtrancl_into_rtrancl a)
      have aj1: "nextrel0 ?M a ?j1" by (rule rtrancl_into_rtrancl(2))
      have ja: "(nextrel0 ?M)\<^sup>*\<^sup>* j a" by (rule rtrancl_into_rtrancl(1))
      have "nextR ?M 0 a ?j1" using aj1 by (simp add: nextR_def)
      hence "a = ?jp" by (rule nextR0_diagApp_last_unique[OF uv wlo whi])
      hence "(nextrel0 ?M)\<^sup>*\<^sup>* j ?jp" using ja by simp
      hence "j \<le> ?jp" by (rule nextrel0_rtrancl_mono)
      thus ?thesis by simp
    qed
  qed
qed

text \<open>Prefix row-\<open>i\<close> parents are consecutive: for an interior index
  \<open>0 < j\<^sub>1' \<le> v - u\<close>, any row-\<open>i\<close> parent is \<open>j\<^sub>1' - 1\<close>.\<close>

lemma nextR_diagApp_prefix_parent:
  assumes uv: "u < v" and i: "i \<le> 1" and j1lev: "j1' \<le> v - u" and j1pos: "0 < j1'"
    and nx: "nextR (diagSeq u v @ [(w', w)]) i p j1'"
  shows "Suc p = j1'"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  have uvle: "u \<le> v" using uv by simp
  have ej1: "entry ?M i j1' = u + j1'" using j1lev uvle by (rule entry_diagApp_lo)
  consider (r0) "i = 0" | (r1) "i = 1" using i by linarith
  thus ?thesis
  proof cases
    case r0
    have nr0: "nextrel0 ?M p j1'" using nx r0 by (simp add: nextR_def)
    hence lt: "p < j1'"
      and univ: "\<forall>j. p < j \<and> j < j1' \<longrightarrow> entry ?M 0 j \<ge> entry ?M 0 j1'"
      by (auto simp: nextrel0_def)
    show ?thesis
    proof (rule ccontr)
      assume "Suc p \<noteq> j1'"
      hence pm: "p < j1' - 1" using lt by linarith
      have mid: "p < j1' - 1 \<and> j1' - 1 < j1'" using pm j1pos by linarith
      have m1lev: "j1' - 1 \<le> v - u" using j1lev by simp
      have em: "entry ?M 0 (j1' - 1) = u + (j1' - 1)" using m1lev uvle by (rule entry_diagApp_lo)
      have "entry ?M 0 (j1' - 1) < entry ?M 0 j1'" using em ej1 j1pos r0 by simp
      moreover have "entry ?M 0 (j1' - 1) \<ge> entry ?M 0 j1'" using univ mid by blast
      ultimately show False by simp
    qed
  next
    case r1
    have nr1: "nextrel1 ?M p j1'" using nx r1 by (simp add: nextR_def)
    hence lt: "p < j1'"
      and univ: "\<forall>j. p < j \<and> le0 ?M j j1' \<longrightarrow> entry ?M 1 j \<ge> entry ?M 1 j1'"
      by (auto simp: nextrel1_def)
    show ?thesis
    proof (rule ccontr)
      assume "Suc p \<noteq> j1'"
      hence pm: "p < j1' - 1" using lt by linarith
      have m1lev: "j1' - 1 \<le> v - u" using j1lev by simp
      have le0mid: "le0 ?M (j1' - 1) j1'"
        using le0_diagApp_prefix[OF _ j1lev uvle, of "j1' - 1"] by simp
      have mid: "p < j1' - 1 \<and> le0 ?M (j1' - 1) j1'" using pm le0mid by simp
      have em: "entry ?M 1 (j1' - 1) = u + (j1' - 1)" using m1lev uvle by (rule entry_diagApp_lo)
      have "entry ?M 1 (j1' - 1) < entry ?M 1 j1'" using em ej1 j1pos r1 by simp
      moreover have "entry ?M 1 (j1' - 1) \<ge> entry ?M 1 j1'" using univ mid by blast
      ultimately show False by simp
    qed
  qed
qed

text \<open>The last-index row-1 parent (when it exists) is at entry \<open>w - 1\<close>, so
  \<open>RedCondA\<close> at \<open>(1, j\<^sub>1)\<close> holds; this needs \<open>w \<le> w'\<close> (true in all four cases).\<close>

lemma nextR1_diagApp_last:
  assumes uv: "u < v" and wlo: "u < w'" and whi: "w' \<le> Suc v" and wle: "w \<le> w'"
    and nx: "nextR (diagSeq u v @ [(w', w)]) 1 p (Suc v - u)"
  shows "entry (diagSeq u v @ [(w', w)]) 1 p + 1 = w"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  let ?jp = "w' - u - 1"
  let ?j1 = "Suc v - u"
  have uvle: "u \<le> v" using uv by simp
  have ej1: "entry ?M 1 ?j1 = w" using uvle entry_diagApp_last1 by simp
  have nr1: "nextrel1 ?M p ?j1" using nx by (simp add: nextR_def)
  hence lt: "p < ?j1" and elt: "entry ?M 1 p < entry ?M 1 ?j1"
    and le0p: "le0 ?M p ?j1"
    and univ: "\<forall>j. p < j \<and> le0 ?M j ?j1 \<longrightarrow> entry ?M 1 j \<ge> entry ?M 1 ?j1"
    by (auto simp: nextrel1_def)
  \<comment> \<open>\<open>p\<close> is on the spine (\<open>\<le> j\<^sub>p\<close>), so \<open>entry M 1 p = u + p\<close>\<close>
  have pconf: "p \<le> ?jp" using le0_diagApp_pred_confine[OF uv wlo whi le0p] lt by simp
  have plev: "p \<le> v - u" using pconf wlo whi by linarith
  have ep: "entry ?M 1 p = u + p" using plev uvle by (rule entry_diagApp_lo)
  have upw: "u + p < w" using ep elt ej1 by simp
  \<comment> \<open>\<open>p + 1 \<le> w - u \<le> w' - u = j\<^sub>p + 1\<close>, so \<open>p + 1 \<le> j\<^sub>p\<close> or \<open>p = j\<^sub>p\<close>\<close>
  show "entry ?M 1 p + 1 = w"
  proof (cases "Suc p \<le> ?jp")
    case True
    \<comment> \<open>\<open>p+1\<close> is on the spine and reaches \<open>j\<^sub>1\<close>; the univ forces \<open>u + p + 1 \<ge> w\<close>\<close>
    have sple: "Suc p \<le> v - u" using True wlo whi by linarith
    have le0sp_jp: "le0 ?M (Suc p) ?jp"
      using le0_diagApp_prefix[OF True _ uvle] wlo whi by simp
    have jpj1: "nextrel0 ?M ?jp ?j1" by (rule nextrel0_diagApp_parent[OF uv wlo whi])
    have rt_sp_jp: "(nextrel0 ?M)\<^sup>*\<^sup>* (Suc p) ?jp" using le0sp_jp by (simp add: le0_def)
    have rt_sp_j1: "(nextrel0 ?M)\<^sup>*\<^sup>* (Suc p) ?j1"
      using rt_sp_jp jpj1 by (simp add: rtranclp.rtrancl_into_rtrancl)
    have L: "Lng ?M = Suc v - u + 1" using uvle by (rule Lng_diagApp)
    have spL: "Suc p < Lng ?M" using sple L by simp
    have j1L: "?j1 < Lng ?M" using L by simp
    have le0sp: "le0 ?M (Suc p) ?j1" unfolding le0_def using spL j1L rt_sp_j1 by simp
    have esp: "entry ?M 1 (Suc p) = u + Suc p" using sple uvle by (rule entry_diagApp_lo)
    have "entry ?M 1 (Suc p) \<ge> entry ?M 1 ?j1" using univ le0sp by simp
    hence "u + Suc p \<ge> w" using esp ej1 by simp
    thus ?thesis using ep upw by simp
  next
    case False
    hence "p = ?jp" using pconf by simp
    have "entry ?M 1 ?jp = w' - 1"
      using entry_diagApp_lo[of ?jp v u w' w 1] wlo whi uvle by simp
    moreover have "w' - 1 < w" using upw ep \<open>p = ?jp\<close> by simp
    ultimately have "w' \<le> w" using wlo by simp
    hence "w' = w" using wle by simp
    thus ?thesis using ep \<open>p = ?jp\<close> \<open>entry ?M 1 ?jp = w' - 1\<close> wlo by simp
  qed
qed

text \<open>\<open>M = diagSeq u v @ [(w',w)]\<close> satisfies \<open>RedCondA\<close> and \<open>RedCondB\<close>, hence
  (with @{thm [source] m_6_6_reduced_iff_cond}) is reduced.  Hypotheses
  \<open>u < w' \<le> Suc v\<close> and \<open>w \<le> w'\<close> are met by all four cases of the corollary.\<close>

lemma RedCondA_diagApp:
  assumes uv: "u < v" and wlo: "u < w'" and whi: "w' \<le> Suc v" and wle: "w \<le> w'"
  shows "RedCondA (diagSeq u v @ [(w', w)])"
  unfolding RedCondA_def
proof (intro allI impI)
  let ?M = "diagSeq u v @ [(w', w)]"
  let ?j1 = "Suc v - u"
  have uvle: "u \<le> v" using uv by simp
  have L: "Lng ?M = Suc v - u + 1" using uvle by (rule Lng_diagApp)
  fix i j1' assume i: "i \<le> 1" and hp: "hasParent ?M i j1'"
  have exu: "\<exists>!q. nextR ?M i q j1'" using hp by (simp add: hasParent_def)
  have par: "nextR ?M i (parent ?M i j1') j1'"
    unfolding parent_def using exu by (rule theI')
  let ?p = "parent ?M i j1'"
  have j1L: "j1' < Lng ?M"
    using par by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
  have j1le: "j1' \<le> ?j1" using j1L L by simp
  show "entry ?M i ?p + 1 = entry ?M i j1'"
  proof (cases "j1' = ?j1")
    case True
    show ?thesis
    proof (cases "i = 0")
      case True
      \<comment> \<open>row 0 at the last index: parent is \<open>w'-u-1\<close>, entry \<open>w'-1\<close>, \<open>+1 = w'\<close>\<close>
      have "?p = w' - u - 1"
        using nextR0_diagApp_last_unique[OF uv wlo whi] par \<open>j1' = ?j1\<close> True by simp
      moreover have "entry ?M 0 (w' - u - 1) = w' - 1"
        using entry_diagApp_lo[of "w'-u-1" v u w' w 0] wlo whi uvle by simp
      moreover have "entry ?M 0 ?j1 = w'" using uvle entry_diagApp_last0 by simp
      ultimately show ?thesis using \<open>j1' = ?j1\<close> True wlo by simp
    next
      case False
      hence i1: "i = 1" using i by linarith
      have nx: "nextR ?M 1 ?p ?j1" using par \<open>j1' = ?j1\<close> i1 by simp
      have "entry ?M 1 ?p + 1 = w" by (rule nextR1_diagApp_last[OF uv wlo whi wle nx])
      moreover have "entry ?M 1 ?j1 = w" using uvle entry_diagApp_last1 by simp
      ultimately show ?thesis using \<open>j1' = ?j1\<close> i1 by simp
    qed
  next
    case False
    hence j1lt: "j1' < ?j1" using j1le by simp
    hence j1lev: "j1' \<le> v - u" by linarith
    have j1pos: "0 < j1'"
    proof (rule ccontr)
      assume "\<not> 0 < j1'"
      hence "j1' = 0" by simp
      thus False using par by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
    qed
    have suc: "Suc ?p = j1'" by (rule nextR_diagApp_prefix_parent[OF uv i j1lev j1pos par])
    have plev: "?p \<le> v - u" using suc j1lev by linarith
    have ep: "entry ?M i ?p = u + ?p" using plev uvle by (rule entry_diagApp_lo)
    have ej: "entry ?M i j1' = u + j1'" using j1lev uvle by (rule entry_diagApp_lo)
    show ?thesis using ep ej suc by simp
  qed
qed

lemma RedCondB_diagApp:
  assumes uv: "u < v" and wlo: "u < w'" and whi: "w' \<le> Suc v"
  shows "RedCondB (diagSeq u v @ [(w', w)])"
  unfolding RedCondB_def
proof (intro allI impI)
  let ?M = "diagSeq u v @ [(w', w)]"
  let ?j1 = "Suc v - u"
  have uvle: "u \<le> v" using uv by simp
  have L: "Lng ?M = Suc v - u + 1" using uvle by (rule Lng_diagApp)
  fix j1' assume H: "\<not> hasParent ?M 0 j1' \<and> j1' \<le> Lng ?M - 1"
  hence noP: "\<not> hasParent ?M 0 j1'" and hle: "j1' \<le> ?j1" using L by simp_all
  \<comment> \<open>both the last index (parent \<open>w'-u-1\<close>) and any interior \<open>j1' > 0\<close> have a
      unique row-0 parent; so a parentless \<open>j1'\<close> must be \<open>0\<close>\<close>
  have "j1' = 0"
  proof (rule ccontr)
    assume "j1' \<noteq> 0"
    hence j1pos: "0 < j1'" by simp
    show False
    proof (cases "j1' = ?j1")
      case True
      have nr: "nextrel0 ?M (w'-u-1) ?j1" by (rule nextrel0_diagApp_parent[OF uv wlo whi])
      have nx: "nextR ?M 0 (w'-u-1) ?j1" using nr by (simp add: nextR_def)
      have "hasParent ?M 0 ?j1" unfolding hasParent_def
        using nx nextR0_diagApp_last_unique[OF uv wlo whi] by blast
      thus False using noP True by simp
    next
      case False
      hence j1lt: "j1' < ?j1" using hle by simp
      hence j1lev: "j1' \<le> v - u" by linarith
      have m1lt: "j1' - 1 < v - u" using j1lev j1pos by linarith
      have sm1: "Suc (j1' - 1) = j1'" using j1pos by simp
      have step: "nextrel0 ?M (j1' - 1) j1'"
        using nextrel0_diagApp_step[of "j1' - 1" v u w' w, OF m1lt uvle] sm1 by simp
      have nx: "nextR ?M 0 (j1' - 1) j1'" using step by (simp add: nextR_def)
      have uniq: "\<And>q. nextR ?M 0 q j1' \<Longrightarrow> q = j1' - 1"
      proof -
        fix q assume nq: "nextR ?M 0 q j1'"
        have "Suc q = j1'"
          by (rule nextR_diagApp_prefix_parent[OF uv _ j1lev j1pos nq]) simp
        thus "q = j1' - 1" by simp
      qed
      have "hasParent ?M 0 j1'" unfolding hasParent_def using nx uniq by blast
      thus False using noP by simp
    qed
  qed
  thus "entry ?M 0 j1' = entry ?M 1 j1'"
    using entry_diagApp_lo[of 0 v u w' w 0] entry_diagApp_lo[of 0 v u w' w 1] uvle by simp
qed

lemma reduced_diagApp:
  assumes uv: "u < v" and wlo: "u < w'" and whi: "w' \<le> Suc v" and wle: "w \<le> w'"
  shows "diagSeq u v @ [(w', w)] \<in> RT_PS"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  have MT: "?M \<in> T_PS" by (simp add: T_PS_def)
  have A: "RedCondA ?M" by (rule RedCondA_diagApp[OF uv wlo whi wle])
  have B: "RedCondB ?M" by (rule RedCondB_diagApp[OF uv wlo whi])
  show ?thesis using m_6_6_reduced_iff_cond[OF MT] A B by blast
qed

text \<open>\<open>M = diagSeq u v @ [(w',w)]\<close> is mono (the row-0 trunk runs \<open>0 \<to>\<^sup>* j\<^sub>p \<to> j\<^sub>1\<close>).\<close>

text \<open>Index \<open>0\<close> is always admissible (the lower row-1 step \<open>nextR M 1 0 0\<close> is
  impossible, so \<open>0\<close> cannot be non-admissible).\<close>

lemma adm_index0: "adm M 0"
proof -
  have "\<not> nextrel1 M 0 0" by (simp add: nextrel1_def)
  hence "\<not> nextR M 1 (0 - 1) 0" by (simp add: nextR_def)
  thus ?thesis by (simp add: adm_def nadm_def)
qed

text \<open>The last index \<open>Lng M - 1\<close> is always admissible (the upper row-1 step
  \<open>nextR M 1 (Lng M - 1) (Lng M)\<close> is impossible since \<open>Lng M < Lng M\<close>).\<close>

lemma adm_lastindex: "adm M (Lng M - 1)"
proof -
  have nlt: "\<not> (Lng M - 1) + 1 < Lng M" by linarith
  have "\<not> nextrel1 M (Lng M - 1) ((Lng M - 1) + 1)"
    using nlt by (simp add: nextrel1_def)
  hence "\<not> nextR M 1 (Lng M - 1) ((Lng M - 1) + 1)" by (simp add: nextR_def)
  thus ?thesis by (simp add: adm_def nadm_def)
qed

lemma monoT_diagApp:
  assumes uv: "u < v" and wlo: "u < w'" and whi: "w' \<le> Suc v"
  shows "monoT (diagSeq u v @ [(w', w)])"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  let ?jp = "w' - u - 1"
  let ?j1 = "Suc v - u"
  have uvle: "u \<le> v" using uv by simp
  have L: "Lng ?M = Suc v - u + 1" using uvle by (rule Lng_diagApp)
  have Lne1: "Lng ?M \<noteq> 1" using L uv by simp
  have nz: "\<not> zeroT ?M" using Lne1 by (simp add: zeroT_def)
  have jplev: "?jp \<le> v - u" using wlo whi by linarith
  have le0_0jp: "le0 ?M 0 ?jp" by (rule le0_diagApp_prefix[OF _ jplev uvle]) simp
  have rt0jp: "(nextrel0 ?M)\<^sup>*\<^sup>* 0 ?jp" using le0_0jp by (simp add: le0_def)
  have jpj1: "nextrel0 ?M ?jp ?j1" by (rule nextrel0_diagApp_parent[OF uv wlo whi])
  have rt0j1: "(nextrel0 ?M)\<^sup>*\<^sup>* 0 ?j1"
    using rt0jp jpj1 by (simp add: rtranclp.rtrancl_into_rtrancl)
  have j1L: "?j1 < Lng ?M" using L by simp
  have le0: "le0 ?M 0 ?j1" unfolding le0_def using j1L rt0j1 by simp
  have "leR ?M 0 0 (Lng ?M - 1)" using le0 L by (simp add: leR_def)
  thus ?thesis using nz by (simp add: monoT_def)
qed

text \<open>Row-1 consecutive \<open><\<^sup>Next\<close>-step on the diagonal prefix of the append
  (\<open>j + 1 \<le> v - u\<close>).\<close>

lemma nextR1_diagApp_spine:
  assumes j: "Suc j \<le> v - u" and uv: "u \<le> v"
  shows "nextR (diagSeq u v @ [(w', w)]) 1 j (Suc j)"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  have L: "Lng ?M = Suc v - u + 1" using uv by (rule Lng_diagApp)
  have sjL: "Suc j < Lng ?M" using j L by simp
  have jlev: "j \<le> v - u" using j by simp
  have ej: "entry ?M 0 j = u + j" "entry ?M 1 j = u + j" using jlev uv
    by (auto simp: entry_diagApp_lo)
  have esj: "entry ?M 0 (Suc j) = u + Suc j" "entry ?M 1 (Suc j) = u + Suc j" using j uv
    by (auto simp: entry_diagApp_lo)
  show ?thesis by (rule nextR1_consecutive[OF sjL]) (use ej esj in simp_all)
qed

text \<open>Interior spine index \<open>0 < j < v - u\<close> is non-admissible (both row-1 steps).\<close>

lemma nadm_diagApp_interior:
  assumes j0: "0 < j" and jlt: "j < v - u" and uv: "u \<le> v"
  shows "nadm (diagSeq u v @ [(w', w)]) j"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  have nx1: "nextR ?M 1 (j - 1) j"
    using nextR1_diagApp_spine[of "j - 1" v u w' w] j0 jlt uv by simp
  have nx2: "nextR ?M 1 j (Suc j)"
    using nextR1_diagApp_spine[of j v u w' w] jlt uv by simp
  show ?thesis unfolding nadm_def using nx1 nx2 j0 by simp
qed

text \<open>For cases (2)/(3)/(4) (\<open>w' \<le> v\<close>), \<open>Adm M j\<^sub>p = 0\<close> (\<open>j\<^sub>p = w'-u-1\<close> is interior
  or \<open>0\<close>, and below it only \<open>0\<close> is admissible).\<close>

lemma Adm_diagApp_parent_lo:
  assumes uv: "u < v" and wlo: "u < w'" and whi: "w' \<le> v"
  shows "Adm (diagSeq u v @ [(w', w)]) (w' - u - 1) = 0"
proof -
  let ?M = "diagSeq u v @ [(w', w)]"
  let ?jp = "w' - u - 1"
  have uvle: "u \<le> v" using uv by simp
  have adm0: "adm ?M 0" by (rule adm_index0)
  show ?thesis
  proof (cases "?jp = 0")
    case True
    show ?thesis using True adm0 by (simp add: Adm_def)
  next
    case False
    hence jppos: "0 < ?jp" by simp
    have jplt: "?jp < v - u" using wlo whi by linarith
    have nadmjp: "\<not> adm ?M ?jp"
      using nadm_diagApp_interior[OF jppos jplt uvle] by (simp add: adm_def)
    have Admd: "Adm ?M ?jp = Max {j'. adm ?M j' \<and> j' < ?jp}"
      using nadmjp by (simp add: Adm_def)
    have only0: "{j'. adm ?M j' \<and> j' < ?jp} = {0}"
    proof (rule set_eqI, rule iffI)
      fix j' assume "j' \<in> {j'. adm ?M j' \<and> j' < ?jp}"
      hence aj: "adm ?M j'" and jl: "j' < ?jp" by auto
      show "j' \<in> {0}"
      proof (rule ccontr)
        assume "j' \<notin> {0}"
        hence j'pos: "0 < j'" by simp
        have "j' < v - u" using jl jplt by linarith
        hence "nadm ?M j'" using nadm_diagApp_interior[OF j'pos _ uvle] by simp
        thus False using aj by (simp add: adm_def)
      qed
    next
      fix j' assume "j' \<in> {0::nat}"
      thus "j' \<in> {j'. adm ?M j' \<and> j' < ?jp}" using adm0 jppos by simp
    qed
    show ?thesis using Admd only0 by simp
  qed
qed

text \<open>For case (1) (\<open>w' = Suc v\<close>, \<open>u < w \<le> v\<close>), the row-0 parent
  \<open>j\<^sub>p = v - u = j\<^sub>1 - 1\<close> is itself admissible (the step \<open>j\<^sub>p \<to> j\<^sub>1\<close> fails since
  \<open>w \<le> v\<close>), so \<open>Adm M j\<^sub>p = j\<^sub>p\<close>.\<close>

lemma adm_diagApp_parent_hi:
  assumes uv: "u < v" and wle: "w \<le> v"
  shows "adm (diagSeq u v @ [(Suc v, w)]) (v - u)"
proof -
  let ?M = "diagSeq u v @ [(Suc v, w)]"
  let ?jp = "v - u"
  have uvle: "u \<le> v" using uv by simp
  have L: "Lng ?M = Suc v - u + 1" using uvle by (rule Lng_diagApp)
  \<comment> \<open>the step \<open>j\<^sub>p \<to> j\<^sub>p + 1 = j\<^sub>1\<close> fails: \<open>entry M 1 j\<^sub>p = v \<ge> w = entry M 1 j\<^sub>1\<close>\<close>
  have ejp: "entry ?M 1 ?jp = v" using entry_diagApp_lo[of ?jp v u "Suc v" w 1] uvle by simp
  have sjeq: "Suc ?jp = Suc v - u" using uvle by simp
  have ej1: "entry ?M 1 (Suc ?jp) = w"
    using entry_diagApp_last1[OF uvle, of "Suc v" w] sjeq by simp
  have "\<not> nextrel1 ?M ?jp (Suc ?jp)"
  proof
    assume "nextrel1 ?M ?jp (Suc ?jp)"
    hence "entry ?M 1 ?jp < entry ?M 1 (Suc ?jp)" by (simp add: nextrel1_def)
    thus False using ejp ej1 wle by simp
  qed
  hence "\<not> nextR ?M 1 ?jp (Suc ?jp)" by (simp add: nextR_def)
  thus ?thesis by (simp add: adm_def nadm_def)
qed

text \<open>The non-trivial scb-\<open>SOME\<close> for case (1): \<open>t\<^sub>1 = D\<^sub>u (D\<^sub>v 0)\<close> decomposes at
  \<open>c\<^sub>1 = D\<^sub>v 0\<close> with \<open>s\<^sub>1 = [D\<^sub>u]\<close>, \<open>b\<^sub>1 = []\<close>.\<close>

lemma scb_decomp_Du_Dv:
  "scb_decomp (Dpt (enat u) (Dpt (enat v) 0\<^sub>B)) [Dsym (enat u)] (flatBT (Dpt (enat v) 0\<^sub>B)) []"
proof -
  have fl: "flatBT (Dpt (enat u) (Dpt (enat v) 0\<^sub>B))
            = [Dsym (enat u)] @ flatBT (Dpt (enat v) 0\<^sub>B) @ []" by simp
  have pt: "isPTB_str (flatBT (Dpt (enat v) 0\<^sub>B))"
    by (rule isPTB_str_Dpt) simp_all
  show ?thesis unfolding scb_decomp_def using fl pt by simp
qed

lemma scb_SOME_Du_Dv:
  "(SOME sb. scb_decomp (Dpt (enat u) (Dpt (enat v) 0\<^sub>B)) (fst sb)
                (flatBT (Dpt (enat v) 0\<^sub>B)) (snd sb)) = ([Dsym (enat u)], [])"
proof (rule some_equality)
  show "scb_decomp (Dpt (enat u) (Dpt (enat v) 0\<^sub>B)) (fst ([Dsym (enat u)], []))
          (flatBT (Dpt (enat v) 0\<^sub>B)) (snd ([Dsym (enat u)], []))"
    using scb_decomp_Du_Dv by simp
next
  fix sb assume h: "scb_decomp (Dpt (enat u) (Dpt (enat v) 0\<^sub>B)) (fst sb)
                       (flatBT (Dpt (enat v) 0\<^sub>B)) (snd sb)"
  have tne: "Dpt (enat u) (Dpt (enat v) 0\<^sub>B) \<noteq> Trm []" by simp
  have "fst sb = [Dsym (enat u)] \<and> snd sb = []"
    using m_7_2_scb_unique_sb[OF h scb_decomp_Du_Dv tne] by simp
  thus "sb = ([Dsym (enat u)], [])" by (cases sb) auto
qed

text \<open>系（\<open>Pred\<close>が公差\<open>(1,1)\<close>のペア数列の\<open>Trans\<close>の基本性質） (§8.1, article 2871),
  discharging @{thm [source] p_8_1_Pred_diagSeq_Trans}.  For \<open>M = diagSeq u v
  @ [(w',w)]\<close> (mono, reduced) with \<open>Pred M = diagSeq u v\<close> and \<open>t\<^sub>1 = D\<^sub>u D\<^sub>v 0\<close>
  (@{thm [source] m_8_1_diagSeq_Trans}): four cases compute the row-0 parent
  \<open>j\<^sub>p = w'-u-1\<close>, the second basepoint \<open>j\<^sub>-\<^sub>1\<close>, \<open>c\<^sub>1\<close> and the c2-surgery.\<close>

lemma m_8_1_Pred_diagSeq_Trans:
  assumes "u < v"
  shows
    "(w' = v + 1 \<and> u < w \<and> w \<le> v
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) (Dpt (enat w) 0\<^sub>B)))
   \<and> (u < w' \<and> w' \<le> v \<and> w = w'
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B))
   \<and> (u + 1 < w' \<and> w' \<le> v \<and> w < w'
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) 0\<^sub>B
                    +\<^sub>B Dpt (enat (w' - 1)) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B)))
   \<and> (u + 1 = w' \<and> w < w'
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B))"
proof -
  have uv: "u < v" by (rule assms)
  have uvle: "u \<le> v" using uv by simp
  let ?D = "diagSeq u v"
  \<comment> \<open>shared facts about \<open>Pred M = ?D\<close>\<close>
  have PR: "?D \<in> RT_PS" by (rule bf_diagSeq_reduced[OF uvle])
  have PT: "?D \<in> T_PS" using PR by (simp add: RT_PS_def)
  have Pmono: "monoT ?D" by (rule monoT_diagSeq_lt[OF uv])
  have LD: "Lng ?D = Suc v - u" by simp
  have t1v: "Trans ?D = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)" by (rule m_8_1_diagSeq_Trans[OF uv])
  have t1ne: "Trans ?D \<noteq> 0\<^sub>B" using t1v by simp
  \<comment> \<open>left-end basepoint \<open>(?D, 0) \<in> Marked\<close>, value \<open>Trans ?D = D\<^sub>u D\<^sub>v 0\<close>\<close>
  have D0M: "(?D, 0) \<in> Marked"
  proof -
    have padm0: "adm ?D 0" by (rule adm_index0)
    have ple: "leR ?D 0 0 (Lng ?D - 1)" using Pmono by (simp add: monoT_def)
    show ?thesis using PT padm0 ple by (simp add: Marked_def)
  qed
  have mark0: "Mark ?D 0 = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)"
    using ra_Mark0_eq_Trans[THEN mp, THEN mp, OF D0M PR] t1v by simp
  \<comment> \<open>right-end basepoint \<open>(?D, v-u) \<in> Marked\<close>, value \<open>D\<^sub>v 0\<close>\<close>
  have LDne1: "Lng ?D \<noteq> 1" using LD uv by simp
  have nzD: "\<not> zeroT ?D" using LDne1 by (simp add: zeroT_def)
  have DjM: "(?D, Lng ?D - 1) \<in> Marked"
  proof -
    have padm: "adm ?D (Lng ?D - 1)" by (rule adm_lastindex)
    have LDpos: "Lng ?D - 1 < Lng ?D" using LD uv by simp
    have ple: "leR ?D 0 (Lng ?D - 1) (Lng ?D - 1)"
      using LDpos by (simp add: leR_def le0_def)
    show ?thesis using PT padm ple by (simp add: Marked_def)
  qed
  have e1Dj: "entry ?D 1 (Lng ?D - 1) = v" using LD uv by (simp add: entry_diagSeq)
  have markRight: "Mark ?D (Lng ?D - 1) = Dpt (enat v) 0\<^sub>B"
    using Mark_rightmost1_forward[OF PR nzD DjM] e1Dj by simp
  show ?thesis
  proof (intro conjI impI)
    \<comment> \<open>------------------------------------------------------------------ case (1)\<close>
    assume H1: "w' = v + 1 \<and> u < w \<and> w \<le> v"
    hence w'eq: "w' = Suc v" and uw: "u < w" and wv: "w \<le> v" by auto
    let ?M = "?D @ [(w', w)]"
    let ?j1 = "Suc v - u"
    have wlo: "u < w'" using w'eq uv by simp
    have whi: "w' \<le> Suc v" using w'eq by simp
    have wle: "w \<le> w'" using w'eq wv by simp
    have MR: "?M \<in> RT_PS" by (rule reduced_diagApp[OF uv wlo whi wle])
    have MT: "?M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have mono: "monoT ?M" by (rule monoT_diagApp[OF uv wlo whi])
    have domT: "Trans_Mark_dom (Inl ?M)" by (rule m_7_3_Trans_welldef[OF MR])
    have LM: "Lng ?M = Suc v - u + 1" using uvle by (rule Lng_diagApp)
    have Lgt1: "1 < Lng ?M" using LM uv by simp
    have Lgt1': "\<not> Lng ?M \<le> Suc 0" using Lgt1 by simp
    have predM: "Pred ?M = ?D" by (rule Pred_diagApp[OF uvle])
    have j1eq: "Lng ?M - 1 = ?j1" using LM by simp
    \<comment> \<open>parent and second basepoint\<close>
    have jp: "parent ?M 0 (Lng ?M - 1) = w' - u - 1"
      using parent0_diagApp[OF uv wlo whi] j1eq by simp
    have jpval: "w' - u - 1 = v - u" using w'eq by simp
    have admpv: "adm ?M (v - u)"
    proof -
      have "adm (?D @ [(Suc v, w)]) (v - u)" by (rule adm_diagApp_parent_hi[OF uv wv])
      thus ?thesis using w'eq by simp
    qed
    have admjp: "Adm ?M (parent ?M 0 (Lng ?M - 1)) = v - u"
      using admpv jp jpval by (simp add: Adm_def)
    \<comment> \<open>\<open>c\<^sub>1 = Mark (?D) (v-u) = Mark (?D) (Lng ?D - 1) = D\<^sub>v 0\<close>\<close>
    have c1v: "Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1))) = Dpt (enat v) 0\<^sub>B"
    proof -
      have "Mark ?D (v - u) = Dpt (enat v) 0\<^sub>B" using markRight LD by simp
      thus ?thesis using predM admjp by simp
    qed
    have t1vM: "Trans (Pred ?M) = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)" using predM t1v by simp
    have t1neM: "Trans (Pred ?M) \<noteq> 0\<^sub>B" using t1vM by simp
    \<comment> \<open>row-1 entries at \<open>j\<^sub>1\<close>, \<open>j\<^sub>p\<close>\<close>
    have e1j1: "entry ?M 1 (Lng ?M - 1) = w"
      using entry_diagApp_last1[OF uvle] j1eq by simp
    have e1jp: "entry ?M 1 (parent ?M 0 (Lng ?M - 1)) = v"
      using jp jpval entry_diagApp_lo[of "v-u" v u w' w 1] uvle by simp
    \<comment> \<open>condition (III) fires (\<open>w > 0\<close>, \<open>v \<ge> w\<close>, \<open>j\<^sub>p\<close> admissible)\<close>
    have admp: "adm ?M (parent ?M 0 (Lng ?M - 1))" using admpv jp jpval by simp
    have condIII: "transCondIII ?M"
      unfolding transCondIII_def using e1j1 e1jp uw wv admp by simp
    have IorIIIorV: "transCondI ?M \<or> transCondIII ?M \<or> transCondV ?M" using condIII by simp
    \<comment> \<open>\<open>v\<^bsup>M\<^esup> = v\<close>, \<open>t\<^sub>2 = 0\<close>\<close>
    have bvc1: "bpHeadV (Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1)))) = enat v"
      using c1v by simp
    have btc1: "bpHeadT (Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1)))) = 0\<^sub>B"
      using c1v by simp
    \<comment> \<open>scb-\<open>SOME\<close> of \<open>t\<^sub>1 = D\<^sub>u D\<^sub>v 0\<close> at \<open>c\<^sub>1 = D\<^sub>v 0\<close> is \<open>([D\<^sub>u], [])\<close>\<close>
    have somev: "(SOME sb. scb_decomp (Trans (Pred ?M)) (fst sb)
                    (flatBT (Dpt (enat v) 0\<^sub>B)) (snd sb)) = ([Dsym (enat u)], [])"
      using scb_SOME_Du_Dv[of u v] t1vM by simp
    have j1pos: "Lng ?M - 1 \<noteq> 0" using Lgt1 by simp
    have notle: "\<not> w' \<le> u" using wlo by simp
    \<comment> \<open>unfold the mono branch; \<open>c\<^sub>2 = D\<^sub>v (0 + D\<^sub>w 0) = D\<^sub>v (D\<^sub>w 0)\<close>\<close>
    have trans_val: "Trans ?M = unflatBT ([Dsym (enat u)]
                       @ flatBT (Dpt (enat v) (0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B)) @ [])"
      using Trans.psimps[OF domT] MR Lgt1' j1pos mono t1neM c1v somev IorIIIorV
            jp admjp bvc1 btc1 e1j1
      by (simp add: Let_def)
    have flateq: "[Dsym (enat u)] @ flatBT (Dpt (enat v) (0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B)) @ []
            = flatBT (Dpt (enat u) (Dpt (enat v) (Dpt (enat w) 0\<^sub>B)))" by simp
    have "Trans ?M = unflatBT (flatBT (Dpt (enat u) (Dpt (enat v) (Dpt (enat w) 0\<^sub>B))))"
      by (simp only: trans_val flateq)
    thus "Trans ?M = Dpt (enat u) (Dpt (enat v) (Dpt (enat w) 0\<^sub>B))"
      by (simp only: unflatBT_flat)
  next
    \<comment> \<open>------------------------------------------------------------------ case (2)\<close>
    assume H2: "u < w' \<and> w' \<le> v \<and> w = w'"
    hence wlo: "u < w'" and w'v: "w' \<le> v" and ww': "w = w'" by auto
    let ?M = "?D @ [(w', w)]"
    let ?j1 = "Suc v - u"
    have whi: "w' \<le> Suc v" using w'v by simp
    have wle: "w \<le> w'" using ww' by simp
    have MR: "?M \<in> RT_PS" by (rule reduced_diagApp[OF uv wlo whi wle])
    have mono: "monoT ?M" by (rule monoT_diagApp[OF uv wlo whi])
    have domT: "Trans_Mark_dom (Inl ?M)" by (rule m_7_3_Trans_welldef[OF MR])
    have LM: "Lng ?M = Suc v - u + 1" using uvle by (rule Lng_diagApp)
    have Lgt1: "1 < Lng ?M" using LM uv by simp
    have Lgt1': "\<not> Lng ?M \<le> Suc 0" using Lgt1 by simp
    have predM: "Pred ?M = ?D" by (rule Pred_diagApp[OF uvle])
    have j1eq: "Lng ?M - 1 = ?j1" using LM by simp
    have jp: "parent ?M 0 (Lng ?M - 1) = w' - u - 1"
      using parent0_diagApp[OF uv wlo whi] j1eq by simp
    have admjp: "Adm ?M (parent ?M 0 (Lng ?M - 1)) = 0"
      using jp Adm_diagApp_parent_lo[OF uv wlo w'v] by simp
    \<comment> \<open>\<open>c\<^sub>1 = Mark (?D) 0 = D\<^sub>u D\<^sub>v 0\<close>\<close>
    have c1v: "Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1)))
                 = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)"
      using predM admjp mark0 by simp
    have t1vM: "Trans (Pred ?M) = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)" using predM t1v by simp
    have t1neM: "Trans (Pred ?M) \<noteq> 0\<^sub>B" using t1vM by simp
    have e1j1: "entry ?M 1 (Lng ?M - 1) = w" using entry_diagApp_last1[OF uvle] j1eq by simp
    have e1jp: "entry ?M 1 (parent ?M 0 (Lng ?M - 1)) = w' - 1"
      using jp entry_diagApp_lo[of "w'-u-1" v u w' w 1] wlo w'v uvle by simp
    \<comment> \<open>condition (V): \<open>w = w' > 0\<close>, \<open>(w'-1)+1 = w'\<close>, \<open>j\<^sub>p+1 < j\<^sub>1\<close>\<close>
    have condV: "transCondV ?M"
    proof -
      have a: "entry ?M 1 (Lng ?M - 1) > 0" using e1j1 ww' wlo by simp
      have b: "entry ?M 1 (parent ?M 0 (Lng ?M - 1)) + 1 = entry ?M 1 (Lng ?M - 1)"
        using e1jp e1j1 ww' wlo by simp
      have c: "parent ?M 0 (Lng ?M - 1) + 1 < Lng ?M - 1"
        using jp j1eq wlo w'v by linarith
      show ?thesis unfolding transCondV_def using a b c by simp
    qed
    have IorIIIorV: "transCondI ?M \<or> transCondIII ?M \<or> transCondV ?M" using condV by simp
    have bvc1: "bpHeadV (Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1)))) = enat u"
      using c1v by simp
    have btc1: "bpHeadT (Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1)))) = Dpt (enat v) 0\<^sub>B"
      using c1v by simp
    \<comment> \<open>scb-\<open>SOME\<close> is trivial (\<open>c\<^sub>1 = t\<^sub>1\<close>)\<close>
    have somev: "(SOME sb. scb_decomp (Trans (Pred ?M)) (fst sb)
                    (flatBT (Dpt (enat u) (Dpt (enat v) 0\<^sub>B))) (snd sb)) = ([], [])"
    proof -
      have pt: "isPTB_str (flatBT (Dpt (enat u) (Dpt (enat v) 0\<^sub>B)))"
        by (rule isPTB_str_Dpt) simp_all
      show ?thesis using scb_SOME_self[OF pt] t1vM by simp
    qed
    have j1pos: "Lng ?M - 1 \<noteq> 0" using Lgt1 by simp
    have trans_val: "Trans ?M = unflatBT (flatBT
                       (Dpt (enat u) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B)))"
      using Trans.psimps[OF domT] MR Lgt1' j1pos mono t1neM c1v somev IorIIIorV
            jp admjp bvc1 btc1 e1j1
      by (simp add: Let_def)
    show "Trans ?M = Dpt (enat u) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B)"
      by (simp only: trans_val unflatBT_flat)
  next
    \<comment> \<open>------------------------------------------------------------------ case (3)\<close>
    assume H3: "u + 1 < w' \<and> w' \<le> v \<and> w < w'"
    hence wgt: "u + 1 < w'" and w'v: "w' \<le> v" and ww': "w < w'" by auto
    let ?M = "?D @ [(w', w)]"
    let ?j1 = "Suc v - u"
    have wlo: "u < w'" using wgt by simp
    have whi: "w' \<le> Suc v" using w'v by simp
    have wle: "w \<le> w'" using ww' by simp
    have MR: "?M \<in> RT_PS" by (rule reduced_diagApp[OF uv wlo whi wle])
    have mono: "monoT ?M" by (rule monoT_diagApp[OF uv wlo whi])
    have domT: "Trans_Mark_dom (Inl ?M)" by (rule m_7_3_Trans_welldef[OF MR])
    have LM: "Lng ?M = Suc v - u + 1" using uvle by (rule Lng_diagApp)
    have Lgt1: "1 < Lng ?M" using LM uv by simp
    have Lgt1': "\<not> Lng ?M \<le> Suc 0" using Lgt1 by simp
    have predM: "Pred ?M = ?D" by (rule Pred_diagApp[OF uvle])
    have j1eq: "Lng ?M - 1 = ?j1" using LM by simp
    have jp: "parent ?M 0 (Lng ?M - 1) = w' - u - 1"
      using parent0_diagApp[OF uv wlo whi] j1eq by simp
    have admjp: "Adm ?M (parent ?M 0 (Lng ?M - 1)) = 0"
      using jp Adm_diagApp_parent_lo[OF uv wlo w'v] by simp
    have c1v: "Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1)))
                 = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)"
      using predM admjp mark0 by simp
    have t1vM: "Trans (Pred ?M) = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)" using predM t1v by simp
    have t1neM: "Trans (Pred ?M) \<noteq> 0\<^sub>B" using t1vM by simp
    have e1j1: "entry ?M 1 (Lng ?M - 1) = w" using entry_diagApp_last1[OF uvle] j1eq by simp
    have e1jp: "entry ?M 1 (parent ?M 0 (Lng ?M - 1)) = w' - 1"
      using jp entry_diagApp_lo[of "w'-u-1" v u w' w 1] wlo w'v uvle by simp
    \<comment> \<open>none of (I),(III),(V),(VI) fire: \<open>j\<^sub>p\<close> is non-admissible interior and
        \<open>w \<noteq> w'\<close>; the final \<open>else\<close> (with \<open>t\<^sub>2 = D\<^sub>v 0 \<noteq> 0\<close>) applies\<close>
    have jppos: "parent ?M 0 (Lng ?M - 1) > 0" using jp wgt by linarith
    have jplt: "parent ?M 0 (Lng ?M - 1) < v - u" using jp wlo w'v by linarith
    have nadmjp: "\<not> adm ?M (parent ?M 0 (Lng ?M - 1))"
      using nadm_diagApp_interior[OF jppos jplt uvle] by (simp add: adm_def)
    have notI: "\<not> transCondI ?M"
      using nadmjp by (simp add: transCondI_def)
    have notIII: "\<not> transCondIII ?M"
      using nadmjp by (simp add: transCondIII_def)
    have notV: "\<not> transCondV ?M"
      using e1jp e1j1 ww' by (simp add: transCondV_def)
    have notVI: "\<not> transCondVI ?M"
      using e1jp e1j1 ww' by (simp add: transCondVI_def)
    have notIIIV: "\<not> (transCondI ?M \<or> transCondIII ?M \<or> transCondV ?M)"
      using notI notIII notV by simp
    have bvc1: "bpHeadV (Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1)))) = enat u"
      using c1v by simp
    have btc1: "bpHeadT (Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1)))) = Dpt (enat v) 0\<^sub>B"
      using c1v by simp
    \<comment> \<open>\<open>t\<^sub>2 = D\<^sub>v 0\<close>: \<open>J\<^sub>1 = 0\<close>, \<open>pj = D\<^sub>v 0\<close>, \<open>leftDj0 = (v = w'-1) = False\<close>\<close>
    have vne: "enat v \<noteq> enat (entry ?M 1 (parent ?M 0 (Lng ?M - 1)))"
      using e1jp w'v wlo by simp
    have somev: "(SOME sb. scb_decomp (Trans (Pred ?M)) (fst sb)
                    (flatBT (Dpt (enat u) (Dpt (enat v) 0\<^sub>B))) (snd sb)) = ([], [])"
    proof -
      have pt: "isPTB_str (flatBT (Dpt (enat u) (Dpt (enat v) 0\<^sub>B)))"
        by (rule isPTB_str_Dpt) simp_all
      show ?thesis using scb_SOME_self[OF pt] t1vM by simp
    qed
    have j1pos: "Lng ?M - 1 \<noteq> 0" using Lgt1 by simp
    \<comment> \<open>unfold the mono branch; the final-\<open>else\<close> \<open>c\<^sub>2 = D\<^sub>u(D\<^sub>v 0 + D\<^bsub>w'-1\<^esub>(D\<^sub>v 0 + D\<^sub>w 0))\<close>\<close>
    have trans_val: "Trans ?M = unflatBT (flatBT
                       (Dpt (enat u) (Dpt (enat v) 0\<^sub>B
                          +\<^sub>B Dpt (enat (w' - 1)) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B))))"
      using Trans.psimps[OF domT] MR Lgt1' j1pos mono t1neM c1v somev
            notIIIV notVI jp admjp bvc1 btc1 e1j1 e1jp vne
      by (simp add: Let_def PB_def SigmaB_def)
    show "Trans ?M = Dpt (enat u) (Dpt (enat v) 0\<^sub>B
            +\<^sub>B Dpt (enat (w' - 1)) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B))"
      by (simp only: trans_val unflatBT_flat)
  next
    \<comment> \<open>------------------------------------------------------------------ case (4)\<close>
    assume H4: "u + 1 = w' \<and> w < w'"
    hence w'eq: "w' = u + 1" and ww': "w < w'" by auto
    let ?M = "?D @ [(w', w)]"
    let ?j1 = "Suc v - u"
    have wlo: "u < w'" using w'eq by simp
    have whi: "w' \<le> Suc v" using w'eq uvle by simp
    have wle: "w \<le> w'" using ww' by simp
    have wleu: "w \<le> u" using ww' w'eq by simp
    have MR: "?M \<in> RT_PS" by (rule reduced_diagApp[OF uv wlo whi wle])
    have mono: "monoT ?M" by (rule monoT_diagApp[OF uv wlo whi])
    have domT: "Trans_Mark_dom (Inl ?M)" by (rule m_7_3_Trans_welldef[OF MR])
    have LM: "Lng ?M = Suc v - u + 1" using uvle by (rule Lng_diagApp)
    have Lgt1: "1 < Lng ?M" using LM uv by simp
    have Lgt1': "\<not> Lng ?M \<le> Suc 0" using Lgt1 by simp
    have predM: "Pred ?M = ?D" by (rule Pred_diagApp[OF uvle])
    have j1eq: "Lng ?M - 1 = ?j1" using LM by simp
    have jp: "parent ?M 0 (Lng ?M - 1) = 0"
      using parent0_diagApp[OF uv wlo whi] j1eq w'eq by simp
    have admjp: "Adm ?M (parent ?M 0 (Lng ?M - 1)) = 0"
    proof -
      have "adm ?M 0" by (rule adm_index0)
      thus ?thesis using jp by (simp add: Adm_def)
    qed
    have c1v: "Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1)))
                 = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)"
      using predM admjp mark0 by simp
    have t1vM: "Trans (Pred ?M) = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)" using predM t1v by simp
    have t1neM: "Trans (Pred ?M) \<noteq> 0\<^sub>B" using t1vM by simp
    have e1j1: "entry ?M 1 (Lng ?M - 1) = w" using entry_diagApp_last1[OF uvle] j1eq by simp
    have e1jp: "entry ?M 1 (parent ?M 0 (Lng ?M - 1)) = u"
      using jp entry_diagApp_lo[of 0 v u w' w 1] uvle by simp
    have admp0: "adm ?M (parent ?M 0 (Lng ?M - 1))"
      using jp by (simp add: adm_index0)
    \<comment> \<open>condition (I) (\<open>w = 0\<close>) or (III) (\<open>0 < w \<le> u\<close>); both put us in the
        \<open>I \<or> III \<or> V\<close> branch\<close>
    have IorIIIorV: "transCondI ?M \<or> transCondIII ?M \<or> transCondV ?M"
    proof (cases "w = 0")
      case True
      have "transCondI ?M" unfolding transCondI_def using e1j1 True admp0 by simp
      thus ?thesis by simp
    next
      case False
      have "transCondIII ?M" unfolding transCondIII_def
        using e1j1 e1jp False wleu admp0 by simp
      thus ?thesis by simp
    qed
    have bvc1: "bpHeadV (Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1)))) = enat u"
      using c1v by simp
    have btc1: "bpHeadT (Mark (Pred ?M) (Adm ?M (parent ?M 0 (Lng ?M - 1)))) = Dpt (enat v) 0\<^sub>B"
      using c1v by simp
    have somev: "(SOME sb. scb_decomp (Trans (Pred ?M)) (fst sb)
                    (flatBT (Dpt (enat u) (Dpt (enat v) 0\<^sub>B))) (snd sb)) = ([], [])"
    proof -
      have pt: "isPTB_str (flatBT (Dpt (enat u) (Dpt (enat v) 0\<^sub>B)))"
        by (rule isPTB_str_Dpt) simp_all
      show ?thesis using scb_SOME_self[OF pt] t1vM by simp
    qed
    have j1pos: "Lng ?M - 1 \<noteq> 0" using Lgt1 by simp
    have trans_val: "Trans ?M = unflatBT (flatBT
                       (Dpt (enat u) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B)))"
      using Trans.psimps[OF domT] MR Lgt1' j1pos mono t1neM c1v somev IorIIIorV
            jp admjp bvc1 btc1 e1j1
      by (simp add: Let_def)
    show "Trans ?M = Dpt (enat u) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B)"
      by (simp only: trans_val unflatBT_flat)
  qed
qed


section \<open>§8 infra: Trans/Mark of a non-reduced ancestor slice = of its Red\<close>

text \<open>Foundational §8 helpers: an ancestor slice \<open>seg M j0' j1'\<close> equals
  \<open>(IncrFirst^^k)(Red (seg M j0' j1'))\<close> (@{thm [source] m_6_6_ancestor_slice_Red_IncrFirst}),
  and \<open>Trans\<close>/\<open>Mark\<close> are \<open>IncrFirst\<close>-invariant, so \<open>Trans\<close>/\<open>Mark\<close> of the (possibly
  non-reduced) slice coincide with those of its reduced form \<open>Red (seg \<dots>)\<close>, which
  is reduced+mono and computable.  Unblocks §8.1 c1-around parts (1g)/(3)/(4) and
  the §7.4 Mark-Trans representation.\<close>

lemma T_PS_funpow_IncrFirst:
  "M \<in> T_PS \<Longrightarrow> (IncrFirst ^^ k) M \<in> T_PS"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  have "(IncrFirst ^^ k) M \<in> T_PS" using Suc by simp
  hence "IncrFirst ((IncrFirst ^^ k) M) \<in> T_PS" by (simp add: T_PS_def IncrFirst_def)
  thus ?case by simp
qed

lemma Trans_funpow_IncrFirst:
  assumes MT: "M \<in> T_PS" and RR: "Red M \<in> RT_PS"
  shows "Trans ((IncrFirst ^^ k) M) = Trans M"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  let ?N = "(IncrFirst ^^ k) M"
  have NT: "?N \<in> T_PS" using MT by (rule T_PS_funpow_IncrFirst)
  have RN: "Red ?N \<in> RT_PS" using a1_Red_funpow_IncrFirst[OF MT] RR by simp
  have "(IncrFirst ^^ Suc k) M = IncrFirst ?N" by simp
  hence "Trans ((IncrFirst ^^ Suc k) M) = Trans (IncrFirst ?N)" by simp
  also have "\<dots> = Trans ?N" by (rule m_7_3_Trans_IncrFirst[OF NT RN])
  also have "\<dots> = Trans M" using Suc.IH by simp
  finally show ?case .
qed

lemma Mark_funpow_IncrFirst:
  assumes MT: "M \<in> T_PS" and RR: "Red M \<in> RT_PS"
  shows "Mark ((IncrFirst ^^ k) M) m = Mark M m"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  let ?N = "(IncrFirst ^^ k) M"
  have NT: "?N \<in> T_PS" using MT by (rule T_PS_funpow_IncrFirst)
  have RN: "Red ?N \<in> RT_PS" using a1_Red_funpow_IncrFirst[OF MT] RR by simp
  have "(IncrFirst ^^ Suc k) M = IncrFirst ?N" by simp
  hence "Mark ((IncrFirst ^^ Suc k) M) m = Mark (IncrFirst ?N) m" by simp
  also have "\<dots> = Mark ?N m" by (rule m_7_3_Mark_IncrFirst[OF NT RN])
  also have "\<dots> = Mark M m" using Suc.IH by simp
  finally show ?case .
qed

lemma slice_Red_in_RT_PS:
  assumes "M \<in> RT_PS" and "j0' < j1'" and "j1' \<le> Lng M - 1" and "leR M 0 j0' j1'"
  shows "Red (seg M j0' j1') \<in> RT_PS \<and> seg M j0' j1' \<in> T_PS \<and> Red (seg M j0' j1') \<in> T_PS"
proof -
  have segne: "seg M j0' j1' \<noteq> []" using assms(2) by (simp add: seg_def)
  hence segT: "seg M j0' j1' \<in> T_PS" by (simp add: T_PS_def)
  have rel: "Red (Red (seg M j0' j1')) = Red (seg M j0' j1')"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF assms] by simp
  have lng: "Lng (Red (seg M j0' j1')) = Lng (seg M j0' j1')"
    by (rule m_6_5_Lng_Red[OF segT])
  have "0 < Lng (seg M j0' j1')" using segne by (cases "seg M j0' j1'") auto
  hence "0 < Lng (Red (seg M j0' j1'))" using lng by simp
  hence "Red (seg M j0' j1') \<noteq> []" by (cases "Red (seg M j0' j1')") auto
  hence redT: "Red (seg M j0' j1') \<in> T_PS" by (simp add: T_PS_def)
  have "Red (seg M j0' j1') \<in> RT_PS" using redT rel by (simp add: RT_PS_def)
  thus ?thesis using segT redT by simp
qed

lemma Trans_slice_eq_Red:
  assumes "M \<in> RT_PS" and "j0' < j1'" and "j1' \<le> Lng M - 1" and "leR M 0 j0' j1'"
  shows "Trans (seg M j0' j1') = Trans (Red (seg M j0' j1'))"
proof -
  let ?S = "seg M j0' j1'"  let ?N = "Red ?S"
  let ?k = "entry M 0 j0' - entry M 1 j0'"
  have segeq: "?S = (IncrFirst ^^ ?k) ?N"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF assms] by simp
  have NR: "?N \<in> RT_PS" using slice_Red_in_RT_PS[OF assms] by simp
  have NT: "?N \<in> T_PS" using NR by (simp add: RT_PS_def)
  have RN: "Red ?N \<in> RT_PS" using NR by (simp add: RT_PS_def)
  have "Trans ?S = Trans ((IncrFirst ^^ ?k) ?N)" using segeq by simp
  also have "\<dots> = Trans ?N" by (rule Trans_funpow_IncrFirst[OF NT RN])
  finally show ?thesis .
qed

lemma Mark_slice_eq_Red:
  assumes "M \<in> RT_PS" and "j0' < j1'" and "j1' \<le> Lng M - 1" and "leR M 0 j0' j1'"
  shows "Mark (seg M j0' j1') m = Mark (Red (seg M j0' j1')) m"
proof -
  let ?S = "seg M j0' j1'"  let ?N = "Red ?S"
  let ?k = "entry M 0 j0' - entry M 1 j0'"
  have segeq: "?S = (IncrFirst ^^ ?k) ?N"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF assms] by simp
  have NR: "?N \<in> RT_PS" using slice_Red_in_RT_PS[OF assms] by simp
  have NT: "?N \<in> T_PS" using NR by (simp add: RT_PS_def)
  have RN: "Red ?N \<in> RT_PS" using NR by (simp add: RT_PS_def)
  have "Mark ?S m = Mark ((IncrFirst ^^ ?k) ?N) m" using segeq by simp
  also have "\<dots> = Mark ?N m" by (rule Mark_funpow_IncrFirst[OF NT RN])
  finally show ?thesis .
qed


text \<open>§8.1 補題 part(2) (content.md 2933, A20/A21-guarded form): for the unique
  next-parent \<open>j\<^sub>0'\<close> of \<open>j\<^sub>0 = parent M 0 (Lng M - 1)\<close>, with \<open>j\<^sub>-\<^sub>1' = Adm M j\<^sub>0'\<close>,
  we have \<open>j\<^sub>0' \<le> j\<^sub>1 - 2\<close>, \<open>(Pred M, j\<^sub>-\<^sub>1') \<in> Marked\<close> and
  \<open>(seg M j\<^sub>-\<^sub>1' (j\<^sub>1 - 1), j\<^sub>0 - j\<^sub>-\<^sub>1') \<in> Marked\<close>.  Standalone green; the slice
  heredity is @{thm [source] m_6_3_marked_slice}, the \<open>Pred\<close> heredity
  @{thm [source] Marked_Pred}, the admissibility ancestry chain mirrors
  @{thm [source] Marked_Pred_Adm}.\<close>

lemma m_8_1_c1_around_part2:
  fixes M :: pairseq
  defines "j1 \<equiv> Lng M - 1"
  defines "j0 \<equiv> parent M 0 j1"
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and admj0: "adm M j0" and j1gt: "j1 > 1"
    and np: "nextR M 0 j0' j0"
  defines "jm1' \<equiv> Adm M j0'"
  shows "j0' \<le> j1 - 2
       \<and> (Pred M, jm1') \<in> Marked
       \<and> (seg M jm1' (j1 - 1), j0 - jm1') \<in> Marked"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using j1gt by (simp add: j1_def)
  have j1lt: "j1 < Lng M" using L by (simp add: j1_def)
  \<comment> \<open>\<open>j\<^sub>0\<close> is the row-0 parent of \<open>j\<^sub>1\<close>\<close>
  have hp: "hasParent M 0 j1" using monoT_hasParent0_last[OF MT mono L] j1_def by simp
  have parj0: "nextR M 0 j0 j1"
    using hp unfolding hasParent_def j0_def parent_def j1_def by (rule theI')
  have j0ltj1: "j0 < j1" and j0Mleq: "leR M 0 j0 j1"
    using poper_nextR_imp_le0[OF parj0] by simp_all
  have le0j0: "le0 M j0 j1" using j0Mleq by (simp add: leR_def)
  \<comment> \<open>\<open>j\<^sub>0'\<close> is a row-0 ancestor of \<open>j\<^sub>0\<close>, strictly below it\<close>
  have j0'ltj0: "j0' < j0" and j0'Mleq: "leR M 0 j0' j0"
    using poper_nextR_imp_le0[OF np] by simp_all
  have le0j0': "le0 M j0' j0" using j0'Mleq by (simp add: leR_def)
  \<comment> \<open>\<open>j\<^sub>0' \<le> j\<^sub>1 - 2\<close>\<close>
  have j0'leq: "j0' \<le> j1 - 2" using j0'ltj0 j0ltj1 by linarith
  \<comment> \<open>admissibilization \<open>jm1' = Adm M j0' \<le> j0'\<close>, admissible\<close>
  have admA: "adm M jm1'" using jm1'_def by (simp add: adm_Adm_adm)
  have aLe: "jm1' \<le> j0'" using jm1'_def by (simp add: adm_Adm_le)
  have jm1'ltj0: "jm1' < j0" using aLe j0'ltj0 by linarith
  have jm1'ltj1: "jm1' < j1" using jm1'ltj0 j0ltj1 by linarith
  \<comment> \<open>row-1 ancestry \<open>jm1' \<le>\<^sub>1 j\<^sub>0'\<close>, hence \<open>jm1' \<le>\<^sub>0 j\<^sub>0'\<close>, then \<open>\<le>\<^sub>0 j\<^sub>1\<close>\<close>
  have j0'b: "j0' \<le> Lng M - 1" using j0'ltj0 j0ltj1 j1lt j1_def by linarith
  have le1a: "leR M 1 jm1' j0'" using adm_row1_ancestry[OF MT j0'b] jm1'_def by simp
  have le0a: "leR M 0 jm1' j0'" by (rule m_le1_imp_le0[OF le1a])
  have le0aj0: "le0 M jm1' j0"
  proof -
    have "(nextrel0 M)\<^sup>*\<^sup>* jm1' j0'" using le0a by (simp add: leR_def le0_def)
    moreover have "(nextrel0 M)\<^sup>*\<^sup>* j0' j0" using le0j0' by (simp add: le0_def)
    ultimately have "(nextrel0 M)\<^sup>*\<^sup>* jm1' j0" by simp
    moreover have "jm1' < Lng M" using jm1'ltj1 j1lt by linarith
    moreover have "j0 < Lng M" using j0ltj1 j1lt by linarith
    ultimately show ?thesis by (simp add: le0_def)
  qed
  have le0aj1: "le0 M jm1' j1"
    using le0_trans[OF le0aj0 le0j0] by simp
  have leMaj1: "leR M 0 jm1' j1" using le0aj1 by (simp add: leR_def)
  \<comment> \<open>\<open>(M, jm1') \<in> Marked\<close>\<close>
  have markedAj1: "(M, jm1') \<in> Marked"
    using MT admA leMaj1 j1_def by (simp add: Marked_def)
  \<comment> \<open>(Pred M, jm1') \<in> Marked via @{thm Marked_Pred}\<close>
  have predA: "(Pred M, jm1') \<in> Marked"
    using Marked_Pred[OF MT L markedAj1] jm1'ltj1 j1_def by simp
  \<comment> \<open>(M, j0) \<in> Marked, then slice heredity to the segment\<close>
  have markedJ0: "(M, j0) \<in> Marked"
    using MT admj0 j0Mleq j1_def by (simp add: Marked_def)
  have segMk: "(seg M jm1' (j1 - 1), j0 - jm1') \<in> Marked"
  proof (rule m_6_3_marked_slice[OF markedJ0])
    show "jm1' \<le> j0" using jm1'ltj0 by linarith
    show "j0 \<le> j1 - 1" using j0ltj1 by linarith
    show "j1 - 1 \<le> Lng M - 1" using j1_def by simp
  qed
  show ?thesis using j0'leq predA segMk by blast
qed


text \<open>§8.1 補題 part(1), the conjuncts NOT involving the A20-guarded slice
  equality (content.md 2949–2955): \<open>Trans (Pred M) \<noteq> 0\<close>, \<open>condI \<or> condIII\<close>,
  \<open>c\<^sub>1 \<in> T_B\<close> and \<open>c\<^sub>1\<close> principal.  Standalone green.  The guarded conjunct
  \<open>j\<^sub>0 < j\<^sub>1 - 1 \<longrightarrow> Trans (seg M j\<^sub>0 (j\<^sub>1 - 1)) = c\<^sub>1\<close> requires the §7.4 Mark–Trans
  representation \<open>Mark M m = Trans (seg M m (Lng M - 1))\<close> (content.md 2490),
  currently unproven, and is NOT discharged here.\<close>

lemma m_8_1_c1_around_part1_noeq:
  fixes M :: pairseq
  defines "j1 \<equiv> Lng M - 1"
  defines "j0 \<equiv> parent M 0 j1"
  defines "jm1 \<equiv> Adm M j0"
  defines "c1 \<equiv> Mark (Pred M) jm1"
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and admj0: "adm M j0" and j1gt: "j1 > 1"
    and ge: "entry M 1 j0 \<ge> entry M 1 j1"
  shows "Trans (Pred M) \<noteq> 0\<^sub>B
       \<and> (transCondI M \<or> transCondIII M)
       \<and> c1 \<in> T_B \<and> (\<exists>p. c1 = Trm [p])"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using j1gt by (simp add: j1_def)
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using predb by simp
  \<comment> \<open>\<open>j\<^sub>0\<close> is the row-0 parent of \<open>j\<^sub>1 = Lng M - 1\<close>; \<open>adm M j\<^sub>0\<close> gives \<open>jm1 = j\<^sub>0\<close>\<close>
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  have j0eq: "j0 = parent M 0 (Lng M - 1)" by (simp add: j0_def j1_def)
  have jm1eq: "jm1 = j0" using admj0 by (simp add: jm1_def Adm_def)
  \<comment> \<open>(1a) \<open>Trans (Pred M) \<noteq> 0\<close>: \<open>Pred M\<close> is non-zero (\<open>Lng > 1\<close>)\<close>
  have nzPred: "\<not> zeroT (Pred M)"
  proof -
    have "1 < Lng (Pred M)" using LP j1gt j1_def by linarith
    thus ?thesis by (auto simp: zeroT_def)
  qed
  have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B"
    using m_7_3_Trans_zeroT[OF predRT] nzPred by blast
  \<comment> \<open>(1b) condition (I) or (III)\<close>
  have condIorIII: "transCondI M \<or> transCondIII M"
  proof (cases "entry M 1 (Lng M - 1) = 0")
    case True
    have "transCondI M" using True admj0 j0eq by (simp add: transCondI_def)
    thus ?thesis by blast
  next
    case False
    hence pos: "entry M 1 (Lng M - 1) > 0" by simp
    have ge': "entry M 1 (parent M 0 (Lng M - 1)) \<ge> entry M 1 (Lng M - 1)"
      using ge by (simp add: j0_def j1_def)
    have "transCondIII M" using pos ge' admj0 j0eq by (simp add: transCondIII_def)
    thus ?thesis by blast
  qed
  \<comment> \<open>(1c) \<open>c\<^sub>1 = Mark (Pred M) j\<^sub>0\<close> is in \<open>T_B\<close> and principal\<close>
  have markedJ0: "(Pred M, j0) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp] j0eq jm1eq jm1_def by simp
  have c1eq: "c1 = Mark (Pred M) j0" using jm1eq c1_def by simp
  have c1TB: "c1 \<in> T_B"
    using m_7_3_Mark_in_T_B[OF predRT markedJ0] c1eq by simp
  have c1princ: "\<exists>p. c1 = Trm [p]"
    using mark_marked_principal(1)[OF predRT markedJ0 t1ne] c1eq by simp
  show ?thesis using t1ne condIorIII c1TB c1princ by blast
qed


end

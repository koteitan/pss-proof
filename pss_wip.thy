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
        have "q # ps2 = butlast (q # ps2) @ [last (q # ps2)]"
          by (simp add: append_butlast_last_id)
        thus ?thesis by (metis concat_append list.simps(8) list.simps(9)
                               map_append append_Nil2 concat.simps(1) concat.simps(2))
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

end

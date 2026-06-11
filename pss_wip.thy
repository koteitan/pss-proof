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

end

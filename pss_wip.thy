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

end

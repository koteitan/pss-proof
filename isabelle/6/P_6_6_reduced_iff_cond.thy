theory P_6_6_reduced_iff_cond
  imports Frontier_6_070
begin

text \<open>命題（簡約性と係数の関係） — reducedness \<open>\<longleftrightarrow>\<close> conditions (A) and (B).\<close>

text \<open>\<S>6.6 命題（簡約性と係数の関係）— reducedness \<open>\<longleftrightarrow>\<close> conditions (A) and (B).
  The HEADLINE \<open>m_6_6_reduced_iff_cond\<close>: \<open>M \<in> RT_PS \<longleftrightarrow> RedCondA M \<and> RedCondB M\<close> for
  \<open>M \<in> T_PS\<close>.  Combines the GREEN forward direction
  @{thm [source] kst_reduced_imp_condAB_uncond} with the now-unconditional backward
  @{thm [source] fa_kst_condAB_imp_reduced}.  Discharges
  @{text p_6_6_reduced_iff_cond}.\<close>

lemma m_6_6_reduced_iff_cond:
  assumes M: "M \<in> T_PS"
  shows "M \<in> RT_PS \<longleftrightarrow> RedCondA M \<and> RedCondB M"
proof
  assume "M \<in> RT_PS"
  thus "RedCondA M \<and> RedCondB M" by (rule kst_reduced_imp_condAB_uncond)
next
  assume AB: "RedCondA M \<and> RedCondB M"
  hence condA: "RedCondA M" and condB: "RedCondB M" by simp_all
  have "Red M = M" by (rule fa_kst_condAB_imp_reduced[OF M condA condB])
  thus "M \<in> RT_PS" using M by (simp add: RT_PS_def)
qed


lemma p_6_6_reduced_iff_cond:
  assumes "M \<in> T_PS"
  shows "M \<in> RT_PS \<longleftrightarrow> RedCondA M \<and> RedCondB M"
  using assms by (rule m_6_6_reduced_iff_cond)

end

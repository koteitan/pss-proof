theory Support_6_046
  imports Frontier_6_066
begin

text \<open>The GENERAL \<S>6.6 keystone BACKWARD, modulo the two monoT residual
  hypotheses.  When the monoT core and monoT-m10>0 reductions land on HEAD this
  becomes unconditional.  Cites only GREEN facts (no \<open>p_*\<close> stub, no goal
  self-reference).\<close>

text \<open>The GENERAL \<S>6.6 keystone IFF, modulo the same two residual hypotheses.
  Combines the GREEN forward @{thm [source] kst_reduced_imp_condAB_uncond} with the
  conditional backward @{thm [source] kst_condAB_imp_reduced_cond}.\<close>

lemma m_6_6_reduced_iff_cond_cond:
  assumes core:
    "\<And>N. N \<in> T_PS \<Longrightarrow> monoT N \<Longrightarrow> entry N 0 0 = 0 \<Longrightarrow> entry N 1 0 = 0
       \<Longrightarrow> RedCondA N \<Longrightarrow> RedCondB N \<Longrightarrow> Red N = N"
  assumes monoT_m10pos:
    "\<And>N. N \<in> T_PS \<Longrightarrow> monoT N \<Longrightarrow> 0 < entry N 1 0
       \<Longrightarrow> RedCondA N \<Longrightarrow> RedCondB N \<Longrightarrow> Red N = N"
  assumes M: "M \<in> T_PS"
  shows "M \<in> RT_PS \<longleftrightarrow> RedCondA M \<and> RedCondB M"
proof
  assume "M \<in> RT_PS"
  thus "RedCondA M \<and> RedCondB M" by (rule kst_reduced_imp_condAB_uncond)
next
  assume AB: "RedCondA M \<and> RedCondB M"
  hence condA: "RedCondA M" and condB: "RedCondB M" by simp_all
  have "Red M = M"
    by (rule kst_condAB_imp_reduced_cond[OF core monoT_m10pos M condA condB])
  thus "M \<in> RT_PS" using M by (simp add: RT_PS_def)
qed

end

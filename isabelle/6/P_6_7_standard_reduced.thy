theory P_6_7_standard_reduced
  imports Frontier_6_087
begin

subsection \<open>§6.7 標準形\<close>

text \<open>命題（標準形の簡約性） — \<open>ST\<^sub>PS \<subseteq> RT\<^sub>PS\<close>.\<close>

text \<open>§6.7 standard-form reducedness ST_PS \<subseteq> RT_PS (the theorem
  @{thm [source] m_6_7_standard_reduced}), fully discharged: operCA by the
  gate-free @{thm [source] operCA_tiling_full} and operCB by
  @{thm [source] operCB_tiling}.  No sorry anywhere in this chain.\<close>

lemma m_6_7_ST_PS_subseteq_RT_PS: "ST_PS \<subseteq> RT_PS"
  by (rule m_6_7_standard_reduced[OF operCA_tiling_full operCB_tiling])

lemma p_6_7_standard_reduced:
  shows "ST_PS \<subseteq> RT_PS"
  by (rule m_6_7_ST_PS_subseteq_RT_PS)

end

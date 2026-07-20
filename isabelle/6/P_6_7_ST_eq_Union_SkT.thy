theory P_6_7_ST_eq_Union_SkT
  imports Frontier_6_024
begin

text \<open>\<open>ST\<^sub>PS = \<Union>\<^sub>k S\<^sub>kT\<^sub>PS\<close> (\<open>ST\<^sub>PS\<close> の定義に基づく最小性より).\<close>

lemma m_6_7_ST_eq_Union_SkT:
  shows "ST_PS = (\<Union>k. SkT_PS k)"
  using ST_PS_subset_Union_SkT SkT_PS_subset_ST_PS by blast


lemma p_6_7_ST_eq_Union_SkT:
  shows "ST_PS = (\<Union>k. SkT_PS k)"
  by (rule m_6_7_ST_eq_Union_SkT)

end

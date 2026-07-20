theory P_6_7_standard_P_components
  imports Frontier_6_026
begin

text \<open>命題（標準形の単項成分が標準形であること） — \<open>P(M) \<in> S\<^sub>kT\<^sub>PS\<^bsup><\<omega>\<^esup>\<close>.\<close>

lemma m_6_7_standard_P_components:
  \<comment> \<open>m: 命題（標準形の単項成分が標準形であること） (§6.7).
     Discharges p_6_7_standard_P_components.\<close>
  assumes "M \<in> SkT_PS k"
  shows "\<forall>J < Lng (P M). P M ! J \<in> SkT_PS k"
  using assms SkT_P_comp by (metis nth_mem)


lemma p_6_7_standard_P_components:
  assumes "M \<in> SkT_PS k"
  shows "\<forall>J < Lng (P M). P M ! J \<in> SkT_PS k"
  using assms by (rule m_6_7_standard_P_components)

end

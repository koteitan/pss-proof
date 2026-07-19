theory P_6_5_admof_Red
  imports P_6_5_Red_adm
begin

text \<open>系（許容化の\<open>Red\<close>不変性）.\<close>

lemma m_6_5_admof_Red_final:
  assumes M: "M \<in> anchored_slice"
  shows "Adm M j = Adm (Red M) j"
  using m_6_5_adm_Red_eq[OF M] by (simp add: Adm_def)

lemma p_6_5_admof_Red:
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
  shows "Adm M j = Adm (Red M) j"
  using assms by (rule m_6_5_admof_Red_final)

end

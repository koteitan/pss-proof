theory P_6_5_Red_adm
  imports Support_6_071
begin

text \<open>命題（\<open>Red\<close>が許容性を保つこと） — \<open>\<nat>\<^sub>M = \<nat>\<^bsub>Red M\<^esub>\<close>.\<close>

lemma m_6_5_Red_adm_final:
  assumes M: "M \<in> anchored_slice"
  shows "AdmSet M = AdmSet (Red M)"
  using m_6_5_adm_Red_eq[OF M] by (simp add: AdmSet_def)

lemma p_6_5_Red_adm:
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
  shows "AdmSet M = AdmSet (Red M)"
  using assms by (rule m_6_5_Red_adm_final)

end

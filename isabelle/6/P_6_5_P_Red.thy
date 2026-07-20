theory P_6_5_P_Red
  imports Support_6_070
begin

text \<open>系（\<open>P\<close>の\<open>Red\<close>同変性） — \<open>P(Red M) = (Red (P M\<^sub>J))\<^bsub>J\<^esub>\<close>.\<close>

lemma m_6_5_P_Red_final:
  assumes M: "M \<in> anchored_slice"
  shows "P (Red M) = map Red (P M)"
proof -
  have nmu: "\<not> multiT M" by (rule m_6_5_anchored_not_multiT[OF M])
  have PM: "P M = [M]" using nmu by (intro poper_P_nonmulti) simp
  have PR: "P (Red M) = [Red M]"
    using m_6_5_Red_not_multiT[OF M] by (intro poper_P_nonmulti) simp
  show ?thesis by (simp add: PM PR)
qed

lemma p_6_5_P_Red:
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
  shows "P (Red M) = map Red (P M)"
  using assms by (rule m_6_5_P_Red_final)

end

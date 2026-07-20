theory P_6_5_Red_IncrFirst
  imports Support_6_034
begin

text \<open>命題（\<open>Red\<close>の\<open>IncrFirst\<close>不変性）.\<close>

text \<open>m: §6.5 命題（\<open>Red\<close>の\<open>IncrFirst\<close>不変性）— discharges \<open>p_6_5_Red_IncrFirst\<close>.
  The engine reduces every branch of @{thm [source] eng_Red_IncrFirst_modB2} to
  the single \<open>(B2)\<close> instance above.\<close>

lemma m_6_5_Red_IncrFirst:
  assumes MT: "M \<in> T_PS"
  shows "Red (IncrFirst M) = Red M"
proof (rule eng_Red_IncrFirst_modB2[OF _ MT])
  fix X assume XT: "X \<in> T_PS" and mono: "monoT X" and pos: "0 < entry X 1 0"
  show "Red (coreReduce (IncrFirst X)) = Red (coreReduce X)"
    by (rule m_6_5_Red_IncrFirst_B2[OF XT mono pos])
qed


lemma p_6_5_Red_IncrFirst:
  assumes "M \<in> T_PS"
  shows "Red (IncrFirst M) = Red M"
  using assms by (rule m_6_5_Red_IncrFirst)

end

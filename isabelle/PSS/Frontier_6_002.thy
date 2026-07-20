theory Frontier_6_002
  imports P_6_1_le_IncrFirst_inv
begin

section \<open>§6.2 単項性\<close>

text \<open>Helper: a pair sequence in \<open>T_PS\<close> with \<open>Lng M \<noteq> 1\<close> has \<open>Lng M > 1\<close>.\<close>

lemma T_PS_Lng_gt1:
  assumes "M \<in> T_PS" "Lng M \<noteq> 1"
  shows "Lng M > 1"
  using assms by (cases M) (auto simp: T_PS_def)

end

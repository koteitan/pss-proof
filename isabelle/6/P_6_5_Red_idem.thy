theory P_6_5_Red_idem
  imports Frontier_6_055
begin

text \<open>命題（\<open>Red\<close>の冪等性）.\<close>

text \<open>a1: (E) §6.5 命題（\<open>Red\<close>の冪等性）— discharges \<open>p_6_5_Red_idem\<close>.
  On the anchored slice \<open>M\<close> is never \<open>multiT\<close>
  (@{thm [source] idem_anchored_not_multi}), so non-multi idempotency
  (@{thm [source] idem_nonmulti}) applies (\<open>M \<in> T\<^sub>PS\<close> by
  @{thm [source] anchored_slice_imp_T_PS}).\<close>

lemma m_6_5_Red_idem:
  assumes M: "M \<in> anchored_slice"
  shows "Red (Red M) = Red M"
proof -
  have MT: "M \<in> T_PS" by (rule anchored_slice_imp_T_PS[OF M])
  have nmu: "\<not> multiT M" by (rule idem_anchored_not_multi[OF M])
  show ?thesis by (rule idem_nonmulti[OF MT nmu])
qed


lemma p_6_5_Red_idem:
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
  shows "Red (Red M) = Red M"
  using assms by (rule m_6_5_Red_idem)

end

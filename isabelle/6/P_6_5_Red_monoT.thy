theory P_6_5_Red_monoT
  imports P_6_5_Red_le
begin

text \<open>系（\<open>Red\<close>が単項性を保つこと）.\<close>

section \<open>§6.5 系（\<open>Red\<close>が単項性を保つこと）/ 系（\<open>P\<close>の\<open>Red\<close>同変性） — A4 final forms\<close>

text \<open>On \<open>anchored_slice\<close> the \<open>multiT\<close> branch of \<open>Red\<close> is unreachable
  (@{thm [source] m_6_5_anchored_not_multiT}), so both corollaries collapse:
  \<^item> 系（\<open>Red\<close>が単項性を保つこと） \<open>monoT M \<longleftrightarrow> monoT (Red M)\<close>: forward is the
    keystone @{thm [source] m_6_5_Red_preserves_monoT}; backward, \<open>M\<close> is
    \<open>zeroT\<close> or \<open>monoT\<close> and \<open>zeroT\<close> transfers both ways
    (@{thm [source] m_6_5_Red_zeroT}).
  \<^item> 系（\<open>P\<close>の\<open>Red\<close>同変性） \<open>P (Red M) = map Red (P M)\<close>: both \<open>M\<close> and \<open>Red M\<close>
    are non-multi, so both sides are singletons \<open>[Red M]\<close>
    (@{thm [source] poper_P_nonmulti}).\<close>

lemma m_6_5_Red_monoT_final:
  assumes M: "M \<in> anchored_slice"
  shows "monoT M \<longleftrightarrow> monoT (Red M)"
proof -
  have MT: "M \<in> T_PS" by (rule anchored_slice_imp_T_PS[OF M])
  show ?thesis
  proof
    assume mono: "monoT M"
    have "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
    thus "monoT (Red M)" by (rule m_6_5_Red_preserves_monoT)
  next
    assume monoR: "monoT (Red M)"
    have "\<not> zeroT M"
    proof
      assume "zeroT M"
      hence "zeroT (Red M)" using m_6_5_Red_zeroT[OF MT] by simp
      thus False using monoR by (simp add: monoT_def)
    qed
    thus "monoT M" using m_6_5_anchored_zeroT_or_monoT[OF M] by simp
  qed
qed

lemma p_6_5_Red_monoT:
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
  shows "monoT M \<longleftrightarrow> monoT (Red M)"
  using assms by (rule m_6_5_Red_monoT_final)

end

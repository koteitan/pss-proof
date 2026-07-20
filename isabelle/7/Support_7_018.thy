theory Support_7_018
  imports Frontier_7_020
begin

text \<open>The article's well-definedness value-part, as clean corollaries.\<close>

lemma m_7_3_Trans_in_T_B:
  assumes "M \<in> RT_PS"
  shows "Trans M \<in> T_B"
  using Trans_Mark_invariant_aux assms by (simp add: T_B_def)

lemma m_7_3_Mark_in_T_B:
  assumes "M \<in> RT_PS" and "(M, m) \<in> Marked"
  shows "Mark M m \<in> T_B"
  using Trans_Mark_invariant_aux assms by (simp add: T_B_def)

lemma m_7_3_Trans_Mark_MarkedB:
  assumes "M \<in> RT_PS" and "(M, m) \<in> Marked"
  shows "(Trans M, Mark M m) \<in> MarkedB"
  using Trans_Mark_invariant_aux assms by simp


section \<open>§7.3 命題（\<open>Trans\<close>が零項性を保つこと）— content.md 2254\<close>

text \<open>The article states \<open>M \<in> T\<^sub>PS \<Longrightarrow> (zeroT M \<longleftrightarrow> Trans M = 0)\<close>, reducing
  to the reduced case by \<open>Red\<close>-zero-preservation and the \<open>(IncrFirst,Red)\<close>-invariant
  \<open>P\<close>-equivariance.  Since \<open>Trans\<close> is well-defined only on \<open>RT\<^sub>PS\<close> (the A15/A4
  caveat: \<open>Red\<close> idempotency is false on \<open>T\<^sub>PS\<close>), we state it on \<open>RT\<^sub>PS\<close>.
  \<open>\<Longleftarrow>\<close> is the contrapositive of the value invariant's
  \<open>\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<close> conjunct; \<open>\<Longrightarrow>\<close> reduces \<open>M\<close> to \<open>[(0,0)]\<close> via
  @{thm [source] m_6_6_oneColumn} and evaluates @{thm [source] Trans_singleton}.\<close>

lemma m_7_3_Trans_zeroT:
  assumes MR: "M \<in> RT_PS"
  shows "zeroT M \<longleftrightarrow> Trans M = 0\<^sub>B"
proof
  assume z: "zeroT M"
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L1: "Lng M = 1" using z by (simp add: zeroT_def)
  obtain v where Mv: "M = [(v, v)]"
    using m_6_6_oneColumn[OF MT] MR L1 by auto
  have "entry M 1 0 = 0" using z by (simp add: zeroT_def)
  hence "v = 0" using Mv by (simp add: entry_def)
  hence "M = [(0, 0)]" using Mv by simp
  thus "Trans M = 0\<^sub>B" using Trans_singleton[of 0] by simp
next
  assume t: "Trans M = 0\<^sub>B"
  have "\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<^sub>B"
    using Trans_Mark_invariant_aux MR by blast
  thus "zeroT M" using t by blast
qed

end

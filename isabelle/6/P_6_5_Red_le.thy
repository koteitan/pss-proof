theory P_6_5_Red_le
  imports Support_6_069
begin

text \<open>系（直系先祖の\<open>Red\<close>不変性） — \<open>\<le>\<^bsub>M\<^esub>\<close> and \<open>\<le>\<^bsub>Red M\<^esub>\<close> coincide.\<close>

lemma m_6_5_Red_le_final:
  assumes M: "M \<in> anchored_slice"
  shows "leR M i j0 j1 = leR (Red M) i j0 j1"
proof -
  have stdCA: "\<And>S. S \<in> ST_PS \<Longrightarrow> RedCondA S" by (rule stdCA_ST_PS)
  have monoCong: "\<And>N. N \<in> T_PS \<Longrightarrow> RedCondA N \<Longrightarrow> monoT N \<Longrightarrow> congR N (Red N)"
    by (rule m_6_5_congR_self_Red_monoT)
  show ?thesis by (rule m_6_5_Red_le[OF M stdCA monoCong])
qed

lemma p_6_5_Red_le:
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4: false on \<open>T\<^sub>PS\<close>; provisional domain\<close>
  shows "leR M i j0 j1 = leR (Red M) i j0 j1"
  using assms by (rule m_6_5_Red_le_final)

end

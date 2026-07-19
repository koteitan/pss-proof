theory P_6_2_multi_crit_12
  imports P_6_2_multi_crit_23
begin

subsection \<open>§6.2 単項性\<close>

text \<open>命題（複項性の判定条件） — equivalence of: (1) not multi; (2) strict
  increase from the left; (3) \<open>(0,0) \<le>\<^sub>M (0, Lng M - 1)\<close>.\<close>

text \<open>m: 命題（複項性の判定条件） (1)=(2) — discharges @{text p_6_2_multi_crit_12}.\<close>

lemma m_6_2_multi_crit_12:
  assumes "M \<in> T_PS"
  shows "(\<not> multiT M) = (\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j)"
  using m_6_2_not_multi_iff_le[OF assms] m_6_2_multi_crit_23[OF assms] by simp

lemma p_6_2_multi_crit_12:
  assumes "M \<in> T_PS"
  shows "(\<not> multiT M) = (\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j)"
  using assms by (rule m_6_2_multi_crit_12)

end

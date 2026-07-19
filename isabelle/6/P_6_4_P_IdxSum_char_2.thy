theory P_6_4_P_IdxSum_char_2
  imports P_6_4_P_IdxSum_char_1
begin

text \<open>m: 系（\<open>P\<close>と\<open>IdxSum\<close>の合成の特徴付け） (2) — discharges
  @{text p_6_4_P_IdxSum_char_2}.\<close>

lemma m_6_4_P_IdxSum_char_2:
  assumes "M \<in> T_PS" "j \<le> Lng M - 1" "\<not> (\<exists>!j0. nextR M 0 j0 j)"
  shows "\<exists>J. J \<le> Lng (P M) - 1 \<and> j = IdxSum (P M) ! J"
proof -
  have L0: "Lng M \<ge> 1" using assms(1) by (cases M) (auto simp: T_PS_def)
  have jL: "j < Lng M" using assms(2) L0 by simp
  have lmin: "\<forall>j'<j. entry M 0 j' \<ge> entry M 0 j"
    using idxsum_no_parent0_iff[OF assms(1) jL] assms(3) by blast
  obtain J where J: "J < length (P M)" "IdxSum (P M) ! J = j"
    using idxsum_lmin_leftend[OF assms(1) assms(2) lmin] by blast
  have "J \<le> Lng (P M) - 1" using J(1) by simp
  thus ?thesis using J(2) by auto
qed

lemma p_6_4_P_IdxSum_char_2:
  assumes "M \<in> T_PS" "j \<le> Lng M - 1" "\<not> (\<exists>!j0. nextR M 0 j0 j)"
  shows "\<exists>J. J \<le> Lng (P M) - 1 \<and> j = IdxSum (P M) ! J"
  using assms by (rule m_6_4_P_IdxSum_char_2)

end

theory P_6_4_P_IdxSum_char_1
  imports Frontier_6_012
begin

text \<open>系（\<open>P\<close>と\<open>IdxSum\<close>の合成の特徴付け）.\<close>

text \<open>m: 系（\<open>P\<close>と\<open>IdxSum\<close>の合成の特徴付け） (1) — discharges
  @{text p_6_4_P_IdxSum_char_1}.\<close>

lemma m_6_4_P_IdxSum_char_1:
  assumes "M \<in> T_PS" "J \<le> Lng (P M) - 1"
  shows "\<not> (\<exists>!j0. nextR M 0 j0 (IdxSum (P M) ! J))"
proof -
  have ne: "P M \<noteq> []" by (rule P_nonempty)
  hence JL: "J < length (P M)" using assms(2) by (cases "P M") auto
  let ?k = "IdxSum (P M) ! J"
  have lm: "IdxSum (P M) ! J \<le> Lng M - 1
          \<and> (\<forall>j < IdxSum (P M) ! J. entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! J))"
    by (rule idxsum_leftend_lmin[OF assms(1) JL])
  hence krange: "?k \<le> Lng M - 1" and lmin: "\<forall>j<?k. entry M 0 j \<ge> entry M 0 ?k" by blast+
  have L0: "Lng M \<ge> 1" using assms(1) by (cases M) (auto simp: T_PS_def)
  have kL: "?k < Lng M" using krange L0 by simp
  show ?thesis
    using idxsum_no_parent0_iff[OF assms(1) kL] lmin by blast
qed

lemma p_6_4_P_IdxSum_char_1:
  assumes "M \<in> T_PS" "J \<le> Lng (P M) - 1"
  shows "\<not> (\<exists>!j0. nextR M 0 j0 (IdxSum (P M) ! J))"
  using assms by (rule m_6_4_P_IdxSum_char_1)

end

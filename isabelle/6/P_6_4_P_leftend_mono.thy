theory P_6_4_P_leftend_mono
  imports Frontier_6_013
begin

text \<open>命題（\<open>P\<close>の各成分の左端の単調性）.\<close>

text \<open>m: 命題（\<open>P\<close>の各成分の左端の単調性） — discharges
  @{text p_6_4_P_leftend_mono}.\<close>

lemma m_6_4_P_leftend_mono:
  assumes "M \<in> T_PS" "J0' \<le> J1'" "J1' \<le> Lng (P M) - 1"
  shows "entry ((P M) ! J0') 0 0 \<ge> entry ((P M) ! J1') 0 0"
proof -
  let ?Q = "P M"
  have ne: "?Q \<noteq> []" by (rule P_nonempty)
  hence J1L: "J1' < length ?Q" using assms(3) by (cases ?Q) auto
  have J0L: "J0' < length ?Q" using assms(2) J1L by simp
  have J0le: "J0' \<le> Lng ?Q - 1" using assms(2,3) by simp
  let ?a0 = "IdxSum ?Q ! J0'"
  let ?a1 = "IdxSum ?Q ! J1'"
  \<comment> \<open>component left ends are the IdxSum values\<close>
  have seg0: "?Q ! J0' = seg M ?a0 (IdxSum ?Q ! (J0' + 1) - 1)"
    by (rule m_6_4_P_IdxSum[OF assms(1) J0le])
  have seg1: "?Q ! J1' = seg M ?a1 (IdxSum ?Q ! (J1' + 1) - 1)"
    by (rule m_6_4_P_IdxSum[OF assms(1) assms(3)])
  \<comment> \<open>each component is non-empty, so its 0-th entry is \<open>entry M 0 (left end)\<close>\<close>
  have len0: "0 < Lng (?Q ! J0')"
    by (rule idxsum_P_component_nonempty[OF assms(1) J0L])
  have len1: "0 < Lng (?Q ! J1')"
    by (rule idxsum_P_component_nonempty[OF assms(1) J1L])
  have e0: "entry (?Q ! J0') 0 0 = entry M 0 ?a0"
  proof -
    have "0 < Lng (seg M ?a0 (IdxSum ?Q ! (J0' + 1) - 1))"
      using len0 seg0 by simp
    hence "entry (seg M ?a0 (IdxSum ?Q ! (J0' + 1) - 1)) 0 0 = entry M 0 ?a0"
      by (subst entry_seg) auto
    thus ?thesis using seg0 by simp
  qed
  have e1: "entry (?Q ! J1') 0 0 = entry M 0 ?a1"
  proof -
    have "0 < Lng (seg M ?a1 (IdxSum ?Q ! (J1' + 1) - 1))"
      using len1 seg1 by simp
    hence "entry (seg M ?a1 (IdxSum ?Q ! (J1' + 1) - 1)) 0 0 = entry M 0 ?a1"
      by (subst entry_seg) auto
    thus ?thesis using seg1 by simp
  qed
  \<comment> \<open>\<open>?a1\<close> is a row-0 left-minimum and \<open>?a0 \<le> ?a1\<close>\<close>
  have lm1: "IdxSum ?Q ! J1' \<le> Lng M - 1
           \<and> (\<forall>j < IdxSum ?Q ! J1'. entry M 0 j \<ge> entry M 0 (IdxSum ?Q ! J1'))"
    by (rule idxsum_leftend_lmin[OF assms(1) J1L])
  hence lmin1: "\<forall>j < ?a1. entry M 0 j \<ge> entry M 0 ?a1" by blast
  have mono: "?a0 \<le> ?a1"
    by (rule idxsum_mono[OF assms(2) less_imp_le_nat[OF J1L]])
  show ?thesis
  proof (cases "?a0 = ?a1")
    case True
    thus ?thesis using e0 e1 by simp
  next
    case False
    with mono have "?a0 < ?a1" by simp
    hence "entry M 0 ?a0 \<ge> entry M 0 ?a1" using lmin1 by blast
    thus ?thesis using e0 e1 by simp
  qed
qed


lemma p_6_4_P_leftend_mono:
  assumes "M \<in> T_PS" "J0' \<le> J1'" "J1' \<le> Lng (P M) - 1"
  shows "entry ((P M) ! J0') 0 0 \<ge> entry ((P M) ! J1') 0 0"
  using assms by (rule m_6_4_P_leftend_mono)

end

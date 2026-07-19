theory P_6_2_mono_ancestor_slice
  imports Frontier_6_003
begin

text \<open>命題（単項性の直系先祖による切片への遺伝性） — an ancestor slice is mono.\<close>

text \<open>m: 命題（単項性の直系先祖による切片への遺伝性） — discharges
  @{text p_6_2_mono_ancestor_slice}.\<close>

lemma m_6_2_mono_ancestor_slice:
  assumes "M \<in> T_PS" "j0' < j1'" "leR M 0 j0' j1'"
  shows "monoT (seg M j0' j1')"
proof -
  let ?M' = "seg M j0' j1'"
  have LM'gt1: "Lng ?M' > 1" using assms(2) by simp
  have lne: "Lng ?M' \<noteq> 0" using assms(2) by simp
  have M'TPS: "?M' \<in> T_PS" using lne by (cases ?M') (auto simp: T_PS_def)
  have notzero: "\<not> zeroT ?M'" using LM'gt1 by (auto simp: zeroT_def)
  have "leR ?M' 0 0 (Lng ?M' - 1)"
  proof (rule m_5_1_parent_exists_3[OF M'TPS])
    show "0 < Lng ?M' - 1" using LM'gt1 by simp
    show "Lng ?M' - 1 < Lng ?M'" using LM'gt1 by simp
    fix j assume "0 < j" "j \<le> Lng ?M' - 1"
    hence jlt: "j < Lng ?M'" using LM'gt1 by simp
    have e0: "entry ?M' 0 0 = entry M 0 j0'" using LM'gt1 by (simp add: entry_seg)
    have ej: "entry ?M' 0 j = entry M 0 (j0' + j)" using jlt by (simp add: entry_seg)
    have "entry M 0 j0' < entry M 0 (j0' + j)"
    proof (rule m_5_1_ancestor_basic_1[OF assms(1) _ _ assms(3)])
      show "j0' < j0' + j" using \<open>0 < j\<close> by simp
      show "j0' + j \<le> j1'" using \<open>j \<le> Lng ?M' - 1\<close> assms(2) by simp
    qed
    thus "entry ?M' 0 0 < entry ?M' 0 j" using e0 ej by simp
  qed
  thus ?thesis using notzero by (simp add: monoT_def)
qed

lemma p_6_2_mono_ancestor_slice:
  assumes "M \<in> T_PS" "j0' < j1'" "leR M 0 j0' j1'"
  shows "monoT (seg M j0' j1')"
  using assms by (rule m_6_2_mono_ancestor_slice)

end

theory P_6_2_mono_prefix
  imports P_6_2_mono_ancestor_slice
begin

text \<open>系（単項性の始切片への遺伝性） — a proper initial slice of a mono is mono.\<close>

text \<open>m: 系（単項性の始切片への遺伝性） — discharges @{text p_6_2_mono_prefix}.\<close>

lemma m_6_2_mono_prefix:
  assumes "M \<in> PT_PS" "0 < j0" "j0 < Lng M"
  shows "monoT (seg M 0 j0)"
proof -
  have MT: "M \<in> T_PS" and mono: "monoT M" using assms(1) by (simp_all add: PT_PS_def)
  have "\<not> multiT M" using mono by (simp add: multiT_def)
  hence le: "leR M 0 0 (Lng M - 1)" using m_6_2_not_multi_iff_le[OF MT] by simp
  have "leR M 0 0 j0"
  proof (rule m_5_1_ancestor_tree_1[OF MT le])
    show "0 \<le> j0" by simp
    show "j0 \<le> Lng M - 1" using assms(3) by simp
  qed
  thus ?thesis by (rule m_6_2_mono_ancestor_slice[OF MT assms(2)])
qed

lemma p_6_2_mono_prefix:
  assumes "M \<in> PT_PS" "0 < j0" "j0 < Lng M"
  shows "monoT (seg M 0 j0)"
  using assms by (rule m_6_2_mono_prefix)

end

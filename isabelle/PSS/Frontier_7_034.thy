theory Frontier_7_034
  imports Support_7_028
begin

lemma slice_Red_in_RT_PS:
  assumes "M \<in> RT_PS" and "j0' < j1'" and "j1' \<le> Lng M - 1" and "leR M 0 j0' j1'"
  shows "Red (seg M j0' j1') \<in> RT_PS \<and> seg M j0' j1' \<in> T_PS \<and> Red (seg M j0' j1') \<in> T_PS"
proof -
  have segne: "seg M j0' j1' \<noteq> []" using assms(2) by (simp add: seg_def)
  hence segT: "seg M j0' j1' \<in> T_PS" by (simp add: T_PS_def)
  have rel: "Red (Red (seg M j0' j1')) = Red (seg M j0' j1')"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF assms] by simp
  have lng: "Lng (Red (seg M j0' j1')) = Lng (seg M j0' j1')"
    by (rule m_6_5_Lng_Red[OF segT])
  have "0 < Lng (seg M j0' j1')" using segne by (cases "seg M j0' j1'") auto
  hence "0 < Lng (Red (seg M j0' j1'))" using lng by simp
  hence "Red (seg M j0' j1') \<noteq> []" by (cases "Red (seg M j0' j1')") auto
  hence redT: "Red (seg M j0' j1') \<in> T_PS" by (simp add: T_PS_def)
  have "Red (seg M j0' j1') \<in> RT_PS" using redT rel by (simp add: RT_PS_def)
  thus ?thesis using segT redT by simp
qed

lemma Trans_slice_eq_Red:
  assumes "M \<in> RT_PS" and "j0' < j1'" and "j1' \<le> Lng M - 1" and "leR M 0 j0' j1'"
  shows "Trans (seg M j0' j1') = Trans (Red (seg M j0' j1'))"
proof -
  let ?S = "seg M j0' j1'"  let ?N = "Red ?S"
  let ?k = "entry M 0 j0' - entry M 1 j0'"
  have segeq: "?S = (IncrFirst ^^ ?k) ?N"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF assms] by simp
  have NR: "?N \<in> RT_PS" using slice_Red_in_RT_PS[OF assms] by simp
  have NT: "?N \<in> T_PS" using NR by (simp add: RT_PS_def)
  have RN: "Red ?N \<in> RT_PS" using NR by (simp add: RT_PS_def)
  have "Trans ?S = Trans ((IncrFirst ^^ ?k) ?N)" using segeq by simp
  also have "\<dots> = Trans ?N" by (rule Trans_funpow_IncrFirst[OF NT RN])
  finally show ?thesis .
qed

end

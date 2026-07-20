theory P_6_7_standard_prefix
  imports Support_6_008
begin

text \<open>命題（標準形の始切片への遺伝性）.\<close>

lemma m_6_7_standard_prefix:
  \<comment> \<open>m: 命題（標準形の始切片への遺伝性） (§6.7)
     Discharges p_6_7_standard_prefix.\<close>
  assumes "M \<in> ST_PS" "j1' \<le> Lng M - 1"
  shows "seg M 0 j1' \<in> ST_PS"
  by (rule ST_PS_seg_0_aux[OF assms(1) assms(2)])


lemma p_6_7_standard_prefix:
  assumes "M \<in> ST_PS" "j1' \<le> Lng M - 1"
  shows "seg M 0 j1' \<in> ST_PS"
  using assms by (rule m_6_7_standard_prefix)

end

theory P_6_8_standard_P_descending
  imports Support_6_009
begin

text \<open>命題（標準形の単項成分が降順であること）.\<close>

lemma m_6_8_standard_P_descending:
  \<comment> \<open>m: 命題（標準形の単項成分が降順であること） (§6.8).
     Discharges p_6_8_standard_P_descending.\<close>
  assumes "M \<in> ST_PS" "J0' \<le> J1'" "J1' \<le> Lng (P M) - 1"
    "entry (P M ! J0') 0 0 = entry (P M ! J1') 0 0"
  shows "entry (P M ! J0') 1 0 \<ge> entry (P M ! J1') 1 0"
proof -
  obtain k where "M \<in> SkT_PS k"
    using assms(1) ST_PS_subset_Union_SkT by auto
  thus ?thesis using SkT_P_descending assms(2,3,4) by blast
qed

lemma p_6_8_standard_P_descending:
  assumes "M \<in> ST_PS" "J0' \<le> J1'" "J1' \<le> Lng (P M) - 1"
    "entry (P M ! J0') 0 0 = entry (P M ! J1') 0 0"
  shows "entry (P M ! J0') 1 0 \<ge> entry (P M ! J1') 1 0"
  using assms by (rule m_6_8_standard_P_descending)

end

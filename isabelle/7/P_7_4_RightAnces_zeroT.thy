theory P_7_4_RightAnces_zeroT
  imports P_7_4_RightAnces_RightNodes
begin

theorem y3r_7_4_RightAnces_zeroT_TPS:
  assumes MT: "M \<in> T_PS"
  shows "zeroT M \<longleftrightarrow> RightAnces M = []"
  by (rule y3s_7_4_RightAnces_zeroT_TPS[OF MT y3r_RedStab_TPS[OF MT]])


text \<open>系（非零項の\<open>RightAnces\<close>が非空であること） (§7.4, 2809).\<close>

lemma p_7_4_RightAnces_zeroT:
  assumes "M \<in> T_PS"
  shows "zeroT M \<longleftrightarrow> RightAnces M = []"
  using assms by (rule y3r_7_4_RightAnces_zeroT_TPS)

end

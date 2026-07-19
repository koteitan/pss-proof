theory P_5_1_parent_basic_2
  imports Pre_5
begin

lemma p_5_1_parent_basic_2:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1"
  assumes "nextR M 1 j0 j1" "leR M 0 j j1"
  shows "entry M 1 j \<ge> entry M 1 j1"
proof -
  from assms(4) have "nextrel1 M j0 j1" by (simp add: nextR_def)
  hence "\<forall>j'. j0 < j' \<and> le0 M j' j1 \<longrightarrow> entry M 1 j' \<ge> entry M 1 j1"
    by (simp add: nextrel1_def)
  moreover from assms(5) have "le0 M j j1" by (simp add: leR_def)
  ultimately show ?thesis using assms(2) by blast
qed

text \<open>m: 命題（親の基本性質） (2) — discharges @{thm [source] p_5_1_parent_basic_2}.\<close>

lemma m_5_1_parent_basic_2:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1" "nextR M 1 j0 j1" "leR M 0 j j1"
  shows "entry M 1 j \<ge> entry M 1 j1"
proof -
  from assms(4) have "nextrel1 M j0 j1" by (simp add: nextR_def)
  hence "\<forall>j'. j0 < j' \<and> le0 M j' j1 \<longrightarrow> entry M 1 j' \<ge> entry M 1 j1"
    by (simp add: nextrel1_def)
  moreover from assms(5) have "le0 M j j1" by (simp add: leR_def)
  ultimately show ?thesis using assms(2) by blast
qed

end

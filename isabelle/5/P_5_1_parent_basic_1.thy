theory P_5_1_parent_basic_1
  imports Pre_5
begin

text \<open>命題（親の基本性質） — basic property of the parent.\<close>

lemma p_5_1_parent_basic_1:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1"
  assumes "nextR M 0 j0 j1"
  shows "entry M 0 j \<ge> entry M 0 j1"
proof (cases "j = j1")
  case True thus ?thesis by simp
next
  case False
  with assms have "j0 < j" "j < j1" by auto
  thus ?thesis using assms(4) by (auto simp: nextR_def nextrel0_def)
qed

text \<open>m: 命題（親の基本性質） (1) — discharges @{thm [source] p_5_1_parent_basic_1}.\<close>

lemma m_5_1_parent_basic_1:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1" "nextR M 0 j0 j1"
  shows "entry M 0 j \<ge> entry M 0 j1"
proof (cases "j = j1")
  case True thus ?thesis by simp
next
  case False
  with assms have "j0 < j" "j < j1" by auto
  thus ?thesis using assms(4) by (auto simp: nextR_def nextrel0_def)
qed

end

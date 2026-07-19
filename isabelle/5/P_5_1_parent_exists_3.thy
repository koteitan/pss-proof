theory P_5_1_parent_exists_3
  imports After_5_1_Parent_Exists_1
begin

lemma p_5_1_parent_exists_3:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M"
  assumes "\<And>j. j0 < j \<Longrightarrow> j \<le> j1 \<Longrightarrow> entry M 0 j0 < entry M 0 j"
  shows "leR M 0 j0 j1"
proof -
  have allh: "\<forall>j. j0 < j \<and> j \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 j" using assms(4) by blast
  have "(nextrel0 M)\<^sup>*\<^sup>* j0 j1" using le0_build[OF assms(1) assms(3) assms(2) allh] .
  thus ?thesis using assms(2,3) by (simp add: leR_def le0_def)
qed

text \<open>m: 命題（親の存在の判定条件） (3) — discharges @{thm [source] p_5_1_parent_exists_3}.\<close>

lemma m_5_1_parent_exists_3:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M"
    and H: "\<And>j. j0 < j \<Longrightarrow> j \<le> j1 \<Longrightarrow> entry M 0 j0 < entry M 0 j"
  shows "leR M 0 j0 j1"
proof -
  have allh: "\<forall>j. j0 < j \<and> j \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 j" using H by blast
  have "(nextrel0 M)\<^sup>*\<^sup>* j0 j1" using le0_build[OF assms(1) assms(3) assms(2) allh] .
  thus ?thesis using assms(2,3) by (simp add: leR_def le0_def)
qed

end

theory P_5_1_parent_exists_4
  imports Support_5_1_Parent_Exists_4
begin

lemma p_5_1_parent_exists_4:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M"
  assumes "\<And>j. j0 < j \<Longrightarrow> leR M 0 j j1 \<Longrightarrow> entry M 1 j0 < entry M 1 j"
  assumes "leR M 0 j0 j1"
  shows "leR M 1 j0 j1"
proof -
  have U: "\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j0 < entry M 1 j"
  proof (intro allI impI)
    fix j assume a: "j0 < j \<and> le0 M j j1"
    hence "leR M 0 j j1" by (simp add: leR_def)
    thus "entry M 1 j0 < entry M 1 j" using assms(4) a by blast
  qed
  have "(nextrel1 M)\<^sup>*\<^sup>* j0 j1" using le1_build[OF assms(1) assms(3) assms(2) assms(5) U] .
  thus ?thesis using assms(2,3) by (simp add: leR_def le1_def)
qed

text \<open>m: 命題（親の存在の判定条件） (4) — discharges @{thm [source] p_5_1_parent_exists_4}.\<close>

lemma m_5_1_parent_exists_4:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M"
    and H: "\<And>j. j0 < j \<Longrightarrow> leR M 0 j j1 \<Longrightarrow> entry M 1 j0 < entry M 1 j"
    and L: "leR M 0 j0 j1"
  shows "leR M 1 j0 j1"
proof -
  have U: "\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j0 < entry M 1 j"
  proof (intro allI impI)
    fix j assume a: "j0 < j \<and> le0 M j j1"
    hence "leR M 0 j j1" by (simp add: leR_def)
    thus "entry M 1 j0 < entry M 1 j" using H a by blast
  qed
  have "(nextrel1 M)\<^sup>*\<^sup>* j0 j1" using le1_build[OF assms(1) assms(3) assms(2) L U] .
  thus ?thesis using assms(2,3) by (simp add: leR_def le1_def)
qed

end

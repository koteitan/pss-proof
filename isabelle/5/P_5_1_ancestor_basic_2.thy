theory P_5_1_ancestor_basic_2
  imports After_5_1_Ancestor_Tree_1
begin

lemma p_5_1_ancestor_basic_2:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1"
  assumes "leR M 1 j0 j1" "leR M 0 j j1"
  shows "entry M 1 j0 < entry M 1 j"
proof -
  from assms(4) have "(nextrel1 M)\<^sup>*\<^sup>* j0 j1" by (simp add: leR_def le1_def)
  moreover from assms(5) have "le0 M j j1" by (simp add: leR_def)
  ultimately show ?thesis using le1_ances_aux[OF assms(1)] assms(2,3) by blast
qed

text \<open>m: 系（直系先祖の基本性質） (2) — discharges @{thm [source] p_5_1_ancestor_basic_2}.\<close>

lemma m_5_1_ancestor_basic_2:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1" "leR M 1 j0 j1" "leR M 0 j j1"
  shows "entry M 1 j0 < entry M 1 j"
proof -
  from assms(4) have "(nextrel1 M)\<^sup>*\<^sup>* j0 j1" by (simp add: leR_def le1_def)
  moreover from assms(5) have "le0 M j j1" by (simp add: leR_def)
  ultimately show ?thesis using le1_ances_aux[OF assms(1)] assms(2,3) by blast
qed

end

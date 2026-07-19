theory P_5_1_ancestor_tree_2
  imports P_5_1_ancestor_basic_2 P_5_1_parent_exists_4
begin

lemma p_5_1_ancestor_tree_2:
  assumes "M \<in> T_PS" "leR M 1 j0 j1" "j0 \<le> j" "leR M 0 j j1"
  shows "leR M 1 j0 j"
proof (cases "j = j0")
  case True
  have "j0 < Lng M" using assms(2) by (simp add: leR_def le1_def)
  thus ?thesis using True by (simp add: leR_def le1_def)
next
  case False
  with assms(3) have j0j: "j0 < j" by simp
  have jL: "j < Lng M" using assms(4) by (simp add: leR_def le0_def)
  have le0jj1: "le0 M j j1" using assms(4) by (simp add: leR_def)
  have jj1: "j \<le> j1"
  proof -
    have "(nextrel0 M)\<^sup>*\<^sup>* j j1" using le0jj1 by (simp add: le0_def)
    thus ?thesis by (rule nextrel0_rtrancl_mono)
  qed
  have le00j1: "leR M 0 j0 j1" using m_le1_imp_le0[OF assms(2)] .
  have j0lej: "j0 \<le> j" using j0j by simp
  have le00j: "leR M 0 j0 j"
    by (rule m_5_1_ancestor_tree_1[OF assms(1) le00j1 j0lej jj1])
  show ?thesis
  proof (rule m_5_1_parent_exists_4[OF assms(1) j0j jL _ le00j])
    fix j'' assume H1: "j0 < j''" and H2: "leR M 0 j'' j"
    have le0j''j: "le0 M j'' j" using H2 by (simp add: leR_def)
    have "j'' \<le> j"
    proof -
      have "(nextrel0 M)\<^sup>*\<^sup>* j'' j" using le0j''j by (simp add: le0_def)
      thus ?thesis by (rule nextrel0_rtrancl_mono)
    qed
    hence j''j1: "j'' \<le> j1" using jj1 by simp
    have "leR M 0 j'' j1" using le0_trans[OF le0j''j le0jj1] by (simp add: leR_def)
    thus "entry M 1 j0 < entry M 1 j''"
      using m_5_1_ancestor_basic_2[OF assms(1) H1 j''j1 assms(2)] by simp
  qed
qed

text \<open>m: 系（直系先祖の木構造） (2) — discharges @{thm [source] p_5_1_ancestor_tree_2}.\<close>

lemma m_5_1_ancestor_tree_2:
  assumes "M \<in> T_PS" "leR M 1 j0 j1" "j0 \<le> j" "leR M 0 j j1"
  shows "leR M 1 j0 j"
proof (cases "j = j0")
  case True
  have "j0 < Lng M" using assms(2) by (simp add: leR_def le1_def)
  thus ?thesis using True by (simp add: leR_def le1_def)
next
  case False
  with assms(3) have j0j: "j0 < j" by simp
  have jL: "j < Lng M" using assms(4) by (simp add: leR_def le0_def)
  have le0jj1: "le0 M j j1" using assms(4) by (simp add: leR_def)
  have jj1: "j \<le> j1"
  proof -
    have "(nextrel0 M)\<^sup>*\<^sup>* j j1" using le0jj1 by (simp add: le0_def)
    thus ?thesis by (rule nextrel0_rtrancl_mono)
  qed
  have le00j1: "leR M 0 j0 j1" using m_le1_imp_le0[OF assms(2)] .
  have j0lej: "j0 \<le> j" using j0j by simp
  have le00j: "leR M 0 j0 j"
    by (rule m_5_1_ancestor_tree_1[OF assms(1) le00j1 j0lej jj1])
  show ?thesis
  proof (rule m_5_1_parent_exists_4[OF assms(1) j0j jL _ le00j])
    fix j'' assume H1: "j0 < j''" and H2: "leR M 0 j'' j"
    have le0j''j: "le0 M j'' j" using H2 by (simp add: leR_def)
    have "j'' \<le> j"
    proof -
      have "(nextrel0 M)\<^sup>*\<^sup>* j'' j" using le0j''j by (simp add: le0_def)
      thus ?thesis by (rule nextrel0_rtrancl_mono)
    qed
    hence j''j1: "j'' \<le> j1" using jj1 by simp
    have "leR M 0 j'' j1" using le0_trans[OF le0j''j le0jj1] by (simp add: leR_def)
    thus "entry M 1 j0 < entry M 1 j''"
      using m_5_1_ancestor_basic_2[OF assms(1) H1 j''j1 assms(2)] by simp
  qed
qed

end

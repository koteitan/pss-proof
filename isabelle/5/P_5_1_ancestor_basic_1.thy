theory P_5_1_ancestor_basic_1
  imports Pre_5
begin

text \<open>系（直系先祖の基本性質） — basic property of (lineal) ancestors.\<close>

lemma p_5_1_ancestor_basic_1:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1"
  assumes "leR M 0 j0 j1"
  shows "entry M 0 j0 < entry M 0 j"
proof -
  from assms(4) have "(nextrel0 M)\<^sup>*\<^sup>* j0 j1" by (simp add: leR_def le0_def)
  thus ?thesis using le0_ances_aux assms(2,3) by blast
qed

text \<open>m: 系（直系先祖の基本性質） (1) — discharges @{thm [source] p_5_1_ancestor_basic_1}.\<close>

lemma m_5_1_ancestor_basic_1:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1" "leR M 0 j0 j1"
  shows "entry M 0 j0 < entry M 0 j"
proof -
  from assms(4) have "(nextrel0 M)\<^sup>*\<^sup>* j0 j1" by (simp add: leR_def le0_def)
  thus ?thesis using le0_ances_aux assms(2,3) by blast
qed

end

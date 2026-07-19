theory Support_5_1_Parent_Exists_4
  imports P_5_1_parent_exists_2 P_5_1_ancestor_tree_1
begin

text \<open>Auxiliary for §5.1 命題（親の存在の判定条件） (4): build a row-1 chain.\<close>

lemma le1_build:
  assumes "M \<in> T_PS" "j1 < Lng M" "j0 < j1"
    and "leR M 0 j0 j1"
    and "\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j0 < entry M 1 j"
  shows "(nextrel1 M)\<^sup>*\<^sup>* j0 j1"
  using assms(2,3,4,5)
proof (induction j1 rule: less_induct)
  case (less j1)
  have le0j1j1: "le0 M j1 j1" using less.prems(1) by (rule le0_refl)
  have hj1: "entry M 1 j0 < entry M 1 j1"
    using less.prems(4) less.prems(2) le0j1j1 by blast
  obtain j where j: "j0 \<le> j" "j < j1" "nextR M 1 j j1"
    using m_5_1_parent_exists_2[OF assms(1) less.prems(2) less.prems(1) hj1 less.prems(3)]
    by auto
  have nx: "nextrel1 M j j1" using j(3) by (simp add: nextR_def)
  hence le0jj1: "le0 M j j1" by (simp add: nextrel1_def)
  show ?case
  proof (cases "j = j0")
    case True
    thus ?thesis using nx by blast
  next
    case False
    with j(1) have j0j: "j0 < j" by simp
    have jL: "j < Lng M" using j(2) less.prems(1) by simp
    have j0lej: "j0 \<le> j" using j0j by simp
    have jlej1: "j \<le> j1" using j(2) by simp
    have l0j: "leR M 0 j0 j"
      by (rule m_5_1_ancestor_tree_1[OF assms(1) less.prems(3) j0lej jlej1])
    have Uj: "\<forall>j'. j0 < j' \<and> le0 M j' j \<longrightarrow> entry M 1 j0 < entry M 1 j'"
    proof (intro allI impI)
      fix j' assume a: "j0 < j' \<and> le0 M j' j"
      hence "le0 M j' j1" using le0jj1 le0_trans by blast
      thus "entry M 1 j0 < entry M 1 j'" using less.prems(4) a by blast
    qed
    have chain: "(nextrel1 M)\<^sup>*\<^sup>* j0 j"
    proof (rule less.IH)
      show "j < j1" using j(2) .
      show "j < Lng M" using jL .
      show "j0 < j" using j0j .
      show "leR M 0 j0 j" using l0j .
      show "\<forall>j'. j0 < j' \<and> le0 M j' j \<longrightarrow> entry M 1 j0 < entry M 1 j'" using Uj .
    qed
    from chain nx show ?thesis by (rule rtranclp.rtrancl_into_rtrancl)
  qed
qed

end

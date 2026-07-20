theory After_5_1_Ancestor_Tree_1
  imports P_5_1_ancestor_tree_1
begin

text \<open>Auxiliary for §5.1 系（直系先祖の基本性質） (2), by induction on the row-1 chain.\<close>

lemma le1_ances_aux:
  assumes "M \<in> T_PS" "(nextrel1 M)\<^sup>*\<^sup>* j0 j1"
  shows "\<forall>j. j0 < j \<and> j \<le> j1 \<and> le0 M j j1 \<longrightarrow> entry M 1 j0 < entry M 1 j"
  using assms(2)
proof (induction rule: rtranclp_induct)
  case base
  show ?case by auto
next
  case (step y z)
  have ley: "entry M 1 j0 \<le> entry M 1 y"
  proof (cases "j0 < y")
    case True
    have yL: "y < Lng M" using step.hyps(2) by (simp add: nextrel1_def)
    have le0yy: "le0 M y y" using yL by (rule le0_refl)
    have "entry M 1 j0 < entry M 1 y" using step.IH True le0yy by blast
    thus ?thesis by simp
  next
    case False
    have "j0 \<le> y" using step.hyps(1) nextrel1_rtrancl_mono by blast
    with False have "j0 = y" by simp
    thus ?thesis by simp
  qed
  from step.hyps(2) have yz: "y < z" and yzv: "entry M 1 y < entry M 1 z"
    and univ: "\<forall>j'. y < j' \<and> le0 M j' z \<longrightarrow> entry M 1 j' \<ge> entry M 1 z"
    by (auto simp: nextrel1_def)
  show ?case
  proof (intro allI impI)
    fix j assume j: "j0 < j \<and> j \<le> z \<and> le0 M j z"
    show "entry M 1 j0 < entry M 1 j"
    proof (cases "j \<le> y")
      case True
      have lez: "leR M 0 j z" using j by (simp add: leR_def)
      have "y \<le> z" using yz by simp
      have "leR M 0 j y" using m_5_1_ancestor_tree_1[OF assms(1) lez True \<open>y \<le> z\<close>] .
      hence "le0 M j y" by (simp add: leR_def)
      thus ?thesis using step.IH j True by blast
    next
      case False
      hence "y < j" by simp
      hence "entry M 1 j \<ge> entry M 1 z" using univ j by blast
      thus ?thesis using ley yzv by simp
    qed
  qed
qed

end

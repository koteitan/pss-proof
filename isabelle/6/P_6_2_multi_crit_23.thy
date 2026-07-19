theory P_6_2_multi_crit_23
  imports Support_6_001
begin

text \<open>m: 命題（複項性の判定条件） (2)=(3) — discharges @{text p_6_2_multi_crit_23}.\<close>

lemma m_6_2_multi_crit_23:
  assumes "M \<in> T_PS"
  shows "(\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j) = leR M 0 0 (Lng M - 1)"
proof
  assume H: "\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j"
  show "leR M 0 0 (Lng M - 1)"
  proof (cases "Lng M = 1")
    case True thus ?thesis by (simp add: leR_def le0_def)
  next
    case False
    have L: "Lng M > 1" by (rule T_PS_Lng_gt1[OF assms False])
    show ?thesis
    proof (rule m_5_1_parent_exists_3[OF assms])
      show "0 < Lng M - 1" using L by simp
      show "Lng M - 1 < Lng M" using L by simp
      fix j assume "0 < j" "j \<le> Lng M - 1"
      hence "j < Lng M" using L by simp
      thus "entry M 0 0 < entry M 0 j" using H \<open>0 < j\<close> by blast
    qed
  qed
next
  assume le: "leR M 0 0 (Lng M - 1)"
  show "\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j"
  proof (intro allI impI)
    fix j assume a: "0 < j \<and> j < Lng M"
    hence "0 < j" "j \<le> Lng M - 1" by auto
    thus "entry M 0 0 < entry M 0 j"
      using m_5_1_ancestor_basic_1[OF assms _ _ le] by blast
  qed
qed

lemma p_6_2_multi_crit_23:
  assumes "M \<in> T_PS"
  shows "(\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j)
         = leR M 0 0 (Lng M - 1)"
  using assms by (rule m_6_2_multi_crit_23)

end

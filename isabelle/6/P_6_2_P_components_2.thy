theory P_6_2_P_components_2
  imports Frontier_6_004
begin

text \<open>m: 命題（\<open>P\<close>の各成分の非複項性） (2) — discharges @{text p_6_2_P_components_2}.\<close>

lemma m_6_2_P_components_2:
  assumes "M \<in> T_PS"
  shows "multiT M \<longleftrightarrow> length (P M) > 1"
proof (cases "multiT M")
  case True
  hence "Lng M > 1" using multiT_imp_Lng_gt1[OF assms] by simp
  with True have "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
    by (subst P.simps) simp
  hence "length (P M) = Suc (length (P (take (Pcut M) M)))" by simp
  thus ?thesis using True P_nonempty[of "take (Pcut M) M"]
    by (cases "P (take (Pcut M) M)") auto
next
  case False
  hence "P M = [M]" by (subst P.simps) simp
  with False show ?thesis by simp
qed


lemma p_6_2_P_components_2:
  assumes "M \<in> T_PS"
  shows "multiT M \<longleftrightarrow> length (P M) > 1"
  using assms by (rule m_6_2_P_components_2)

end

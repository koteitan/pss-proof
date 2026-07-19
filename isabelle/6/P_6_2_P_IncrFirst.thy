theory P_6_2_P_IncrFirst
  imports Frontier_6_005
begin

text \<open>命題（\<open>P\<close>の\<open>IncrFirst\<close>同変性） — \<open>P\<close> commutes with \<open>IncrFirst\<close>.\<close>

lemma m_6_2_P_IncrFirst:
  shows "P (IncrFirst M) = map IncrFirst (P M)"
proof (induction M rule: P.induct)
  case (1 M)
  show ?case
  proof (cases "multiT M \<and> 1 < Lng M")
    case True
    hence step: "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
      by (subst P.simps) simp
    from True have stepI:
      "P (IncrFirst M)
         = P (take (Pcut M) (IncrFirst M)) @ [drop (Pcut M) (IncrFirst M)]"
      by (subst P.simps) (simp add: IncrFirst_multiT_eq IncrFirst_Pcut_eq)
    have IH: "P (IncrFirst (take (Pcut M) M)) = map IncrFirst (P (take (Pcut M) M))"
      using True 1 by blast
    show ?thesis
      using stepI step IH
      by (simp add: IncrFirst_take IncrFirst_drop)
  next
    case False
    hence "P M = [M]" by (subst P.simps) simp
    moreover have "P (IncrFirst M) = [IncrFirst M]"
      using False by (subst P.simps) (simp add: IncrFirst_multiT_eq)
    ultimately show ?thesis by simp
  qed
qed

lemma p_6_2_P_IncrFirst:
  shows "P (IncrFirst M) = map IncrFirst (P M)"
  by (rule m_6_2_P_IncrFirst)

end

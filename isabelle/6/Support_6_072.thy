theory Support_6_072
  imports Frontier_6_092
begin

text \<open>補題（簡約性と係数の基本性質）, full form: in a reduced sequence row 0
  dominates row 1 (multiT case via componentwise reduction
  @{thm [source] m_6_6_P_reduced} + the non-multi classification
  @{thm [source] m_6_2_P_components_1}).\<close>

lemma m_6_6_reduced_coeff_set:
  assumes M: "M \<in> RT_PS"
  shows "\<forall>p \<in> set M. snd p \<le> fst p"
proof (cases "multiT M")
  case False
  thus ?thesis using reduced_nonmulti_coeff_set[OF M] by simp
next
  case True
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  show ?thesis
  proof
    fix p assume "p \<in> set M"
    hence "p \<in> set (concat (P M))" by (simp add: poper_concat_P)
    then obtain K where Kin: "K \<in> set (P M)" and pK: "p \<in> set K" by auto
    obtain J where JL: "J < Lng (P M)" and KJ: "K = P M ! J"
      using Kin by (auto simp: in_set_conv_nth)
    have KR: "K \<in> RT_PS"
      using m_6_6_P_reduced[OF MT] M JL KJ by simp
    have "zeroT K \<or> monoT K" using m_6_2_P_components_1[OF MT] Kin by blast
    hence Knmu: "\<not> multiT K" by (auto simp: multiT_def)
    show "snd p \<le> fst p"
      using reduced_nonmulti_coeff_set[OF KR Knmu] pK by blast
  qed
qed

end

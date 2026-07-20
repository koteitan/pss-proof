theory P_6_6_reduced_oper
  imports Frontier_6_093
begin

text \<open>命題（簡約性が基本列で保たれること）.\<close>

text \<open>命題（簡約性が基本列で保たれること）: reducedness is preserved by the
  fundamental sequence on ALL of \<open>RT\<^sub>PS\<close> (not just along standard expansions) —
  keystone @{thm [source] m_6_6_reduced_iff_cond} + the \<open>T\<^sub>PS\<close>-general
  tiling (@{thm [source] operCA_tiling_T} / @{thm [source] operCB_tiling_T})
  and non-tiling (@{thm [source] RedCondA_oper_nontiling} /
  @{thm [source] RedCondB_oper_nontiling}) bricks.  Empirically: 0/100,344
  oper instances over all 33,448 reduced sequences (len \<le> 6, entries \<le> 3).\<close>

lemma m_6_6_reduced_oper:
  assumes M: "M \<in> RT_PS" and n1: "1 \<le> n"
  shows "(M::pairseq)[n] \<in> RT_PS"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have condA: "RedCondA M" and condB: "RedCondB M"
    using m_6_6_reduced_iff_cond[OF MT] M by auto
  have MnT: "(M::pairseq)[n] \<in> T_PS" by (rule oper_T_PS[OF MT n1])
  have AB: "RedCondA ((M::pairseq)[n]) \<and> RedCondB ((M::pairseq)[n])"
  proof (cases "Lng M - 1 = 0
                \<or> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
                \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)")
    case True
    show ?thesis
      using RedCondA_oper_nontiling[OF MT condA n1 True]
            RedCondB_oper_nontiling[OF MT condB n1 True] by blast
  next
    case False
    show ?thesis
      using operCA_tiling_T[OF condA n1 False]
            operCB_tiling_T[OF MT condB n1 False] by blast
  qed
  show ?thesis using m_6_6_reduced_iff_cond[OF MnT] AB by blast
qed

lemma p_6_6_reduced_oper:
  assumes "M \<in> RT_PS" "n \<ge> 1"
  shows "((M::pairseq)[n]) \<in> RT_PS"
  using assms by (rule m_6_6_reduced_oper)

end

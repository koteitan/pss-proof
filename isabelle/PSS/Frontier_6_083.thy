theory Frontier_6_083
  imports Support_6_062
begin

text \<open>
  REMAINING RESIDUAL (the single crux; NOT closed here).  The \<open>shift\<close> case of
  \<open>Red\<close>-\<open>oper\<close>-commutativity on \<open>ST\<^sub>PS\<close>:
    \<open>M \<in> ST\<^sub>PS \<Longrightarrow> M \<in> RT\<^sub>PS \<Longrightarrow> 1 \<le> n \<Longrightarrow> M[n] \<noteq> Pred M \<Longrightarrow> (Red M)[n] = Red (M[n])\<close>.
  The discriminator \<open>M[n] \<noteq> Pred M\<close> is exactly the tiling case
    \<open>\<not> (Lng M - 1 = 0 \<or> (M\<^bsub>0,j\<^sub>1\<^esub> = 0 \<and> M\<^bsub>1,j\<^sub>1\<^esub> = 0) \<or> \<not> hasParent M (idx1 M j\<^sub>1) j\<^sub>1)\<close>
  (the negation of the three degenerate \<open>oper\<close>-branches), i.e. the \<open>\<not> ?nontile\<close>
  case of @{thm [source] m_6_7_standard_RedCondAB}.  It maps to the existing
  \<open>operCA\<close>/\<open>operCB\<close> tiling machinery (@{thm [source] m_6_7_standard_RedCondAB},
  @{thm [source] operB_gen_LngM}, the \<open>fc_D_oper\<close>/\<open>has_gz \<Longrightarrow> D(N)\<close> periodic-tiling
  bricks of §6.7).  Verified non-vacuous and TRUE on all reduced \<open>M\<close> in
  red_model.py (enum(3,3), 0-fail).
\<close>


subsection \<open>(vi) Wiring the \<open>shift\<close> residual to the \<open>operCA\<close>/\<open>operCB\<close> tiling bricks\<close>

text \<open>
  The discriminator of the lone \<open>shift\<close> residual, \<open>M[n] \<noteq> Pred M\<close>, is exactly the
  \<^emph>\<open>non-degenerate\<close> (tiling) \<open>oper\<close> case.  In every one of the three degenerate
  \<open>oper\<close>-branches \<open>M[n] = Pred M\<close>:
  \<^item> \<open>Lng M - 1 = 0\<close>: \<open>M[n] = M\<close> (first @{const oper} branch) and \<open>Pred M = M\<close>
    (@{const Pred} on \<open>Lng M \<le> 1\<close>), so \<open>M[n] = Pred M\<close>.
  \<^item> \<open>M\<^bsub>j\<^sub>1\<^esub> = (0,0)\<close> or no unique parent (with \<open>Lng M > 1\<close>): \<open>M[n] = Pred M\<close> by
    @{thm [source] oper_degenerate_eq_Pred}.
  Hence \<open>M[n] \<noteq> Pred M\<close> forces the negation of the \<open>?nontile\<close> disjunction, the
  exact \<open>\<not> ?nontile\<close> precondition of @{thm [source] m_6_7_standard_RedCondAB}'s
  \<open>operCA\<close>/\<open>operCB\<close> hypotheses.
\<close>

lemma oper_nontile_eq_Pred:
  assumes nontile: "Lng M - 1 = 0
                    \<or> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
                    \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "(M::pairseq)[n] = Pred M"
proof (cases "Lng M - 1 = 0")
  case True
  hence "(M::pairseq)[n] = M" by (simp add: oper_def Let_def)
  moreover have "Pred M = M" using True by (simp add: Pred_def)
  ultimately show ?thesis by simp
next
  case False
  hence L: "Lng M > 1" by simp
  have D: "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0
           \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    using nontile False by blast
  show ?thesis by (rule oper_degenerate_eq_Pred[OF L D])
qed

end

theory Support_6_052
  imports Frontier_6_072
begin

text \<open>§6.7 standard \<open>\<Longrightarrow>\<close> \<open>RedCondA \<and> RedCondB\<close>, by \<open>ST_PS.induct\<close>.
  The \<open>diag\<close> base is the GREEN @{thm [source] kfwd_condAB_diagSeq}.  The \<open>oper\<close>
  step splits on the §5.3 case analysis: the three degenerate (NON-TILING)
  branches preserve \<open>RedCondA\<close>/\<open>RedCondB\<close> via @{thm [source] RedCondA_oper_nontiling}
  / @{thm [source] RedCondB_oper_nontiling} from the IH; the genuine TILING branch
  is supplied by the explicit hypotheses \<open>operCA\<close>/\<open>operCB\<close> (= Front A's tiling
  bricks), which receive the IH facts \<open>RedCondA M \<and> RedCondB M\<close>.  Empirically
  (red_model.py, 285 ST_PS forms) both \<open>RedCondA\<close> and \<open>RedCondB\<close> hold with 0 fail.\<close>

lemma m_6_7_standard_RedCondAB:
  assumes Mst: "M \<in> ST_PS"
    and operCA: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondA ((N::pairseq)[n])"
    and operCB: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondB ((N::pairseq)[n])"
  shows "RedCondA M \<and> RedCondB M"
  using Mst
proof (induct M rule: ST_PS.induct)
  case (diag u v)
  thus ?case by (rule kfwd_condAB_diagSeq)
next
  case (oper M n)
  have MST: "M \<in> ST_PS" by (rule oper.hyps(1))
  have MT: "M \<in> T_PS" by (rule ST_PS_T_PS[OF MST])
  have condA: "RedCondA M" and condB: "RedCondB M" using oper.hyps(2) by simp_all
  have n1: "1 \<le> n" by (rule oper.hyps(3))
  let ?nontile = "Lng M - 1 = 0
                  \<or> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
                  \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  show ?case
  proof (cases ?nontile)
    case True
    have "RedCondA ((M::pairseq)[n])"
      by (rule RedCondA_oper_nontiling[OF MT condA n1 True])
    moreover have "RedCondB ((M::pairseq)[n])"
      by (rule RedCondB_oper_nontiling[OF MT condB n1 True])
    ultimately show ?thesis by blast
  next
    case False
    have "RedCondA ((M::pairseq)[n])"
      by (rule operCA[OF MST condA condB n1 False])
    moreover have "RedCondB ((M::pairseq)[n])"
      by (rule operCB[OF MST condA condB n1 False])
    ultimately show ?thesis by blast
  qed
qed

text \<open>§6.7 \<open>ST\<^sub>PS \<subseteq> RT\<^sub>PS\<close> (= mechanized @{text p_6_7_standard_reduced}).
  Every standard form is in \<open>T\<^sub>PS\<close> (@{thm [source] ST_PS_T_PS}) and satisfies
  \<open>RedCondA \<and> RedCondB\<close> (@{thm [source] m_6_7_standard_RedCondAB}), so by the §6.6
  keystone @{thm [source] m_6_6_reduced_iff_cond} it is reduced.  Conditional on
  the \<open>oper\<close>-tiling bricks \<open>operCA\<close>/\<open>operCB\<close> (Front A).\<close>

lemma m_6_7_standard_reduced:
  assumes operCA: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondA ((N::pairseq)[n])"
    and operCB: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondB ((N::pairseq)[n])"
  shows "ST_PS \<subseteq> RT_PS"
proof
  fix M assume M: "M \<in> ST_PS"
  have MT: "M \<in> T_PS" by (rule ST_PS_T_PS[OF M])
  have AB: "RedCondA M \<and> RedCondB M"
    by (rule m_6_7_standard_RedCondAB[OF M operCA operCB])
  show "M \<in> RT_PS" using m_6_6_reduced_iff_cond[OF MT] AB by blast
qed

text \<open>The \<open>stdCA\<close> residual of Front A's §6.5 assembly: \<open>M \<in> ST_PS \<Longrightarrow> RedCondA M\<close>,
  immediate from @{thm [source] m_6_7_standard_RedCondAB} (conditional on the
  same \<open>oper\<close>-tiling bricks).\<close>

lemma m_6_5_ST_PS_imp_RedCondA:
  assumes M: "M \<in> ST_PS"
    and operCA: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondA ((N::pairseq)[n])"
    and operCB: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondB ((N::pairseq)[n])"
  shows "RedCondA M"
  using m_6_7_standard_RedCondAB[OF M operCA operCB] by simp

end

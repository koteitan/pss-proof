theory Support_6_064
  imports Frontier_6_084
begin

lemma treewf_diag:
  assumes uv: "u \<le> v"
  shows "TreeWF (diagSeq u v)"
proof (intro allI impI)
  fix z
  let ?M = "diagSeq u v"  let ?j1 = "Lng ?M - 1"
  assume H: "parent ?M 1 ?j1 < z \<and> z < ?j1"
  hence zlt: "z < ?j1" and zgt: "parent ?M 1 ?j1 < z" by auto
  have L1: "1 < Lng ?M" using zlt by linarith
  have lng: "Lng ?M = Suc v - u" by simp
  have j1lt: "Suc (?j1 - 1) < Suc v - u" using L1 lng by simp
  have nx: "nextR ?M 1 (?j1 - 1) (Suc (?j1 - 1))" by (rule nextR1_diagSeq[OF j1lt])
  have suc: "Suc (?j1 - 1) = ?j1" using L1 by simp
  have nxj1: "nextR ?M 1 (?j1 - 1) ?j1" using nx suc by simp
  have hpj1: "hasParent ?M 1 ?j1" unfolding hasParent_def using nxj1 nextR1_unique by blast
  have parR: "nextR ?M 1 (parent ?M 1 ?j1) ?j1"
    using hpj1 unfolding hasParent_def parent_def by (rule theI')
  have pj1: "parent ?M 1 ?j1 = ?j1 - 1" by (rule nextR1_unique[OF parR nxj1])
  have False using zgt zlt pj1 by linarith
  thus "hasParent ?M 1 z \<and> parent ?M 1 ?j1 \<le> parent ?M 1 z" by simp
qed

lemma m_6_7_treewf:
  assumes treewf_oper_step:
      "\<And>K n. \<lbrakk>K \<in> ST_PS; 1 \<le> n; TreeWF K\<rbrakk> \<Longrightarrow> TreeWF ((K::pairseq)[n])"
    and M: "M \<in> ST_PS"
  shows "TreeWF M"
  using M
proof (induct M rule: ST_PS.induct)
  case (diag u v)
  show ?case by (rule treewf_diag[OF diag.hyps])
next
  case (oper K n)
  have KST: "K \<in> ST_PS" and n1: "1 \<le> n" using oper.hyps by auto
  have IH: "TreeWF K" using oper.hyps by blast
  show ?case by (rule treewf_oper_step[OF KST n1 IH])
qed

text \<open>
  The \<open>oper\<close> step of @{thm [source] m_6_7_treewf}, split on the \<open>oper\<close> branches:
  \<^item> \<open>Lng K - 1 = 0\<close>: \<open>K[n] = K\<close>, so \<open>TreeWF (K[n]) = TreeWF K\<close> (the IH).  GREEN.
  \<^item> degenerate (\<open>K\<^bsub>j\<^sub>1\<^esub> = (0,0)\<close> or no parent): \<open>K[n] = Pred K\<close>
    (@{thm [source] oper_nontile_eq_Pred}); reduced to the residual @{text treewf_pred}.
  \<^item> tiling (\<open>1 < Lng K\<close>, endpoint \<open>\<noteq> (0,0)\<close>, \<open>hasParent\<close>): reduced to the residual
    @{text treewf_tile}, the main readback case (\<open>i\<^sub>1 = 0/1\<close>), where \<open>TreeWF K\<close> (the
    IH) supplies the M-side gate that @{thm [source] oper_parent1_readback} needs.
\<close>

lemma treewf_oper_step:
  assumes treewf_pred:
      "\<And>K. \<lbrakk>K \<in> ST_PS; TreeWF K; 1 < Lng K;
             entry K 0 (Lng K - 1) = 0 \<and> entry K 1 (Lng K - 1) = 0
             \<or> \<not> hasParent K (idx1 K (Lng K - 1)) (Lng K - 1)\<rbrakk>
            \<Longrightarrow> TreeWF (Pred K)"
    and treewf_tile:
      "\<And>K n. \<lbrakk>K \<in> ST_PS; TreeWF K; 1 < Lng K;
              \<not> (entry K 0 (Lng K - 1) = 0 \<and> entry K 1 (Lng K - 1) = 0);
              hasParent K (idx1 K (Lng K - 1)) (Lng K - 1); 1 \<le> n\<rbrakk>
             \<Longrightarrow> TreeWF ((K::pairseq)[n])"
    and KST: "K \<in> ST_PS" and n1: "1 \<le> n" and IH: "TreeWF K"
  shows "TreeWF ((K::pairseq)[n])"
proof (cases "Lng K - 1 = 0")
  case True
  have "(K::pairseq)[n] = K" using True by (simp add: oper_def Let_def)
  thus ?thesis using IH by simp
next
  case False
  hence L: "1 < Lng K" by linarith
  show ?thesis
  proof (cases "entry K 0 (Lng K - 1) = 0 \<and> entry K 1 (Lng K - 1) = 0
                \<or> \<not> hasParent K (idx1 K (Lng K - 1)) (Lng K - 1)")
    case True
    have nontile: "Lng K - 1 = 0
                   \<or> (entry K 0 (Lng K - 1) = 0 \<and> entry K 1 (Lng K - 1) = 0)
                   \<or> \<not> hasParent K (idx1 K (Lng K - 1)) (Lng K - 1)"
      using True by blast
    have eq: "(K::pairseq)[n] = Pred K" by (rule oper_nontile_eq_Pred[OF nontile])
    show ?thesis using treewf_pred[OF KST IH L True] eq by simp
  next
    case False
    hence nz: "\<not> (entry K 0 (Lng K - 1) = 0 \<and> entry K 1 (Lng K - 1) = 0)"
      and hp: "hasParent K (idx1 K (Lng K - 1)) (Lng K - 1)" by auto
    show ?thesis by (rule treewf_tile[OF KST IH L nz hp n1])
  qed
qed

end

theory Support_6_066
  imports Frontier_6_086
begin

text \<open>The \<open>oper\<close> step of @{thm [source] m_6_7_globaltreewf}, split on the \<open>oper\<close>
  branches, with the degenerate branch discharged by @{thm [source] gtw_pred}:
  \<^item> \<open>Lng K-1 = 0\<close>: \<open>K[n] = K\<close> (the IH).  GREEN.
  \<^item> degenerate (\<open>K\<^bsub>j\<^sub>1\<^esub>=(0,0)\<close> or no parent): \<open>K[n] = Pred K\<close>, \<open>GTWF (Pred K)\<close> by
    @{thm [source] gtw_pred}.  GREEN.
  \<^item> tiling: reduced to the single residual @{text gtw_tile} (the global readback).\<close>

lemma gtw_oper_step:
  assumes gtw_tile:
      "\<And>K n. \<lbrakk>K \<in> ST_PS; GTWF K; 1 < Lng K;
              \<not> (entry K 0 (Lng K - 1) = 0 \<and> entry K 1 (Lng K - 1) = 0);
              hasParent K (idx1 K (Lng K - 1)) (Lng K - 1); 1 \<le> n\<rbrakk>
             \<Longrightarrow> GTWF ((K::pairseq)[n])"
    and KST: "K \<in> ST_PS" and n1: "1 \<le> n" and IH: "GTWF K"
  shows "GTWF ((K::pairseq)[n])"
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
    show ?thesis using gtw_pred[OF L IH] eq by simp
  next
    case False
    hence nz: "\<not> (entry K 0 (Lng K - 1) = 0 \<and> entry K 1 (Lng K - 1) = 0)"
      and hp: "hasParent K (idx1 K (Lng K - 1)) (Lng K - 1)" by auto
    show ?thesis by (rule gtw_tile[OF KST IH L nz hp n1])
  qed
qed

end

theory Support_6_065
  imports Frontier_6_085
begin

lemma gtw_diag:
  assumes uv: "u \<le> v"
  shows "GTWF (diagSeq u v)"
proof (intro allI impI)
  fix y z
  assume hpy: "hasParent (diagSeq u v) 1 y"
     and H: "parent (diagSeq u v) 1 y < z \<and> z < y"
  let ?M = "diagSeq u v"
  have parR: "nextR ?M 1 (parent ?M 1 y) y"
    using hpy unfolding hasParent_def parent_def by (rule theI')
  have i1: "(1::nat) \<le> 1" by simp
  have suc: "Suc (parent ?M 1 y) = y" by (rule kfwd_nextR_diagSeq_parent[OF uv i1 parR])
  have False using H suc by linarith
  thus "hasParent ?M 1 z \<and> parent ?M 1 y \<le> parent ?M 1 z" by simp
qed

lemma m_6_7_globaltreewf:
  assumes gtw_oper_step:
      "\<And>K n. \<lbrakk>K \<in> ST_PS; 1 \<le> n; GTWF K\<rbrakk> \<Longrightarrow> GTWF ((K::pairseq)[n])"
    and M: "M \<in> ST_PS"
  shows "GTWF M"
  using M
proof (induct M rule: ST_PS.induct)
  case (diag u v)
  show ?case by (rule gtw_diag[OF diag.hyps])
next
  case (oper K n)
  have KST: "K \<in> ST_PS" and n1: "1 \<le> n" using oper.hyps by auto
  have IH: "GTWF K" using oper.hyps by blast
  show ?case by (rule gtw_oper_step[OF KST n1 IH])
qed

end

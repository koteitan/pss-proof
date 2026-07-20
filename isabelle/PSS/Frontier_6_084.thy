theory Frontier_6_084
  imports Support_6_063
begin

subsection \<open>(x) §6.7 row-1 tree inheritance — \<open>m_6_7_treewf\<close> (the core invariant)\<close>

text \<open>
  \<open>TreeWF M\<close>: in \<open>M\<close>, with \<open>j\<^sub>0 = parent M 1 (Lng M-1)\<close>, every interior column
  \<open>z\<close> (\<open>j\<^sub>0 < z < Lng M-1\<close>) has a row-1 parent that lands \<open>\<ge> j\<^sub>0\<close>.  This is the
  irreducible core of §6.7 (the "row-1 reachable parent-base inherited from \<open>M\<close>"
  the analysis showed unavoidable).  It is an \<open>ST\<^sub>PS\<close> INDUCTIVE INVARIANT
  (verified: diag base 18/0, oper step \<open>TreeWF K \<Longrightarrow> TreeWF (K[n])\<close> 1971/0 on the
  broad closure).  The oper step is carried as the named residual
  @{text treewf_oper_step}; once GREEN, \<open>TreeWF\<close> holds on all \<open>ST\<^sub>PS\<close> and (via
  @{thm [source] oper_parent1_readback}, now applicable since \<open>TreeWF K\<close> supplies
  its M-side gate) unblocks the \<open>j\<^sub>0\<close>-readback, the \<open>w>1\<close> wrapper and the \<open>D(N)\<close>
  cascade.

  \<open>diag\<close> base is VACUOUS: in a diagonal every parent is the immediate predecessor
  (@{thm [source] kfwd_nextR_diagSeq_parent}: \<open>Suc j\<^sub>0 = j\<^sub>1\<close>), so the interior
  interval \<open>(j\<^sub>1-1, j\<^sub>1)\<close> is empty.
\<close>

abbreviation TreeWF :: "pairseq \<Rightarrow> bool" where
  "TreeWF M \<equiv> (\<forall>z. parent M 1 (Lng M - 1) < z \<and> z < Lng M - 1
                    \<longrightarrow> hasParent M 1 z \<and> parent M 1 (Lng M - 1) \<le> parent M 1 z)"

end

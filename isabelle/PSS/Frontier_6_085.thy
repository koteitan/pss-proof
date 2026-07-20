theory Frontier_6_085
  imports Support_6_064
begin

subsection \<open>(xi) §6.7 GLOBAL row-1 tree wellformedness — \<open>m_6_7_globaltreewf\<close>\<close>

text \<open>
  \<open>GTWF M\<close> strengthens \<open>TreeWF M\<close> from "the LAST node's block is wellformed" to
  "EVERY node's block is wellformed": for every \<open>y\<close> that HAS a row-1 parent, the
  interior \<open>(parent M 1 y, y)\<close> consists of nodes that also have row-1 parents
  landing \<open>\<ge> parent M 1 y\<close>.  Quantifying only over \<open>y\<close> WITH a parent makes it
  well-specified even for degenerate \<open>M\<close> (no \<open>THE\<close>-of-nonexistent), which the
  last-node \<open>TreeWF\<close> is not.  \<open>GTWF\<close> is an \<open>ST\<^sub>PS\<close> inductive invariant (verified:
  diag 35/0, oper step 723/0, all-in-closure 241/0); crucially it propagates
  through the degenerate \<open>Pred\<close> branch CLEANLY (\<open>Pred K\<close> is a prefix of \<open>K\<close>, so
  every \<open>y < Lng K-1\<close> keeps its \<open>K\<close>-tree).  \<open>TreeWF M\<close> for a gated \<open>M\<close> is then the
  special case \<open>y = Lng M-1\<close>.
\<close>

abbreviation GTWF :: "pairseq \<Rightarrow> bool" where
  "GTWF M \<equiv> (\<forall>y. hasParent M 1 y
               \<longrightarrow> (\<forall>z. parent M 1 y < z \<and> z < y
                        \<longrightarrow> hasParent M 1 z \<and> parent M 1 y \<le> parent M 1 z))"

end

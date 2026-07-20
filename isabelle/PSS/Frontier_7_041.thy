theory Frontier_7_041
  imports Support_7_035
begin

(* ===== integrated from wt-s7 ===== *)

section \<open>§8.7 OT (ordinal-term) infrastructure\<close>

text \<open>Basic facts about \<open>lessBT\<close> against \<open>0\<^sub>B\<close> and the membership conditions
  for ordinal terms.  These are the independent OT-side lemmas of §8.7.\<close>

lemma lessBT_Zero_right [simp]: "\<not> lessBT t (Trm [])"
proof (cases t)
  case (Trm ps) thus ?thesis by (cases ps) simp_all
qed

lemma lessBT_Zero_left [simp]: "lessBT (Trm []) t \<longleftrightarrow> t \<noteq> Trm []"
proof (cases t)
  case (Trm ps) thus ?thesis by (cases ps) simp_all
qed

(* ===== round-2 from wt-r87 ===== *)

text \<open>命題（公差\<open>(0,0)\<close>のペア数列の\<open>Trans\<close>の基本性質） (§8.7, article 5857),
  discharging @{text p_8_7_const00_Trans}.  The constant 公差\<open>(0,0)\<close>
  sequence \<open>cnst u j\<^sub>1 = ((u,u))\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>1\<^esup> = replicate (Suc j\<^sub>1) (u,u)\<close> has both
  rows constant, hence (for \<open>j\<^sub>1 > 0\<close>) is 複項 (multi): the row-0 path
  relation \<open>nextrel0\<close> needs a \<^emph>\<open>strict\<close> increase, so no \<open>j\<close> reaches \<open>j\<^sub>1\<close> and
  \<open>monoT\<close> fails.  \<open>P\<close> therefore splits it into \<open>Suc j\<^sub>1\<close> singleton blocks
  \<open>[(u,u)]\<close>, and \<open>Trans\<close>'s 複項 branch accumulates them into
  \<open>(D\<^sub>u 0)\<times>(j\<^sub>1+1)\<close> (\<open>(D\<^sub>0 0)\<times>j\<^sub>1\<close> when \<open>u = 0\<close>, since the leftmost
  \<open>(0,0)\<close> contributes \<open>0\<close>, not \<open>D\<^sub>0 0\<close>).\<close>

abbreviation cnst :: "nat \<Rightarrow> nat \<Rightarrow> pairseq" where
  "cnst u j1 \<equiv> replicate (Suc j1) (u, u)"

end

theory Frontier_7_004
  imports P_7_1_lessBT_linord
begin

(* ===== block from workflow t2-rnsub ===== *)
subsection \<open>§7.2 命題（\<open>RightNodes\<close>と部分表現の関係） — m_7_2_RightNodes_subexpr\<close>

text \<open>
  Development block (rnsub_*).  We prove the proposition directly at the \<^typ>\<open>BT\<close>
  level, replacing the article's string-level scb argument by a structural
  recursion along the rightmost spine.  The witness \<open>t\<^sub>1\<close> is \<open>t\<^sub>0\<close> with the
  rightmost-spine bottom principal \<open>D\<^sub>v 0\<close> having its \<open>0\<close>-argument replaced by \<open>t\<close>.
\<close>

\<comment> \<open>Termination of \<open>RightNodes\<close>: the single recursive call \<open>RightNodes a\<close> (where
   \<open>last xs = DB u a\<close>) is on a strict subterm, so the datatype \<open>size\<close> measure
   decreases.  This discharges the deferred termination and gives us the
   unconditional simp rule \<open>RightNodes.simps\<close>.\<close>

lemma rnsub_size_arg_lt:
  assumes "xs \<noteq> []" "last xs = DB u a"
  shows "size a < size (Trm xs)"
proof -
  have "DB u a \<in> set xs" using assms last_in_set by metis
  hence "size (DB u a) \<le> size_list size xs"
    by (simp add: size_list_estimation' [where x = "DB u a"] order.strict_implies_order)
  moreover have "size (Trm xs) = Suc (size_list size xs)" by simp
  moreover have "size a < size (DB u a)" by simp
  ultimately show ?thesis by linarith
qed

lemma rnsub_size_arg_lt':
  "last xs = DB u a \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> size a < size (Trm xs)"
  using rnsub_size_arg_lt by blast

termination RightNodes
  apply (relation "measure size")
   apply simp
  apply (clarsimp simp only: in_measure)
  apply (rule rnsub_size_arg_lt')
   apply assumption
  apply simp
  done

end

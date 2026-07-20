theory Frontier_7_002
  imports P_7_1_term_components
begin

text \<open>
  Mutual structural induction: both \<open>flatBT\<close> and \<open>flatBP\<close> produce paren-balanced strings.
  We prove the two claims simultaneously using the function induction rule
  \<open>flatBT_flatBP.induct\<close>.
\<close>

\<comment> \<open>Helper: equal LP/RP counts preserved under concat of balanced lists\<close>
lemma filter_concat_bal:
  "\<forall>xs \<in> set xss.
     length (filter ((=) LP) xs) = length (filter ((=) RP) xs) \<Longrightarrow>
   length (filter ((=) LP) (concat xss)) = length (filter ((=) RP) (concat xss))"
  by (induct xss) auto

lemma flatBT_paren_balance:
  "length (filter ((=) LP) (flatBT t)) = length (filter ((=) RP) (flatBT t))"
  and flatBP_paren_balance:
  "length (filter ((=) LP) (flatBP p)) = length (filter ((=) RP) (flatBP p))"
proof (induct rule: flatBT_flatBP.induct)
  \<comment> \<open>flatBT (Trm []) = [Zsym]: no parens\<close>
  case 1 show ?case by simp
next
  \<comment> \<open>flatBT (Trm [p]) = flatBP p: balance by IH for p\<close>
  case (2 p) show ?case using 2 by simp
next
  \<comment> \<open>flatBT (Trm (p#q#ps)) = LP # (flatBP p @ concat ...) @ [RP]\<close>
  case (3 p q ps)
  \<comment> \<open>IH(1): flatBP p is balanced; IH(2): flatBP r is balanced for r \<in> set(q#ps)\<close>
  have IH_p: "length (filter ((=) LP) (flatBP p)) =
              length (filter ((=) RP) (flatBP p))"
    using 3(1) by blast
  have IH_qps: "\<forall>r \<in> set (q # ps).
    length (filter ((=) LP) (flatBP r)) = length (filter ((=) RP) (flatBP r))"
    using 3(2) by simp
  have concat_bal:
    "length (filter ((=) LP) (concat (map (\<lambda>r. CM # flatBP r) (q # ps)))) =
     length (filter ((=) RP) (concat (map (\<lambda>r. CM # flatBP r) (q # ps))))"
  proof (rule filter_concat_bal)
    show "\<forall>xs \<in> set (map (\<lambda>r. CM # flatBP r) (q # ps)).
      length (filter ((=) LP) xs) = length (filter ((=) RP) xs)"
    proof
      fix xs assume "xs \<in> set (map (\<lambda>r. CM # flatBP r) (q # ps))"
      then obtain r where "r \<in> set (q # ps)" "xs = CM # flatBP r" by auto
      thus "length (filter ((=) LP) xs) = length (filter ((=) RP) xs)"
        using IH_qps by auto
    qed
  qed
  show ?case
  proof -
    define inner where "inner = flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))"
    have expand: "flatBT (Trm (p # q # ps)) = LP # inner @ [RP]"
      unfolding inner_def by simp
    have inner_bal: "length (filter ((=) LP) inner) = length (filter ((=) RP) inner)"
      unfolding inner_def
      by (simp only: filter_append length_append IH_p concat_bal)
    show ?thesis
      unfolding expand
      using inner_bal by simp
  qed
next
  \<comment> \<open>flatBP (DB u a) = Dsym u # flatBT a: balance by IH for a\<close>
  case (4 u a) show ?case using 4 by simp
qed

end

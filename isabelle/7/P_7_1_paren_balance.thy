theory P_7_1_paren_balance
  imports Frontier_7_002
begin

lemma m_7_1_paren_balance:
  \<comment> \<open>m: 命題（括弧の対応）(§7.1) — the \<open>(\<close>-count equals the \<open>)\<close>-count in \<open>flat t\<close>\<close>
  assumes "t \<in> T_B"
  shows "length (filter (\<lambda>x. x = LP) (flatBT t)) =
         length (filter (\<lambda>x. x = RP) (flatBT t))"
proof -
  have LP_eq: "filter (\<lambda>x. x = LP) (flatBT t) = filter ((=) LP) (flatBT t)"
    by (rule filter_cong) (auto simp: eq_commute)
  have RP_eq: "filter (\<lambda>x. x = RP) (flatBT t) = filter ((=) RP) (flatBT t)"
    by (rule filter_cong) (auto simp: eq_commute)
  show ?thesis unfolding LP_eq RP_eq using flatBT_paren_balance[of t] .
qed

text \<open>命題（順序数項のカッコの個数が左右で等しいこと） (§7.1): in the \<open>\<Sigma>\<close>-string
  of any \<open>t \<in> T\<^bsub>B\<^esub>\<close> the letter \<open>\<^bold>(\<close> occurs as often as \<open>\<^bold>)\<close>.\<close>

lemma p_7_1_paren_balance:
  assumes "t \<in> T_B"
  shows "length (filter (\<lambda>x. x = LP) (flatBT t))
       = length (filter (\<lambda>x. x = RP) (flatBT t))"
  using assms by (rule m_7_1_paren_balance)

end

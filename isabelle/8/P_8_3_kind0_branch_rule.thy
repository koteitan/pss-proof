theory P_8_3_kind0_branch_rule
  imports Support_8_C
begin

text \<open>補題（第\<open>0\<close>種型基本列の基本分岐規則） (§8.3, article 3984): for \<open>M \<in> RT\<^bsub>PS\<^esub>\<close>,
  \<open>n \<in> \<nat>\<^sub>+\<close>, \<open>q \<in> \<nat>\<close>, with \<open>j\<^sub>1 = Lng M - 1\<close>, if there is a unique \<open>j\<^sub>0\<close> with
  \<open>(0,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>Next (0,j\<^sub>1)\<close>, \<open>M\<^bsub>1,j\<^sub>1\<^esub> = 0\<close>, \<open>q \<le> n-1\<close>, and \<open>j\<^sub>0\<close> is non-\<open>M\<close>-
  admissible, then \<open>(0,j\<^sub>0-1) <\<^bsub>M[n]\<^esub>\<^sup>Next (0,j\<^sub>0+q(j\<^sub>1-j\<^sub>0))\<close> and
  \<open>(1,j\<^sub>0-1) <\<^bsub>M[n]\<^esub>\<^sup>Next (1,j\<^sub>0+q(j\<^sub>1-j\<^sub>0))\<close>.\<close>

lemma p_8_3_kind0_branch_rule:
  fixes M :: pairseq
  assumes "M \<in> RT_PS" "0 < n"
    and "hasParent M 0 (Lng M - 1)"
    and "entry M 1 (Lng M - 1) = 0"
    and "q \<le> n - 1"
    and "\<not> adm M (parent M 0 (Lng M - 1))"
  shows "nextR (M[n]) 0 (parent M 0 (Lng M - 1) - 1)
            (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1)))
       \<and> nextR (M[n]) 1 (parent M 0 (Lng M - 1) - 1)
            (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1)))"
  by (rule m_8_3_kind0_branch_rule[OF assms])

end

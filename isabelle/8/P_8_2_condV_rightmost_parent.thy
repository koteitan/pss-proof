theory P_8_2_condV_rightmost_parent
  imports Support_8_C
begin

text \<open>補題（条件(V)の下での右端の親の基本性質） (§8.2, article 3602):
  for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> and \<open>m \<in> \<nat>\<close>, under
  「\<open>m < j'\<^sub>0\<close>」or「\<open>m = j'\<^sub>0 \<and> M\<^bsub>0,j'\<^sub>1\<^esub> = M\<^bsub>1,j'\<^sub>1\<^esub> \<and> Br M\<close> descending」,
  a unique \<open>j\<^sub>0\<close> satisfies (1)–(4).  \<open><\<^bsub>M\<^esub>\<^sup>Next\<close> on row 0 = \<open>nextR M 0\<close>.\<close>

lemma p_8_2_condV_rightmost_parent:
  fixes M :: pairseq and m :: nat
  defines "j1 \<equiv> Lng M - 1"
  defines "J1 \<equiv> Lng (Br M) - 1"
  defines "j0' \<equiv> Joints M ! J1"
  defines "j1' \<equiv> FirstNodes M ! J1"
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "Br M \<noteq> []"
    and "m < j0' \<or> (m = j0' \<and> entry M 0 j1' = entry M 1 j1' \<and> descending (Br M))"
  shows "\<exists>!j0.
      \<comment> \<open>(1)\<close> nextR M 0 j0 j1
    \<and> \<comment> \<open>(2)\<close> j0' \<le> j0
    \<and> \<comment> \<open>(3)\<close> (m < j0 \<or> entry M 0 j1 = entry M 1 j1)
    \<and> \<comment> \<open>(4)\<close> (m = j0 \<longrightarrow> j0 < TrMax M)"
  unfolding j1_def J1_def j0'_def j1'_def
  by (rule m_8_2_condV_rightmost_parent[OF assms(5) assms(6) assms(7)
        assms(8)[unfolded j0'_def j1'_def J1_def]])

end

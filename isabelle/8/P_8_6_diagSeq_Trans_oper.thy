theory P_8_6_diagSeq_Trans_oper
  imports Support_8_C
begin

text \<open>補題（公差\<open>(1,1)\<close>のペア数列の\<open>Trans\<close>の展開規則） (§8.6, content.md 5575):
  for \<open>u, j\<^sub>1 \<in> \<nat>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, with \<open>M := ((u+j,u+j))\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>1\<^esup> \<in> T\<^bsub>PS\<^esub>\<close>
  (\<open>= diagSeq u (u+j\<^sub>1)\<close>), if \<open>j\<^sub>1 > 1\<close> then
  \<open>Trans(M[n]) = D\<^sub>u D\<^bsub>u+j\<^sub>1-1\<^esub>\<^sup>n 0\<close>.  Transcribable: \<open>D\<^bsub>u+j\<^sub>1-1\<^esub>\<^sup>n 0\<close> is
  \<open>(Dpt (enat (u+j\<^sub>1-1)) ^^ n) 0\<^sub>B\<close>, then one outer \<open>D\<^sub>u\<close>.\<close>

lemma p_8_6_diagSeq_Trans_oper:
  fixes u j1 n :: nat
  defines "M \<equiv> diagSeq u (u + j1)"
  assumes "M \<in> T_PS" "0 < n" "j1 > 1"
  shows "Trans ((M::pairseq)[n]) = Dpt (enat u) ((Dpt (enat (u + j1 - 1)) ^^ n) 0\<^sub>B)"
  unfolding M_def
  by (rule m_8_6_diagSeq_Trans_oper_paper[OF assms(2)[unfolded M_def] assms(3) assms(4)])

end

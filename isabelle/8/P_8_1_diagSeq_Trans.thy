theory P_8_1_diagSeq_Trans
  imports Support_8_C
begin

subsection \<open>§8.1 条件(I)の下での展開規則 (Expansion rule under condition (I))\<close>

text \<open>補題（公差\<open>(1,1)\<close>のペア数列の\<open>Trans\<close>の基本性質） (§8.1, article 2837):
  for \<open>u, v \<in> \<nat>\<close> with \<open>u < v\<close>, the diagonal (公差\<open>(1,1)\<close>) pair sequence
  \<open>M = ((j,j))\<^bsub>j=u\<^esub>\<^bsup>v\<^esup>\<close> has \<open>Trans(M) = D\<^sub>u D\<^sub>v 0\<close>.  Modelling: \<open>((j,j))\<^bsub>j=u\<^esub>\<^bsup>v\<^esup>\<close>
  is the existing \<open>diagSeq u v\<close>; \<open>D\<^sub>u D\<^sub>v 0\<close> is \<open>Dpt (enat u) (Dpt (enat v) 0\<^sub>B)\<close>.\<close>

lemma p_8_1_diagSeq_Trans:
  assumes "u < v"
  shows "Trans (diagSeq u v) = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)"
  by (rule m_8_1_diagSeq_Trans[OF assms])

end

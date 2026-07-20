theory P_8_1_Trans_fseq_condI
  imports Support_8_C
begin

text \<open>命題（条件(I)の下での\<open>Trans\<close>と基本列の交換関係） (§8.1, article 2827):
  for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, if \<open>j\<^sub>1 = Lng M - 1 > 1\<close> and \<open>M\<close>
  satisfies condition (I) (\<open>transCondI M\<close>), then
    (1) \<open>Trans(M[n]) = Trans(M)[n-1]\<close> and
    (2) \<open>Trans(M[n]) < Trans(M)\<close>.
  Modelling: the Buchholz fundamental sequence \<open>a[k]\<close> is \<open>operB a (numBT k)\<close>;
  \<open><\<close> on \<open>T\<^bsub>B\<^esub>\<close> is \<open>lessBT\<close>; \<open>n \<in> \<nat>\<^sub>+\<close> is \<open>n \<ge> 1\<close>.\<close>

lemma p_8_1_Trans_fseq_condI:
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "n \<ge> 1"
    and "Lng M - 1 > 1" "transCondI M"
  shows "Trans (M[n]) = operB (Trans M) (numBT (n - 1))"
    and "lessBT (Trans (M[n])) (Trans M)"
  using y3g_p_8_1_Trans_fseq_condI[OF assms] by blast+

end

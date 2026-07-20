theory P_8_7_fseq_descend
  imports Support_8_C
begin

text \<open>補題（基本列の降下性） (§8.7, article 5869):
  for \<open>M \<in> ST\<^bsub>PS\<^esub>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, if \<open>Lng M > 1\<close> then
  \<open>Trans(M[n]) < Trans(M)\<close> (\<open><\<close> on \<open>T\<^bsub>B\<^esub>\<close> = \<open>lessBT\<close>).\<close>

lemma p_8_7_fseq_descend:
  assumes "M \<in> ST_PS" "n \<ge> 1" "Lng M > 1"
  shows "lessBT (Trans (M[n])) (Trans M)"
  by (rule y5_Trans_descend[OF assms])

end

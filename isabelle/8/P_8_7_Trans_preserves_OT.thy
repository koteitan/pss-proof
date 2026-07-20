theory P_8_7_Trans_preserves_OT
  imports Support_8_C
begin

text \<open>補題（\<open>Trans\<close>が標準形を保つこと） (§8.7, article 6122):
  for \<open>M \<in> ST\<^bsub>PS\<^esub>\<close>, \<open>Trans(M) \<in> OT\<^bsub>B\<^esub>\<close> (\<open>Trans\<close> lands in ordinal terms).\<close>

lemma p_8_7_Trans_preserves_OT:
  assumes "M \<in> ST_PS"
  shows "Trans M \<in> OT_B"
  by (rule y5_Trans_OT_B[OF assms])

end

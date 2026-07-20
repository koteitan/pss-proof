theory P_7_3_Trans_zeroT
  imports P_7_3_Mark_IncrFirst_Red
begin

subsection \<open>The four \<section>7 propositions, now on bare \<open>T\<^bsub>PS\<^esub>\<close>\<close>

theorem y3r_7_3_Trans_zeroT_TPS:
  assumes MT: "M \<in> T_PS"
  shows "zeroT M \<longleftrightarrow> Trans M = 0\<^sub>B"
  by (rule y3s_7_3_Trans_zeroT_TPS[OF MT y3r_RedStab_TPS[OF MT]])

text \<open>命題（\<open>Trans\<close>が零項性を保つこと） (§7.3, 2254).\<close>

lemma p_7_3_Trans_zeroT:
  assumes "M \<in> T_PS"
  shows "zeroT M \<longleftrightarrow> Trans M = 0\<^sub>B"
  using assms by (rule y3r_7_3_Trans_zeroT_TPS)

end

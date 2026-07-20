theory P_8_7_termination
  imports Support_8_C
begin

text \<open>定理（標準形ペア数列システムの停止性） (§8.7, article 5851):
  \<open>ST\<^bsub>PS\<^esub> \<times> \<nat>\<^sub>+ \<subseteq> Dom(F)\<close>.  Here \<open>Dom(F)\<close> is \<open>Fdom f\<close> (§5.4); the auxiliary
  map \<open>f : \<nat>\<^sub>+ \<to> \<nat>\<^sub>+\<close> is fixed (article 346), modelled by the positivity
  hypothesis \<open>1 \<le> k \<Longrightarrow> 1 \<le> f k\<close>.  The proof is the well-foundedness of \<open><\<close>
  on \<open>OT\<^bsub>B\<^esub>\<close> ([Buc1] Lemma 2.2) together with 基本列の降下性 + Trans が標準形を
  保つこと: each expansion step strictly decreases \<open>Trans\<close>.\<close>

theorem p_8_7_termination:
  assumes "M \<in> ST_PS" "n \<ge> 1" "\<And>k. 1 \<le> k \<Longrightarrow> 1 \<le> f k"
  shows "Fdom f M n"
  by (rule y5_Fdom[OF assms])

end

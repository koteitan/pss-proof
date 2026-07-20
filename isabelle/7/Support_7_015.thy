theory Support_7_015
  imports Frontier_7_018
begin

text \<open>命題（\<open>Trans\<close>の well-defined 性）, totality part, on \<open>RT\<^sub>PS\<close>.\<close>

lemma m_7_3_Trans_welldef:
  assumes "M \<in> RT_PS"
  shows "Trans_Mark_dom (Inl M)"
  using Trans_Mark_dom_RT_PS_aux assms by blast

lemma m_7_3_Mark_welldef:
  assumes "M \<in> RT_PS"
  shows "Trans_Mark_dom (Inr (M, m))"
  using Trans_Mark_dom_RT_PS_aux assms by blast

end

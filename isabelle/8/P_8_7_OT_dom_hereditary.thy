theory P_8_7_OT_dom_hereditary
  imports Support_8_C
begin

text \<open>補題（順序数項の共終数の遺伝性） (§8.7, article 5962):
  for \<open>t, t' \<in> T\<^bsub>B\<^esub>\<close> and \<open>s, b \<in> \<Sigma>\<^bsup><\<omega>\<^esup>\<close>, if \<open>dom(t') = \<nat>\<close>
  (\<open>domB t' = NatSet\<close>) and \<open>(s,t',b)\<close> is an scb-decomposition of \<open>t\<close>, then
  \<open>dom(t) = \<nat>\<close>.\<close>

lemma p_8_7_OT_dom_hereditary:
  assumes "t \<in> T_B" "t' \<in> T_B" "domB t' = NatSet" "scb_decomp t s (flatBT t') b"
  shows "domB t = NatSet"
  by (rule m_8_7_OT_dom_hereditary[OF assms])

end

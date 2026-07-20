theory P_8_7_OT_scb_recursive
  imports Support_8_C
begin

text \<open>補題（順序数項の再帰構造） (§8.7, article 5953):
  for \<open>t \<in> OT\<^bsub>B\<^esub>\<close>, \<open>c \<in> T\<^bsub>B\<^esub>\<close> and \<open>s, b \<in> \<Sigma>\<^bsup><\<omega>\<^esup>\<close> (= \<^typ>\<open>Sym list\<close>),
  if \<open>(s,c,b)\<close> is an scb-decomposition of \<open>t\<close> (\<open>scb_decomp t s (flatBT c) b\<close>)
  then \<open>c\<close> is an ordinal term (\<open>c \<in> OT\<close>).\<close>

lemma p_8_7_OT_scb_recursive:
  assumes "t \<in> OT_B" "c \<in> T_B" "scb_decomp t s (flatBT c) b"
  shows "c \<in> OT"
  by (rule m_8_7_OT_scb_recursive[OF assms])

end

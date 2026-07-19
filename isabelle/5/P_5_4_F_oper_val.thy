theory P_5_4_F_oper_val
  imports Pre_5
begin

lemma p_5_4_F_oper_val:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng M > 1" "Fdom f M n"
  shows "Fval f M n = Fval f (M[n]) (f n)"
  using assms(3) by (simp add: Fval.simps)

text \<open>m: 命題（F_M と基本列の関係） value part — discharges @{thm [source] p_5_4_F_oper_val}.\<close>

lemma m_5_4_F_oper_val:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng M > 1" "Fdom f M n"
  shows "Fval f M n = Fval f (M[n]) (f n)"
  using assms(3) by (simp add: Fval.simps)

end

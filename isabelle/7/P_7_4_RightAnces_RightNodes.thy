theory P_7_4_RightAnces_RightNodes
  imports P_7_3_Pred_Trans_descend
begin

theorem y3r_7_4_RightAnces_RightNodes_TPS:
  assumes MT: "M \<in> T_PS"
  shows "RightAnces M = RightNodes (Trans M)"
  by (rule y3s_7_4_RightAnces_RightNodes_TPS[OF y3r_RedStab_TPS[OF MT]])

text \<open>命題（\<open>RightNodes\<close>と\<open>RightAnces\<close>の関係） (§7.4, 2745).\<close>

lemma p_7_4_RightAnces_RightNodes:
  assumes "M \<in> T_PS"
  shows "RightAnces M = RightNodes (Trans M)"
  using assms by (rule y3r_7_4_RightAnces_RightNodes_TPS)

end

theory P_7_3_Pred_Trans_descend
  imports P_7_3_Trans_zeroT
begin

theorem y3r_7_3_Pred_Trans_descend_TPS:
  assumes MT: "M \<in> T_PS" and L: "1 < Lng M"
  shows "lessBT (Trans (Pred M)) (Trans M)"
  by (rule y3s_7_3_Pred_Trans_descend_TPS[OF MT y3r_RedStab_TPS[OF MT] L])

text \<open>命題（\<open>Pred\<close>の\<open>Trans\<close>に関する降下性） (§7.3, 2278).\<close>

lemma p_7_3_Pred_Trans_descend:
  assumes "M \<in> T_PS" "Lng M > 1"
  shows "lessBT (Trans (Pred M)) (Trans M)"
  using assms by (rule y3r_7_3_Pred_Trans_descend_TPS)

end

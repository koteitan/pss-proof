theory Support_6_047
  imports Frontier_6_067
begin

lemma kst_condAB_imp_reduced_core_only:
  assumes core:
    "\<And>N. N \<in> T_PS \<Longrightarrow> monoT N \<Longrightarrow> entry N 0 0 = 0 \<Longrightarrow> entry N 1 0 = 0
       \<Longrightarrow> RedCondA N \<Longrightarrow> RedCondB N \<Longrightarrow> Red N = N"
  assumes M0: "M \<in> T_PS" and condA0: "RedCondA M" and condB0: "RedCondB M"
  shows "Red M = M"
proof (rule kst_condAB_imp_reduced_cond[OF core _ M0 condA0 condB0])
  fix N assume A: "N \<in> T_PS" "monoT N" "0 < entry N 1 0" "RedCondA N" "RedCondB N"
  show "Red N = N"
    by (rule kst_condAB_imp_reduced_monoT_m10pos[OF core A(1) A(2) A(3) A(4) A(5)])
qed

end

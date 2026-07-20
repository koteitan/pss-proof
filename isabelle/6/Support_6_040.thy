theory Support_6_040
  imports Frontier_6_058
begin

lemma roper_base_Lng1:
  assumes MT: "M \<in> T_PS" and L1: "Lng M = 1"
  shows "(Red M)[n] = Red (M[n])"
proof -
  have opM: "M[n] = M" by (rule roper_oper_Lng1[OF L1])
  have "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  hence LR1: "Lng (Red M) = 1" using L1 by simp
  have "(Red M)[n] = Red M" by (rule roper_oper_Lng1[OF LR1])
  thus ?thesis using opM by simp
qed

end

theory Support_6_070
  imports P_6_5_Red_monoT
begin

lemma m_6_5_Red_not_multiT:
  assumes M: "M \<in> anchored_slice"
  shows "\<not> multiT (Red M)"
proof -
  have MT: "M \<in> T_PS" by (rule anchored_slice_imp_T_PS[OF M])
  show ?thesis
  proof (cases "zeroT M")
    case True
    hence "zeroT (Red M)" using m_6_5_Red_zeroT[OF MT] by simp
    thus ?thesis by (simp add: multiT_def)
  next
    case False
    hence "monoT M" using m_6_5_anchored_zeroT_or_monoT[OF M] by simp
    hence "monoT (Red M)" using m_6_5_Red_monoT_final[OF M] by simp
    thus ?thesis by (simp add: multiT_def)
  qed
qed

end

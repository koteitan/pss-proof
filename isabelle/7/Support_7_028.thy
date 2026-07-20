theory Support_7_028
  imports Frontier_7_033
begin

lemma Mark_funpow_IncrFirst:
  assumes MT: "M \<in> T_PS" and RR: "Red M \<in> RT_PS"
  shows "Mark ((IncrFirst ^^ k) M) m = Mark M m"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  let ?N = "(IncrFirst ^^ k) M"
  have NT: "?N \<in> T_PS" using MT by (rule T_PS_funpow_IncrFirst)
  have RN: "Red ?N \<in> RT_PS" using a1_Red_funpow_IncrFirst[OF MT] RR by simp
  have "(IncrFirst ^^ Suc k) M = IncrFirst ?N" by simp
  hence "Mark ((IncrFirst ^^ Suc k) M) m = Mark (IncrFirst ?N) m" by simp
  also have "\<dots> = Mark ?N m" by (rule m_7_3_Mark_IncrFirst[OF NT RN])
  also have "\<dots> = Mark M m" using Suc.IH by simp
  finally show ?case .
qed

end

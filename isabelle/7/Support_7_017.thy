theory Support_7_017
  imports P_7_3_twoColumn
begin

section \<open>§7.3 命題（\<open>Trans\<close>の\<open>(IncrFirst,Red)\<close>不変性） — A4-corrected domain\<close>

text \<open>\<open>Trans M = Trans (Red M)\<close> and \<open>Trans (IncrFirst M) = Trans M\<close> on the
  domain \<open>Red M \<in> RT\<^sub>PS\<close> (the article states them on all of \<open>T\<^sub>PS\<close>, but the
  (D) recursion only reaches a defined value when \<open>Red M\<close> is reduced —
  the same A4 idempotency caveat as the well-definedness).  The \<open>IncrFirst\<close>
  invariance is immediate from the \<open>Red\<close> one via
  @{thm [source] m_6_5_Red_IncrFirst}.\<close>

lemma m_7_3_Trans_Red:
  assumes RR: "Red M \<in> RT_PS"
  shows "Trans M = Trans (Red M)"
proof (cases "M \<in> RT_PS")
  case True
  hence "Red M = M" by (simp add: RT_PS_def)
  thus ?thesis by simp
next
  case False
  have domR: "Trans_Mark_dom (Inl (Red M))" by (rule m_7_3_Trans_welldef[OF RR])
  have domM: "Trans_Mark_dom (Inl M)"
    by (rule Trans_Mark.domintros(1)) (use False domR in \<open>simp_all\<close>)
  show ?thesis using Trans.psimps[OF domM] False by simp
qed

lemma m_7_3_Mark_Red:
  assumes RR: "Red M \<in> RT_PS"
  shows "Mark M m = Mark (Red M) m"
proof (cases "M \<in> RT_PS")
  case True
  hence "Red M = M" by (simp add: RT_PS_def)
  thus ?thesis by simp
next
  case False
  have domR: "Trans_Mark_dom (Inr (Red M, m))" by (rule m_7_3_Mark_welldef[OF RR])
  have domM: "Trans_Mark_dom (Inr (M, m))"
    by (rule Trans_Mark.domintros(2)) (use False domR in \<open>simp_all\<close>)
  show ?thesis using Mark.psimps[OF domM] False by simp
qed

lemma m_7_3_Trans_IncrFirst:
  assumes MT: "M \<in> T_PS" and RR: "Red M \<in> RT_PS"
  shows "Trans (IncrFirst M) = Trans M"
proof -
  have RI: "Red (IncrFirst M) = Red M" by (rule m_6_5_Red_IncrFirst[OF MT])
  have RRI: "Red (IncrFirst M) \<in> RT_PS" using RI RR by simp
  have "Trans (IncrFirst M) = Trans (Red (IncrFirst M))"
    by (rule m_7_3_Trans_Red[OF RRI])
  also have "\<dots> = Trans (Red M)" using RI by simp
  also have "\<dots> = Trans M" by (rule m_7_3_Trans_Red[OF RR, symmetric])
  finally show ?thesis .
qed

lemma m_7_3_Mark_IncrFirst:
  assumes MT: "M \<in> T_PS" and RR: "Red M \<in> RT_PS"
  shows "Mark (IncrFirst M) m = Mark M m"
proof -
  have RI: "Red (IncrFirst M) = Red M" by (rule m_6_5_Red_IncrFirst[OF MT])
  have RRI: "Red (IncrFirst M) \<in> RT_PS" using RI RR by simp
  have "Mark (IncrFirst M) m = Mark (Red (IncrFirst M)) m"
    by (rule m_7_3_Mark_Red[OF RRI])
  also have "\<dots> = Mark (Red M) m" using RI by simp
  also have "\<dots> = Mark M m" by (rule m_7_3_Mark_Red[OF RR, symmetric])
  finally show ?thesis .
qed

end

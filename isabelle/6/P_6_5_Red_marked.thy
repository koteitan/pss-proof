theory P_6_5_Red_marked
  imports P_6_5_admof_Red
begin

text \<open>系（\<open>Red\<close>が基点を保つこと） — a marked pair sequence stays marked under
  \<open>Red\<close>; in the article the codomain is \<open>RT\<^bsub>PS\<^esub>\<^sup>Marked\<close> (marked AND reduced),
  the reducedness being @{text p_6_5_Red_idem}.  \<open>RT\<^sub>PS\<close> itself is §6.6.\<close>

lemma m_6_5_Red_marked_final:
  assumes Mm: "(M, m) \<in> Marked" and M: "M \<in> anchored_slice"
  shows "(Red M, m) \<in> Marked"
proof -
  have MT: "M \<in> T_PS" by (rule anchored_slice_imp_T_PS[OF M])
  have admM: "adm M m" and leM: "leR M 0 m (Lng M - 1)"
    using Mm by (auto simp: Marked_def)
  have L: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  have RT: "Red M \<in> T_PS"
  proof -
    have "M \<noteq> []" using MT by (simp add: T_PS_def)
    hence "0 < Lng M" by (cases M) auto
    hence "0 < Lng (Red M)" using L by simp
    hence "Red M \<noteq> []" using length_greater_0_conv by blast
    thus ?thesis by (simp add: T_PS_def)
  qed
  have admR: "adm (Red M) m"
    using admM by (simp add: m_6_5_adm_Red_eq[OF M, symmetric])
  have leRR: "leR (Red M) 0 m (Lng (Red M) - 1)"
    using m_6_5_Red_le_final[OF M, of 0 m "Lng M - 1"] leM L by simp
  show ?thesis using RT admR leRR by (simp add: Marked_def)
qed

lemma p_6_5_Red_marked:
  assumes "(M, m) \<in> Marked" "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
  shows "(Red M, m) \<in> Marked"
  using assms by (rule m_6_5_Red_marked_final)

end

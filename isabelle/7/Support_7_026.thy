theory Support_7_026
  imports Frontier_7_031
begin

text \<open>An interior marked image has right-spine length \<open>\<ge> 2\<close> (its tail is
  nonzero by @{thm [source] Mark_tail_nonzero}).\<close>

lemma Mark_interior_RN_ge2:
  assumes MR: "M \<in> RT_PS" and mM: "(M, m) \<in> Marked"
    and pos: "0 < m" and lt: "m < Lng M - 1"
  shows "2 \<le> length (RightNodes (Mark M m))"
proof -
  obtain a0 a1 where RMark: "RightNodes (Mark M m) = [entry M 1 m] @ a1"
    using m_7_4_RightNodes_Mark[OF mM MR pos lt] by blast
  have tne: "Mark M m \<noteq> Dpt (enat (entry M 1 m)) 0\<^sub>B"
    using Mark_tail_nonzero mM MR lt by blast
  have disj: "Mark M m = 0\<^sub>B \<or> (\<exists>t. Mark M m = Dpt (enat (entry M 1 m)) t)"
    using Mark_leftend_form mM MR by blast
  have notz: "Mark M m \<noteq> 0\<^sub>B"
  proof
    assume "Mark M m = 0\<^sub>B"
    hence "RightNodes (Mark M m) = []" by simp
    thus False using RMark by simp
  qed
  from notz disj obtain t where mk: "Mark M m = Dpt (enat (entry M 1 m)) t" by blast
  have tne0: "t \<noteq> 0\<^sub>B" using tne mk by auto
  have "RightNodes (Mark M m) = entry M 1 m # RightNodes t"
    using mk by (simp add: rnsub_RightNodes_Dpt)
  moreover have "RightNodes t \<noteq> []" using tne0 by (simp add: rnsub_RightNodes_empty_iff)
  ultimately show ?thesis by (cases "RightNodes t") auto
qed

text \<open>\<open>Mark\<close> is injective on marked columns \<open>> 0\<close>: for \<open>0 < m0 < m1\<close> the
  right-spine of \<open>Mark M m0\<close> is strictly longer than that of \<open>Mark M m1\<close>
  (interior case by @{thm [source] RightNodes_seg_len_strict_mono}; the
  rightmost case by length \<open>1\<close> vs \<open>\<ge> 2\<close>).\<close>

lemma Mark_distinct:
  assumes MR: "M \<in> RT_PS" and m0M: "(M, m0) \<in> Marked" and m1M: "(M, m1) \<in> Marked"
    and pos: "0 < m0" and lt: "m0 < m1" and m1le: "m1 \<le> Lng M - 1"
  shows "Mark M m0 \<noteq> Mark M m1"
proof -
  have m0lt: "m0 < Lng M - 1" using lt m1le by simp
  have m1pos: "0 < m1" using pos lt by simp
  show ?thesis
  proof (cases "m1 < Lng M - 1")
    case True
    obtain b0 c0 where S0: "RightNodes (Trans (seg M 0 m0)) = b0 @ [entry M 1 m0]"
      and T0: "RightNodes (Trans M) = b0 @ [entry M 1 m0] @ c0"
      and R0: "RightNodes (Mark M m0) = [entry M 1 m0] @ c0"
      using m_7_4_RightNodes_Mark[OF m0M MR pos m0lt] by blast
    obtain b1 c1 where S1: "RightNodes (Trans (seg M 0 m1)) = b1 @ [entry M 1 m1]"
      and T1: "RightNodes (Trans M) = b1 @ [entry M 1 m1] @ c1"
      and R1: "RightNodes (Mark M m1) = [entry M 1 m1] @ c1"
      using m_7_4_RightNodes_Mark[OF m1M MR m1pos True] by blast
    have g: "length (RightNodes (Trans (seg M 0 m0)))
           < length (RightNodes (Trans (seg M 0 m1)))"
      by (rule RightNodes_seg_len_strict_mono[OF MR m0M pos lt m1le])
    have lb: "length b0 < length b1" using g S0 S1 by simp
    have q0: "length (RightNodes (Trans M)) = length b0 + 1 + length c0" using T0 by simp
    have q1: "length (RightNodes (Trans M)) = length b1 + 1 + length c1" using T1 by simp
    have "length c1 < length c0" using q0 q1 lb by linarith
    hence "length (RightNodes (Mark M m1)) < length (RightNodes (Mark M m0))"
      using R0 R1 by simp
    thus ?thesis by auto
  next
    case False
    hence m1eq: "m1 = Lng M - 1" using m1le by simp
    have L1: "1 < Lng M" using m0lt by simp
    have nz: "\<not> zeroT M" using L1 by (auto simp: zeroT_def)
    have "Mark M m1 = Dpt (enat (entry M 1 m1)) 0\<^sub>B"
      using m_7_3_Mark_rightmost1[OF m1M MR nz] m1eq by simp
    hence "length (RightNodes (Mark M m1)) = 1" by (simp add: rnsub_RightNodes_Dpt)
    moreover have "2 \<le> length (RightNodes (Mark M m0))"
      by (rule Mark_interior_RN_ge2[OF MR m0M pos m0lt])
    ultimately show ?thesis by auto
  qed
qed

end

theory Frontier_7_031
  imports Support_7_025
begin

text \<open>Key length-monotonicity for "Mark preserves order": the right-spine of
  \<open>Trans\<close> of a longer marked prefix is strictly longer.  Apply
  @{thm [source] m_7_4_RightNodes_Mark} to \<open>N = seg M 0 m1\<close> at column \<open>m0\<close>:
  \<open>RightNodes(Trans(seg M 0 m0))\<close> is a proper prefix of \<open>RightNodes(Trans(seg M 0 m1))\<close>,
  the extra suffix \<open>a1\<close> being nonempty because \<open>m0 < Lng N - 1\<close> makes
  \<open>Mark N m0\<close> have a nonzero tail (@{thm [source] Mark_tail_nonzero}).\<close>

lemma RightNodes_seg_len_strict_mono:
  assumes MR: "M \<in> RT_PS" and m0M: "(M, m0) \<in> Marked"
    and pos: "0 < m0" and lt: "m0 < m1" and m1le: "m1 \<le> Lng M - 1"
  shows "length (RightNodes (Trans (seg M 0 m0)))
       < length (RightNodes (Trans (seg M 0 m1)))"
proof -
  let ?N = "seg M 0 m1"
  have L1: "1 < Lng M" using pos lt m1le by linarith
  have m1ltM: "m1 < Lng M" using m1le L1 by linarith
  have NR: "?N \<in> RT_PS" by (rule seg_0_RT_PS[OF MR m1le])
  have LN: "Lng ?N = Suc m1" by simp
  have Nm0: "(?N, m0) \<in> Marked"
  proof -
    have "(seg M 0 m1, m0 - 0) \<in> Marked"
      by (rule m_6_3_marked_slice[OF m0M]) (use pos lt m1le in auto)
    thus ?thesis by simp
  qed
  have m0ltN: "m0 < Lng ?N - 1" using lt LN by simp
  obtain a0 a1 where
        RT: "RightNodes (Trans ?N) = a0 @ [entry ?N 1 m0] @ a1"
    and Rseg: "RightNodes (Trans (seg ?N 0 m0)) = a0 @ [entry ?N 1 m0]"
    and RMark: "RightNodes (Mark ?N m0) = [entry ?N 1 m0] @ a1"
    using m_7_4_RightNodes_Mark[OF Nm0 NR pos m0ltN] by blast
  have segeq: "seg ?N 0 m0 = seg M 0 m0"
  proof -
    have nN: "?N = take (Suc m1) M" by (rule seg_0_eq_take) (use m1ltM in linarith)
    have "seg ?N 0 m0 = take (Suc m0) ?N"
      by (rule seg_0_eq_take) (use m0ltN LN in linarith)
    also have "\<dots> = take (Suc m0) (take (Suc m1) M)" using nN by simp
    also have "\<dots> = take (Suc m0) M" using lt by (simp add: take_take min_def)
    also have "\<dots> = seg M 0 m0" by (rule seg_0_eq_take[symmetric]) (use m1ltM lt in linarith)
    finally show ?thesis .
  qed
  have a1ne: "a1 \<noteq> []"
  proof -
    have tne: "Mark ?N m0 \<noteq> Dpt (enat (entry ?N 1 m0)) 0\<^sub>B"
      using Mark_tail_nonzero Nm0 NR m0ltN by blast
    have disj: "Mark ?N m0 = 0\<^sub>B \<or> (\<exists>t. Mark ?N m0 = Dpt (enat (entry ?N 1 m0)) t)"
      using Mark_leftend_form Nm0 NR by blast
    have notz: "Mark ?N m0 \<noteq> 0\<^sub>B"
    proof
      assume "Mark ?N m0 = 0\<^sub>B"
      hence "RightNodes (Mark ?N m0) = []" by simp
      thus False using RMark by simp
    qed
    from notz disj obtain t where mk: "Mark ?N m0 = Dpt (enat (entry ?N 1 m0)) t" by blast
    have tne0: "t \<noteq> 0\<^sub>B" using tne mk by auto
    have "RightNodes (Mark ?N m0) = entry ?N 1 m0 # RightNodes t"
      using mk by (simp add: rnsub_RightNodes_Dpt)
    hence "a1 = RightNodes t" using RMark by simp
    moreover have "RightNodes t \<noteq> []" using tne0 by (simp add: rnsub_RightNodes_empty_iff)
    ultimately show ?thesis by simp
  qed
  have e1: "RightNodes (Trans (seg M 0 m0)) = a0 @ [entry ?N 1 m0]"
    using Rseg segeq by simp
  have "length (RightNodes (Trans (seg M 0 m0))) = length a0 + 1" using e1 by simp
  moreover have "length (RightNodes (Trans ?N)) = length a0 + 1 + length a1"
    using RT by simp
  ultimately show ?thesis using a1ne by simp
qed

end

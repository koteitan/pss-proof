theory Support_6_027
  imports Frontier_6_045
begin

text \<open>T2(ii): for the core diagonal \<open>diagSeq 0 v\<close> (\<open>v > 0\<close>), \<open>Pred\<close> stays a core
  diagonal and \<open>Red (Pred (diagSeq 0 v)) = butlast (Red (diagSeq 0 v))\<close>, both
  equal to \<open>diagSeq 0 (v - 1)\<close>.\<close>

lemma Red_Pred_core_diagSeq:
  assumes vpos: "0 < v"
  shows "Red (Pred (diagSeq 0 v)) = butlast (Red (diagSeq 0 v))"
proof -
  obtain w where vw: "v = Suc w" using vpos by (cases v) auto
  have w0: "(0::nat) \<le> w" by simp
  \<comment> \<open>\<open>Pred (diagSeq 0 (Suc w)) = diagSeq 0 w\<close>, a core diagonal.\<close>
  have predM: "Pred (diagSeq 0 v) = diagSeq 0 w"
    using vw Pred_diagSeq_Suc[OF w0] by simp
  have "Red (Pred (diagSeq 0 v)) = Red (diagSeq 0 w)" by (simp add: predM)
  also have "\<dots> = diagSeq 0 w" by (rule Red_core_diagSeq)
  also have "\<dots> = butlast (diagSeq 0 v)"
    using vw butlast_diagSeq[of 0 v] vpos by simp
  \<comment> \<open>\<open>butlast_diagSeq\<close> needs \<open>0 \<le> v\<close> (trivial) and \<open>0 < v\<close> (\<open>vpos\<close>); \<open>v - 1 = w\<close>.\<close>
  also have "\<dots> = butlast (Red (diagSeq 0 v))" by (simp add: Red_core_diagSeq)
  finally show ?thesis .
qed

end

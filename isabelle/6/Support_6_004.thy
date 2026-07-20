theory Support_6_004
  imports Frontier_6_020
begin

text \<open>Both rows are strictly increasing along the trunk: a consecutive trunk
  step \<open>k \<rightarrow> k+1\<close> (\<open>k < TrMax M\<close>) strictly increases each row's entry, hence so
  does any forward jump within the trunk.\<close>

lemma trunk_step_lt:
  assumes M: "M \<in> T_PS" and i: "i = 0 \<or> i = 1" and k: "k < TrMax M"
  shows "entry M i k < entry M i (Suc k)"
proof -
  have nx: "nextR M 1 k (Suc k)" using TrMax_in_S[OF M] k by simp
  from i show ?thesis
  proof
    assume i0: "i = 0"
    have le: "leR M 0 k (Suc k)" using nx by (auto simp: leR_def nextR_def nextrel1_def)
    have "entry M 0 k < entry M 0 (Suc k)"
      by (rule m_5_1_ancestor_basic_1[OF M _ _ le]) auto
    thus ?thesis using i0 by simp
  next
    assume i1: "i = 1"
    have "entry M 1 k < entry M 1 (Suc k)" using nx by (auto simp: nextR_def nextrel1_def)
    thus ?thesis using i1 by simp
  qed
qed

end

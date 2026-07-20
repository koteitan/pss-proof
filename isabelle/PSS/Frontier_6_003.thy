theory Frontier_6_003
  imports P_6_2_multi_crit_12
begin

text \<open>Basic facts about the slice \<open>seg M a b\<close>.\<close>

lemma Lng_seg[simp]: "Lng (seg M a b) = Suc b - a"
  by (simp add: seg_def del: upt_Suc)

lemma entry_seg:
  assumes "j < Lng (seg M a b)"
  shows "entry (seg M a b) i j = entry M i (a + j)"
proof -
  have lj: "j < Suc b - a" using assms by simp
  hence "a + j < Suc b" by simp
  hence "[a..<Suc b] ! j = a + j" by (simp add: nth_upt del: upt_Suc)
  moreover have "j < length [a..<Suc b]" using lj by (simp add: length_upt del: upt_Suc)
  ultimately show ?thesis by (simp add: seg_def entry_def del: upt_Suc)
qed

end

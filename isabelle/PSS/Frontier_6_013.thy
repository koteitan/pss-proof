theory Frontier_6_013
  imports P_6_4_P_IdxSum_char_2
begin

text \<open>\<open>IdxSum Q\<close> is monotone in the index (up to \<open>length Q\<close>).\<close>

lemma idxsum_mono:
  assumes "J0 \<le> J1" "J1 \<le> length Q"
  shows "IdxSum Q ! J0 \<le> IdxSum Q ! J1"
proof -
  have "IdxSum Q ! J0 = sum_list (map length (take J0 Q))"
    using assms by (simp add: idxsum_nth)
  moreover have "IdxSum Q ! J1 = sum_list (map length (take J1 Q))"
    using assms(2) by (simp add: idxsum_nth)
  moreover have "sum_list (map length (take J0 Q)) \<le> sum_list (map length (take J1 Q))"
    using assms(1) by (rule idxsum_sum_take_mono)
  ultimately show ?thesis by simp
qed

end

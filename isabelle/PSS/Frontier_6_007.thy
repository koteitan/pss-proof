theory Frontier_6_007
  imports P_6_2_P_additive
begin

text \<open>The cut index \<open>Pcut M\<close> satisfies its defining predicate when \<open>M\<close> is multi.\<close>

lemma Pcut_le:
  assumes "1 < Lng M"
  shows "0 < Pcut M \<and> Pcut M \<le> Lng M - 1 \<and> leR M 0 (Pcut M) (Lng M - 1)"
proof -
  let ?P = "\<lambda>j. 0 < j \<and> j \<le> Lng M - 1 \<and> leR M 0 j (Lng M - 1)"
  have wit: "?P (Lng M - 1)"
    using assms by (auto simp: leR_def le0_def)
  have "?P (Pcut M)"
    unfolding Pcut_def by (rule LeastI[where P = ?P, OF wit])
  thus ?thesis .
qed

text \<open>\<open>drop k M\<close> is the slice \<open>seg M k (Lng M - 1)\<close> when \<open>k < Lng M\<close>.\<close>

lemma drop_eq_seg:
  assumes "k < Lng M"
  shows "drop k M = seg M k (Lng M - 1)"
proof -
  have "Suc (Lng M - 1) = Lng M" using assms by simp
  hence eq: "seg M k (Lng M - 1) = map (nth M) [k..<Lng M]"
    by (simp add: seg_def del: upt_Suc)
  have "drop k M = map (nth M) [k..<Lng M]"
    by (intro nth_equalityI) (auto simp: nth_upt)
  thus ?thesis using eq by simp
qed

end

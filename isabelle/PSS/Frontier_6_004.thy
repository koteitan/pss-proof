theory Frontier_6_004
  imports P_6_2_mono_prefix
begin

text \<open>A non-empty multi-term pair sequence has length \<open>> 1\<close>.\<close>

lemma multiT_imp_Lng_gt1:
  assumes "M \<in> T_PS" "multiT M"
  shows "Lng M > 1"
proof (rule ccontr)
  assume "\<not> Lng M > 1"
  with assms(1) have L1: "Lng M = 1" by (cases M) (auto simp: T_PS_def)
  from assms(2) have "\<not> zeroT M" "\<not> monoT M" by (simp_all add: multiT_def)
  from L1 \<open>\<not> zeroT M\<close> have "monoT M" by (simp add: monoT_def leR_def le0_def)
  with \<open>\<not> monoT M\<close> show False ..
qed

text \<open>\<open>P M\<close> is always non-empty.\<close>

lemma P_nonempty: "P M \<noteq> []"
  by (subst P.simps) simp

end

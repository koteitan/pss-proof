theory P_6_4_P_IdxSum
  imports Frontier_6_011
begin

subsection \<open>§6.4 幹と枝\<close>

text \<open>命題（\<open>P\<close>と\<open>IdxSum\<close>の関係） — each component of \<open>P M\<close> is the \<open>M\<close>-slice
  between consecutive \<open>IdxSum\<close> values.\<close>

text \<open>m: 命題（\<open>P\<close>と\<open>IdxSum\<close>の関係） — discharges @{text p_6_4_P_IdxSum}.
  Each component of \<open>P M\<close> is the \<open>M\<close>-slice between consecutive \<open>IdxSum\<close> values.\<close>

lemma m_6_4_P_IdxSum:
  assumes "M \<in> T_PS" "J \<le> Lng (P M) - 1"
  shows "(P M) ! J = seg M (IdxSum (P M) ! J) (IdxSum (P M) ! (J + 1) - 1)"
proof -
  let ?Q = "P M"
  have ne: "?Q \<noteq> []" by (rule P_nonempty)
  hence JL: "J < length ?Q" using assms(2) by (cases ?Q) auto
  let ?a = "IdxSum ?Q ! J"
  let ?b = "IdxSum ?Q ! (J + 1) - 1"
  have aval: "?a = sum_list (map length (take J ?Q))"
    using JL by (simp add: idxsum_nth)
  have diff: "IdxSum ?Q ! (J + 1) = ?a + length (?Q ! J)"
    using JL by (rule idxsum_diff)
  have concatM: "concat ?Q = M" by (rule idxsum_concat_P)
  \<comment> \<open>length of \<open>M\<close> via concat\<close>
  have lenM: "length M = sum_list (map length ?Q)"
    using concatM by (metis length_concat)
  \<comment> \<open>the block equals the take/drop slice\<close>
  have block: "?Q ! J = take (length (?Q ! J)) (drop ?a M)"
    using idxsum_concat_block[OF JL] aval concatM by (simp del: P.simps)
  \<comment> \<open>range bound: \<open>?a + length (?Q!J) \<le> length M\<close>\<close>
  have rangeb: "?a + length (?Q ! J) \<le> length M"
  proof -
    have "?a + length (?Q ! J) = sum_list (map length (take (Suc J) ?Q))"
      using aval JL by (simp add: take_Suc_conv_app_nth)
    also have "\<dots> \<le> sum_list (map length (take (length ?Q) ?Q))"
      using JL by (intro idxsum_sum_take_mono) simp
    also have "\<dots> = sum_list (map length ?Q)" by simp
    finally show ?thesis using lenM by simp
  qed
  \<comment> \<open>\<open>Suc ?b = IdxSum ?Q ! (J+1)\<close>\<close>
  have lenpos: "0 < length (?Q ! J)"
    using idxsum_P_component_nonempty[OF assms(1) JL] by simp
  have sucb: "Suc ?b = ?a + length (?Q ! J)"
    using diff lenpos by simp
  have "seg M ?a ?b = map (nth M) [?a..<Suc ?b]"
    by (simp add: seg_def del: upt_Suc)
  also have "\<dots> = map (nth M) [?a..<?a + length (?Q ! J)]"
    by (simp only: sucb)
  also have "\<dots> = take (length (?Q ! J)) (drop ?a M)"
    using rangeb by (rule map_nth_range_eq_take_drop)
  also have "\<dots> = ?Q ! J" using block by simp
  finally show ?thesis by simp
qed

lemma p_6_4_P_IdxSum:
  assumes "M \<in> T_PS" "J \<le> Lng (P M) - 1"
  shows "(P M) ! J = seg M (IdxSum (P M) ! J) (IdxSum (P M) ! (J + 1) - 1)"
  using assms by (rule m_6_4_P_IdxSum)

end

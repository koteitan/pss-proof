theory P_6_2_nonmulti_oper_1
  imports Frontier_6_014
begin

text \<open>命題（非複項性と基本列の関係） — for a non-multi \<open>M\<close>, \<open>P(M[n])\<close> is either
  \<open>n\<close> copies of \<open>Pred M\<close> or the singleton \<open>[M[n]]\<close>.\<close>

text \<open>m: 命題（非複項性と基本列の関係）(1) — \<open>n\<close> copies of \<open>Pred M\<close>.\<close>

lemma m_6_2_nonmulti_oper_1:
  assumes M: "M \<in> T_PS" and n: "n \<ge> 1" and nm: "\<not> multiT M"
    and par: "nextR M 0 0 (Lng M - 1)" and e1: "entry M 1 (Lng M - 1) = 0"
  shows "P (M[n]) = replicate n (Pred M)"
proof -
  let ?j1 = "Lng M - 1"
  \<comment> \<open>\<open>nextR M 0 0 ?j1\<close> forces \<open>Lng M > 1\<close>\<close>
  have nr0: "nextrel0 M 0 ?j1" using par by (simp add: nextR_def)
  have j1pos: "0 < ?j1" using nr0 by (simp add: nextrel0_def)
  have L: "1 < Lng M" using j1pos by simp
  have nz: "?j1 \<noteq> 0" using L by simp
  \<comment> \<open>last pair is not \<open>(0,0)\<close> (row 0 entry is positive)\<close>
  have e0pos: "entry M 0 ?j1 > 0" using nr0 by (simp add: nextrel0_def)
  have notzero: "\<not> (entry M 0 ?j1 = 0 \<and> entry M 1 ?j1 = 0)" using e0pos by simp
  \<comment> \<open>\<open>i1 = 0\<close> since the last second coordinate is 0\<close>
  have i1: "idx1 M ?j1 = 0" using e1 by (simp add: idx1_def)
  \<comment> \<open>the row-0 parent of \<open>?j1\<close> is \<open>0\<close>\<close>
  have ex1: "\<exists>!j0. nextR M 0 j0 ?j1"
    by (metis idxsum_ex1_parent0_iff par)
  have hp: "hasParent M (idx1 M ?j1) ?j1"
    unfolding i1 hasParent_def using ex1 .
  have parent0: "parent M (idx1 M ?j1) ?j1 = 0"
    unfolding i1 parent_def by (rule the1_equality[OF ex1 par])
  \<comment> \<open>operator expands with zero increments and zero offset\<close>
  have op: "M[n] = concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1]) [0..<n])"
  proof -
    have "M[n] = take (parent M (idx1 M ?j1) ?j1) M @
        concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j +
                  k * (if 0 < idx1 M ?j1 then entry M 0 ?j1 - entry M 0 (parent M (idx1 M ?j1) ?j1) else 0),
                              entry M 1 j +
                  k * (if 1 < idx1 M ?j1 then entry M 1 ?j1 - entry M 1 (parent M (idx1 M ?j1) ?j1) else 0)))
                              [parent M (idx1 M ?j1) ?j1..<?j1]) [0..<n])"
      using poper_oper_expand[OF L notzero hp, of n] by (simp add: Let_def)
    thus ?thesis using i1 parent0 by simp
  qed
  \<comment> \<open>each block equals \<open>Pred M = take ?j1 M\<close>\<close>
  have predtake: "Pred M = take ?j1 M" using L by (simp add: Pred_def butlast_conv_take)
  have block: "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] = Pred M"
  proof -
    have jL: "?j1 \<le> Lng M" by simp
    have "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] = take ?j1 M"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1]) = length (take ?j1 M)"
        using jL by simp
    next
      fix i assume "i < length (map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1])"
      hence ilt: "i < ?j1" by simp
      hence "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] ! i = (entry M 0 i, entry M 1 i)"
        by (simp add: nth_upt)
      also have "\<dots> = M ! i" by (rule entry_pair)
      also have "\<dots> = take ?j1 M ! i" using ilt by (simp add: nth_take)
      finally show "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] ! i = take ?j1 M ! i" .
    qed
    thus ?thesis using predtake by simp
  qed
  have opn: "M[n] = concat (replicate n (Pred M))"
  proof -
    have "M[n] = concat (map (\<lambda>k. Pred M) [0..<n])" using op block by simp
    also have "\<dots> = concat (replicate n (Pred M))" by (simp add: map_replicate_const)
    finally show ?thesis .
  qed
  \<comment> \<open>\<open>Pred M\<close> is a non-empty non-multi sequence\<close>
  have predNM: "\<not> multiT (Pred M)" by (rule nonmulti_Pred[OF M nm L])
  have predT: "Pred M \<in> T_PS" using L by (cases M) (auto simp: T_PS_def Pred_def)
  show ?thesis
    using opn P_concat_replicate_nonmulti[OF predT predNM n] by simp
qed

lemma p_6_2_nonmulti_oper_1:
  assumes "M \<in> T_PS" "n \<ge> 1" "\<not> multiT M"
    "nextR M 0 0 (Lng M - 1)" "entry M 1 (Lng M - 1) = 0"
  shows "P (M[n]) = replicate n (Pred M)"
  using assms by (rule m_6_2_nonmulti_oper_1)

end

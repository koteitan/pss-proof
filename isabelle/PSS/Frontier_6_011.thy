theory Frontier_6_011
  imports P_6_2_P_oper_2
begin

section \<open>§6.4 幹と枝\<close>

text \<open>
  The auto-generated \<open>P.simps\<close> is a non-terminating rewrite (it always unfolds
  \<open>P\<close> once more); throughout this section we keep it OFF as a default simp rule
  and unfold \<open>P\<close> only explicitly via \<open>subst P.simps\<close>.
\<close>

declare P.simps[simp del]

text \<open>
  FOUNDATIONAL helper: the components of \<open>P M\<close> concatenate back to \<open>M\<close>.
  By the recursion of \<open>P\<close>: in the multi case \<open>P M = P (take c M) @ [drop c M]\<close>,
  so \<open>concat (P M) = concat (P (take c M)) @ drop c M = take c M @ drop c M = M\<close>
  using the IH on \<open>take c M\<close>.
\<close>

lemma idxsum_concat_P: "concat (P M) = M"
proof (induction M rule: P.induct)
  case (1 M)
  show ?case
  proof (cases "multiT M \<and> 1 < Lng M")
    case True
    hence step: "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
      by (subst P.simps) simp
    have IH: "concat (P (take (Pcut M) M)) = take (Pcut M) M"
      using True "1.IH" by blast
    have "concat (P M) = concat (P (take (Pcut M) M)) @ drop (Pcut M) M"
      by (simp only: step) simp
    also have "\<dots> = take (Pcut M) M @ drop (Pcut M) M" by (simp only: IH)
    also have "\<dots> = M" by simp
    finally show ?thesis .
  next
    case False
    hence "P M = [M]" by (subst P.simps) (simp only: if_not_P if_False)
    thus ?thesis by simp
  qed
qed

text \<open>The \<open>J\<close>-th value of \<open>IdxSum Q\<close> is the cumulative length sum of the first \<open>J\<close> blocks.\<close>

lemma idxsum_nth:
  assumes "J \<le> length Q"
  shows "IdxSum Q ! J = sum_list (map length (take J Q))"
proof -
  have JL: "J < length [0..<Suc (length Q)]" using assms by simp
  have "IdxSum Q ! J = (\<lambda>J. sum_list (map length (take J Q))) ([0..<Suc (length Q)] ! J)"
    unfolding IdxSum_def using JL by (rule nth_map)
  also have "[0..<Suc (length Q)] ! J = J" using assms by (simp del: upt_Suc)
  finally show ?thesis by simp
qed

text \<open>Cumulative length sums are monotone in the prefix length.\<close>

lemma idxsum_sum_take_mono:
  assumes "J0 \<le> J1"
  shows "sum_list (map length (take J0 Q)) \<le> sum_list (map length (take J1 Q))"
proof -
  have "take J0 Q = take J0 (take J1 Q)"
    using assms by (simp add: min.absorb1)
  hence "\<exists>ys. take J1 Q = take J0 Q @ ys"
    by (metis append_take_drop_id)
  then obtain ys where "take J1 Q = take J0 Q @ ys" by blast
  thus ?thesis by simp
qed

text \<open>The successive difference of \<open>IdxSum\<close> is the length of the \<open>J\<close>-th block.\<close>

lemma idxsum_diff:
  assumes "J < length Q"
  shows "IdxSum Q ! (J + 1) = IdxSum Q ! J + length (Q ! J)"
proof -
  have a: "IdxSum Q ! J = sum_list (map length (take J Q))"
    using assms by (simp add: idxsum_nth)
  have b: "IdxSum Q ! (J + 1) = sum_list (map length (take (Suc J) Q))"
    using assms by (simp add: idxsum_nth)
  have "take (Suc J) Q = take J Q @ [Q ! J]"
    using assms by (simp add: take_Suc_conv_app_nth)
  hence "sum_list (map length (take (Suc J) Q))
         = sum_list (map length (take J Q)) + length (Q ! J)" by simp
  thus ?thesis using a b by simp
qed

text \<open>A list-level block-extraction fact: the \<open>J\<close>-th block of \<open>concat Q\<close> lies between
  its cumulative length sums.\<close>

lemma idxsum_concat_block:
  assumes "J < length Q"
  shows "Q ! J = take (length (Q ! J)) (drop (sum_list (map length (take J Q))) (concat Q))"
proof -
  have decomp: "concat Q = concat (take J Q) @ Q ! J @ concat (drop (Suc J) Q)"
  proof -
    have "Q = take J Q @ Q ! J # drop (Suc J) Q"
      using assms by (rule id_take_nth_drop)
    hence "concat Q = concat (take J Q @ Q ! J # drop (Suc J) Q)" by simp
    thus ?thesis by simp
  qed
  have len: "length (concat (take J Q)) = sum_list (map length (take J Q))"
    by (simp add: length_concat)
  have "drop (sum_list (map length (take J Q))) (concat Q)
        = Q ! J @ concat (drop (Suc J) Q)"
    by (subst decomp) (simp add: len)
  thus ?thesis by simp
qed

text \<open>\<open>map (nth M) [a..<a+n]\<close> is \<open>take n (drop a M)\<close> when in range.\<close>

lemma map_nth_range_eq_take_drop:
  assumes "a + n \<le> length M"
  shows "map (nth M) [a..<a + n] = take n (drop a M)"
  using assms by (intro nth_equalityI) (auto simp: nth_drop)

text \<open>Each component of \<open>P M\<close> is non-empty (being zero- or mono-term).\<close>

lemma idxsum_P_component_nonempty:
  assumes "M \<in> T_PS" "J < length (P M)"
  shows "Lng (P M ! J) > 0"
proof -
  have "P M ! J \<in> set (P M)" using assms(2) by (rule nth_mem)
  hence "zeroT (P M ! J) \<or> monoT (P M ! J)"
    using m_6_2_P_components_1[OF assms(1)] by blast
  thus ?thesis
  proof
    assume "zeroT (P M ! J)"
    thus ?thesis by (simp add: zeroT_def)
  next
    assume "monoT (P M ! J)"
    hence "leR (P M ! J) 0 0 (Lng (P M ! J) - 1)" by (simp add: monoT_def)
    thus ?thesis by (simp add: leR_def le0_def)
  qed
qed

end

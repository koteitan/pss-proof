theory Frontier_6_039
  imports Support_6_021
begin

text \<open>§6.8 geomB — the ANCHOR-AT-\<open>k\<close> bridge (a leftend \<open>k\<close> pins the anchor from
  BELOW).  Dual of @{thm [source] anchor_lt_of_uniform_witness}: if an index \<open>k\<close>
  is a row-0 LEFT-MINIMUM of \<open>S\<close> (\<open>\<forall>j<k. entry S 0 k \<le> entry S 0 j\<close>) and
  \<open>k \<le> Lng S - 1\<close>, then \<open>k\<close> is a leftend (an \<open>IdxSum\<close> value,
  @{thm [source] idxsum_lmin_leftend}); since the last anchor
  \<open>c = IdxSum (P S) ! (length (P S)-1)\<close> is the LARGEST leftend
  (@{thm [source] idxsum_mono}), \<open>k \<le> c\<close>.  Combined with the upper bound
  \<open>c \<le> k\<close> of @{thm [source] oper_d1pos_clt_regB} this pins \<open>c = k\<close>.\<close>

lemma anchor_ge_of_leftmin:
  fixes S :: pairseq
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
  assumes ST: "S \<in> T_PS"
    and kle: "k \<le> Lng S - 1"
    and lmin: "\<forall>j < k. entry S 0 k \<le> entry S 0 j"
  shows "k \<le> c"
proof -
  obtain J where JL: "J < length (P S)" and Jk: "IdxSum (P S) ! J = k"
    using idxsum_lmin_leftend[OF ST kle] lmin by auto
  have "IdxSum (P S) ! J \<le> IdxSum (P S) ! (length (P S) - 1)"
    by (rule idxsum_mono) (use JL in auto)
  thus ?thesis using Jk unfolding c_def by simp
qed

end

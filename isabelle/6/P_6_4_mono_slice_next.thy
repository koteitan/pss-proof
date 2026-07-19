theory P_6_4_mono_slice_next
  imports P_6_2_nonmulti_oper_2
begin

text \<open>命題（切片の単項成分と\<open><\<^bsub>M\<^esub>\<^sup>Next\<close>の関係）.\<close>

text \<open>m: 命題（切片の単項成分と\<open><\<^bsub>M\<^esub>\<^sup>Next\<close>の関係） — discharges
  @{text p_6_4_mono_slice_next}.\<close>

lemma m_6_4_mono_slice_next:
  assumes "M \<in> PT_PS" "0 < j0" "j0 \<le> Lng M - 1"
    "J \<le> Lng (P (seg M j0 (Lng M - 1))) - 1"
  shows "hasParent M 0 (j0 + IdxSum (P (seg M j0 (Lng M - 1))) ! J)
       \<and> parent M 0 (j0 + IdxSum (P (seg M j0 (Lng M - 1))) ! J) < j0"
proof -
  let ?N = "seg M j0 (Lng M - 1)"
  let ?Q = "P ?N"
  let ?k = "IdxSum ?Q ! J"
  have MT: "M \<in> T_PS" and monoM: "monoT M" using assms(1) by (auto simp: PT_PS_def)
  have LM: "Lng M > 0" using MT by (cases M) (auto simp: T_PS_def)
  have j0LM: "j0 < Lng M" using assms(3) LM by linarith
  \<comment> \<open>The slice is non-empty, hence in \<open>T_PS\<close>.\<close>
  have LN: "Lng ?N = Suc (Lng M - 1) - j0" by simp
  have LNpos: "Lng ?N > 0" using j0LM LM by simp
  have Nne: "?N \<noteq> []" using LNpos length_greater_0_conv by blast
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have ne: "?Q \<noteq> []" by (rule P_nonempty)
  hence JL: "J < length ?Q" using assms(4) by (cases ?Q) auto
  \<comment> \<open>\<open>?k\<close> is a row-0 left-minimum of \<open>?N\<close>, in range.\<close>
  have lm: "?k \<le> Lng ?N - 1
          \<and> (\<forall>j < ?k. entry ?N 0 j \<ge> entry ?N 0 ?k)"
    by (rule idxsum_leftend_lmin[OF NT JL])
  hence krange: "?k \<le> Lng ?N - 1" and lmin: "\<forall>j < ?k. entry ?N 0 j \<ge> entry ?N 0 ?k"
    by blast+
  have kN: "?k < Lng ?N" using krange LNpos by simp
  have kabsLM: "j0 + ?k < Lng M" using kN LN j0LM by simp
  \<comment> \<open>Translate the left-minimum to \<open>M\<close>: every \<open>j'\<in>[j0, j0+?k)\<close> has
      \<open>entry M 0 j' \<ge> entry M 0 (j0+?k)\<close>.\<close>
  have ek: "entry ?N 0 ?k = entry M 0 (j0 + ?k)" using kN by (simp add: entry_seg)
  have lminM: "\<forall>j'. j0 \<le> j' \<and> j' < j0 + ?k \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j0 + ?k)"
  proof (intro allI impI)
    fix j' assume a: "j0 \<le> j' \<and> j' < j0 + ?k"
    let ?j = "j' - j0"
    have jk: "?j < ?k" using a by linarith
    hence jN: "?j < Lng ?N" using kN by simp
    have "entry ?N 0 ?j \<ge> entry ?N 0 ?k" using lmin jk by blast
    moreover have "entry ?N 0 ?j = entry M 0 j'" using jN a by (simp add: entry_seg)
    ultimately show "entry M 0 j' \<ge> entry M 0 (j0 + ?k)" using ek by simp
  qed
  \<comment> \<open>\<open>M\<close> is mono, so \<open>(0,0) \<le>\<^sub>M (0, Lng M - 1)\<close>, hence \<open>entry M 0 0 < entry M 0 (j0+?k)\<close>.\<close>
  have le00: "leR M 0 0 (Lng M - 1)" using monoM by (simp add: monoT_def)
  have lt0: "entry M 0 0 < entry M 0 (j0 + ?k)"
  proof (rule m_5_1_ancestor_basic_1[OF MT _ _ le00])
    show "0 < j0 + ?k" using assms(2) by simp
    show "j0 + ?k \<le> Lng M - 1" using kabsLM by simp
  qed
  \<comment> \<open>A row-0 parent of \<open>j0+?k\<close> exists in \<open>M\<close>.\<close>
  obtain p where p: "0 \<le> p" "p < j0 + ?k" "nextR M 0 p (j0 + ?k)"
    using m_5_1_parent_exists_1[OF MT _ kabsLM lt0] assms(2) by auto
  have ex1: "\<exists>!j0'. nextR M 0 j0' (j0 + ?k)"
    using p(3) idxsum_ex1_parent0_iff by metis
  hence hp: "hasParent M 0 (j0 + ?k)" by (simp add: hasParent_def)
  \<comment> \<open>\<open>parent\<close> is exactly \<open>p\<close>, and \<open>p < j0\<close> since all of \<open>[j0,j0+?k)\<close> are \<open>\<ge>\<close>.\<close>
  have parent_eq: "parent M 0 (j0 + ?k) = p"
    unfolding parent_def using p(3) ex1
    by (rule the1_equality[rotated])
  have pval: "entry M 0 p < entry M 0 (j0 + ?k)"
    using p(3) by (auto simp: nextR_def nextrel0_def)
  have plt: "p < j0"
  proof (rule ccontr)
    assume "\<not> p < j0"
    hence "j0 \<le> p" by simp
    hence "entry M 0 p \<ge> entry M 0 (j0 + ?k)" using lminM p(2) by simp
    thus False using pval by simp
  qed
  show ?thesis using hp parent_eq plt by simp
qed


lemma p_6_4_mono_slice_next:
  assumes "M \<in> PT_PS" "0 < j0" "j0 \<le> Lng M - 1"
    "J \<le> Lng (P (seg M j0 (Lng M - 1))) - 1"
  shows "hasParent M 0 (j0 + IdxSum (P (seg M j0 (Lng M - 1))) ! J)
       \<and> parent M 0 (j0 + IdxSum (P (seg M j0 (Lng M - 1))) ! J) < j0"
  using assms by (rule m_6_4_mono_slice_next)

end

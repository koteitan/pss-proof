theory Support_6_045
  imports Frontier_6_065
begin

text \<open>In a \<open>monoT\<close> sequence with \<open>M\<^bsub>0,0\<^esub>=0\<close>, every node \<open>k \<ge> 1\<close> has a unique
  row-0 parent: \<open>monoT\<close> gives \<open>M\<^bsub>0,0\<^esub> < M\<^bsub>0,k\<^esub>\<close> (@{thm [source] m_6_2_multi_crit_23}),
  so \<open>k\<close> is not a row-0 left-minimum (@{thm [source] idxsum_no_parent0_iff}).
  Hence the only row-0-parentless node is \<open>0\<close>.\<close>

lemma m_6_6_monoT_hasParent0:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and e00: "entry M 0 0 = 0"
    and k: "0 < k" and kL: "k < Lng M"
  shows "hasParent M 0 k"
proof -
  have le0last: "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
  have allpos: "\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j"
    using m_6_2_multi_crit_23[OF MT] le0last by blast
  have posk: "0 < entry M 0 k" using allpos k kL e00 by auto
  \<comment> \<open>If \<open>k\<close> had no row-0 parent, then \<open>entry M 0 0 \<ge> entry M 0 k\<close> (left-minimum).\<close>
  have "\<not> (\<not> hasParent M 0 k)"
  proof
    assume "\<not> hasParent M 0 k"
    hence "\<not> (\<exists>!j0. nextR M 0 j0 k)" unfolding hasParent_def by simp
    hence lm: "\<forall>j<k. entry M 0 j \<ge> entry M 0 k"
      using idxsum_no_parent0_iff[OF MT kL] by simp
    have "entry M 0 0 \<ge> entry M 0 k" using lm k by blast
    thus False using posk e00 by simp
  qed
  thus ?thesis by simp
qed

text \<open>命題（簡約性と係数の関係）, backward base value support (content.md 1232):
  a \<open>monoT\<close> sequence with \<open>M\<^bsub>0,0\<^esub> = M\<^bsub>1,0\<^esub>\<close> satisfies condition (B).  The only
  row-0-parentless node is \<open>0\<close> (@{thm [source] m_6_6_monoT_hasParent0}), and there
  \<open>M\<^bsub>0,0\<^esub> = M\<^bsub>1,0\<^esub>\<close> by hypothesis.  Fully structural — no \<open>Red\<close> unfold (A4-free).\<close>

lemma m_6_6_monoT_RedCondB:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and eq0: "entry M 0 0 = entry M 1 0"
  shows "RedCondB M"
  unfolding RedCondB_def
proof (intro allI impI)
  fix j1' :: nat
  assume H: "\<not> hasParent M 0 j1' \<and> j1' \<le> Lng M - 1"
  hence nhp: "\<not> hasParent M 0 j1'" and jle: "j1' \<le> Lng M - 1" by simp_all
  have LM: "1 \<le> Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have jL: "j1' < Lng M" using jle LM by simp
  show "entry M 0 j1' = entry M 1 j1'"
  proof (cases "j1' = 0")
    case True
    show ?thesis using True e00 eq0 by simp
  next
    case False
    hence "0 < j1'" by simp
    hence "hasParent M 0 j1'" by (rule m_6_6_monoT_hasParent0[OF MT mono e00 _ jL])
    thus ?thesis using nhp by contradiction
  qed
qed

end

theory Frontier_6_049
  imports Support_6_030
begin

(* ===== keystone concat-transfer block from workflow kc-rcpb ===== *)

(* ===== block inheritance of RedCondA/RedCondB (worktree kc-rcpb) ===== *)

text \<open>rcpb: structural data for a \<open>P\<close>-block.  For \<open>M \<in> T_PS\<close> and
  \<open>J < length (P M)\<close>, setting \<open>a = IdxSum (P M) ! J\<close> and \<open>L = Lng (P M ! J)\<close>,
  the block is the \<open>M\<close>-slice \<open>seg M a (a + L - 1)\<close>, has positive length, and
  lies entirely inside \<open>M\<close> (so \<open>a + L - 1 < Lng M\<close>).\<close>

lemma rcpb_block_eq:
  assumes M: "M \<in> T_PS" and JL: "J < length (P M)"
  shows "P M ! J = seg M (IdxSum (P M) ! J) (IdxSum (P M) ! J + Lng (P M ! J) - 1)
       \<and> 0 < Lng (P M ! J)
       \<and> IdxSum (P M) ! J + Lng (P M ! J) - 1 < Lng M"
proof -
  let ?a = "IdxSum (P M) ! J"
  let ?b = "IdxSum (P M) ! (J + 1) - 1"
  let ?L = "Lng (P M ! J)"
  have ne: "P M \<noteq> []" by (rule P_nonempty)
  have J1: "J \<le> Lng (P M) - 1" using JL ne by (cases "P M") auto
  have seq: "P M ! J = seg M ?a ?b" by (rule m_6_4_P_IdxSum[OF M J1])
  have Lpos: "0 < ?L" by (rule idxsum_P_component_nonempty[OF M JL])
  have Leq: "?L = Suc ?b - ?a" using seq by simp
  have diff: "IdxSum (P M) ! (J + 1) = ?a + length (P M ! J)"
    by (rule idxsum_diff[OF JL])
  have sucb: "Suc ?b = ?a + ?L" using diff Lpos by simp
  hence bval: "?b = ?a + ?L - 1" by simp
  \<comment> \<open>range bound \<open>?a + ?L \<le> Lng M\<close>\<close>
  have aval: "?a = sum_list (map length (take J (P M)))"
    using JL by (simp add: idxsum_nth)
  have lenM: "length M = sum_list (map length (P M))"
    using idxsum_concat_P[of M] by (metis length_concat)
  have rangeb: "?a + ?L \<le> Lng M"
  proof -
    have "?a + ?L = sum_list (map length (take (Suc J) (P M)))"
      using aval JL by (simp add: take_Suc_conv_app_nth)
    also have "\<dots> \<le> sum_list (map length (take (length (P M)) (P M)))"
      using JL by (intro idxsum_sum_take_mono) simp
    also have "\<dots> = sum_list (map length (P M))" by simp
    finally show ?thesis using lenM by simp
  qed
  have blt: "?a + ?L - 1 < Lng M" using rangeb Lpos by linarith
  show ?thesis using seq[unfolded bval] Lpos blt by simp
qed

text \<open>rcpb: row-\<open>i\<close> \<open>nextR\<close> on a slice corresponds to that on \<open>M\<close> shifted by the
  slice offset (uniform in \<open>i \<le> 1\<close>), packaging
  @{thm [source] adm_nextrel0_seg}/@{thm [source] adm_nextrel1_seg}.\<close>

lemma rcpb_nextR_seg:
  assumes b: "b < Lng M" and i: "i \<le> 1"
    and p: "p < Lng (seg M a b)" and q: "q < Lng (seg M a b)"
  shows "nextR (seg M a b) i p q \<longleftrightarrow> nextR M i (a + p) (a + q)"
proof (cases "i = 0")
  case True
  thus ?thesis using adm_nextrel0_seg[OF b p q] by (simp add: nextR_def)
next
  case False
  hence "i = 1" using i by simp
  thus ?thesis using adm_nextrel1_seg[OF b p q] by (simp add: nextR_def)
qed

text \<open>rcpb: the parent-set bijection.  Inside a \<open>P\<close>-block, the row-\<open>i\<close> parents in
  \<open>M\<close> of a node at local column \<open>jl\<close> are exactly the (offset-shifted) row-\<open>i\<close>
  parents in the block.  Block-locality (@{thm [source] m_6_4_parent_in_block})
  bounds every \<open>M\<close>-parent below by the block start \<open>a\<close>; the child relation
  \<open>nextR\<close> bounds it above by the child column; the slice bridge
  (@{thm [source] rcpb_nextR_seg}) then identifies the in-block parents.\<close>

lemma rcpb_parent_iff:
  assumes M: "M \<in> T_PS" and JL: "J < length (P M)" and i: "i \<le> 1"
    and jl: "jl < Lng (P M ! J)"
  defines "a \<equiv> IdxSum (P M) ! J"
  shows "nextR (P M ! J) i pl jl \<longleftrightarrow> (pl < Lng (P M ! J) \<and> nextR M i (a + pl) (a + jl))"
proof -
  let ?B = "P M ! J"
  let ?L = "Lng ?B"
  let ?b = "a + ?L - 1"
  have be: "?B = seg M a ?b" and Lpos: "0 < ?L" and blt: "?b < Lng M"
    using rcpb_block_eq[OF M JL] unfolding a_def by auto
  have segL: "Lng (seg M a ?b) = ?L" using be by simp
  have jlseg: "jl < Lng (seg M a ?b)" using jl segL by simp
  show ?thesis
  proof
    assume H: "nextR ?B i pl jl"
    \<comment> \<open>parent column \<open>pl\<close> is in the block (\<open>< L\<close>) because \<open>nextR\<close> needs \<open>pl < jl\<close>.\<close>
    have plj: "pl < jl"
      using H by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
    hence plL: "pl < ?L" using jl by simp
    have plseg: "pl < Lng (seg M a ?b)" using plL segL by simp
    have "nextR (seg M a ?b) i pl jl" using H be by simp
    hence "nextR M i (a + pl) (a + jl)"
      using rcpb_nextR_seg[OF blt i plseg jlseg] by simp
    thus "pl < ?L \<and> nextR M i (a + pl) (a + jl)" using plL by simp
  next
    assume H: "pl < ?L \<and> nextR M i (a + pl) (a + jl)"
    hence plL: "pl < ?L" and HM: "nextR M i (a + pl) (a + jl)" by simp_all
    have plseg: "pl < Lng (seg M a ?b)" using plL segL by simp
    have "nextR (seg M a ?b) i pl jl"
      using rcpb_nextR_seg[OF blt i plseg jlseg] HM by simp
    thus "nextR ?B i pl jl" using be by simp
  qed
qed

text \<open>rcpb: \<open>hasParent\<close> agrees between the block and \<open>M\<close>.  Every \<open>M\<close>-parent of an
  in-block node lies in the same block (@{thm [source] m_6_4_parent_in_block}
  gives \<open>\<ge> a\<close>; \<open>nextR\<close> gives \<open>< a + jl < a + L\<close>), so the offset map \<open>pl \<mapsto> a+pl\<close>
  is a bijection between block-parents and \<open>M\<close>-parents.  Existence/uniqueness and
  the parent value therefore transfer.\<close>

lemma rcpb_hasParent_iff:
  assumes M: "M \<in> T_PS" and JL: "J < length (P M)" and i: "i \<le> 1"
    and jl: "jl < Lng (P M ! J)"
  defines "a \<equiv> IdxSum (P M) ! J"
  shows "hasParent (P M ! J) i jl \<longleftrightarrow> hasParent M i (a + jl)"
    and "hasParent (P M ! J) i jl \<Longrightarrow> a + parent (P M ! J) i jl = parent M i (a + jl)"
proof -
  let ?B = "P M ! J"
  let ?L = "Lng ?B"
  \<comment> \<open>The parent equivalence as a single named fact (offset \<open>a\<close> folded in).\<close>
  have piff: "\<And>pl. nextR ?B i pl jl \<longleftrightarrow> (pl < ?L \<and> nextR M i (a + pl) (a + jl))"
    using rcpb_parent_iff[OF M JL i jl] unfolding a_def by simp
  \<comment> \<open>Block parents and \<open>M\<close>-parents of \<open>a + jl\<close> correspond via \<open>pl \<mapsto> a + pl\<close>.\<close>
  have block_to_M: "\<And>pl. nextR ?B i pl jl \<Longrightarrow> nextR M i (a + pl) (a + jl)"
  proof -
    fix pl assume "nextR ?B i pl jl"
    thus "nextR M i (a + pl) (a + jl)" using piff[of pl] by simp
  qed
  have M_in_block: "\<And>p. nextR M i p (a + jl) \<Longrightarrow> (\<exists>pl. p = a + pl \<and> nextR ?B i pl jl)"
  proof -
    fix p assume Hp: "nextR M i p (a + jl)"
    \<comment> \<open>lower bound from block-locality\<close>
    have age: "a \<le> p"
      using m_6_4_parent_in_block[OF M JL i _ Hp] unfolding a_def by simp
    then obtain pl where pl: "p = a + pl" by (metis le_add_diff_inverse)
    \<comment> \<open>parent column is below the child, hence inside the block.\<close>
    have "p < a + jl" using Hp
      by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
    hence plL: "pl < ?L" using pl jl by simp
    have "nextR ?B i pl jl" using piff[of pl] plL Hp pl by simp
    thus "\<exists>pl. p = a + pl \<and> nextR ?B i pl jl" using pl by blast
  qed
  \<comment> \<open>existence both ways\<close>
  have ex_iff: "(\<exists>pl. nextR ?B i pl jl) \<longleftrightarrow> (\<exists>p. nextR M i p (a + jl))"
    using block_to_M M_in_block by metis
  \<comment> \<open>uniqueness transfers because the offset map is injective\<close>
  have uniq_iff: "(\<exists>!pl. nextR ?B i pl jl) \<longleftrightarrow> (\<exists>!p. nextR M i p (a + jl))"
  proof
    assume "\<exists>!pl. nextR ?B i pl jl"
    then obtain pl0 where pl0: "nextR ?B i pl0 jl"
      and uB: "\<And>pl'. nextR ?B i pl' jl \<Longrightarrow> pl' = pl0" by blast
    have m0: "nextR M i (a + pl0) (a + jl)" using block_to_M pl0 by blast
    have "\<And>p'. nextR M i p' (a + jl) \<Longrightarrow> p' = a + pl0"
    proof -
      fix p' assume "nextR M i p' (a + jl)"
      then obtain pl' where pl': "p' = a + pl'" "nextR ?B i pl' jl"
        using M_in_block by blast
      have "pl' = pl0" using uB pl'(2) by blast
      thus "p' = a + pl0" using pl'(1) by simp
    qed
    with m0 show "\<exists>!p. nextR M i p (a + jl)" by blast
  next
    assume "\<exists>!p. nextR M i p (a + jl)"
    then obtain p0 where p0: "nextR M i p0 (a + jl)"
      and uM: "\<And>p'. nextR M i p' (a + jl) \<Longrightarrow> p' = p0" by blast
    obtain pl0 where pl0eq: "p0 = a + pl0" and bpl0: "nextR ?B i pl0 jl"
      using M_in_block p0 by blast
    have "\<And>pl'. nextR ?B i pl' jl \<Longrightarrow> pl' = pl0"
    proof -
      fix pl' assume "nextR ?B i pl' jl"
      hence "nextR M i (a + pl') (a + jl)" using block_to_M by blast
      hence "a + pl' = p0" using uM by blast
      thus "pl' = pl0" using pl0eq by simp
    qed
    with bpl0 show "\<exists>!pl. nextR ?B i pl jl" by blast
  qed
  show hpi: "hasParent ?B i jl \<longleftrightarrow> hasParent M i (a + jl)"
    using uniq_iff by (simp add: hasParent_def)
  \<comment> \<open>parent value\<close>
  show "hasParent ?B i jl \<Longrightarrow> a + parent ?B i jl = parent M i (a + jl)"
  proof -
    assume hp: "hasParent ?B i jl"
    hence ex1B: "\<exists>!pl. nextR ?B i pl jl" by (simp add: hasParent_def)
    then obtain pl0 where pl0: "nextR ?B i pl0 jl"
      and uB: "\<And>pl'. nextR ?B i pl' jl \<Longrightarrow> pl' = pl0" by blast
    have pB: "parent ?B i jl = pl0"
      unfolding parent_def
      by (rule the_equality[where P="\<lambda>pl. nextR ?B i pl jl", OF pl0 uB])
    have m0: "nextR M i (a + pl0) (a + jl)" using block_to_M pl0 by blast
    have uM: "\<And>p'. nextR M i p' (a + jl) \<Longrightarrow> p' = a + pl0"
    proof -
      fix p' assume "nextR M i p' (a + jl)"
      then obtain pl' where pl': "p' = a + pl'" "nextR ?B i pl' jl"
        using M_in_block by blast
      thus "p' = a + pl0" using uB by simp
    qed
    have pM: "parent M i (a + jl) = a + pl0"
      unfolding parent_def
      by (rule the_equality[where P="\<lambda>p. nextR M i p (a + jl)", OF m0 uM])
    show "a + parent ?B i jl = parent M i (a + jl)" using pB pM by simp
  qed
qed

end

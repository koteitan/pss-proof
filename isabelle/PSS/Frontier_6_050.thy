theory Frontier_6_050
  imports Support_6_031
begin

(* ===== keystone concat-transfer block from workflow kc-clift ===== *)

(* ===== C2 (concat-lifting): forward transfer of RedCondA/RedCondB ===== *)

text \<open>\<open>clift_block_bounds\<close>: structural facts about the \<open>J\<close>-th \<open>P\<close>-block of
  \<open>M\<close>.  Writing \<open>a = IdxSum (P M) ! J\<close> and \<open>b = IdxSum (P M) ! (J+1) - 1\<close>, the
  block equals \<open>seg M a b\<close>, is non-empty with \<open>Lng (seg M a b) = Suc b - a\<close>,
  and \<open>Suc b = a + Lng (P M ! J) \<le> Lng M\<close>, so \<open>b < Lng M\<close>.\<close>

lemma clift_block_bounds:
  assumes M: "M \<in> T_PS" and JL: "J < length (P M)"
  shows "P M ! J = seg M (IdxSum (P M) ! J) (IdxSum (P M) ! (J + 1) - 1)
       \<and> 0 < Lng (P M ! J)
       \<and> Suc (IdxSum (P M) ! (J + 1) - 1) = IdxSum (P M) ! J + Lng (P M ! J)
       \<and> IdxSum (P M) ! J + Lng (P M ! J) \<le> Lng M
       \<and> IdxSum (P M) ! (J + 1) - 1 < Lng M"
proof -
  let ?Q = "P M"
  let ?a = "IdxSum ?Q ! J"
  let ?b = "IdxSum ?Q ! (J + 1) - 1"
  have Jle: "J \<le> Lng ?Q - 1" using JL by simp
  have seg: "?Q ! J = seg M ?a ?b" by (rule m_6_4_P_IdxSum[OF M Jle])
  have lenpos: "0 < Lng (?Q ! J)" by (rule idxsum_P_component_nonempty[OF M JL])
  have diff: "IdxSum ?Q ! (J + 1) = ?a + length (?Q ! J)" using JL by (rule idxsum_diff)
  have sucb: "Suc ?b = ?a + Lng (?Q ! J)" using diff lenpos by simp
  \<comment> \<open>\<open>?a + Lng block \<le> Lng M\<close> via the cumulative-length bound.\<close>
  have concatM: "concat ?Q = M" by (rule idxsum_concat_P)
  have lenM: "Lng M = sum_list (map length ?Q)"
    using concatM by (metis length_concat)
  have aval: "?a = sum_list (map length (take J ?Q))" using JL by (simp add: idxsum_nth)
  have rangeb: "?a + Lng (?Q ! J) \<le> Lng M"
  proof -
    have "?a + length (?Q ! J) = sum_list (map length (take (Suc J) ?Q))"
      using aval JL by (simp add: take_Suc_conv_app_nth)
    also have "\<dots> \<le> sum_list (map length (take (length ?Q) ?Q))"
      using JL by (intro idxsum_sum_take_mono) simp
    also have "\<dots> = sum_list (map length ?Q)" by simp
    finally show ?thesis using lenM by simp
  qed
  have bL: "?b < Lng M" using sucb rangeb lenpos by linarith
  show ?thesis using seg lenpos sucb rangeb bL by blast
qed

text \<open>\<open>clift_nextR_lift\<close>: the per-block \<open>nextR\<close> relation transfers up to \<open>M\<close>.
  If \<open>x\<close>, \<open>y\<close> are interior to the \<open>J\<close>-th block (\<open>< Lng (block)\<close>) then
  \<open>nextR block i x y \<longleftrightarrow> nextR M i (a + x) (a + y)\<close>, where \<open>a = IdxSum (P M) ! J\<close>.
  Both rows reduce to the slice correspondences @{thm [source] adm_nextrel0_seg}
  / @{thm [source] adm_nextR1_seg}.\<close>

lemma clift_nextR_lift:
  assumes M: "M \<in> T_PS" and JL: "J < length (P M)" and i: "i \<le> 1"
    and x: "x < Lng (P M ! J)" and y: "y < Lng (P M ! J)"
  shows "nextR (P M ! J) i x y \<longleftrightarrow> nextR M i (IdxSum (P M) ! J + x) (IdxSum (P M) ! J + y)"
proof -
  let ?a = "IdxSum (P M) ! J"
  let ?b = "IdxSum (P M) ! (J + 1) - 1"
  note B = clift_block_bounds[OF M JL]
  hence seg: "P M ! J = seg M ?a ?b" and bL: "?b < Lng M" by blast+
  have xseg: "x < Lng (seg M ?a ?b)" using x seg by simp
  have yseg: "y < Lng (seg M ?a ?b)" using y seg by simp
  show ?thesis
  proof (cases "i = 0")
    case True
    have "nextR (P M ! J) 0 x y \<longleftrightarrow> nextrel0 (seg M ?a ?b) x y"
      using seg by (simp add: nextR_def)
    also have "\<dots> \<longleftrightarrow> nextrel0 M (?a + x) (?a + y)"
      by (rule adm_nextrel0_seg[OF bL xseg yseg])
    also have "\<dots> \<longleftrightarrow> nextR M 0 (?a + x) (?a + y)" by (simp add: nextR_def)
    finally show ?thesis using True by simp
  next
    case False
    hence i1: "i = 1" using i by simp
    have "nextR (P M ! J) 1 x y \<longleftrightarrow> nextR (seg M ?a ?b) 1 x y" using seg by simp
    also have "\<dots> \<longleftrightarrow> nextR M 1 (?a + x) (?a + y)"
      by (rule adm_nextR1_seg[OF bL xseg yseg])
    finally show ?thesis using i1 by simp
  qed
qed

text \<open>\<open>clift_hasParent_lift\<close>: for a node interior to block \<open>J\<close> (with the global
  parent already known to land \<open>\<ge> a\<close> by @{thm [source] m_6_4_parent_in_block}),
  having a unique local parent is equivalent to having one in \<open>M\<close>, and the
  parents correspond by the shift \<open>a\<close>.\<close>

lemma clift_local_imp_global_parent:
  assumes M: "M \<in> T_PS" and JL: "J < length (P M)" and i: "i \<le> 1"
    and y: "y < Lng (P M ! J)"
    and lp: "nextR (P M ! J) i q y"
  shows "nextR M i (IdxSum (P M) ! J + q) (IdxSum (P M) ! J + y)"
proof -
  have qy: "q < y" using lp by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
  have q: "q < Lng (P M ! J)" using qy y by simp
  show ?thesis using clift_nextR_lift[OF M JL i q y] lp by simp
qed

text \<open>Conversely a global parent of an interior node lands inside the block and
  descends to a local parent.\<close>

lemma clift_global_imp_local_parent:
  assumes M: "M \<in> T_PS" and JL: "J < length (P M)" and i: "i \<le> 1"
    and y: "y < Lng (P M ! J)"
    and gp: "nextR M i p (IdxSum (P M) ! J + y)"
  shows "p \<ge> IdxSum (P M) ! J \<and> nextR (P M ! J) i (p - IdxSum (P M) ! J) y"
proof -
  let ?a = "IdxSum (P M) ! J"
  \<comment> \<open>parent stays in the block.\<close>
  have alo: "?a \<le> ?a + y" by simp
  have pge: "?a \<le> p" by (rule m_6_4_parent_in_block[OF M JL i alo gp])
  \<comment> \<open>and \<open>p < ?a + y\<close> from the strict-order part of \<open>nextR\<close>.\<close>
  have plt: "p < ?a + y"
    using gp by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
  have py: "p - ?a < y" using pge plt by linarith
  have pblk: "p - ?a < Lng (P M ! J)" using py y by simp
  have shift: "?a + (p - ?a) = p" using pge by simp
  have "nextR (P M ! J) i (p - ?a) y \<longleftrightarrow> nextR M i (?a + (p - ?a)) (?a + y)"
    by (rule clift_nextR_lift[OF M JL i pblk y])
  hence "nextR (P M ! J) i (p - ?a) y \<longleftrightarrow> nextR M i p (?a + y)" using shift by simp
  thus ?thesis using gp pge by simp
qed

end

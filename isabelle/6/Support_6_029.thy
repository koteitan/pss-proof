theory Support_6_029
  imports Frontier_6_047
begin

text \<open>
  L1 — parent block-locality (§6.4 structural foundation).  Within the
  \<open>P M\<close>-block decomposition, a node's parent never crosses a block boundary
  backward: for \<open>M \<in> T_PS\<close>, \<open>J < length (P M)\<close>, and a row-\<open>i\<close> node at global
  column \<open>j\<close> lying in block \<open>J\<close> (i.e. \<open>IdxSum (P M) ! J \<le> j\<close>), if
  \<open>nextR M i p j\<close> then \<open>p \<ge> IdxSum (P M) ! J\<close>, i.e. the parent lies in the
  same block.  The block left-end \<open>IdxSum (P M) ! J\<close> is a row-0 left-minimum
  (@{thm [source] idxsum_leftend_lmin}); both row-0 and row-1 parent edges
  imply an \<open>le0\<close> ancestry (\<open>nextrel0\<close> directly, \<open>nextrel1\<close> via its \<open>le0\<close>
  conjunct), so @{thm [source] le0_leftmin_ancestor_ge} applies uniformly.
  Empirically TRUE: 102000/102000 in-block parent edges (\<open>maxlen 4, maxe 3\<close>).
\<close>

lemma m_6_4_parent_in_block:
  assumes M: "M \<in> T_PS" and JL: "J < length (P M)"
    and i: "i \<le> 1"
    and jlo: "IdxSum (P M) ! J \<le> j"
    and par: "nextR M i p j"
  shows "IdxSum (P M) ! J \<le> p"
proof -
  let ?a = "IdxSum (P M) ! J"
  \<comment> \<open>The block left-end is a row-0 left-minimum.\<close>
  have lmin: "\<forall>z < ?a. entry M 0 z \<ge> entry M 0 ?a"
    using idxsum_leftend_lmin[OF M JL] by blast
  \<comment> \<open>Both row-0 and row-1 parent edges give an \<open>le0\<close> chain \<open>p \<to> j\<close>.\<close>
  have chain: "(nextrel0 M)\<^sup>*\<^sup>* p j"
  proof (cases "i = 0")
    case True
    hence "nextrel0 M p j" using par by (simp add: nextR_def)
    thus ?thesis by blast
  next
    case False
    hence "i = 1" using i by simp
    hence "nextrel1 M p j" using par by (simp add: nextR_def)
    hence "le0 M p j" by (simp add: nextrel1_def)
    thus ?thesis by (simp add: le0_def)
  qed
  show "?a \<le> p"
    by (rule le0_leftmin_ancestor_ge[OF lmin chain jlo])
qed

end

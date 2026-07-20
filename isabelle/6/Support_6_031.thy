theory Support_6_031
  imports Frontier_6_049
begin

text \<open>rcpb (§6.6, C1): blockwise inheritance of the reducedness conditions.
  Each \<open>P\<close>-block of \<open>M\<close> inherits \<open>RedCondA\<close> and \<open>RedCondB\<close> from \<open>M\<close>.

  Route: a block is the slice \<open>seg M a (a+L-1)\<close> (@{thm [source] rcpb_block_eq});
  parent edges transfer edge-by-edge through the offset bijection
  (@{thm [source] rcpb_hasParent_iff}, built on block-locality
  @{thm [source] m_6_4_parent_in_block} and the slice \<open>nextR\<close> bridge).  For
  \<open>RedCondA\<close>: \<open>hasParent (block) i jl\<close> gives \<open>hasParent M i (a+jl)\<close> with the same
  \<open>+1\<close> entry relation (entries shift by \<open>a\<close> via @{thm [source] entry_seg}).  For
  \<open>RedCondB\<close>: a block node with no row-0 parent in the block has no row-0 parent
  in \<open>M\<close> either (the offset bijection again — block-locality already excludes any
  cross-block parent, so the block left end is also a global left-minimum), so
  \<open>RedCondB M\<close> applies at \<open>a+jl\<close>.\<close>

lemma m_6_6_RedCond_P_block:
  assumes M: "M \<in> T_PS" and multi: "multiT M"
    and condA: "RedCondA M" and condB: "RedCondB M"
    and JL: "J < length (P M)"
  shows "RedCondA (P M ! J) \<and> RedCondB (P M ! J)"
proof -
  let ?B = "P M ! J"
  let ?a = "IdxSum (P M) ! J"
  let ?L = "Lng ?B"
  have be: "?B = seg M ?a (?a + ?L - 1)" and Lpos: "0 < ?L"
    and blt: "?a + ?L - 1 < Lng M"
    using rcpb_block_eq[OF M JL] by auto
  \<comment> \<open>entries of the block are \<open>M\<close>-entries shifted by \<open>?a\<close>.\<close>
  have eB: "\<And>i j. j < ?L \<Longrightarrow> entry ?B i j = entry M i (?a + j)"
  proof -
    fix i j assume jL: "j < ?L"
    have jseg: "j < Lng (seg M ?a (?a + ?L - 1))" using jL be by simp
    have "entry (seg M ?a (?a + ?L - 1)) i j = entry M i (?a + j)"
      by (rule entry_seg[OF jseg])
    thus "entry ?B i j = entry M i (?a + j)" using be by simp
  qed
  \<comment> \<open>any in-block column maps to an \<open>M\<close>-column \<open>\<le> Lng M - 1\<close>.\<close>
  have ajle: "\<And>jl. jl < ?L \<Longrightarrow> ?a + jl \<le> Lng M - 1"
    using blt by simp
  have condAB: "RedCondA ?B \<and> RedCondB ?B"
  proof (intro conjI)
    \<comment> \<open>RedCondA on the block.\<close>
    show "RedCondA ?B"
      unfolding RedCondA_def
    proof (intro allI impI)
      fix i jl assume i: "i \<le> 1" and hp: "hasParent ?B i jl"
      show "entry ?B i (parent ?B i jl) + 1 = entry ?B i jl"
      proof (cases "jl < ?L")
        case True
        have hpM: "hasParent M i (?a + jl)"
          using rcpb_hasParent_iff(1)[OF M JL i True] hp by simp
        have pval: "?a + parent ?B i jl = parent M i (?a + jl)"
          using rcpb_hasParent_iff(2)[OF M JL i True] hp by simp
        \<comment> \<open>parent column is also in the block (it is \<open>< jl\<close>).\<close>
        have ex1: "\<exists>!pl. nextR ?B i pl jl" using hp by (simp add: hasParent_def)
        then obtain pl0 where pl0: "nextR ?B i pl0 jl"
          and uB: "\<And>pl'. nextR ?B i pl' jl \<Longrightarrow> pl' = pl0" by blast
        have plj: "pl0 < jl"
          using pl0 by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
        have pB: "parent ?B i jl = pl0"
          unfolding parent_def
          by (rule the_equality[where P="\<lambda>pl. nextR ?B i pl jl", OF pl0 uB])
        have plL: "parent ?B i jl < ?L" using pB plj True by simp
        \<comment> \<open>apply \<open>RedCondA M\<close> at the shifted child.\<close>
        have "entry M i (parent M i (?a + jl)) + 1 = entry M i (?a + jl)"
          using condA hpM i unfolding RedCondA_def by blast
        hence "entry M i (?a + parent ?B i jl) + 1 = entry M i (?a + jl)"
          using pval by simp
        thus ?thesis using eB[OF plL] eB[OF True] by simp
      next
        case False
        \<comment> \<open>out-of-range \<open>jl\<close>: no parent, contradiction with \<open>hasParent\<close>.\<close>
        have "\<not> nextR ?B i pl jl" for pl
        proof
          assume "nextR ?B i pl jl"
          hence "jl < ?L" by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
          thus False using False by simp
        qed
        hence "\<not> hasParent ?B i jl" by (auto simp: hasParent_def)
        thus ?thesis using hp by simp
      qed
    qed
  next
    \<comment> \<open>RedCondB on the block.\<close>
    show "RedCondB ?B"
      unfolding RedCondB_def
    proof (intro allI impI)
      fix jl assume hyp: "\<not> hasParent ?B 0 jl \<and> jl \<le> Lng ?B - 1"
      have nhp: "\<not> hasParent ?B 0 jl" and jlb: "jl \<le> ?L - 1" using hyp by simp_all
      have jlL: "jl < ?L" using jlb Lpos by linarith
      have i0: "(0::nat) \<le> 1" by simp
      \<comment> \<open>no row-0 parent in the block \<Longrightarrow> none in \<open>M\<close> either.\<close>
      have nhpM: "\<not> hasParent M 0 (?a + jl)"
        using rcpb_hasParent_iff(1)[OF M JL i0 jlL] nhp by simp
      have ajle': "?a + jl \<le> Lng M - 1" using ajle[OF jlL] by simp
      \<comment> \<open>apply \<open>RedCondB M\<close> at the shifted node.\<close>
      have "entry M 0 (?a + jl) = entry M 1 (?a + jl)"
        using condB nhpM ajle' unfolding RedCondB_def by blast
      thus "entry ?B 0 jl = entry ?B 1 jl" using eB[OF jlL] by simp
    qed
  qed
  thus ?thesis by simp
qed

end

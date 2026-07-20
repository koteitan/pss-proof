theory Support_6_032
  imports Frontier_6_050
begin

text \<open>m (§6.6 C2, concat-lifting): if every \<open>P\<close>-block of \<open>M\<close> satisfies
  \<open>RedCondA\<close> and \<open>RedCondB\<close> then so does \<open>M = concat (P M)\<close>.  Forward transfer,
  inverse of the inheritance: every node of \<open>M\<close> lies in a unique block; by
  @{thm [source] m_6_4_parent_in_block} its parent stays in that block, so the
  per-block edge relation lifts to \<open>M\<close> edge-by-edge
  (@{thm [source] clift_nextR_lift}), and entries agree by the slice offset
  (@{thm [source] entry_seg}).  For \<open>RedCondB\<close>: a row-0 parentless node of \<open>M\<close> is
  also row-0 parentless inside its block, so the block's \<open>RedCondB\<close> applies.\<close>

lemma m_6_6_RedCond_concat_lift:
  assumes M: "M \<in> T_PS" and multi: "multiT M"
    and blocks: "\<forall>J < length (P M). RedCondA (P M ! J) \<and> RedCondB (P M ! J)"
  shows "RedCondA M \<and> RedCondB M"
proof
  show "RedCondA M"
    unfolding RedCondA_def
  proof (intro allI impI)
    fix i j1' assume i: "i \<le> 1" and hp: "hasParent M i j1'"
    \<comment> \<open>Let \<open>p\<close> be the (unique) parent of \<open>j1'\<close> in row \<open>i\<close>.\<close>
    have exu: "\<exists>!p. nextR M i p j1'" using hp by (simp add: hasParent_def)
    have par: "nextR M i (parent M i j1') j1'"
      unfolding parent_def using exu by (rule theI')
    let ?p = "parent M i j1'"
    \<comment> \<open>\<open>j1' < Lng M\<close> from the relation.\<close>
    have j1L: "j1' < Lng M"
      using par by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
    \<comment> \<open>Locate the block of \<open>j1'\<close>.\<close>
    let ?Q = "P M"
    have ne: "?Q \<noteq> []" by (rule P_nonempty)
    have total: "IdxSum ?Q ! (length ?Q) = Lng M"
    proof -
      have "IdxSum ?Q ! (length ?Q) = sum_list (map length (take (length ?Q) ?Q))"
        by (simp add: idxsum_nth)
      also have "\<dots> = sum_list (map length ?Q)" by simp
      also have "\<dots> = Lng M" using idxsum_concat_P[of M] by (metis length_concat)
      finally show ?thesis .
    qed
    have j1tot: "j1' < IdxSum ?Q ! (length ?Q)" using j1L total by simp
    obtain J where JL: "J < length ?Q"
      and Jlo: "IdxSum ?Q ! J \<le> j1'" and Jhi: "j1' < IdxSum ?Q ! (J + 1)"
      using idxsum_locate[OF j1tot] by blast
    let ?a = "IdxSum ?Q ! J"
    \<comment> \<open>Block structural facts.\<close>
    note B = clift_block_bounds[OF M JL]
    hence sucb: "Suc (IdxSum ?Q ! (J + 1) - 1) = ?a + Lng (?Q ! J)" by blast
    have idxeq: "IdxSum ?Q ! (J + 1) = ?a + Lng (?Q ! J)" using idxsum_diff[OF JL] by simp
    \<comment> \<open>\<open>j1'\<close> sits interior to block \<open>J\<close> (local index \<open>j1' - ?a\<close>).\<close>
    have yltLen: "j1' - ?a < Lng (?Q ! J)" using Jhi idxeq Jlo by linarith
    have shifty: "?a + (j1' - ?a) = j1'" using Jlo by simp
    \<comment> \<open>The global parent descends to a local parent at shift \<open>p - ?a\<close>.\<close>
    have gp: "nextR M i ?p (?a + (j1' - ?a))" using par shifty by simp
    obtain pge: "?a \<le> ?p"
      and lp: "nextR (?Q ! J) i (?p - ?a) (j1' - ?a)"
      using clift_global_imp_local_parent[OF M JL i yltLen gp] by blast
    \<comment> \<open>Local parent is unique, hence \<open>hasParent\<close> on the block, with parent \<open>?p - ?a\<close>.\<close>
    have qlt: "?p - ?a < j1' - ?a"
      using lp by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
    have qLen: "?p - ?a < Lng (?Q ! J)" using qlt yltLen by simp
    have luniq: "\<And>q. nextR (?Q ! J) i q (j1' - ?a) \<Longrightarrow> q = ?p - ?a"
    proof -
      fix q assume lq: "nextR (?Q ! J) i q (j1' - ?a)"
      have "nextR M i (?a + q) (?a + (j1' - ?a))"
        by (rule clift_local_imp_global_parent[OF M JL i yltLen lq])
      hence "nextR M i (?a + q) j1'" using shifty by simp
      hence "?a + q = ?p" using exu par by (metis (no_types) the1_equality hasParent_def)
      thus "q = ?p - ?a" by simp
    qed
    have lhp: "hasParent (?Q ! J) i (j1' - ?a)"
      unfolding hasParent_def using lp luniq by blast
    have lex1: "\<exists>!j0. nextR (?Q ! J) i j0 (j1' - ?a)" using lp luniq by blast
    have lpar: "parent (?Q ! J) i (j1' - ?a) = ?p - ?a"
    proof -
      have "parent (?Q ! J) i (j1' - ?a) = (THE j0. nextR (?Q ! J) i j0 (j1' - ?a))"
        by (simp add: parent_def)
      also have "\<dots> = ?p - ?a" by (rule the1_equality[OF lex1 lp])
      finally show ?thesis .
    qed
    \<comment> \<open>Apply the block's \<open>RedCondA\<close>.\<close>
    have condA: "RedCondA (?Q ! J)" using blocks JL by blast
    have local: "entry (?Q ! J) i (parent (?Q ! J) i (j1' - ?a)) + 1
               = entry (?Q ! J) i (j1' - ?a)"
      using condA i lhp unfolding RedCondA_def by blast
    have local2: "entry (?Q ! J) i (?p - ?a) + 1 = entry (?Q ! J) i (j1' - ?a)"
      using local lpar by simp
    \<comment> \<open>Lift entries through the slice (\<open>?Q ! J = seg M ?a ?b\<close>).\<close>
    have seg: "?Q ! J = seg M ?a (IdxSum ?Q ! (J + 1) - 1)" using B by blast
    have eP: "entry (?Q ! J) i (?p - ?a) = entry M i ?p"
    proof -
      have "entry (?Q ! J) i (?p - ?a) = entry (seg M ?a (IdxSum ?Q ! (J + 1) - 1)) i (?p - ?a)"
        using seg by simp
      also have "\<dots> = entry M i (?a + (?p - ?a))"
        by (rule entry_seg) (use qLen seg in simp)
      also have "\<dots> = entry M i ?p" using pge by simp
      finally show ?thesis .
    qed
    have eJ: "entry (?Q ! J) i (j1' - ?a) = entry M i j1'"
    proof -
      have "entry (?Q ! J) i (j1' - ?a) = entry (seg M ?a (IdxSum ?Q ! (J + 1) - 1)) i (j1' - ?a)"
        using seg by simp
      also have "\<dots> = entry M i (?a + (j1' - ?a))"
        by (rule entry_seg) (use yltLen seg in simp)
      also have "\<dots> = entry M i j1'" using shifty by simp
      finally show ?thesis .
    qed
    show "entry M i (parent M i j1') + 1 = entry M i j1'"
      using local2 eP eJ by simp
  qed
next
  show "RedCondB M"
    unfolding RedCondB_def
  proof (intro allI impI)
    fix j1' assume hyp: "\<not> hasParent M 0 j1' \<and> j1' \<le> Lng M - 1"
    have nhp: "\<not> hasParent M 0 j1'" and j1le: "j1' \<le> Lng M - 1" using hyp by blast+
    have L0: "Lng M \<ge> 1" using M by (cases M) (auto simp: T_PS_def)
    have j1L: "j1' < Lng M" using j1le L0 by linarith
    \<comment> \<open>Locate the block.\<close>
    let ?Q = "P M"
    have total: "IdxSum ?Q ! (length ?Q) = Lng M"
    proof -
      have "IdxSum ?Q ! (length ?Q) = sum_list (map length (take (length ?Q) ?Q))"
        by (simp add: idxsum_nth)
      also have "\<dots> = sum_list (map length ?Q)" by simp
      also have "\<dots> = Lng M" using idxsum_concat_P[of M] by (metis length_concat)
      finally show ?thesis .
    qed
    have j1tot: "j1' < IdxSum ?Q ! (length ?Q)" using j1L total by simp
    obtain J where JL: "J < length ?Q"
      and Jlo: "IdxSum ?Q ! J \<le> j1'" and Jhi: "j1' < IdxSum ?Q ! (J + 1)"
      using idxsum_locate[OF j1tot] by blast
    let ?a = "IdxSum ?Q ! J"
    note B = clift_block_bounds[OF M JL]
    hence sucb: "Suc (IdxSum ?Q ! (J + 1) - 1) = ?a + Lng (?Q ! J)" by blast
    have idxeq: "IdxSum ?Q ! (J + 1) = ?a + Lng (?Q ! J)" using idxsum_diff[OF JL] by simp
    have seg: "?Q ! J = seg M ?a (IdxSum ?Q ! (J + 1) - 1)" using B by blast
    have yltLen: "j1' - ?a < Lng (?Q ! J)" using Jhi idxeq Jlo by linarith
    have shifty: "?a + (j1' - ?a) = j1'" using Jlo by simp
    \<comment> \<open>\<open>j1'\<close> is row-0 parentless in its block too: a local row-0 parent would
        lift to a global one (row-0 parents are unique).\<close>
    have lnhp: "\<not> hasParent (?Q ! J) 0 (j1' - ?a)"
    proof
      assume "hasParent (?Q ! J) 0 (j1' - ?a)"
      then obtain q where lq: "nextR (?Q ! J) 0 q (j1' - ?a)"
        by (auto simp: hasParent_def)
      have "nextR M 0 (?a + q) (?a + (j1' - ?a))"
        by (rule clift_local_imp_global_parent[OF M JL _ yltLen lq]) simp
      hence "nextR M 0 (?a + q) j1'" using shifty by simp
      hence "\<exists>j0. nextR M 0 j0 j1'" by blast
      hence "\<exists>!j0. nextR M 0 j0 j1'" by (simp add: idxsum_ex1_parent0_iff)
      thus False using nhp by (simp add: hasParent_def)
    qed
    \<comment> \<open>Apply the block's \<open>RedCondB\<close>.  Local index \<open>\<le> Lng block - 1\<close>.\<close>
    have yle: "j1' - ?a \<le> Lng (?Q ! J) - 1" using yltLen by linarith
    have condB: "RedCondB (?Q ! J)" using blocks JL by blast
    have local: "entry (?Q ! J) 0 (j1' - ?a) = entry (?Q ! J) 1 (j1' - ?a)"
      using condB lnhp yle unfolding RedCondB_def by blast
    \<comment> \<open>Lift both entries through the slice.\<close>
    have e0: "entry (?Q ! J) 0 (j1' - ?a) = entry M 0 j1'"
    proof -
      have "entry (?Q ! J) 0 (j1' - ?a) = entry (seg M ?a (IdxSum ?Q ! (J + 1) - 1)) 0 (j1' - ?a)"
        using seg by simp
      also have "\<dots> = entry M 0 (?a + (j1' - ?a))"
        by (rule entry_seg) (use yltLen seg in simp)
      also have "\<dots> = entry M 0 j1'" using shifty by simp
      finally show ?thesis .
    qed
    have e1: "entry (?Q ! J) 1 (j1' - ?a) = entry M 1 j1'"
    proof -
      have "entry (?Q ! J) 1 (j1' - ?a) = entry (seg M ?a (IdxSum ?Q ! (J + 1) - 1)) 1 (j1' - ?a)"
        using seg by simp
      also have "\<dots> = entry M 1 (?a + (j1' - ?a))"
        by (rule entry_seg) (use yltLen seg in simp)
      also have "\<dots> = entry M 1 j1'" using shifty by simp
      finally show ?thesis .
    qed
    show "entry M 0 j1' = entry M 1 j1'" using local e0 e1 by simp
  qed
qed

end

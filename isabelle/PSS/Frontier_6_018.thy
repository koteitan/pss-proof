theory Frontier_6_018
  imports P_6_4_mono_slice
begin

text \<open>
  Inline helper: row-1 parents are unique (analogous to @{thm idxsum_parent0_unique} for row 0).
\<close>

lemma nextR1_unique:
  assumes "nextR M 1 a j" "nextR M 1 b j"
  shows "a = b"
proof (rule ccontr)
  assume ne: "a \<noteq> b"
  from assms(1) have na: "nextrel1 M a j" by (simp add: nextR_def)
  from assms(2) have nb: "nextrel1 M b j" by (simp add: nextR_def)
  from na have le0aj: "le0 M a j" by (simp add: nextrel1_def)
  from nb have le0bj: "le0 M b j" by (simp add: nextrel1_def)
  from na have ea: "entry M 1 a < entry M 1 j" by (simp add: nextrel1_def)
  from nb have eb: "entry M 1 b < entry M 1 j" by (simp add: nextrel1_def)
  from na have ca: "\<forall>x. a < x \<and> le0 M x j \<longrightarrow> entry M 1 x \<ge> entry M 1 j"
    by (simp add: nextrel1_def)
  from nb have cb: "\<forall>x. b < x \<and> le0 M x j \<longrightarrow> entry M 1 x \<ge> entry M 1 j"
    by (simp add: nextrel1_def)
  from ne consider "a < b" | "b < a" by linarith
  thus False
  proof cases
    case 1
    have "entry M 1 b \<ge> entry M 1 j" using ca 1 le0bj by blast
    with eb show False by simp
  next
    case 2
    have "entry M 1 a \<ge> entry M 1 j" using cb 2 le0aj by blast
    with ea show False by simp
  qed
qed

text \<open>
  Helper: if row-1 has no parent at position j, entry M 1 j = 0 (under condB).
  Proof: by contradiction. If entry M 1 j > 0, find the P-component K containing j.
  Its left-end ?a satisfies: entry M 0 ?a = 0 (from e00 and almin), so ¬ hasParent M 0 ?a,
  hence entry M 1 ?a = 0 by RedCondB. The component is monoT (length > 1 since j > ?a),
  so le0 M ?a j by adm_le0_seg. Then m_5_1_parent_exists_2 yields a row-1 parent of j,
  contradicting nop.
\<close>

lemma condAB_row1_noparent_zero:
  assumes M: "M \<in> T_PS"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and condB: "RedCondB M"
    and j: "j < Lng M" and nop: "\<not> hasParent M 1 j"
  shows "entry M 1 j = 0"
proof (cases "j = 0")
  case True thus ?thesis using e10 by simp
next
  case j0: False
  hence jp: "0 < j" by simp
  show ?thesis
  proof (rule ccontr)
    assume ne: "entry M 1 j \<noteq> 0"
    hence jpos: "0 < entry M 1 j" by simp
    \<comment> \<open>Locate j's component in P M.\<close>
    have total: "IdxSum (P M) ! (length (P M)) = Lng M"
    proof -
      have "IdxSum (P M) ! (length (P M)) = sum_list (map length (P M))"
        by (simp add: idxsum_nth)
      also have "\<dots> = length (concat (P M))" by (simp add: length_concat)
      also have "concat (P M) = M" by (rule idxsum_concat_P)
      finally show ?thesis by simp
    qed
    have jlt: "j < IdxSum (P M) ! (length (P M))" using j total by simp
    obtain K where K1: "K < length (P M)"
      and K2: "IdxSum (P M) ! K \<le> j"
      and K3: "j < IdxSum (P M) ! (K + 1)"
      using idxsum_locate[OF jlt] by blast
    let ?a = "IdxSum (P M) ! K"
    have arange: "?a \<le> Lng M - 1"
      using idxsum_leftend_lmin[OF M K1] by blast
    have almin: "\<forall>j' < ?a. entry M 0 j' \<ge> entry M 0 ?a"
      using idxsum_leftend_lmin[OF M K1] by blast
    have LMpos: "0 < Lng M" using j by linarith
    have aL: "?a < Lng M"
    proof -
      have "Suc ?a \<le> Suc (Lng M - 1)" using arange by simp
      also have "Suc (Lng M - 1) = Lng M" using LMpos by simp
      finally show ?thesis by simp
    qed
    have ae0: "entry M 0 ?a = 0"
    proof -
      have "entry M 0 0 \<ge> entry M 0 ?a"
      proof (cases "?a = 0")
        case True thus ?thesis using e00 by simp
      next
        case False hence "0 < ?a" by simp
        thus ?thesis using almin by blast
      qed
      thus ?thesis using e00 by (simp add: antisym)
    qed
    have anopar0: "\<not> hasParent M 0 ?a"
      using idxsum_no_parent0_iff[OF M aL] almin unfolding hasParent_def by blast
    have ae1: "entry M 1 ?a = 0"
    proof -
      have "entry M 0 ?a = entry M 1 ?a"
        using condB anopar0 arange
        unfolding RedCondB_def hasParent_def by blast
      thus ?thesis using ae0 by simp
    qed
    have elt: "entry M 1 ?a < entry M 1 j" using ae1 jpos by simp
    have le0aj: "le0 M ?a j"
    proof (cases "?a = j")
      case True
      thus ?thesis using aL by (simp add: le0_def)
    next
      case False
      hence alt: "?a < j" using K2 by simp
      have CK: "P M ! K \<in> set (P M)" using K1 by (rule nth_mem)
      have Czm: "zeroT (P M ! K) \<or> monoT (P M ! K)"
        using m_6_2_P_components_1[OF M] CK by blast
      have Kle: "K \<le> Lng (P M) - 1" using K1 by (cases "P M") auto
      let ?b = "IdxSum (P M) ! (K + 1) - 1"
      have comp: "P M ! K = seg M ?a ?b"
        by (rule m_6_4_P_IdxSum[OF M Kle])
      have diff: "IdxSum (P M) ! (K + 1) = ?a + length (P M ! K)"
        by (rule idxsum_diff[OF K1])
      have lenpos: "0 < length (P M ! K)"
        by (rule idxsum_P_component_nonempty[OF M K1])
      have bge: "j \<le> ?b" using K3 diff lenpos by linarith
      have bL: "?b < Lng M"
      proof -
        have "IdxSum (P M) ! (K + 1) \<le> IdxSum (P M) ! (length (P M))"
          by (rule idxsum_mono) (use K1 in simp_all)
        hence "IdxSum (P M) ! (K + 1) \<le> Lng M" using total by simp
        thus ?thesis using lenpos diff by linarith
      qed
      have CL: "Lng (P M ! K) = Suc ?b - ?a"
        using comp by simp
      have Cgt1: "Lng (P M ! K) > 1" using alt bge CL by linarith
      have Cmono: "monoT (P M ! K)" using Czm Cgt1 by (auto simp: zeroT_def)
      have CTPS: "P M ! K \<in> T_PS"
        using Cgt1 by (cases "P M ! K") (auto simp: T_PS_def)
      have leCfull: "leR (P M ! K) 0 0 (Lng (P M ! K) - 1)"
        using Cmono by (simp add: monoT_def)
      let ?p = "j - ?a"
      have ppos: "0 < ?p" using alt by simp
      have pb: "?p \<le> Lng (P M ! K) - 1" using bge CL alt by linarith
      have leCp: "leR (P M ! K) 0 0 ?p"
        by (rule m_5_1_ancestor_tree_1[OF CTPS leCfull]) (use pb in linarith, use pb in linarith)
      have le0Cp: "le0 (P M ! K) 0 ?p" using leCp by (simp add: leR_def)
      have le0Cseg: "le0 (seg M ?a ?b) 0 ?p \<longleftrightarrow> le0 M (?a + 0) (?a + ?p)"
      proof (rule adm_le0_seg)
        show "?b < Lng M" using bL .
        show "0 \<le> ?b - ?a" by simp
        show "?p \<le> ?b - ?a" using bge CL alt by linarith
        show "?a \<le> ?b" using alt bge by linarith
      qed
      have aplus: "?a + ?p = j" using alt by simp
      have "le0 M (?a + 0) (?a + ?p)" using le0Cp comp le0Cseg by simp
      hence "le0 M ?a j" using aplus by simp
      thus ?thesis by simp
    qed
    have a_lt_j: "?a < j"
    proof -
      have "?a \<noteq> j"
      proof
        assume eq: "?a = j"
        hence "entry M 1 j = 0" using ae1 by simp
        thus False using jpos by simp
      qed
      thus ?thesis using K2 by linarith
    qed
    have leR0aj: "leR M 0 ?a j" using le0aj by (simp add: leR_def)
    obtain j' where j'range: "?a \<le> j'" "j' < j" and j'par: "nextR M 1 j' j"
      using m_5_1_parent_exists_2[OF M a_lt_j j elt leR0aj] by blast
    have "hasParent M 1 j"
      unfolding hasParent_def
    proof (rule ex_ex1I)
      show "\<exists>j0. nextR M 1 j0 j" using j'par by blast
    next
      fix a b assume "nextR M 1 a j" "nextR M 1 b j"
      thus "a = b" using nextR1_unique by blast
    qed
    with nop show False by simp
  qed
qed

end

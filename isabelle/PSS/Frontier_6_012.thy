theory Frontier_6_012
  imports P_6_4_P_IdxSum
begin

text \<open>Row-0 parents are unique: \<open>nextR M 0 _ k\<close> determines its source.\<close>

lemma idxsum_parent0_unique:
  assumes "nextR M 0 a k" "nextR M 0 b k"
  shows "a = b"
proof -
  from assms have na: "nextrel0 M a k" and nb: "nextrel0 M b k"
    by (simp_all add: nextR_def)
  show ?thesis
  proof (rule ccontr)
    assume "a \<noteq> b"
    then consider "a < b" | "b < a" by linarith
    thus False
    proof cases
      case 1
      from na have "a < k" and bnd: "\<forall>j. a < j \<and> j < k \<longrightarrow> entry M 0 j \<ge> entry M 0 k"
        by (auto simp: nextrel0_def)
      from nb have "b < k" and "entry M 0 b < entry M 0 k" by (auto simp: nextrel0_def)
      moreover have "entry M 0 b \<ge> entry M 0 k" using bnd 1 \<open>b < k\<close> by simp
      ultimately show False by simp
    next
      case 2
      from nb have "b < k" and bnd: "\<forall>j. b < j \<and> j < k \<longrightarrow> entry M 0 j \<ge> entry M 0 k"
        by (auto simp: nextrel0_def)
      from na have "a < k" and "entry M 0 a < entry M 0 k" by (auto simp: nextrel0_def)
      moreover have "entry M 0 a \<ge> entry M 0 k" using bnd 2 \<open>a < k\<close> by simp
      ultimately show False by simp
    qed
  qed
qed

text \<open>Hence \<open>\<exists>!\<close>-parent in row 0 collapses to mere existence.\<close>

lemma idxsum_ex1_parent0_iff:
  "(\<exists>!j0. nextR M 0 j0 k) \<longleftrightarrow> (\<exists>j0. nextR M 0 j0 k)"
  using idxsum_parent0_unique by metis

text \<open>No row-0 parent of \<open>k\<close> iff \<open>k\<close> is a row-0 left-minimum.\<close>

lemma idxsum_no_parent0_iff:
  assumes "M \<in> T_PS" "k < Lng M"
  shows "(\<not> (\<exists>!j0. nextR M 0 j0 k)) \<longleftrightarrow> (\<forall>j<k. entry M 0 j \<ge> entry M 0 k)"
proof -
  have "(\<exists>j0. nextR M 0 j0 k) \<longleftrightarrow> (\<exists>j<k. entry M 0 j < entry M 0 k)"
  proof
    assume "\<exists>j0. nextR M 0 j0 k"
    then obtain j0 where "nextR M 0 j0 k" by blast
    hence "j0 < k \<and> entry M 0 j0 < entry M 0 k" by (auto simp: nextR_def nextrel0_def)
    thus "\<exists>j<k. entry M 0 j < entry M 0 k" by blast
  next
    assume "\<exists>j<k. entry M 0 j < entry M 0 k"
    then obtain j where j: "j < k" "entry M 0 j < entry M 0 k" by blast
    obtain j' where "nextR M 0 j' k"
      using m_5_1_parent_exists_1[OF assms(1) j(1) assms(2) j(2)] by blast
    thus "\<exists>j0. nextR M 0 j0 k" by blast
  qed
  hence "(\<not> (\<exists>j0. nextR M 0 j0 k)) \<longleftrightarrow> (\<forall>j<k. \<not> entry M 0 j < entry M 0 k)"
    by blast
  thus ?thesis by (simp add: idxsum_ex1_parent0_iff not_less)
qed

text \<open>
  CORE: the left endpoints of the components of \<open>P M\<close> are exactly the row-0
  left-minima of \<open>M\<close>.  Proved by induction on \<open>P\<close>.  Direction 1 (left endpoint
  \<Rightarrow> left-minimum, in range).
\<close>

lemma idxsum_leftend_lmin:
  assumes "M \<in> T_PS" "J < length (P M)"
  shows "IdxSum (P M) ! J \<le> Lng M - 1
       \<and> (\<forall>j < IdxSum (P M) ! J. entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! J))"
  using assms
proof (induction M arbitrary: J rule: P.induct)
  case (1 M)
  show ?case
  proof (cases "multiT M \<and> 1 < Lng M")
    case multi: True
    let ?c = "Pcut M"
    have multiM: "multiT M" using multi by simp
    have L: "1 < Lng M" using multi by simp
    have step: "P M = P (take ?c M) @ [drop ?c M]"
      using multi by (subst P.simps) simp
    have cut: "0 < ?c \<and> ?c \<le> Lng M - 1 \<and> leR M 0 ?c (Lng M - 1)"
      by (rule Pcut_le[OF L])
    hence c0: "0 < ?c" and cj1: "?c \<le> Lng M - 1" and cle: "leR M 0 ?c (Lng M - 1)"
      by simp_all
    have cL: "?c < Lng M" using cj1 L by simp
    have preTPS: "take ?c M \<in> T_PS"
      using c0 cL by (cases "take ?c M") (auto simp: T_PS_def)
    have lenpre: "length (take ?c M) = ?c" using cL by simp
    \<comment> \<open>length sums\<close>
    have concpre: "concat (P (take ?c M)) = take ?c M" by (rule idxsum_concat_P)
    have sumpre: "sum_list (map length (P (take ?c M))) = ?c"
      using concpre lenpre by (metis length_concat)
    have lenPM: "length (P M) = Suc (length (P (take ?c M)))"
      using step by simp
    show ?thesis
    proof (cases "J < length (P (take ?c M))")
      case inpre: True
      have eqidx: "IdxSum (P M) ! J = IdxSum (P (take ?c M)) ! J"
      proof -
        have "IdxSum (P M) ! J = sum_list (map length (take J (P M)))"
          using "1.prems"(2) by (simp add: idxsum_nth)
        also have "take J (P M) = take J (P (take ?c M))"
          using inpre step by (simp add: append_eq_conv_conj)
        also have "sum_list (map length (take J (P (take ?c M)))) = IdxSum (P (take ?c M)) ! J"
          using inpre by (simp add: idxsum_nth less_imp_le_nat)
        finally show ?thesis .
      qed
      have IH: "IdxSum (P (take ?c M)) ! J \<le> Lng (take ?c M) - 1
              \<and> (\<forall>j < IdxSum (P (take ?c M)) ! J.
                   entry (take ?c M) 0 j \<ge> entry (take ?c M) 0 (IdxSum (P (take ?c M)) ! J))"
        using "1.IH"[OF multi preTPS inpre] .
      let ?a = "IdxSum (P (take ?c M)) ! J"
      have aub: "?a \<le> ?c - 1" using IH lenpre by simp
      have altc: "?a < ?c" using aub c0 by simp
      have arange: "IdxSum (P M) ! J \<le> Lng M - 1"
        using eqidx altc cj1 by simp
      have lmin: "\<forall>j < IdxSum (P M) ! J. entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! J)"
      proof (intro allI impI)
        fix j assume jlt: "j < IdxSum (P M) ! J"
        hence jlta: "j < ?a" using eqidx by simp
        hence jc: "j < ?c" and ac: "?a < ?c" using altc by auto
        have e1: "entry (take ?c M) 0 j = entry M 0 j"
          using jc cL by (simp add: entry_def)
        have e2: "entry (take ?c M) 0 ?a = entry M 0 ?a"
          using ac cL by (simp add: entry_def)
        have "entry (take ?c M) 0 j \<ge> entry (take ?c M) 0 ?a"
          using IH jlta by blast
        thus "entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! J)"
          using e1 e2 eqidx by simp
      qed
      show ?thesis using arange lmin by blast
    next
      case False
      with "1.prems"(2) lenPM have Jeq: "J = length (P (take ?c M))" by simp
      have eqc: "IdxSum (P M) ! J = ?c"
      proof -
        have "IdxSum (P M) ! J = sum_list (map length (take J (P M)))"
          using "1.prems"(2) by (simp add: idxsum_nth)
        also have "take J (P M) = P (take ?c M)"
          using Jeq step by simp
        also have "sum_list (map length (P (take ?c M))) = ?c" by (rule sumpre)
        finally show ?thesis .
      qed
      have arange: "IdxSum (P M) ! J \<le> Lng M - 1" using eqc cj1 by simp
      have lmin: "\<forall>j < IdxSum (P M) ! J. entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! J)"
        using eqc P_add_Pcut_left_min[OF "1.prems"(1) multiM L] by simp
      show ?thesis using arange lmin by blast
    qed
  next
    case nonmulti: False
    hence PM: "P M = [M]" by (subst P.simps) (simp only: if_not_P if_False)
    hence Jeq: "J = 0" using "1.prems"(2) by simp
    have idx0: "IdxSum (P M) ! J = 0"
      using Jeq PM by (simp add: IdxSum_def)
    show ?thesis using idx0 by simp
  qed
qed

text \<open>Direction 2 (left-minimum, in range \<Rightarrow> left endpoint).\<close>

lemma idxsum_lmin_leftend:
  assumes "M \<in> T_PS" "k \<le> Lng M - 1"
    "\<forall>j<k. entry M 0 j \<ge> entry M 0 k"
  shows "\<exists>J < length (P M). IdxSum (P M) ! J = k"
  using assms
proof (induction M arbitrary: k rule: P.induct)
  case (1 M)
  show ?case
  proof (cases "multiT M \<and> 1 < Lng M")
    case multi: True
    let ?c = "Pcut M"
    have L: "1 < Lng M" using multi by simp
    have step: "P M = P (take ?c M) @ [drop ?c M]"
      using multi by (subst P.simps) simp
    have cut: "0 < ?c \<and> ?c \<le> Lng M - 1 \<and> leR M 0 ?c (Lng M - 1)"
      by (rule Pcut_le[OF L])
    hence c0: "0 < ?c" and cj1: "?c \<le> Lng M - 1" and cle: "leR M 0 ?c (Lng M - 1)"
      by simp_all
    have cL: "?c < Lng M" using cj1 L by simp
    have preTPS: "take ?c M \<in> T_PS"
      using c0 cL by (cases "take ?c M") (auto simp: T_PS_def)
    have lenpre: "length (take ?c M) = ?c" using cL by simp
    have concpre: "concat (P (take ?c M)) = take ?c M" by (rule idxsum_concat_P)
    have sumpre: "sum_list (map length (P (take ?c M))) = ?c"
      using concpre lenpre by (metis length_concat)
    have lenPM: "length (P M) = Suc (length (P (take ?c M)))"
      using step by simp
    \<comment> \<open>Rule out \<open>?c < k\<close>: such \<open>k\<close> cannot be a left-minimum.\<close>
    have kc: "k \<le> ?c"
    proof (rule ccontr)
      assume "\<not> k \<le> ?c"
      hence ck: "?c < k" by simp
      have kL: "k < Lng M" using "1.prems"(2) L by simp
      have ck1: "k \<le> Lng M - 1" using "1.prems"(2) .
      have leck: "leR M 0 ?c k"
        by (rule m_5_1_ancestor_tree_1[OF "1.prems"(1) cle less_imp_le[OF ck] ck1])
      have "entry M 0 ?c < entry M 0 k"
        by (rule m_5_1_ancestor_basic_1[OF "1.prems"(1) ck order.refl leck])
      moreover have "entry M 0 ?c \<ge> entry M 0 k" using "1.prems"(3) ck by blast
      ultimately show False by simp
    qed
    show ?thesis
    proof (cases "k = ?c")
      case True
      have "IdxSum (P M) ! (length (P (take ?c M))) = ?c"
      proof -
        have "IdxSum (P M) ! (length (P (take ?c M)))
              = sum_list (map length (take (length (P (take ?c M))) (P M)))"
          using lenPM by (simp add: idxsum_nth)
        also have "take (length (P (take ?c M))) (P M) = P (take ?c M)"
          using step by simp
        finally show ?thesis using sumpre by simp
      qed
      thus ?thesis using True lenPM by (intro exI[of _ "length (P (take ?c M))"]) simp
    next
      case False
      with kc have kltc: "k < ?c" by simp
      \<comment> \<open>Transfer the left-minimum to the prefix and apply the IH.\<close>
      have kpre: "k \<le> Lng (take ?c M) - 1" using kltc lenpre by simp
      have lminpre: "\<forall>j<k. entry (take ?c M) 0 j \<ge> entry (take ?c M) 0 k"
      proof (intro allI impI)
        fix j assume "j < k"
        hence jc: "j < ?c" and kc': "k < ?c" using kltc by auto
        have "entry (take ?c M) 0 j = entry M 0 j" using jc cL by (simp add: entry_def)
        moreover have "entry (take ?c M) 0 k = entry M 0 k"
          using kc' cL by (simp add: entry_def)
        ultimately show "entry (take ?c M) 0 j \<ge> entry (take ?c M) 0 k"
          using "1.prems"(3) \<open>j < k\<close> by simp
      qed
      obtain J where J: "J < length (P (take ?c M))" "IdxSum (P (take ?c M)) ! J = k"
        using "1.IH"[OF multi preTPS kpre lminpre] by blast
      have "IdxSum (P M) ! J = IdxSum (P (take ?c M)) ! J"
      proof -
        have "IdxSum (P M) ! J = sum_list (map length (take J (P M)))"
          using J(1) lenPM by (simp add: idxsum_nth)
        also have "take J (P M) = take J (P (take ?c M))"
          using J(1) step by (simp add: append_eq_conv_conj)
        also have "sum_list (map length (take J (P (take ?c M)))) = IdxSum (P (take ?c M)) ! J"
          using J(1) by (simp add: idxsum_nth less_imp_le_nat)
        finally show ?thesis .
      qed
      hence "IdxSum (P M) ! J = k" using J(2) by simp
      thus ?thesis using J(1) lenPM by (intro exI[of _ J]) simp
    qed
  next
    case nonmulti: False
    hence PM: "P M = [M]" by (subst P.simps) (simp only: if_not_P if_False)
    \<comment> \<open>For non-multi \<open>M\<close>, the only row-0 left-minimum in range is \<open>0\<close>.\<close>
    have k0: "k = 0"
    proof (rule ccontr)
      assume "k \<noteq> 0"
      hence kpos: "0 < k" by simp
      have L1: "Lng M \<ge> 1" using "1.prems"(1) by (cases M) (auto simp: T_PS_def)
      have kL: "k < Lng M" using "1.prems"(2) kpos by simp
      have neq1: "Lng M \<noteq> 1" using kpos "1.prems"(2) kL by linarith
      have L: "1 < Lng M" by (rule T_PS_Lng_gt1[OF "1.prems"(1) neq1])
      have notmulti: "\<not> multiT M" using nonmulti L by simp
      have le00: "leR M 0 0 (Lng M - 1)"
        using m_6_2_not_multi_iff_le[OF "1.prems"(1)] notmulti by simp
      have le0k: "leR M 0 0 k"
        by (rule m_5_1_ancestor_tree_1[OF "1.prems"(1) le00 _ "1.prems"(2)]) simp
      have "entry M 0 0 < entry M 0 k"
        by (rule m_5_1_ancestor_basic_1[OF "1.prems"(1) kpos order.refl le0k])
      moreover have "entry M 0 0 \<ge> entry M 0 k" using "1.prems"(3) kpos by blast
      ultimately show False by simp
    qed
    have "IdxSum (P M) ! 0 = 0" using PM by (simp add: IdxSum_def)
    thus ?thesis using PM k0 by (intro exI[of _ 0]) simp
  qed
qed

end

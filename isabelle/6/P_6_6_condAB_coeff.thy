theory P_6_6_condAB_coeff
  imports Frontier_6_018
begin

text \<open>補題（条件(A)と(B)と係数の基本性質）.\<close>

text \<open>
  m: 補題（条件(A)と(B)と係数の基本性質） — discharges @{text p_6_6_condAB_coeff}
  (§6.6, 補題（条件(A)と(B)と係数の基本性質）).
\<close>

lemma m_6_6_condAB_coeff:
  assumes MT: "M \<in> T_PS" and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and condA: "RedCondA M"
  shows
    "(\<forall>j \<le> Lng M - 1. entry M 0 j \<le> j)
   \<and> (RedCondB M \<longrightarrow> (\<forall>j \<le> Lng M - 1. entry M 0 j \<ge> entry M 1 j))
   \<and> (\<forall>i \<le> 1. (i = 0 \<or> (i = 1 \<and> RedCondB M)) \<longrightarrow>
        (\<forall>j \<le> Lng M - 1.
           (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j))"
proof -
  have LM: "1 \<le> Lng M" using MT by (cases M) (auto simp: T_PS_def)
  \<comment> \<open>From RedCondA: if hasParent M i j, then entry M i j = entry M i (parent M i j) + 1.\<close>
  have condA_entry: "\<And>i j. i \<le> 1 \<Longrightarrow> j < Lng M \<Longrightarrow> hasParent M i j \<Longrightarrow>
      entry M i (parent M i j) + 1 = entry M i j"
    using condA unfolding RedCondA_def by blast
  \<comment> \<open>parent M i j < j when hasParent M i j.\<close>
  have parent_lt: "\<And>i j. i \<le> 1 \<Longrightarrow> j < Lng M \<Longrightarrow> hasParent M i j \<Longrightarrow> parent M i j < j"
  proof -
    fix i j assume hi: "i \<le> 1" and hj: "j < Lng M" and hp: "hasParent M i j"
    from hp obtain j0 where j0: "nextR M i j0 j"
      unfolding hasParent_def by blast
    have "parent M i j = j0" unfolding parent_def
      using hp j0 by (auto simp: hasParent_def dest: the1_equality)
    moreover have "j0 < j"
      using j0 unfolding nextR_def nextrel0_def nextrel1_def by (auto split: if_splits)
    ultimately show "parent M i j < j" by simp
  qed
  \<comment> \<open>row-0 no-parent implies entry M 0 j = 0.\<close>
  have nopar0_zero: "\<And>j. j < Lng M \<Longrightarrow> \<not> hasParent M 0 j \<Longrightarrow> entry M 0 j = 0"
  proof -
    fix j assume hj: "j < Lng M" and hp: "\<not> hasParent M 0 j"
    have lmin: "\<forall>j' < j. entry M 0 j' \<ge> entry M 0 j"
      using idxsum_no_parent0_iff[OF MT hj] hp unfolding hasParent_def by blast
    have "entry M 0 0 \<ge> entry M 0 j"
    proof (cases "j = 0")
      case True thus ?thesis using e00 by simp
    next
      case False hence "0 < j" by simp
      thus ?thesis using lmin by blast
    qed
    thus "entry M 0 j = 0" using e00 by simp
  qed
  \<comment> \<open>----------- Part 1: entry M 0 j ≤ j for all j < Lng M. -----------\<close>
  have part1: "\<forall>j. j < Lng M \<longrightarrow> entry M 0 j \<le> j"
  proof (intro allI impI)
    fix j assume hjL: "j < Lng M"
    show "entry M 0 j \<le> j"
    using hjL
    proof (induction j rule: less_induct)
      case (less j)
      show "entry M 0 j \<le> j"
      proof (cases "hasParent M 0 j")
        case hp: False
        have "entry M 0 j = 0" using nopar0_zero[OF less.prems] hp by simp
        thus ?thesis by simp
      next
        case hp: True
        let ?p = "parent M 0 j"
        have plt: "?p < j" using parent_lt[of 0 j] hp less.prems by simp
        have pL: "?p < Lng M" using plt less.prems by linarith
        have pind: "entry M 0 ?p \<le> ?p" using less.IH[OF plt pL] .
        have eA: "entry M 0 ?p + 1 = entry M 0 j"
          using condA_entry[of 0 j] hp less.prems by simp
        from pind eA plt show "entry M 0 j \<le> j" by linarith
      qed
    qed
  qed
  \<comment> \<open>----------- Part 2: RedCondB → entry M 0 j ≥ entry M 1 j for all j < Lng M. -----------\<close>
  have part2: "RedCondB M \<longrightarrow> (\<forall>j. j < Lng M \<longrightarrow> entry M 0 j \<ge> entry M 1 j)"
  proof (intro impI allI impI)
    fix j
    assume condB: "RedCondB M" and hjL: "j < Lng M"
    show "entry M 0 j \<ge> entry M 1 j"
    using hjL
    proof (induction j rule: less_induct)
      case (less j)
      show "entry M 0 j \<ge> entry M 1 j"
      proof (cases "hasParent M 1 j")
        case hp1: False
        have "entry M 1 j = 0"
          using condAB_row1_noparent_zero[OF MT e00 e10 condB less.prems hp1] .
        thus ?thesis by simp
      next
        case hp1: True
        let ?p1 = "parent M 1 j"
        have p1lt: "?p1 < j" using parent_lt[of 1 j] hp1 less.prems by simp
        have p1L: "?p1 < Lng M" using p1lt less.prems by linarith
        have e1A: "entry M 1 ?p1 + 1 = entry M 1 j"
          using condA_entry[of 1 j] hp1 less.prems by simp
        have IH1: "entry M 0 ?p1 \<ge> entry M 1 ?p1"
          using less.IH[OF p1lt p1L] .
        have par1: "nextR M 1 ?p1 j"
          using hp1 unfolding hasParent_def parent_def by (rule theI')
        have le0p1j: "le0 M ?p1 j"
          using poper_nextR_imp_le0[OF par1] by (simp add: leR_def)
        have leR0p1j: "leR M 0 ?p1 j" using le0p1j by (simp add: leR_def)
        have e0lt: "entry M 0 ?p1 < entry M 0 j"
          by (rule m_5_1_ancestor_basic_1[OF MT p1lt _ leR0p1j]) simp
        from e1A IH1 e0lt show "entry M 0 j \<ge> entry M 1 j" by linarith
      qed
    qed
  qed
  \<comment> \<open>----------- Part 3: gap ⟹ strict entry bound. -----------\<close>
  have part3: "\<forall>i \<le> 1. (i = 0 \<or> (i = 1 \<and> RedCondB M)) \<longrightarrow>
        (\<forall>j \<le> Lng M - 1.
           (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j)"
  proof (rule allI, rule impI, rule impI)
    fix i :: nat assume hi: "i \<le> 1" and hcond: "i = 0 \<or> (i = 1 \<and> RedCondB M)"
    \<comment> \<open>Prove the implication for all j simultaneously by strong induction.\<close>
    have key: "\<forall>j. j < Lng M \<longrightarrow>
        (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j"
    proof (intro allI)
      fix j
      show "j < Lng M \<longrightarrow> (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j"
      proof (induction j rule: less_induct)
        case (less j)
        show ?case
        proof (intro impI)
          assume hjL: "j < Lng M"
            and gap: "\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j"
          from gap obtain j0' j1' where
              gap0: "\<not> leR M i j0' j1'" and gap1: "j0' < j1'" and gap2: "j1' \<le> j"
            by blast
          have jpos: "0 < j" using gap1 gap2 by linarith
          \<comment> \<open>Abbreviate the IH for later use.\<close>
          have IH: "\<forall>y < j. y < Lng M \<longrightarrow>
              (\<exists>j0'' j1''. \<not> leR M i j0'' j1'' \<and> j0'' < j1'' \<and> j1'' \<le> y) \<longrightarrow>
              entry M i y < y"
            using less.IH by blast
          show "entry M i j < j"
          proof (cases "hasParent M i j")
            case hp: False
            \<comment> \<open>No parent: entry M i j = 0 < j.\<close>
            show ?thesis
            proof (cases i)
              case i0: 0
              have "entry M 0 j = 0"
                using nopar0_zero[OF hjL] hp i0 by simp
              thus ?thesis using jpos by (simp add: i0)
            next
              case i1: (Suc n)
              have i_eq: "i = 1" using hi i1 by simp
              have condB: "RedCondB M" using hcond i_eq by simp
              have "entry M 1 j = 0"
                using condAB_row1_noparent_zero[OF MT e00 e10 condB hjL] hp i_eq by simp
              thus ?thesis using jpos i_eq by simp
            qed
          next
            case hp: True
            let ?p = "parent M i j"
            have plt: "?p < j" using parent_lt[of i j] hp hjL hi by simp
            have pL: "?p < Lng M" using plt hjL by linarith
            have eA: "entry M i ?p + 1 = entry M i j"
              using condA_entry[of i j] hp hjL hi by simp
            show "entry M i j < j"
            proof (cases "j1' \<le> ?p")
              case True
              \<comment> \<open>Gap entirely in [0..?p]: apply IH to ?p.\<close>
              have gap_p: "\<exists>j0'' j1''. \<not> leR M i j0'' j1'' \<and> j0'' < j1'' \<and> j1'' \<le> ?p"
                using gap0 gap1 True by blast
              have epp: "entry M i ?p < ?p" using IH[rule_format, OF plt pL gap_p] .
              from epp eA plt show "entry M i j < j" by linarith
            next
              case False
              \<comment> \<open>j1' > ?p. Case split on whether ?p < j-1 or ?p = j-1.\<close>
              show ?thesis
              proof (cases "?p < j - 1")
                case ppj1: True
                \<comment> \<open>?p < j-1: entry M i j = entry M i ?p + 1 ≤ ?p + 1 ≤ j-1 < j.\<close>
                have eple: "entry M i ?p \<le> ?p"
                proof (cases i)
                  case 0
                  thus ?thesis using part1 pL by blast
                next
                  case (Suc n)
                  have i_eq: "i = 1" using hi \<open>i = Suc n\<close> by simp
                  have condB: "RedCondB M" using hcond i_eq by simp
                  have e0ge: "entry M 0 ?p \<ge> entry M 1 ?p"
                    using part2 condB pL by blast
                  have e0le: "entry M 0 ?p \<le> ?p" using part1 pL by blast
                  have "entry M 1 ?p \<le> ?p" using e0ge e0le by linarith
                  thus ?thesis using i_eq by simp
                qed
                from eple eA ppj1 show "entry M i j < j" by linarith
              next
                case pj1: False
                \<comment> \<open>?p = j-1. Since j1' > ?p = j-1 and j1' ≤ j, we get j1' = j.\<close>
                hence peq: "?p = j - 1" using plt by linarith
                hence j1'_eq_j: "j1' = j" using False gap2 by linarith
                \<comment> \<open>So ¬leR M i j0' j, j0' < j.\<close>
                have gap0': "\<not> leR M i j0' j" using gap0 j1'_eq_j by simp
                \<comment> \<open>j0' ≤ ?p or j0' > ?p.\<close>
                show ?thesis
                proof (cases "j0' \<le> ?p")
                  case hj0: True
                  \<comment> \<open>j0' ≤ ?p.\<close>
                  have j0'_lt_p: "j0' < ?p"
                  proof -
                    have "j0' \<noteq> ?p"
                    proof
                      assume eq: "j0' = ?p"
                      have par: "nextR M i ?p j"
                        using hp unfolding hasParent_def parent_def by (rule theI')
                      have "leR M i ?p j"
                      proof (cases "i = 0")
                        case True
                        hence nr: "nextrel0 M ?p j" using par by (simp add: nextR_def)
                        have pL: "?p < Lng M" using nr by (simp add: nextrel0_def)
                        have jL: "j < Lng M" using nr by (simp add: nextrel0_def)
                        have rtc: "(nextrel0 M)\<^sup>*\<^sup>* ?p j" using nr by (rule r_into_rtranclp)
                        thus ?thesis using True pL jL by (simp add: leR_def le0_def)
                      next
                        case False
                        hence nr: "nextrel1 M ?p j" using par by (simp add: nextR_def)
                        have pL: "?p < Lng M" using nr by (simp add: nextrel1_def)
                        have jL: "j < Lng M" using nr by (simp add: nextrel1_def)
                        have rtc: "(nextrel1 M)\<^sup>*\<^sup>* ?p j" using nr by (rule r_into_rtranclp)
                        thus ?thesis using False pL jL by (simp add: leR_def le1_def)
                      qed
                      thus False using gap0' eq by simp
                    qed
                    thus ?thesis using hj0 by linarith
                  qed
                  have not_le_p: "\<not> leR M i j0' ?p"
                  proof
                    assume le_j0'_p: "leR M i j0' ?p"
                    have par: "nextR M i ?p j"
                      using hp unfolding hasParent_def parent_def by (rule theI')
                    have le_p_j: "leR M i ?p j"
                    proof (cases "i = 0")
                      case True
                      hence nr: "nextrel0 M ?p j" using par by (simp add: nextR_def)
                      have pL: "?p < Lng M" using nr by (simp add: nextrel0_def)
                      have jL: "j < Lng M" using nr by (simp add: nextrel0_def)
                      have rtc: "(nextrel0 M)\<^sup>*\<^sup>* ?p j" using nr by (rule r_into_rtranclp)
                      thus ?thesis using True pL jL by (simp add: leR_def le0_def)
                    next
                      case False
                      hence nr: "nextrel1 M ?p j" using par by (simp add: nextR_def)
                      have pL: "?p < Lng M" using nr by (simp add: nextrel1_def)
                      have jL: "j < Lng M" using nr by (simp add: nextrel1_def)
                      have rtc: "(nextrel1 M)\<^sup>*\<^sup>* ?p j" using nr by (rule r_into_rtranclp)
                      thus ?thesis using False pL jL by (simp add: leR_def le1_def)
                    qed
                    have "leR M i j0' j"
                    proof (cases "i = 0")
                      case True
                      from le_j0'_p have "le0 M j0' ?p" using True by (simp add: leR_def)
                      from le_p_j have "le0 M ?p j" using True by (simp add: leR_def)
                      show ?thesis using le0_trans[OF \<open>le0 M j0' ?p\<close> \<open>le0 M ?p j\<close>] True
                        by (simp add: leR_def)
                    next
                      case False
                      have i_eq: "i = 1" using hi False by linarith
                      from le_j0'_p have le0p: "le1 M j0' ?p" using False by (simp add: leR_def)
                      from le_p_j have le1p: "le1 M ?p j" using False by (simp add: leR_def)
                      have "le1 M j0' j" using le0p le1p by (auto simp: le1_def intro: rtranclp_trans)
                      thus ?thesis using False by (simp add: leR_def)
                    qed
                    thus False using gap0' by simp
                  qed
                  have gap_p: "\<exists>j0'' j1''. \<not> leR M i j0'' j1'' \<and> j0'' < j1'' \<and> j1'' \<le> ?p"
                    using not_le_p gap1 j1'_eq_j j0'_lt_p by blast
                  have epp2: "entry M i ?p < ?p" using IH[rule_format, OF plt pL gap_p] .
                  from epp2 eA plt show "entry M i j < j" by linarith
                next
                  case hj0: False
                  \<comment> \<open>j0' > ?p and j0' < j (from j0' < j1' = j).\<close>
                  \<comment> \<open>?p = j-1, so j-1 < j0' < j is impossible for natural numbers.\<close>
                  have lt1: "j0' < j" using gap1 j1'_eq_j by linarith
                  have lt2: "j - 1 < j0'" using hj0 peq by linarith
                  from lt1 lt2 peq show "entry M i j < j" by linarith
                qed
              qed
            qed
          qed
        qed
      qed
    qed
    have key': "\<And>j. j \<le> Lng M - 1 \<Longrightarrow>
        (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<Longrightarrow> entry M i j < j"
    proof -
      fix j :: nat
      assume hjle: "j \<le> Lng M - 1"
        and gap: "\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j"
      have hjL: "j < Lng M" using hjle LM by linarith
      from key have "(\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j"
        using hjL by blast
      thus "entry M i j < j" using gap by blast
    qed
    show "\<forall>j \<le> Lng M - 1. (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow>
           entry M i j < j"
    proof (intro allI impI)
      fix j :: nat
      assume "j \<le> Lng M - 1"
        and "\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j"
      thus "entry M i j < j" by (rule key')
    qed
  qed
  \<comment> \<open>Assemble: convert j ≤ Lng M - 1 ↔ j < Lng M (using LM: 1 ≤ Lng M).\<close>
  have part1': "\<forall>j \<le> Lng M - 1. entry M 0 j \<le> j"
  proof (intro allI impI)
    fix j assume hjle: "j \<le> Lng M - 1"
    have "j < Lng M" using hjle LM by linarith
    thus "entry M 0 j \<le> j" using part1 by blast
  qed
  have part2': "RedCondB M \<longrightarrow> (\<forall>j \<le> Lng M - 1. entry M 0 j \<ge> entry M 1 j)"
  proof (intro impI allI impI)
    fix j assume cb: "RedCondB M" and hjle: "j \<le> Lng M - 1"
    have "j < Lng M" using hjle LM by linarith
    thus "entry M 0 j \<ge> entry M 1 j" using part2 cb by blast
  qed
  show ?thesis using part1' part2' part3 by blast
qed

lemma p_6_6_condAB_coeff:
  assumes "M \<in> T_PS" "entry M 0 0 = 0" "entry M 1 0 = 0" "RedCondA M"
  shows
    "(\<forall>j \<le> Lng M - 1. entry M 0 j \<le> j)
   \<and> (RedCondB M \<longrightarrow> (\<forall>j \<le> Lng M - 1. entry M 0 j \<ge> entry M 1 j))
   \<and> (\<forall>i \<le> 1. (i = 0 \<or> (i = 1 \<and> RedCondB M)) \<longrightarrow>
        (\<forall>j \<le> Lng M - 1.
           (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j))"
  using assms by (rule m_6_6_condAB_coeff)

end

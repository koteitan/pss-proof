theory P_6_2_P_additive
  imports Frontier_6_006
begin

text \<open>命題（\<open>P\<close>の加法性） — additivity of \<open>P\<close> at a left-minimal cut \<open>j\<^sub>0\<close>.\<close>

text \<open>
  m: 命題（\<open>P\<close>の加法性） — discharges @{text p_6_2_P_additive}.
  Additivity of \<open>P\<close> at a left-minimal cut \<open>j\<^sub>0\<close>.  We prove the equivalent
  \<open>take\<close> / \<open>drop\<close> form by strong induction on \<open>Lng M\<close>: in the multi-term case
  the recursive cut \<open>c = Pcut M\<close> satisfies \<open>j\<^sub>0 \<le> c\<close> (article: \<open>0 < j\<^sub>0 \<le> j'\<^sub>0\<close>),
  and both the prefix \<open>take c M\<close> and the suffix \<open>drop j\<^sub>0 M\<close> are strictly shorter,
  so the induction hypothesis applies to both, mirroring the article's
  lexicographic induction on \<open>(j'\<^sub>0 - j\<^sub>0, j\<^sub>0)\<close>.
\<close>

lemma m_6_2_P_additive:
  assumes "M \<in> T_PS" "0 < j0" "j0 \<le> Lng M - 1"
    and "\<And>j. j < j0 \<Longrightarrow> entry M 0 j \<ge> entry M 0 j0"
  shows "P M = P (seg M 0 (j0 - 1)) @ P (seg M j0 (Lng M - 1))"
proof -
  have "\<forall>Mm j0. Mm \<in> T_PS \<longrightarrow> Lng Mm = n \<longrightarrow> 0 < j0 \<longrightarrow> j0 \<le> Lng Mm - 1 \<longrightarrow>
        (\<forall>j. j < j0 \<longrightarrow> entry Mm 0 j \<ge> entry Mm 0 j0) \<longrightarrow>
        P Mm = P (take j0 Mm) @ P (drop j0 Mm)" for n
  proof (induction n rule: less_induct)
    case (less n)
    show ?case
    proof (intro allI impI)
      fix j0 :: nat and Mm :: pairseq
      assume MT: "Mm \<in> T_PS" and Ln: "Lng Mm = n" and j00: "0 < j0"
        and j0L: "j0 \<le> Lng Mm - 1"
        and hyp: "\<forall>j. j < j0 \<longrightarrow> entry Mm 0 j \<ge> entry Mm 0 j0"
      have L: "Lng Mm > 1" using j00 j0L by linarith
      show "P Mm = P (take j0 Mm) @ P (drop j0 Mm)"
      proof (cases "multiT Mm")
        case nonmulti: False
        have "monoT Mm" using nonmulti L by (auto simp: multiT_def zeroT_def)
        hence le00: "leR Mm 0 0 (Lng Mm - 1)" by (simp add: monoT_def)
        have "entry Mm 0 0 < entry Mm 0 j0"
          by (rule m_5_1_ancestor_basic_1[OF MT j00 j0L le00])
        moreover have "entry Mm 0 0 \<ge> entry Mm 0 j0" using hyp j00 by blast
        ultimately show ?thesis by simp
      next
        case multi: True
        let ?c = "Pcut Mm"
        let ?j1 = "Lng Mm - 1"
        from P_add_Pcut_props[OF L] have c0: "0 < ?c" and cj1: "?c \<le> ?j1"
          and lec: "leR Mm 0 ?c ?j1" by auto
        have cL: "?c < Lng Mm" using cj1 L by simp
        have lmin: "\<And>j. j < ?c \<Longrightarrow> entry Mm 0 j \<ge> entry Mm 0 ?c"
          using P_add_Pcut_left_min[OF MT multi L] .
        have j0c: "j0 \<le> ?c"
        proof (rule ccontr)
          assume "\<not> j0 \<le> ?c"
          hence cj0: "?c < j0" by simp
          have "entry Mm 0 ?c < entry Mm 0 j0"
            by (rule m_5_1_ancestor_basic_1[OF MT cj0 j0L lec])
          moreover have "entry Mm 0 ?c \<ge> entry Mm 0 j0" using hyp cj0 by blast
          ultimately show False by simp
        qed
        have cond: "multiT Mm \<and> 1 < Lng Mm" using multi L by simp
        have Pstep: "P Mm = P (take ?c Mm) @ [drop ?c Mm]"
          by (subst P.simps) (simp only: cond if_True simp_thms)
        have Pdrop_c: "P (drop ?c Mm) = [drop ?c Mm]"
          by (rule P_add_drop_ancestor[OF MT c0 cj1 lec])
        show ?thesis
        proof (cases "j0 = ?c")
          case True
          show ?thesis using Pstep Pdrop_c True by simp
        next
          case False
          with j0c have j0ltc: "j0 < ?c" by simp
          let ?Mp = "take ?c Mm"
          have MpT: "?Mp \<in> T_PS" using c0 cL by (cases ?Mp) (auto simp: T_PS_def)
          have LMp: "Lng ?Mp = ?c" using cL by simp
          have IH1: "P ?Mp = P (take j0 ?Mp) @ P (drop j0 ?Mp)"
          proof -
            have "Lng ?Mp < n" using LMp cL Ln by simp
            moreover have "j0 \<le> Lng ?Mp - 1" using LMp j0ltc by simp
            moreover have "\<forall>j. j < j0 \<longrightarrow> entry ?Mp 0 j \<ge> entry ?Mp 0 j0"
            proof (intro allI impI)
              fix j assume "j < j0"
              hence "j < ?c" "j0 < ?c" using j0ltc by auto
              hence "entry ?Mp 0 j = entry Mm 0 j" "entry ?Mp 0 j0 = entry Mm 0 j0"
                by (auto simp: entry_def)
              thus "entry ?Mp 0 j \<ge> entry ?Mp 0 j0" using hyp \<open>j < j0\<close> by simp
            qed
            ultimately show ?thesis
              using less.IH[rule_format, OF _ MpT refl j00] by blast
          qed
          have tj0: "take j0 ?Mp = take j0 Mm"
            using j0ltc by (simp add: take_take min.absorb1)
          have dj0: "drop j0 ?Mp = take (?c - j0) (drop j0 Mm)"
            by (simp add: drop_take)
          let ?Ms = "drop j0 Mm"
          have MsT: "?Ms \<in> T_PS" using j0L L by (cases ?Ms) (auto simp: T_PS_def)
          have LMs: "Lng ?Ms = Lng Mm - j0" by simp
          have IH2: "P ?Ms = P (take (?c - j0) ?Ms) @ P (drop (?c - j0) ?Ms)"
          proof -
            have "Lng ?Ms < n" using LMs j00 Ln L by simp
            moreover have "0 < ?c - j0" using j0ltc by simp
            moreover have "?c - j0 \<le> Lng ?Ms - 1" using LMs cj1 j00 by simp
            moreover have "\<forall>j. j < ?c - j0 \<longrightarrow> entry ?Ms 0 j \<ge> entry ?Ms 0 (?c - j0)"
            proof (intro allI impI)
              fix j assume jlt: "j < ?c - j0"
              have jc: "j0 + j < ?c" using jlt j0c by simp
              hence jcL: "j0 + j < Lng Mm" using cL by simp
              have e1: "entry ?Ms 0 j = entry Mm 0 (j0 + j)"
                using jcL by (simp add: entry_def nth_drop)
              have e2: "entry ?Ms 0 (?c - j0) = entry Mm 0 ?c"
                using j0c cL by (simp add: entry_def nth_drop)
              have "entry Mm 0 (j0 + j) \<ge> entry Mm 0 ?c" using jc by (rule lmin)
              thus "entry ?Ms 0 j \<ge> entry ?Ms 0 (?c - j0)" using e1 e2 by simp
            qed
            ultimately show ?thesis
              using less.IH[rule_format, OF _ MsT refl] by blast
          qed
          have ds: "drop (?c - j0) ?Ms = drop ?c Mm"
            using j0c by (simp add: drop_drop)
          have IH1': "P (take ?c Mm) = P (take j0 Mm) @ P (take (?c - j0) ?Ms)"
            using IH1 by (simp only: tj0 dj0)
          have IH2': "P ?Ms = P (take (?c - j0) ?Ms) @ P (drop ?c Mm)"
            using IH2 by (simp only: ds)
          have "P Mm = P (take ?c Mm) @ [drop ?c Mm]" by (rule Pstep)
          also have "\<dots> = (P (take j0 Mm) @ P (take (?c - j0) ?Ms)) @ [drop ?c Mm]"
            by (simp only: IH1')
          also have "\<dots> = P (take j0 Mm) @ (P (take (?c - j0) ?Ms) @ P (drop ?c Mm))"
            by (simp only: Pdrop_c append_assoc)
          also have "\<dots> = P (take j0 Mm) @ P ?Ms" by (simp only: IH2')
          finally show ?thesis .
        qed
      qed
    qed
  qed
  hence main: "P M = P (take j0 M) @ P (drop j0 M)"
    using assms by blast
  have e1: "take j0 M = seg M 0 (j0 - 1)"
    using assms(2,3) by (subst P_add_seg_0_eq_take) auto
  have e2: "drop j0 M = seg M j0 (Lng M - 1)"
    using assms(2,3) by (subst P_add_seg_to_last_eq_drop) auto
  show ?thesis using main e1 e2 by simp
qed


lemma p_6_2_P_additive:
  assumes "M \<in> T_PS" "0 < j0" "j0 \<le> Lng M - 1"
    and "\<And>j. j < j0 \<Longrightarrow> entry M 0 j \<ge> entry M 0 j0"
  shows "P M = P (seg M 0 (j0 - 1)) @ P (seg M j0 (Lng M - 1))"
  using assms by (rule m_6_2_P_additive)

end

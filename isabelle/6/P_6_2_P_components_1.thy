theory P_6_2_P_components_1
  imports Frontier_6_007
begin

text \<open>命題（\<open>P\<close>の各成分の非複項性） — each component of \<open>P M\<close> is non-multi, and
  \<open>M\<close> is multi iff \<open>Lng (P M) > 1\<close>.\<close>

text \<open>m: 命題（\<open>P\<close>の各成分の非複項性） (1) — discharges @{text p_6_2_P_components_1}.\<close>

lemma m_6_2_P_components_1:
  assumes "M \<in> T_PS"
  shows "\<forall>M' \<in> set (P M). zeroT M' \<or> monoT M'"
proof -
  have "M \<in> T_PS \<longrightarrow> (\<forall>M' \<in> set (P M). zeroT M' \<or> monoT M')"
  proof (induction M rule: P.induct)
    case (1 M)
    show ?case
    proof (rule impI)
      assume MT: "M \<in> T_PS"
    show "\<forall>M' \<in> set (P M). zeroT M' \<or> monoT M'"
    proof (cases "multiT M \<and> 1 < Lng M")
      case False
      hence PM: "P M = [M]" by (subst P.simps) simp
      have "zeroT M \<or> monoT M"
      proof (cases "multiT M")
        case True
        \<comment> \<open>\<open>multiT M\<close> with \<open>M \<in> T_PS\<close> forces \<open>1 < Lng M\<close>, contradicting the base case.\<close>
        have "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT True])
        with False True show ?thesis by simp
      next
        case False
        thus ?thesis by (simp add: multiT_def)
      qed
      thus ?thesis using PM by simp
    next
      case True
      hence multi: "multiT M" and L: "1 < Lng M" by simp_all
      have PM: "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
        using True by (subst P.simps) simp
      have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1 \<and> leR M 0 (Pcut M) (Lng M - 1)"
        by (rule Pcut_le[OF L])
      hence c0: "0 < Pcut M" and c1: "Pcut M \<le> Lng M - 1"
        and cle: "leR M 0 (Pcut M) (Lng M - 1)" by simp_all
      have cltL: "Pcut M < Lng M" using c1 L by simp
      \<comment> \<open>The prefix \<open>take (Pcut M) M\<close> is non-empty, hence in \<open>T_PS\<close>; apply the IH.\<close>
      have pre_TPS: "take (Pcut M) M \<in> T_PS"
      proof -
        have "Lng (take (Pcut M) M) = Pcut M" using cltL by simp
        hence "take (Pcut M) M \<noteq> []" using c0 by auto
        thus ?thesis by (simp add: T_PS_def)
      qed
      have IH: "\<forall>M' \<in> set (P (take (Pcut M) M)). zeroT M' \<or> monoT M'"
        using "1.IH"[OF True] pre_TPS by blast
      have last_nonmulti: "zeroT (drop (Pcut M) M) \<or> monoT (drop (Pcut M) M)"
      proof (cases "Pcut M < Lng M - 1")
        case True
        have "monoT (seg M (Pcut M) (Lng M - 1))"
          by (rule m_6_2_mono_ancestor_slice[OF MT True cle])
        hence "monoT (drop (Pcut M) M)" unfolding drop_eq_seg[OF cltL] .
        thus ?thesis by simp
      next
        case False
        with c1 have eq: "Pcut M = Lng M - 1" by simp
        let ?M' = "drop (Pcut M) M"
        have len1: "Lng ?M' = 1" using eq cltL by simp
        show ?thesis
        proof (cases "entry ?M' 1 0 = 0")
          case True
          thus ?thesis using len1 by (simp add: zeroT_def)
        next
          case False
          have nz: "\<not> zeroT ?M'" using False by (simp add: zeroT_def)
          have "leR ?M' 0 0 (Lng ?M' - 1)"
            using len1 by (simp add: leR_def le0_def)
          thus ?thesis using nz by (simp add: monoT_def)
        qed
      qed
      have setPM: "set (P M) = set (P (take (Pcut M) M)) \<union> {drop (Pcut M) M}"
        by (subst PM) (simp del: P.simps)
      show ?thesis unfolding setPM using IH last_nonmulti by blast
    qed
    qed
  qed
  thus ?thesis using assms by blast
qed


lemma p_6_2_P_components_1:
  assumes "M \<in> T_PS"
  shows "\<forall>M' \<in> set (P M). zeroT M' \<or> monoT M'"
  using assms by (rule m_6_2_P_components_1)

end

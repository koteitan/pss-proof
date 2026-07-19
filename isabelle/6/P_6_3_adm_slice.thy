theory P_6_3_adm_slice
  imports Frontier_6_008
begin

subsection \<open>§6.3 許容性\<close>

text \<open>命題（許容性の切片への遺伝性） — admissibility transfers to slices.\<close>

text \<open>m: 命題（許容性の切片への遺伝性） — discharges @{text p_6_3_adm_slice}.\<close>

lemma m_6_3_adm_slice:
  assumes "M \<in> T_PS" "j0' \<le> j0" "j0 \<le> j1'" "j1' \<le> Lng M - 1"
  shows "(adm M j0 \<or> j0' = j0 \<or> j0 = j1') = adm (seg M j0' j1') (j0 - j0')"
proof -
  let ?N = "seg M j0' j1'"
  have LM: "Lng M > 0" using assms(1) by (cases M) (auto simp: T_PS_def)
  have j1LM: "j1' < Lng M" using assms(4) LM by linarith
  have LN: "Lng ?N = Suc j1' - j0'" by simp
  show ?thesis
  proof (cases "j0' = j0 \<or> j0 = j1'")
    case True
    \<comment> \<open>Boundary cases: \<open>j0-j0'\<close> is \<open>0\<close> or \<open>Lng N - 1\<close>, so \<open>j0-j0'\<close> is \<open>N\<close>-admissible.\<close>
    have lhs: "adm M j0 \<or> j0' = j0 \<or> j0 = j1'" using True by blast
    have "adm ?N (j0 - j0')"
    proof -
      have "\<not> nadm ?N (j0 - j0')"
      proof
        assume nd: "nadm ?N (j0 - j0')"
        have notgt: "\<not> (j0 - j0' > Lng ?N)" using assms(2,3) LN by simp
        with nd have nx2: "nextR ?N 1 (j0 - j0') (j0 - j0' + 1)"
          by (simp add: nadm_def)
        from True show False
        proof
          assume "j0' = j0"
          hence "j0 - j0' = 0" by simp
          with nd notgt have "nextR ?N 1 0 (0 - 1) \<and> nextR ?N 1 0 (0 + 1)"
            by (simp add: nadm_def)
          \<comment> \<open>\<open>nextR ?N 1 0 (0-1)\<close> needs \<open>0 < 0\<close>; impossible.\<close>
          hence "nextrel1 ?N 0 0" by (simp add: nextR_def)
          thus False by (simp add: nextrel1_def)
        next
          assume e: "j0 = j1'"
          hence jeq: "j0 - j0' = Lng ?N - 1" using LN assms(2,3) by simp
          have "j0 - j0' + 1 < Lng ?N" using nx2 by (simp add: nextR_def nextrel1_def)
          thus False using jeq LN assms(2,3) e by simp
        qed
      qed
      thus ?thesis by (simp add: adm_def)
    qed
    thus ?thesis using lhs by blast
  next
    case False
    hence ne: "j0' \<noteq> j0" "j0 \<noteq> j1'" by auto
    hence j0'j0: "j0' < j0" and j0j1: "j0 < j1'" using assms(2,3) by auto
    have lhs_eq: "(adm M j0 \<or> j0' = j0 \<or> j0 = j1') = adm M j0" using ne by blast
    \<comment> \<open>Strict interior: reduce to the row-1 \<open>nextR\<close> correspondence.\<close>
    have notgtM: "\<not> (j0 > Lng M)" using j0j1 j1LM by simp
    have notgtN: "\<not> (j0 - j0' > Lng ?N)" using assms(2,3) LN by simp
    \<comment> \<open>indices of the two relevant relations are in range of \<open>N\<close>.\<close>
    have b1: "j0 - j0' - 1 < Lng ?N" using j0'j0 j0j1 LN by simp
    have b2: "j0 - j0' < Lng ?N" using j0j1 LN assms(2) by simp
    have b3: "j0 - j0' + 1 < Lng ?N" using j0j1 LN assms(2) by simp
    have sh1: "j0' + (j0 - j0' - 1) = j0 - 1" using j0'j0 by simp
    have sh2: "j0' + (j0 - j0') = j0" using j0'j0 by simp
    have sh3: "j0' + (j0 - j0' + 1) = j0 + 1" using j0'j0 by simp
    have c1: "nextR ?N 1 (j0 - j0' - 1) (j0 - j0') \<longleftrightarrow> nextR M 1 (j0 - 1) j0"
      using adm_nextR1_seg[OF j1LM b1 b2] sh1 sh2 by simp
    have c2: "nextR ?N 1 (j0 - j0') (j0 - j0' + 1) \<longleftrightarrow> nextR M 1 j0 (j0 + 1)"
      using adm_nextR1_seg[OF j1LM b2 b3] sh2 sh3 by simp
    have "nadm M j0 \<longleftrightarrow> nadm ?N (j0 - j0')"
      using notgtM notgtN c1 c2 by (simp add: nadm_def)
    hence "adm M j0 \<longleftrightarrow> adm ?N (j0 - j0')" by (simp add: adm_def)
    thus ?thesis using lhs_eq by simp
  qed
qed

lemma p_6_3_adm_slice:
  assumes "M \<in> T_PS" "j0' \<le> j0" "j0 \<le> j1'" "j1' \<le> Lng M - 1"
  shows "(adm M j0 \<or> j0' = j0 \<or> j0 = j1') = adm (seg M j0' j1') (j0 - j0')"
  using assms by (rule m_6_3_adm_slice)

end

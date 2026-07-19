theory P_6_3_admof_slice
  imports Frontier_6_009
begin

text \<open>命題（許容化の切片への遺伝性） — admissibilization transfers to slices.\<close>

text \<open>m: 命題（許容化の切片への遺伝性） — discharges @{text p_6_3_admof_slice}.\<close>

lemma m_6_3_admof_slice:
  assumes "M \<in> T_PS" "j0' \<le> Adm M j0" "j0 < j1'" "j1' \<le> Lng M - 1"
  shows "Adm (seg M j0' j1') (j0 - j0') = Adm M j0 - j0'"
proof -
  let ?N = "seg M j0' j1'"
  let ?am = "Adm M j0"
  let ?aN = "Adm ?N (j0 - j0')"
  have LM: "Lng M > 0" using assms(1) by (cases M) (auto simp: T_PS_def)
  have j1LM: "j1' < Lng M" using assms(4) LM by linarith
  have amle: "?am \<le> j0" by (rule adm_Adm_le)
  have amadm: "adm M ?am" by (rule adm_Adm_adm)
  have j0'am: "j0' \<le> ?am" using assms(2) .
  have j0'j0: "j0' \<le> j0" using j0'am amle by simp
  \<comment> \<open>\<open>?am\<close> is \<open>M\<close>-admissible and \<open>j0' \<le> ?am \<le> j0 < j1'\<close>, so \<open>?am - j0'\<close> is
      \<open>?N\<close>-admissible by the slice lemma.\<close>
  have amN: "adm ?N (?am - j0')"
  proof -
    have "(adm M ?am \<or> j0' = ?am \<or> ?am = j1') = adm ?N (?am - j0')"
      by (rule m_6_3_adm_slice[OF assms(1) j0'am _ assms(4)]) (use amle assms(3) in simp)
    thus ?thesis using amadm by simp
  qed
  have amj1: "?am - j0' \<le> j0 - j0'" using amle by simp
  \<comment> \<open>Lower bound: \<open>?aN \<ge> ?am - j0'\<close> by maximality of \<open>?aN\<close>.\<close>
  have ge: "?am - j0' \<le> ?aN" by (rule adm_Adm_max[OF amN amj1])
  \<comment> \<open>Upper bound.  First, \<open>?aN \<le> j0 - j0'\<close> and \<open>?aN\<close> is \<open>?N\<close>-admissible.\<close>
  have aNle: "?aN \<le> j0 - j0'" by (rule adm_Adm_le)
  have aNadm: "adm ?N ?aN" by (rule adm_Adm_adm)
  \<comment> \<open>\<open>?aN + j0'\<close> is \<open>M\<close>-admissible or hits a boundary, hence \<open>\<le> ?am\<close>.\<close>
  have le: "?aN \<le> ?am - j0'"
  proof (rule ccontr)
    assume "\<not> ?aN \<le> ?am - j0'"
    hence gt: "?am - j0' < ?aN" by simp
    have aNj0: "?aN + j0' \<le> j0" using aNle j0'j0 by simp
    \<comment> \<open>Convert \<open>?N\<close>-admissibility of \<open>?aN\<close> back to \<open>M\<close> at index \<open>?aN + j0'\<close>.\<close>
    have eq: "(adm M (?aN + j0') \<or> j0' = ?aN + j0' \<or> ?aN + j0' = j1')
              = adm ?N ((?aN + j0') - j0')"
      by (rule m_6_3_adm_slice[OF assms(1) _ _ assms(4)])
         (use aNj0 assms(3) in simp_all)
    have "(?aN + j0') - j0' = ?aN" by simp
    with eq aNadm have disj: "adm M (?aN + j0') \<or> j0' = ?aN + j0' \<or> ?aN + j0' = j1'"
      by simp
    \<comment> \<open>\<open>j0' = ?aN + j0'\<close> means \<open>?aN = 0 \<le> ?am - j0'\<close>, contradicting \<open>gt\<close>;
        \<open>?aN + j0' = j1' > j0 \<ge> ?aN + j0'\<close> is impossible; so \<open>?aN + j0'\<close> is
        \<open>M\<close>-admissible.\<close>
    have admM: "adm M (?aN + j0')"
    proof -
      have "j0' \<noteq> ?aN + j0'" using gt by auto
      moreover have "?aN + j0' \<noteq> j1'" using aNj0 assms(3) by simp
      ultimately show ?thesis using disj by blast
    qed
    \<comment> \<open>By maximality of \<open>?am\<close>, \<open>?aN + j0' \<le> ?am\<close>, i.e. \<open>?aN \<le> ?am - j0'\<close>.\<close>
    have "?aN + j0' \<le> ?am" by (rule adm_Adm_max[OF admM aNj0])
    hence "?aN \<le> ?am - j0'" using j0'am by simp
    thus False using gt by simp
  qed
  show ?thesis using ge le by simp
qed

lemma p_6_3_admof_slice:
  assumes "M \<in> T_PS" "j0' \<le> Adm M j0" "j0 < j1'" "j1' \<le> Lng M - 1"
  shows "Adm (seg M j0' j1') (j0 - j0') = Adm M j0 - j0'"
  using assms by (rule m_6_3_admof_slice)

end

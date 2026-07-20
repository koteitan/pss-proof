theory P_6_3_marked_slice
  imports P_6_3_admof_slice
begin

text \<open>命題（基点の切片への遺伝性） — a marked pair sequence restricts to a marked slice.\<close>

text \<open>m: 命題（基点の切片への遺伝性） — discharges @{text p_6_3_marked_slice}.\<close>

lemma m_6_3_marked_slice:
  assumes "(M, m) \<in> Marked" "j0' \<le> m" "m \<le> j1'" "j1' \<le> Lng M - 1"
  shows "(seg M j0' j1', m - j0') \<in> Marked"
proof -
  let ?N = "seg M j0' j1'"
  have MT: "M \<in> T_PS" and admM: "adm M m" and leM: "leR M 0 m (Lng M - 1)"
    using assms(1) by (auto simp: Marked_def)
  have LM: "Lng M > 0" using MT by (cases M) (auto simp: T_PS_def)
  have j1LM: "j1' < Lng M" using assms(4) LM by linarith
  have j0j1: "j0' \<le> j1'" using assms(2,3) by simp
  \<comment> \<open>\<open>?N\<close> is non-empty, hence in \<open>T_PS\<close>.\<close>
  have LN: "Lng ?N = Suc j1' - j0'" by simp
  have LNpos: "Lng ?N > 0" using j0j1 LN by simp
  have NT: "?N \<in> T_PS" using LNpos by (cases ?N) (auto simp: T_PS_def)
  \<comment> \<open>\<open>m - j0'\<close> is \<open>?N\<close>-admissible by the slice lemma.\<close>
  have admN: "adm ?N (m - j0')"
  proof -
    have "(adm M m \<or> j0' = m \<or> m = j1') = adm ?N (m - j0')"
      by (rule m_6_3_adm_slice[OF MT assms(2,3,4)])
    thus ?thesis using admM by blast
  qed
  \<comment> \<open>\<open>(0, m - j0') \<le>\<^sub>?N (0, Lng ?N - 1)\<close> via the row-0 \<open>le0\<close> slice correspondence.\<close>
  have leN: "leR ?N 0 (m - j0') (Lng ?N - 1)"
  proof -
    have mlast: "leR M 0 m (Lng M - 1)" by (rule leM)
    \<comment> \<open>Bring the row-0 ancestry down to the slice's last index \<open>j1'\<close>.\<close>
    have mj1: "leR M 0 m j1'"
      by (rule m_5_1_ancestor_tree_1[OF MT mlast assms(3)]) (use assms(4) LM in linarith)
    have le0Mj1: "le0 M (j0' + (m - j0')) (j0' + (j1' - j0'))"
      using mj1 assms(2,3) j0j1 by (simp add: leR_def)
    have "le0 ?N (m - j0') (j1' - j0')"
      using adm_le0_seg[OF j1LM _ _ j0j1] assms(2,3) j0j1 le0Mj1 by simp
    moreover have "Lng ?N - 1 = j1' - j0'" using LN by simp
    ultimately show ?thesis by (simp add: leR_def)
  qed
  show ?thesis using NT admN leN by (simp add: Marked_def)
qed


lemma p_6_3_marked_slice:
  assumes "(M, m) \<in> Marked" "j0' \<le> m" "m \<le> j1'" "j1' \<le> Lng M - 1"
  shows "(seg M j0' j1', m - j0') \<in> Marked"
  using assms by (rule m_6_3_marked_slice)

end

theory P_7_4_Adm_nextAdm
  imports Frontier_7_001
begin

text \<open>
  m: 命題（\<open>Adm\<^sub>M\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） — discharges
  @{text p_7_4_Adm_nextAdm} (§7.4).
\<close>

lemma m_7_4_Adm_nextAdm:
  assumes "M \<in> T_PS" "hasParent M i (Lng M - 1)"
  shows "nextAdm M i (Adm M (parent M i (Lng M - 1))) (Lng M - 1)"
proof -
  let ?j1 = "Lng M - 1"
  let ?j0 = "parent M i ?j1"
  let ?a = "Adm M ?j0"
  \<comment> \<open>The unique row-\<open>i\<close> parent of \<open>j1\<close> (\<open>i = 0\<close> uses row 0, any other \<open>i\<close> row 1).\<close>
  from assms(2) have par: "nextR M i ?j0 ?j1"
    unfolding hasParent_def parent_def by (rule theI')
  have j0lt: "?j0 < ?j1"
    using par unfolding nextR_def nextrel0_def nextrel1_def by (auto split: if_splits)
  have j0le1: "?j0 \<le> ?j1" using j0lt by simp
  have L: "Lng M > 1" using j0lt by linarith
  have j1L: "?j1 < Lng M" using L by linarith
  \<comment> \<open>(2) \<open>a < j1\<close>.\<close>
  have ale: "?a \<le> ?j0" by (rule adm_Adm_le)
  have alt: "?a < ?j1" using ale j0lt by simp
  \<comment> \<open>(3) \<open>adm M a\<close>.\<close>
  have aadm: "adm M ?a" by (rule adm_Adm_adm)
  \<comment> \<open>(1) \<open>leR M i a j1\<close>: row-1 ancestry of \<open>a\<close> below \<open>j0\<close>, then step \<open>j0 <\<^sup>Next j1\<close>.\<close>
  have j0le: "?j0 \<le> Lng M - 1" using j0lt by simp
  have a_anc_j0_1: "leR M 1 ?a ?j0" by (rule adm_row1_ancestry[OF assms(1) j0le])
  have step_j0_j1: "leR M i ?j0 ?j1" by (rule nextR_imp_leR[OF par])
  have leR_i_a_j1: "leR M i ?a ?j1"
  proof (cases "i = 0")
    case True
    have "leR M 0 ?a ?j0" by (rule m_le1_imp_le0[OF a_anc_j0_1])
    moreover have "leR M 0 ?j0 ?j1" using step_j0_j1 True by simp
    ultimately have "leR M 0 ?a ?j1" using le0_trans by (simp add: leR_def)
    thus ?thesis using True by simp
  next
    case False
    have a_anc_j0_i: "leR M i ?a ?j0" using a_anc_j0_1 False by (simp add: leR_def)
    show ?thesis by (rule leR_trans[OF a_anc_j0_i step_j0_j1])
  qed
  \<comment> \<open>(4) intermediate indices are non-ancestors or non-admissible.\<close>
  have mid: "\<forall>j. ?a < j \<and> j < ?j1 \<longrightarrow> \<not> leR M i j ?j1 \<or> \<not> adm M j"
  proof (intro allI impI)
    fix j assume jb: "?a < j \<and> j < ?j1"
    show "\<not> leR M i j ?j1 \<or> \<not> adm M j"
    proof (rule ccontr)
      assume "\<not> (\<not> leR M i j ?j1 \<or> \<not> adm M j)"
      hence anc: "leR M i j ?j1" and jadm: "adm M j" by auto
      have "j \<le> ?j0" by (rule parent_max[OF assms(2) par anc]) (use jb in simp)
      hence "j \<le> ?a" using adm_Adm_max[OF jadm] by simp
      with jb show False by simp
    qed
  qed
  show ?thesis
    unfolding nextAdm_def using leR_i_a_j1 alt aadm mid by blast
qed


subsection \<open>§7.4 許容的親子関係\<close>

text \<open>命題（\<open>Adm\<^sub>M\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） — when \<open>j\<^sub>1 = Lng M - 1\<close> has a
  unique row-\<open>i\<close> parent \<open>j\<^sub>0\<close>, its admissibilization \<open>Adm\<^sub>M(j\<^sub>0)\<close> is the
  admissible parent of \<open>j\<^sub>1\<close>.  (This §7.4 proposition is \<open>Trans\<close>-free; the
  remaining §7.3 / §7.4 statements await the \<open>Trans\<close> / \<open>Mark\<close> definition.)\<close>

lemma p_7_4_Adm_nextAdm:
  assumes "M \<in> T_PS" "hasParent M i (Lng M - 1)"
  shows "nextAdm M i (Adm M (parent M i (Lng M - 1))) (Lng M - 1)"
  using assms by (rule m_7_4_Adm_nextAdm)

end

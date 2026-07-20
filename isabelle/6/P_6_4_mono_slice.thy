theory P_6_4_mono_slice
  imports Frontier_6_017
begin

text \<open>系（単項性の切片への遺伝性） — §6.4 version (via Joints).\<close>

text \<open>m: 系（単項性の切片への遺伝性, §6.4 version） — discharges
  @{text p_6_4_mono_slice}.\<close>

lemma m_6_4_mono_slice:
  assumes M: "M \<in> PT_PS" and lt: "j0' < j1'" and j1L: "j1' \<le> Lng M - 1"
    and j0le: "j0' \<le> Joints M ! (Lng (Br M) - 1)"
  shows "monoT (seg M j0' j1')"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have LM: "Lng M > 0" using MT by (cases M) (auto simp: T_PS_def)
  have j1lt: "j1' < Lng M" using j1L LM by linarith
  show ?thesis
  proof (cases "Br M = []")
    case True
    \<comment> \<open>Degenerate trunk-only case: \<open>TrMax M = Lng M - 1\<close>, so the whole sequence is
        the trunk and \<open>leR M 0 0 (Lng M - 1)\<close> already holds; the slice is mono.\<close>
    have trmax: "TrMax M = Lng M - 1"
    proof (rule ccontr)
      assume "TrMax M \<noteq> Lng M - 1"
      hence "Br M = P (seg M (TrMax M + 1) (Lng M - 1))" by (simp add: Br_def)
      moreover have "P (seg M (TrMax M + 1) (Lng M - 1)) \<noteq> []" by (rule P_nonempty)
      ultimately show False using True by simp
    qed
    have le: "leR M 0 j0' j1'"
    proof (rule m_5_1_parent_exists_3[OF MT lt j1lt])
      fix kk assume k: "j0' < kk" "kk \<le> j1'"
      hence kL: "kk \<le> Lng M - 1" using j1L by simp
      hence kTr: "kk \<le> TrMax M" using trmax by simp
      have "leR M 0 j0' kk" by (rule trunk_le0[OF MT less_imp_le_nat[OF k(1)] kTr])
      thus "entry M 0 j0' < entry M 0 kk"
        by (rule m_5_1_ancestor_basic_1[OF MT k(1) order.refl])
    qed
    show ?thesis by (rule m_6_2_mono_ancestor_slice[OF MT lt le])
  next
    case False
    have le: "leR M 0 j0' j1'"
    proof (rule m_5_1_parent_exists_3[OF MT lt j1lt])
      fix kk assume k: "j0' < kk" "kk \<le> j1'"
      hence kL: "kk \<le> Lng M - 1" using j1L by simp
      have "leR M 0 j0' kk"
        by (rule slice_le0_to_index[OF M False j0le k(1) kL])
      thus "entry M 0 j0' < entry M 0 kk"
        by (rule m_5_1_ancestor_basic_1[OF MT k(1) order.refl])
    qed
    show ?thesis by (rule m_6_2_mono_ancestor_slice[OF MT lt le])
  qed
qed

lemma p_6_4_mono_slice:
  assumes "M \<in> PT_PS" "j0' < j1'" "j1' \<le> Lng M - 1"
    "j0' \<le> Joints M ! (Lng (Br M) - 1)"
  shows "monoT (seg M j0' j1')"
  using assms by (rule m_6_4_mono_slice)

end

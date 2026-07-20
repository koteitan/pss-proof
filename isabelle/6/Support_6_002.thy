theory Support_6_002
  imports Frontier_6_016
begin

text \<open>m: 系（\<open>FirstNodes\<close>と\<open>Joints\<close>の単調性）の主要部 (parts (1),(2),(3)) —
  \<open>FirstNodes\<close> increasing, \<open>Joints\<close> decreasing (non-strict), row-0 entries at
  \<open>FirstNodes\<close> decreasing.  Part (2) here is the non-strict form, which is all
  that \<open>m_6_4_mono_slice\<close> needs.\<close>

lemma m_6_4_FirstNodes_Joints_mono_aux:
  assumes M: "M \<in> PT_PS" and lt: "J0' < J1'" and J1: "J1' < Lng (Br M)"
  shows "FirstNodes M ! J0' \<le> FirstNodes M ! J1'
       \<and> Joints M ! J0' \<ge> Joints M ! J1'
       \<and> entry M 0 (FirstNodes M ! J0') \<ge> entry M 0 (FirstNodes M ! J1')"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have J0L: "J0' < length (Br M)" using lt J1 by simp
  have J1L: "J1' < length (Br M)" using J1 by simp
  have J0le: "J0' \<le> J1'" using lt by simp
  \<comment> \<open>(1) FirstNodes increasing\<close>
  have idxmono: "IdxSum (Br M) ! J0' \<le> IdxSum (Br M) ! J1'"
    by (rule idxsum_mono[OF J0le less_imp_le_nat[OF J1L]])
  have fn0: "FirstNodes M ! J0' = TrMax M + 1 + IdxSum (Br M) ! J0'"
    by (rule FirstNodes_nth[OF J0L])
  have fn1: "FirstNodes M ! J1' = TrMax M + 1 + IdxSum (Br M) ! J1'"
    by (rule FirstNodes_nth[OF J1L])
  have part1: "FirstNodes M ! J0' \<le> FirstNodes M ! J1'"
    using fn0 fn1 idxmono by simp
  \<comment> \<open>(3) row-0 entries at FirstNodes decreasing, via \<open>m_6_4_P_leftend_mono\<close>\<close>
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with J1 show False by simp
  qed
  with tb have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have NLpos: "Lng ?N > 0" using trlt by simp
  have Nne: "?N \<noteq> []" using NLpos length_greater_0_conv by blast
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have J1Q: "J1' \<le> Lng (P ?N) - 1" using J1L brQ by (cases "P ?N") auto
  have leftend: "entry ((P ?N) ! J0') 0 0 \<ge> entry ((P ?N) ! J1') 0 0"
    by (rule m_6_4_P_leftend_mono[OF NT J0le J1Q])
  have ec0: "entry M 0 (FirstNodes M ! J0') = entry (Br M ! J0') 0 0"
    by (rule entry_FirstNodes_eq_component[OF M J0L])
  have ec1: "entry M 0 (FirstNodes M ! J1') = entry (Br M ! J1') 0 0"
    by (rule entry_FirstNodes_eq_component[OF M J1L])
  have part3: "entry M 0 (FirstNodes M ! J0') \<ge> entry M 0 (FirstNodes M ! J1')"
    using ec0 ec1 leftend brQ by simp
  \<comment> \<open>(2) Joints decreasing (non-strict): \<open>a1\<close> is a row-0 ancestor of \<open>f0\<close>,
      hence \<open>\<le> a0 = parent M 0 f0\<close>.\<close>
  let ?f0 = "FirstNodes M ! J0'"
  let ?f1 = "FirstNodes M ! J1'"
  let ?a0 = "Joints M ! J0'"
  let ?a1 = "Joints M ! J1'"
  have a0_eq: "?a0 = parent M 0 ?f0" by (rule Joints_nth[OF J0L])
  have a1_eq: "?a1 = parent M 0 ?f1" by (rule Joints_nth[OF J1L])
  \<comment> \<open>parents exist and lie in the trunk\<close>
  have tj0: "Joints M ! J0' \<le> TrMax M \<and> TrMax M < FirstNodes M ! J0'"
    by (rule m_6_4_FirstNodes_TrMax_Joints[OF M J0L])
  have tj1: "Joints M ! J1' \<le> TrMax M \<and> TrMax M < FirstNodes M ! J1'"
    by (rule m_6_4_FirstNodes_TrMax_Joints[OF M J1L])
  have a0tr: "?a0 \<le> TrMax M" and trf0: "TrMax M < ?f0" using tj0 by simp_all
  have a1tr: "?a1 \<le> TrMax M" and trf1: "TrMax M < ?f1" using tj1 by simp_all
  \<comment> \<open>get the actual \<open>nextR\<close> facts for the two parents\<close>
  have brQne: "length (P ?N) > 0" using P_nonempty by auto
  have J0Q': "J0' \<le> Lng (P ?N) - 1" using J0L brQ by (cases "P ?N") auto
  have hp0: "hasParent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J0')
           \<and> parent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J0') < TrMax M + 1"
    using m_6_4_mono_slice_next[OF M _ _ J0Q'] trlt by auto
  have hp1: "hasParent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J1')
           \<and> parent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J1') < TrMax M + 1"
    using m_6_4_mono_slice_next[OF M _ _ J1Q] trlt by auto
  have idx0: "TrMax M + 1 + IdxSum (P ?N) ! J0' = ?f0" using fn0 brQ by simp
  have idx1: "TrMax M + 1 + IdxSum (P ?N) ! J1' = ?f1" using fn1 brQ by simp
  have hpf0: "hasParent M 0 ?f0" using hp0 idx0 by simp
  have hpf1: "hasParent M 0 ?f1" using hp1 idx1 by simp
  have nx0: "nextR M 0 ?a0 ?f0"
  proof -
    have "\<exists>!j0. nextR M 0 j0 ?f0" using hpf0 by (simp add: hasParent_def)
    hence "nextR M 0 (THE j0. nextR M 0 j0 ?f0) ?f0" by (rule theI')
    thus ?thesis using a0_eq by (simp add: parent_def)
  qed
  have nx1: "nextR M 0 ?a1 ?f1"
  proof -
    have "\<exists>!j0. nextR M 0 j0 ?f1" using hpf1 by (simp add: hasParent_def)
    hence "nextR M 0 (THE j0. nextR M 0 j0 ?f1) ?f1" by (rule theI')
    thus ?thesis using a1_eq by (simp add: parent_def)
  qed
  \<comment> \<open>\<open>a1 < f1\<close>, \<open>entry M 0 a1 < entry M 0 f1\<close>\<close>
  from nx1 have a1f1: "?a1 < ?f1" and ea1: "entry M 0 ?a1 < entry M 0 ?f1"
    by (simp_all add: nextR_def nextrel0_def)
  \<comment> \<open>\<open>leR M 0 a1 f1\<close>, then by the tree, \<open>leR M 0 a1 f0\<close> (since \<open>a1 \<le> f0 \<le> f1\<close>)\<close>
  have lea1f1: "leR M 0 ?a1 ?f1"
    using nx1 a1f1 by (auto simp: nextR_def leR_def le0_def nextrel0_def)
  have a1lef0: "?a1 \<le> ?f0" using a1tr trf0 by simp
  have f0lef1: "?f0 \<le> ?f1" using part1 by simp
  have lea1f0: "leR M 0 ?a1 ?f0"
    by (rule m_5_1_ancestor_tree_1[OF MT lea1f1 a1lef0 f0lef1])
  \<comment> \<open>\<open>a1\<close> is below \<open>f0\<close> with smaller row-0 entry, so \<open>a1 \<le> parent M 0 f0 = a0\<close>\<close>
  have a1ltf0: "?a1 < ?f0" using a1tr trf0 by simp
  have ea1f0: "entry M 0 ?a1 < entry M 0 ?f0"
    by (rule m_5_1_ancestor_basic_1[OF MT a1ltf0 le_refl lea1f0])
  have part2: "?a0 \<ge> ?a1"
    using nextR0_largest_below[OF nx0 a1ltf0 ea1f0] by simp
  show ?thesis using part1 part2 part3 by blast
qed

end

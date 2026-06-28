theory pss_scratch
  imports "PSS_B.pss_wip"
begin

text \<open>LAYER c — sub-agent scratch theory.  Sub-agents add this round's in-progress
  lemmas here and build session PSS_C, which sits on top of the pre-built PSS_B heap
  (pss_wip) so only this file is processed.  When a job is verified green, the parent
  moves the proven lemmas into pss_wip (LAYER b) and rebuilds PSS_B, then resets this
  file to empty for the next round.\<close>

text \<open>§8.5 (content.md ~5165) 補題（条件(V)の下での Joints と FirstNodes と t2 の基本性質）,
  parts (1)–(2), the Trans-FREE conclusions.  This is the §8.5 specialisation of the
  §8.4 rightmost-non-admissible-direct-ancestor lemma to the host's own right end
  (\<open>m\<^sub>0 = j\<^sub>0\<close>, \<open>m\<^sub>1 = j\<^sub>1\<close>).  Route: \<open>N = seg M (Adm M j\<^sub>0) j\<^sub>1\<close> sits in the
  \<open>transJm1 (Red N) = 0\<close> (Adm-zero) regime, so the proven §8.2 Adm0 family
  (@{thm [source] m_8_2_parent_le_TrMax_Adm0}, @{thm [source] m_8_2_j1eq_Adm0},
  @{thm [source] m_8_2_j0eq_Adm0}) gives parts (1b)/(1c); \<open>Br (Red N) \<noteq> []\<close> (1a)
  comes from the row-1 trunk step (@{thm [source] TrMax_trunk_step}) transferred back
  through the slice/IncrFirst bridges and contradicting \<open>\<not> nextR M 1 (j\<^sub>1-1) j\<^sub>1\<close>;
  part (2) is the trunk-diagonal coincidence (@{thm [source] trunk_entries_offset})
  plus two RedCondA steps.\<close>

lemma m_8_5_Joints_FirstNodes_basic:
  fixes M :: pairseq
  defines "j1 \<equiv> Lng M - 1"
    and "j0 \<equiv> parent M 0 (Lng M - 1)"
  assumes "M \<in> ST_PS" "M \<in> PT_PS"
    and "nextR M 1 j0 j1"
    and "\<not> adm M j0"
    and "j0 < j1 - 1"
  shows \<comment> \<open>(1)\<close>
        "Lng (Br (Red (seg M (Adm M j0) j1))) \<ge> 1"
    and "j0 - Adm M j0
           = Joints (Red (seg M (Adm M j0) j1)) ! (Lng (Br (Red (seg M (Adm M j0) j1))) - 1)"
    and "FirstNodes (Red (seg M (Adm M j0) j1)) ! (Lng (Br (Red (seg M (Adm M j0) j1))) - 1)
           = j1 - Adm M j0"
    and \<comment> \<open>(2)\<close>
        "entry (Red (seg M (Adm M j0) j1)) 0 (j1 - Adm M j0)
           = entry (Red (seg M (Adm M j0) j1)) 1 (j1 - Adm M j0)"
proof -
  let ?mm1 = "Adm M j0"
  let ?N = "seg M ?mm1 j1"
  let ?RN = "Red ?N"
  \<comment> \<open>basic memberships\<close>
  have Mst: "M \<in> ST_PS" by (rule assms(3))
  have MP: "M \<in> PT_PS" by (rule assms(4))
  have MR: "M \<in> RT_PS" using Mst m_6_7_ST_PS_subseteq_RT_PS by blast
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have nxR1: "nextR M 1 j0 j1" by (rule assms(5))
  have nadm: "\<not> adm M j0" by (rule assms(6))
  have gap: "j0 < j1 - 1" by (rule assms(7))
  \<comment> \<open>length bounds\<close>
  have j1eqLM: "j1 = Lng M - 1" by (simp add: j1_def)
  have L1: "1 < Lng M" using gap j1eqLM by linarith
  have j1pos: "0 < j1" using gap by linarith
  have j1ltLM: "j1 < Lng M" using j1eqLM L1 by linarith
  have j1leLM1: "j1 \<le> Lng M - 1" by (simp add: j1_def)
  \<comment> \<open>\<open>j\<^sub>0\<close> is the row-0 parent of the last column\<close>
  have hp0M: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L1])
  have parj0: "nextR M 0 j0 j1"
    using hp0M unfolding hasParent_def j0_def parent_def j1_def by (rule theI')
  have j0ltj1: "j0 < j1" and lej0j1: "leR M 0 j0 j1"
    using poper_nextR_imp_le0[OF parj0] by simp_all
  have j0leLM1: "j0 \<le> Lng M - 1" using j0ltj1 j1leLM1 by linarith
  \<comment> \<open>\<open>?mm1 = Adm M j\<^sub>0 < j\<^sub>0\<close>\<close>
  have mm1ltj0: "?mm1 < j0" by (rule nadm_Adm_lt[OF nadm])
  have admmm1: "adm M ?mm1" by (rule adm_Adm_adm)
  have mm1lej0: "?mm1 \<le> j0" using mm1ltj0 by linarith
  have mm1ltj1: "?mm1 < j1" using mm1ltj0 j0ltj1 by linarith
  have mm1lej1: "?mm1 \<le> j1" using mm1ltj1 by linarith
  \<comment> \<open>\<open>leR M 0 ?mm1 j\<^sub>1\<close> and \<open>(M,?mm1) \<in> Marked\<close>\<close>
  have le1a: "leR M 1 ?mm1 j0" using adm_row1_ancestry[OF MT j0leLM1] by simp
  have le0a: "leR M 0 ?mm1 j0" by (rule m_le1_imp_le0[OF le1a])
  have le0mm1j0: "le0 M ?mm1 j0" using le0a by (simp add: leR_def)
  have le0j0j1: "le0 M j0 j1" using lej0j1 by (simp add: leR_def)
  have le0mm1j1: "le0 M ?mm1 j1" by (rule le0_trans[OF le0mm1j0 le0j0j1])
  have leM: "leR M 0 ?mm1 j1" using le0mm1j1 by (simp add: leR_def)
  have leM2: "leR M 0 ?mm1 (Lng M - 1)" using leM j1eqLM by simp
  have marked: "(M, ?mm1) \<in> Marked" using MT admmm1 leM j1eqLM by (simp add: Marked_def)
  \<comment> \<open>premises of the shift lemmas (\<open>m = ?mm1\<close>, slice up to the last column)\<close>
  have mint: "?mm1 < Lng M - 2" using mm1ltj0 j0ltj1 gap j1eqLM by linarith
  have anc0: "?mm1 \<le> parent M 0 (Lng M - 1)" using mm1lej0 j0_def by simp
  have j0lt: "parent M 0 (Lng M - 1) < Lng M - 1" using j0ltj1 j1eqLM j0_def by simp
  \<comment> \<open>\<open>?RN\<close> facts: in RT/PT/DT, length preserved, IncrFirst-bridge\<close>
  have segT: "?N \<in> T_PS" using slice_Red_in_RT_PS[OF MR mm1ltj1 j1leLM1 leM] by simp
  have NR: "?RN \<in> RT_PS" using slice_Red_in_RT_PS[OF MR mm1ltj1 j1leLM1 leM] by simp
  have NT: "?RN \<in> T_PS" using NR by (simp add: RT_PS_def)
  have ND: "?RN \<in> DT_PS" by (rule m_8_2_standard_slice_Red_strongmono[OF Mst mm1ltj1 j1leLM1 leM])
  have monoRN: "monoT ?RN" using ND by (simp add: DT_PS_def)
  have NP: "?RN \<in> PT_PS" using NT monoRN by (simp add: PT_PS_def)
  have LRN: "Lng ?RN = Lng ?N" by (rule m_6_5_Lng_Red[OF segT])
  have LNval: "Lng ?N = Suc j1 - ?mm1" by simp
  have LRNm1: "Lng ?RN - 1 = j1 - ?mm1" using LRN LNval mm1lej1 by simp
  have segeq: "?N = (IncrFirst ^^ (entry M 0 ?mm1 - entry M 1 ?mm1)) ?RN"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR mm1ltj1 j1leLM1 leM] by simp
  \<comment> \<open>the slice/IncrFirst \<open>nextR\<close> bridge: \<open>nextR ?RN i p q = nextR M i (?mm1+p) (?mm1+q)\<close>\<close>
  have bridge: "\<And>i p q. i \<le> (1::nat) \<Longrightarrow> p < Lng ?N \<Longrightarrow> q < Lng ?N
                 \<Longrightarrow> nextR ?RN i p q = nextR M i (?mm1 + p) (?mm1 + q)"
  proof -
    fix i p q :: nat assume i: "i \<le> 1" and p: "p < Lng ?N" and q: "q < Lng ?N"
    have "nextR ?RN i p q
            = nextR ((IncrFirst ^^ (entry M 0 ?mm1 - entry M 1 ?mm1)) ?RN) i p q"
      by (simp add: nextR_funpow_IncrFirst_eq)
    also have "\<dots> = nextR ?N i p q" using segeq by simp
    also have "\<dots> = nextR M i (?mm1 + p) (?mm1 + q)"
      by (rule rcpb_nextR_seg[OF j1ltLM i p q])
    finally show "nextR ?RN i p q = nextR M i (?mm1 + p) (?mm1 + q)" .
  qed
  \<comment> \<open>shift identities: \<open>transJ0 (Red N) = j\<^sub>0 - ?mm1\<close>, \<open>transJm1 (Red N) = 0\<close>\<close>
  have RNexp: "?RN = Red (seg M ?mm1 (Lng M - 1))" by (simp add: j1_def)
  have tj0M: "transJ0 M = j0" by (simp add: transJ0_def transJ1_def j0_def)
  have tjm1M: "transJm1 M = ?mm1" by (simp add: transJm1_def transJ0_def transJ1_def j0_def)
  have tj0RN: "transJ0 ?RN = j0 - ?mm1"
    unfolding RNexp using repr_transJ0_shift[OF MR mint leM2 hp0M anc0] tj0M by simp
  have Adm0RN: "transJm1 ?RN = 0"
    unfolding RNexp using repr_transJm1_shift[OF marked MR mint leM2 hp0M anc0 j0lt] tjm1M by simp
  \<comment> \<open>parent of the last column in \<open>?RN\<close> is \<open>j\<^sub>0 - ?mm1\<close>\<close>
  have parRNlast: "parent ?RN 0 (Lng ?RN - 1) = j0 - ?mm1"
    using tj0RN by (simp add: transJ0_def transJ1_def)
  \<comment> \<open>(Y) \<open>j\<^sub>0 - ?mm1 \<le> TrMax (Red N)\<close>\<close>
  have jpTr: "j0 - ?mm1 \<le> TrMax ?RN"
    using m_8_2_parent_le_TrMax_Adm0[OF NR NP Adm0RN] parRNlast by simp
  have jppos: "0 < j0 - ?mm1" using mm1ltj0 by linarith
  have TrMaxpos: "0 < TrMax ?RN" using jpTr jppos by linarith
  \<comment> \<open>row-1 / row-0 next relations on \<open>?RN\<close> from the host (bridge)\<close>
  have plt0: "j0 - ?mm1 < Lng ?N" using LNval j0ltj1 mm1lej1 by linarith
  have qlt: "j1 - ?mm1 < Lng ?N" using LNval mm1lej1 by linarith
  have add_j0: "?mm1 + (j0 - ?mm1) = j0" using mm1lej0 by simp
  have add_j1: "?mm1 + (j1 - ?mm1) = j1" using mm1lej1 by simp
  have B0: "nextR ?RN 0 (j0 - ?mm1) (j1 - ?mm1)"
    using bridge[of 0 "j0 - ?mm1" "j1 - ?mm1"] plt0 qlt parj0 add_j0 add_j1 by simp
  have B1: "nextR ?RN 1 (j0 - ?mm1) (j1 - ?mm1)"
    using bridge[of 1 "j0 - ?mm1" "j1 - ?mm1"] plt0 qlt nxR1 add_j0 add_j1 by simp
  \<comment> \<open>\<open>\<not> nextR M 1 (j\<^sub>1-1) j\<^sub>1\<close>: row-1 parent of \<open>j\<^sub>1\<close> is unique \<open>= j\<^sub>0 \<noteq> j\<^sub>1-1\<close>\<close>
  have notnext: "\<not> nextR M 1 (j1 - 1) j1"
  proof
    assume H: "nextR M 1 (j1 - 1) j1"
    have "j1 - 1 = j0" by (rule nextR1_unique[OF H nxR1])
    thus False using gap by linarith
  qed
  \<comment> \<open>(1a) \<open>Br (Red N) \<noteq> []\<close>, i.e. \<open>TrMax (Red N) < Lng (Red N) - 1\<close>\<close>
  have Brne: "Br ?RN \<noteq> []"
  proof
    assume Bemp: "Br ?RN = []"
    have trmaxeq: "TrMax ?RN = Lng ?RN - 1"
    proof (rule ccontr)
      assume ne: "TrMax ?RN \<noteq> Lng ?RN - 1"
      hence "Br ?RN = P (seg ?RN (TrMax ?RN + 1) (Lng ?RN - 1))" by (simp add: Br_def)
      hence "Br ?RN \<noteq> []" using P_nonempty by simp
      thus False using Bemp by simp
    qed
    have RNge2: "2 \<le> Lng ?RN" using LRNm1 mm1ltj1 j0ltj1 mm1ltj0 by linarith
    have step: "nextR ?RN 1 (TrMax ?RN - 1) (TrMax ?RN)"
      using TrMax_trunk_step[OF NT, of "TrMax ?RN - 1"] TrMaxpos by simp
    have e2: "TrMax ?RN - 1 = Lng ?RN - 2" using trmaxeq by simp
    have p2: "Lng ?RN - 2 < Lng ?N" using LRN RNge2 by linarith
    have q2: "Lng ?RN - 1 < Lng ?N" using LRN RNge2 by linarith
    have add_p2: "?mm1 + (Lng ?RN - 2) = j1 - 1" using LRNm1 RNge2 mm1lej1 by linarith
    have add_q2: "?mm1 + (Lng ?RN - 1) = j1" using LRNm1 mm1lej1 by linarith
    have stepRN: "nextR ?RN 1 (Lng ?RN - 2) (Lng ?RN - 1)" using step trmaxeq e2 by simp
    have "nextR M 1 (j1 - 1) j1"
      using bridge[of 1 "Lng ?RN - 2" "Lng ?RN - 1"] p2 q2 stepRN add_p2 add_q2 by simp
    thus False using notnext by simp
  qed
  have j1gtRN: "Lng ?RN - 1 > 1" using LRNm1 mm1ltj0 j0ltj1 gap by linarith
  \<comment> \<open>(1c) \<open>FirstNodes (Red N) ! J\<^sub>1 = Lng (Red N) - 1 = j\<^sub>1 - ?mm1\<close>\<close>
  have FNlast: "FirstNodes ?RN ! (Lng (Br ?RN) - 1) = Lng ?RN - 1"
    by (rule m_8_2_j1eq_Adm0[OF NR NP Brne j1gtRN Adm0RN])
  have G3: "FirstNodes ?RN ! (Lng (Br ?RN) - 1) = j1 - ?mm1" using FNlast LRNm1 by simp
  \<comment> \<open>(1b) \<open>Joints (Red N) ! J\<^sub>1 = transJ0 (Red N) = j\<^sub>0 - ?mm1\<close>\<close>
  have Jlast: "Joints ?RN ! (Lng (Br ?RN) - 1) = transJ0 ?RN"
    by (rule m_8_2_j0eq_Adm0[OF NR NP Brne j1gtRN Adm0RN])
  have G2: "j0 - ?mm1 = Joints ?RN ! (Lng (Br ?RN) - 1)" using Jlast tj0RN by simp
  \<comment> \<open>(1a) packaged\<close>
  have G1: "1 \<le> Lng (Br ?RN)" using Brne by (cases "Br ?RN") auto
  \<comment> \<open>(2): the trunk-diagonal coincidence at \<open>j\<^sub>0-?mm1\<close> climbed by RedCondA to \<open>Lng-1\<close>\<close>
  have condAB: "RedCondA ?RN \<and> RedCondB ?RN" using m_6_6_reduced_iff_cond[OF NT] NR by simp
  have condA: "RedCondA ?RN" using condAB by simp
  have condB: "RedCondB ?RN" using condAB by simp
  have noPar00: "\<not> hasParent ?RN 0 0"
    by (auto simp: hasParent_def nextR_def nextrel0_def)
  have LRNpos: "0 < Lng ?RN" using LRN LNval mm1lej1 by simp
  have e00: "entry ?RN 0 0 = entry ?RN 1 0"
    using condB noPar00 LRNpos unfolding RedCondB_def by simp
  have off: "entry ?RN 0 (j0 - ?mm1) = entry ?RN 0 0 + (j0 - ?mm1)
           \<and> entry ?RN 1 (j0 - ?mm1) = entry ?RN 1 0 + (j0 - ?mm1)"
    by (rule trunk_entries_offset[OF NT condA jpTr])
  have coincide: "entry ?RN 0 (j0 - ?mm1) = entry ?RN 1 (j0 - ?mm1)" using off e00 by simp
  \<comment> \<open>RedCondA at the last column, both rows (parents \<open>= j\<^sub>0-?mm1\<close>)\<close>
  have B0': "nextR ?RN 0 (j0 - ?mm1) (Lng ?RN - 1)" using B0 LRNm1 by simp
  have B1': "nextR ?RN 1 (j0 - ?mm1) (Lng ?RN - 1)" using B1 LRNm1 by simp
  have hp0RN: "hasParent ?RN 0 (Lng ?RN - 1)"
    unfolding hasParent_def using B0' idxsum_parent0_unique by metis
  have hp1RN: "hasParent ?RN 1 (Lng ?RN - 1)"
    unfolding hasParent_def using B1' nextR1_unique by metis
  have par1RN: "parent ?RN 1 (Lng ?RN - 1) = j0 - ?mm1"
  proof -
    have "(THE p. nextR ?RN 1 p (Lng ?RN - 1)) = j0 - ?mm1"
      by (rule the_equality, rule B1') (rule nextR1_unique[OF _ B1'])
    thus ?thesis by (simp add: parent_def)
  qed
  have rcA0: "entry ?RN 0 (j0 - ?mm1) + 1 = entry ?RN 0 (Lng ?RN - 1)"
    using condA[unfolded RedCondA_def, rule_format, of 0 "Lng ?RN - 1"] hp0RN parRNlast by simp
  have rcA1: "entry ?RN 1 (j0 - ?mm1) + 1 = entry ?RN 1 (Lng ?RN - 1)"
    using condA[unfolded RedCondA_def, rule_format, of 1 "Lng ?RN - 1"] hp1RN par1RN by simp
  have eqlast: "entry ?RN 0 (Lng ?RN - 1) = entry ?RN 1 (Lng ?RN - 1)"
    using rcA0 rcA1 coincide by simp
  have G4: "entry ?RN 0 (j1 - ?mm1) = entry ?RN 1 (j1 - ?mm1)" using eqlast LRNm1 by simp
  \<comment> \<open>assemble\<close>
  show "Lng (Br (Red (seg M (Adm M j0) j1))) \<ge> 1" using G1 by simp
  show "j0 - Adm M j0
          = Joints (Red (seg M (Adm M j0) j1)) ! (Lng (Br (Red (seg M (Adm M j0) j1))) - 1)"
    using G2 by simp
  show "FirstNodes (Red (seg M (Adm M j0) j1)) ! (Lng (Br (Red (seg M (Adm M j0) j1))) - 1)
          = j1 - Adm M j0" using G3 by simp
  show "entry (Red (seg M (Adm M j0) j1)) 0 (j1 - Adm M j0)
          = entry (Red (seg M (Adm M j0) j1)) 1 (j1 - Adm M j0)" using G4 by simp
qed

text \<open>§8.4 (content.md ~4247) 補題（右端の非許容直系先祖の基本性質） — the GENERAL
  rightmost-non-admissible-direct-ancestor lemma (\<open>m_8_5_Joints_FirstNodes_basic\<close>
  above is the special case \<open>m\<^sub>0 = parent M 0 (Lng M-1)\<close>, \<open>m\<^sub>1 = Lng M-1\<close>).  Here
  \<open>m\<^sub>1\<close> is interior (\<open>m\<^sub>1 \<le> j\<^sub>1\<close>), so the last branch's first node \<open>m\<^sub>1-m\<^sub>-\<^sub>1\<close> is
  INTERIOR (\<open>\<noteq> Lng(Red N)-1\<close>) and \<open>transJm1(Red N) \<noteq> 0\<close> — the §8.2 Adm0 family does
  NOT apply to the full slice.  Route: \<open>Adm(Red N)(m\<^sub>0-m\<^sub>-\<^sub>1) = 0\<close> (slice-Adm
  heredity @{thm [source] m_6_3_admof_slice} + IncrFirst-invariance) gives
  \<open>m\<^sub>0-m\<^sub>-\<^sub>1 \<le> TrMax\<close>; the strictness from \<open>Adm(TrMax)=TrMax\<close>; \<open>TrMax < m\<^sub>1-m\<^sub>-\<^sub>1\<close>
  from the row-1 trunk step contradicting \<open>\<not> nextR M 1 (m\<^sub>1-1) m\<^sub>1\<close>; and the
  INTERIOR last-branch identification \<open>FirstNodes(Red N)!J\<^sub>1 = m\<^sub>1-m\<^sub>-\<^sub>1\<close> via the
  left-minimum / last-block-start pincer
  (@{thm [source] anchor_ge_of_leftmin} \<open>\<le>\<close> + @{thm [source] le0_leftmin_ancestor_ge}
  \<open>\<ge>\<close>) on the post-trunk slice.\<close>

lemma m_8_4_rightmost_nonadm_ancestor:
  fixes M :: pairseq and m0 m1 :: nat
  defines "j1 \<equiv> Lng M - 1"
    and "mm1 \<equiv> Adm M m0"
  assumes "M \<in> ST_PS" "M \<in> PT_PS"
    and "nextR M 0 m0 m1" "leR M 0 m1 j1"
    and "\<not> nextR M 1 (m1 - 1) m1"
    and "\<not> adm M m0"
  shows "Lng (Br (Red (seg M mm1 j1))) \<ge> 1"
    and "0 < m0 - mm1 \<and> m0 - mm1 < TrMax (Red (seg M mm1 j1))"
    and "m0 - mm1 = Joints (Red (seg M mm1 j1)) ! (Lng (Br (Red (seg M mm1 j1))) - 1)"
    and "FirstNodes (Red (seg M mm1 j1)) ! (Lng (Br (Red (seg M mm1 j1))) - 1) = m1 - mm1"
proof -
  let ?N = "seg M mm1 j1"
  let ?RN = "Red ?N"
  \<comment> \<open>memberships\<close>
  have Mst: "M \<in> ST_PS" by (rule assms(3))
  have MP: "M \<in> PT_PS" by (rule assms(4))
  have MR: "M \<in> RT_PS" using Mst m_6_7_ST_PS_subseteq_RT_PS by blast
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have nxR0: "nextR M 0 m0 m1" by (rule assms(5))
  have leRm1j1: "leR M 0 m1 j1" by (rule assms(6))
  have notnx1: "\<not> nextR M 1 (m1 - 1) m1" by (rule assms(7))
  have nadm: "\<not> adm M m0" by (rule assms(8))
  \<comment> \<open>order facts\<close>
  have m0ltm1: "m0 < m1" and lem0m1: "leR M 0 m0 m1"
    using poper_nextR_imp_le0[OF nxR0] by simp_all
  have j1eqLM: "j1 = Lng M - 1" by (simp add: j1_def)
  have le0m1j1: "le0 M m1 j1" using leRm1j1 by (simp add: leR_def)
  have m1ltLM: "m1 < Lng M" using le0m1j1 by (simp add: le0_def)
  have m1lej1: "m1 \<le> j1" using m1ltLM j1eqLM by linarith
  have L1: "1 < Lng M" using m0ltm1 m1ltLM by linarith
  have j1ltLM: "j1 < Lng M" using j1eqLM L1 by linarith
  have j1leLM1: "j1 \<le> Lng M - 1" by (simp add: j1_def)
  have m0lej1: "m0 < j1" using m0ltm1 m1lej1 by linarith
  have m0leLM1: "m0 \<le> Lng M - 1" using m0lej1 j1leLM1 by linarith
  \<comment> \<open>\<open>mm1 = Adm M m0 < m0\<close>\<close>
  have mm1ltm0: "mm1 < m0" using nadm_Adm_lt[OF nadm] mm1_def by simp
  have admmm1: "adm M mm1" using adm_Adm_adm mm1_def by simp
  have mm1ltm1: "mm1 < m1" using mm1ltm0 m0ltm1 by linarith
  have mm1ltj1: "mm1 < j1" using mm1ltm1 m1lej1 by linarith
  have mm1lem0: "mm1 \<le> m0" using mm1ltm0 by linarith
  have mm1lem1: "mm1 \<le> m1" using mm1ltm1 by linarith
  have mm1lej1: "mm1 \<le> j1" using mm1ltj1 by linarith
  \<comment> \<open>\<open>leR M 0 mm1 j1\<close>\<close>
  have le1a: "leR M 1 mm1 m0" using adm_row1_ancestry[OF MT m0leLM1] mm1_def by simp
  have le0a: "leR M 0 mm1 m0" by (rule m_le1_imp_le0[OF le1a])
  have le0mm1m0: "le0 M mm1 m0" using le0a by (simp add: leR_def)
  have le0m0m1: "le0 M m0 m1" using lem0m1 by (simp add: leR_def)
  have le0mm1m1: "le0 M mm1 m1" by (rule le0_trans[OF le0mm1m0 le0m0m1])
  have le0mm1j1: "le0 M mm1 j1" by (rule le0_trans[OF le0mm1m1 le0m1j1])
  have leM: "leR M 0 mm1 j1" using le0mm1j1 by (simp add: leR_def)
  \<comment> \<open>\<open>?RN\<close> facts\<close>
  have segT: "?N \<in> T_PS" using slice_Red_in_RT_PS[OF MR mm1ltj1 j1leLM1 leM] by simp
  have NR: "?RN \<in> RT_PS" using slice_Red_in_RT_PS[OF MR mm1ltj1 j1leLM1 leM] by simp
  have NT: "?RN \<in> T_PS" using NR by (simp add: RT_PS_def)
  have ND: "?RN \<in> DT_PS" by (rule m_8_2_standard_slice_Red_strongmono[OF Mst mm1ltj1 j1leLM1 leM])
  have monoRN: "monoT ?RN" using ND by (simp add: DT_PS_def)
  have NP: "?RN \<in> PT_PS" using NT monoRN by (simp add: PT_PS_def)
  have LRN: "Lng ?RN = Lng ?N" by (rule m_6_5_Lng_Red[OF segT])
  have LNval: "Lng ?N = Suc j1 - mm1" by simp
  have LRNm1: "Lng ?RN - 1 = j1 - mm1" using LRN LNval mm1lej1 by simp
  have LRNpos: "0 < Lng ?RN" using LRN LNval mm1lej1 by simp
  have segeq: "?N = (IncrFirst ^^ (entry M 0 mm1 - entry M 1 mm1)) ?RN"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR mm1ltj1 j1leLM1 leM] by simp
  \<comment> \<open>\<open>nextR\<close> bridge\<close>
  have bridge: "\<And>i p q. i \<le> (1::nat) \<Longrightarrow> p < Lng ?N \<Longrightarrow> q < Lng ?N
                 \<Longrightarrow> nextR ?RN i p q = nextR M i (mm1 + p) (mm1 + q)"
  proof -
    fix i p q :: nat assume i: "i \<le> 1" and p: "p < Lng ?N" and q: "q < Lng ?N"
    have "nextR ?RN i p q
            = nextR ((IncrFirst ^^ (entry M 0 mm1 - entry M 1 mm1)) ?RN) i p q"
      by (simp add: nextR_funpow_IncrFirst_eq)
    also have "\<dots> = nextR ?N i p q" using segeq by simp
    also have "\<dots> = nextR M i (mm1 + p) (mm1 + q)"
      by (rule rcpb_nextR_seg[OF j1ltLM i p q])
    finally show "nextR ?RN i p q = nextR M i (mm1 + p) (mm1 + q)" .
  qed
  \<comment> \<open>\<open>le0\<close> bridge (the row-0 chain \<open>m\<^sub>1-mm1 \<le> j\<^sub>1-mm1\<close> survives in \<open>?RN\<close>)\<close>
  have plt0: "m0 - mm1 < Lng ?N" using LNval m0lej1 mm1lem0 by linarith
  have qlt1: "m1 - mm1 < Lng ?N" using LNval m1lej1 mm1lem1 by linarith
  have add_m0: "mm1 + (m0 - mm1) = m0" using mm1lem0 by simp
  have add_m1: "mm1 + (m1 - mm1) = m1" using mm1lem1 by simp
  have add_j1: "mm1 + (j1 - mm1) = j1" using mm1lej1 by simp
  have B0: "nextR ?RN 0 (m0 - mm1) (m1 - mm1)"
    using bridge[of 0 "m0 - mm1" "m1 - mm1"] plt0 qlt1 nxR0 add_m0 add_m1 by simp
  have le0RN: "le0 ?RN (m1 - mm1) (j1 - mm1)"
  proof -
    have a1: "m1 - mm1 \<le> j1 - mm1" using m1lej1 by simp
    have a2: "j1 - mm1 \<le> j1 - mm1" by simp
    have "le0 ?N (m1 - mm1) (j1 - mm1) = le0 M (mm1 + (m1 - mm1)) (mm1 + (j1 - mm1))"
      by (rule adm_le0_seg[OF j1ltLM a1 a2 mm1lej1])
    hence "le0 ?N (m1 - mm1) (j1 - mm1)" using add_m1 add_j1 le0m1j1 by simp
    thus ?thesis using segeq le0_funpow_IncrFirst_eq[of "entry M 0 mm1 - entry M 1 mm1" ?RN] by simp
  qed
  \<comment> \<open>\<open>Adm(Red N)(m0-mm1) = 0\<close>\<close>
  have AdmN: "Adm ?N (m0 - mm1) = 0"
  proof -
    have "Adm ?N (m0 - mm1) = Adm M m0 - mm1"
      using m_6_3_admof_slice[OF MT _ m0lej1 j1leLM1] mm1_def by simp
    thus ?thesis using mm1_def by simp
  qed
  have Adm0: "Adm ?RN (m0 - mm1) = 0"
    using segeq Adm_funpow_IncrFirst_eq[of "entry M 0 mm1 - entry M 1 mm1" ?RN "m0 - mm1"] AdmN
    by simp
  \<comment> \<open>\<open>0 < m0-mm1 \<le> TrMax(Red N)\<close>\<close>
  have jppos: "0 < m0 - mm1" using mm1ltm0 by linarith
  have jpTr: "m0 - mm1 \<le> TrMax ?RN"
  proof (rule ccontr)
    assume "\<not> m0 - mm1 \<le> TrMax ?RN"
    hence le: "TrMax ?RN + 1 \<le> m0 - mm1" by simp
    have a: "adm ?RN (TrMax ?RN + 1)" by (rule adm_TrMax_succ[OF NT])
    have "TrMax ?RN + 1 \<le> Adm ?RN (m0 - mm1)" by (rule adm_Adm_max[OF a le])
    thus False using Adm0 by simp
  qed
  \<comment> \<open>strictness \<open>m0-mm1 < TrMax(Red N)\<close>\<close>
  have admT: "adm ?RN (TrMax ?RN)" by (rule adm_TrMax[OF NT])
  have AdmTeq: "Adm ?RN (TrMax ?RN) = TrMax ?RN" using admT by (simp add: Adm_def)
  have jpstrict: "m0 - mm1 < TrMax ?RN"
  proof -
    have "m0 - mm1 \<noteq> TrMax ?RN"
    proof
      assume eq: "m0 - mm1 = TrMax ?RN"
      hence "Adm ?RN (m0 - mm1) = TrMax ?RN" using AdmTeq by simp
      hence "TrMax ?RN = 0" using Adm0 by simp
      thus False using eq jppos by simp
    qed
    thus ?thesis using jpTr by linarith
  qed
  \<comment> \<open>\<open>TrMax(Red N) < m1-mm1\<close> from the row-1 trunk step vs \<open>\<not> nextR M 1 (m1-1) m1\<close>\<close>
  have tlt: "TrMax ?RN < m1 - mm1"
  proof (rule ccontr)
    assume "\<not> TrMax ?RN < m1 - mm1"
    hence ge: "m1 - mm1 \<le> TrMax ?RN" by simp
    have m1mm1pos: "0 < m1 - mm1" using mm1ltm1 by linarith
    have j'lt: "m1 - mm1 - 1 < TrMax ?RN" using ge m1mm1pos by linarith
    have step: "nextR ?RN 1 (m1 - mm1 - 1) ((m1 - mm1 - 1) + 1)"
      by (rule TrMax_trunk_step[OF NT j'lt])
    have eqn: "(m1 - mm1 - 1) + 1 = m1 - mm1" using m1mm1pos by simp
    have stepRN: "nextR ?RN 1 (m1 - mm1 - 1) (m1 - mm1)" using step eqn by simp
    have p1: "m1 - mm1 - 1 < Lng ?N" using qlt1 by linarith
    have add_p1: "mm1 + (m1 - mm1 - 1) = m1 - 1" using mm1ltm1 by linarith
    have "nextR M 1 (m1 - 1) m1"
      using bridge[of 1 "m1 - mm1 - 1" "m1 - mm1"] p1 qlt1 stepRN add_p1 add_m1 by simp
    thus False using notnx1 by simp
  qed
  \<comment> \<open>(1a) \<open>Br(Red N) \<noteq> []\<close>\<close>
  have m1mm1_leLm1: "m1 - mm1 \<le> Lng ?RN - 1" using LRNm1 m1lej1 mm1lem1 by linarith
  have trlt: "TrMax ?RN < Lng ?RN - 1" using tlt m1mm1_leLm1 by linarith
  have Brne: "Br ?RN \<noteq> []"
  proof -
    have "Br ?RN = P (seg ?RN (TrMax ?RN + 1) (Lng ?RN - 1))" using trlt by (simp add: Br_def)
    thus ?thesis using P_nonempty by simp
  qed
  have G1: "1 \<le> Lng (Br ?RN)" using Brne by (cases "Br ?RN") auto
  have JBr: "Lng (Br ?RN) - 1 < length (Br ?RN)" using G1 by simp
  \<comment> \<open>(1c) the INTERIOR last-branch identification: \<open>FirstNodes(Red N)!J\<^sub>1 = m\<^sub>1-mm1\<close>\<close>
  let ?t = "TrMax ?RN"
  let ?L = "Lng ?RN"
  let ?S = "seg ?RN (?t + 1) (?L - 1)"
  let ?k = "m1 - mm1 - (?t + 1)"
  let ?c = "IdxSum (P ?S) ! (length (P ?S) - 1)"
  have BrPS: "Br ?RN = P ?S" using trlt by (simp add: Br_def)
  have LSval: "Lng ?S = Suc (?L - 1) - (?t + 1)" by simp
  have LSpos: "0 < Lng ?S" using LSval trlt by linarith
  have STSne: "?S \<noteq> []"
  proof
    assume "?S = []"
    hence "Lng ?S = 0" by simp
    thus False using LSpos by simp
  qed
  have STS: "?S \<in> T_PS" using STSne by (simp add: T_PS_def)
  have tk: "(?t + 1) + ?k = m1 - mm1" using tlt by linarith
  have kle: "?k \<le> Lng ?S - 1" using LSval m1mm1_leLm1 tlt by linarith
  have klt: "?k < Lng ?S" using kle LSpos by linarith
  \<comment> \<open>the \<open>nextrel0\<close> middle condition from \<open>B0\<close>\<close>
  have mid: "\<forall>z. m0 - mm1 < z \<and> z < m1 - mm1 \<longrightarrow> entry ?RN 0 z \<ge> entry ?RN 0 (m1 - mm1)"
    using B0 by (simp add: nextR_def nextrel0_def)
  \<comment> \<open>\<open>m1-mm1\<close> (local \<open>?k\<close>) is a left-minimum of \<open>?S\<close>\<close>
  have lminK: "\<forall>j < ?k. entry ?S 0 ?k \<le> entry ?S 0 j"
  proof (intro allI impI)
    fix j assume jk: "j < ?k"
    have jlt: "j < Lng ?S" using jk klt by linarith
    have e1: "entry ?S 0 ?k = entry ?RN 0 (m1 - mm1)"
      by (subst entry_seg[OF klt], subst tk, rule refl)
    have e2: "entry ?S 0 j = entry ?RN 0 ((?t + 1) + j)" by (rule entry_seg[OF jlt])
    have rng: "m0 - mm1 < (?t + 1) + j \<and> (?t + 1) + j < m1 - mm1"
      using jk jpstrict tk by linarith
    have "entry ?RN 0 ((?t + 1) + j) \<ge> entry ?RN 0 (m1 - mm1)" using mid rng by blast
    thus "entry ?S 0 ?k \<le> entry ?S 0 j" using e1 e2 by simp
  qed
  have anchorK: "?k \<le> ?c" by (rule anchor_ge_of_leftmin[OF STS kle lminK])
  \<comment> \<open>\<open>?c\<close> is itself a left-minimum, and the chain \<open>?k \<rightarrow> Lng ?S - 1\<close> cannot cross it\<close>
  have PSne: "P ?S \<noteq> []" by (rule P_nonempty)
  have cIdx: "length (P ?S) - 1 < length (P ?S)" using PSne by (cases "P ?S") auto
  have lmin_c: "(\<forall>j < ?c. entry ?S 0 j \<ge> entry ?S 0 ?c) \<and> ?c \<le> Lng ?S - 1"
    using idxsum_leftend_lmin[OF STS cIdx] by simp
  have ac: "?c \<le> Lng ?S - 1" using lmin_c by simp
  have le0S: "le0 ?S ?k (Lng ?S - 1)"
  proof -
    have b1: "?k \<le> (?L - 1) - (?t + 1)" using kle LSval by linarith
    have b2: "Lng ?S - 1 \<le> (?L - 1) - (?t + 1)" using LSval by linarith
    have tLe: "?t + 1 \<le> ?L - 1" using trlt by linarith
    have LLM: "?L - 1 < ?L" using LRNpos by linarith
    have eq: "le0 ?S ?k (Lng ?S - 1) = le0 ?RN ((?t + 1) + ?k) ((?t + 1) + (Lng ?S - 1))"
      by (rule adm_le0_seg[OF LLM b1 b2 tLe])
    have i2: "(?t + 1) + (Lng ?S - 1) = j1 - mm1" using LSval LRNm1 tLe by linarith
    show ?thesis by (subst eq, subst tk, subst i2, rule le0RN)
  qed
  have chainS: "(nextrel0 ?S)\<^sup>*\<^sup>* ?k (Lng ?S - 1)" using le0S by (simp add: le0_def)
  have ck: "?c \<le> ?k"
    by (rule le0_leftmin_ancestor_ge[OF _ chainS ac]) (use lmin_c in blast)
  have ckeq: "?c = ?k" using anchorK ck by linarith
  have FNval: "FirstNodes ?RN ! (Lng (Br ?RN) - 1) = ?t + 1 + ?c"
    using FirstNodes_nth[OF JBr] BrPS by simp
  have G4: "FirstNodes ?RN ! (Lng (Br ?RN) - 1) = m1 - mm1"
  proof -
    have "FirstNodes ?RN ! (Lng (Br ?RN) - 1) = ?t + 1 + ?c" by (rule FNval)
    also have "\<dots> = ?t + 1 + ?k" by (subst ckeq, rule refl)
    also have "\<dots> = m1 - mm1" by (rule tk)
    finally show ?thesis .
  qed
  \<comment> \<open>(1b) \<open>Joints(Red N)!J\<^sub>1 = m0-mm1\<close>\<close>
  have parRNm1: "parent ?RN 0 (m1 - mm1) = m0 - mm1"
  proof -
    have "(THE p. nextR ?RN 0 p (m1 - mm1)) = m0 - mm1"
      by (rule the_equality, rule B0) (rule idxsum_parent0_unique[OF _ B0])
    thus ?thesis by (simp add: parent_def)
  qed
  have Jval: "Joints ?RN ! (Lng (Br ?RN) - 1) = parent ?RN 0 (FirstNodes ?RN ! (Lng (Br ?RN) - 1))"
    by (rule Joints_nth[OF JBr])
  have G2: "m0 - mm1 = Joints ?RN ! (Lng (Br ?RN) - 1)" using Jval G4 parRNm1 by simp
  \<comment> \<open>assemble\<close>
  show "Lng (Br (Red (seg M mm1 j1))) \<ge> 1" using G1 by simp
  show "0 < m0 - mm1 \<and> m0 - mm1 < TrMax (Red (seg M mm1 j1))" using jppos jpstrict by simp
  show "m0 - mm1 = Joints (Red (seg M mm1 j1)) ! (Lng (Br (Red (seg M mm1 j1))) - 1)"
    using G2 by simp
  show "FirstNodes (Red (seg M mm1 j1)) ! (Lng (Br (Red (seg M mm1 j1))) - 1) = m1 - mm1"
    using G4 by simp
qed

end

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


text \<open>§8.5 step2 WIRING (M-agnostic): the uniform pair-side recurrence
  \<open>step2\<close> reduces to THREE clean residuals stated at the SUBTREE level
  (\<open>bd q \<equiv> bpHeadT (Mark (M[q]) jm1)\<close>, the head subtree of the marked
  principal — the term \<open>OW\<close> wraps, NOT the full marked principal \<open>D\<^bsub>u\<^esub> (bd q)\<close>):
  the iterate \<open>OW\<close>-wrap \<open>wrap\<close> (\<open>Trans (M[q]) = OW (bd q)\<close>), outer-wrap
  injectivity \<open>inj\<close>, and the per-oper-step body recurrence \<open>body\<close>
  (\<open>bd (Suc q) = C (bd q)\<close>).  Given \<open>Trans (M[p]) = OW b\<close>, \<open>inj\<close> pins
  \<open>b = bd p\<close>, \<open>body\<close> grows it by one \<open>C\<close>, and \<open>wrap\<close> at \<open>Suc p\<close> re-wraps to
  \<open>OW (C b)\<close>.  The SUBTREE level is essential — the Mark-LEVEL analogue
  (\<open>Trans (M[q]) = OW (Mark (M[q]) jm1)\<close>) is FALSE (python/_step2_decomp_check:
  Mark-level wrap/body 0/36, subtree-level 36/36).  Exact drop-in for the \<open>step2\<close>
  hypothesis of @{thm [source] m_8_5_TransCondV_descend_of_step2_residuals}.\<close>

lemma m_8_5_step2_of_wrap_body:
  fixes M :: pairseq and OW C :: "BT \<Rightarrow> BT" and jm1 p :: nat and b :: BT
  assumes wrap: "\<And>q. 1 \<le> q \<Longrightarrow> Trans ((M::pairseq)[q]) = OW (bpHeadT (Mark ((M::pairseq)[q]) jm1))"
    and inj: "\<And>x y. OW x = OW y \<Longrightarrow> x = y"
    and body: "\<And>q. 2 \<le> q \<Longrightarrow> bpHeadT (Mark ((M::pairseq)[Suc q]) jm1)
                              = C (bpHeadT (Mark ((M::pairseq)[q]) jm1))"
    and p2: "2 \<le> p" and hb: "Trans ((M::pairseq)[p]) = OW b"
  shows "Trans ((M::pairseq)[Suc p]) = OW (C b)"
proof -
  have p1: "1 \<le> p" using p2 by simp
  have wp: "Trans ((M::pairseq)[p]) = OW (bpHeadT (Mark ((M::pairseq)[p]) jm1))"
    by (rule wrap[OF p1])
  have "OW (bpHeadT (Mark ((M::pairseq)[p]) jm1)) = OW b" using wp hb by simp
  hence beq: "bpHeadT (Mark ((M::pairseq)[p]) jm1) = b" by (rule inj)
  have sp1: "1 \<le> Suc p" by simp
  have "Trans ((M::pairseq)[Suc p]) = OW (bpHeadT (Mark ((M::pairseq)[Suc p]) jm1))"
    by (rule wrap[OF sp1])
  also have "bpHeadT (Mark ((M::pairseq)[Suc p]) jm1)
               = C (bpHeadT (Mark ((M::pairseq)[p]) jm1))" by (rule body[OF p2])
  also have "\<dots> = C b" using beq by simp
  finally show ?thesis .
qed

text \<open>§8.5 base2 WIRING (M-agnostic): the \<open>k\<close>-jump first oper step
  \<open>Trans (M[2]) = OW ((C\<^bsup>k\<^esup>) leafL\<^sub>0)\<close> (\<open>k \<in> {1,2}\<close>) from the same SUBTREE-level
  residuals — \<open>wrap\<close> at \<open>p = 2\<close>, the \<open>n = 1\<close> leaf identification
  \<open>bd 1 = leafL\<^sub>0\<close> (\<open>= transT2 M\<close>, @{thm [source] m_8_5_base_scb}), and the
  first-step \<open>k\<close>-jump \<open>bd 2 = (C\<^bsup>k\<^esup>) (bd 1)\<close> (the base analogue of \<open>body\<close>,
  with \<open>k \<in> {1,2}\<close> instead of exactly one \<open>C\<close>; python base2 28/28, k=1:27/k=2:1).\<close>

lemma m_8_5_base2_of_wrap_body:
  fixes M :: pairseq and OW C :: "BT \<Rightarrow> BT" and jm1 k :: nat and leafL\<^sub>0 :: BT
  assumes wrap2: "Trans ((M::pairseq)[2]) = OW (bpHeadT (Mark ((M::pairseq)[2]) jm1))"
    and baseleaf: "bpHeadT (Mark ((M::pairseq)[1]) jm1) = leafL\<^sub>0"
    and basejump: "bpHeadT (Mark ((M::pairseq)[2]) jm1)
                     = (C ^^ k) (bpHeadT (Mark ((M::pairseq)[1]) jm1))"
  shows "Trans ((M::pairseq)[2]) = OW ((C ^^ k) leafL\<^sub>0)"
proof -
  have "Trans ((M::pairseq)[2]) = OW (bpHeadT (Mark ((M::pairseq)[2]) jm1))" by (rule wrap2)
  also have "bpHeadT (Mark ((M::pairseq)[2]) jm1)
               = (C ^^ k) (bpHeadT (Mark ((M::pairseq)[1]) jm1))" by (rule basejump)
  also have "\<dots> = (C ^^ k) leafL\<^sub>0" using baseleaf by simp
  finally show ?thesis .
qed

text \<open>§8.5 base-leaf residual DISCHARGED: the \<open>n = 1\<close> subtree-level leaf body is
  \<open>transT2 M\<close>.  \<open>M[1] = Pred M\<close> (@{thm [source] m_8_4_oper1_eq_Pred}), so the marked
  subterm \<open>Mark (M[1]) (transJm1 M) = Mark (Pred M) (transJm1 M) = transC1 M\<close>
  (@{thm [source] transC1_def}) and its head subtree is \<open>bpHeadT (transC1 M) =
  transT2 M\<close> (@{thm [source] transT2_def}).  This is the \<open>baseleaf\<close> hypothesis of
  @{thm [source] m_8_5_base2_of_wrap_body} with \<open>jm1 = transJm1 M\<close>, \<open>leafL\<^sub>0 = transT2 M\<close>.\<close>

lemma m_8_5_base_leaf:
  assumes MT: "M \<in> T_PS"
  shows "bpHeadT (Mark ((M::pairseq)[1]) (transJm1 M)) = transT2 M"
proof -
  have o1: "(M::pairseq)[1] = Pred M" by (rule m_8_4_oper1_eq_Pred[OF MT])
  have "Mark ((M::pairseq)[1]) (transJm1 M) = Mark (Pred M) (transJm1 M)" using o1 by simp
  also have "\<dots> = transC1 M" by (simp add: transC1_def)
  finally show ?thesis by (simp add: transT2_def)
qed

text \<open>§8.5 outer-wrap INJECTIVITY DISCHARGED.  The kind-1 outer wrap
  \<open>OW x = unflatBT (s\<^sub>1 \<frown> D\<^bsub>u\<^esub> # flat x \<frown> b\<^sub>1)\<close> built from ANY scb-decomposition of a
  term \<open>t\<close> at the single-principal centre \<open>D\<^bsub>u\<^esub> t\<^sub>0\<close> is injective: by
  @{thm [source] scbimg_image_BT} (\<open>b\<^sub>1\<close> all \<open>RP\<close>) the string \<open>s\<^sub>1 \<frown> D\<^bsub>u\<^esub> # flat x \<frown> b\<^sub>1\<close>
  is in the flat image, so \<open>flat (OW x) = s\<^sub>1 \<frown> D\<^bsub>u\<^esub> # flat x \<frown> b\<^sub>1\<close>
  (@{thm [source] unflatBT_flat}); cancelling the common prefix/suffix and using
  flat injectivity gives \<open>x = y\<close>.  Discharges the \<open>inj\<close> hypothesis of
  @{thm [source] m_8_5_step2_of_wrap_body} from the producer's kind-1 scb-decomp.\<close>

lemma m_8_5_OW_inj_of_scb:
  fixes s\<^sub>1 b\<^sub>1 :: "Sym list" and u :: nat and OW :: "BT \<Rightarrow> BT" and t t\<^sub>0 x y :: BT
  assumes OW_def: "OW = (\<lambda>x. unflatBT (s\<^sub>1 @ Dsym (enat u) # flatBT x @ b\<^sub>1))"
    and scb: "scb_decomp t s\<^sub>1 (flatBT (Dpt (enat u) t\<^sub>0)) b\<^sub>1"
    and hxy: "OW x = OW y"
  shows "x = y"
proof -
  have bRP: "\<forall>z \<in> set b\<^sub>1. z = RP" using scb by (simp add: scb_decomp_def)
  have flatc: "flatBT t = s\<^sub>1 @ flatBT (Dpt (enat u) t\<^sub>0) @ b\<^sub>1"
    using scb by (simp add: scb_decomp_def)
  have flat_t: "flatBT t = s\<^sub>1 @ flatBP (DB (enat u) t\<^sub>0) @ b\<^sub>1" using flatc by simp
  have fow: "\<And>z. flatBT (OW z) = s\<^sub>1 @ Dsym (enat u) # flatBT z @ b\<^sub>1"
  proof -
    fix z
    have "\<exists>t'. flatBT t' = s\<^sub>1 @ flatBP (DB (enat u) z) @ b\<^sub>1"
      by (rule scbimg_image_BT[OF flat_t bRP])
    then obtain tz where tz: "flatBT tz = s\<^sub>1 @ flatBP (DB (enat u) z) @ b\<^sub>1" by blast
    have "OW z = unflatBT (s\<^sub>1 @ Dsym (enat u) # flatBT z @ b\<^sub>1)" by (simp add: OW_def)
    also have "s\<^sub>1 @ Dsym (enat u) # flatBT z @ b\<^sub>1 = s\<^sub>1 @ flatBP (DB (enat u) z) @ b\<^sub>1" by simp
    also have "unflatBT \<dots> = unflatBT (flatBT tz)" using tz by simp
    also have "\<dots> = tz" by (rule unflatBT_flat)
    finally have "OW z = tz" .
    thus "flatBT (OW z) = s\<^sub>1 @ Dsym (enat u) # flatBT z @ b\<^sub>1" using tz by simp
  qed
  have "s\<^sub>1 @ Dsym (enat u) # flatBT x @ b\<^sub>1 = s\<^sub>1 @ Dsym (enat u) # flatBT y @ b\<^sub>1"
    using fow[of x] fow[of y] hxy by simp
  hence "flatBT x @ b\<^sub>1 = flatBT y @ b\<^sub>1" by simp
  hence "flatBT x = flatBT y" by simp
  hence "unflatBT (flatBT x) = unflatBT (flatBT y)" by simp
  thus "x = y" by (simp add: unflatBT_flat)
qed

text \<open>§8.5 marking-nesting STEP REDUCED to the single block-append SURGERY (uniform
  in the body endofunction \<open>F\<close>: \<open>F = C\<close> gives the \<open>body\<close> recurrence \<open>q \<ge> 2\<close>,
  \<open>F = C\<^bsup>k\<^esup>\<close> the \<open>base-jump\<close> first oper step \<open>q = 1\<close>, \<open>k \<in> {1,2}\<close>).  The marked-
  subterm recurrence \<open>bpHeadT (Mark (M[Suc q]) jm1) = F (bpHeadT (Mark (M[q]) jm1))\<close>
  follows from the §7.4 Mark-representations (@{thm [source] Mark_iterate_slice_append}
  for \<open>M[Suc q]\<close>, @{thm [source] m_7_4_Mark_Trans_repr} for \<open>M[q]\<close>) and the SURGERY
  \<open>Trans (Y \<frown> B) = D\<^bsub>u\<^esub> (F (bpHeadT (Trans Y)))\<close> on the tail slice
  \<open>Y = seg (M[q]) jm1 (Lng (M[q]) - 1)\<close>: both marked subterms read back as \<open>Trans\<close>
  of the slice (resp. the slice with the appended oper block \<open>B\<close>), so taking
  \<open>bpHeadT\<close> of the surgery (the \<open>D\<^bsub>u\<^esub>\<close>-head is discarded) yields exactly \<open>F\<close> applied
  to the slice's body.  The SURGERY (one net \<open>C\<close> per appended block — \<open>F = C\<close> for the
  uniform iterates, \<open>F = C\<^bsup>k\<^esup>\<close> for the first step; the §8 master-key residual,
  python/_step2_decomp_check surgery 36/36) and the iterate basepoint memberships
  \<open>(M[q],jm1),(M[Suc q],jm1) \<in> Marked\<close> are the remaining obligations.  Discharges
  \<open>body\<close> (\<open>F:=C\<close>) of @{thm [source] m_8_5_step2_of_wrap_body} and \<open>basejump\<close>
  (\<open>F:=(C^^k)\<close>) of @{thm [source] m_8_5_base2_of_wrap_body}.\<close>

lemma m_8_5_markstep_of_surgery:
  fixes M B :: pairseq and F :: "BT \<Rightarrow> BT" and jm1 q u :: nat
  defines "Y \<equiv> seg ((M::pairseq)[q]) jm1 (Lng ((M::pairseq)[q]) - 1)"
  assumes mkSuc: "((M::pairseq)[Suc q], jm1) \<in> Marked"
    and MRSuc: "(M::pairseq)[Suc q] \<in> RT_PS"
    and rngSuc: "jm1 < Lng ((M::pairseq)[Suc q]) - 1"
    and app: "(M::pairseq)[Suc q] = (M::pairseq)[q] @ B"
    and Mqne: "0 < Lng ((M::pairseq)[q])"
    and jle: "jm1 \<le> Lng ((M::pairseq)[q])"
    and mkq: "((M::pairseq)[q], jm1) \<in> Marked"
    and MRq: "(M::pairseq)[q] \<in> RT_PS"
    and rngq: "jm1 < Lng ((M::pairseq)[q]) - 1"
    and surgery: "Trans (Y @ B) = Dpt (enat u) (F (bpHeadT (Trans Y)))"
  shows "bpHeadT (Mark ((M::pairseq)[Suc q]) jm1) = F (bpHeadT (Mark ((M::pairseq)[q]) jm1))"
proof -
  have markSuc: "Mark ((M::pairseq)[Suc q]) jm1 = Trans (Y @ B)"
    unfolding Y_def by (rule Mark_iterate_slice_append[OF mkSuc MRSuc rngSuc app Mqne jle])
  have markq: "Mark ((M::pairseq)[q]) jm1 = Trans Y"
    unfolding Y_def by (rule m_7_4_Mark_Trans_repr[OF mkq MRq rngq])
  have "bpHeadT (Mark ((M::pairseq)[Suc q]) jm1) = bpHeadT (Trans (Y @ B))"
    using markSuc by simp
  also have "\<dots> = bpHeadT (Dpt (enat u) (F (bpHeadT (Trans Y))))" using surgery by simp
  also have "\<dots> = F (bpHeadT (Trans Y))" by simp
  also have "\<dots> = F (bpHeadT (Mark ((M::pairseq)[q]) jm1))" using markq by simp
  finally show ?thesis .
qed

text \<open>§8.5 \<open>wrap\<close> residual REDUCED to the iterate kind-1 scb (context stability).
  The subtree-level \<open>OW\<close>-wrap \<open>Trans (M[q]) = OW (bpHeadT (Mark (M[q]) jm1))\<close> is
  IMMEDIATE from the \<open>OW\<close>-anchor @{thm [source] m_8_5_anchor_OW} once the iterate
  \<open>M[q]\<close> carries the SAME kind-1 scb context \<open>(s\<^sub>1,b\<^sub>1)\<close> and head \<open>u\<close> as the producer,
  at its own marked subterm \<open>D\<^bsub>u\<^esub> (bpHeadT (Mark (M[q]) jm1))\<close> — the residual
  \<open>iterscb\<close>.  \<open>iterscb\<close> is the iterate analogue of the producer's \<open>k1\<close>, supplied by
  the OW-context stability @{thm [source] scb_context_eq_of_prefix} (the trunk
  prefix \<open>seg (M[q]) 0 jm1 = seg M 0 jm1\<close> is verbatim, so the scb-context matches
  the \<open>n = 1\<close> base / producer) plus the iterate basepoint membership
  \<open>(M[q],jm1) \<in> Marked\<close> (@{thm [source] m_8_3_kind1_base_basepoint}).  Discharges
  \<open>wrap\<close> of @{thm [source] m_8_5_step2_of_wrap_body} / @{thm [source]
  m_8_5_base2_of_wrap_body}.\<close>

lemma m_8_5_wrap_of_iterscb:
  fixes M :: pairseq and OW :: "BT \<Rightarrow> BT" and s\<^sub>1 b\<^sub>1 :: "Sym list" and u jm1 q :: nat
  assumes OW_def: "OW = (\<lambda>x. unflatBT (s\<^sub>1 @ Dsym (enat u) # flatBT x @ b\<^sub>1))"
    and iterscb: "scb_kind1 (Trans ((M::pairseq)[q])) s\<^sub>1
                    (flatBT (Dpt (enat u) (bpHeadT (Mark ((M::pairseq)[q]) jm1)))) b\<^sub>1"
  shows "Trans ((M::pairseq)[q]) = OW (bpHeadT (Mark ((M::pairseq)[q]) jm1))"
  by (rule m_8_5_anchor_OW[OF OW_def iterscb])

text \<open>§8.5 step2/base2 REDUCTION LADDER (this round, layer c).  The unconditional
  §8.5 condition-(V) descent reduces — via @{thm [source]
  m_8_5_TransCondV_descend_of_step2_residuals} and the wirings above — to exactly
  three GENUINE residuals, all empirically validated (python/_step2_decomp_check):
    (1) SURGERY  \<open>Trans (Y \<frown> B) = D\<^bsub>u\<^esub> (F (bpHeadT (Trans Y)))\<close>  (one net \<open>C\<close> per
        appended oper block; \<open>F=C\<close> iterates, \<open>F=C\<^bsup>k\<^esup>\<close> first step) — the §8 master key;
    (2) ITERSCB  the iterate kind-1 scb-context match (context stability,
        @{thm [source] scb_context_eq_of_prefix});
    (3) BASEPOINT  \<open>(M[q],jm1) \<in> Marked\<close> (@{thm [source] m_8_3_kind1_base_basepoint},
        needing condV \<Longrightarrow> hp1/coin/parR/j0lt2).
  All other obligations (\<open>inj\<close>, \<open>base-leaf\<close>, the wirings) are discharged here.\<close>

text \<open>SURGERY — empirical structure (python/_surgery_trace.py + _spine_Pm.py;
  condV hosts, p \<in> {2,3}), for whoever closes the |B|-composition:
  • (A) EVERY appended-block column triggers @{thm [source] m_8_2_keystone} case
    (3)/(4) (DEEPEN the trailing principal \<open>D\<^bsub>x\<^esub> a \<rightarrow> D\<^bsub>x\<^esub> b\<close>), NEVER case (1)/(2)
    (74/74 cols).  So the 4-way disjunction collapses to the two deepen cases —
    provable from the block FirstNodes/Joints structure (the §8.5 Joints-FirstNodes
    target; no such lemma yet in this base).
  • (B) the genuine value-recurrence.  The keystone (3)/(4) gives the trailing-leaf
    change SHAPE (\<open>a \<rightarrow> b\<close>) but NOT \<open>b\<close>'s value.  The per-column transform is NOT
    uniform: it applies one keystone DEEPEN at the CURRENT TRAILING-MOST leaf, and
    the descent DEPTH GROWS WITH p (p=2: col[0] appends \<open>D\<^bsub>v-1\<^esub> 0\<close> then interiors
    build \<open>t\<^sub>2\<close>; p=3: BOTH columns deepen one level lower; …).  It is a RECURSIVE
    spine-descent, well-founded on the trailing-leaf depth, netting exactly one
    \<open>C x = t\<^sub>2 +\<^sub>B D\<^bsub>v-1\<^esub> x\<close> per w-column block.
  • CIRCULARITY of the naive m-induction (verified): the spine invariant
    \<open>Trans (Y \<frown> take m B) = D\<^bsub>u\<^esub> (t\<^sub>2 +\<^sub>B D\<^bsub>v-1\<^esub> (P m))\<close> forces \<open>P 0 = bd (q-1)\<close>
    (= bpHeadT(Mark (M[q-1]) jm1); 55/56, the 1 exception is the k=2 first step),
    so its BASE case (m=0) is \<open>bpHeadT(Trans Y) = t\<^sub>2 +\<^sub>B D\<^bsub>v-1\<^esub>(bd (q-1))\<close>, i.e.
    \<open>bd q = C (bd (q-1))\<close> — the surgery CONCLUSION itself.  Hence a standalone
    induction on m does NOT close it; the surgery needs an OUTER induction on q
    (the closed-form @{thm [source] funpow_closed_of_step_from2} already inducts on
    q — the q-1 body structure is the IH) wrapping the spine-descent for the step,
    or a single well-founded induction on \<open>Lng (Y \<frown> B)\<close>.
  NET RESIDUAL: appending one w-column oper block traverses-and-rebuilds the
  trailing \<open>D\<^bsub>v-1\<^esub>\<close>-spine of \<open>bd (q-1)\<close>, wrapping it in one more \<open>C\<close>; this is the
  §8.5 |B|-composition master key and has no existing closing lemma.\<close>


text \<open>Head-extraction from a single-principal \<open>leBT\<close>: \<open>leBT (D\<^bsub>u\<^esub> a) (D\<^bsub>v\<^esub> b)\<close> forces
  \<open>u \<le> v\<close> (the lexicographic head dominates).  Companion of @{thm [source] leBT_Dpt_mono}
  (which moves the body under a fixed head).\<close>

lemma leBT_Dpt_head_le:
  assumes "leBT (Dpt u a) (Dpt v b)"
  shows "u \<le> v"
proof -
  have "lessBT (Trm [DB u a]) (Trm [DB v b]) \<or> Trm [DB u a] = Trm [DB v b]"
    using assms by simp
  thus ?thesis
  proof
    assume "lessBT (Trm [DB u a]) (Trm [DB v b])"
    hence "lessBP (DB u a) (DB v b)" by simp
    hence "u < v \<or> (u = v \<and> lessBT a b)" by simp
    thus ?thesis by auto
  next
    assume "Trm [DB u a] = Trm [DB v b]"
    thus ?thesis by simp
  qed
qed

text \<open>§8.7 R2 brick — keystone PROPER-PREFIX \<open>dstep\<close> reduction to the equal-head tail
  (cases (3)/(4), surgery-FREE).  In keystone cases (3)/(4) the predecessor body is a
  PROPER prefix \<open>Trm ps\<close> trailing an appended principal \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>j\<^esub> q\<^sub>p\<close> at the SAME head
  index \<open>jj\<close> (\<open>jj = j\<^sub>1'\<close> for (3), \<open>jj = j\<^sub>0'\<close> for (4)) as the \<open>M\<close>-appended principal
  \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>j\<^esub> q\<close>.  The \<open>head\<close> input \<open>x \<le> hd\<close> is then FREE from the IH \<open>descP\<close>:
  \<open>isOT_BT (Trans (Pred M))\<close> exposes \<open>descP (ps @ [D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>j\<^esub> q\<^sub>p])\<close>, whose last step
  (@{thm [source] descP_last_le}) gives \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>j\<^esub> q\<^sub>p \<le> last ps\<close>, hence the head bound
  \<open>M\<^bsub>1,jj\<^esub> \<le> hd\<close> (@{thm [source] leBT_Dpt_head_le}).  This DISCHARGES the head and
  isolates the genuine residual to the equal-head tail \<open>tail\<close>: \<open>M\<^bsub>1,jj\<^esub> = hd \<Longrightarrow>
  leBT q qb\<close> — the genuine \<open>Trans\<close>-spine descent (the \<open>M\<close>-appended body \<open>q \<ge> q\<^sub>p\<close> by the
  §7.3 \<open>Pred\<close>-descent, so this does NOT come from \<open>descP\<close>-inheritance).  Empirically
  verified: \<open>dstep\<close> 0-fail and equal-head \<open>leBT q qb\<close> 0-fail over 1450+ \<open>ST\<^bsub>PS\<^esub>\<close>
  keystone samples (\<open>python/_r2_dstep_check.py\<close>; equal-head occurs at \<open>x = 0\<close> AND
  \<open>x > 0\<close>, with \<open>q = qb\<close> in the periodic-copy subcases and \<open>q < qb\<close> strictly otherwise).\<close>

lemma m_8_7_dstep_properprefix_reduce:
  fixes M :: pairseq and ps :: "BP list" and q qp :: BT and jj :: nat
  assumes ihBT: "isOT_BT (Trans (Pred M))"
    and predW: "Trans (Pred M)
                = Dpt (enat (entry M 1 0)) (Trm ps +\<^sub>B Dpt (enat (entry M 1 jj)) qp)"
    and psne: "ps \<noteq> []"
    and tail: "\<And>hd qb. last ps = DB (enat hd) qb \<Longrightarrow> entry M 1 jj = hd \<Longrightarrow> leBT q qb"
  shows "leBT (Dpt (enat (entry M 1 jj)) q) (Trm [last ps])"
proof -
  let ?x = "entry M 1 jj"
  have bodyOT: "isOT_BT (Trm ps +\<^sub>B Dpt (enat ?x) qp)"
    using ihBT predW by simp
  have "isOT_BT (Trm (ps @ [DB (enat ?x) qp]))" using bodyOT by simp
  hence dP: "descP (ps @ [DB (enat ?x) qp])" by simp
  have dl: "leBT (Trm [DB (enat ?x) qp]) (Trm [last ps])"
    by (rule descP_last_le[OF dP psne])
  obtain lw qb where lastps: "last ps = DB lw qb" by (cases "last ps")
  have dl': "leBT (Dpt (enat ?x) qp) (Dpt lw qb)"
    using dl lastps by simp
  show ?thesis
  proof (cases "enat ?x = lw")
    case False
    have "enat ?x \<le> lw" by (rule leBT_Dpt_head_le[OF dl'])
    hence "enat ?x < lw" using False by simp
    hence "lessBP (DB (enat ?x) q) (DB lw qb)" by simp
    hence "lessBT (Dpt (enat ?x) q) (Dpt lw qb)" by simp
    thus ?thesis using lastps by simp
  next
    case True
    obtain hd where hd: "lw = enat hd" using True by (cases lw) auto
    have xhd: "?x = hd" using True hd by simp
    have lastps2: "last ps = DB (enat hd) qb" using lastps hd by simp
    have "leBT q qb" by (rule tail[OF lastps2 xhd])
    hence "leBT (Dpt (enat hd) q) (Dpt (enat hd) qb)" by (rule leBT_Dpt_mono)
    thus ?thesis using lastps hd xhd by simp
  qed
qed

text \<open>§8.5 SURGERY sub-fact (A.collapse) — the per-column DEEPEN step.  Appending a
  single column \<open>col\<close> to \<open>X\<close> (host \<open>M' = X \<frown> [col]\<close>) whose last branch is NOT a
  singleton (\<open>j\<^sub>1' = FirstNodes M' ! J\<^sub>1 \<noteq> j\<^sub>1\<close>) collapses the §8.2 keystone four-way
  disjunction (@{thm [source] Trans_append_col_keystone}) to its two DEEPEN cases
  (3)/(4): the trailing principal keeps its head \<open>h\<close> and only its subtree changes
  \<open>a \<rightarrow> b\<close>, with a COMMON prefix body \<open>t\<close>.  Cases (1)/(2) both assert \<open>j\<^sub>1' = j\<^sub>1\<close>
  and are killed by \<open>j1ne\<close>.  Empirically \<open>j\<^sub>1' \<noteq> j\<^sub>1\<close> holds for every appended-block
  column (148/148, python/probeA), so this is exactly the SHAPE half of the surgery
  spine-descent; the genuine residual is the VALUE step \<open>a \<rightarrow> b\<close> (sub-fact B).\<close>

lemma m_8_5_deepen_step:
  fixes X :: pairseq and col :: "nat \<times> nat"
  defines "M' \<equiv> X @ [col]"
  defines "j1 \<equiv> Lng M' - 1"
  defines "J1 \<equiv> Lng (Br M') - 1"
  defines "j0' \<equiv> Joints M' ! J1"
  defines "j1' \<equiv> FirstNodes M' ! J1"
  assumes Xne: "0 < Lng X"
    and MR: "M' \<in> RT_PS" and MP: "M' \<in> PT_PS"
    and Brne: "Br M' \<noteq> []" and j1gt: "j1 > 1"
    and j1ne: "j1' \<noteq> j1"
  shows "\<exists>t h a b. (h = entry M' 1 j1' \<or> h = entry M' 1 j0')
              \<and> Trans X = Dpt (enat (entry M' 1 0)) (t +\<^sub>B Dpt (enat h) a)
              \<and> Trans M' = Dpt (enat (entry M' 1 0)) (t +\<^sub>B Dpt (enat h) b)"
proof -
  have key: "(j1' = j1 \<and> (TrMax M' = 0 \<or> j0' < TrMax M')
        \<and> (entry M' 0 j1' = entry M' 1 j1' \<or> adm M' j0')
        \<and> (\<exists>!t1. Trans X = Dpt (enat (entry M' 1 0)) t1
              \<and> Trans M' = Dpt (enat (entry M' 1 0))
                            (t1 +\<^sub>B Dpt (enat (entry M' 1 j1')) 0\<^sub>B)))
   \<or> (j1' = j1 \<and> entry M' 0 j1' > entry M' 1 j1' \<and> \<not> adm M' j0'
        \<and> (\<exists>!t12. Trans X = Dpt (enat (entry M' 1 0)) (fst t12)
              \<and> Trans M' = Dpt (enat (entry M' 1 0))
                            (fst t12 +\<^sub>B Dpt (enat (entry M' 1 j0')) (snd t12))))
   \<or> (\<exists>!t123. Trans X
                = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j1')) (fst (snd t123)))
            \<and> Trans M' = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j1')) (snd (snd t123))))
   \<or> (\<exists>!t123. Trans X
                = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j0')) (fst (snd t123)))
            \<and> Trans M' = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j0')) (snd (snd t123))))"
    using Trans_append_col_keystone[OF Xne MR[unfolded M'_def] MP[unfolded M'_def]
            Brne[unfolded M'_def] j1gt[unfolded j1_def M'_def]]
    unfolding M'_def j1_def J1_def j0'_def j1'_def .
  from key j1ne have "(\<exists>!t123. Trans X
                = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j1')) (fst (snd t123)))
            \<and> Trans M' = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j1')) (snd (snd t123))))
   \<or> (\<exists>!t123. Trans X
                = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j0')) (fst (snd t123)))
            \<and> Trans M' = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j0')) (snd (snd t123))))"
    by blast
  thus ?thesis
  proof
    assume "\<exists>!t123. Trans X
                = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j1')) (fst (snd t123)))
            \<and> Trans M' = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j1')) (snd (snd t123)))"
    then obtain t123 where
      "Trans X = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j1')) (fst (snd t123)))
       \<and> Trans M' = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j1')) (snd (snd t123)))"
      by (blast dest: ex1_implies_ex)
    thus ?thesis by blast
  next
    assume "\<exists>!t123. Trans X
                = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j0')) (fst (snd t123)))
            \<and> Trans M' = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j0')) (snd (snd t123)))"
    then obtain t123 where
      "Trans X = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j0')) (fst (snd t123)))
       \<and> Trans M' = Dpt (enat (entry M' 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M' 1 j0')) (snd (snd t123)))"
      by (blast dest: ex1_implies_ex)
    thus ?thesis by blast
  qed
qed

text \<open>§8.5 SURGERY sub-fact (A.shape) — the P-decomposition direction.  If the
  last column's row-0 PARENT lies strictly past the trunk (\<open>parent M' 0 (Lng M'-1)
  > TrMax M'\<close>, i.e. it attaches inside a BRANCH, not the trunk), then the last
  column is NOT the first node of the last branch (\<open>j\<^sub>1' \<noteq> j\<^sub>1\<close>).  Mechanism: every
  branch first node has its row-0 parent in the trunk
  (@{thm [source] m_6_4_FirstNodes_TrMax_Joints}: \<open>Joints M' ! J \<le> TrMax M'\<close>, and
  \<open>Joints M' ! J = parent M' 0 (FirstNodes M' ! J)\<close> by @{thm [source] Joints_nth});
  so if the last column \<open>Lng M'-1\<close> WERE that first node \<open>j\<^sub>1'\<close>, its parent would be
  \<open>\<le> TrMax M'\<close>, contradicting \<open>par\<close>.  This is the exact (A)-characterisation:
  empirically \<open>j\<^sub>1' \<noteq> j\<^sub>1 \<longleftrightarrow> parent M' 0 (Lng M'-1) > TrMax M'\<close> (python/probeC,
  148/148), so it feeds @{thm [source] m_8_5_deepen_step}'s \<open>j1ne\<close> hypothesis.\<close>

lemma m_8_5_appended_col_j1ne:
  fixes M' :: pairseq
  assumes MP: "M' \<in> PT_PS" and Brne: "Br M' \<noteq> []"
    and par: "parent M' 0 (Lng M' - 1) > TrMax M'"
  shows "FirstNodes M' ! (Lng (Br M') - 1) \<noteq> Lng M' - 1"
proof
  assume eq: "FirstNodes M' ! (Lng (Br M') - 1) = Lng M' - 1"
  have J1lt: "Lng (Br M') - 1 < Lng (Br M')" using Brne by (cases "Br M'") auto
  have jle: "Joints M' ! (Lng (Br M') - 1) \<le> TrMax M'"
    using m_6_4_FirstNodes_TrMax_Joints[OF MP J1lt] by simp
  have jpar: "Joints M' ! (Lng (Br M') - 1)
                = parent M' 0 (FirstNodes M' ! (Lng (Br M') - 1))"
    using J1lt by (simp add: Joints_nth)
  have "parent M' 0 (Lng M' - 1) \<le> TrMax M'" using jle jpar eq by simp
  thus False using par by simp
qed

text \<open>§8.5 SURGERY — the per-column DEEPEN step packaged from the geometric
  (A)-characterisation.  Combines @{thm [source] m_8_5_appended_col_j1ne} (the last
  column attaches inside a branch \<Longrightarrow> \<open>j\<^sub>1' \<noteq> j\<^sub>1\<close>) with
  @{thm [source] m_8_5_deepen_step} (keystone collapse) into a single drop-in: for a
  reduced standard host \<open>X \<frown> [col]\<close> whose appended column's row-0 parent is past the
  trunk, the §8.2 keystone four-way collapses to the two DEEPEN cases — the trailing
  principal keeps its head \<open>h\<close>, only its subtree changes \<open>a \<rightarrow> b\<close>, with a common
  prefix body \<open>t\<close>.  This is the SHAPE half of the surgery spine-descent; the residual
  is the VALUE step \<open>a \<rightarrow> b\<close> (sub-fact B) and the geometric input \<open>par\<close>.\<close>

lemma m_8_5_appended_col_deepen:
  fixes X :: pairseq and col :: "nat \<times> nat"
  defines "M' \<equiv> X @ [col]"
  assumes Xne: "0 < Lng X"
    and MR: "M' \<in> RT_PS" and MP: "M' \<in> PT_PS"
    and Brne: "Br M' \<noteq> []" and j1gt: "Lng M' - 1 > 1"
    and par: "parent M' 0 (Lng M' - 1) > TrMax M'"
  shows "\<exists>t h a b.
       (h = entry M' 1 (FirstNodes M' ! (Lng (Br M') - 1))
          \<or> h = entry M' 1 (Joints M' ! (Lng (Br M') - 1)))
       \<and> Trans X = Dpt (enat (entry M' 1 0)) (t +\<^sub>B Dpt (enat h) a)
       \<and> Trans M' = Dpt (enat (entry M' 1 0)) (t +\<^sub>B Dpt (enat h) b)"
proof -
  have j1ne: "FirstNodes M' ! (Lng (Br M') - 1) \<noteq> Lng M' - 1"
    by (rule m_8_5_appended_col_j1ne[OF MP Brne par])
  show ?thesis
    using m_8_5_deepen_step[OF Xne MR[unfolded M'_def] MP[unfolded M'_def]
            Brne[unfolded M'_def] j1gt[unfolded M'_def] j1ne[unfolded M'_def]]
    unfolding M'_def .
qed

text \<open>§8.5 SURGERY — VALUE step (B) precise residual (python/_probeVal, 26/26
  classified, 0 OTHER).  The SHAPE half is now green (@{thm [source]
  m_8_5_deepen_step} / @{thm [source] m_8_5_appended_col_deepen}): each appended
  column keeps the prefix body \<open>t\<close> and trailing head \<open>h\<close>, changing only the trailing
  subtree \<open>a \<rightarrow> b\<close>.  The VALUE \<open>b = f(a,col)\<close> is NOT a flat formula — it is the SAME
  keystone append-or-deepen applied RECURSIVELY to \<open>a\<close> at its OWN trailing position:
    • APPEND base (\<open>a\<close>'s trailing slot is a leaf): \<open>b = a +\<^sub>B D\<^bsub>v-1\<^esub> 0\<^sub>B\<close>;
    • DEEPEN otherwise: \<open>b = a\<close> with its LAST principal's subtree recursively
      transformed by the same rule (one spine level deeper).
  Self-similarity (the irreducible core).  By the §7.3 \<open>Trans\<close>/\<open>Mark\<close> recursion
  (monoT branch: \<open>Trans M' = unflatBT(s \<frown> flat c2 \<frown> b'),  c2 = D\<^bsub>v\<^esub>(t2 +\<^sub>B D\<^bsub>e1j1\<^esub> 0\<^sub>B)\<close>
  substituted for the marked subterm \<open>c1 = Mark (Pred M') jm1\<close>), the trailing subtree
  of \<open>bd q\<close> (\<open>= bpHeadT (Mark (M[q]) jm1)\<close>) equals \<open>bd (q-1)\<close> (python: \<open>P0 = bd(q-1)\<close>
  55/56).  So the column-walk of block \<open>B\<^bsub>q\<^esub>\<close> acting on \<open>bd q\<close>'s trailing subtree IS
  the surgery at \<open>q-1\<close> acting on the inner slice \<open>Y\<^bsub>q-1\<^esub> = seg (M[q-1]) jm1 (\<dots>)\<close>
  one spine level down.  Hence surgery(q) reduces to surgery(q-1) — the OUTER
  induction on q (@{thm [source] funpow_closed_of_step_from2} supplies the q-1 body
  IH); the naive m-induction on columns is circular (its m=0 base = body(q-1)).
  CLOSING LEMMA NEEDED (does not exist in the base): an inner-slice / subtree-readback
  BRIDGE \<open>a = bpHeadT (Trans Z) \<and> b = bpHeadT (Trans (Z \<frown> [col']))\<close> identifying the
  deepen-case trailing subtree \<open>a\<close> with \<open>Trans\<close> of the marked subterm's own pairseq
  \<open>Z\<close> (= \<open>Y\<^bsub>q-1\<^esub>\<close> at the top level), so the keystone applies recursively at \<open>Z\<close>.
  With that bridge, @{thm [source] m_8_5_deepen_step} (shape) + the bridge (value) +
  the outer-q induction assemble the \<open>surgery\<close> hypothesis of @{thm [source]
  m_8_5_markstep_of_surgery}, hence the ladder \<Rightarrow> \<open>m_8_5_TransCondV_descend\<close>.
  SECONDARY residual — the geometric input \<open>par: parent M' 0 (Lng M'-1) > TrMax M'\<close>
  feeding @{thm [source] m_8_5_appended_col_deepen} (148/148 empirically): closable
  but laborious from the oper-append trunk machinery (@{thm [source]
  TrMax_seg_oper_d1pos_eq}, @{thm [source] oper_parent1_readback}); fully closes
  sub-fact (A) = deepen-only.\<close>


text \<open>§8.5 BRIDGE brick (1) — the COMMON-PREFIX body readback.  The deepen-case
  common prefix \<open>t\<close> of the surgery walk (the \<open>t\<^sub>2\<close> of the period context
  \<open>C x = t\<^sub>2 +\<^sub>B D\<^bsub>v-1\<^esub> x\<close>) reads back as \<open>bpHeadT (Trans Z')\<close> of the inner slice
  \<open>Z' = seg (Pred M) (transJm1 M) (Lng (Pred M) - 1)\<close>.  This is immediate from the
  §7.4 keystone @{thm [source] m_7_4_Mark_Trans_repr} applied to \<open>Pred M\<close> at the
  basepoint \<open>transJm1 M\<close> (\<open>transT2 M = bpHeadT (transC1 M)\<close>,
  \<open>transC1 M = Mark (Pred M) (transJm1 M)\<close>).  It converts the producer's \<open>t\<^sub>2\<close>
  (defined as a \<open>Mark\<close>-head) into a \<open>Trans\<close>-of-slice head, the first half of the
  subtree-readback BRIDGE.\<close>

lemma m_8_5_transT2_readback:
  fixes M :: pairseq
  assumes mk: "(Pred M, transJm1 M) \<in> Marked"
    and pr: "Pred M \<in> RT_PS"
    and rng: "transJm1 M < Lng (Pred M) - 1"
  shows "transT2 M = bpHeadT (Trans (seg (Pred M) (transJm1 M) (Lng (Pred M) - 1)))"
proof -
  have c1: "transC1 M = Mark (Pred M) (transJm1 M)" by (simp add: transC1_def)
  have "transT2 M = bpHeadT (Mark (Pred M) (transJm1 M))"
    using c1 by (simp add: transT2_def)
  also have "Mark (Pred M) (transJm1 M)
               = Trans (seg (Pred M) (transJm1 M) (Lng (Pred M) - 1))"
    by (rule m_7_4_Mark_Trans_repr[OF mk pr rng])
  finally show ?thesis .
qed


text \<open>§8.5 BRIDGE brick (2) — the PARTIAL-ITERATE slice readback (M-agnostic).
  The surgery walk forms the partial-block hosts \<open>Y \<frown> take m B\<close>
  (\<open>Y = seg (M[q]) jm1 (Lng (M[q]) - 1)\<close>); each one reads back as \<open>Mark\<close> of the
  partial iterate \<open>X \<frown> B'\<close> (\<open>X = M[q]\<close>, \<open>B' = take m B\<close>).  This is the
  M-agnostic generalisation of @{thm [source] Mark_iterate_slice_append} (which is
  the special case \<open>X \<frown> B' = M[Suc p]\<close> a FULL block): for ANY split \<open>X \<frown> B'\<close> with
  basepoint \<open>jm1 \<le> Lng X\<close>, @{thm [source] m_7_4_Mark_Trans_repr} on \<open>X \<frown> B'\<close>
  combined with the slice-extension @{thm [source] seg_to_last_append}
  (\<open>seg (X \<frown> B') jm1 end = seg X jm1 (Lng X - 1) \<frown> B'\<close>) gives
  \<open>Mark (X \<frown> B') jm1 = Trans (seg X jm1 (Lng X - 1) \<frown> B')\<close>.  This is what turns
  every \<open>Trans (slice \<frown> columns)\<close> in the walk into \<open>Mark\<close> of a partial iterate —
  the necessary first move of the subtree-readback BRIDGE (it identifies the inner
  \<open>Z = seg X jm1 (Lng X - 1) \<frown> B'\<close> with the \<open>Mark\<close> of \<open>X \<frown> B'\<close>).\<close>

lemma m_8_5_Mark_slice_block_readback:
  fixes X B :: pairseq and jm1 :: nat
  assumes mk: "(X @ B, jm1) \<in> Marked"
    and MR: "X @ B \<in> RT_PS"
    and rng: "jm1 < Lng (X @ B) - 1"
    and Xne: "0 < Lng X"
    and jle: "jm1 \<le> Lng X"
  shows "Mark (X @ B) jm1 = Trans (seg X jm1 (Lng X - 1) @ B)"
proof -
  have "Mark (X @ B) jm1 = Trans (seg (X @ B) jm1 (Lng (X @ B) - 1))"
    by (rule m_7_4_Mark_Trans_repr[OF mk MR rng])
  also have "seg (X @ B) jm1 (Lng (X @ B) - 1) = seg X jm1 (Lng X - 1) @ B"
    by (rule seg_to_last_append[OF Xne jle])
  finally show ?thesis .
qed


text \<open>§8.5 BRIDGE — the |B|-COMPOSITION spine-walk (M-agnostic, the master-key
  structural skeleton).  Composes the per-column DEEPEN steps over the whole
  appended block \<open>B\<close> into the block-level spine identity.  The SHAPE half
  (@{thm [source] m_8_5_deepen_step} / @{thm [source] m_8_5_appended_col_deepen})
  fixes the prefix-and-head form \<open>Trans (Y \<frown> take m B) = D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> (P m))\<close>;
  the per-column VALUE step \<open>step\<close> (the subtree-readback BRIDGE, supplying
  \<open>P (Suc m)\<close> from \<open>P m\<close>) advances the trailing subtree one column.  This lemma
  is the clean \<open>take m B\<close>-induction that walks the spine from \<open>m = 0\<close> (\<open>base\<close>:
  \<open>Trans Y = D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> (P 0))\<close>, \<open>P 0 = bd (q-1)\<close>) to \<open>m = Lng B\<close>,
  giving \<open>Trans (Y \<frown> B) = D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> (P (Lng B)))\<close>.  The surgery
  \<open>Trans (Y \<frown> B) = D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> (bpHeadT (Trans Y)))\<close> is then exactly this
  with the endpoint identity \<open>P (Lng B) = bpHeadT (Trans Y)\<close> (= the bridge at
  \<open>m = Lng B\<close> composed with the slice-extension \<open>Y\<^sub>q = Y\<^bsub>q-1\<^esub> \<frown> B\<^bsub>q-1\<^esub>\<close>, supplied by
  the OUTER-q induction).  Discharges the |B|-composition; leaves exactly the
  per-column \<open>step\<close> (the irreducible keystone-deepen matching) and the endpoint.\<close>

text \<open>§8.5 SURGERY value-step — the CONCRETE spine function \<open>P\<close>.  The trailing-leaf
  subtree extractor: strip the outer head (\<open>bpHeadT\<close>), take the LAST principal of the
  body (\<open>last (PB \<cdot>)\<close>), and read its subtree (\<open>bpHeadT\<close>).  Applied to a term in spine
  form \<open>D\<^bsub>e\<^esub>(t +\<^sub>B D\<^bsub>h\<^esub> z)\<close> it returns exactly the deepest slot \<open>z\<close>
  (lemma \<open>m_8_5_spineLeaf_Dpt_addBT\<close>).  This is the concrete witness
  \<open>P m := spineLeaf (Trans (Y \<frown> take m B))\<close> that makes the per-column \<open>step\<close> of
  \<open>m_8_5_surgery_spine_compose\<close> hold definitionally once the SHAPE
  (@{thm [source] m_8_5_appended_col_deepen}) pins the deepened subtree.\<close>

definition spineLeaf :: "BT \<Rightarrow> BT" where
  "spineLeaf T = bpHeadT (last (PB (bpHeadT T)))"

lemma m_8_5_spineLeaf_Dpt_addBT:
  "spineLeaf (Dpt (enat e) (t +\<^sub>B Dpt (enat h) z)) = z"
proof -
  have hb: "bpHeadT (Dpt (enat e) (t +\<^sub>B Dpt (enat h) z)) = t +\<^sub>B Dpt (enat h) z"
    by simp
  have pdz: "PB (Dpt (enat h) z) = [Trm [DB (enat h) z]]" by (simp add: PB_def)
  have pb: "PB (t +\<^sub>B Dpt (enat h) z) = PB t @ [Trm [DB (enat h) z]]"
    using PB_addBT_app[of t "Dpt (enat h) z"] pdz by simp
  show ?thesis by (simp add: spineLeaf_def hb pb)
qed

text \<open>§8.5 SURGERY value-step ALGEBRAIC GLUE (sub-fact B, cancellation core).
  Two decompositions of \<open>Trans X\<close> — the spine invariant form \<open>D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> a)\<close>
  (the IH at column \<open>m\<close>) and the keystone-deepen SHAPE form \<open>D\<^bsub>e10'\<^esub>(t +\<^sub>B D\<^bsub>h\<^esub> a\<^sub>0)\<close>
  (@{thm [source] m_8_5_appended_col_deepen}) — are FORCED to coincide head-for-head
  by the single-principal cancellation (@{thm [source] Dpt_addBT_right_cancel} family):
  \<open>e10 = e10'\<close>, \<open>t\<^sub>2 = t\<close>, \<open>vm1 = h\<close>.  Substituting those equalities into the SHAPE
  output \<open>Trans M' = D\<^bsub>e10'\<^esub>(t +\<^sub>B D\<^bsub>h\<^esub> b)\<close> re-expresses the deepened term in the spine
  invariant's frame \<open>D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> b)\<close>.  This is the algebraic half of the
  per-column \<open>step\<close>: it PINS the deepened subtree \<open>b\<close> into the spine slot, so
  \<open>P (Suc m) := b\<close> advances the invariant.  The remaining (geometric) half is supplying
  the SHAPE lemma's hypotheses at the partial host \<open>X = Y \<frown> take m B\<close>.\<close>

lemma m_8_5_spine_step_glue:
  fixes X M' :: pairseq and t2 t a a0 b :: BT and e10 e10' vm1 h :: nat
  assumes ih: "Trans X = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) a)"
    and shX: "Trans X = Dpt (enat e10') (t +\<^sub>B Dpt (enat h) a0)"
    and shM: "Trans M' = Dpt (enat e10') (t +\<^sub>B Dpt (enat h) b)"
  shows "Trans M' = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) b)"
proof -
  have eq: "Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) a)
              = Dpt (enat e10') (t +\<^sub>B Dpt (enat h) a0)"
    using ih shX by simp
  have headeq: "e10 = e10'" using eq by simp
  have bodyeq: "t2 +\<^sub>B Dpt (enat vm1) a = t +\<^sub>B Dpt (enat h) a0" using eq by simp
  have listeq: "untrm t2 @ [DB (enat vm1) a] = untrm t @ [DB (enat h) a0]"
    using bodyeq by (cases t2; cases t) simp_all
  have lasteq: "DB (enat vm1) a = DB (enat h) a0"
    using listeq by (simp add: append_eq_append_conv)
  hence hh: "h = vm1" by simp
  have "untrm t2 = untrm t" using listeq by (simp add: append_eq_append_conv)
  hence tt: "t2 = t" by (cases t2; cases t) simp_all
  show ?thesis using shM headeq hh tt by simp
qed

text \<open>§8.5 SURGERY value-step — the per-column \<open>step\<close> REDUCED to the geometric input.
  This is the drop-in for the \<open>step\<close> hypothesis of \<open>m_8_5_surgery_spine_compose\<close>
  at the concrete witness \<open>P m = spineLeaf (Trans
  (Y \<frown> take m B))\<close>.  Appending the column \<open>B ! m\<close> to the partial host \<open>Y \<frown> take m B\<close>
  is \<open>Y \<frown> take (Suc m) B\<close> (@{thm [source] take_Suc_conv_app_nth}); the SHAPE collapse
  (@{thm [source] m_8_5_appended_col_deepen}) gives a common-prefix-body deepen
  \<open>a \<rightarrow> b\<close>, the GLUE (@{thm [source] m_8_5_spine_step_glue}) pins it into the spine
  frame, and \<open>spineLeaf\<close> reads \<open>P (Suc m) = b\<close> back off the result
  (@{thm [source] m_8_5_spineLeaf_Dpt_addBT}).  The ONLY residuals are the
  per-column GEOMETRIC inputs on the partial host \<open>M' = (Y \<frown> take m B) \<frown> [B ! m]\<close>:
  reduced-standard membership (\<open>MR\<close>/\<open>MP\<close>), nonempty last branch (\<open>Brne\<close>), depth
  (\<open>j1gt\<close>), the row-0 parent-past-trunk condition (\<open>par\<close>, the deepen trigger; 148/148
  empirically), and the constant outer head \<open>entry M' 1 0 = e10\<close>.\<close>

lemma m_8_5_surgery_spine_step:
  fixes Y B :: pairseq and t2 :: BT and e10 vm1 m :: nat
  assumes mlt: "m < Lng B"
    and Yne: "0 < Lng (Y @ take m B)"
    and MR: "(Y @ take m B) @ [B ! m] \<in> RT_PS"
    and MP: "(Y @ take m B) @ [B ! m] \<in> PT_PS"
    and Brne: "Br ((Y @ take m B) @ [B ! m]) \<noteq> []"
    and j1gt: "Lng ((Y @ take m B) @ [B ! m]) - 1 > 1"
    and par: "parent ((Y @ take m B) @ [B ! m]) 0 (Lng ((Y @ take m B) @ [B ! m]) - 1)
                > TrMax ((Y @ take m B) @ [B ! m])"
    and e10eq: "entry ((Y @ take m B) @ [B ! m]) 1 0 = e10"
    and ih: "Trans (Y @ take m B)
               = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take m B))))"
  shows "Trans (Y @ take (Suc m) B)
           = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take (Suc m) B))))"
proof -
  have Msplit: "Y @ take (Suc m) B = (Y @ take m B) @ [B ! m]"
    using mlt by (simp add: take_Suc_conv_app_nth)
  from m_8_5_appended_col_deepen[where X = "Y @ take m B" and col = "B ! m",
         OF Yne MR MP Brne j1gt par]
  obtain t h a bb where
    sh2: "Trans (Y @ take m B)
            = Dpt (enat (entry ((Y @ take m B) @ [B ! m]) 1 0)) (t +\<^sub>B Dpt (enat h) a)"
    and sh3: "Trans ((Y @ take m B) @ [B ! m])
            = Dpt (enat (entry ((Y @ take m B) @ [B ! m]) 1 0)) (t +\<^sub>B Dpt (enat h) bb)"
    by blast
  have shX: "Trans (Y @ take m B) = Dpt (enat e10) (t +\<^sub>B Dpt (enat h) a)"
    using sh2 e10eq by simp
  have shM: "Trans ((Y @ take m B) @ [B ! m]) = Dpt (enat e10) (t +\<^sub>B Dpt (enat h) bb)"
    using sh3 e10eq by simp
  have glued: "Trans ((Y @ take m B) @ [B ! m]) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) bb)"
    by (rule m_8_5_spine_step_glue[OF ih shX shM])
  have sL: "spineLeaf (Trans ((Y @ take m B) @ [B ! m])) = bb"
    using glued by (simp add: m_8_5_spineLeaf_Dpt_addBT)
  have final: "Trans ((Y @ take m B) @ [B ! m])
        = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1)
              (spineLeaf (Trans ((Y @ take m B) @ [B ! m]))))"
    by (subst sL) (rule glued)
  thus ?thesis using Msplit by simp
qed

lemma m_8_5_surgery_spine_compose:
  fixes Y B :: pairseq and t2 :: BT and e10 vm1 :: nat and P :: "nat \<Rightarrow> BT"
  assumes base: "Trans Y = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (P 0))"
    and step: "\<And>m. m < Lng B
                 \<Longrightarrow> Trans (Y @ take m B) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (P m))
                 \<Longrightarrow> Trans (Y @ take (Suc m) B)
                       = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (P (Suc m)))"
  shows "Trans (Y @ B) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (P (Lng B)))"
proof -
  have gen: "\<And>m. m \<le> Lng B
               \<longrightarrow> Trans (Y @ take m B) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (P m))"
  proof -
    fix m
    show "m \<le> Lng B
            \<longrightarrow> Trans (Y @ take m B) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (P m))"
    proof (induct m)
      case 0
      have "Y @ take 0 B = Y" by simp
      thus ?case using base by simp
    next
      case (Suc m)
      show ?case
      proof
        assume sle: "Suc m \<le> Lng B"
        have mlt: "m < Lng B" using sle by simp
        have mle: "m \<le> Lng B" using sle by simp
        have ih: "Trans (Y @ take m B) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (P m))"
          using Suc.hyps mle by simp
        show "Trans (Y @ take (Suc m) B)
                = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (P (Suc m)))"
          by (rule step[OF mlt ih])
      qed
    qed
  qed
  have "Trans (Y @ take (Lng B) B)
          = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (P (Lng B)))"
    using gen[of "Lng B"] by simp
  thus ?thesis by simp
qed

text \<open>§8.5 SURGERY — ASSEMBLED from the per-column step + spine composition, leaving
  EXACTLY the three genuine residuals.  Instantiating @{thm [source]
  m_8_5_surgery_spine_compose} at the concrete witness \<open>P m = spineLeaf (Trans
  (Y \<frown> take m B))\<close>, the per-column \<open>step\<close> is discharged uniformly by
  @{thm [source] m_8_5_surgery_spine_step} (from the per-\<open>m\<close> GEOMETRIC inputs), the
  composition walks the whole block, and the ENDPOINT identity \<open>spineLeaf (Trans
  (Y \<frown> B)) = bpHeadT (Trans Y)\<close> rewrites the trailing spine slot back to the head
  body of \<open>Trans Y\<close>.  The conclusion is EXACTLY the \<open>surgery\<close> hypothesis of
  @{thm [source] m_8_5_markstep_of_surgery} with \<open>u = e10\<close> and
  \<open>F = (\<lambda>x. t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> x)\<close> (one net \<open>C\<close> per appended block).  The three residuals:
    \<^item> \<open>base\<close>: \<open>Trans Y = D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> (spineLeaf (Trans Y)))\<close> — the spine
       shape of the slice's own \<open>Trans\<close> (\<open>n=1\<close> base / §7.4 Mark representation);
    \<^item> \<open>geom\<close> (seven per-\<open>m\<close> facts): the partial-host membership + parent-past-trunk
       deepen triggers (148/148 empirically);
    \<^item> \<open>endpoint\<close>: the SELF-SIMILAR bridge result (\<open>P\<^bsup>(q)\<^esup>\<^sub>m = body of the (q-1)-walk\<close>,
       203/204, the one miss = the \<open>q=2\<close> base) — the genuine irreducible core,
       provable only by the OUTER-\<open>q\<close> induction (the q-1 surgery feeds the m=0 base).
  This DISCHARGES the |B|-composition and the algebraic value-pinning completely;
  the residual content is concentrated in \<open>endpoint\<close> + \<open>geom\<close> (the self-similar
  recurrence \<open>P\<^bsup>(q)\<^esup>\<^sub>m = C (P\<^bsup>(q-1)\<^esup>\<^sub>m)\<close>, the genuine wall).\<close>

lemma m_8_5_surgery_of_geom_endpoint:
  fixes Y B :: pairseq and t2 :: BT and e10 vm1 :: nat
  assumes base: "Trans Y = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans Y)))"
    and gYne: "\<And>m. m < Lng B \<Longrightarrow> 0 < Lng (Y @ take m B)"
    and gMR: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> RT_PS"
    and gMP: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> PT_PS"
    and gBrne: "\<And>m. m < Lng B \<Longrightarrow> Br ((Y @ take m B) @ [B ! m]) \<noteq> []"
    and gj1gt: "\<And>m. m < Lng B \<Longrightarrow> Lng ((Y @ take m B) @ [B ! m]) - 1 > 1"
    and gpar: "\<And>m. m < Lng B \<Longrightarrow> parent ((Y @ take m B) @ [B ! m]) 0
                 (Lng ((Y @ take m B) @ [B ! m]) - 1) > TrMax ((Y @ take m B) @ [B ! m])"
    and ge10: "\<And>m. m < Lng B \<Longrightarrow> entry ((Y @ take m B) @ [B ! m]) 1 0 = e10"
    and endpoint: "spineLeaf (Trans (Y @ B)) = bpHeadT (Trans Y)"
  shows "Trans (Y @ B) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Y)))"
proof -
  have step: "\<And>m. m < Lng B \<Longrightarrow>
        Trans (Y @ take m B)
          = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take m B)))) \<Longrightarrow>
        Trans (Y @ take (Suc m) B)
          = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take (Suc m) B))))"
  proof -
    fix m
    assume m: "m < Lng B"
      and ih: "Trans (Y @ take m B)
                 = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take m B))))"
    show "Trans (Y @ take (Suc m) B)
            = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take (Suc m) B))))"
      by (rule m_8_5_surgery_spine_step
            [OF m gYne[OF m] gMR[OF m] gMP[OF m] gBrne[OF m] gj1gt[OF m]
                gpar[OF m] ge10[OF m] ih])
  qed
  have base': "Trans Y
        = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take 0 B))))"
    using base by simp
  have comp: "Trans (Y @ B)
        = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take (Lng B) B))))"
    by (rule m_8_5_surgery_spine_compose
          [where P = "\<lambda>m. spineLeaf (Trans (Y @ take m B))", OF base' step])
  have comp2: "Trans (Y @ B)
        = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ B))))"
    using comp by simp
  show ?thesis by (subst comp2) (simp add: endpoint)
qed

text \<open>§8.5 SURGERY — \<open>base\<close> is NOT an independent §7.4 fact: it IS \<open>surgery(q-1)\<close>.
  EMPIRICALLY DECISIVE (python/base_probe): the spine shape \<open>base(q)\<close>
  (\<open>bd q\<close>'s last principal has head \<open>vm1\<close> AND its prefix \<open>= t\<^sub>2\<close>) FAILS for \<open>q=1\<close>
  (0/28: \<open>bd 1 = t\<^sub>2\<close> need not end in \<open>D\<^bsub>vm1\<^esub>\<close>) and HOLDS for \<open>q\<ge>2\<close> (28/28) — exactly
  tracking "one block already applied".  The reason is structural: for \<open>q\<ge>2\<close>,
  \<open>bd q = C (bd (q-1)) = t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub>(bd (q-1))\<close> (= \<open>surgery(q-1)\<close>), so its last
  principal is \<open>D\<^bsub>vm1\<^esub>(bd (q-1))\<close> and its prefix is exactly \<open>t\<^sub>2\<close>; \<open>spineLeaf\<close> then
  reads back \<open>bd (q-1)\<close>.  Hence \<open>base(q)\<close> is a one-line consequence of the previous
  iterate's surgery — there is no §7.4 shortcut.  This is the outer-\<open>q\<close> induction's
  base wiring: the IH \<open>surgery(q-1)\<close> supplies \<open>base(q)\<close>.\<close>

lemma m_8_5_base_of_surgery_pred:
  fixes Y :: pairseq and t2 z :: BT and e10 vm1 :: nat
  assumes prev: "Trans Y = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) z)"
  shows "Trans Y = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans Y)))"
proof -
  have "spineLeaf (Trans Y) = z" using prev by (simp add: m_8_5_spineLeaf_Dpt_addBT)
  thus ?thesis using prev by simp
qed

text \<open>§8.5 SURGERY — the OUTER-\<open>q\<close> INDUCTION STEP, fully assembled.  Combines
  \<open>m_8_5_base_of_surgery_pred\<close> (the IH \<open>surgery(q-1)\<close> supplies \<open>base(q)\<close>) with
  \<open>m_8_5_surgery_of_geom_endpoint\<close>: it derives \<open>surgery(q)\<close> from \<open>surgery(q-1)\<close>
  (\<open>prev\<close>: \<open>Trans Y = D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> z)\<close>, where \<open>Y = Y\<^bsub>q\<^esub> = Y\<^bsub>q-1\<^esub> \<frown> B\<^bsub>q-1\<^esub>\<close>
  and \<open>z = bd (q-1)\<close>), the per-column GEOMETRIC inputs, and the ENDPOINT.  After this,
  the SOLE residuals of the entire surgery are: (i) \<open>geom\<close> — slice-host membership,
  which empirically FAILS 8/148 (the slice formulation is geometrically lossy; the
  faithful fix walks the FULL-prefix hosts \<open>M[q] \<frown> take m B\<close> (148/148) via the readback
  + a \<open>Mark\<close>-append keystone that does not yet exist; candidate engine
  @{thm [source] Mark_monoT_via_Pred}, the interior-Mark-under-\<open>Pred\<close> recurrence); and
  (ii) \<open>endpoint\<close> — the self-similar BRIDGE \<open>P\<^bsup>(q)\<^esup>\<^sub>m = C (P\<^bsup>(q-1)\<^esup>\<^sub>m)\<close> (102/102 for
  \<open>q=3\<close>), whose \<open>m\<close>-induction has base \<open>= surgery(q-2)\<close> but STEP \<open>= the keystone-deepen
  COMMUTATION\<close> \<open>g (C x) = C (g x)\<close> relating two different hosts — the master-key wall.\<close>

text \<open>§8.5 ENDPOINT ENGINE — the scb-context SUBSTITUTION operator and its
  COMMUTATION with the period wrapper \<open>C\<close>.  The interior-\<open>Mark\<close> recurrence
  (@{thm [source] Mark_monoT_via_Pred}) exposes \<open>Mark N jm1 = G (Mark (Pred N) jm1)\<close>
  where \<open>G\<close> substitutes the marked principal \<open>c\<^sub>1\<close> by the period block \<open>c\<^sub>2\<close> in the
  scb-context: \<open>G x = unflatBT (s\<^sub>x \<frown> flat c\<^sub>2 \<frown> b\<^sub>x)\<close>, \<open>(s\<^sub>x,b\<^sub>x)\<close> the scb-decomposition
  of \<open>x\<close> at \<open>c\<^sub>1\<close>.  The self-similar BRIDGE step is the COMMUTATION
  \<open>G (pre +\<^sub>B D\<^bsub>h\<^esub> x) = pre +\<^sub>B D\<^bsub>h\<^esub> (G x)\<close>: substituting deep inside \<open>x\<close> commutes with
  wrapping one more period context around it.  Mechanism: the scb-context of
  \<open>pre +\<^sub>B D\<^bsub>h\<^esub> x\<close> at \<open>c\<^sub>1\<close> is the \<open>C\<close>-shifted context of \<open>x\<close> at \<open>c\<^sub>1\<close> (prefix gains the
  \<open>liftS\<close> head, suffix gains one \<open>RP\<close>; @{thm [source] scb_addBT_left}), so the
  substitution + \<open>unflatBT\<close> factor through the wrapper.  This is the keystone-deepen
  commutation \<open>g (C x) = C (g x)\<close> at the explicit-\<open>scb\<close> level, the master-key
  bridge's irreducible step.\<close>

definition scbSubst :: "BT \<Rightarrow> BT \<Rightarrow> BT \<Rightarrow> BT" where
  "scbSubst c1 c2 x =
     unflatBT (fst (SOME sb. scb_decomp x (fst sb) (flatBT c1) (snd sb))
               @ flatBT c2
               @ snd (SOME sb. scb_decomp x (fst sb) (flatBT c1) (snd sb)))"

lemma scb_SOME_eq:
  assumes d: "scb_decomp t s c b" and tne: "t \<noteq> Trm []"
  shows "(SOME sb. scb_decomp t (fst sb) c (snd sb)) = (s, b)"
proof (rule some_equality)
  show "scb_decomp t (fst (s, b)) c (snd (s, b))" using d by simp
next
  fix sb assume h: "scb_decomp t (fst sb) c (snd sb)"
  have "fst sb = s \<and> snd sb = b"
    using m_7_2_scb_unique_sb[OF h d tne] by simp
  thus "sb = (s, b)" by (cases sb) auto
qed

lemma scbSubst_eq:
  assumes d: "scb_decomp t s (flatBT c1) b" and tne: "t \<noteq> Trm []"
  shows "scbSubst c1 c2 t = unflatBT (s @ flatBT c2 @ b)"
  using scb_SOME_eq[OF d tne] by (simp add: scbSubst_def)

lemma flat_addBT_Dpt:
  assumes prene: "untrm pre \<noteq> []"
  shows "flatBT (pre +\<^sub>B Dpt (enat h) G)
           = liftS pre (Dsym (enat h) # flatBT G) @ [RP]"
proof -
  obtain p ps where ps: "untrm pre = p # ps" using prene by (cases "untrm pre") auto
  obtain q rest where qr: "ps @ [DB (enat h) G] = q # rest"
    by (cases "ps @ [DB (enat h) G]") auto
  have addeq: "pre +\<^sub>B Dpt (enat h) G = Trm (p # q # rest)"
    using ps qr by (cases pre) simp
  have "flatBT (pre +\<^sub>B Dpt (enat h) G)
        = LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # rest))) @ [RP]"
    using addeq by simp
  also have "concat (map (\<lambda>r. CM # flatBP r) (q # rest))
        = concat (map (\<lambda>r. CM # flatBP r) (ps @ [DB (enat h) G]))"
    using qr by simp
  also have "\<dots> = concat (map (\<lambda>r. CM # flatBP r) ps) @ CM # Dsym (enat h) # flatBT G"
    by simp
  finally have flatL: "flatBT (pre +\<^sub>B Dpt (enat h) G)
        = LP # flatBP p @ concat (map (\<lambda>r. CM # flatBP r) ps)
              @ CM # Dsym (enat h) # flatBT G @ [RP]"
    by simp
  have lifte: "liftS pre (Dsym (enat h) # flatBT G) @ [RP]
        = LP # flatBP p @ concat (map (\<lambda>r. CM # flatBP r) ps)
              @ CM # Dsym (enat h) # flatBT G @ [RP]"
    using ps by (simp add: liftS_def)
  show ?thesis using flatL lifte by simp
qed

lemma m_8_5_scbSubst_addBT_commute:
  fixes pre c1 c2 x :: BT and h :: nat and sx bx :: "Sym list"
  assumes mk: "scb_decomp x sx (flatBT c1) bx"
    and xnz: "x \<noteq> Trm []"
    and c2p: "isPTB_str (flatBT c2)"
    and prene: "untrm pre \<noteq> []"
  shows "scbSubst c1 c2 (pre +\<^sub>B Dpt (enat h) x)
           = pre +\<^sub>B Dpt (enat h) (scbSubst c1 c2 x)"
proof -
  \<comment> \<open>unpack the scb-decomposition of \<open>x\<close> at \<open>c\<^sub>1\<close>\<close>
  have flatx: "flatBT x = sx @ flatBT c1 @ bx"
    using mk by (simp add: scb_decomp_def)
  have ptc1: "isPTB_str (flatBT c1)" using mk xnz by (simp add: scb_decomp_def)
  have rbx: "\<forall>z \<in> set bx. z = RP" using mk by (simp add: scb_decomp_def)
  obtain p1 where p1: "flatBT c1 = flatBP p1" using ptc1 by (auto simp: isPTB_str_def)
  obtain p2 where p2: "flatBT c2 = flatBP p2" using c2p by (auto simp: isPTB_str_def)
  \<comment> \<open>scb of \<open>D\<^bsub>h\<^esub> x\<close> at \<open>c\<^sub>1\<close>, then transport to \<open>pre +\<^sub>B D\<^bsub>h\<^esub> x\<close>\<close>
  have dhxne: "Dpt (enat h) x \<noteq> Trm []" by simp
  have scbDhx: "scb_decomp (Dpt (enat h) x) (Dsym (enat h) # sx) (flatBT c1) bx"
    unfolding scb_decomp_def using flatx ptc1 rbx by simp
  have dhx1: "length (untrm (Dpt (enat h) x)) = 1" by simp
  have scbT: "scb_decomp (pre +\<^sub>B Dpt (enat h) x)
                (liftS pre (Dsym (enat h) # sx)) (flatBT c1) (bx @ [RP])"
    by (rule scb_addBT_left[OF scbDhx dhx1 prene])
  have prexne: "pre +\<^sub>B Dpt (enat h) x \<noteq> Trm []"
    using prene by (cases pre) simp
  \<comment> \<open>LHS via the transported scb\<close>
  have LHS: "scbSubst c1 c2 (pre +\<^sub>B Dpt (enat h) x)
        = unflatBT (liftS pre (Dsym (enat h) # sx) @ flatBT c2 @ (bx @ [RP]))"
    by (rule scbSubst_eq[OF scbT prexne])
  \<comment> \<open>flat of the inner substitution result\<close>
  have GxV: "scbSubst c1 c2 x = unflatBT (sx @ flatBT c2 @ bx)"
    by (rule scbSubst_eq[OF mk xnz])
  have fx1: "flatBT x = sx @ flatBP p1 @ bx" using flatx p1 by simp
  obtain t' where t': "flatBT t' = sx @ flatBP p2 @ bx"
    using scbimg_image_BT[OF fx1 rbx, of p2] by blast
  have flatGx: "flatBT (scbSubst c1 c2 x) = sx @ flatBT c2 @ bx"
    using GxV t' p2 by (metis unflatBT_flat)
  \<comment> \<open>RHS flat via the wrapper computation\<close>
  have flatRHS: "flatBT (pre +\<^sub>B Dpt (enat h) (scbSubst c1 c2 x))
        = liftS pre (Dsym (enat h) # sx) @ flatBT c2 @ (bx @ [RP])"
    using flat_addBT_Dpt[OF prene, of h "scbSubst c1 c2 x"] flatGx
    by (simp add: liftS_def)
  show ?thesis
    using LHS flatRHS by (metis unflatBT_flat)
qed

text \<open>§6.7 take-closure of standard form (item (a), the foundational unblocker for the
  full-prefix surgery walk).  A prefix \<open>take k M\<close> of a standard-form sequence is
  standard: immediate from @{thm [source] m_6_7_standard_prefix} (the 始切片 hereditary
  lemma) once \<open>seg M 0 (k-1) = take k M\<close> (@{thm [source] seg_0_eq_take}); the
  \<open>k \<ge> Lng M\<close> case is \<open>take_all\<close>.  Corollaries: \<open>take k M \<in> RT_PS / T_PS\<close>.\<close>

lemma ST_PS_take:
  assumes M: "M \<in> ST_PS" and k: "0 < k"
  shows "take k M \<in> ST_PS"
proof (cases "k < Lng M")
  case True
  have kL: "k \<le> Lng M" using True by simp
  have sk: "Suc (k - 1) = k" using k by simp
  have b1: "Suc (k - 1) \<le> Lng M" using sk kL by simp
  have seg: "seg M 0 (k - 1) = take (Suc (k - 1)) M" by (rule seg_0_eq_take[OF b1])
  have jle: "k - 1 \<le> Lng M - 1" using kL by simp
  have "seg M 0 (k - 1) \<in> ST_PS" by (rule m_6_7_standard_prefix[OF M jle])
  thus ?thesis using seg sk by simp
next
  case False
  hence "Lng M \<le> k" by simp
  hence "take k M = M" by simp
  thus ?thesis using M by simp
qed

lemma RT_PS_take:
  assumes "M \<in> ST_PS" and "0 < k"
  shows "take k M \<in> RT_PS"
  using ST_PS_take[OF assms] m_6_7_ST_PS_subseteq_RT_PS by blast

lemma T_PS_take:
  assumes "M \<in> ST_PS" and "0 < k"
  shows "take k M \<in> T_PS"
  by (rule ST_PS_T_PS[OF ST_PS_take[OF assms]])

text \<open>§8.5 ENDPOINT ENGINE — the interior-\<open>Mark\<close> RECURRENCE \<open>Mark M n = G (Mark (Pred M) n)\<close>
  in scbSubst form, extracted as a standalone fact from the \<open>mark_raw\<close> step internal
  to @{thm [source] Mark_monoT_via_Pred}.  In the \<open>monoT\<close>, \<open>t\<^sub>1 \<noteq> 0\<close> regime, for an
  interior index \<open>n < Lng M - 1\<close> whose predecessor-mark sits in the marked-block
  context \<open>(Mark (Pred M) n, transC1 M) \<in> MarkedB\<close>, the \<open>Mark\<close> recursion exposes
  \<open>Mark M n = scbSubst (transC1 M) (transC2 M) (Mark (Pred M) n)\<close>: it substitutes the
  marked principal \<open>c\<^sub>1 = transC1 M\<close> by the period block \<open>c\<^sub>2 = transC2 M\<close> in the
  scb-context of \<open>Mark (Pred M) n\<close>.  This is the operator \<open>G\<close> whose COMMUTATION with the
  period wrapper (@{thm [source] m_8_5_scbSubst_addBT_commute}) drives the self-similar
  endpoint bridge.\<close>

lemma m_8_5_Mark_scbSubst_step:
  fixes M :: pairseq and n :: nat
  assumes MR: "M \<in> RT_PS" and mono: "monoT M" and L: "1 < Lng M"
    and t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B"
    and nlt: "n < Lng M - 1"
    and mk: "(Mark (Pred M) n, transC1 M) \<in> MarkedB"
  shows "Mark M n = scbSubst (transC1 M) (transC2 M) (Mark (Pred M) n)"
proof -
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  have domK: "\<And>k. Trans_Mark_dom (Inr (M, k))" by (rule m_7_3_Mark_welldef[OF MR])
  let ?bv = "entry M 1 (Lng M - 1)"
  define jp where "jp = parent M 0 (Lng M - 1)"
  define c1 where "c1 = Mark (Pred M) (Adm M jp)"
  define vv where "vv = bpHeadV c1"
  define tt2 where "tt2 = bpHeadT c1"
  define JJ1 where "JJ1 = Lng (PB tt2) - 1"
  define pj where "pj = PB tt2 ! JJ1"
  define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
  define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
  define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
  define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                         then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                         else if transCondVI M
                         then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                         else if tt2 = 0\<^sub>B
                         then Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                         else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                            (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
  have mark_raw: "Mark M n = (if (Mark (Pred M) n, c1) \<in> MarkedB
              then unflatBT
                     (fst (SOME sb. scb_decomp (Mark (Pred M) n) (fst sb)
                                      (flatBT c1) (snd sb))
                      @ flatBT c2
                      @ snd (SOME sb. scb_decomp (Mark (Pred M) n) (fst sb)
                                        (flatBT c1) (snd sb)))
              else Dpt (enat ?bv) 0\<^sub>B)"
    using Mark.psimps[OF domK] MR Lgt1 mono t1ne nlt
    unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
              tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
              ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
              c2_def[symmetric]
    by simp
  \<comment> \<open>identify the local context with transC1/transC2\<close>
  have jpT: "jp = transJ0 M" by (simp add: jp_def transJ0_def transJ1_def)
  have c1T: "c1 = transC1 M" by (simp add: c1_def transC1_def transJm1_def jpT)
  have vvT: "vv = transV M" by (simp add: vv_def transV_def c1T)
  have tt2T: "tt2 = transT2 M" by (simp add: tt2_def transT2_def c1T)
  have JJ1T: "JJ1 = Lng (PB (transT2 M)) - 1" by (simp add: JJ1_def tt2T)
  have pjT: "pj = PB (transT2 M) ! (Lng (PB (transT2 M)) - 1)"
    by (simp add: pj_def tt2T JJ1T)
  have ldjT: "ldj = (bpHeadV (PB (transT2 M) ! (Lng (PB (transT2 M)) - 1))
                       = enat (entry M 1 (transJ0 M)))"
    by (simp add: ldj_def pjT jpT)
  have c2T: "c2 = transC2 M"
    by (simp add: c2_def transC2_def Let_def vvT tt2T jpT
                  transV_def transT2_def transJ1_def
                  tt3_def tt4_def ldjT pjT JJ1T)
  have cond: "(Mark (Pred M) n, c1) \<in> MarkedB" using mk c1T by simp
  have "Mark M n = unflatBT
                     (fst (SOME sb. scb_decomp (Mark (Pred M) n) (fst sb)
                                      (flatBT c1) (snd sb))
                      @ flatBT c2
                      @ snd (SOME sb. scb_decomp (Mark (Pred M) n) (fst sb)
                                        (flatBT c1) (snd sb)))"
    using mark_raw cond by simp
  also have "\<dots> = scbSubst (transC1 M) (transC2 M) (Mark (Pred M) n)"
    by (simp add: scbSubst_def c1T c2T)
  finally show ?thesis .
qed

text \<open>§8.5 ENDPOINT ENGINE — the per-column Mark-level DEEPEN STEP (recurrence +
  commutation, fully wired).  Combines @{thm [source] m_8_5_Mark_scbSubst_step} (the
  interior-\<open>Mark\<close> recurrence \<open>Mark M n = G (Mark (Pred M) n)\<close>, \<open>G = scbSubst c\<^sub>1 c\<^sub>2\<close>)
  with @{thm [source] m_8_5_scbSubst_addBT_commute} (the commutation \<open>G (pre +\<^sub>B D\<^bsub>h\<^esub> x)
  = pre +\<^sub>B D\<^bsub>h\<^esub> (G x)\<close>): when the predecessor-mark has the SPINE shape
  \<open>Mark (Pred M) n = pre +\<^sub>B D\<^bsub>h\<^esub> x\<close> and the marked principal \<open>c\<^sub>1 = transC1 M\<close> sits
  DEEP inside the trailing slot \<open>x\<close>, the marked term \<open>Mark M n\<close> keeps the SAME
  \<open>pre +\<^sub>B D\<^bsub>h\<^esub>\<close> wrapper and substitutes the period block \<open>c\<^sub>2 = transC2 M\<close> one level
  deeper.  This is the master-key self-similar bridge's inductive step at the explicit
  \<open>Mark\<close> level: \<open>g (C x) = C (g x)\<close> with \<open>C = (pre +\<^sub>B D\<^bsub>h\<^esub> _)\<close>, \<open>g = G\<close>.\<close>

lemma m_8_5_Mark_spine_deepen:
  fixes M :: pairseq and n h :: nat and pre x :: BT and sx bx :: "Sym list"
  assumes MR: "M \<in> RT_PS" and mono: "monoT M" and L: "1 < Lng M"
    and t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B"
    and nlt: "n < Lng M - 1"
    and mkB: "(Mark (Pred M) n, transC1 M) \<in> MarkedB"
    and spine: "Mark (Pred M) n = pre +\<^sub>B Dpt (enat h) x"
    and mk: "scb_decomp x sx (flatBT (transC1 M)) bx"
    and xnz: "x \<noteq> Trm []"
    and c2p: "isPTB_str (flatBT (transC2 M))"
    and prene: "untrm pre \<noteq> []"
  shows "Mark M n = pre +\<^sub>B Dpt (enat h) (scbSubst (transC1 M) (transC2 M) x)"
proof -
  have "Mark M n = scbSubst (transC1 M) (transC2 M) (Mark (Pred M) n)"
    by (rule m_8_5_Mark_scbSubst_step[OF MR mono L t1ne nlt mkB])
  also have "\<dots> = scbSubst (transC1 M) (transC2 M) (pre +\<^sub>B Dpt (enat h) x)"
    using spine by simp
  also have "\<dots> = pre +\<^sub>B Dpt (enat h) (scbSubst (transC1 M) (transC2 M) x)"
    by (rule m_8_5_scbSubst_addBT_commute[OF mk xnz c2p prene])
  finally show ?thesis .
qed

lemma m_8_5_surgery_of_pred_geom_endpoint:
  fixes Y B :: pairseq and t2 z :: BT and e10 vm1 :: nat
  assumes prev: "Trans Y = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) z)"
    and gYne: "\<And>m. m < Lng B \<Longrightarrow> 0 < Lng (Y @ take m B)"
    and gMR: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> RT_PS"
    and gMP: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> PT_PS"
    and gBrne: "\<And>m. m < Lng B \<Longrightarrow> Br ((Y @ take m B) @ [B ! m]) \<noteq> []"
    and gj1gt: "\<And>m. m < Lng B \<Longrightarrow> Lng ((Y @ take m B) @ [B ! m]) - 1 > 1"
    and gpar: "\<And>m. m < Lng B \<Longrightarrow> parent ((Y @ take m B) @ [B ! m]) 0
                 (Lng ((Y @ take m B) @ [B ! m]) - 1) > TrMax ((Y @ take m B) @ [B ! m])"
    and ge10: "\<And>m. m < Lng B \<Longrightarrow> entry ((Y @ take m B) @ [B ! m]) 1 0 = e10"
    and endpoint: "spineLeaf (Trans (Y @ B)) = bpHeadT (Trans Y)"
  shows "Trans (Y @ B) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Y)))"
proof -
  have base: "Trans Y = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans Y)))"
    by (rule m_8_5_base_of_surgery_pred[OF prev])
  show ?thesis
    by (rule m_8_5_surgery_of_geom_endpoint
          [OF base gYne gMR gMP gBrne gj1gt gpar ge10 endpoint])
qed


text \<open>§8.7 R2 brick — keystone WHOLE-BODY \<open>dstep\<close> reduction to the equal-head tail
  (cases (1)/(2), surgery-FREE; uniform generalisation of @{thm [source]
  m_8_7_dstep_case1}).  In keystone cases (1)/(2) the predecessor body is the WHOLE
  prefix \<open>Trm ps\<close> (no trailing principal: \<open>r = 0\<^sub>B\<close>) and \<open>M\<close> appends ONE principal
  \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>j\<^esub> q\<close> at head index \<open>jj\<close> (\<open>jj = j\<^sub>1'\<close> for (1) with \<open>q = 0\<^sub>B\<close>,
  \<open>jj = j\<^sub>0'\<close> for (2) with general \<open>q = snd t12\<close>).  Under the Admpos regime the head
  index is PINNED to the prefix's last head: \<open>rn1_outer_inner_trailing\<close> reads
  \<open>RightNodes (Trans M)\<^bsub>1\<^esub> = M\<^bsub>1,jj\<^esub>\<close> (from \<open>dec\<close>) and
  \<open>RightNodes (Trans (Pred M))\<^bsub>1\<^esub> = hd\<close> (from \<open>predW\<close> via the butlast/last split),
  while @{thm [source] m_8_2_wid_step} equates the two — so \<open>M\<^bsub>1,jj\<^esub> = hd\<close> always
  (the whole-body cases are ALWAYS equal-head, unlike the proper-prefix cases (3)/(4)
  which mostly escape strictly via @{thm [source] descP_last_le}).  Hence the head
  bound is FREE and the dstep reduces, via @{thm [source] m_8_7_dstep_assemble}, to
  exactly the equal-head tail \<open>M\<^bsub>1,jj\<^esub> = hd \<Longrightarrow> leBT q qb\<close> — the genuine \<open>Trans\<close>-spine
  descent.  (Case (1) recovers as \<open>jj := j\<^sub>1'\<close>, \<open>q := 0\<^sub>B\<close>, tail trivial via
  @{thm [source] lessBT_Zero_left}; matches @{thm [source] m_8_7_dstep_case1}.)\<close>

lemma m_8_7_dstep_wholebody:
  fixes M :: pairseq and ps :: "BP list" and q :: BT and jj :: nat
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and j1gt: "Lng M - 1 > 1"
    and Admpos: "transJm1 M > 0"
    and predW: "Trans (Pred M) = Dpt (enat (entry M 1 0)) (Trm ps)"
    and dec: "Trans M = Dpt (enat (entry M 1 0))
                (Trm ps +\<^sub>B Dpt (enat (entry M 1 jj)) q)"
    and predTB: "Trans (Pred M) \<in> T_B"
    and psne: "ps \<noteq> []"
    and tail: "\<And>hd qb. last ps = DB (enat hd) qb \<Longrightarrow> entry M 1 jj = hd \<Longrightarrow> leBT q qb"
  shows "leBT (Dpt (enat (entry M 1 jj)) q) (Trm [last ps])"
proof -
  let ?x = "entry M 1 jj"
  have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B" using predW by simp
  obtain lw qb where lastps_raw: "last ps = DB lw qb" by (cases "last ps")
  have lin: "last ps \<in> set ps" using psne by simp
  have dfreeP: "dfree_BT (Trm ps)"
  proof -
    have "dfree_BT (Dpt (enat (entry M 1 0)) (Trm ps))"
      using predTB predW by (simp add: T_B_def)
    thus ?thesis by simp
  qed
  have "dfree_BP (last ps)" using dfreeP lin by simp
  hence lwne: "lw \<noteq> \<infinity>" using lastps_raw by simp
  obtain hd where hd: "lw = enat hd" using lwne by (cases lw) auto
  have lastps: "last ps = DB (enat hd) qb" using lastps_raw hd by simp
  have psdecomp: "Trm ps = Trm (butlast ps) +\<^sub>B Dpt (enat hd) qb"
  proof -
    have "Trm (butlast ps) +\<^sub>B Dpt (enat hd) qb = Trm (butlast ps @ [DB (enat hd) qb])"
      by simp
    also have "\<dots> = Trm ps"
      using append_butlast_last_id[OF psne] lastps by simp
    finally show ?thesis by simp
  qed
  \<comment> \<open>head pin: \<open>?x = hd\<close> from the two trailing-head read-offs + wid_step\<close>
  have rn1M: "RightNodes (Trans M) ! 1 = ?x"
  proof -
    have e: "Trans M = Dpt (enat (entry M 1 0)) (Trm ps +\<^sub>B Dpt (enat ?x) q)"
      using dec by simp
    show ?thesis unfolding e by (rule rn1_outer_inner_trailing)
  qed
  have rn1P: "RightNodes (Trans (Pred M)) ! 1 = hd"
  proof -
    have e: "Trans (Pred M)
              = Dpt (enat (entry M 1 0)) (Trm (butlast ps) +\<^sub>B Dpt (enat hd) qb)"
      using predW psdecomp by simp
    show ?thesis unfolding e by (rule rn1_outer_inner_trailing)
  qed
  have wid: "RightNodes (Trans M) ! 1 = RightNodes (Trans (Pred M)) ! 1"
    by (rule m_8_2_wid_step[OF MR MP j1gt Admpos t1ne])
  have xhd: "?x = hd" using rn1M rn1P wid by simp
  have head: "?x \<le> hd" using xhd by simp
  have tail': "?x = hd \<longrightarrow> leBT q qb" using tail[OF lastps] xhd by simp
  show ?thesis
    by (rule m_8_7_dstep_assemble[OF lastps psne head tail'])
qed

text \<open>§8.2 (content.md ~3602) 補題（条件(V)の下での右端の親の基本性質） — the
  Trans-FREE rightmost row-0 parent lemma for the last column \<open>j\<^sub>1 = Lng M - 1\<close>.
  The unique witness is \<open>j\<^sub>0 = parent M 0 j\<^sub>1\<close> (it exists & is unique by
  @{thm [source] monoT_hasParent0_last}, giving (1) and the \<open>\<exists>!\<close>).
  \<^item> (2) \<open>j\<^sub>0' \<le> j\<^sub>0\<close>: if \<open>j\<^sub>1' = j\<^sub>1\<close> the joint \<open>j\<^sub>0' = parent M 0 j\<^sub>1' = j\<^sub>0\<close>;
    if \<open>j\<^sub>1' < j\<^sub>1\<close> the last branch \<open>Br M ! J\<^sub>1 = seg M j\<^sub>1' j\<^sub>1\<close> is \<open>monoT\<close>
    (@{thm [source] wf21_Br_eq_seg}, @{thm [source] Br_component_nonmulti}), so
    \<open>le0 M j\<^sub>1' j\<^sub>1\<close> (@{thm [source] le0_monoT_seg_into_list}) pins
    \<open>j\<^sub>1' \<le> j\<^sub>0\<close> (@{thm [source] m_8_2_le0_above_parent}), hence
    \<open>j\<^sub>0' < j\<^sub>1' \<le> j\<^sub>0\<close>.
  \<^item> (3),(4): the only interesting case is \<open>m = j\<^sub>0\<close>, which (via (2),
    \<open>m \<le> j\<^sub>0'\<close>) forces \<open>m = j\<^sub>0' = j\<^sub>0\<close>, i.e. the RIGHT disjunct
    (\<open>M\<^bsub>0,j\<^sub>1'\<^esub> = M\<^bsub>1,j\<^sub>1'\<^esub>\<close>, \<open>Br M\<close> descending).  Then the joint/first-node row
    identity (@{thm [source] m_8_2_joint_row1_eq},
    @{thm [source] m_8_2_branch_col0_val}) gives the \<open>det\<close> inequality
    \<open>M\<^bsub>1,j\<^sub>0'\<^esub> < M\<^bsub>1,j\<^sub>1'\<^esub>\<close>, so @{thm [source] m_8_2_det_imp_joint_lt_TrMax}
    yields \<open>j\<^sub>0' < TrMax M\<close> (= (4)); (3) reads off the row identity at \<open>j\<^sub>1' = j\<^sub>1\<close>.\<close>

lemma m_8_2_condV_rightmost_parent:
  fixes M :: pairseq and m :: nat
  defines "j1 \<equiv> Lng M - 1"
  defines "J1 \<equiv> Lng (Br M) - 1"
  defines "j0' \<equiv> Joints M ! J1"
  defines "j1' \<equiv> FirstNodes M ! J1"
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS" and Brne: "Br M \<noteq> []"
    and hyp: "m < j0' \<or> (m = j0' \<and> entry M 0 j1' = entry M 1 j1' \<and> descending (Br M))"
  shows "\<exists>!j0.
      \<comment> \<open>(1)\<close> nextR M 0 j0 j1
    \<and> \<comment> \<open>(2)\<close> j0' \<le> j0
    \<and> \<comment> \<open>(3)\<close> (m < j0 \<or> entry M 0 j1 = entry M 1 j1)
    \<and> \<comment> \<open>(4)\<close> (m = j0 \<longrightarrow> j0 < TrMax M)"
proof -
  \<comment> \<open>plain equalities for the abbreviations\<close>
  have j1v: "j1 = Lng M - 1" by (simp add: j1_def)
  have J1v: "J1 = Lng (Br M) - 1" by (simp add: J1_def)
  have j0'v: "j0' = Joints M ! J1" by (simp add: j0'_def)
  have j1'v: "j1' = FirstNodes M ! J1" by (simp add: j1'_def)
  \<comment> \<open>memberships\<close>
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  \<comment> \<open>branch index\<close>
  have BrL: "0 < Lng (Br M)" using Brne by (cases "Br M") auto
  have J1Br: "J1 < Lng (Br M)" using BrL J1v by simp
  \<comment> \<open>\<open>j\<^sub>0'\<close>, \<open>j\<^sub>1'\<close> geometry\<close>
  have geom: "j0' \<le> TrMax M \<and> TrMax M < j1'"
    using m_6_4_FirstNodes_TrMax_Joints[OF MP J1Br] by (simp add: j0'v j1'v)
  have Trlt1': "TrMax M < j1'" using geom by simp
  have fL: "j1' < Lng M" using a1_FN_lt[OF MP J1Br] by (simp add: j1'v)
  have j1'lej1: "j1' \<le> j1" using fL j1v by linarith
  have L1: "1 < Lng M" using Trlt1' fL by linarith
  \<comment> \<open>\<open>j\<^sub>0'\<close> is the row-0 parent of \<open>j\<^sub>1'\<close>\<close>
  have nxJ: "nextR M 0 j0' j1'" using Joints_parent_nextR[OF MP J1Br] by (simp add: j0'v j1'v)
  have j0'lt1': "j0' < j1'" using poper_nextR_imp_le0[OF nxJ] by simp
  have j0'par: "parent M 0 j1' = j0'" using Joints_nth[OF J1Br] by (simp add: j0'v j1'v)
  \<comment> \<open>the row-0 parent of the last column\<close>
  define j0s where "j0s = parent M 0 j1"
  have hpj1: "hasParent M 0 j1" using monoT_hasParent0_last[OF MT mono L1] by (simp add: j1v)
  have EXU: "\<exists>!a. nextR M 0 a j1" using hpj1 by (simp add: hasParent_def)
  have nx0s: "nextR M 0 j0s j1" using theI'[OF EXU] by (simp add: j0s_def parent_def)
  have uniq0: "\<And>a. nextR M 0 a j1 \<Longrightarrow> a = j0s"
  proof -
    fix a assume h: "nextR M 0 a j1"
    show "a = j0s" using the1_equality[OF EXU h] by (simp add: j0s_def parent_def)
  qed
  \<comment> \<open>last-branch ancestry: \<open>j\<^sub>1' < j\<^sub>1 \<Longrightarrow> j\<^sub>1' \<le> j\<^sub>0\<close>\<close>
  have facC: "j1' < j1 \<Longrightarrow> j1' \<le> j0s"
  proof -
    assume j1'ltj1: "j1' < j1"
    have blkeq: "Br M ! J1 = seg M j1' j1"
      using wf21_Br_eq_seg[OF MP Brne] by (simp add: J1v j1'v j1v)
    have lenblk: "Lng (Br M ! J1) = Suc j1 - j1'" using blkeq by simp
    have lenblk_gt: "1 < Lng (Br M ! J1)" using lenblk j1'ltj1 by linarith
    have nz: "\<not> zeroT (Br M ! J1)" using lenblk_gt by (auto simp: zeroT_def)
    have monoblk: "monoT (Br M ! J1)" using Br_component_nonmulti[OF MP J1Br] nz by blast
    have segmono: "monoT (seg M j1' j1)" using monoblk blkeq by simp
    have j1ltLM: "j1 < Lng M" using j1v L1 by linarith
    have le0: "le0 M j1' j1"
      by (rule le0_monoT_seg_into_list[OF MT segmono j1'lej1 order.refl j1ltLM])
    have "j1' \<le> parent M 0 j1"
      by (rule m_8_2_le0_above_parent[OF hpj1 le0]) (use j1'ltj1 in simp)
    thus "j1' \<le> j0s" by (simp add: j0s_def)
  qed
  \<comment> \<open>(2)\<close>
  have C2: "j0' \<le> j0s"
  proof (cases "j1' = j1")
    case True
    have "parent M 0 j1 = parent M 0 j1'" using True by simp
    also have "\<dots> = j0'" by (rule j0'par)
    finally have "parent M 0 j1 = j0'" .
    thus ?thesis by (simp add: j0s_def)
  next
    case False
    hence "j1' < j1" using j1'lej1 by linarith
    from facC[OF this] j0'lt1' show ?thesis by linarith
  qed
  \<comment> \<open>helper: under the RIGHT disjunct, \<open>j\<^sub>0' < TrMax M\<close> (the \<open>det\<close> route)\<close>
  have rightlt: "\<lbrakk>entry M 0 j1' = entry M 1 j1'; descending (Br M)\<rbrakk> \<Longrightarrow> j0' < TrMax M"
  proof -
    assume E: "entry M 0 j1' = entry M 1 j1'" and desc: "descending (Br M)"
    have MD: "M \<in> DT_PS" using MR mono desc by (simp add: DT_PS_def)
    have e1j0': "entry M 1 j0' = entry (Br M ! J1) 0 0 - 1"
      using m_8_2_joint_row1_eq[OF MD J1Br] by (simp add: j0'v)
    have e0j1': "entry M 0 j1' = entry (Br M ! J1) 0 0"
      using entry_FirstNodes_eq_component_gen[OF MP J1Br] by (simp add: j1'v)
    have c0val: "entry (Br M ! J1) 0 0 = entry M 1 0 + j0' + 1"
      using m_8_2_branch_col0_val[OF MD J1Br] by (simp add: j0'v)
    have aval: "entry M 1 j0' = entry M 1 0 + j0'" using e1j0' c0val by simp
    have b1val: "entry M 1 j1' = entry M 1 0 + j0' + 1"
    proof -
      have "entry M 1 j1' = entry M 0 j1'" using E by simp
      also have "\<dots> = entry (Br M ! J1) 0 0" by (rule e0j1')
      also have "\<dots> = entry M 1 0 + j0' + 1" by (rule c0val)
      finally show ?thesis .
    qed
    have det: "entry M 1 j0' < entry M 1 j1'" using aval b1val by simp
    have detform: "entry M 1 (Joints M ! (Lng (Br M) - 1))
                     < entry M 1 (FirstNodes M ! (Lng (Br M) - 1))"
      using det by (simp add: j0'v j1'v J1v)
    have "Joints M ! (Lng (Br M) - 1) < TrMax M"
      by (rule m_8_2_det_imp_joint_lt_TrMax[OF MD Brne detform])
    thus "j0' < TrMax M" by (simp add: j0'v J1v)
  qed
  \<comment> \<open>(3)\<close>
  have C3: "m < j0s \<or> entry M 0 j1 = entry M 1 j1"
  proof (cases "m < j0'")
    case True
    with C2 have "m < j0s" by linarith
    thus ?thesis by blast
  next
    case False
    have notlt: "\<not> m < j0'" by (rule False)
    have meq: "m = j0'" and E: "entry M 0 j1' = entry M 1 j1'"
      using hyp notlt by auto
    show ?thesis
    proof (cases "j1' = j1")
      case True
      have "entry M 0 j1 = entry M 1 j1" using E True by simp
      thus ?thesis by blast
    next
      case False
      hence "j1' < j1" using j1'lej1 by linarith
      from facC[OF this] have "j1' \<le> j0s" .
      with j0'lt1' meq have "m < j0s" by linarith
      thus ?thesis by blast
    qed
  qed
  \<comment> \<open>(4)\<close>
  have C4: "m = j0s \<longrightarrow> j0s < TrMax M"
  proof
    assume meqs: "m = j0s"
    have mlej0': "m \<le> j0'" using hyp by auto
    have meq': "m = j0'" using mlej0' C2 meqs by linarith
    have notlt: "\<not> m < j0'" using meq' by simp
    have E: "entry M 0 j1' = entry M 1 j1'" and desc: "descending (Br M)"
      using hyp notlt by auto
    have lt: "j0' < TrMax M" by (rule rightlt[OF E desc])
    have "j0s = j0'" using meqs meq' by linarith
    thus "j0s < TrMax M" using lt by simp
  qed
  \<comment> \<open>assemble the \<open>\<exists>!\<close>\<close>
  show ?thesis
  proof (rule ex1I[where a = j0s])
    show "nextR M 0 j0s j1 \<and> j0' \<le> j0s
            \<and> (m < j0s \<or> entry M 0 j1 = entry M 1 j1)
            \<and> (m = j0s \<longrightarrow> j0s < TrMax M)"
      using nx0s C2 C3 C4 by blast
  next
    fix j0
    assume "nextR M 0 j0 j1 \<and> j0' \<le> j0
              \<and> (m < j0 \<or> entry M 0 j1 = entry M 1 j1)
              \<and> (m = j0 \<longrightarrow> j0 < TrMax M)"
    hence "nextR M 0 j0 j1" by simp
    thus "j0 = j0s" by (rule uniq0)
  qed
qed

text \<open>§8.5 ENDPOINT ENGINES added this round: @{thm [source] m_8_5_Mark_scbSubst_step}
  (interior-Mark recurrence in scbSubst form) and @{thm [source] m_8_5_Mark_spine_deepen}
  (per-column Mark-level deepen via recurrence + commutation).\<close>


text \<open>§8.5 item (b) FOUNDATION — the full-prefix surgery host is standard (M-agnostic).
  The faithful surgery host Y @ take k B is the prefix take (Lng Y + k) (Y @ B):
  by take_append, take (Lng Y + k) (Y @ B) = take (Lng Y + k) Y @ take k B = Y @ take k B.
  Hence if Y @ B is standard (at wiring Y @ B = M[Suc q], oper_ST_RT_T), item (a)
  ST_PS_take gives Y @ take k B in ST_PS, hence RT_PS / T_PS.  This kills the lossy
  suffix-slice membership problem (the slice (8/148) fails; the full prefix is 148/148).\<close>

lemma fullprefix_take_eq:
  fixes Y B :: pairseq and k :: nat
  shows "Y @ take k B = take (Lng Y + k) (Y @ B)"
proof -
  have "take (Lng Y + k) (Y @ B) = take (Lng Y + k) Y @ take (Lng Y + k - Lng Y) B"
    by (rule take_append)
  also have "take (Lng Y + k) Y = Y" by simp
  also have "Lng Y + k - Lng Y = k" by simp
  finally show ?thesis by simp
qed

lemma m_8_5_fullprefix_ST:
  fixes Y B :: pairseq and k :: nat
  assumes Nst: "Y @ B \<in> ST_PS" and kpos: "0 < k"
  shows "Y @ take k B \<in> ST_PS"
proof -
  have kpos': "0 < Lng Y + k" using kpos by simp
  have st: "take (Lng Y + k) (Y @ B) \<in> ST_PS" by (rule ST_PS_take[OF Nst kpos'])
  show ?thesis by (subst fullprefix_take_eq) (rule st)
qed

lemma m_8_5_fullprefix_RT:
  fixes Y B :: pairseq and k :: nat
  assumes Nst: "Y @ B \<in> ST_PS" and kpos: "0 < k"
  shows "Y @ take k B \<in> RT_PS"
  using m_8_5_fullprefix_ST[OF Nst kpos] m_6_7_ST_PS_subseteq_RT_PS by blast

text \<open>§8.5 item (b) FOUNDATION — the full-prefix host is PROPER (in PT_PS).  The
  surgery's per-column SHAPE collapse (@{thm [source] m_8_5_appended_col_deepen})
  needs PT_PS = T_PS \<inter> monoT.  T_PS comes from the standard membership; monoT comes
  from @{thm [source] m_6_2_mono_prefix}: an initial segment seg N 0 j0 of a proper
  (PT_PS) sequence N is monoT.  Writing the host as seg (Y @ B) 0 (Lng Y + k - 1)
  (= take (Lng Y + k) (Y @ B) via @{thm [source] seg_0_eq_take}) reduces gMP to the
  SINGLE residual Y @ B \<in> PT_PS (at wiring: M[Suc q] \<in> PT_PS, the condition-(V)
  iterate monoT — NOT supplied by oper_ST_RT_T, which gives only ST_PS/RT_PS/T_PS).\<close>

lemma m_8_5_fullprefix_PT:
  fixes Y B :: pairseq and k :: nat
  assumes Nst: "Y @ B \<in> ST_PS" and Npt: "Y @ B \<in> PT_PS"
    and kpos: "0 < k" and kle: "k \<le> Lng B" and L2: "1 < Lng Y + k"
  shows "Y @ take k B \<in> PT_PS"
proof -
  have MT: "Y @ take k B \<in> T_PS" by (rule ST_PS_T_PS[OF m_8_5_fullprefix_ST[OF Nst kpos]])
  have BL: "0 < Lng B" using kpos kle by linarith
  have r_le: "Suc (Lng Y + k - 1) \<le> Lng (Y @ B)"
  proof -
    have "Lng Y + k \<le> Lng Y + Lng B" using kle by simp
    thus ?thesis using L2 by simp
  qed
  have segeq: "seg (Y @ B) 0 (Lng Y + k - 1) = take (Lng Y + k) (Y @ B)"
    using seg_0_eq_take[OF r_le] L2 by simp
  have j0pos: "0 < Lng Y + k - 1" using L2 by simp
  have j0lt: "Lng Y + k - 1 < Lng (Y @ B)"
  proof -
    have "Lng (Y @ B) = Lng Y + Lng B" by simp
    thus ?thesis using kle BL L2 by linarith
  qed
  have mono: "monoT (seg (Y @ B) 0 (Lng Y + k - 1))"
    by (rule m_6_2_mono_prefix[OF Npt j0pos j0lt])
  have monoH: "monoT (Y @ take k B)"
    by (subst fullprefix_take_eq, subst segeq[symmetric]) (rule mono)
  show ?thesis using MT monoH by (simp add: PT_PS_def)
qed

text \<open>§8.5 item (b) ASSEMBLED — the FULL-PREFIX surgery, with all the per-column
  MEMBERSHIP geom inputs (gYne/gMR/gMP/gj1gt/ge10) DISCHARGED uniformly from the
  full-prefix foundations above.  The per-column host (Y @ take m B) @ [B ! m]
  equals Y @ take (Suc m) B (take_Suc_conv_app_nth); the foundations
  @{thm [source] m_8_5_fullprefix_RT} / @{thm [source] m_8_5_fullprefix_PT} give its
  RT_PS / PT_PS membership from Y @ B \<in> ST_PS / PT_PS (the lossy-slice problem is
  gone).  The constant outer head (ge10) reads off column 0 (= Y ! 0, e10v) and the
  depth (gj1gt) from 1 < Lng Y.  This reduces @{thm [source]
  m_8_5_surgery_of_pred_geom_endpoint} to EXACTLY the GENUINE residuals:
    \<^item> prev:     the outer-q IH Trans Y = D_e10 (t2 +_B D_vm1 z);
    \<^item> Y @ B \<in> PT_PS: the condition-(V) iterate monoT (M[Suc q] \<in> PT_PS; NOT given by
       oper_ST_RT_T, the one remaining membership obligation);
    \<^item> gpar:     the per-column DEEPEN TRIGGER parent (.. ) 0 (Lng - 1) > TrMax (.. )
       (148/148 empirically; closable but laborious from the oper-append trunk
       machinery TrMax_seg_oper_d1pos_eq / oper_parent1_readback);
    \<^item> gBrne:    the per-column branch-nonemptiness (follows from gpar via the parent
       bound, kept explicit here to match the underlying lemma);
    \<^item> endpoint: the self-similar bridge spineLeaf (Trans (Y @ B)) = bpHeadT (Trans Y).
  Setting Y = M[q], B the appended condV block (Y @ B = M[Suc q]) turns this into the
  outer-q surgery step.\<close>

lemma m_8_5_surgery_fullprefix:
  fixes Y B :: pairseq and t2 z :: BT and e10 vm1 :: nat
  assumes Nst: "Y @ B \<in> ST_PS" and Npt: "Y @ B \<in> PT_PS"
    and YL2: "1 < Lng Y"
    and prev: "Trans Y = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) z)"
    and e10v: "entry Y 1 0 = e10"
    and gBrne: "\<And>m. m < Lng B \<Longrightarrow> Br ((Y @ take m B) @ [B ! m]) \<noteq> []"
    and gpar: "\<And>m. m < Lng B \<Longrightarrow> parent ((Y @ take m B) @ [B ! m]) 0
                 (Lng ((Y @ take m B) @ [B ! m]) - 1) > TrMax ((Y @ take m B) @ [B ! m])"
    and endpoint: "spineLeaf (Trans (Y @ B)) = bpHeadT (Trans Y)"
  shows "Trans (Y @ B) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Y)))"
proof -
  have Yne: "0 < Lng Y" using YL2 by linarith
  have hosteq: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] = Y @ take (Suc m) B"
  proof -
    fix m assume m: "m < Lng B"
    have "take (Suc m) B = take m B @ [B ! m]" by (rule take_Suc_conv_app_nth[OF m])
    thus "(Y @ take m B) @ [B ! m] = Y @ take (Suc m) B" by simp
  qed
  have gYne: "\<And>m. m < Lng B \<Longrightarrow> 0 < Lng (Y @ take m B)"
  proof -
    fix m assume "m < Lng B"
    have "Lng Y \<le> Lng (Y @ take m B)" by simp
    thus "0 < Lng (Y @ take m B)" using Yne by linarith
  qed
  have gMR: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> RT_PS"
  proof -
    fix m assume m: "m < Lng B"
    have "Y @ take (Suc m) B \<in> RT_PS" by (rule m_8_5_fullprefix_RT[OF Nst]; simp)
    thus "(Y @ take m B) @ [B ! m] \<in> RT_PS" by (simp only: hosteq[OF m])
  qed
  have gMP: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> PT_PS"
  proof -
    fix m assume m: "m < Lng B"
    have sm: "0 < Suc m" by simp
    have smle: "Suc m \<le> Lng B" using m by simp
    have l2: "1 < Lng Y + Suc m" using YL2 by linarith
    have "Y @ take (Suc m) B \<in> PT_PS" by (rule m_8_5_fullprefix_PT[OF Nst Npt sm smle l2])
    thus "(Y @ take m B) @ [B ! m] \<in> PT_PS" by (simp only: hosteq[OF m])
  qed
  have gj1gt: "\<And>m. m < Lng B \<Longrightarrow> Lng ((Y @ take m B) @ [B ! m]) - 1 > 1"
  proof -
    fix m assume m: "m < Lng B"
    have mle: "m \<le> Lng B" using m by simp
    have lt: "Lng (take m B) = m" by (simp add: min.absorb1 mle)
    have "Lng ((Y @ take m B) @ [B ! m]) = Lng Y + m + 1" using lt by simp
    thus "Lng ((Y @ take m B) @ [B ! m]) - 1 > 1" using YL2 by linarith
  qed
  have ge10: "\<And>m. m < Lng B \<Longrightarrow> entry ((Y @ take m B) @ [B ! m]) 1 0 = e10"
  proof -
    fix m assume "m < Lng B"
    have "((Y @ take m B) @ [B ! m]) ! 0 = Y ! 0" using Yne by (simp add: nth_append)
    thus "entry ((Y @ take m B) @ [B ! m]) 1 0 = e10" using e10v by (simp add: entry_def)
  qed
  show ?thesis
    by (rule m_8_5_surgery_of_pred_geom_endpoint
          [OF prev gYne gMR gMP gBrne gj1gt gpar ge10 endpoint])
qed


text \<open>§8.5 SURGERY residual gBrne DISCHARGED from gpar (parent-bound fold).  The
  branch-nonemptiness per-column residual \<open>Br M' \<noteq> []\<close> of @{thm [source]
  m_8_5_surgery_fullprefix} is NOT an independent obligation: it follows from the
  DEEPEN-TRIGGER \<open>gpar\<close> (\<open>TrMax M' < parent M' 0 (Lng M'-1)\<close>) together with the
  membership/depth residuals the assembler already discharges (\<open>gMP\<close>: \<open>M' \<in> PT_PS\<close>,
  \<open>gj1gt\<close>: \<open>1 < Lng M'\<close>).  Mechanism: the last column has a UNIQUE row-0 parent
  (@{thm [source] monoT_hasParent0_last}, from \<open>monoT M'\<close>), which by \<open>nextrel0\<close> sits
  strictly LEFT of the last column, so \<open>TrMax M' < parent M' 0 (Lng M'-1) < Lng M'-1\<close>;
  hence \<open>TrMax M' \<noteq> Lng M'-1\<close> and the \<open>else\<close> branch of @{thm [source] Br_def}
  (ALWAYS non-empty, @{thm [source] P_nonempty}) is taken.  This is exactly the note
  at @{thm [source] m_8_5_surgery_fullprefix} ("gBrne follows from gpar via the
  parent bound"); it lets the assembler drop the gBrne residual slot, leaving only
  \<open>gpar\<close> as the genuine geometric input.\<close>

lemma m_8_5_gBrne_from_gpar:
  fixes M' :: pairseq
  assumes MP: "M' \<in> PT_PS"
    and L: "1 < Lng M'"
    and par: "TrMax M' < parent M' 0 (Lng M' - 1)"
  shows "Br M' \<noteq> []"
proof -
  have MT: "M' \<in> T_PS" and mono: "monoT M'" using MP by (simp_all add: PT_PS_def)
  have hp: "hasParent M' 0 (Lng M' - 1)"
    by (rule monoT_hasParent0_last[OF MT mono L])
  have parR: "nextR M' 0 (parent M' 0 (Lng M' - 1)) (Lng M' - 1)"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have nr0: "nextrel0 M' (parent M' 0 (Lng M' - 1)) (Lng M' - 1)"
    using parR by (simp add: nextR_def)
  have plt: "parent M' 0 (Lng M' - 1) < Lng M' - 1"
    using nr0 by (simp add: nextrel0_def)
  have "TrMax M' \<noteq> Lng M' - 1" using par plt by linarith
  thus "Br M' \<noteq> []" by (simp add: Br_def P_nonempty)
qed


text \<open>§8.5 SURGERY gpar REDUCTION — TRUNK CONSTANCY under the appended block.  The
  per-column host of @{thm [source] m_8_5_surgery_fullprefix} is \<open>Y \<frown> S\<close> with \<open>S\<close> a
  right-extension (\<open>S = take m B \<frown> [B!m]\<close>).  When the prefix \<open>Y\<close> ALREADY deepens
  (\<open>Br Y \<noteq> []\<close>, i.e. its trunk stops strictly inside it, \<open>TrMax Y < Lng Y - 1\<close>) the
  trunk is INSENSITIVE to anything appended on the right: \<open>TrMax (Y \<frown> S) = TrMax Y\<close>.
  Mechanism: the trunk steps live in the shared prefix \<open>[0, Lng Y-1]\<close>
  (@{thm [source] TrMax_eq_of_prefix_agree}); the boundary stop
  \<open>\<not> nextR (Y\<frown>S) 1 (TrMax Y) (TrMax Y+1)\<close> transfers a hypothetical big-side step back
  to \<open>Y\<close> (@{thm [source] nextrel1_prefix_imp}, both indices \<open>\<le> Lng Y-1\<close> since
  \<open>TrMax Y < Lng Y-1\<close>) and contradicts the trunk maximality of \<open>Y\<close>
  (@{thm [source] TrMax_stop}).  This SHARPENS the gpar residual: it suffices to show
  \<open>parent (host) 0 (Lng host-1) > TrMax Y\<close> (the trunk of the FIXED prefix \<open>Y\<close>), the
  trunk no longer drifting with the column index \<open>m\<close>.\<close>

lemma m_8_5_TrMax_append_Br:
  fixes Y S :: pairseq
  assumes YT: "Y \<in> T_PS" and MT: "Y @ S \<in> T_PS"
    and BrY: "Br Y \<noteq> []"
  shows "TrMax (Y @ S) = TrMax Y"
proof -
  have tne: "TrMax Y \<noteq> Lng Y - 1"
  proof
    assume "TrMax Y = Lng Y - 1"
    hence "Br Y = []" by (simp add: Br_def)
    thus False using BrY by simp
  qed
  have tle: "TrMax Y \<le> Lng Y - 1" by (rule TrMax_bound[OF YT])
  have tlt: "TrMax Y < Lng Y - 1" using tne tle by linarith
  let ?c = "Lng Y - 1"
  have cN: "?c < Lng Y" using tlt by linarith
  have cM: "?c < Lng (Y @ S)" using cN by simp
  have agree: "\<And>j. j \<le> ?c \<Longrightarrow> (Y @ S) ! j = Y ! j"
  proof -
    fix j assume "j \<le> ?c"
    hence "j < Lng Y" using cN by linarith
    thus "(Y @ S) ! j = Y ! j" by (simp add: nth_append)
  qed
  have tnc: "TrMax Y \<le> ?c" by (rule tle)
  have stop: "\<not> nextR (Y @ S) 1 (TrMax Y) (TrMax Y + 1)"
  proof
    assume "nextR (Y @ S) 1 (TrMax Y) (TrMax Y + 1)"
    hence stepM: "nextrel1 (Y @ S) (TrMax Y) (TrMax Y + 1)" by (simp add: nextR_def)
    have xle: "TrMax Y \<le> ?c" by (rule tle)
    have yle: "TrMax Y + 1 \<le> ?c" using tlt by linarith
    have "nextrel1 Y (TrMax Y) (TrMax Y + 1)"
      by (rule nextrel1_prefix_imp[OF agree cM cN xle yle stepM])
    hence "nextR Y 1 (TrMax Y) (TrMax Y + 1)" by (simp add: nextR_def)
    moreover have "\<not> nextR Y 1 (TrMax Y) (TrMax Y + 1)" by (rule TrMax_stop[OF YT tlt])
    ultimately show False by simp
  qed
  show ?thesis by (rule TrMax_eq_of_prefix_agree[OF MT YT agree cM cN tnc stop])
qed

text \<open>§8.5 SURGERY gpar REDUCTION — host-shaped corollary of
  @{thm [source] m_8_5_TrMax_append_Br}.  Specialises the trunk-constancy to the exact
  per-column host \<open>(Y \<frown> take m B) \<frown> [B!m]\<close> of @{thm [source] m_8_5_surgery_fullprefix}
  (associating \<open>S = take m B \<frown> [B!m]\<close>): given the prefix already deepens
  (\<open>Br Y \<noteq> []\<close>) and the host is a pair sequence (\<open>\<in> T_PS\<close>, available from the gMR/gMP
  membership residuals), the host trunk equals the FIXED prefix trunk \<open>TrMax Y\<close>.  Slots
  the gpar residual \<open>parent (host) 0 (Lng host-1) > TrMax (host)\<close> down to
  \<open>parent (host) 0 (Lng host-1) > TrMax Y\<close>.\<close>

lemma m_8_5_TrMax_host:
  fixes Y B :: pairseq and m :: nat
  assumes YT: "Y \<in> T_PS"
    and hostT: "(Y @ take m B) @ [B ! m] \<in> T_PS"
    and BrY: "Br Y \<noteq> []"
  shows "TrMax ((Y @ take m B) @ [B ! m]) = TrMax Y"
proof -
  have e: "(Y @ take m B) @ [B ! m] = Y @ (take m B @ [B ! m])" by simp
  have hT: "Y @ (take m B @ [B ! m]) \<in> T_PS" using hostT e by simp
  have "TrMax (Y @ (take m B @ [B ! m])) = TrMax Y"
    by (rule m_8_5_TrMax_append_Br[OF YT hT BrY])
  thus ?thesis using e by simp
qed

text \<open>§8.5 SURGERY gpar BRIDGE (a) — ROW-0 PARENT prefix agreement.  The row-0
  parent of the LAST column of a prefix \<open>take k M\<close> equals the row-0 parent of the
  SAME column in the full \<open>M\<close>: \<open>parent (take k M) 0 (k-1) = parent M 0 (k-1)\<close>.  The
  parent is a backward search confined to \<open>[0,k-1]\<close>, the shared region, so the
  \<open>nextrel0\<close> edge into \<open>k-1\<close> is identical on both sides (@{thm [source]
  nextrel0_prefix_imp}, applied in BOTH directions — its hypotheses \<open>x,y \<le> k-1\<close>
  hold because any \<open>nextrel0 _ a (k-1)\<close> forces \<open>a < k-1\<close>); the \<open>THE\<close> witnesses
  therefore coincide.  This bridges the gpar host \<open>(Y\<frown>take m B)\<frown>[B!m] =
  take (Lng Y+m+1) (Y\<frown>B)\<close> (a prefix of the iterate \<open>Y\<frown>B = M[Suc q]\<close>) to the
  FULL-iterate row-0 parent, where the oper block-tiling machinery
  (@{thm [source] oper_gen_tiling_row0_boundary} etc.) lives — the remaining gpar
  residual is then \<open>parent (Y\<frown>B) 0 (Lng Y+m) > TrMax Y\<close> (full-iterate parent index
  vs the fixed prefix trunk).\<close>

lemma m_8_5_parent0_take_prefix:
  fixes M :: pairseq and k :: nat
  assumes k0: "0 < k" and kL: "k \<le> Lng M"
  shows "parent (take k M) 0 (k - 1) = parent M 0 (k - 1)"
proof -
  let ?T = "take k M"
  have len: "Lng ?T = k" using kL by simp
  have b2: "k - 1 < Lng M" using kL k0 by linarith
  have agreeTM: "\<And>j. j \<le> k - 1 \<Longrightarrow> ?T ! j = M ! j"
  proof -
    fix j assume "j \<le> k - 1" hence "j < k" using k0 by linarith
    thus "?T ! j = M ! j" by simp
  qed
  have agreeMT: "\<And>j. j \<le> k - 1 \<Longrightarrow> M ! j = ?T ! j" using agreeTM by simp
  have cT: "k - 1 < Lng ?T" using len k0 by linarith
  have equiv: "\<And>a. nextrel0 ?T a (k - 1) = nextrel0 M a (k - 1)"
  proof -
    fix a
    show "nextrel0 ?T a (k - 1) = nextrel0 M a (k - 1)"
    proof
      assume h: "nextrel0 ?T a (k - 1)"
      have ac: "a \<le> k - 1" using h by (simp add: nextrel0_def)
      show "nextrel0 M a (k - 1)"
        by (rule nextrel0_prefix_imp[OF agreeTM b2 ac order.refl h])
    next
      assume h: "nextrel0 M a (k - 1)"
      have ac: "a \<le> k - 1" using h by (simp add: nextrel0_def)
      show "nextrel0 ?T a (k - 1)"
        by (rule nextrel0_prefix_imp[OF agreeMT cT ac order.refl h])
    qed
  qed
  have nr: "\<And>a. nextR ?T 0 a (k - 1) = nextR M 0 a (k - 1)"
    using equiv by (simp add: nextR_def)
  have "parent ?T 0 (k - 1) = (THE a. nextR ?T 0 a (k - 1))" by (simp add: parent_def)
  also have "\<dots> = (THE a. nextR M 0 a (k - 1))" using nr by simp
  also have "\<dots> = parent M 0 (k - 1)" by (simp add: parent_def)
  finally show ?thesis .
qed

text \<open>§8.5 SURGERY gpar BRIDGE (a) — host-shaped corollary of
  @{thm [source] m_8_5_parent0_take_prefix}.  The per-column gpar host
  \<open>(Y\<frown>take m B)\<frown>[B!m]\<close> is the length-\<open>(Lng Y+Suc m)\<close> prefix of the iterate
  \<open>Y\<frown>B\<close> (\<open>take_Suc_conv_app_nth\<close>+\<open>take_append\<close>), so its last-column row-0 parent reads
  off the FULL iterate: \<open>parent (host) 0 (Lng host-1) = parent (Y\<frown>B) 0 (Lng host-1)\<close>.
  Combined with @{thm [source] m_8_5_TrMax_host} (\<open>TrMax host = TrMax Y\<close>), the gpar
  residual becomes the purely full-iterate statement
  \<open>parent (Y\<frown>B) 0 (Lng Y+m) > TrMax Y\<close>.\<close>

lemma m_8_5_parent_host:
  fixes Y B :: pairseq and m :: nat
  assumes m: "m < Lng B"
  shows "parent ((Y @ take m B) @ [B ! m]) 0 (Lng ((Y @ take m B) @ [B ! m]) - 1)
       = parent (Y @ B) 0 (Lng ((Y @ take m B) @ [B ! m]) - 1)"
proof -
  let ?h = "(Y @ take m B) @ [B ! m]"
  have hostL: "Lng ?h = Lng Y + Suc m" using m by simp
  have tk: "take (Suc m) B = take m B @ [B ! m]" by (rule take_Suc_conv_app_nth[OF m])
  have split: "take (Lng Y + Suc m) (Y @ B) = Y @ take (Suc m) B"
    by (subst take_append) simp
  have he: "?h = take (Lng ?h) (Y @ B)"
  proof -
    have "take (Lng ?h) (Y @ B) = Y @ take (Suc m) B" by (simp only: hostL split)
    also have "\<dots> = Y @ (take m B @ [B ! m])" by (simp add: tk)
    also have "\<dots> = ?h" by simp
    finally show ?thesis ..
  qed
  have k0: "0 < Lng ?h" using hostL by simp
  have kL: "Lng ?h \<le> Lng (Y @ B)" using hostL m by simp
  have P: "parent (take (Lng ?h) (Y @ B)) 0 (Lng ?h - 1)
             = parent (Y @ B) 0 (Lng ?h - 1)"
    by (rule m_8_5_parent0_take_prefix[OF k0 kL])
  have step1: "parent ?h 0 (Lng ?h - 1) = parent (take (Lng ?h) (Y @ B)) 0 (Lng ?h - 1)"
    by (rule arg_cong[where f = "\<lambda>X. parent X 0 (Lng ?h - 1)", OF he])
  show ?thesis using step1 P by simp
qed

text \<open>§8.5 SURGERY gpar BRIDGE (b) — ROW-0 oper parent INDEX at a BLOCK START
  (m = 0 boundary).  The row-0 parent of the block-\<open>q\<close>-start column
  \<open>x = j\<^sub>0 + q\<cdot>w\<close> of the iterate \<open>N[n]\<close> lands ONE FULL PERIOD back, in block
  \<open>q-1\<close> at the SAME offset \<open>r = parent N 0 (Lng N-1) - j\<^sub>0\<close> as \<open>N\<close>'s own row-0
  parent of its last column:
    \<open>parent (N[n]) 0 (j\<^sub>0 + q\<cdot>w) = j\<^sub>0 + (q-1)\<cdot>w + r = parent N 0 (Lng N-1) + (q-1)\<cdot>w\<close>.
  This is the INDEX half of @{thm [source] oper_gen_tiling_row0_boundary} (whose
  \<open>shows\<close> only exposes the row-0 \<open>+1\<close> ENTRY relation, RedCondA-gated): its proof
  builds the explicit edge \<open>nextrel0 (N[n]) ?P x\<close> and the uniqueness
  (\<open>idxsum_parent0_unique\<close> reflecting any candidate parent down to \<open>N\<close>'s parent edge
  at \<open>j\<^sub>1\<close>), then @{thm [source] parent0_eqI} pins the index — ALL before the
  \<open>condA\<close>/\<open>+1\<close> step.  So the index is RedCondA-FREE, built only from the GREEN
  RedCondA-free bricks @{thm [source] oper_gen_block_entry0},
  @{thm [source] oper_last_row0_haspar}, @{thm [source] oper_gen_strict_period_floor},
  @{thm [source] operB_gen_LngM}.  (For the gpar m=0 column \<open>Lng Y = j\<^sub>0+q\<cdot>w\<close> with
  \<open>Y = M[q]\<close>, this gives \<open>parent (M[Suc q]) 0 (Lng Y) = parent M 0 (Lng M-1)+(q-1)\<cdot>w\<close>,
  which exceeds \<open>TrMax Y\<close> via base-gpar + the trunk invariance \<open>TrMax(M[q])=TrMax M\<close>.)\<close>

lemma oper_gen_row0_boundary_index:
  fixes N :: pairseq and n q :: nat
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and q1: "1 \<le> q" and qn: "q < n"
  shows "parent ((N::pairseq)[n]) 0
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
       = parent N (idx1 N (Lng N - 1)) (Lng N - 1)
           + (q - 1) * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
           + (parent N 0 (Lng N - 1) - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?d0 = "if 0 < ?i1 then entry N 0 ?j1 - entry N 0 ?j0 else 0"
  let ?Nn = "(N::pairseq)[n]"
  let ?B = "?j0 + q * ?w"  let ?x = "?B"
  have w0: "0 < ?w" using j0lt by linarith
  have d0def: "?d0 = entry N 0 ?j1 - entry N 0 ?j0" using i1 by simp
  have blk: "\<And>k t. k < n \<Longrightarrow> t < ?w \<Longrightarrow> entry ?Nn 0 (?j0 + k * ?w + t) = entry N 0 (?j0 + t) + k * ?d0"
  proof -
    fix k t assume k: "k < n" and t: "t < ?w"
    show "entry ?Nn 0 (?j0 + k * ?w + t) = entry N 0 (?j0 + t) + k * ?d0"
      by (rule oper_gen_block_entry0[OF L notzero hp j0lt k t])
  qed
  have ex: "entry ?Nn 0 ?x = entry N 0 ?j0 + q * ?d0" using blk[OF qn w0] by simp
  have hp0: "hasParent N 0 ?j1" by (rule oper_last_row0_haspar[OF hp i1 j0lt[unfolded i1]])
  have parR: "nextR N 0 (parent N 0 ?j1) ?j1"
    using hp0 unfolding hasParent_def parent_def by (rule theI')
  let ?pN = "parent N 0 ?j1"  let ?r = "?pN - ?j0"
  have parN0: "nextrel0 N ?pN ?j1" using parR by (simp add: nextR_def)
  have pNj1: "?pN < ?j1" using parN0 by (simp add: nextrel0_def)
  have floor: "entry N 0 ?j0 < entry N 0 ?j1"
  proof -
    have sle: "?w \<le> Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)" by simp
    have jle: "?j0 \<le> ?j1" using j0lt by linarith
    have jeq: "?j0 + ?w = ?j1" using jle by (rule le_add_diff_inverse)
    have flt: "entry N 0 ?j0 < entry N 0 (?j0 + ?w)"
      using oper_gen_strict_period_floor[OF hp j0lt w0 sle] .
    show ?thesis using flt unfolding jeq .
  qed
  have pNge: "?j0 \<le> ?pN"
  proof (rule ccontr)
    assume "\<not> ?j0 \<le> ?pN"
    hence plo: "?pN < ?j0" by simp
    have j0hi: "?j0 < ?j1" by (rule j0lt)
    have "entry N 0 ?j1 \<le> entry N 0 ?j0" using parN0 plo j0hi by (simp add: nextrel0_def)
    thus False using floor by simp
  qed
  have rw: "?r < ?w" using pNj1 pNge by linarith
  have psplit: "?pN = ?j0 + ?r" using pNge by simp
  let ?P = "?j0 + (q - 1) * ?w + ?r"
  have q1n: "q - 1 < n" using qn by linarith
  have eP: "entry ?Nn 0 ?P = entry N 0 ?pN + (q - 1) * ?d0"
    using blk[OF q1n rw] psplit by simp
  have floorid: "entry N 0 ?j0 + ?d0 = entry N 0 ?j1"
    using floor d0def by simp
  have qsplit: "\<And>z::nat. q * z = (q - 1) * z + z"
  proof -
    fix z :: nat
    have "q * z = (Suc (q - 1)) * z" using q1 by simp
    thus "q * z = (q - 1) * z + z" by simp
  qed
  have qw: "q * ?w = (q - 1) * ?w + ?w" by (rule qsplit)
  have qd: "q * ?d0 = (q - 1) * ?d0 + ?d0" by (rule qsplit)
  have qshift: "entry N 0 ?j1 + (q - 1) * ?d0 = entry N 0 ?j0 + q * ?d0"
  proof -
    have "entry N 0 ?j0 + q * ?d0 = entry N 0 ?j0 + ((q - 1) * ?d0 + ?d0)" using qd by simp
    also have "\<dots> = (entry N 0 ?j0 + ?d0) + (q - 1) * ?d0" by simp
    also have "\<dots> = entry N 0 ?j1 + (q - 1) * ?d0" using floorid by simp
    finally show ?thesis by simp
  qed
  have LngNn: "Lng ?Nn = ?j0 + n * ?w" using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have Bbound: "\<And>k. k < n \<Longrightarrow> ?j0 + k * ?w + ?w \<le> Lng ?Nn"
  proof -
    fix k assume "k < n" hence "Suc k \<le> n" by simp
    hence "Suc k * ?w \<le> n * ?w" by (rule mult_le_mono1)
    hence "?j0 + k * ?w + ?w \<le> ?j0 + n * ?w" by simp
    thus "?j0 + k * ?w + ?w \<le> Lng ?Nn" using LngNn by simp
  qed
  have xlt: "?x < Lng ?Nn"
  proof -
    have "?j0 + q * ?w < ?j0 + q * ?w + ?w"
      using w0 by (simp only: less_add_same_cancel1)
    thus ?thesis using Bbound[OF qn] by (rule less_le_trans)
  qed
  have Plt: "?P < Lng ?Nn"
  proof -
    have "?j0 + (q-1) * ?w + ?r < ?j0 + (q-1) * ?w + ?w"
      by (rule add_strict_left_mono[OF rw])
    thus ?thesis using Bbound[OF q1n] by (rule less_le_trans)
  qed
  have xeq: "?x = ?j0 + (q - 1) * ?w + ?w"
    by (simp only: qw add.assoc)
  have jeqw': "?j0 + ?w = ?j1" using j0lt[THEN less_imp_le] by (rule le_add_diff_inverse)
  have Px: "?P < ?x"
  proof -
    have "?j0 + (q-1) * ?w + ?r < ?j0 + (q-1) * ?w + ?w"
      by (rule add_strict_left_mono[OF rw])
    also have "\<dots> = ?x" using xeq by (rule sym)
    finally show ?thesis .
  qed
  have stepval: "entry ?Nn 0 ?P < entry ?Nn 0 ?x"
  proof -
    have a: "entry N 0 ?pN < entry N 0 ?j1" using parN0 by (simp add: nextrel0_def)
    have "entry ?Nn 0 ?P = entry N 0 ?pN + (q-1)*?d0" by (rule eP)
    also have "\<dots> < entry N 0 ?j1 + (q-1)*?d0" using a by simp
    also have "\<dots> = entry N 0 ?j0 + q*?d0" using qshift by simp
    also have "\<dots> = entry ?Nn 0 ?x" using ex by simp
    finally show ?thesis .
  qed
  have window: "\<And>j. ?P < j \<Longrightarrow> j < ?x \<Longrightarrow> entry ?Nn 0 ?x \<le> entry ?Nn 0 j"
  proof -
    fix j assume jlo: "?P < j" and jhi: "j < ?x"
    have jge: "?j0 + (q-1) * ?w \<le> j" using jlo by linarith
    let ?t = "j - (?j0 + (q-1) * ?w)"
    have tlo: "?r < ?t" using jlo by linarith
    have xeq': "?x = ?j0 + (q-1) * ?w + ?w" by (rule xeq)
    have thi: "?t < ?w" using jhi jge xeq' by linarith
    have jt: "j = ?j0 + (q-1) * ?w + ?t" using jge by (simp add: add.commute)
    have ej: "entry ?Nn 0 j = entry N 0 (?j0 + ?t) + (q-1) * ?d0"
      using blk[OF q1n thi] jt by simp
    have lo': "?pN < ?j0 + ?t" using tlo psplit by linarith
    have jeqw: "?j0 + ?w = ?j1" using j0lt[THEN less_imp_le] by (rule le_add_diff_inverse)
    have hi': "?j0 + ?t < ?j1" using thi jeqw by linarith
    have vN: "entry N 0 ?j1 \<le> entry N 0 (?j0 + ?t)" using parN0 lo' hi' by (simp add: nextrel0_def)
    have "entry ?Nn 0 ?x = entry N 0 ?j0 + q*?d0" by (rule ex)
    also have "\<dots> = entry N 0 ?j1 + (q-1)*?d0" using qshift by simp
    also have "\<dots> \<le> entry N 0 (?j0 + ?t) + (q-1)*?d0" using vN by simp
    also have "\<dots> = entry ?Nn 0 j" using ej by simp
    finally show "entry ?Nn 0 ?x \<le> entry ?Nn 0 j" .
  qed
  have edge: "nextrel0 ?Nn ?P ?x"
    unfolding nextrel0_def using Plt xlt Px stepval window by simp
  let ?Bp = "?j0 + (q - 1) * ?w"
  have eBp: "entry ?Nn 0 ?Bp = entry N 0 ?j0 + (q - 1) * ?d0"
    using blk[OF q1n w0] by simp
  have BpLT: "entry ?Nn 0 ?Bp < entry ?Nn 0 ?x"
  proof -
    have "entry N 0 ?j0 + (q-1)*?d0 < entry N 0 ?j0 + q*?d0"
    proof -
      have dpos: "0 < ?d0" using floor d0def by simp
      have "(q-1)*?d0 < q*?d0" using qd dpos by simp
      thus ?thesis by simp
    qed
    thus ?thesis using eBp ex by simp
  qed
  have uniqNn: "\<And>p'. nextrel0 ?Nn p' ?x \<Longrightarrow> p' = ?P"
  proof -
    fix p' assume Hp': "nextrel0 ?Nn p' ?x"
    have p'x: "p' < ?x" using Hp' by (simp add: nextrel0_def)
    have p'val: "\<And>j. p' < j \<Longrightarrow> j < ?x \<Longrightarrow> entry ?Nn 0 ?x \<le> entry ?Nn 0 j"
      using Hp' by (simp add: nextrel0_def)
    have Bpp: "?Bp \<le> p'"
    proof (rule ccontr)
      assume "\<not> ?Bp \<le> p'"
      hence pB: "p' < ?Bp" by simp
      have Bx: "?Bp < ?x" using Px psplit by linarith
      have "entry ?Nn 0 ?x \<le> entry ?Nn 0 ?Bp" using p'val[OF pB Bx] .
      thus False using BpLT by simp
    qed
    have xeqBp: "?x = ?Bp + ?w" using xeq by (simp add: add.assoc)
    have r'w: "p' - ?Bp < ?w" using p'x Bpp xeqBp by linarith
    have p'split: "p' = ?Bp + (p' - ?Bp)" using Bpp by simp
    have eP': "entry ?Nn 0 p' = entry N 0 (?j0 + (p' - ?Bp)) + (q-1) * ?d0"
      using blk[OF q1n r'w] p'split by (simp add: add.assoc)
    let ?pn = "?j0 + (p' - ?Bp)"
    have pnlt: "?pn < Lng N" using r'w j0lt by linarith
    have stepN: "nextrel0 N ?pn ?j1"
      unfolding nextrel0_def
    proof (intro conjI allI impI)
      show "?pn < Lng N" by (rule pnlt)
      show "?j1 < Lng N" using L by simp
      show "?pn < ?j1" using r'w j0lt by linarith
      have "entry ?Nn 0 p' < entry ?Nn 0 ?x" using Hp' by (simp add: nextrel0_def)
      hence "entry N 0 ?pn + (q-1)*?d0 < entry N 0 ?j0 + q*?d0" using eP' ex by simp
      hence "entry N 0 ?pn + (q-1)*?d0 < entry N 0 ?j1 + (q-1)*?d0" using qshift by simp
      thus "entry N 0 ?pn < entry N 0 ?j1" by simp
    next
      fix jj assume jjr: "?pn < jj \<and> jj < ?j1"
      hence jlo: "?pn < jj" and jhi: "jj < ?j1" by simp_all
      have jge: "?j0 \<le> jj" using jlo r'w by linarith
      let ?t = "jj - ?j0"
      have tw: "?t < ?w" using jhi jge jeqw' by linarith
      have jt: "jj = ?j0 + ?t" using jge by simp
      have tlo: "p' - ?Bp < ?t" using jlo p'split jt by linarith
      have Btlo: "p' < ?Bp + ?t" using jlo p'split jt by linarith
      have Bthi: "?Bp + ?t < ?x" using jhi jt xeqBp jge by linarith
      have "entry ?Nn 0 ?x \<le> entry ?Nn 0 (?Bp + ?t)" using p'val[OF Btlo Bthi] .
      hence "entry N 0 ?j0 + q*?d0 \<le> entry N 0 (?j0+?t) + (q-1)*?d0"
        using ex blk[OF q1n tw] by (simp add: add.assoc)
      hence "entry N 0 ?j1 + (q-1)*?d0 \<le> entry N 0 (?j0+?t) + (q-1)*?d0" using qshift by simp
      hence "entry N 0 ?j1 \<le> entry N 0 (?j0+?t)" by simp
      thus "entry N 0 ?j1 \<le> entry N 0 jj" using jt by simp
    qed
    have "?pn = ?pN" using idxsum_parent0_unique[of N ?pn ?j1 ?pN]
      stepN parN0 by (simp add: nextR_def)
    hence "?j0 + (p' - ?Bp) = ?j0 + ?r" using psplit by simp
    hence "p' - ?Bp = ?r" by simp
    thus "p' = ?P" using p'split by simp
  qed
  have parNn: "parent ?Nn 0 ?x = ?P"
  proof -
    have edgeR: "nextR ?Nn 0 ?P ?x" using edge by (simp add: nextR_def)
    have uniqR: "\<And>p'. nextR ?Nn 0 p' ?x \<Longrightarrow> p' = ?P"
      using uniqNn by (simp add: nextR_def)
    show ?thesis by (rule parent0_eqI[OF edgeR uniqR])
  qed
  from parNn show ?thesis .
qed

text \<open>§8.5 SURGERY gpar — the m=0 BOUNDARY column DISCHARGED (the binding case).
  Assembles the full gpar inequality for the block-start column \<open>Lng (M[q]) = j\<^sub>0+q\<cdot>w\<close>
  (\<open>= Lng Y\<close>, \<open>Y = M[q]\<close>, the \<open>m=0\<close> host of @{thm [source] m_8_5_surgery_fullprefix}):
  @{thm [source] oper_gen_row0_boundary_index} pins the row-0 parent at
  \<open>parent M 0 (Lng M-1) + (q-1)\<cdot>w\<close> (\<open>\<ge> parent M 0 (Lng M-1)\<close>), which exceeds
  \<open>TrMax (M[q])\<close> via the TRUNK INVARIANCE \<open>TrMax(M[q]) = TrMax M\<close> (obstacle-#1, supplied
  here as \<open>cinv\<close>) and the BASE deepen-trigger \<open>TrMax M < parent M 0 (Lng M-1)\<close> (\<open>basegpar\<close>,
  the un-iterated gpar for \<open>M\<close>, supplied by the surgery caller).  RedCondA-free.\<close>

lemma m_8_5_gpar_m0:
  fixes M :: pairseq and q :: nat
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
    and q1: "1 \<le> q"
    and basegpar: "TrMax M < parent M 0 (Lng M - 1)"
    and cinv: "TrMax (M[q]) = TrMax M"
  shows "TrMax (M[q]) < parent (M[Suc q]) 0 (Lng (M[q]))"
proof -
  define j0 where "j0 = parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  define w where "w = Lng M - 1 - j0"
  have qn: "q < Suc q" by simp
  have col: "Lng (M[q]) = j0 + q * w"
    unfolding j0_def w_def using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have idx: "parent (M[Suc q]) 0 (j0 + q * w)
              = j0 + (q - 1) * w + (parent M 0 (Lng M - 1) - j0)"
    unfolding j0_def w_def
    using oper_gen_row0_boundary_index[OF L notzero hp i1 j0lt q1 qn] by simp
  have ge: "parent M 0 (Lng M - 1) \<le> j0 + (q - 1) * w + (parent M 0 (Lng M - 1) - j0)"
    by linarith
  have "TrMax (M[q]) = TrMax M" by (rule cinv)
  also have "\<dots> < parent M 0 (Lng M - 1)" by (rule basegpar)
  also have "\<dots> \<le> j0 + (q - 1) * w + (parent M 0 (Lng M - 1) - j0)" by (rule ge)
  also have "\<dots> = parent (M[Suc q]) 0 (j0 + q * w)" using idx by (rule sym)
  also have "\<dots> = parent (M[Suc q]) 0 (Lng (M[q]))" using col by simp
  finally show ?thesis .
qed

text \<open>§8.5 SURGERY gpar BRIDGE (b) — ROW-0 oper parent lower bound at an INTERIOR
  column (m = s ≥ 1).  For an interior column \<open>x = j\<^sub>0 + q\<cdot>w + s\<close> (\<open>0 < s < w\<close>) of
  the iterate \<open>N[n]\<close>, the row-0 parent stays IN BLOCK \<open>q\<close>:
    \<open>parent (N[n]) 0 x \<ge> j\<^sub>0 + q\<cdot>w\<close>  (the block-\<open>q\<close> START).
  Key: \<open>j\<^sub>0\<close> is the STRICT row-0 MINIMUM of the whole active block
  (@{thm [source] oper_gen_strict_period_floor} holds at EVERY offset \<open>0<s\<le>w\<close>, not
  just the endpoints), so the block-\<open>q\<close> start (row-0 value \<open>e\<^sub>0(N,j\<^sub>0)+q\<cdot>d\<^sub>0\<close>) is
  STRICTLY below \<open>x\<close> (row-0 \<open>e\<^sub>0(N,j\<^sub>0+s)+q\<cdot>d\<^sub>0\<close>); were the parent left of the block
  start, the \<open>nextrel0\<close> valley clause would force the start \<open>\<ge> x\<close>, contradiction.
  RedCondA-FREE (only @{thm [source] oper_gen_block_entry0} +
  @{thm [source] oper_gen_strict_period_floor}).  Since \<open>j\<^sub>0+q\<cdot>w = Lng (N[q]) > TrMax\<close>,
  interior columns clear gpar with NO appeal to base-gpar — only the trunk invariance.\<close>

lemma oper_gen_row0_interior_lower:
  fixes N :: pairseq and n q s :: nat
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n" and s0: "0 < s"
    and sw: "s < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and hpx: "hasParent ((N::pairseq)[n]) 0
                (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + s)"
  shows "parent N (idx1 N (Lng N - 1)) (Lng N - 1)
           + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
       \<le> parent ((N::pairseq)[n]) 0
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + s)"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?d0 = "if 0 < ?i1 then entry N 0 ?j1 - entry N 0 ?j0 else 0"
  let ?Nn = "(N::pairseq)[n]"
  let ?B = "?j0 + q * ?w"  let ?x = "?B + s"
  have w0: "0 < ?w" using j0lt by linarith
  have eB: "entry ?Nn 0 ?B = entry N 0 ?j0 + q * ?d0"
    using oper_gen_block_entry0[OF L notzero hp j0lt qn w0] by simp
  have eX: "entry ?Nn 0 ?x = entry N 0 (?j0 + s) + q * ?d0"
    using oper_gen_block_entry0[OF L notzero hp j0lt qn sw] by (simp add: add.assoc)
  have sle: "s \<le> ?w" using sw by simp
  have fl: "entry N 0 ?j0 < entry N 0 (?j0 + s)"
    using oper_gen_strict_period_floor[OF hp j0lt s0 sle] .
  have BX: "entry ?Nn 0 ?B < entry ?Nn 0 ?x" using eB eX fl by simp
  have parR: "nextrel0 ?Nn (parent ?Nn 0 ?x) ?x"
  proof -
    have "nextR ?Nn 0 (parent ?Nn 0 ?x) ?x"
      using hpx unfolding hasParent_def parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  have v: "\<forall>j. parent ?Nn 0 ?x < j \<and> j < ?x \<longrightarrow> entry ?Nn 0 ?x \<le> entry ?Nn 0 j"
    using parR by (simp add: nextrel0_def)
  show "?B \<le> parent ?Nn 0 ?x"
  proof (rule ccontr)
    assume "\<not> ?B \<le> parent ?Nn 0 ?x"
    hence pB: "parent ?Nn 0 ?x < ?B" by simp
    have Bx: "?B < ?x" using s0 by simp
    have "entry ?Nn 0 ?x \<le> entry ?Nn 0 ?B" using v pB Bx by blast
    thus False using BX by simp
  qed
qed

text \<open>§8.5 SURGERY gpar — the INTERIOR columns DISCHARGED (m = s ≥ 1).  Assembles the
  gpar inequality for every interior host column \<open>Lng (M[q]) + s = j\<^sub>0+q\<cdot>w+s\<close>
  (\<open>0 < s < w\<close>): @{thm [source] oper_gen_row0_interior_lower} pins the row-0 parent
  \<open>\<ge> j\<^sub>0+q\<cdot>w = Lng (M[q])\<close>, which already exceeds \<open>TrMax (M[q]) = TrMax M\<close> (\<open>cinv\<close>),
  since \<open>TrMax M < parent M 0 (Lng M-1) < Lng M-1 = j\<^sub>0+w \<le> j\<^sub>0+q\<cdot>w\<close> (\<open>basegpar\<close>, \<open>q\<ge>1\<close>).
  The interior \<open>hasParent\<close> witness comes from the iterate being reduced-standard
  (@{thm [source] m_6_6_monoT_hasParent0}, \<open>M[Suc q] \<in> PT_PS\<close>, first column \<open>(0,0)\<close>).
  RedCondA-free.\<close>

lemma m_8_5_gpar_interior:
  fixes M :: pairseq and q s :: nat
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
    and q1: "1 \<le> q" and s0: "0 < s"
    and sw: "s < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and basegpar: "TrMax M < parent M 0 (Lng M - 1)"
    and cinv: "TrMax (M[q]) = TrMax M"
    and MSq_pt: "(M::pairseq)[Suc q] \<in> PT_PS"
    and e00: "entry ((M::pairseq)[Suc q]) 0 0 = 0"
  shows "TrMax (M[q]) < parent (M[Suc q]) 0 (Lng (M[q]) + s)"
proof -
  define j0 where "j0 = parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  define w where "w = Lng M - 1 - j0"
  have qn: "q < Suc q" by simp
  have j0le: "j0 < Lng M - 1" using j0lt unfolding j0_def .
  have sw': "s < w" using sw unfolding w_def j0_def .
  have LY: "Lng (M[q]) = j0 + q * w"
    unfolding j0_def w_def using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have LSq: "Lng (M[Suc q]) = j0 + Suc q * w"
    unfolding j0_def w_def using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have MT: "(M::pairseq)[Suc q] \<in> T_PS" and mono: "monoT ((M::pairseq)[Suc q])"
    using MSq_pt by (simp_all add: PT_PS_def)
  have colpos: "0 < j0 + q * w + s" using s0 by simp
  have collt: "j0 + q * w + s < Lng (M[Suc q])"
  proof -
    have "j0 + q * w + s < j0 + q * w + w" using sw' by simp
    also have "\<dots> = j0 + Suc q * w" by simp
    also have "\<dots> = Lng (M[Suc q])" using LSq by (rule sym)
    finally show ?thesis .
  qed
  have hpx: "hasParent (M[Suc q]) 0 (j0 + q * w + s)"
    by (rule m_6_6_monoT_hasParent0[OF MT mono e00 colpos collt])
  have lb: "j0 + q * w \<le> parent (M[Suc q]) 0 (j0 + q * w + s)"
  proof -
    have "parent M (idx1 M (Lng M - 1)) (Lng M - 1)
            + q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1))
          \<le> parent (M[Suc q]) 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1)
                + q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s)"
      by (rule oper_gen_row0_interior_lower[OF L notzero hp j0lt qn s0 sw hpx[unfolded j0_def w_def]])
    thus ?thesis unfolding j0_def w_def .
  qed
  have par0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
  proof -
    have hp0: "hasParent M 0 (Lng M - 1)" by (rule oper_last_row0_haspar[OF hp i1 j0lt[unfolded i1]])
    have "nextR M 0 (parent M 0 (Lng M - 1)) (Lng M - 1)"
      using hp0 unfolding hasParent_def parent_def by (rule theI')
    hence "nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1)" by (simp add: nextR_def)
    thus ?thesis by (simp add: nextrel0_def)
  qed
  have tlt: "TrMax M < j0 + q * w"
  proof -
    have j1eq: "Lng M - 1 = j0 + w" unfolding w_def using j0le by simp
    have wle: "w \<le> q * w" using mult_le_mono1[OF q1, of w] by simp
    have "TrMax M < parent M 0 (Lng M - 1)" by (rule basegpar)
    also have "\<dots> < Lng M - 1" by (rule par0lt)
    also have "\<dots> = j0 + w" by (rule j1eq)
    also have "\<dots> \<le> j0 + q * w" using wle by simp
    finally show ?thesis .
  qed
  have "TrMax (M[q]) = TrMax M" by (rule cinv)
  also have "\<dots> < j0 + q * w" by (rule tlt)
  also have "\<dots> \<le> parent (M[Suc q]) 0 (j0 + q * w + s)" by (rule lb)
  finally have "TrMax (M[q]) < parent (M[Suc q]) 0 (j0 + q * w + s)" .
  thus ?thesis using LY by simp
qed

text \<open>§8.5 SURGERY gpar — PER-COLUMN, ALL m (the full geometric residual on the
  iterate).  Combines @{thm [source] m_8_5_gpar_m0} (the \<open>m=0\<close> block start) and
  @{thm [source] m_8_5_gpar_interior} (interior \<open>0<m<w\<close>) into the single deepen-trigger
  for EVERY appended column \<open>m < w = Lng B\<close>:
    \<open>TrMax (M[q]) < parent (M[Suc q]) 0 (Lng (M[q]) + m)\<close>.
  With \<open>Y = M[q]\<close>, \<open>Y \<frown> B = M[Suc q]\<close> (\<open>Lng B = w\<close>) this is EXACTLY the gpar residual
  of @{thm [source] m_8_5_surgery_fullprefix} pulled onto the full iterate by
  @{thm [source] m_8_5_parent_host} (parent) and @{thm [source] m_8_5_TrMax_host}
  (trunk).  RedCondA-free; rests on the trunk invariance \<open>cinv\<close> (= mk's obstacle-#1
  \<open>TrMax (M[q]) = TrMax M\<close>) and the base deepen-trigger \<open>basegpar\<close>
  (\<open>TrMax M < parent M 0 (Lng M-1)\<close>, the un-iterated gpar for \<open>M\<close>, from the caller).\<close>

lemma m_8_5_gpar_col:
  fixes M :: pairseq and q m :: nat
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
    and q1: "1 \<le> q"
    and mw: "m < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and basegpar: "TrMax M < parent M 0 (Lng M - 1)"
    and cinv: "TrMax (M[q]) = TrMax M"
    and MSq_pt: "(M::pairseq)[Suc q] \<in> PT_PS"
    and e00: "entry ((M::pairseq)[Suc q]) 0 0 = 0"
  shows "TrMax (M[q]) < parent (M[Suc q]) 0 (Lng (M[q]) + m)"
proof (cases "m = 0")
  case True
  have "TrMax (M[q]) < parent (M[Suc q]) 0 (Lng (M[q]))"
    by (rule m_8_5_gpar_m0[OF L notzero hp i1 j0lt q1 basegpar cinv])
  thus ?thesis using True by simp
next
  case False
  hence s0: "0 < m" by simp
  show ?thesis
    by (rule m_8_5_gpar_interior[OF L notzero hp i1 j0lt q1 s0 mw basegpar cinv MSq_pt e00])
qed

text \<open>§8.5 ENDPOINT (BLOCKER-1 prep) — the condV period-block \<open>c\<^sub>2 = transC2\<close> CLOSED
  FORM.  Under \<open>transCondV M\<close> (the condV branch of the @{const transC2} definition,
  shared with condI/condIII), the substituted period block collapses to a SINGLE
  trailing-leaf principal: \<open>c\<^sub>2 = D\<^bsub>v\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<^sub>B)\<close> with \<open>v = transV M\<close>,
  \<open>t\<^sub>2 = transT2 M\<close>, \<open>j\<^sub>1 = Lng M-1\<close>.  This is exactly the per-column block that the
  endpoint netfold \<open>scbSubst (transC1 host\<^sub>m) (transC2 host\<^sub>m)\<close> grafts into the
  accumulator; the \<open>+\<^sub>B D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<^sub>B\<close> tail is what advances the spine one column.\<close>

lemma m_8_5_transC2_condV:
  fixes M :: pairseq
  assumes "transCondV M"
  shows "transC2 M
       = Dpt (transV M) (transT2 M +\<^sub>B Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
  using assms by (simp add: transC2_def Let_def transJ1_def)

text \<open>§7.4 KEYSTONE (BLOCKER-1/B2 building block) — the marked-column → spine-DEPTH
  SPLIT, re-exported clean from @{thm [source] m_7_4_RightNodes_Mark}.  For a marked
  interior column \<open>(M,m)\<close> the right-spine of \<open>Trans M\<close> factors as
    \<open>RightNodes (Trans M) = RightNodes (Trans (seg M 0 m)) \<frown> tl (RightNodes (Mark M m))\<close>,
  i.e. the column-\<open>m\<close> prefix slice carries the TOP \<open>RightNodes (Trans (seg M 0 m))\<close>
  (whose LAST node is the marked head \<open>M\<^bsub>1,m\<^esub>\<close>) and \<open>Mark M m\<close> carries the suffix
  spine FROM the marked node (its HEAD is \<open>M\<^bsub>1,m\<^esub>\<close>).  Hence the marked column sits at
  spine DEPTH \<open>length (RightNodes (Trans (seg M 0 m))) − 1\<close>; combined with the strict
  monotonicity @{thm [source] RightNodes_seg_len_strict_mono} this is the single
  column → depth datum feeding BOTH the netfold per-column positions (B1) and the
  deepest-slot localization (B2).  Pure re-export of GREEN PSS_B infra.\<close>

lemma m_8_5_Mark_RightNodes_split:
  fixes M :: pairseq and m :: nat
  assumes mk: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS"
    and m0: "0 < m" and mlt: "m < Lng M - 1"
  shows "RightNodes (Trans M)
           = RightNodes (Trans (seg M 0 m)) @ tl (RightNodes (Mark M m))"
    and "hd (RightNodes (Mark M m)) = entry M 1 m"
    and "RightNodes (Mark M m) \<noteq> []"
    and "last (RightNodes (Trans (seg M 0 m))) = entry M 1 m"
proof -
  obtain a0 a1 where
    RT: "RightNodes (Trans M) = a0 @ [entry M 1 m] @ a1"
    and RS: "RightNodes (Trans (seg M 0 m)) = a0 @ [entry M 1 m]"
    and RM: "RightNodes (Mark M m) = [entry M 1 m] @ a1"
    using m_7_4_RightNodes_Mark[OF mk MR m0 mlt] by blast
  have tlM: "tl (RightNodes (Mark M m)) = a1" using RM by simp
  show "RightNodes (Trans M)
          = RightNodes (Trans (seg M 0 m)) @ tl (RightNodes (Mark M m))"
    using RT RS tlM by simp
  show "hd (RightNodes (Mark M m)) = entry M 1 m" using RM by simp
  show "RightNodes (Mark M m) \<noteq> []" using RM by simp
  show "last (RightNodes (Trans (seg M 0 m))) = entry M 1 m" using RS by simp
qed

text \<open>§7.4 ENDPOINT (BLOCKER-1 #1 part (a)) — the marked-core WHOLE-Trans
  LOCALIZATION.  For a marked interior column \<open>(M,m)\<close>, the marked core \<open>Mark M m\<close>
  occurs as a flat \<open>scb\<close>-BLOCK of \<open>Trans M\<close>: \<open>scb_decomp (Trans M) s (flatBT (Mark M m))
  b\<close>.  This is the existential half of the §7.4 keystone @{thm [source]
  m_7_4_Trans_Mark_seg}; with \<open>M = Pred (host\<^sub>k) = Y \<frown> take k B\<close> and \<open>m = transJm1
  host\<^sub>k\<close> the block is exactly \<open>transC1 host\<^sub>k = Mark (Pred host\<^sub>k) (transJm1 host\<^sub>k)\<close>, so
  the netfold's marked core is localized in the WHOLE \<open>Trans (Pred host\<^sub>k)\<close> for free.
  The remaining step (DESCEND this to the deepest slot \<open>spineLeaf (Trans (Pred
  host\<^sub>k))\<close> by stripping the \<open>D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> \<langle>\<cdot>\<rangle>)\<close> wrapper) is the
  reverse-of-@{thm [source] scb_addBT_left} descent, supplied with the spine-form from
  the surgery context.\<close>

lemma m_8_5_Mark_whole_loc:
  fixes M :: pairseq and m :: nat
  assumes mk: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS"
    and m0: "0 < m" and mlt: "m < Lng M - 1"
  shows "\<exists>s b. scb_decomp (Trans M) s (flatBT (Mark M m)) b"
proof -
  obtain sb where
    "scb_decomp (Trans (seg M 0 m)) (fst sb)
        (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) (snd sb)
     \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
    using m_7_4_Trans_Mark_seg[OF mk MR m0 mlt] by (blast dest: ex1_implies_ex)
  thus ?thesis by blast
qed

text \<open>§7.4/§8.5 ENDPOINT (BLOCKER-1 netfold, WHOLE-Trans recurrence) — the per-column
  \<open>Trans\<close> step at the WHOLE level, free from base.  For a condV-shaped \<open>M\<close>
  (\<open>monoT\<close>, \<open>j\<^sub>1>0\<close>, \<open>t\<^sub>1\<noteq>0\<close>), @{thm [source] trans_surgery_localized} localizes the
  marked core \<open>transC1 M\<close> in \<open>Trans (Pred M)\<close> and rewrites \<open>Trans M\<close> as the SAME scb
  context with \<open>transC1 M\<close> replaced by the period block \<open>transC2 M\<close>:
    \<open>Trans M = scbSubst (transC1 M) (transC2 M) (Trans (Pred M))\<close>.
  This is the per-column netfold operator acting at the WHOLE-Trans level (where the
  scb position is given for free, NO slot-descent needed); composing it over the
  appended block \<open>B\<close> and taking \<open>spineLeaf\<close> at the end gives the endpoint without
  descending each column into the spine slot.\<close>

lemma m_8_5_Trans_scbSubst_whole:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
  shows "Trans M = scbSubst (transC1 M) (transC2 M) (Trans (Pred M))"
proof -
  obtain s1 b1 body2 where
    dsd: "scb_decomp (Trans (Pred M)) s1 (flatBT (Dpt (transV M) (transT2 M))) b1"
    and tM: "Trans M = unflatBT (s1 @ flatBT (Dpt (transV M) body2) @ b1)"
    and c1eq: "transC1 M = Dpt (transV M) (transT2 M)"
    and c2eq: "transC2 M = Dpt (transV M) body2"
    using trans_surgery_localized[OF MR MP J1pos T1] by blast
  have tpne: "Trans (Pred M) \<noteq> Trm []" using T1 by (simp add: transT1_def)
  have dsd': "scb_decomp (Trans (Pred M)) s1 (flatBT (transC1 M)) b1"
    using dsd c1eq by simp
  have "scbSubst (transC1 M) (transC2 M) (Trans (Pred M))
          = unflatBT (s1 @ flatBT (transC2 M) @ b1)"
    by (rule scbSubst_eq[OF dsd' tpne])
  also have "\<dots> = unflatBT (s1 @ flatBT (Dpt (transV M) body2) @ b1)"
    using c2eq by simp
  also have "\<dots> = Trans M" using tM by (rule sym)
  finally show ?thesis by (rule sym)
qed

text \<open>§8.5 ENDPOINT (BLOCKER-1 netfold, WHOLE-Trans telescoping SKELETON).  Given the
  per-column WHOLE-Trans step (@{thm [source] m_8_5_Trans_scbSubst_whole} instantiated
  at \<open>host\<^sub>m = Y \<frown> take (Suc m) B\<close>), the \<open>fold\<close> over the appended block composes the
  per-column operators into one net transform: \<open>fold op [0..<Lng B] (Trans Y) =
  Trans (Y \<frown> B)\<close>.  Pure \<open>take m B\<close>-induction, no scb content (the content is in the
  per-column \<open>step\<close>).  Composed with the WHOLE-level recurrence this realises the
  netfold at the whole-Trans level — NO per-column slot descent — leaving only the
  endpoint \<open>spineLeaf (Trans (Y \<frown> B)) = bpHeadT (Trans Y)\<close> (taken once at the end).\<close>

lemma m_8_5_scbSubst_netfold:
  fixes Y B :: pairseq and op :: "nat \<Rightarrow> BT \<Rightarrow> BT"
  assumes step: "\<And>m. m < Lng B \<Longrightarrow> Trans (Y @ take (Suc m) B) = op m (Trans (Y @ take m B))"
  shows "Trans (Y @ B) = fold op [0..<Lng B] (Trans Y)"
proof -
  have gen: "\<And>k. k \<le> Lng B \<Longrightarrow> fold op [0..<k] (Trans Y) = Trans (Y @ take k B)"
  proof -
    fix k show "k \<le> Lng B \<Longrightarrow> fold op [0..<k] (Trans Y) = Trans (Y @ take k B)"
    proof (induct k)
      case 0 thus ?case by simp
    next
      case (Suc k)
      have kle: "k \<le> Lng B" using Suc.prems by simp
      have klt: "k < Lng B" using Suc.prems by simp
      have "fold op [0..<Suc k] (Trans Y) = op k (fold op [0..<k] (Trans Y))" by simp
      also have "\<dots> = op k (Trans (Y @ take k B))" using Suc.hyps kle by simp
      also have "\<dots> = Trans (Y @ take (Suc k) B)" using step[OF klt] by (rule sym)
      finally show ?case .
    qed
  qed
  have "fold op [0..<Lng B] (Trans Y) = Trans (Y @ take (Lng B) B)" using gen by simp
  thus ?thesis by simp
qed

text \<open>§8.5 ENDPOINT (BLOCKER-1 netfold, ASSEMBLED at the WHOLE level).  Combines the
  per-column WHOLE-Trans recurrence (@{thm [source] m_8_5_Trans_scbSubst_whole} at each
  host (Y @ take m B) @ [B!m] = Y @ take (Suc m) B) with the telescoping skeleton
  (@{thm [source] m_8_5_scbSubst_netfold}): the per-column scbSubst operators compose
  into the WHOLE-Trans identity
    Trans (Y @ B) = fold (\<lambda>m acc. scbSubst (transC1 host) (transC2 host) acc)
                         [0..<Lng B] (Trans Y).
  The per-column hypotheses (host in RT_PS and PT_PS, transJ1 host > 0, transT1 host
  nonzero) are exactly the surgery's per-column membership/depth residuals
  (gMR/gMP/gj1gt + the predecessor-slice nonzero).  This is the netfold at the
  whole-Trans level (NO slot descent); the endpoint spineLeaf (Trans (Y @ B)) =
  bpHeadT (Trans Y) is the single final spineLeaf-readback of this fold.\<close>

lemma m_8_5_Trans_netfold_condV:
  fixes Y B :: pairseq
  assumes hostR: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> RT_PS"
    and hostP: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> PT_PS"
    and hostJ1: "\<And>m. m < Lng B \<Longrightarrow> transJ1 ((Y @ take m B) @ [B ! m]) > 0"
    and hostT1: "\<And>m. m < Lng B \<Longrightarrow> transT1 ((Y @ take m B) @ [B ! m]) \<noteq> 0\<^sub>B"
  shows "Trans (Y @ B)
       = fold (\<lambda>m acc. scbSubst (transC1 ((Y @ take m B) @ [B ! m]))
                                 (transC2 ((Y @ take m B) @ [B ! m])) acc)
              [0..<Lng B] (Trans Y)"
proof -
  have step: "\<And>m. m < Lng B \<Longrightarrow>
        Trans (Y @ take (Suc m) B)
          = scbSubst (transC1 ((Y @ take m B) @ [B ! m]))
                     (transC2 ((Y @ take m B) @ [B ! m])) (Trans (Y @ take m B))"
  proof -
    fix m assume m: "m < Lng B"
    have host: "(Y @ take m B) @ [B ! m] = Y @ take (Suc m) B"
      using m by (simp add: take_Suc_conv_app_nth)
    have L1: "1 < Lng ((Y @ take m B) @ [B ! m])"
      using hostJ1[OF m] by (simp add: transJ1_def)
    have bl: "butlast ((Y @ take m B) @ [B ! m]) = Y @ take m B" by (rule butlast_snoc)
    have pred: "Pred ((Y @ take m B) @ [B ! m]) = Y @ take m B"
    proof -
      have "Pred ((Y @ take m B) @ [B ! m]) = butlast ((Y @ take m B) @ [B ! m])"
        using L1 by (simp add: Pred_def)
      thus ?thesis using bl by simp
    qed
    have rec: "Trans ((Y @ take m B) @ [B ! m])
                 = scbSubst (transC1 ((Y @ take m B) @ [B ! m]))
                            (transC2 ((Y @ take m B) @ [B ! m]))
                            (Trans (Pred ((Y @ take m B) @ [B ! m])))"
      by (rule m_8_5_Trans_scbSubst_whole[OF hostR[OF m] hostP[OF m] hostJ1[OF m] hostT1[OF m]])
    have rec2: "Trans ((Y @ take m B) @ [B ! m])
                 = scbSubst (transC1 ((Y @ take m B) @ [B ! m]))
                            (transC2 ((Y @ take m B) @ [B ! m])) (Trans (Y @ take m B))"
      using rec pred by simp
    have lhs: "Trans (Y @ take (Suc m) B) = Trans ((Y @ take m B) @ [B ! m])"
      using host by simp
    show "Trans (Y @ take (Suc m) B)
            = scbSubst (transC1 ((Y @ take m B) @ [B ! m]))
                       (transC2 ((Y @ take m B) @ [B ! m])) (Trans (Y @ take m B))"
      using lhs rec2 by simp
  qed
  show ?thesis
    by (rule m_8_5_scbSubst_netfold
          [where op = "\<lambda>m acc. scbSubst (transC1 ((Y @ take m B) @ [B ! m]))
                                          (transC2 ((Y @ take m B) @ [B ! m])) acc",
           OF step])
qed

text \<open>§8.5 ENDPOINT (BLOCKER-1 netfold, MEMBERSHIPS DISCHARGED).  Wires the per-column
  membership/depth hypotheses of @{thm [source] m_8_5_Trans_netfold_condV} from the
  surgery-level facts: \<open>Y@B \<in> ST_PS \<inter> PT_PS\<close>, \<open>1 < Lng Y\<close>, \<open>Trans Y \<noteq> 0_B\<close>.
  The per-column host \<open>(Y@take m B)@[B!m] = Y@take(Suc m)B\<close> is a take-prefix of
  \<open>Y@B\<close>, so RT_PS/PT_PS come from @{thm [source] m_8_5_fullprefix_RT} /
  @{thm [source] m_8_5_fullprefix_PT}; \<open>transJ1>0\<close> from \<open>1<Lng Y\<close>; the predecessor
  \<open>transT1 = Trans(Y@take m B) \<noteq> 0_B\<close> from monoT (\<open>\<not> zeroT\<close>) via
  @{thm [source] m_7_3_Trans_zeroT} (m\<ge>1) or \<open>Trans Y \<noteq> 0_B\<close> (m=0).  This is the
  surgery-ready netfold — one of the two inputs to endpt's \<open>m_8_5_surgery_whole\<close>.\<close>

lemma m_8_5_Trans_netfold_surgery:
  fixes Y B :: pairseq
  assumes Nst: "Y @ B \<in> ST_PS" and Npt: "Y @ B \<in> PT_PS"
    and YL2: "1 < Lng Y" and TY0: "Trans Y \<noteq> 0\<^sub>B"
  shows "Trans (Y @ B)
       = fold (\<lambda>m acc. scbSubst (transC1 ((Y @ take m B) @ [B ! m]))
                                 (transC2 ((Y @ take m B) @ [B ! m])) acc)
              [0..<Lng B] (Trans Y)"
proof -
  have hostR: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> RT_PS"
  proof -
    fix m assume m: "m < Lng B"
    have e: "(Y @ take m B) @ [B ! m] = Y @ take (Suc m) B"
      using m by (simp add: take_Suc_conv_app_nth)
    have "Y @ take (Suc m) B \<in> RT_PS" by (rule m_8_5_fullprefix_RT[OF Nst]; simp)
    thus "(Y @ take m B) @ [B ! m] \<in> RT_PS" using e by simp
  qed
  have hostP: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> PT_PS"
  proof -
    fix m assume m: "m < Lng B"
    have e: "(Y @ take m B) @ [B ! m] = Y @ take (Suc m) B"
      using m by (simp add: take_Suc_conv_app_nth)
    have sm: "0 < Suc m" by simp
    have smle: "Suc m \<le> Lng B" using m by simp
    have l2: "1 < Lng Y + Suc m" using YL2 by linarith
    have "Y @ take (Suc m) B \<in> PT_PS" by (rule m_8_5_fullprefix_PT[OF Nst Npt sm smle l2])
    thus "(Y @ take m B) @ [B ! m] \<in> PT_PS" using e by simp
  qed
  have hostJ1: "\<And>m. m < Lng B \<Longrightarrow> transJ1 ((Y @ take m B) @ [B ! m]) > 0"
  proof -
    fix m assume m: "m < Lng B"
    have mle: "m \<le> Lng B" using m by simp
    have Lh: "Lng ((Y @ take m B) @ [B ! m]) = Lng Y + m + 1"
      using mle by (simp add: min.absorb1)
    have "transJ1 ((Y @ take m B) @ [B ! m]) = Lng Y + m"
      using Lh by (simp add: transJ1_def)
    thus "transJ1 ((Y @ take m B) @ [B ! m]) > 0" using YL2 by linarith
  qed
  have hostT1: "\<And>m. m < Lng B \<Longrightarrow> transT1 ((Y @ take m B) @ [B ! m]) \<noteq> 0\<^sub>B"
  proof -
    fix m assume m: "m < Lng B"
    have L1: "1 < Lng ((Y @ take m B) @ [B ! m])"
      using hostJ1[OF m] by (simp add: transJ1_def)
    have bl: "butlast ((Y @ take m B) @ [B ! m]) = Y @ take m B" by (rule butlast_snoc)
    have predh: "Pred ((Y @ take m B) @ [B ! m]) = Y @ take m B"
    proof -
      have "Pred ((Y @ take m B) @ [B ! m]) = butlast ((Y @ take m B) @ [B ! m])"
        using L1 by (simp add: Pred_def)
      thus ?thesis using bl by simp
    qed
    have tne: "Trans (Y @ take m B) \<noteq> 0\<^sub>B"
    proof (cases "m = 0")
      case True thus ?thesis using TY0 by simp
    next
      case False
      have m0: "0 < m" using False by simp
      have mle: "m \<le> Lng B" using m by simp
      have l2m: "1 < Lng Y + m" using YL2 by linarith
      have RTm: "Y @ take m B \<in> RT_PS" by (rule m_8_5_fullprefix_RT[OF Nst m0])
      have PTm: "Y @ take m B \<in> PT_PS" by (rule m_8_5_fullprefix_PT[OF Nst Npt m0 mle l2m])
      have "monoT (Y @ take m B)" using PTm by (simp add: PT_PS_def)
      hence "\<not> zeroT (Y @ take m B)" by (simp add: monoT_def)
      thus ?thesis using m_7_3_Trans_zeroT[OF RTm] by simp
    qed
    show "transT1 ((Y @ take m B) @ [B ! m]) \<noteq> 0\<^sub>B"
      using predh tne by (simp add: transT1_def)
  qed
  show ?thesis
    by (rule m_8_5_Trans_netfold_condV[OF hostR hostP hostJ1 hostT1])
qed


text \<open>§8.5 SURGERY gpar — FINAL ASSEMBLY.  Discharges the \<open>\<forall>m\<close> gpar (deepen-trigger)
  residual of @{thm [source] m_8_5_surgery_fullprefix} for the genuine oper-iterate
  surgery \<open>Y = M[q]\<close>, \<open>Y \<frown> B = M[Suc q]\<close> (\<open>B\<close> the appended period block).  For each
  appended column \<open>m < Lng B\<close>, the per-column gpar @{thm [source] m_8_5_gpar_col}
  (\<open>TrMax (M[q]) < parent (M[Suc q]) 0 (Lng (M[q]) + m)\<close>) transports onto the host
  \<open>(Y \<frown> take m B) \<frown> [B!m]\<close> via the two bridges @{thm [source] m_8_5_parent_host} (the
  host's row-0 parent reads off the full iterate) and @{thm [source] m_8_5_TrMax_host}
  (host trunk \<open>= TrMax Y\<close>, from \<open>Br Y \<noteq> []\<close> and the host \<in> T_PS, the latter from the
  iterate's standardness via @{thm [source] T_PS_take}).  RedCondA-free; rests on the
  un-iterated deepen \<open>basegpar\<close> and the trunk invariance \<open>cinv\<close> (= obstacle-#1).  This
  is the remaining geometric input to @{thm [source] m_8_5_surgery_fullprefix} (whose
  \<open>gBrne\<close> residual then follows from this via @{thm [source] m_8_5_gBrne_from_gpar}).
  Empirically: gpar/gBrne hold 36/36 on genuine deepen-condV oper iterates.\<close>

lemma m_8_5_gpar_fullprefix:
  fixes M B :: pairseq and q :: nat
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
    and q1: "1 \<le> q"
    and basegpar: "TrMax M < parent M 0 (Lng M - 1)"
    and cinv: "TrMax ((M::pairseq)[q]) = TrMax M"
    and Nst: "(M::pairseq)[Suc q] \<in> ST_PS"
    and MSq_pt: "(M::pairseq)[Suc q] \<in> PT_PS"
    and e00: "entry ((M::pairseq)[Suc q]) 0 0 = 0"
    and BrY: "Br ((M::pairseq)[q]) \<noteq> []"
    and app: "(M::pairseq)[Suc q] = (M::pairseq)[q] @ B"
  shows "\<forall>m<Lng B. TrMax (((M::pairseq)[q] @ take m B) @ [B ! m])
            < parent (((M::pairseq)[q] @ take m B) @ [B ! m]) 0
                (Lng (((M::pairseq)[q] @ take m B) @ [B ! m]) - 1)"
proof (intro allI impI)
  fix m assume m: "m < Lng B"
  define j0 where "j0 = parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  define w where "w = Lng M - 1 - j0"
  have w0: "0 < w" using j0lt unfolding w_def j0_def by simp
  have qwpos: "0 < q * w"
  proof -
    have "w \<le> q * w" using mult_le_mono1[OF q1, of w] by simp
    thus ?thesis using w0 by linarith
  qed
  have Lq: "Lng ((M::pairseq)[q]) = j0 + q * w"
    unfolding j0_def w_def using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have LSq: "Lng ((M::pairseq)[Suc q]) = j0 + Suc q * w"
    unfolding j0_def w_def using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have LB: "Lng B = w"
  proof -
    have "Lng ((M::pairseq)[Suc q]) = Lng ((M::pairseq)[q]) + Lng B" using app by simp
    hence "j0 + Suc q * w = (j0 + q * w) + Lng B" using Lq LSq by simp
    thus ?thesis by simp
  qed
  have mw: "m < w" using m LB by simp
  have mw': "m < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    using mw unfolding w_def j0_def by simp
  let ?Y = "(M::pairseq)[q]"
  let ?h = "(?Y @ take m B) @ [B ! m]"
  have hlen: "Lng ?h = Lng ?Y + Suc m" using m by simp
  have lh: "Lng ?h - 1 = Lng ?Y + m" using hlen by simp
  have Ypos: "0 < Lng ?Y" using Lq qwpos by linarith
  have hpos: "0 < Lng ?h" using hlen by simp
  have Yeq: "?Y = take (Lng ?Y) ((M::pairseq)[Suc q])"
  proof -
    have "take (Lng ?Y) ((M::pairseq)[Suc q]) = take (Lng ?Y) (?Y @ B)" using app by simp
    also have "\<dots> = ?Y" by simp
    finally show ?thesis by (rule sym)
  qed
  have YT: "?Y \<in> T_PS" using T_PS_take[OF Nst Ypos] Yeq by simp
  have heq: "?h = take (Lng ?h) ((M::pairseq)[Suc q])"
  proof -
    have tk: "take (Suc m) B = take m B @ [B ! m]" by (rule take_Suc_conv_app_nth[OF m])
    have "take (Lng ?h) ((M::pairseq)[Suc q]) = take (Lng ?h) (?Y @ B)" using app by simp
    also have "\<dots> = take (Lng ?Y + Suc m) (?Y @ B)" using hlen by simp
    also have "\<dots> = ?Y @ take (Suc m) B" by (subst take_append) simp
    also have "\<dots> = ?Y @ (take m B @ [B ! m])" using tk by simp
    also have "\<dots> = ?h" by simp
    finally show ?thesis by (rule sym)
  qed
  have hostT: "?h \<in> T_PS" using T_PS_take[OF Nst hpos] heq by simp
  have th: "TrMax ?h = TrMax ?Y" by (rule m_8_5_TrMax_host[OF YT hostT BrY])
  have gc: "TrMax ((M::pairseq)[q])
              < parent ((M::pairseq)[Suc q]) 0 (Lng ((M::pairseq)[q]) + m)"
    by (rule m_8_5_gpar_col[OF L notzero hp i1 j0lt q1 mw' basegpar cinv MSq_pt e00])
  have key: "parent ?h 0 (Lng ?h - 1)
               = parent ((M::pairseq)[Suc q]) 0 (Lng ((M::pairseq)[q]) + m)"
  proof -
    have "parent ?h 0 (Lng ?h - 1) = parent (?Y @ B) 0 (Lng ?h - 1)"
      by (rule m_8_5_parent_host[OF m])
    also have "\<dots> = parent (?Y @ B) 0 (Lng ?Y + m)" using lh by simp
    also have "\<dots> = parent ((M::pairseq)[Suc q]) 0 (Lng ((M::pairseq)[q]) + m)"
      using app by simp
    finally show ?thesis .
  qed
  have "TrMax ?h = TrMax ((M::pairseq)[q])" by (rule th)
  also have "\<dots> < parent ((M::pairseq)[Suc q]) 0 (Lng ((M::pairseq)[q]) + m)" by (rule gc)
  also have "\<dots> = parent ?h 0 (Lng ?h - 1)" by (rule key[symmetric])
  finally show "TrMax ?h < parent ?h 0 (Lng ?h - 1)" .
qed

text \<open>§8.5 surgery CHECKPOINT — (A) deepen-classification geom is GREEN
  (@{thm [source] m_8_5_gpar_fullprefix} discharges the strict parent>TrMax
  deepen-trigger; @{thm [source] m_8_5_gBrne_from_gpar} discharges gBrne).
  The \<open>cinv\<close> (TrMax iterate-invariance) is now also GREEN
  (lemma \<open>m_8_5_cinv\<close>, below), so \<open>basegpar\<close> (the regime's un-iterated deepen)
  is the only gpar input the outer-q caller must supply as a hypothesis.
  ALL step2-route NON-surgery residuals are now GREEN: \<open>inj\<close>
  (@{thm [source] m_8_5_OW_inj_of_scb}), BASEPOINT (\<open>m_8_5_basepoint\<close>),
  brick B (\<open>m_8_5_brickB\<close>), ITERSCB (\<open>m_8_5_iterscb\<close>) — feeding \<open>wrap\<close> via
  @{thm [source] m_8_5_wrap_of_iterscb}.  The remaining piece of §8.5 surgery is the
  slice-Y surgery \<open>Trans (Y \<frown> B) = D\<^bsub>u\<^esub>(F (bpHeadT (Trans Y)))\<close>, Y the marked-basepoint
  slice.  This looked like an unbounded depth-recurrence at the FULL iterate (gpar
  \<Longleftrightarrow> full-iterate endpoint FALSE), but Red COLLAPSES the q-tower: \<open>Red (Y \<frown> B) = Red Y \<frown> B''\<close>
  (lemmas \<open>red_slice_extend\<close> + \<open>seg_append_prefix\<close>, below) with \<open>Red Y\<close>, \<open>B''\<close>
  q-invariant + standard, so the surgery reduces (\<open>m_8_5_slice_surgery_skeleton\<close>, below)
  to a BOUNDED surgery on the small reduced slice \<open>Red Y \<frown> B''\<close> — a FINITE well-founded
  walk (spineLeaf (Trans (Red Y)) = 0, so the value-step bottoms out: ONE condI sibling-append
  + (w-1) deepens, w-general).  The LONE remaining brick is the condI-append spine-step
  (keystone cases 1/2, the append-analog of @{thm [source] m_8_5_appended_col_deepen}),
  composed via @{thm [source] m_8_5_surgery_spine_compose} with the green deepen-step.\<close>


text \<open>§8.5 SURGERY cinv — TRUNK INVARIANCE of the oper-iterate (obstacle #1).  For the
  deepen-condV regime (last column row-1 positive with a row-1 parent strictly inside,
  and the row-0 deepen-trigger \<open>TrMax M < parent M 0 (Lng M-1)\<close>), every oper-iterate
  preserves the trunk length: \<open>TrMax (M[q]) = TrMax M\<close> (q \<ge> 1).  Proof = induction on
  the iterate index: the base \<open>M[1] = Pred M\<close> (@{thm [source] m_8_4_oper1_eq_Pred}) drops
  only the last column, leaving the trunk (@{thm [source] TrMax_Pred}, using \<open>TrMax M \<noteq>
  Lng M-1\<close> from the deepen-trigger); the step \<open>M[Suc(Suc k)] = M[Suc k] @ B\<close>
  (@{thm [source] m_8_4_oper_Suc_append}) appends ONE more period block past the trunk,
  which by @{thm [source] m_8_5_TrMax_append_Br} leaves \<open>TrMax\<close> fixed — the deepen branch
  \<open>Br (M[Suc k]) \<noteq> []\<close> holding because the IH pins \<open>TrMax (M[Suc k]) = TrMax M\<close> and the
  trigger gives \<open>TrMax M + 2 \<le> Lng M-1 \<le> Lng (M[Suc k]) - 1\<close>.  Discharges the \<open>cinv\<close>
  hypothesis of the gpar tower (@{thm [source] m_8_5_gpar_col} / @{thm [source]
  m_8_5_gpar_fullprefix}); the iterate memberships go in as the named assumption \<open>iterT\<close>.\<close>

lemma m_8_5_cinv:
  fixes M :: pairseq and q :: nat
  assumes MT: "M \<in> T_PS"
    and L: "1 < Lng M"
    and i1: "idx1 M (Lng M - 1) = 1"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
    and basegpar: "TrMax M < parent M 0 (Lng M - 1)"
    and iterT: "\<And>k. 1 \<le> k \<Longrightarrow> (M::pairseq)[k] \<in> T_PS"
    and q1: "1 \<le> q"
  shows "TrMax ((M::pairseq)[q]) = TrMax M"
proof -
  have e1pos: "entry M 1 (Lng M - 1) > 0"
  proof (rule ccontr)
    assume "\<not> entry M 1 (Lng M - 1) > 0"
    hence "idx1 M (Lng M - 1) = 0" by (simp add: idx1_def)
    thus False using i1 by simp
  qed
  have notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    using e1pos by simp
  have hp1: "hasParent M 1 (Lng M - 1)" using hp i1 by simp
  have j1pos: "Lng M - 1 > 0" using L by simp
  define j0 where "j0 = parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  define w where "w = Lng M - 1 - j0"
  have j0ltw: "j0 < Lng M - 1" using j0lt by (simp add: j0_def)
  have w0: "0 < w" using j0ltw unfolding w_def by simp
  have j0w: "j0 + w = Lng M - 1" using j0ltw unfolding w_def by simp
  have j0lt1: "parent M 1 (Lng M - 1) < Lng M - 1" by (rule j0lt[unfolded i1])
  have hp0: "hasParent M 0 (Lng M - 1)"
    by (rule oper_last_row0_haspar[OF hp i1 j0lt1])
  have par0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
  proof -
    have "nextR M 0 (parent M 0 (Lng M - 1)) (Lng M - 1)"
      using hp0 unfolding hasParent_def parent_def by (rule theI')
    hence "nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1)" by (simp add: nextR_def)
    thus ?thesis by (simp add: nextrel0_def)
  qed
  have tbound: "TrMax M + 2 \<le> Lng M - 1" using basegpar par0lt by linarith
  have br: "TrMax M \<noteq> Lng M - 1" using tbound by linarith
  have LngI: "\<And>n. Lng ((M::pairseq)[n]) = j0 + n * w"
    unfolding j0_def w_def using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have aux: "\<And>k. TrMax ((M::pairseq)[Suc k]) = TrMax M"
  proof -
    fix k
    show "TrMax ((M::pairseq)[Suc k]) = TrMax M"
    proof (induct k)
      case 0
      have "(M::pairseq)[Suc 0] = Pred M" using m_8_4_oper1_eq_Pred[OF MT] by simp
      thus ?case using TrMax_Pred[OF MT L br] by simp
    next
      case (Suc k)
      obtain B' where appB: "(M::pairseq)[Suc k + 1] = (M::pairseq)[Suc k] @ B'"
        using m_8_4_oper_Suc_append[OF j1pos e1pos hp1] by blast
      have eqSS: "(M::pairseq)[Suc (Suc k)] = (M::pairseq)[Suc k] @ B'" using appB by simp
      have LSk: "Lng ((M::pairseq)[Suc k]) = j0 + Suc k * w" by (rule LngI)
      have LSkge: "Lng M - 1 \<le> Lng ((M::pairseq)[Suc k])"
      proof -
        have "j0 + w \<le> j0 + Suc k * w" using w0 by simp
        thus ?thesis using LSk j0w by simp
      qed
      have IH: "TrMax ((M::pairseq)[Suc k]) = TrMax M" by (rule Suc.hyps)
      have brSk: "TrMax ((M::pairseq)[Suc k]) \<noteq> Lng ((M::pairseq)[Suc k]) - 1"
        using IH tbound LSkge by linarith
      have BrSk: "Br ((M::pairseq)[Suc k]) \<noteq> []"
        using brSk by (simp add: Br_def P_nonempty)
      have sk1: "1 \<le> Suc k" by simp
      have ssk1: "1 \<le> Suc (Suc k)" by simp
      have T1: "(M::pairseq)[Suc k] \<in> T_PS" by (rule iterT[OF sk1])
      have T2: "(M::pairseq)[Suc (Suc k)] \<in> T_PS" by (rule iterT[OF ssk1])
      have T2': "(M::pairseq)[Suc k] @ B' \<in> T_PS" using T2 eqSS by simp
      have "TrMax ((M::pairseq)[Suc k] @ B') = TrMax ((M::pairseq)[Suc k])"
        by (rule m_8_5_TrMax_append_Br[OF T1 T2' BrSk])
      hence "TrMax ((M::pairseq)[Suc (Suc k)]) = TrMax ((M::pairseq)[Suc k])"
        using eqSS by simp
      thus ?case using IH by simp
    qed
  qed
  obtain k where qk: "q = Suc k" using q1 by (cases q) auto
  show ?thesis using aux[of k] qk by simp
qed


text \<open>§8.5 SURGERY residual (3) BASEPOINT — the iterate basepoint membership
  \<open>(M[n], jm1) \<in> Marked\<close>, discharged from the condition-(V) regime via the GREEN
  engine @{thm [source] m_8_3_kind1_base_basepoint}.  \<open>e1pos\<close> and \<open>j0lt2\<close> come from
  @{const transCondV} (with \<open>coin\<close>: the row-1 and row-0 parents of the last column
  coincide); \<open>hp1\<close>/\<open>parR\<close>/\<open>coin\<close>/\<open>jm1pos\<close> are the named regime inputs.  One of the
  three step2 residuals of the §8.5 surgery ladder.\<close>

lemma m_8_5_basepoint:
  fixes M :: pairseq and n jm1 :: nat
  assumes M: "M \<in> RT_PS" and n1: "0 < n"
    and cv: "transCondV M"
    and hp1: "hasParent M 1 (Lng M - 1)"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and coin: "parent M 1 (Lng M - 1) = parent M 0 (Lng M - 1)"
    and jm1def: "jm1 = Adm M (parent M 0 (Lng M - 1))"
    and jm1pos: "0 < jm1"
  shows "((M::pairseq)[n], jm1) \<in> Marked"
proof -
  have e1pos: "entry M 1 (Lng M - 1) > 0" using cv by (simp add: transCondV_def)
  have j0lt2: "parent M 1 (Lng M - 1) + 1 < Lng M - 1"
  proof -
    have "parent M 0 (Lng M - 1) + 1 < Lng M - 1" using cv by (simp add: transCondV_def)
    thus ?thesis using coin by simp
  qed
  show ?thesis
    by (rule conjunct1[OF m_8_3_kind1_base_basepoint
          [OF M n1 e1pos hp1 j0lt2 parR coin jm1def jm1pos]])
qed


text \<open>§8.5 ITERSCB brick B — the iterate's marked subterm is SINGLE-PRINCIPAL (kind-1).
  Restates @{thm [source] transC1_single_principal} through @{thm [source] transC1_def}
  (\<open>transC1 N = Mark (Pred N) (transJm1 N)\<close>): for a condV-regime host \<open>N\<close> (the per-column
  surgery host \<open>= M[q] \<frown> [col]\<close>, so \<open>Pred N = M[q]\<close> and \<open>transJm1 N = jm1\<close>), the marked
  subterm \<open>Mark (M[q]) jm1\<close> is a single principal.  This is the centre-bridge for
  ITERSCB: it lets the scb centre of @{thm [source] m_8_5_wrap_of_iterscb} be written
  \<open>Dpt u (bpHeadT (Mark (M[q]) jm1))\<close> with the marked subterm reconstructed from its
  head \<open>u = bpHeadV\<close> and body.\<close>

lemma m_8_5_brickB:
  fixes N :: pairseq
  assumes MR: "N \<in> RT_PS" and MP: "N \<in> PT_PS"
    and J1: "transJ1 N > 0" and T1: "transT1 N \<noteq> 0\<^sub>B"
  shows "Lng (PB (Mark (Pred N) (transJm1 N))) = 1"
proof -
  have "Mark (Pred N) (transJm1 N) = transC1 N" by (simp add: transC1_def)
  thus ?thesis using transC1_single_principal[OF MR MP J1 T1] by simp
qed


text \<open>§8.5 ITERSCB — the iterate kind-1 scb-context, assembled.  Upgrades the
  scb-DECOMPOSITION of \<open>Trans (M[q])\<close> at the marked subterm (supplied by
  @{thm [source] scb_context_eq_of_prefix} — the verbatim trunk-prefix context match,
  hyp \<open>scb\<close>) to the full \<open>scb_kind1\<close> required by @{thm [source] m_8_5_wrap_of_iterscb},
  via @{thm [source] scb_kind1_of_suffix}.  The CENTRE bridge uses brick B
  (@{thm [source] m_8_5_brickB}): the marked subterm is a single principal
  \<open>Mark (M[q]) jm1 = D\<^bsub>u\<^esub> bdy\<close> (hyp \<open>c1form\<close>), so the wrap-centre
  \<open>D\<^bsub>u\<^esub> (bpHeadT (Mark (M[q]) jm1))\<close> equals the marked subterm and its flat is
  \<open>flatBP (D\<^bsub>u\<^esub> bdy)\<close>.  The \<open>dfree\<close> (Trans/Mark values are d-free, §7.3 invariant) and
  the \<open>rn\<close>-valley (the right-spine strict-increase/valley of the marked principal, the
  §7.3 \<open>T\<^sub>B\<^sup>Marked\<close> shape) are the named base inputs.  Completes the last step2-route
  non-surgery residual (with inj / BASEPOINT / brick B), isolating the surgery kernel.\<close>

lemma m_8_5_iterscb:
  fixes Mq :: pairseq and jm1 u :: nat and bdy :: BT and s1 b1 :: "Sym list"
  assumes c1form: "Mark Mq jm1 = Dpt (enat u) bdy"
    and scb: "scb_decomp (Trans Mq) s1 (flatBT (Mark Mq jm1)) b1"
    and dfree: "dfree_BT (Mark Mq jm1)"
    and rn: "let r = RightNodes (Mark Mq jm1); j1 = Lng r - 1 in
               j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1)"
  shows "scb_kind1 (Trans Mq) s1 (flatBT (Dpt (enat u) (bpHeadT (Mark Mq jm1)))) b1"
proof -
  have bh: "bpHeadT (Mark Mq jm1) = bdy" using c1form by simp
  have ceq: "Dpt (enat u) (bpHeadT (Mark Mq jm1)) = Mark Mq jm1" using c1form bh by simp
  have dfreep: "dfree_BP (DB (enat u) bdy)" using dfree c1form by simp
  have scbp: "scb_decomp (Trans Mq) s1 (flatBP (DB (enat u) bdy)) b1"
    using scb c1form by simp
  have rnp: "let r = RightNodes (Trm [DB (enat u) bdy]); j1 = Lng r - 1 in
               j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1)"
    using rn c1form by simp
  have "scb_kind1 (Trans Mq) s1 (flatBP (DB (enat u) bdy)) b1"
    by (rule scb_kind1_of_suffix[OF dfreep scbp rnp])
  thus ?thesis using ceq c1form by simp
qed


text \<open>§8.5 KERNEL enabler (1) — RED-APPEND COMPAT, general form.  Extending a slice's
  RIGHT endpoint only APPENDS to its \<open>Red\<close>: the front \<open>Red (seg N a c)\<close> is preserved
  as a PREFIX of \<open>Red (seg N a b)\<close> (\<open>c \<le> b\<close>).  Iterates the GREEN per-column peeling
  @{thm [source] m_7_4_Pred_Red_slice} (\<open>Pred (Red (seg N a j)) = Red (seg N a (j-1))\<close>)
  up the appended columns.  Instantiated at \<open>N = M[Suc q]\<close>, \<open>a = jm1\<close>,
  \<open>c = Lng (M[q]) - 1\<close>, \<open>b = Lng (M[Suc q]) - 1\<close> (with the prefix-slice identity
  \<open>seg (M[Suc q]) jm1 c = seg (M[q]) jm1 c = Y\<close>) this is the Red-collapse
  \<open>Red (Y \<frown> B) = Red Y \<frown> B''\<close> that turns the §8.5 surgery's unbounded q-tower into a
  bounded recursion on the standard reduced slice — the kernel's key enabler.\<close>

lemma red_slice_extend:
  fixes N :: pairseq and a c :: nat
  shows "a \<le> c \<Longrightarrow> c \<le> b \<Longrightarrow> b < Lng N \<Longrightarrow>
         \<exists>tail. Red (seg N a b) = Red (seg N a c) @ tail"
proof (induct b)
  case 0
  have "c = 0" using "0.prems"(2) by simp
  thus ?case by (intro exI[where x="[]"]) simp
next
  case (Suc b)
  show ?case
  proof (cases "c = Suc b")
    case True
    thus ?thesis by (intro exI[where x="[]"]) simp
  next
    case False
    have ac: "a \<le> c" by (rule Suc.prems(1))
    have cb: "c \<le> b" using Suc.prems(2) False by simp
    have bN: "b < Lng N" using Suc.prems(3) by simp
    obtain tail where IH: "Red (seg N a b) = Red (seg N a c) @ tail"
      using Suc.hyps[OF ac cb bN] by blast
    have aSb: "a < Suc b" using ac cb by simp
    have step: "Pred (Red (seg N a (Suc b))) = Red (seg N a b)"
      using m_7_4_Pred_Red_slice[OF aSb] by simp
    have pref: "\<exists>e. Red (seg N a (Suc b)) = Red (seg N a b) @ e"
    proof (cases "Lng (Red (seg N a (Suc b))) \<le> 1")
      case True
      hence "Pred (Red (seg N a (Suc b))) = Red (seg N a (Suc b))" by (simp add: Pred_def)
      hence "Red (seg N a (Suc b)) = Red (seg N a b)" using step by simp
      thus ?thesis by (intro exI[where x="[]"]) simp
    next
      case False
      hence pbl: "Pred (Red (seg N a (Suc b))) = butlast (Red (seg N a (Suc b)))"
        by (simp add: Pred_def)
      have ne: "Red (seg N a (Suc b)) \<noteq> []" using False by auto
      have "Red (seg N a (Suc b))
              = butlast (Red (seg N a (Suc b))) @ [last (Red (seg N a (Suc b)))]"
        by (rule append_butlast_last_id[symmetric, OF ne])
      also have "\<dots> = Red (seg N a b) @ [last (Red (seg N a (Suc b)))]"
        using pbl step by simp
      finally show ?thesis by blast
    qed
    obtain e where e: "Red (seg N a (Suc b)) = Red (seg N a b) @ e" using pref by blast
    have "Red (seg N a (Suc b)) = Red (seg N a c) @ (tail @ e)" using e IH by simp
    thus ?thesis by blast
  qed
qed


text \<open>§8.5 KERNEL — ASSEMBLY SKELETON (STEP A).  Derives the slice-Y surgery
  \<open>Trans (Y \<frown> B) = D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> (bpHeadT (Trans Y)))\<close> from the two crisp
  residuals as NAMED hyps — (1) the Red-append compat \<open>rcompat\<close> (= @{thm [source]
  red_slice_extend} instantiated: \<open>Red (Y\<frown>B) = Red Y \<frown> B''\<close>) and (2) the reduced-slice
  surgery \<open>rsurg\<close> on the bounded standard \<open>Red Y \<frown> B''\<close> — via Trans Red-invariance
  @{thm [source] m_7_3_Trans_Red} (\<open>Trans X = Trans (Red X)\<close>, green).  Red collapses the
  q-tower (rcompat), so the surgery on the raw slice = the surgery on the bounded
  standard reduced slice, lifted back by Trans-Red-invariance.  This packages the
  FINITE kernel structure as green, leaving exactly (2) (and the markstep + outer-q
  lift) as the residual.\<close>

lemma m_8_5_slice_surgery_skeleton:
  fixes Y B B'' :: pairseq and t2 :: BT and e10 vm1 :: nat
  assumes rcompat: "Red (Y @ B) = Red Y @ B''"
    and rsurg: "Trans (Red Y @ B'')
                  = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans (Red Y))))"
    and RRYB: "Red (Y @ B) \<in> RT_PS"
    and RRY: "Red Y \<in> RT_PS"
  shows "Trans (Y @ B) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Y)))"
proof -
  have ti: "Trans (Y @ B) = Trans (Red (Y @ B))" by (rule m_7_3_Trans_Red[OF RRYB])
  have tY: "Trans Y = Trans (Red Y)" by (rule m_7_3_Trans_Red[OF RRY])
  have "Trans (Y @ B) = Trans (Red Y @ B'')" using ti rcompat by simp
  also have "\<dots> = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans (Red Y))))"
    by (rule rsurg)
  also have "\<dots> = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Y)))"
    using tY by simp
  finally show ?thesis .
qed


text \<open>§8.5 KERNEL wiring (1') — PREFIX-SLICE identity (general).  A slice whose right
  endpoint lies inside the shared prefix ignores the append: \<open>seg (X \<frown> Z) a b = seg X a b\<close>
  when \<open>b < Lng X\<close>.  Instantiated at \<open>X = M[q]\<close>, \<open>Z = B'\<close> (\<open>M[Suc q] = M[q] \<frown> B'\<close> by
  @{thm [source] m_8_4_oper_Suc_append}), \<open>a = jm1\<close>, \<open>b = Lng (M[q]) - 1\<close>, this gives
  \<open>seg (M[Suc q]) jm1 (Lng (M[q]) - 1) = seg (M[q]) jm1 (Lng (M[q]) - 1) = Y\<close> — the
  identity that turns @{thm [source] red_slice_extend} on \<open>M[Suc q]\<close> into the
  \<open>rcompat\<close> hyp \<open>Red (Y \<frown> B) = Red Y \<frown> B''\<close> of @{thm [source] m_8_5_slice_surgery_skeleton}.\<close>

lemma seg_append_prefix:
  assumes bX: "b < Lng X"
  shows "seg (X @ Z) a b = seg X a b"
  unfolding seg_def
proof (rule map_cong[OF refl])
  fix j assume "j \<in> set [a..<Suc b]"
  hence "j < Lng X" using bX by auto
  thus "(X @ Z) ! j = X ! j" by (simp add: nth_append)
qed


text \<open>§8.5 KERNEL (2) helper — transC2 CLOSED FORM for the condition-(I) column.  The
  condI/III/V branch of @{const transC2} is SHARED, so the same closed form as
  @{thm [source] m_8_5_transC2_condV} holds under \<open>transCondI\<close>:
  \<open>transC2 M = D\<^bsub>v\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<^sub>B)\<close>.  For a condI column \<open>entry M 1 (Lng M-1) = 0\<close>,
  so this is the SIBLING-APPEND block \<open>D\<^bsub>v\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>0\<^esub> 0\<^sub>B)\<close> — the value grafted by the
  condI-append spine-step of the reduced-slice walk (the per-column step that grows the
  leaf-0 spine by one sibling).\<close>

lemma m_8_5_transC2_condI:
  fixes M :: pairseq
  assumes "transCondI M"
  shows "transC2 M
       = Dpt (transV M) (transT2 M +\<^sub>B Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
  using assms by (simp add: transC2_def Let_def transJ1_def)

text \<open>§8.5 kernel batch checkpoint — Red-collapse lemmas green: \<open>red_slice_extend\<close>,
  \<open>seg_append_prefix\<close>, \<open>m_8_5_slice_surgery_skeleton\<close>, \<open>m_8_5_transC2_condI\<close>.  The §8.5
  surgery kernel is reduced to ONE bounded brick: the condI-append spine-step (keystone
  cases 1/2 append-analog of the deepen-step), composed via \<open>m_8_5_surgery_spine_compose\<close>
  with the green deepen-step.\<close>

text \<open>SS 8.5 KERNEL brick -- the condI-append BASE (Adm0 route, NOT the keystone).
  The reduced-slice col0 (the FIRST column of B'') is an Adm0 column (transJm1 M = 0)
  of transCondI kind (python/_condI_adm0_check: 51/51 genuine kernel openings under
  REAL condI AND Adm0, incl. 16 DEEP slices, 0 failures).  Hence the whole Trans
  COLLAPSES to the single column's transC2 via Trans_eq_transC2_Adm0, sidestepping the
  4-way keystone disjunction (whose case-1 selection has NO clean dual to the
  deepen-step's j1' ~= j1).  With m_8_5_transC2_condI (condI closed form) and
  m_8_5_transT2_readback (transT2 = bpHeadT (Trans (slice)); the slice = whole Pred M
  under Adm0, by seg_0_eq_take), the appended column grows the leaf-0 spine by one
  sibling D[e1j1] 0:  Trans M = D[v](bpHeadT (Trans (Pred M)) +B D[e1j1] 0).  This is
  the base (m = 0 -> 1) of the reduced-slice surgery; the deepen suffix composes on top
  via m_8_5_surgery_spine_compose + the green deepen-step.\<close>

lemma m_8_5_condI_append_base:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and Adm0: "transJm1 M = 0"
    and cI: "transCondI M"
    and mk0: "(Pred M, 0) \<in> Marked"
    and rng: "0 < Lng (Pred M) - 1"
  shows "Trans M
       = Dpt (transV M)
           (bpHeadT (Trans (Pred M)) +\<^sub>B Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
proof -
  have e1: "Trans M = transC2 M"
    by (rule Trans_eq_transC2_Adm0[OF MR MP J1pos T1 Adm0])
  have e2: "transC2 M
            = Dpt (transV M) (transT2 M +\<^sub>B Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
    by (rule m_8_5_transC2_condI[OF cI])
  have pr: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have mk': "(Pred M, transJm1 M) \<in> Marked" using mk0 Adm0 by simp
  have rng': "transJm1 M < Lng (Pred M) - 1" using rng Adm0 by simp
  have rb: "transT2 M
            = bpHeadT (Trans (seg (Pred M) (transJm1 M) (Lng (Pred M) - 1)))"
    by (rule m_8_5_transT2_readback[OF mk' pr rng'])
  have LP: "1 < Lng (Pred M)" using rng by linarith
  have segfull: "seg (Pred M) (transJm1 M) (Lng (Pred M) - 1) = Pred M"
  proof -
    have "seg (Pred M) 0 (Lng (Pred M) - 1) = take (Suc (Lng (Pred M) - 1)) (Pred M)"
      by (rule seg_0_eq_take) (use LP in linarith)
    also have "Suc (Lng (Pred M) - 1) = Lng (Pred M)" using LP by simp
    finally have "seg (Pred M) 0 (Lng (Pred M) - 1) = Pred M" by simp
    thus ?thesis using Adm0 by simp
  qed
  have t2: "transT2 M = bpHeadT (Trans (Pred M))" using rb segfull by simp
  show ?thesis using e1 e2 t2 by simp
qed

text \<open>SS 8.5 KERNEL (iii) — generalised surgery compose-to-endpoint.  Identical to
  m_8_5_surgery_of_geom_endpoint except the final spine slot is a FREE BT (fin) read
  off the endpoint, instead of being forced to bpHeadT (Trans Y).  This is needed for
  the condI-append regime: there Y = Z @ [col0] but the target slot is bpHeadT (Trans Z)
  (= the slice head BEFORE the appended sibling), which differs from bpHeadT (Trans Y)
  by the appended D00.  Proof = the geom_endpoint spine walk verbatim (deepen step
  m_8_5_surgery_spine_step over all columns, spineLeaf-tracking compose
  m_8_5_surgery_spine_compose), closing with the supplied endpoint.\<close>

lemma m_8_5_surgery_compose_to_endpoint:
  fixes Y B :: pairseq and t2 fin :: BT and e10 vm1 :: nat
  assumes base: "Trans Y
        = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans Y)))"
    and gYne: "\<And>m. m < Lng B \<Longrightarrow> 0 < Lng (Y @ take m B)"
    and gMR: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> RT_PS"
    and gMP: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> PT_PS"
    and gBrne: "\<And>m. m < Lng B \<Longrightarrow> Br ((Y @ take m B) @ [B ! m]) \<noteq> []"
    and gj1gt: "\<And>m. m < Lng B \<Longrightarrow> Lng ((Y @ take m B) @ [B ! m]) - 1 > 1"
    and gpar: "\<And>m. m < Lng B \<Longrightarrow> parent ((Y @ take m B) @ [B ! m]) 0
                 (Lng ((Y @ take m B) @ [B ! m]) - 1) > TrMax ((Y @ take m B) @ [B ! m])"
    and ge10: "\<And>m. m < Lng B \<Longrightarrow> entry ((Y @ take m B) @ [B ! m]) 1 0 = e10"
    and endpoint: "spineLeaf (Trans (Y @ B)) = fin"
  shows "Trans (Y @ B) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) fin)"
proof -
  have step: "\<And>m. m < Lng B \<Longrightarrow>
        Trans (Y @ take m B)
          = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take m B)))) \<Longrightarrow>
        Trans (Y @ take (Suc m) B)
          = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take (Suc m) B))))"
  proof -
    fix m
    assume m: "m < Lng B"
      and ih: "Trans (Y @ take m B)
                 = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take m B))))"
    show "Trans (Y @ take (Suc m) B)
            = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take (Suc m) B))))"
      by (rule m_8_5_surgery_spine_step
            [OF m gYne[OF m] gMR[OF m] gMP[OF m] gBrne[OF m] gj1gt[OF m]
                gpar[OF m] ge10[OF m] ih])
  qed
  have base': "Trans Y
        = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take 0 B))))"
    using base by simp
  have comp: "Trans (Y @ B)
        = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ take (Lng B) B))))"
    by (rule m_8_5_surgery_spine_compose
          [where P = "\<lambda>m. spineLeaf (Trans (Y @ take m B))", OF base' step])
  have comp2: "Trans (Y @ B)
        = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Y @ B))))"
    using comp by simp
  show ?thesis by (subst comp2) (simp add: endpoint)
qed

text \<open>SS 8.5 KERNEL (iii) — the REGIME-B reduced-slice surgery (condI-append col0).
  Assembles the bounded reduced-slice surgery rsurg from: the condI-append BASE for the
  FIRST column (cIbase, from m_8_5_condI_append_base; base put in spineLeaf-self form by
  m_8_5_base_of_surgery_pred), the all-deepen GEOMETRIC inputs for the suffix tl B
  (gpar 171/171 empirically), and the ENDPOINT spineLeaf (Trans (Z @ B)) = bpHeadT
  (Trans Z) (the finite-walk readback).  Index algebra: (Z @ [B!0]) @ tl B = Z @ B
  (B nonempty).  Conclusion = the rsurg hypothesis of m_8_5_slice_surgery_skeleton with
  t2 = bpHeadT (Trans Z).  (The all-deepen col0 regime is the existing green
  m_8_5_surgery_of_geom_endpoint; the kernel discriminates on col0's gpar.)\<close>

lemma m_8_5_reduced_slice_surgery_condI:
  fixes Z B :: pairseq and e10 vm1 :: nat
  assumes Bne: "0 < Lng B"
    and cIbase: "Trans (Z @ [B ! 0])
                   = Dpt (enat e10) (bpHeadT (Trans Z) +\<^sub>B Dpt (enat vm1) 0\<^sub>B)"
    and gYne: "\<And>m. m < Lng (tl B) \<Longrightarrow> 0 < Lng ((Z @ [B ! 0]) @ take m (tl B))"
    and gMR: "\<And>m. m < Lng (tl B)
                 \<Longrightarrow> ((Z @ [B ! 0]) @ take m (tl B)) @ [tl B ! m] \<in> RT_PS"
    and gMP: "\<And>m. m < Lng (tl B)
                 \<Longrightarrow> ((Z @ [B ! 0]) @ take m (tl B)) @ [tl B ! m] \<in> PT_PS"
    and gBrne: "\<And>m. m < Lng (tl B)
                 \<Longrightarrow> Br (((Z @ [B ! 0]) @ take m (tl B)) @ [tl B ! m]) \<noteq> []"
    and gj1gt: "\<And>m. m < Lng (tl B)
                 \<Longrightarrow> Lng (((Z @ [B ! 0]) @ take m (tl B)) @ [tl B ! m]) - 1 > 1"
    and gpar: "\<And>m. m < Lng (tl B)
                 \<Longrightarrow> parent (((Z @ [B ! 0]) @ take m (tl B)) @ [tl B ! m]) 0
                       (Lng (((Z @ [B ! 0]) @ take m (tl B)) @ [tl B ! m]) - 1)
                     > TrMax (((Z @ [B ! 0]) @ take m (tl B)) @ [tl B ! m])"
    and ge10: "\<And>m. m < Lng (tl B)
                 \<Longrightarrow> entry (((Z @ [B ! 0]) @ take m (tl B)) @ [tl B ! m]) 1 0 = e10"
    and endpoint: "spineLeaf (Trans (Z @ B)) = bpHeadT (Trans Z)"
  shows "Trans (Z @ B)
       = Dpt (enat e10) (bpHeadT (Trans Z) +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Z)))"
proof -
  have YBeq: "(Z @ [B ! 0]) @ tl B = Z @ B"
    using Bne by (cases B) auto
  have base': "Trans (Z @ [B ! 0])
        = Dpt (enat e10) (bpHeadT (Trans Z)
              +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans (Z @ [B ! 0]))))"
    by (rule m_8_5_base_of_surgery_pred[OF cIbase])
  have ep': "spineLeaf (Trans ((Z @ [B ! 0]) @ tl B)) = bpHeadT (Trans Z)"
    using endpoint YBeq by simp
  have "Trans ((Z @ [B ! 0]) @ tl B)
        = Dpt (enat e10) (bpHeadT (Trans Z) +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Z)))"
    by (rule m_8_5_surgery_compose_to_endpoint
          [OF base' gYne gMR gMP gBrne gj1gt gpar ge10 ep'])
  thus ?thesis using YBeq by simp
qed

text \<open>SS 8.5 KERNEL (B) — the Adm0+condI DISCHARGE for the genuine col0, as a clean
  interface wrapper.  The genuine col0 host is M0 = (Red Y) @ [col0]; empirically
  (python/_condI_adm0_check: 353/353) M0 = Red (seg N jm1 (cY+1)) — the reduced slice
  extended by exactly ONE raw column.  Writing H = seg N 0 (cY+1) for the truncated
  host (Lng H - 1 = cY+1), seg H jm1 (Lng H - 1) = seg N jm1 (cY+1) = M0, so the
  FULL-slice repr lemmas apply to H: repr_transJm1_shift gives transJm1 M0 = transJm1 H
  - jm1 (= 0 when the basepoint of H is jm1, i.e. Adm0), and repr_transCondI_eq gives
  transCondI M0 = transCondI H.  This bundles both: under the repr geometric hyps at
  (H, m=jm1) with transJm1 H = jm1 and transCondI H, M0 = Red (seg H jm1 (Lng H-1)) is
  Adm0 and condI — exactly two of the m_8_5_condI_append_base hypotheses.  (The kernel
  supplies the truncated-host facts: H = M[q] @ [one column], all M[q]-structure.)\<close>

lemma m_8_5_redslice_Adm0_condI:
  fixes H :: pairseq and m :: nat
  assumes mM: "(H, m) \<in> Marked" and HR: "H \<in> RT_PS"
    and mint: "m < Lng H - 2"
    and leM: "leR H 0 m (Lng H - 1)"
    and hp: "hasParent H 0 (Lng H - 1)"
    and anc0: "m \<le> parent H 0 (Lng H - 1)"
    and j0lt: "parent H 0 (Lng H - 1) < Lng H - 1"
    and base0: "transJm1 H = m"
    and cIH: "transCondI H"
  shows "transJm1 (Red (seg H m (Lng H - 1))) = 0
       \<and> transCondI (Red (seg H m (Lng H - 1)))"
proof -
  have shift: "transJm1 (Red (seg H m (Lng H - 1))) = transJm1 H - m"
    by (rule repr_transJm1_shift[OF mM HR mint leM hp anc0 j0lt])
  have A: "transJm1 (Red (seg H m (Lng H - 1))) = 0" using shift base0 by simp
  have B: "transCondI (Red (seg H m (Lng H - 1))) = transCondI H"
    by (rule repr_transCondI_eq[OF mM HR mint leM hp anc0 j0lt])
  show ?thesis using A B cIH by simp
qed

text \<open>§8.5 surgery-chain checkpoint — the slice-Y surgery is GREEN end-to-end: the
  condI-append base, the free-final-slot compose, the regime-B reduced-slice surgery,
  and the Adm0/condI (B)-discharge wrapper.  The §8.5 master-key VALUE content (the
  slice-Y depth-recurrence that was the open wall) is closed; remaining = the top-level
  capstone wiring (the per-q kernel-instantiation + lift to the condV descent).\<close>

text \<open>SS 8.5 CAPSTONE piece — the step2 `body' discharge (q-general).  For each q>=2,
  the per-q slice-Y surgery (surg, supplied; assembled from rcompat + rsurg via
  m_8_5_slice_surgery_skeleton) yields the Mark-step bpHeadT (Mark (M[Suc q]) jm1) =
  F (bpHeadT (Mark (M[q]) jm1)) via m_8_5_markstep_of_surgery.  The markstep
  infrastructure (Marked basepoint + RT_PS membership for M[q] and M[Suc q],
  oper-append M[Suc q]=M[q]@B) is discharged from the condV-regime hyps via
  m_8_3_kind1_base_basepoint + m_8_4_oper_Suc_append; the range jm1<Lng(M[q])-1 is
  carried (rng).  This is exactly the `body' input of m_8_5_step2_of_wrap_body, so
  step2 follows from {wrap, inj, this}.\<close>

lemma m_8_5_body_of_sliceY:
  fixes M :: pairseq and F :: "BT \<Rightarrow> BT" and jm1 u q :: nat
  assumes M: "M \<in> RT_PS"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp1: "hasParent M 1 (Lng M - 1)"
    and j0lt2: "parent M 1 (Lng M - 1) + 1 < Lng M - 1"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and coin: "parent M 1 (Lng M - 1) = parent M 0 (Lng M - 1)"
    and jm1def: "jm1 = Adm M (parent M 0 (Lng M - 1))"
    and jm1pos: "0 < jm1"
    and rng: "\<And>qq. 2 \<le> qq \<Longrightarrow> jm1 < Lng ((M::pairseq)[qq]) - 1"
    and surg: "\<And>qq B. 2 \<le> qq \<Longrightarrow> (M::pairseq)[Suc qq] = (M::pairseq)[qq] @ B \<Longrightarrow>
         Trans (seg ((M::pairseq)[qq]) jm1 (Lng ((M::pairseq)[qq]) - 1) @ B)
           = Dpt (enat u)
               (F (bpHeadT (Trans (seg ((M::pairseq)[qq]) jm1 (Lng ((M::pairseq)[qq]) - 1)))))"
    and q2: "2 \<le> q"
  shows "bpHeadT (Mark ((M::pairseq)[Suc q]) jm1) = F (bpHeadT (Mark ((M::pairseq)[q]) jm1))"
proof -
  have LMpos: "0 < Lng M - 1" using j0lt2 by linarith
  have qp: "0 < q" using q2 by simp
  have Sqp: "0 < Suc q" by simp
  have "\<exists>B. (M::pairseq)[Suc q] = (M::pairseq)[q] @ B"
    using m_8_4_oper_Suc_append[OF LMpos e1pos hp1] by (metis Suc_eq_plus1)
  then obtain B where appB: "(M::pairseq)[Suc q] = (M::pairseq)[q] @ B" by blast
  have mkS: "((M::pairseq)[Suc q], jm1) \<in> Marked \<and> (M::pairseq)[Suc q] \<in> RT_PS"
    by (rule m_8_3_kind1_base_basepoint[OF M Sqp e1pos hp1 j0lt2 parR coin jm1def jm1pos])
  have mkqf: "((M::pairseq)[q], jm1) \<in> Marked \<and> (M::pairseq)[q] \<in> RT_PS"
    by (rule m_8_3_kind1_base_basepoint[OF M qp e1pos hp1 j0lt2 parR coin jm1def jm1pos])
  have rqS: "jm1 < Lng ((M::pairseq)[Suc q]) - 1" using rng[of "Suc q"] q2 by simp
  have rq: "jm1 < Lng ((M::pairseq)[q]) - 1" using rng[OF q2] .
  have mqne: "0 < Lng ((M::pairseq)[q])" using rq by linarith
  have jlef: "jm1 \<le> Lng ((M::pairseq)[q])" using rq by linarith
  have surgF: "Trans (seg ((M::pairseq)[q]) jm1 (Lng ((M::pairseq)[q]) - 1) @ B)
        = Dpt (enat u)
            (F (bpHeadT (Trans (seg ((M::pairseq)[q]) jm1 (Lng ((M::pairseq)[q]) - 1)))))"
    using surg[OF q2 appB] .
  show ?thesis
  proof (rule m_8_5_markstep_of_surgery)
    show "((M::pairseq)[Suc q], jm1) \<in> Marked" using mkS by simp
    show "(M::pairseq)[Suc q] \<in> RT_PS" using mkS by simp
    show "jm1 < Lng ((M::pairseq)[Suc q]) - 1" using rqS .
    show "(M::pairseq)[Suc q] = (M::pairseq)[q] @ B" using appB .
    show "0 < Lng ((M::pairseq)[q])" using mqne .
    show "jm1 \<le> Lng ((M::pairseq)[q])" using jlef .
    show "((M::pairseq)[q], jm1) \<in> Marked" using mkqf by simp
    show "(M::pairseq)[q] \<in> RT_PS" using mkqf by simp
    show "jm1 < Lng ((M::pairseq)[q]) - 1" using rq .
    show "Trans (seg ((M::pairseq)[q]) jm1 (Lng ((M::pairseq)[q]) - 1) @ B)
            = Dpt (enat u)
                (F (bpHeadT (Trans (seg ((M::pairseq)[q]) jm1 (Lng ((M::pairseq)[q]) - 1)))))"
      using surgF .
  qed
qed

text \<open>SS 8.5 CAPSTONE piece — step2 (the descent recurrence) for the genuine kernel.
  Combines the green body discharge (m_8_5_body_of_sliceY, instantiated F:=C) with
  m_8_5_step2_of_wrap_body{wrap, inj}.  Carries as NAMED HYPS the residuals: surgC =
  the per-q slice-Y surgery in C-form (bundles (E) col0-condI + rsurg + rcompat +
  skeleton + the F=C matching), wrap (Trans(M[q])=OW(bpHeadT(Mark(M[q]) jm1)), the
  iterscb-based n=1-base framing), inj (OW injective).  Yields exactly the step2 input
  of m_8_5_TransCondV_descend_of_step2_residuals.\<close>

lemma m_8_5_step2_kernel:
  fixes M :: pairseq and C OW :: "BT \<Rightarrow> BT" and jm1 u p :: nat and b :: BT
  assumes M: "M \<in> RT_PS"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp1: "hasParent M 1 (Lng M - 1)"
    and j0lt2: "parent M 1 (Lng M - 1) + 1 < Lng M - 1"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and coin: "parent M 1 (Lng M - 1) = parent M 0 (Lng M - 1)"
    and jm1def: "jm1 = Adm M (parent M 0 (Lng M - 1))"
    and jm1pos: "0 < jm1"
    and rng: "\<And>qq. 2 \<le> qq \<Longrightarrow> jm1 < Lng ((M::pairseq)[qq]) - 1"
    and surgC: "\<And>qq B. 2 \<le> qq \<Longrightarrow> (M::pairseq)[Suc qq] = (M::pairseq)[qq] @ B \<Longrightarrow>
         Trans (seg ((M::pairseq)[qq]) jm1 (Lng ((M::pairseq)[qq]) - 1) @ B)
           = Dpt (enat u)
               (C (bpHeadT (Trans (seg ((M::pairseq)[qq]) jm1 (Lng ((M::pairseq)[qq]) - 1)))))"
    and wrap: "\<And>q. 1 \<le> q \<Longrightarrow>
                 Trans ((M::pairseq)[q]) = OW (bpHeadT (Mark ((M::pairseq)[q]) jm1))"
    and inj: "\<And>x y. OW x = OW y \<Longrightarrow> x = y"
    and p2: "2 \<le> p"
    and hb: "Trans ((M::pairseq)[p]) = OW b"
  shows "Trans ((M::pairseq)[Suc p]) = OW (C b)"
proof -
  have body: "\<And>q. 2 \<le> q \<Longrightarrow>
      bpHeadT (Mark ((M::pairseq)[Suc q]) jm1) = C (bpHeadT (Mark ((M::pairseq)[q]) jm1))"
  proof -
    fix q :: nat assume q2: "2 \<le> q"
    show "bpHeadT (Mark ((M::pairseq)[Suc q]) jm1) = C (bpHeadT (Mark ((M::pairseq)[q]) jm1))"
      using M e1pos hp1 j0lt2 parR coin jm1def jm1pos rng surgC q2
      by (rule m_8_5_body_of_sliceY)
  qed
  show ?thesis
    by (rule m_8_5_step2_of_wrap_body[OF wrap inj body p2 hb])
qed

text \<open>SS 8.5 CAPSTONE — the condV descent for the genuine kernel, wired GREEN modulo
  exactly THREE documented named residuals:
    (E)  surgC  = the per-q slice-Y surgery in C-form (the descent-regime closure
                  condV(M[q])\<and>gpar(M[q]) => reduced-col0 condI/Adm0; empirically 48/48;
                  bundles condI_append_base[(E)] + reduced_slice_surgery_condI + skeleton
                  + rcompat + the F=C match);
    (OT) TOT    = Trans M \<in> OT_B  (the SS 8.7 ordinal-term membership);
    (B0) the n=1 base / OW-scb context: wrap, inj, C_def, OW_def, tT, uv, bodyT, dbbody,
                  bodyne, innerscb, k1, kpos, base2, botU.
  The condV-deepen regime hyps (Mrt/e1pos/hp1/j0lt2/parR/coin/jm1def/jm1pos/rng) are the
  standard SS 6.x setup (e1pos = cond conjunct-1; the rest from cond + gpar).  step2 is
  DISCHARGED via m_8_5_step2_kernel (= body_of_sliceY + step2_of_wrap_body); the whole
  then feeds m_8_5_TransCondV_descend_of_step2_residuals.  Conclusion: the SS 8.5 descent
  lessBT (Trans (M[n])) (Trans M) for every n>0 — the termination measure descent.\<close>

lemma m_8_5_TransCondV_descend_kernel:
  fixes M :: pairseq and u v k n :: nat and leafL\<^sub>0 body :: BT
    and s\<^sub>0 s\<^sub>1 b\<^sub>0 b\<^sub>1 :: "Sym list" and C OW :: "BT \<Rightarrow> BT" and jm1 :: nat
  assumes MST: "M \<in> ST_PS" and MP: "M \<in> PT_PS"
    and j1: "Lng M - 1 > 1" and cond: "transCondV M"
    and n0: "0 < n" and TOT: "Trans M \<in> OT_B"
    and C_def: "C = (\<lambda>x. unflatBT (s\<^sub>0 @ Dsym (enat (v - 1)) # flatBT x @ b\<^sub>0))"
    and OW_def: "OW = (\<lambda>x. unflatBT (s\<^sub>1 @ Dsym (enat u) # flatBT x @ b\<^sub>1))"
    and tT: "Trans M \<in> T_B" and uv: "u < v" and bodyT: "body \<in> T_B"
    and dbbody: "domB body = TBv (enat (v - 1))" and bodyne: "body \<noteq> Trm []"
    and innerscb: "scb_decomp body s\<^sub>0 (flatBT (Dpt (enat v) 0\<^sub>B)) b\<^sub>0"
    and k1: "scb_kind1 (Trans M) s\<^sub>1 (flatBT (Dpt (enat u) body)) b\<^sub>1"
    and kpos: "1 \<le> k"
    and base2: "Trans ((M::pairseq)[2]) = OW ((C ^^ k) leafL\<^sub>0)"
    and botU: "leBT leafL\<^sub>0 (C (Dpt (enat (v - 1)) 0\<^sub>B))"
    and Mrt: "M \<in> RT_PS"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp1: "hasParent M 1 (Lng M - 1)"
    and j0lt2: "parent M 1 (Lng M - 1) + 1 < Lng M - 1"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and coin: "parent M 1 (Lng M - 1) = parent M 0 (Lng M - 1)"
    and jm1def: "jm1 = Adm M (parent M 0 (Lng M - 1))"
    and jm1pos: "0 < jm1"
    and rng: "\<And>qq. 2 \<le> qq \<Longrightarrow> jm1 < Lng ((M::pairseq)[qq]) - 1"
    and surgC: "\<And>qq B. 2 \<le> qq \<Longrightarrow> (M::pairseq)[Suc qq] = (M::pairseq)[qq] @ B \<Longrightarrow>
         Trans (seg ((M::pairseq)[qq]) jm1 (Lng ((M::pairseq)[qq]) - 1) @ B)
           = Dpt (enat u)
               (C (bpHeadT (Trans (seg ((M::pairseq)[qq]) jm1 (Lng ((M::pairseq)[qq]) - 1)))))"
    and wrap: "\<And>q. 1 \<le> q \<Longrightarrow>
                 Trans ((M::pairseq)[q]) = OW (bpHeadT (Mark ((M::pairseq)[q]) jm1))"
    and inj: "\<And>x y. OW x = OW y \<Longrightarrow> x = y"
  shows "lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  have step2: "\<And>p b. 2 \<le> p \<Longrightarrow> Trans ((M::pairseq)[p]) = OW b
                  \<Longrightarrow> Trans ((M::pairseq)[Suc p]) = OW (C b)"
  proof -
    fix p :: nat and b :: BT
    assume p2: "2 \<le> p" and hb: "Trans ((M::pairseq)[p]) = OW b"
    show "Trans ((M::pairseq)[Suc p]) = OW (C b)"
      using Mrt e1pos hp1 j0lt2 parR coin jm1def jm1pos rng surgC wrap inj p2 hb
      by (rule m_8_5_step2_kernel)
  qed
  show ?thesis
    by (rule m_8_5_TransCondV_descend_of_step2_residuals[OF MST MP j1 cond n0 TOT
          C_def OW_def tT uv bodyT dbbody bodyne innerscb k1 kpos base2 step2 botU])
qed

text \<open>§8.5 CAPSTONE — the condV termination-measure descent \<open>lessBT (Trans (M[n])) (Trans M)\<close>
  is wired GREEN modulo exactly THREE documented named residuals: (E) the per-q slice-Y surgery
  (the descent-regime closure \<open>condV \<and> gpar \<Rightarrow> reduced-col0 condI/Adm0\<close>, empirical 48/48),
  (OT) \<open>Trans M \<in> OT_B\<close> (§8.7 ordinal-term membership), and the n=1-base/OW-scb context
  (\<open>wrap/inj/C_def/OW_def/.../base2/botU\<close>).  The slice-Y depth-recurrence master key — the
  long-open §8 wall — is closed: it reduces, through the green chain
  @{thm [source] m_8_5_TransCondV_descend_kernel}, to those three residuals (each owned elsewhere).\<close>

text \<open>§8.5 B0 CONTEXT — the CLEANLY-DERIVABLE n=1-base / OW-scb bundle hyps.  Of the
  fourteen B0 hyps the capstone @{thm [source] m_8_5_TransCondV_descend_kernel} carries
  free, FOUR follow with NO new deep input — they are NOT independent assumptions:
    \<^item> \<open>tT\<close>     (\<open>Trans M \<in> T_B\<close>)        from \<open>M \<in> RT_PS\<close> (@{thm [source] m_7_3_Trans_in_T_B});
    \<^item> \<open>inj\<close>    (\<open>OW\<close> injective)         from \<open>OW_def\<close> + \<open>k1\<close> (@{thm [source] m_8_5_OW_inj_of_scb}:
              \<open>k1\<close>'s scb makes the centre string in the flat image, so \<open>OW\<close> cancels);
    \<^item> \<open>bodyne\<close> (\<open>body \<noteq> 0\<close>)           from \<open>innerscb\<close> (the centre string
              \<open>flat (D\<^bsub>v\<^esub> 0) = [D\<^bsub>v\<^esub>, Z]\<close> has length 2, so \<open>flat body\<close> has length \<ge> 2 > 1 = \<open>|flat 0|\<close>).
  This lemma packages the three structural ones (the parent can also cite
  @{thm [source] m_7_3_Trans_in_T_B} directly for \<open>tT\<close>).  Empirically all 28/28 on the
  small condV hosts (python/_step2_decomp_check producer + augmented length/uv check); B0.\<close>

lemma m_8_5_B0_derivable:
  fixes M :: pairseq and OW :: "BT \<Rightarrow> BT" and s\<^sub>0 s\<^sub>1 b\<^sub>0 b\<^sub>1 :: "Sym list"
    and u v :: nat and body x y :: BT
  assumes Mrt: "M \<in> RT_PS"
    and OW_def: "OW = (\<lambda>x. unflatBT (s\<^sub>1 @ Dsym (enat u) # flatBT x @ b\<^sub>1))"
    and k1: "scb_kind1 (Trans M) s\<^sub>1 (flatBT (Dpt (enat u) body)) b\<^sub>1"
    and innerscb: "scb_decomp body s\<^sub>0 (flatBT (Dpt (enat v) 0\<^sub>B)) b\<^sub>0"
  shows "Trans M \<in> T_B"
    and "OW x = OW y \<Longrightarrow> x = y"
    and "body \<noteq> Trm []"
proof -
  show "Trans M \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF Mrt])
next
  have scb: "scb_decomp (Trans M) s\<^sub>1 (flatBT (Dpt (enat u) body)) b\<^sub>1"
    using k1 by (simp add: scb_kind1_def)
  show "OW x = OW y \<Longrightarrow> x = y"
    by (rule m_8_5_OW_inj_of_scb[OF OW_def scb])
next
  have flatb: "flatBT body = s\<^sub>0 @ flatBT (Dpt (enat v) 0\<^sub>B) @ b\<^sub>0"
    using innerscb by (simp add: scb_decomp_def)
  show "body \<noteq> Trm []"
  proof
    assume b: "body = Trm []"
    from flatb b have e: "[Zsym] = s\<^sub>0 @ flatBT (Dpt (enat v) 0\<^sub>B) @ b\<^sub>0" by simp
    have "length ([Zsym]::Sym list) = length (s\<^sub>0 @ flatBT (Dpt (enat v) 0\<^sub>B) @ b\<^sub>0)"
      by (simp only: e)
    thus False by simp
  qed
qed

text \<open>§8.5 B0 CONTEXT — the \<open>uv\<close> hyp (\<open>u < v\<close>), discharged for the GENUINE pinned values
  \<open>u = M\<^bsub>1,jm1\<^esub>\<close>, \<open>v = M\<^bsub>1,j\<^sub>1\<^esub>\<close>.  Under condV the row-0 parent boundary \<open>jp = parent M 0 j\<^sub>1\<close>
  satisfies \<open>M\<^bsub>1,jp\<^esub> + 1 = M\<^bsub>1,j\<^sub>1\<^esub>\<close>, and the admissibility basepoint \<open>jm1 = Adm M jp\<close> is a
  row-1 ancestor of \<open>jp\<close> (@{thm [source] adm_row1_ancestry}), so \<open>M\<^bsub>1,jm1\<^esub> \<le> M\<^bsub>1,jp\<^esub>\<close>
  (@{thm [source] le1_imp_entry1_le}) \<open>= v - 1 < v\<close>.  Empirically 28/28 (augmented check). B0.\<close>

lemma m_8_5_B0_uv:
  fixes M :: pairseq and jm1 :: nat
  assumes Mrt: "M \<in> RT_PS" and cond: "transCondV M"
    and jm1def: "jm1 = Adm M (parent M 0 (Lng M - 1))"
  shows "entry M 1 jm1 < entry M 1 (Lng M - 1)"
proof -
  let ?jp = "parent M 0 (Lng M - 1)"
  have MT: "M \<in> T_PS" using Mrt by (simp add: RT_PS_def)
  have condvp: "entry M 1 ?jp + 1 = entry M 1 (Lng M - 1)"
    and jp2: "?jp + 1 < Lng M - 1" using cond by (simp_all add: transCondV_def)
  have jple: "?jp \<le> Lng M - 1" using jp2 by linarith
  have leR1: "leR M 1 (Adm M ?jp) ?jp" by (rule adm_row1_ancestry[OF MT jple])
  have le1: "le1 M jm1 ?jp" using leR1 jm1def by (simp add: leR_def)
  have "entry M 1 jm1 \<le> entry M 1 ?jp" by (rule le1_imp_entry1_le[OF le1])
  thus ?thesis using condvp by linarith
qed

text \<open>§8.5 (E.2) RE-ARCHITECTURE — the descent-regime closure WITHOUT the false
  \<open>d\<^sub>M = 1\<close> shortcut.  Sub-agent (E.2) REFUTED the candidate
  \<open>transCondV M \<and> gpar M \<and> M \<in> ST\<^bsub>PS\<^esub> \<Longrightarrow> entry M 1 (parent M 0 (Lng M-1)) = 0\<close>
  (33/35; two yaBMS-verified standard counterexamples with adjacent duplicate columns
  from the \<open>i\<^sub>1=0\<close> copy-expand; the "parent is depth-1/top-level" reading is itself
  inconsistent with \<open>gpar \<equiv> parent > TrMax\<close>, 35/35 branch).  The genuine surgery col0
  residual is NOT \<open>entry(col0)=0\<close>; the reduced-slice col0 host \<open>M\<^sub>0 = (Red Y) \<frown> [col0]\<close>
  lands UNIFORMLY in \<open>{condI, condIII, condV}\<close> (empirical GATE: Adm0 60/60; cond
  \<in> {I:54, III:6}, never {II,IV,VI}) and the transC2 closed form is SHARED across those
  three.  These three lemmas generalise the condI-only bricks to the shared branch,
  removing the false \<open>condI\<close>-only assumption at the transC2, append-base, and
  redslice-discharge levels.\<close>

text \<open>(E.2)-1: transC2 CLOSED FORM for the SHARED condI/III/V branch.  Generalises
  @{thm [source] m_8_5_transC2_condI}: the \<open>if\<close>-guard of @{const transC2} is literally
  \<open>transCondI M \<or> transCondIII M \<or> transCondV M\<close>, so any disjunct fires the same branch.\<close>

lemma m_8_5_transC2_shared:
  fixes M :: pairseq
  assumes "transCondI M \<or> transCondIII M \<or> transCondV M"
  shows "transC2 M
       = Dpt (transV M) (transT2 M +\<^sub>B Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
  using assms by (simp add: transC2_def Let_def transJ1_def)

text \<open>(E.2)-2: the SHARED Adm0-collapse append BASE.  Generalises
  @{thm [source] m_8_5_condI_append_base} from \<open>transCondI\<close> to the shared
  \<open>transCondI \<or> transCondIII \<or> transCondV\<close> branch (uses @{thm [source] m_8_5_transC2_shared});
  the Adm0 collapse, the transT2 readback and the full-slice rewrite are regime-free.
  Gives the uniform col0 base \<open>Trans M = D\<^bsub>v\<^esub>(bpHeadT (Trans (Pred M)) +\<^sub>B D\<^bsub>e\<^esub> 0\<^sub>B)\<close> for
  ANY \<open>e = entry M 1 (Lng M-1)\<close> (e=0 condI, e>0 condIII/V).\<close>

lemma m_8_5_shared_append_base:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and Adm0: "transJm1 M = 0"
    and cS: "transCondI M \<or> transCondIII M \<or> transCondV M"
    and mk0: "(Pred M, 0) \<in> Marked"
    and rng: "0 < Lng (Pred M) - 1"
  shows "Trans M
       = Dpt (transV M)
           (bpHeadT (Trans (Pred M)) +\<^sub>B Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
proof -
  have e1: "Trans M = transC2 M"
    by (rule Trans_eq_transC2_Adm0[OF MR MP J1pos T1 Adm0])
  have e2: "transC2 M
            = Dpt (transV M) (transT2 M +\<^sub>B Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
    by (rule m_8_5_transC2_shared[OF cS])
  have pr: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have mk': "(Pred M, transJm1 M) \<in> Marked" using mk0 Adm0 by simp
  have rng': "transJm1 M < Lng (Pred M) - 1" using rng Adm0 by simp
  have rb: "transT2 M
            = bpHeadT (Trans (seg (Pred M) (transJm1 M) (Lng (Pred M) - 1)))"
    by (rule m_8_5_transT2_readback[OF mk' pr rng'])
  have LP: "1 < Lng (Pred M)" using rng by linarith
  have segfull: "seg (Pred M) (transJm1 M) (Lng (Pred M) - 1) = Pred M"
  proof -
    have "seg (Pred M) 0 (Lng (Pred M) - 1) = take (Suc (Lng (Pred M) - 1)) (Pred M)"
      by (rule seg_0_eq_take) (use LP in linarith)
    also have "Suc (Lng (Pred M) - 1) = Lng (Pred M)" using LP by simp
    finally have "seg (Pred M) 0 (Lng (Pred M) - 1) = Pred M" by simp
    thus ?thesis using Adm0 by simp
  qed
  have t2: "transT2 M = bpHeadT (Trans (Pred M))" using rb segfull by simp
  show ?thesis using e1 e2 t2 by simp
qed

text \<open>(E.2)-3: the SHARED Adm0+cond DISCHARGE for the genuine col0.  Generalises
  @{thm [source] m_8_5_redslice_Adm0_condI}: under the back-slice repr hyps and
  \<open>transJm1 H = m\<close>, the reduced-slice col0 host \<open>M\<^sub>0 = Red (seg H m (Lng H-1))\<close> is Adm0 and
  keeps the host's trans-condition WITHIN \<open>{I,III,V}\<close> (via the existing
  @{thm [source] repr_transCondI_eq}, @{thm [source] repr_transCondIII_eq},
  @{thm [source] repr_transCondV_eq}).  This is the (E') replacement of the refuted (E):
  the col0 residual is membership in the SHARED branch, NOT \<open>entry(col0)=0\<close>.\<close>

lemma m_8_5_redslice_Adm0_shared:
  fixes H :: pairseq and m :: nat
  assumes mM: "(H, m) \<in> Marked" and HR: "H \<in> RT_PS"
    and mint: "m < Lng H - 2"
    and leM: "leR H 0 m (Lng H - 1)"
    and hp: "hasParent H 0 (Lng H - 1)"
    and anc0: "m \<le> parent H 0 (Lng H - 1)"
    and j0lt: "parent H 0 (Lng H - 1) < Lng H - 1"
    and base0: "transJm1 H = m"
    and cS: "transCondI H \<or> transCondIII H \<or> transCondV H"
  shows "transJm1 (Red (seg H m (Lng H - 1))) = 0
       \<and> (transCondI (Red (seg H m (Lng H - 1)))
          \<or> transCondIII (Red (seg H m (Lng H - 1)))
          \<or> transCondV (Red (seg H m (Lng H - 1))))"
proof -
  have shift: "transJm1 (Red (seg H m (Lng H - 1))) = transJm1 H - m"
    by (rule repr_transJm1_shift[OF mM HR mint leM hp anc0 j0lt])
  have A: "transJm1 (Red (seg H m (Lng H - 1))) = 0" using shift base0 by simp
  have BI: "transCondI (Red (seg H m (Lng H - 1))) = transCondI H"
    by (rule repr_transCondI_eq[OF mM HR mint leM hp anc0 j0lt])
  have BIII: "transCondIII (Red (seg H m (Lng H - 1))) = transCondIII H"
    by (rule repr_transCondIII_eq[OF mM HR mint leM hp anc0 j0lt])
  have BV: "transCondV (Red (seg H m (Lng H - 1))) = transCondV H"
    by (rule repr_transCondV_eq[OF mM HR mint leM hp anc0 j0lt])
  show ?thesis using A BI BIII BV cS by blast
qed

text \<open>§8.5 (E.2) ASSEMBLY — the F=C MATCH (step 4, the crux).  Reconciles the
  slice-surgery skeleton body \<open>t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> z\<close> with the spine wrap \<open>C z\<close>
  (\<open>C = \<lambda>x. unflatBT (s\<^sub>0 \<frown> D\<^bsub>v-1\<^esub> # flat x \<frown> b\<^sub>0)\<close>).  By @{thm [source] flat_addBT_Dpt}
  \<open>flat (t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> z) = liftS t\<^sub>2 [] \<frown> D\<^bsub>vm1\<^esub> # flat z \<frown> [RP]\<close>; so when the
  context matches — \<open>s\<^sub>0 = liftS t\<^sub>2 []\<close>, \<open>b\<^sub>0 = [RP]\<close>, \<open>vm1 = v-1\<close> — the \<open>C\<close>-string IS
  \<open>flat (t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> z)\<close>, hence \<open>C z = t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> z\<close> by @{thm [source] unflatBT_flat}.
  Python-validated (flat-identity + C-reconstruction 5/5).  Isolates the F=C match to
  the four context equalities (\<open>s\<^sub>0/b\<^sub>0/vm1/u\<close>), i.e. the n=1-base \<Rightarrow> slice-head scb
  CONTEXT STABILITY (the \<open>iterscb\<close> residual, @{thm [source] scb_context_eq_of_prefix}).\<close>

lemma m_8_5_FeqC_bridge:
  fixes t2 z :: BT and vm1 v e10 u :: nat and s0 b0 :: "Sym list" and C :: "BT \<Rightarrow> BT"
  assumes Cdef: "C = (\<lambda>x. unflatBT (s0 @ Dsym (enat (v - 1)) # flatBT x @ b0))"
    and prene: "untrm t2 \<noteq> []"
    and s0eq: "s0 = liftS t2 []"
    and b0eq: "b0 = [RP]"
    and vm1eq: "vm1 = v - 1"
    and ueq: "u = e10"
  shows "Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) z) = Dpt (enat u) (C z)"
proof -
  have flatcomp: "flatBT (t2 +\<^sub>B Dpt (enat vm1) z)
                    = liftS t2 (Dsym (enat vm1) # flatBT z) @ [RP]"
    by (rule flat_addBT_Dpt[OF prene])
  have flat2: "flatBT (t2 +\<^sub>B Dpt (enat vm1) z)
                 = liftS t2 [] @ Dsym (enat vm1) # flatBT z @ [RP]"
    using flatcomp by (simp add: liftS_def)
  have argEq: "s0 @ Dsym (enat (v - 1)) # flatBT z @ b0 = flatBT (t2 +\<^sub>B Dpt (enat vm1) z)"
    unfolding s0eq b0eq using flat2 vm1eq by simp
  have "C z = unflatBT (s0 @ Dsym (enat (v - 1)) # flatBT z @ b0)" by (simp add: Cdef)
  also have "\<dots> = unflatBT (flatBT (t2 +\<^sub>B Dpt (enat vm1) z))" using argEq by simp
  also have "\<dots> = t2 +\<^sub>B Dpt (enat vm1) z" by (rule unflatBT_flat)
  finally have CzEq: "C z = t2 +\<^sub>B Dpt (enat vm1) z" .
  show ?thesis using CzEq ueq by simp
qed

text \<open>§8.5 (E.2) ASSEMBLY — surgC FROM the skeleton output.  Given the slice surgery
  in skeleton form \<open>Trans (Y\<frown>B) = D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> (bpHeadT (Trans Y)))\<close> (assembled
  from @{thm [source] m_8_5_shared_append_base} (col0 base) + @{thm [source]
  m_8_5_reduced_slice_surgery_condI} (regime-agnostic) + @{thm [source]
  m_8_5_slice_surgery_skeleton}) and the F=C context match, yields EXACTLY the surgC
  hypothesis shape of @{thm [source] m_8_5_TransCondV_descend_kernel}:
  \<open>Trans (Y\<frown>B) = D\<^bsub>u\<^esub> (C (bpHeadT (Trans Y)))\<close>.\<close>

lemma m_8_5_surgC_of_skeleton:
  fixes Y B :: pairseq and t2 :: BT and e10 vm1 v u :: nat
    and s0 b0 :: "Sym list" and C :: "BT \<Rightarrow> BT"
  assumes skel: "Trans (Y @ B)
                   = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Y)))"
    and Cdef: "C = (\<lambda>x. unflatBT (s0 @ Dsym (enat (v - 1)) # flatBT x @ b0))"
    and prene: "untrm t2 \<noteq> []"
    and s0eq: "s0 = liftS t2 []"
    and b0eq: "b0 = [RP]"
    and vm1eq: "vm1 = v - 1"
    and ueq: "u = e10"
  shows "Trans (Y @ B) = Dpt (enat u) (C (bpHeadT (Trans Y)))"
proof -
  have "Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Y)))
          = Dpt (enat u) (C (bpHeadT (Trans Y)))"
    by (rule m_8_5_FeqC_bridge[OF Cdef prene s0eq b0eq vm1eq ueq])
  thus ?thesis using skel by simp
qed

text \<open>§8.5 (E.2) ASSEMBLY — surgC FROM the GEOM-ENDPOINT surgery (the CORRECTED route).
  Chains the FIXED-t2 composition engine @{thm [source] m_8_5_surgery_of_geom_endpoint}
  (base spine-shape + the all-deepen suffix walk over \<open>B\<close> + the endpoint readback) into
  @{thm [source] m_8_5_surgC_of_skeleton}, yielding the surgC hypothesis shape of
  @{thm [source] m_8_5_TransCondV_descend_kernel}.  This is the route the sub-agent (E.2)
  empirical analysis VALIDATED (base jm1, NOT per-iterate): the surgery body is the
  keystone-graft \<open>t\<^sub>2\<^bsub>FIX\<^esub> +\<^sub>B D\<^bsub>vm1\<^esub> (bpHeadT (Trans Y))\<close> with \<open>t\<^sub>2\<^bsub>FIX\<^esub>\<close> the FIXED q=1 base
  head (\<open>s\<^sub>0 = liftS t\<^sub>2\<^bsub>FIX\<^esub> []\<close>), NOT the self-form of the q=1-only
  @{thm [source] m_8_5_reduced_slice_surgery_condI}.  Empirically (E.2): the base
  spine-shape 5/5, the endpoint readback \<open>spineLeaf (Trans (Y\<frown>B)) = bpHeadT (Trans Y)\<close> 5/5,
  surgC-with-fixed-context-C verified.  The endpoint readback (the per-column value-pinning,
  the keystone-deepen matching) is the SINGLE remaining master-key residual; everything else
  (base spine-shape, the all-deepen geometric hyps, the bridge context) is owned/satisfiable.\<close>

lemma m_8_5_surgC_of_geom:
  fixes Y B :: pairseq and t2 :: BT and e10 vm1 v u :: nat
    and s0 b0 :: "Sym list" and C :: "BT \<Rightarrow> BT"
  assumes base: "Trans Y = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans Y)))"
    and gYne: "\<And>m. m < Lng B \<Longrightarrow> 0 < Lng (Y @ take m B)"
    and gMR: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> RT_PS"
    and gMP: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> PT_PS"
    and gBrne: "\<And>m. m < Lng B \<Longrightarrow> Br ((Y @ take m B) @ [B ! m]) \<noteq> []"
    and gj1gt: "\<And>m. m < Lng B \<Longrightarrow> Lng ((Y @ take m B) @ [B ! m]) - 1 > 1"
    and gpar: "\<And>m. m < Lng B \<Longrightarrow> parent ((Y @ take m B) @ [B ! m]) 0
                 (Lng ((Y @ take m B) @ [B ! m]) - 1) > TrMax ((Y @ take m B) @ [B ! m])"
    and ge10: "\<And>m. m < Lng B \<Longrightarrow> entry ((Y @ take m B) @ [B ! m]) 1 0 = e10"
    and endpoint: "spineLeaf (Trans (Y @ B)) = bpHeadT (Trans Y)"
    and Cdef: "C = (\<lambda>x. unflatBT (s0 @ Dsym (enat (v - 1)) # flatBT x @ b0))"
    and prene: "untrm t2 \<noteq> []"
    and s0eq: "s0 = liftS t2 []"
    and b0eq: "b0 = [RP]"
    and vm1eq: "vm1 = v - 1"
    and ueq: "u = e10"
  shows "Trans (Y @ B) = Dpt (enat u) (C (bpHeadT (Trans Y)))"
proof -
  have skel: "Trans (Y @ B)
                = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Y)))"
    by (rule m_8_5_surgery_of_geom_endpoint
          [OF base gYne gMR gMP gBrne gj1gt gpar ge10 endpoint])
  show ?thesis
    by (rule m_8_5_surgC_of_skeleton[OF skel Cdef prene s0eq b0eq vm1eq ueq])
qed

text \<open>§8.5 (E.2) — the C-BODY identity (standalone).  Under the context match
  (\<open>s\<^sub>0 = liftS t\<^sub>2 []\<close>, \<open>b\<^sub>0 = [RP]\<close>, \<open>vm1 = v-1\<close>), the spine wrap \<open>C\<close> acts on ANY \<open>z\<close> as the
  single sibling-append \<open>C z = t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> z\<close> (\<open>flat_addBT_Dpt\<close> + \<open>unflatBT_flat\<close>).
  The body-level core of @{thm [source] m_8_5_FeqC_bridge}.\<close>

lemma m_8_5_C_body:
  fixes t2 z :: BT and vm1 v :: nat and s0 b0 :: "Sym list" and C :: "BT \<Rightarrow> BT"
  assumes Cdef: "C = (\<lambda>x. unflatBT (s0 @ Dsym (enat (v - 1)) # flatBT x @ b0))"
    and prene: "untrm t2 \<noteq> []"
    and s0eq: "s0 = liftS t2 []"
    and b0eq: "b0 = [RP]"
    and vm1eq: "vm1 = v - 1"
  shows "C z = t2 +\<^sub>B Dpt (enat vm1) z"
proof -
  have flatcomp: "flatBT (t2 +\<^sub>B Dpt (enat vm1) z)
                    = liftS t2 (Dsym (enat vm1) # flatBT z) @ [RP]"
    by (rule flat_addBT_Dpt[OF prene])
  have flat2: "flatBT (t2 +\<^sub>B Dpt (enat vm1) z)
                 = liftS t2 [] @ Dsym (enat vm1) # flatBT z @ [RP]"
    using flatcomp by (simp add: liftS_def)
  have argEq: "s0 @ Dsym (enat (v - 1)) # flatBT z @ b0 = flatBT (t2 +\<^sub>B Dpt (enat vm1) z)"
    unfolding s0eq b0eq using flat2 vm1eq by simp
  have "C z = unflatBT (s0 @ Dsym (enat (v - 1)) # flatBT z @ b0)" by (simp add: Cdef)
  also have "\<dots> = unflatBT (flatBT (t2 +\<^sub>B Dpt (enat vm1) z))" using argEq by simp
  also have "\<dots> = t2 +\<^sub>B Dpt (enat vm1) z" by (rule unflatBT_flat)
  finally show ?thesis .
qed

text \<open>§8.5 (E.2) — the ENDPOINT READBACK reduced to the BLOCK-C realization (the sharpest
  form of the surgC master-key value step).  The geom-endpoint surgery needs
  \<open>spineLeaf (Trans (Y\<frown>B)) = bpHeadT (Trans Y)\<close> (the per-column value-pinning).  Under the
  base spine-shape \<open>Trans Y = D\<^bsub>e10\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> (spineLeaf (Trans Y)))\<close> and the bridge
  context, \<open>bpHeadT (Trans Y) = t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> (spineLeaf (Trans Y)) = C (spineLeaf (Trans Y))\<close>
  (@{thm [source] m_8_5_C_body}), so the readback is EQUIVALENT to the single statement
  \<open>spineLeaf (Trans (Y\<frown>B)) = C (spineLeaf (Trans Y))\<close>: appending the block \<open>B\<close> applies
  exactly ONE \<open>C\<close>-graft to the spine leaf.  This is the canonical keystone-deepen
  value-pinning (the residual the §8 master key reduces to), in the form addressed by the
  deepen-commutation @{thm [source] m_8_5_scbSubst_addBT_commute}.  EMPIRICALLY 5/5 (base jm1).\<close>

lemma m_8_5_endpoint_of_blockC:
  fixes Y B :: pairseq and t2 :: BT and e10 vm1 v :: nat
    and s0 b0 :: "Sym list" and C :: "BT \<Rightarrow> BT"
  assumes shape: "Trans Y = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans Y)))"
    and Cdef: "C = (\<lambda>x. unflatBT (s0 @ Dsym (enat (v - 1)) # flatBT x @ b0))"
    and prene: "untrm t2 \<noteq> []"
    and s0eq: "s0 = liftS t2 []"
    and b0eq: "b0 = [RP]"
    and vm1eq: "vm1 = v - 1"
    and blockC: "spineLeaf (Trans (Y @ B)) = C (spineLeaf (Trans Y))"
  shows "spineLeaf (Trans (Y @ B)) = bpHeadT (Trans Y)"
proof -
  have cb: "C (spineLeaf (Trans Y)) = t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans Y))"
    by (rule m_8_5_C_body[OF Cdef prene s0eq b0eq vm1eq])
  have bh: "bpHeadT (Trans Y) = t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans Y))"
  proof -
    have "bpHeadT (Trans Y)
            = bpHeadT (Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans Y))))"
      by (rule arg_cong[OF shape])
    also have "\<dots> = t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans Y))" by simp
    finally show ?thesis .
  qed
  show ?thesis using blockC cb bh by simp
qed

text \<open>§8.5 (E.2) — blockC REDUCED to the §7.4 Trans-spine law (the CLEANEST residual).
  The endpoint/blockC residual \<open>spineLeaf (Trans (Y\<frown>B)) = bpHeadT (Trans Y)\<close> follows from
  the clean INTRINSIC §7.4 structural law
    \<open>spineLeaf (Trans X) = bpHeadT (Trans ((Pred^^(Pcut X)) X))\<close>
  (here \<open>X = Y\<frown>B\<close>; sub-agent (E.2) empirical 15/15 incl. q=4 — one rightmost-spine step of
  \<open>Trans X\<close> = stripping the first \<open>Pcut\<close>-block by iterated \<open>Pred\<close>) together with the slice
  GEOMETRY fact \<open>Pcut (Y\<frown>B) = Lng B\<close> (appended deepen-block size = first P-cut of the
  extended slice; empirical 10/10).  Since \<open>(Pred^^(Lng B)) (Y\<frown>B) = Y\<close>
  (@{thm [source] herd_Pred_pow_take}), the law lands exactly on \<open>bpHeadT (Trans Y)\<close>.  This
  isolates the §8 master-key VALUE content to ONE standalone §7.4 law on the rightmost spine
  of \<open>Trans\<close> of ANY reduced term — NO surgery context, NO per-column address decoding;
  attackable by structural induction on the \<open>P\<close>-block (multi/mono) decomposition.\<close>

lemma m_8_5_blockC_of_spinelaw:
  fixes Y B :: pairseq
  assumes spinelaw: "spineLeaf (Trans (Y @ B))
                       = bpHeadT (Trans ((Pred ^^ (Pcut (Y @ B))) (Y @ B)))"
    and pcuteq: "Pcut (Y @ B) = Lng B"
    and Yne: "0 < Lng Y"
  shows "spineLeaf (Trans (Y @ B)) = bpHeadT (Trans Y)"
proof -
  have lb: "Lng B < Lng (Y @ B)" using Yne by simp
  have "(Pred ^^ (Lng B)) (Y @ B) = take (Lng (Y @ B) - Lng B) (Y @ B)"
    by (rule herd_Pred_pow_take[OF lb])
  also have "\<dots> = Y" by simp
  finally have predeq: "(Pred ^^ (Lng B)) (Y @ B) = Y" .
  have "spineLeaf (Trans (Y @ B)) = bpHeadT (Trans ((Pred ^^ (Pcut (Y @ B))) (Y @ B)))"
    by (rule spinelaw)
  also have "(Pred ^^ (Pcut (Y @ B))) (Y @ B) = Y" using pcuteq predeq by simp
  finally show ?thesis .
qed

text \<open>§8.5 (E.2) FACT-1 sub-obligation 1 — the EXPLICIT deepen block (oper periodicity).
  Sharpens @{thm [source] m_8_4_oper_Suc_append} (which gives only \<open>\<exists>B\<close>) to the EXPLICIT
  appended block: going \<open>M[n] \<rightarrow> M[Suc n]\<close> appends exactly the \<open>k = n\<close> period-copy
  \<open>\<beta>\<^bsub>n\<^esub> = map (\<lambda>j. (entry M 0 j + n\<cdot>d\<^sub>0, entry M 1 j)) [j\<^sub>0..<j\<^sub>1]\<close>
  (\<open>j\<^sub>0 = parent M 1 (Lng M-1)\<close>, \<open>j\<^sub>1 = Lng M-1\<close>, \<open>d\<^sub>0 = entry M 0 j\<^sub>1 - entry M 0 j\<^sub>0\<close>), read off the
  \<open>oper\<close> general form @{thm [source] m_8_4_oper_genform}.  Row-1 is COPIED VERBATIM and
  row-0 is shifted by \<open>n\<cdot>d\<^sub>0\<close> — so \<open>\<beta>\<^bsub>Suc n\<^esub>\<close>'s row-0 = \<open>\<beta>\<^bsub>n\<^esub>\<close>'s row-0 \<open>+ d\<^sub>0\<close> (the period
  shift; see the row-0 corollary below).  This is the foundation for the
  slice le0-periodicity (FACT 1 sub-ob 2/3); pure \<open>oper\<close> geometry, no \<open>Trans\<close>.\<close>

lemma m_8_5_deepen_block_explicit:
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
  shows "M[Suc n] = M[n] @
           map (\<lambda>j. (entry M 0 j
                       + n * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))),
                      entry M 1 j))
               [parent M 1 (Lng M - 1)..<Lng M - 1]"
proof -
  let ?blk = "\<lambda>k. map (\<lambda>j. (entry M 0 j
                              + k * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))),
                             entry M 1 j))
                       [parent M 1 (Lng M - 1)..<Lng M - 1]"
  have gn: "M[n] = take (parent M 1 (Lng M - 1)) M @ concat (map ?blk [0..<n])"
    by (rule m_8_4_oper_genform[OF j1pos e1pos hp])
  have gsn: "M[Suc n] = take (parent M 1 (Lng M - 1)) M @ concat (map ?blk [0..<Suc n])"
    by (rule m_8_4_oper_genform[OF j1pos e1pos hp])
  have split: "[0..<Suc n] = [0..<n] @ [n]" by simp
  have "concat (map ?blk [0..<Suc n]) = concat (map ?blk [0..<n]) @ ?blk n"
    using split by simp
  hence "M[Suc n] = (take (parent M 1 (Lng M - 1)) M @ concat (map ?blk [0..<n])) @ ?blk n"
    using gsn by simp
  thus ?thesis using gn by simp
qed

text \<open>§8.5 (E.2) FACT-1 sub-obligation 1 (row-0 periodicity corollary).  The explicit
  deepen block @{thm [source] m_8_5_deepen_block_explicit} has, at every interior index
  \<open>i\<close>, row-0 \<open>= entry M 0 (j\<^sub>0+i) + n\<cdot>d\<^sub>0\<close> and row-1 \<open>= entry M 1 (j\<^sub>0+i)\<close> — the
  period-\<open>(j\<^sub>1-j\<^sub>0)\<close>, \<open>+d\<^sub>0\<close>-shift structure that drives the slice le0-cuts.\<close>

lemma m_8_5_deepen_block_row0:
  assumes "i < Lng M - 1 - parent M 1 (Lng M - 1)"
  shows "fst (map (\<lambda>j. (entry M 0 j
                          + n * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))),
                         entry M 1 j))
                  [parent M 1 (Lng M - 1)..<Lng M - 1] ! i)
       = entry M 0 (parent M 1 (Lng M - 1) + i)
           + n * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1)))"
  using assms by simp

text \<open>§8.5 (E.2) FACT-1 ASSEMBLY — \<open>Pcut\<close> from the two le0-cut facts.  Reduces
  \<open>Pcut X = w\<close> to: (sub-ob 2) \<open>w\<close> IS a le0-cut \<open>leR X 0 w (Lng X-1)\<close>, and (sub-ob 3) NO
  smaller \<open>j\<close> is a cut \<open>\<forall>0<j<w. \<not> leR X 0 j (Lng X-1)\<close>, via \<open>Least_equality\<close> on the
  @{thm [source] Pcut_def} \<open>LEAST\<close>.  Instantiated at \<open>X = Y\<frown>B\<close>, \<open>w = Lng B\<close> this is FACT 1
  (\<open>m_8_5_Pcut_append_block\<close>): the appended condV-deepen period \<open>B\<close> is the FIRST le0-period
  of the extended slice.  sub-ob 2/3 are pure §6.2 le0/nextrel0 facts on the periodic
  slice (period \<open>w = Lng B\<close>, established green by @{thm [source] m_8_5_deepen_block_explicit});
  both empirically 16/16.\<close>

lemma m_8_5_Pcut_of_le0_cut:
  fixes X :: pairseq and w :: nat
  assumes wpos: "0 < w" and wle: "w \<le> Lng X - 1"
    and cut: "leR X 0 w (Lng X - 1)"
    and nocut: "\<And>j. 0 < j \<Longrightarrow> j < w \<Longrightarrow> \<not> leR X 0 j (Lng X - 1)"
  shows "Pcut X = w"
proof -
  have "(LEAST j. 0 < j \<and> j \<le> Lng X - 1 \<and> leR X 0 j (Lng X - 1)) = w"
  proof (rule Least_equality)
    show "0 < w \<and> w \<le> Lng X - 1 \<and> leR X 0 w (Lng X - 1)" using wpos wle cut by simp
  next
    fix j assume hj: "0 < j \<and> j \<le> Lng X - 1 \<and> leR X 0 j (Lng X - 1)"
    show "w \<le> j"
    proof (rule ccontr)
      assume "\<not> w \<le> j"
      hence "j < w" by simp
      thus False using hj nocut[of j] by simp
    qed
  qed
  thus ?thesis by (simp add: Pcut_def)
qed

text \<open>§8.5 (E.2) FACT-1 sub-ob 2 helper — the slice is the CONCAT of period copies.
  Dropping the trunk prefix \<open>take j\<^sub>0 M\<close> from \<open>M[n]\<close> leaves exactly the periodic copies
  \<open>concat (map \<beta>\<^bsub>k\<^esub> [0..<n])\<close> (\<open>j\<^sub>0 = parent M 1 (Lng M-1)\<close>).  Since for the condV slice
  \<open>jm1 = j\<^sub>0\<close>, \<open>seg (M[Suc q]) jm1 (Lng-1) = drop jm1 (M[Suc q]) = concat (period copies)\<close> —
  the periodic slice form.  From @{thm [source] m_8_4_oper_genform} + \<open>drop_append\<close>.\<close>

lemma m_8_5_slice_concat:
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
  shows "drop (parent M 1 (Lng M - 1)) (M[n])
       = concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j
                                       + k * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))),
                                      entry M 1 j))
                              [parent M 1 (Lng M - 1)..<Lng M - 1])
                     [0..<n])"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"
  let ?cc = "concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j
                                          + k * (entry M 0 (Lng M - 1) - entry M 0 ?j0),
                                         entry M 1 j))
                                 [?j0..<Lng M - 1])
                        [0..<n])"
  have gn: "M[n] = take ?j0 M @ ?cc" by (rule m_8_4_oper_genform[OF j1pos e1pos hp])
  have ltk: "length (take ?j0 M) = ?j0" using j0le by simp
  have "drop ?j0 (M[n]) = drop ?j0 (take ?j0 M @ ?cc)" using gn by simp
  also have "\<dots> = drop ?j0 (take ?j0 M) @ drop (?j0 - length (take ?j0 M)) ?cc"
    by (simp add: drop_append)
  also have "\<dots> = ?cc" using ltk by simp
  finally show ?thesis .
qed

text \<open>§8.5 (E.2) FACT-1 sub-ob 2 helper — the slice's PERIODIC row-0.  At every index
  \<open>k\<cdot>w + r\<close> (\<open>w = (Lng M-1) - j\<^sub>0\<close>, \<open>k<n\<close>, \<open>r<w\<close>), the slice \<open>drop j\<^sub>0 (M[n])\<close> has row-0
  \<open>= entry M 0 (j\<^sub>0+r) + k\<cdot>d\<^sub>0\<close> (\<open>d\<^sub>0 = entry M 0 (Lng M-1) - entry M 0 j\<^sub>0\<close>).  From
  @{thm [source] m_8_5_slice_concat} + @{thm [source] nth_concat_map_const_len} (each
  period block has constant length \<open>w\<close>) + \<open>nth_map\<close>/\<open>nth_upt\<close>.  This is the explicit
  periodic row-0 the le0-cut reasoning (sub-ob 2/3) runs on.\<close>

lemma m_8_5_slice_entry0:
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
    and r: "r < Lng M - 1 - parent M 1 (Lng M - 1)"
    and k: "k < n"
  shows "entry (drop (parent M 1 (Lng M - 1)) (M[n])) 0
            (k * (Lng M - 1 - parent M 1 (Lng M - 1)) + r)
       = entry M 0 (parent M 1 (Lng M - 1) + r)
           + k * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1)))"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"
  let ?w = "Lng M - 1 - ?j0"
  let ?d0 = "entry M 0 (Lng M - 1) - entry M 0 ?j0"
  let ?B = "\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j)) [?j0..<Lng M - 1]"
  have sc: "drop ?j0 (M[n]) = concat (map ?B [0..<n])"
    by (rule m_8_5_slice_concat[OF j1pos e1pos hp j0le])
  have lenB: "\<And>kk. kk < n \<Longrightarrow> length (?B kk) = ?w" by simp
  have nthc: "concat (map ?B [0..<n]) ! (k * ?w + r) = (?B k) ! r"
    by (rule nth_concat_map_const_len[OF lenB r k])
  have nthB: "(?B k) ! r = (entry M 0 (?j0 + r) + k * ?d0, entry M 1 (?j0 + r))"
    using r by simp
  have "entry (drop ?j0 (M[n])) 0 (k * ?w + r)
          = fst (concat (map ?B [0..<n]) ! (k * ?w + r))"
    using sc by (simp add: entry_def)
  also have "\<dots> = fst ((?B k) ! r)" using nthc by simp
  also have "\<dots> = entry M 0 (?j0 + r) + k * ?d0" using nthB by simp
  finally show ?thesis .
qed

text \<open>§8.5 (E.2) FACT-1 sub-ob 2 helper — the slice LENGTH.  \<open>Lng (drop j\<^sub>0 (M[n])) = n\<cdot>w\<close>
  (\<open>w = (Lng M-1) - j\<^sub>0\<close>): the \<open>n\<close> period copies each have length \<open>w\<close>.  From
  @{thm [source] m_8_5_slice_concat} + \<open>length_concat\<close>.\<close>

lemma m_8_5_Lng_slice:
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
  shows "Lng (drop (parent M 1 (Lng M - 1)) (M[n]))
       = n * (Lng M - 1 - parent M 1 (Lng M - 1))"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"
  let ?w = "Lng M - 1 - ?j0"
  let ?B = "\<lambda>k. map (\<lambda>j. (entry M 0 j + k * (entry M 0 (Lng M - 1) - entry M 0 ?j0),
                          entry M 1 j))
                  [?j0..<Lng M - 1]"
  have sc: "drop ?j0 (M[n]) = concat (map ?B [0..<n])"
    by (rule m_8_5_slice_concat[OF j1pos e1pos hp j0le])
  have "length (concat (map ?B [0..<n])) = sum_list (map length (map ?B [0..<n]))"
    by (simp add: length_concat)
  also have "map length (map ?B [0..<n]) = map (\<lambda>k. ?w) [0..<n]" by simp
  also have "sum_list (map (\<lambda>k. ?w) [0..<n]) = n * ?w" by (simp add: sum_list_triv)
  finally show ?thesis using sc by simp
qed

text \<open>§8.5 (E.2) FACT-1 sub-ob 2 — the BLOCK-START nextrel0 step.  In the periodic slice
  \<open>X = drop j\<^sub>0 (M[Suc q])\<close>, consecutive period boundaries are \<open>nextrel0\<close>-linked:
  \<open>nextrel0 X (k\<cdot>w) ((Suc k)\<cdot>w)\<close> for \<open>Suc k \<le> q\<close>.  The row-0 lt and the
  "all-between-≥-endpoint" both come from \<open>parR\<close> (\<open>nextrel0 M j\<^sub>0 (Lng M-1)\<close>, the committed
  condV fact) transported through the \<open>+k\<cdot>d\<^sub>0\<close> period shift (@{thm [source] m_8_5_slice_entry0}).\<close>

lemma m_8_5_slice_nextrel0_blockstart:
  fixes M :: pairseq and q k :: nat
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and kq: "Suc k \<le> q"
  shows "nextrel0 (drop (parent M 1 (Lng M - 1)) (M[Suc q]))
            (k * (Lng M - 1 - parent M 1 (Lng M - 1)))
            (Suc k * (Lng M - 1 - parent M 1 (Lng M - 1)))"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"
  let ?w = "Lng M - 1 - ?j0"
  let ?d0 = "entry M 0 (Lng M - 1) - entry M 0 ?j0"
  let ?X = "drop ?j0 (M[Suc q])"
  have lt0: "entry M 0 ?j0 < entry M 0 (Lng M - 1)" using parR by (simp add: nextrel0_def)
  have j0lt: "?j0 < Lng M - 1" using parR by (simp add: nextrel0_def)
  have wpos: "0 < ?w" using j0lt by simp
  have d0pos: "0 < ?d0" using lt0 by simp
  have d0eq: "entry M 0 ?j0 + ?d0 = entry M 0 (Lng M - 1)" using lt0 by simp
  have LngX: "Lng ?X = Suc q * ?w" by (rule m_8_5_Lng_slice[OF j1pos e1pos hp j0le])
  have klt: "k < Suc q" using kq by simp
  have k1lt: "Suc k < Suc q" using kq by simp
  have betwall: "\<forall>jj. ?j0 < jj \<and> jj < Lng M - 1 \<longrightarrow> entry M 0 jj \<ge> entry M 0 (Lng M - 1)"
    using parR by (simp add: nextrel0_def)
  have a: "entry ?X 0 (k * ?w) = entry M 0 ?j0 + k * ?d0"
    using m_8_5_slice_entry0[OF j1pos e1pos hp j0le wpos klt] by simp
  have b: "entry ?X 0 (Suc k * ?w) = entry M 0 ?j0 + Suc k * ?d0"
    using m_8_5_slice_entry0[OF j1pos e1pos hp j0le wpos k1lt] by simp
  show ?thesis
    unfolding nextrel0_def
  proof (intro conjI allI impI)
    show "k * ?w < Lng ?X"
      using mult_strict_right_mono[OF klt wpos] by (simp only: LngX)
    show "Suc k * ?w < Lng ?X"
      using mult_strict_right_mono[OF k1lt wpos] by (simp only: LngX)
    show "k * ?w < Suc k * ?w" using wpos by simp
    have sukd: "Suc k * ?d0 = ?d0 + k * ?d0" by simp
    show "entry ?X 0 (k * ?w) < entry ?X 0 (Suc k * ?w)"
      using a b d0pos sukd by linarith
  next
    fix j assume hj: "k * ?w < j \<and> j < Suc k * ?w"
    define r where "r = j - k * ?w"
    have suck: "Suc k * ?w = ?w + k * ?w" by simp
    have rpos: "0 < r" using hj r_def by linarith
    have rlt: "r < ?w" using hj r_def suck by linarith
    have jeq: "j = k * ?w + r" using hj r_def by linarith
    have ej: "entry ?X 0 j = entry M 0 (?j0 + r) + k * ?d0"
      using m_8_5_slice_entry0[OF j1pos e1pos hp j0le rlt klt] jeq by simp
    have jjlt: "?j0 + r < Lng M - 1" using rlt by simp
    have jjgt: "?j0 < ?j0 + r" using rpos by simp
    have betw: "entry M 0 (?j0 + r) \<ge> entry M 0 (Lng M - 1)" using betwall jjgt jjlt by blast
    have sukd: "Suc k * ?d0 = ?d0 + k * ?d0" by simp
    show "entry ?X 0 (Suc k * ?w) \<le> entry ?X 0 j"
      using ej b betw d0eq sukd by linarith
  qed
qed

text \<open>§8.5 (E.2) FACT-1 sub-ob 2 — the WITHIN-BLOCK nextrel0 shift-invariance.  Inside one
  period block (block \<open>k\<close>), \<open>nextrel0\<close> on the slice mirrors \<open>nextrel0\<close> on the base \<open>M\<close>:
  \<open>nextrel0 M (j\<^sub>0+a) (j\<^sub>0+b) \<Longrightarrow> nextrel0 X (k\<cdot>w+a) (k\<cdot>w+b)\<close> (for \<open>a,b<w\<close>, \<open>k<Suc q\<close>) —
  the per-period entry shift \<open>+k\<cdot>d\<^sub>0\<close> cancels in every \<open>nextrel0\<close> comparison
  (@{thm [source] m_8_5_slice_entry0}).  Forward direction; used to transport the base's
  within-block le0-reachability (\<open>le0(M, j\<^sub>0, Lng M-2)\<close>) into the last slice block.\<close>

lemma m_8_5_slice_nextrel0_shift:
  fixes M :: pairseq and q k a b :: nat
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
    and kq: "k < Suc q"
    and aw: "a < Lng M - 1 - parent M 1 (Lng M - 1)"
    and bw: "b < Lng M - 1 - parent M 1 (Lng M - 1)"
    and nr: "nextrel0 M (parent M 1 (Lng M - 1) + a) (parent M 1 (Lng M - 1) + b)"
  shows "nextrel0 (drop (parent M 1 (Lng M - 1)) (M[Suc q]))
            (k * (Lng M - 1 - parent M 1 (Lng M - 1)) + a)
            (k * (Lng M - 1 - parent M 1 (Lng M - 1)) + b)"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"
  let ?w = "Lng M - 1 - ?j0"
  let ?d0 = "entry M 0 (Lng M - 1) - entry M 0 ?j0"
  let ?X = "drop ?j0 (M[Suc q])"
  have LngX: "Lng ?X = Suc q * ?w" by (rule m_8_5_Lng_slice[OF j1pos e1pos hp j0le])
  have nr': "?j0 + a < ?j0 + b \<and> entry M 0 (?j0 + a) < entry M 0 (?j0 + b)
             \<and> (\<forall>jj. ?j0 + a < jj \<and> jj < ?j0 + b \<longrightarrow> entry M 0 jj \<ge> entry M 0 (?j0 + b))"
    using nr by (simp add: nextrel0_def)
  have ablt: "a < b" using nr' by simp
  have ea: "entry ?X 0 (k * ?w + a) = entry M 0 (?j0 + a) + k * ?d0"
    using m_8_5_slice_entry0[OF j1pos e1pos hp j0le aw kq] by simp
  have eb: "entry ?X 0 (k * ?w + b) = entry M 0 (?j0 + b) + k * ?d0"
    using m_8_5_slice_entry0[OF j1pos e1pos hp j0le bw kq] by simp
  have skle: "Suc k * ?w \<le> Suc q * ?w" using kq by (simp add: mult_le_mono1)
  show ?thesis
    unfolding nextrel0_def
  proof (intro conjI allI impI)
    show "k * ?w + a < Lng ?X"
    proof -
      have "k * ?w + a < Suc k * ?w" using aw by simp
      also have "Suc k * ?w \<le> Suc q * ?w" by (rule skle)
      also have "Suc q * ?w = Lng ?X" by (simp only: LngX)
      finally show ?thesis .
    qed
    show "k * ?w + b < Lng ?X"
    proof -
      have "k * ?w + b < Suc k * ?w" using bw by simp
      also have "Suc k * ?w \<le> Suc q * ?w" by (rule skle)
      also have "Suc q * ?w = Lng ?X" by (simp only: LngX)
      finally show ?thesis .
    qed
    show "k * ?w + a < k * ?w + b" using ablt by simp
    show "entry ?X 0 (k * ?w + a) < entry ?X 0 (k * ?w + b)"
      using ea eb nr' by simp
  next
    fix j assume hj: "k * ?w + a < j \<and> j < k * ?w + b"
    define r where "r = j - k * ?w"
    have rge: "a < r" using hj r_def by linarith
    have rlt: "r < b" using hj r_def by linarith
    have rw: "r < ?w" using rlt bw by simp
    have jeq: "j = k * ?w + r" using hj r_def by linarith
    have ej: "entry ?X 0 j = entry M 0 (?j0 + r) + k * ?d0"
      using m_8_5_slice_entry0[OF j1pos e1pos hp j0le rw kq] jeq by simp
    have jjr: "?j0 + a < ?j0 + r \<and> ?j0 + r < ?j0 + b" using rge rlt by simp
    have betwr: "entry M 0 (?j0 + r) \<ge> entry M 0 (?j0 + b)" using nr' jjr by blast
    show "entry ?X 0 (k * ?w + b) \<le> entry ?X 0 j" using ej eb betwr by simp
  qed
qed

text \<open>§8.5 (E.2) FACT-1 sub-ob 2 — WITHIN-LAST-BLOCK le0-transport.  Transports the base's
  within-block reachability \<open>le0(M, j\<^sub>0, Lng M-2)\<close> (the isolated condV fact) to
  \<open>le0 X (q\<cdot>w) (Lng X-1)\<close> in the LAST period block of the slice, via the per-step
  @{thm [source] m_8_5_slice_nextrel0_shift} (k=q) over the M-chain (`rtranclp` transport,
  all chain nodes block-relative \<open><w\<close>).  \<open>le0(M, j\<^sub>0, Lng M-2)\<close> is supplied from the
  condV setup (verified 35/35; sibling to \<open>parR\<close>).\<close>

lemma m_8_5_slice_le0_lastblock:
  fixes M :: pairseq and q :: nat
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
    and le0M: "le0 M (parent M 1 (Lng M - 1)) (Lng M - 2)"
  shows "le0 (drop (parent M 1 (Lng M - 1)) (M[Suc q]))
            (q * (Lng M - 1 - parent M 1 (Lng M - 1)))
            (Lng (drop (parent M 1 (Lng M - 1)) (M[Suc q])) - 1)"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"
  let ?w = "Lng M - 1 - ?j0"
  let ?X = "drop ?j0 (M[Suc q])"
  have chain: "(nextrel0 M)\<^sup>*\<^sup>* ?j0 (Lng M - 2)" using le0M by (simp add: le0_def)
  have j0leLM2: "?j0 \<le> Lng M - 2" using chain nextrel0_rtrancl_mono by blast
  have wpos: "0 < ?w" using j0leLM2 j1pos by simp
  have LngX: "Lng ?X = Suc q * ?w" by (rule m_8_5_Lng_slice[OF j1pos e1pos hp j0le])
  have trans: "\<And>c. (nextrel0 M)\<^sup>*\<^sup>* ?j0 c \<Longrightarrow> c < Lng M - 1 \<Longrightarrow>
                  (nextrel0 ?X)\<^sup>*\<^sup>* (q * ?w) (q * ?w + (c - ?j0))"
  proof -
    fix c assume H: "(nextrel0 M)\<^sup>*\<^sup>* ?j0 c"
    show "c < Lng M - 1 \<Longrightarrow> (nextrel0 ?X)\<^sup>*\<^sup>* (q * ?w) (q * ?w + (c - ?j0))"
      using H
    proof (induction rule: rtranclp_induct)
      case base show ?case by simp
    next
      case (step y z)
      have yz: "nextrel0 M y z" by (rule step.hyps(2))
      have ylt2: "y < z" using yz by (simp add: nextrel0_def)
      have zlt: "z < Lng M - 1" by (rule step.prems)
      have ylt: "y < Lng M - 1" using ylt2 zlt by simp
      have jy: "?j0 \<le> y" using step.hyps(1) nextrel0_rtrancl_mono by blast
      have IHy: "(nextrel0 ?X)\<^sup>*\<^sup>* (q * ?w) (q * ?w + (y - ?j0))" using step.IH ylt by simp
      have jz: "?j0 \<le> z" using jy ylt2 by simp
      have aw: "y - ?j0 < ?w" using ylt jy by linarith
      have bw: "z - ?j0 < ?w" using zlt jz by linarith
      have nrM: "nextrel0 M (?j0 + (y - ?j0)) (?j0 + (z - ?j0))"
        using yz jy jz by simp
      have nrX: "nextrel0 ?X (q * ?w + (y - ?j0)) (q * ?w + (z - ?j0))"
        by (rule m_8_5_slice_nextrel0_shift[OF j1pos e1pos hp j0le lessI aw bw nrM])
      from IHy nrX show ?case by (rule rtranclp.rtrancl_into_rtrancl)
    qed
  qed
  have endc: "Lng M - 2 < Lng M - 1" using j1pos by linarith
  have rt: "(nextrel0 ?X)\<^sup>*\<^sup>* (q * ?w) (q * ?w + ((Lng M - 2) - ?j0))"
    by (rule trans[OF chain endc])
  have idxeq: "q * ?w + ((Lng M - 2) - ?j0) = Lng ?X - 1"
  proof -
    have e1: "(Lng M - 2) - ?j0 = ?w - 1" by simp
    have "q * ?w + ((Lng M - 2) - ?j0) = q * ?w + (?w - 1)" using e1 by simp
    also have "\<dots> = Suc q * ?w - 1" using wpos by simp
    also have "\<dots> = Lng ?X - 1" using LngX by simp
    finally show ?thesis .
  qed
  have qwlt: "q * ?w < Lng ?X"
    using mult_strict_right_mono[OF lessI wpos] by (simp only: LngX)
  have lastlt: "Lng ?X - 1 < Lng ?X" using qwlt by linarith
  show ?thesis
    unfolding le0_def
  proof (intro conjI)
    show "q * ?w < Lng ?X" by (rule qwlt)
    show "Lng ?X - 1 < Lng ?X" by (rule lastlt)
    show "(nextrel0 ?X)\<^sup>*\<^sup>* (q * ?w) (Lng ?X - 1)" using rt idxeq by simp
  qed
qed

text \<open>§8.5 (E.2) FACT-1 sub-ob 2 (le0-cut) — \<open>le0 X w (Lng X-1)\<close>, the first le0-cut at
  the period boundary \<open>w = Lng B\<close>.  Block-start chain \<open>w \<rightarrow> 2w \<rightarrow> \<dots> \<rightarrow> q\<cdot>w\<close>
  (rtrancl of @{thm [source] m_8_5_slice_nextrel0_blockstart}, via \<open>parR\<close>) composed with
  the within-last-block reachability @{thm [source] m_8_5_slice_le0_lastblock} (via the
  isolated \<open>le0(M, j\<^sub>0, Lng M-2)\<close>).  This is sub-ob 2 of FACT 1.\<close>

lemma m_8_5_slice_le0_cut:
  fixes M :: pairseq and q :: nat
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and le0M: "le0 M (parent M 1 (Lng M - 1)) (Lng M - 2)"
    and q1: "1 \<le> q"
  shows "le0 (drop (parent M 1 (Lng M - 1)) (M[Suc q]))
            (Lng M - 1 - parent M 1 (Lng M - 1))
            (Lng (drop (parent M 1 (Lng M - 1)) (M[Suc q])) - 1)"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"
  let ?w = "Lng M - 1 - ?j0"
  let ?X = "drop ?j0 (M[Suc q])"
  have j0lt: "?j0 < Lng M - 1" using parR by (simp add: nextrel0_def)
  have wpos: "0 < ?w" using j0lt by simp
  have LngX: "Lng ?X = Suc q * ?w" by (rule m_8_5_Lng_slice[OF j1pos e1pos hp j0le])
  \<comment> \<open>block-start chain \<open>w \<rightarrow> q\<cdot>w\<close>\<close>
  have chain: "\<And>k. Suc k \<le> q \<Longrightarrow> (nextrel0 ?X)\<^sup>*\<^sup>* ?w (Suc k * ?w)"
  proof -
    fix k assume "Suc k \<le> q"
    thus "(nextrel0 ?X)\<^sup>*\<^sup>* ?w (Suc k * ?w)"
    proof (induction k)
      case 0 show ?case by simp
    next
      case (Suc k)
      have IH: "(nextrel0 ?X)\<^sup>*\<^sup>* ?w (Suc k * ?w)" using Suc.IH Suc.prems by simp
      have st: "nextrel0 ?X (Suc k * ?w) (Suc (Suc k) * ?w)"
        by (rule m_8_5_slice_nextrel0_blockstart[OF j1pos e1pos hp j0le parR Suc.prems])
      from IH st show ?case by (rule rtranclp.rtrancl_into_rtrancl)
    qed
  qed
  have c1: "(nextrel0 ?X)\<^sup>*\<^sup>* ?w (q * ?w)"
  proof -
    have sq: "Suc (q - 1) \<le> q" using q1 by simp
    have "(nextrel0 ?X)\<^sup>*\<^sup>* ?w (Suc (q - 1) * ?w)" by (rule chain[OF sq])
    thus ?thesis using q1 by simp
  qed
  \<comment> \<open>within-last-block reachability \<open>q\<cdot>w \<rightarrow> last\<close>\<close>
  have wb: "le0 ?X (q * ?w) (Lng ?X - 1)"
    by (rule m_8_5_slice_le0_lastblock[OF j1pos e1pos hp j0le le0M])
  have c2: "(nextrel0 ?X)\<^sup>*\<^sup>* (q * ?w) (Lng ?X - 1)" using wb[unfolded le0_def] by blast
  have c12: "(nextrel0 ?X)\<^sup>*\<^sup>* ?w (Lng ?X - 1)" using c1 c2 by (rule rtranclp_trans)
  have wlt: "?w < Lng ?X"
  proof -
    have "?w < 2 * ?w" using wpos by simp
    also have "(2::nat) * ?w \<le> Suc q * ?w" using q1 by (simp add: mult_le_mono1)
    also have "Suc q * ?w = Lng ?X" by (simp only: LngX)
    finally show ?thesis .
  qed
  have lastlt: "Lng ?X - 1 < Lng ?X" using wlt by linarith
  show ?thesis
    unfolding le0_def
  proof (intro conjI)
    show "?w < Lng ?X" by (rule wlt)
    show "Lng ?X - 1 < Lng ?X" by (rule lastlt)
    show "(nextrel0 ?X)\<^sup>*\<^sup>* ?w (Lng ?X - 1)" by (rule c12)
  qed
qed

text \<open>§8.5 (E.2) FACT 1 ASSEMBLY — \<open>Pcut(slice) = Lng B\<close> (modulo sub-ob 3).  Combines
  sub-ob 2 (@{thm [source] m_8_5_slice_le0_cut}, the le0-cut at \<open>w = Lng B\<close>) and sub-ob 3
  (\<open>nocut\<close>, the interior non-ancestor property — supplied as a hyp; see the trapping
  invariant, empirically 142/142) via @{thm [source] m_8_5_Pcut_of_le0_cut}.  For the
  genuine condV slice \<open>X = drop jm1 (M[Suc q]) = seg (M[Suc q]) jm1 (Lng-1)\<close> with
  \<open>jm1 = j\<^sub>0\<close>, this is FACT 1: \<open>Pcut(Y\<frown>B) = Lng B\<close>.\<close>

lemma m_8_5_Pcut_append_block:
  fixes M :: pairseq and q :: nat
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and le0M: "le0 M (parent M 1 (Lng M - 1)) (Lng M - 2)"
    and q1: "1 \<le> q"
    and nocut: "\<And>j. 0 < j \<Longrightarrow> j < Lng M - 1 - parent M 1 (Lng M - 1) \<Longrightarrow>
                  \<not> leR (drop (parent M 1 (Lng M - 1)) (M[Suc q])) 0 j
                       (Lng (drop (parent M 1 (Lng M - 1)) (M[Suc q])) - 1)"
  shows "Pcut (drop (parent M 1 (Lng M - 1)) (M[Suc q]))
       = Lng M - 1 - parent M 1 (Lng M - 1)"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"
  let ?w = "Lng M - 1 - ?j0"
  let ?X = "drop ?j0 (M[Suc q])"
  have j0lt: "?j0 < Lng M - 1" using parR by (simp add: nextrel0_def)
  have wpos: "0 < ?w" using j0lt by simp
  have LngX: "Lng ?X = Suc q * ?w" by (rule m_8_5_Lng_slice[OF j1pos e1pos hp j0le])
  have wlt: "?w < Lng ?X"
  proof -
    have "?w < 2 * ?w" using wpos by simp
    also have "(2::nat) * ?w \<le> Suc q * ?w" using q1 by (simp add: mult_le_mono1)
    also have "Suc q * ?w = Lng ?X" by (simp only: LngX)
    finally show ?thesis .
  qed
  have wle: "?w \<le> Lng ?X - 1" using wlt by linarith
  have cut: "leR ?X 0 ?w (Lng ?X - 1)"
    using m_8_5_slice_le0_cut[OF j1pos e1pos hp j0le parR le0M q1] by (simp add: leR_def)
  show ?thesis by (rule m_8_5_Pcut_of_le0_cut[OF wpos wle cut nocut])
qed

text \<open>§8.5 (E.2) FACT-1 sub-ob 3 — the per-step TRAP.  An interior column of the first
  period (\<open>0<c<w\<close>) has every \<open>nextrel0\<close>-successor still in the first period (\<open>b<w\<close>):
  it cannot cross a block boundary.  Mechanism: \<open>entry0(X,c) \<ge> entry0(X,w)\<close> (interior \<open>c\<close>
  has row-0 \<open>\<ge> entry M 0 (Lng M-1) = entry0(X,w)\<close>, via \<open>parR\<close>'s between), so for any \<open>b\<ge>w\<close>
  the col-\<open>w\<close> witness forces \<open>entry0(X,c) < entry0(X,b) \<le> entry0(X,w) \<le> entry0(X,c)\<close>,
  a contradiction (@{thm [source] m_8_5_slice_entry0}).\<close>

lemma m_8_5_slice_nextrel0_trap:
  fixes M :: pairseq and q c b :: nat
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and q1: "1 \<le> q"
    and cpos: "0 < c"
    and cw: "c < Lng M - 1 - parent M 1 (Lng M - 1)"
    and nr: "nextrel0 (drop (parent M 1 (Lng M - 1)) (M[Suc q])) c b"
  shows "b < Lng M - 1 - parent M 1 (Lng M - 1)"
proof (rule ccontr)
  let ?j0 = "parent M 1 (Lng M - 1)"
  let ?w = "Lng M - 1 - ?j0"
  let ?d0 = "entry M 0 (Lng M - 1) - entry M 0 ?j0"
  let ?X = "drop ?j0 (M[Suc q])"
  assume "\<not> b < ?w"
  hence bw: "?w \<le> b" by simp
  have lt0: "entry M 0 ?j0 < entry M 0 (Lng M - 1)" using parR by (simp add: nextrel0_def)
  have wpos: "0 < ?w" using parR by (simp add: nextrel0_def)
  have s2: "Suc 0 < Suc q" using q1 by simp
  have betwall: "\<forall>jj. ?j0 < jj \<and> jj < Lng M - 1 \<longrightarrow> entry M 0 jj \<ge> entry M 0 (Lng M - 1)"
    using parR by (simp add: nextrel0_def)
  \<comment> \<open>\<open>entry0(X,c) = entry M 0 (j0+c) \<ge> entry M 0 (Lng M-1)\<close>\<close>
  have ec: "entry ?X 0 c = entry M 0 (?j0 + c)"
    using m_8_5_slice_entry0[OF j1pos e1pos hp j0le cw zero_less_Suc] by simp
  have jjc: "?j0 < ?j0 + c \<and> ?j0 + c < Lng M - 1" using cpos cw by simp
  have starM: "entry M 0 (?j0 + c) \<ge> entry M 0 (Lng M - 1)" using betwall jjc by blast
  have starc: "entry ?X 0 c \<ge> entry M 0 (Lng M - 1)" using starM ec by simp
  \<comment> \<open>\<open>entry0(X,w) = entry M 0 (Lng M-1)\<close>\<close>
  have ew0: "entry ?X 0 (Suc 0 * ?w + 0) = entry M 0 (?j0 + 0) + Suc 0 * ?d0"
    by (rule m_8_5_slice_entry0[OF j1pos e1pos hp j0le wpos s2])
  have ew: "entry ?X 0 ?w = entry M 0 (Lng M - 1)" using ew0 lt0 by simp
  have star: "entry ?X 0 ?w \<le> entry ?X 0 c" using starc ew by simp
  \<comment> \<open>contradiction from \<open>nr\<close>\<close>
  have nrc: "entry ?X 0 c < entry ?X 0 b" using nr by (simp add: nextrel0_def)
  show False
  proof (cases "b = ?w")
    case True
    show False using nrc star True by simp
  next
    case False
    hence wlt: "?w < b" using bw by simp
    have allbtw: "\<forall>i. c < i \<and> i < b \<longrightarrow> entry ?X 0 i \<ge> entry ?X 0 b"
      using nr by (simp add: nextrel0_def)
    have "entry ?X 0 ?w \<ge> entry ?X 0 b" using allbtw cw wlt by blast
    thus False using nrc star by simp
  qed
qed

text \<open>§8.5 (E.2) FACT-1 sub-ob 3 — the TRAPPING invariant.  Everything le0-reachable from
  an interior first-period column stays in the first period: \<open>le0 X c b \<and> 0<c<w \<Longrightarrow> b<w\<close>.
  \<open>rtranclp_induct\<close> over the chain, using the per-step
  @{thm [source] m_8_5_slice_nextrel0_trap} (the chain stays \<open>0<\<cdot><w\<close>).\<close>

lemma m_8_5_slice_le0_trap:
  fixes M :: pairseq and q c b :: nat
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and q1: "1 \<le> q"
    and cpos: "0 < c"
    and cw: "c < Lng M - 1 - parent M 1 (Lng M - 1)"
    and le0cb: "le0 (drop (parent M 1 (Lng M - 1)) (M[Suc q])) c b"
  shows "b < Lng M - 1 - parent M 1 (Lng M - 1)"
proof -
  let ?X = "drop (parent M 1 (Lng M - 1)) (M[Suc q])"
  have chain: "(nextrel0 ?X)\<^sup>*\<^sup>* c b" using le0cb by (simp add: le0_def)
  from chain show ?thesis
  proof (induction rule: rtranclp_induct)
    case base
    show ?case by (rule cw)
  next
    case (step y z)
    have cy: "c \<le> y" using step.hyps(1) nextrel0_rtrancl_mono by blast
    have ypos: "0 < y" using cpos cy by simp
    have yw: "y < Lng M - 1 - parent M 1 (Lng M - 1)" by (rule step.IH)
    show ?case
      by (rule m_8_5_slice_nextrel0_trap[OF j1pos e1pos hp j0le parR q1 ypos yw step.hyps(2)])
  qed
qed

text \<open>§8.5 (E.2) FACT-1 sub-ob 3 — the interior NON-CUT.  An interior first-period column
  \<open>0<j<w\<close> is NOT a le0-ancestor of the last column, since (trapping) any le0-reach from it
  stays \<open><w\<close>, but \<open>last = Lng X - 1 \<ge> w\<close> (\<open>q\<ge>1\<close>, \<open>X\<close> spans \<open>\<ge>2\<close> periods).\<close>

lemma m_8_5_slice_interior_nocut:
  fixes M :: pairseq and q j :: nat
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and q1: "1 \<le> q"
    and jpos: "0 < j"
    and jw: "j < Lng M - 1 - parent M 1 (Lng M - 1)"
  shows "\<not> leR (drop (parent M 1 (Lng M - 1)) (M[Suc q])) 0 j
            (Lng (drop (parent M 1 (Lng M - 1)) (M[Suc q])) - 1)"
proof (rule notI)
  let ?j0 = "parent M 1 (Lng M - 1)"
  let ?w = "Lng M - 1 - ?j0"
  let ?X = "drop ?j0 (M[Suc q])"
  assume "leR ?X 0 j (Lng ?X - 1)"
  hence le: "le0 ?X j (Lng ?X - 1)" by (simp add: leR_def)
  have bw: "Lng ?X - 1 < ?w"
    by (rule m_8_5_slice_le0_trap[OF j1pos e1pos hp j0le parR q1 jpos jw le])
  have j0lt: "?j0 < Lng M - 1" using parR by (simp add: nextrel0_def)
  have wpos: "0 < ?w" using j0lt by simp
  have LngX: "Lng ?X = Suc q * ?w" by (rule m_8_5_Lng_slice[OF j1pos e1pos hp j0le])
  have wle: "?w \<le> Lng ?X - 1"
  proof -
    have "?w < 2 * ?w" using wpos by simp
    also have "(2::nat) * ?w \<le> Suc q * ?w" using q1 by (simp add: mult_le_mono1)
    also have "Suc q * ?w = Lng ?X" by (simp only: LngX)
    finally have "?w < Lng ?X" .
    thus ?thesis by linarith
  qed
  show False using bw wle by linarith
qed

text \<open>§8.5 (E.2) FACT 1 (final) — \<open>Pcut(slice) = Lng B\<close>, the interior non-cut sub-ob 3
  now discharged.  surgC's geometry residual \<open>Pcut(Y\<frown>B) = Lng B\<close> reduces to ONLY the
  two condV-setup facts \<open>parR\<close> (committed) and \<open>le0(M, j\<^sub>0, Lng M-2)\<close> (isolated, 35/35).\<close>

lemma m_8_5_Pcut_append:
  fixes M :: pairseq and q :: nat
  assumes j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and le0M: "le0 M (parent M 1 (Lng M - 1)) (Lng M - 2)"
    and q1: "1 \<le> q"
  shows "Pcut (drop (parent M 1 (Lng M - 1)) (M[Suc q]))
       = Lng M - 1 - parent M 1 (Lng M - 1)"
  by (rule m_8_5_Pcut_append_block[OF j1pos e1pos hp j0le parR le0M q1
        m_8_5_slice_interior_nocut[OF j1pos e1pos hp j0le parR q1]])

text \<open>§8.5 (E.2) — the isolated fact \<open>le0M\<close> is PROVEN from \<open>parR\<close>.  \<open>parR\<close> gives
  \<open>leR M 0 j\<^sub>0 (Lng M-1)\<close> (\<open>j\<^sub>0\<close> reaches the last column); by @{thm [source]
  m_5_1_ancestor_tree_1} (reaching \<open>j\<^sub>1\<close> implies reaching every \<open>j \<in> [j\<^sub>0, j\<^sub>1]\<close>),
  \<open>j\<^sub>0\<close> reaches the second-to-last column \<open>Lng M-2\<close> too.  So \<open>le0M\<close> needs no separate
  condV input — only \<open>M \<in> T\<^bsub>PS\<^esub>\<close> (free in the §8.5 regime) and \<open>parR\<close>.\<close>

lemma m_8_5_le0M_of_parR:
  fixes M :: pairseq
  assumes MT: "M \<in> T_PS"
    and j1pos: "Lng M - 1 > 0"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
  shows "le0 M (parent M 1 (Lng M - 1)) (Lng M - 2)"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"
  have rt: "(nextrel0 M)\<^sup>*\<^sup>* ?j0 (Lng M - 1)" using parR by (rule r_into_rtranclp)
  have bnds: "?j0 < Lng M \<and> Lng M - 1 < Lng M" using parR by (simp add: nextrel0_def)
  have parR_le0: "leR M 0 ?j0 (Lng M - 1)" using rt bnds by (simp add: leR_def le0_def)
  have j0lt: "?j0 < Lng M - 1" using parR by (simp add: nextrel0_def)
  have j0le2: "?j0 \<le> Lng M - 2" using j0lt j1pos by linarith
  have LM2le: "Lng M - 2 \<le> Lng M - 1" by simp
  have "leR M 0 ?j0 (Lng M - 2)"
    by (rule m_5_1_ancestor_tree_1[OF MT parR_le0 j0le2 LM2le])
  thus ?thesis by (simp add: leR_def)
qed

text \<open>§8.5 (E.2) FACT 1 (self-contained) — \<open>Pcut(slice) = Lng B\<close> with \<open>le0M\<close> discharged
  from \<open>parR\<close> (@{thm [source] m_8_5_le0M_of_parR}).  Now the surgC GEOMETRY residual
  \<open>Pcut(Y\<frown>B) = Lng B\<close> needs ONLY \<open>M \<in> T\<^bsub>PS\<^esub>\<close> + the committed condV fact \<open>parR\<close>
  (+ the standard genform setup) — NO extra isolated input.\<close>

lemma m_8_5_Pcut_append_T:
  fixes M :: pairseq and q :: nat
  assumes MT: "M \<in> T_PS"
    and j1pos: "Lng M - 1 > 0"
    and e1pos: "entry M 1 (Lng M - 1) > 0"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j0le: "parent M 1 (Lng M - 1) \<le> Lng M"
    and parR: "nextrel0 M (parent M 1 (Lng M - 1)) (Lng M - 1)"
    and q1: "1 \<le> q"
  shows "Pcut (drop (parent M 1 (Lng M - 1)) (M[Suc q]))
       = Lng M - 1 - parent M 1 (Lng M - 1)"
proof -
  have le0M: "le0 M (parent M 1 (Lng M - 1)) (Lng M - 2)"
    by (rule m_8_5_le0M_of_parR[OF MT j1pos parR])
  show ?thesis by (rule m_8_5_Pcut_append[OF j1pos e1pos hp j0le parR le0M q1])
qed

text \<open>§8.5 (E.2) FACT-2 piece 1 — the per-column Trans recurrence as an explicit
  scb-SUBSTITUTION.  From the GREEN, surgC-independent §7.4 @{thm [source]
  m_7_4_Trans_Mark_Pred} (\<open>Trans M\<close> and \<open>Trans (Pred M)\<close> share an scb-context, with the
  Mark-components \<open>Mark M m\<close>/\<open>Mark (Pred M) m\<close> at the centre): \<open>Trans M\<close> is obtained from
  \<open>Trans (Pred M)\<close> by substituting \<open>Mark (Pred M) m \<mapsto> Mark M m\<close> (@{thm [source]
  scbSubst_eq} + @{thm [source] unflatBT_flat}).  This is the per-column step of the
  FACT-2 spine-descent; NON-circular (no step2/surgC).\<close>

lemma m_8_5_Trans_scbSubst_Pred:
  fixes M :: pairseq and m :: nat
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mlt: "m < Lng M - 1"
    and tne: "Trans (Pred M) \<noteq> Trm []"
  shows "Trans M = scbSubst (Mark (Pred M) m) (Mark M m) (Trans (Pred M))"
proof -
  have "\<exists>sb. scb_decomp (Trans (Pred M)) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)
           \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
    using m_7_4_Trans_Mark_Pred[OF mM MR mlt] by (rule ex1_implies_ex)
  then obtain sb
    where dP: "scb_decomp (Trans (Pred M)) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)"
      and dM: "scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)" by blast
  have e1: "scbSubst (Mark (Pred M) m) (Mark M m) (Trans (Pred M))
              = unflatBT (fst sb @ flatBT (Mark M m) @ snd sb)"
    by (rule scbSubst_eq[OF dP tne])
  have flatM: "flatBT (Trans M) = fst sb @ flatBT (Mark M m) @ snd sb"
    using dM by (simp add: scb_decomp_def)
  have e2: "unflatBT (fst sb @ flatBT (Mark M m) @ snd sb) = Trans M"
    using flatM unflatBT_flat[of "Trans M"] by simp
  show ?thesis using e1 e2 by simp
qed

text \<open>§8.7 main result ASSEMBLY (article 6122): \<open>M \<in> ST\<^bsub>PS\<^esub> \<Longrightarrow> Trans M \<in> OT\<^bsub>B\<^esub>\<close>,
  by STRONG induction on \<open>Lng M\<close>, modulo two CLEAN named hypotheses.  This wires the
  full induction skeleton and threads the parallel-in-progress residuals as inputs,
  so the §8.7 OT residual is made concrete and INDEPENDENT of the specific
  R2-tail/R3 proofs.

  The \<open>Pred\<close>-recursion gives \<open>Lng (Pred M) = Lng M - 1 < Lng M\<close> (\<open>Pred M = butlast M\<close>
  for \<open>Lng M > 1\<close>) and \<open>Pred M \<in> ST\<^bsub>PS\<^esub>\<close> (@{thm [source] m_8_7_Pred_ST_PS}), so the
  strong-\<open>Lng\<close> IH supplies \<open>Trans (Pred M) \<in> OT\<^bsub>B\<^esub>\<close> at every step.  The case split is:
  \<^item> \<open>monoT M \<and> Br M \<noteq> [] \<and> Lng M - 1 > 1\<close> — the keystone Pred-recursion step
    @{thm [source] m_8_7_Trans_OT_step_keystone}.  Its only open input is the
    packaged residual \<open>resid\<close> (the R2 descP head-step + the R3 [Buc1] OT2 surface),
    exposed here VERBATIM as the named hypothesis \<open>resid\<close> universally quantified over
    \<open>M\<close> with the keystone preconditions baked in.
  \<^item> otherwise — the clean-leaf / base / multiT branches, threaded as the clean named
    hypothesis \<open>nonkey\<close> (base diagonals @{thm [source] m_8_7_Trans_preserves_OT_base},
    the \<open>cnst\<close>/\<open>rcseq\<close> clean leaves @{thm [source] m_8_7_Trans_cnst_OT} /
    @{thm [source] m_8_7_Trans_rcseq_OT}, and the multiT split), with the strong-\<open>Lng\<close>
    IH supplied to it as a local hypothesis.

  Closing the two hypotheses (\<open>resid\<close> = R2 tail + R3; \<open>nonkey\<close> = the non-keystone
  branch coverage) discharges the §8.7 paper goal \<open>p_8_7_Trans_preserves_OT\<close>.\<close>

lemma m_8_7_Trans_preserves_OT:
  fixes M :: pairseq
  assumes resid:
    "\<And>M x q ps r.
        M \<in> ST_PS \<Longrightarrow> monoT M \<Longrightarrow> Br M \<noteq> [] \<Longrightarrow> Lng M - 1 > 1 \<Longrightarrow>
        Trans (Pred M) = Dpt (enat (entry M 1 0)) (Trm ps +\<^sub>B r) \<Longrightarrow>
        Trans M = Dpt (enat (entry M 1 0)) (Trm ps +\<^sub>B Dpt (enat x) q) \<Longrightarrow>
        isOT_BP (DB (enat x) q)
        \<and> (ps \<noteq> [] \<longrightarrow> leBT (Dpt (enat x) q) (Trm [last ps]))
        \<and> (\<forall>y\<in>GBT (enat (entry M 1 0)) (Trm ps +\<^sub>B Dpt (enat x) q).
               lessBT y (Trm ps +\<^sub>B Dpt (enat x) q))"
  assumes nonkey:
    "\<And>N. N \<in> ST_PS \<Longrightarrow> \<not> (monoT N \<and> Br N \<noteq> [] \<and> Lng N - 1 > 1) \<Longrightarrow>
        (\<And>N'. N' \<in> ST_PS \<Longrightarrow> Lng N' < Lng N \<Longrightarrow> Trans N' \<in> OT_B) \<Longrightarrow>
        Trans N \<in> OT_B"
  shows "M \<in> ST_PS \<Longrightarrow> Trans M \<in> OT_B"
proof (induction "Lng M" arbitrary: M rule: less_induct)
  case (less M)
  have IH: "\<And>M'. M' \<in> ST_PS \<Longrightarrow> Lng M' < Lng M \<Longrightarrow> Trans M' \<in> OT_B"
    using less.hyps by blast
  show ?case
  proof (cases "monoT M \<and> Br M \<noteq> [] \<and> Lng M - 1 > 1")
    case True
    have Mmono: "monoT M" and Brne: "Br M \<noteq> []" and j1gt: "Lng M - 1 > 1"
      using True by auto
    have L: "1 < Lng M" using j1gt by simp
    have predST: "Pred M \<in> ST_PS" by (rule m_8_7_Pred_ST_PS[OF less.prems L])
    have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
    have LP: "Lng (Pred M) < Lng M" using pb L by simp
    have ihOT: "Trans (Pred M) \<in> OT_B" by (rule IH[OF predST LP])
    show ?thesis
      by (rule m_8_7_Trans_OT_step_keystone[OF less.prems Mmono Brne j1gt ihOT
              resid[OF less.prems Mmono Brne j1gt]])
  next
    case False
    show ?thesis
    proof (rule nonkey[OF less.prems False])
      fix N' assume "N' \<in> ST_PS" and "Lng N' < Lng M"
      thus "Trans N' \<in> OT_B" by (rule IH)
    qed
  qed
qed

text \<open>§8.5 (E.2) FACT-2 piece 2a — scbSubst commutes with a \<open>Dpt\<close>-prefix.  The marked-core
  substitution pushes through a head \<open>D\<^bsub>e\<^esub>\<close>: \<open>scbSubst c\<^sub>1 c\<^sub>2 (D\<^bsub>e\<^esub> body) = D\<^bsub>e\<^esub> (scbSubst c\<^sub>1 c\<^sub>2 body)\<close>
  (\<open>c\<^sub>1\<close> the scb-core of \<open>body\<close>, \<open>c\<^sub>2\<close> a principal string).  From the scb-decomp lift through
  the head (\<open>flat (D\<^bsub>e\<^esub> body) = D\<^bsub>e\<^esub> # flat body\<close>) + @{thm [source] scbimg_image_BT} (image
  closure, arbitrary core) + @{thm [source] scbSubst_eq} + @{thm [source] unflatBT_flat}.
  The head-level companion of @{thm [source] m_8_5_scbSubst_addBT_commute}; used to push
  scbSubst through the spine for the FACT-2 spine action.\<close>

lemma m_8_5_scbSubst_Dpt:
  fixes c1 c2 body :: BT and e :: enat and s b :: "Sym list"
  assumes d: "scb_decomp body s (flatBT c1) b"
    and bne: "body \<noteq> Trm []"
    and c2p: "isPTB_str (flatBT c2)"
  shows "scbSubst c1 c2 (Dpt e body) = Dpt e (scbSubst c1 c2 body)"
proof -
  have flatb: "flatBT body = s @ flatBT c1 @ b" using d by (simp add: scb_decomp_def)
  have ptc1: "isPTB_str (flatBT c1)" using d bne by (simp add: scb_decomp_def)
  have rb: "\<forall>x\<in>set b. x = RP" using d by (simp add: scb_decomp_def)
  have flatDe: "flatBT (Dpt e body) = Dsym e # flatBT body" by simp
  have Dene: "Dpt e body \<noteq> Trm []" by simp
  have dDe: "scb_decomp (Dpt e body) (Dsym e # s) (flatBT c1) b"
    unfolding scb_decomp_def using flatDe flatb ptc1 rb by simp
  have e1: "scbSubst c1 c2 (Dpt e body) = unflatBT ((Dsym e # s) @ flatBT c2 @ b)"
    by (rule scbSubst_eq[OF dDe Dene])
  have e2: "scbSubst c1 c2 body = unflatBT (s @ flatBT c2 @ b)"
    by (rule scbSubst_eq[OF d bne])
  obtain p1 where p1: "flatBT c1 = flatBP p1" using ptc1 by (auto simp: isPTB_str_def)
  obtain p2 where p2: "flatBT c2 = flatBP p2" using c2p by (auto simp: isPTB_str_def)
  have fbody: "flatBT body = s @ flatBP p1 @ b" using flatb p1 by simp
  obtain t' where t': "flatBT t' = s @ flatBP p2 @ b"
    using scbimg_image_BT[OF fbody rb] by blast
  have img: "s @ flatBT c2 @ b = flatBT t'" using t' p2 by simp
  have lhs: "scbSubst c1 c2 (Dpt e body) = Dpt e t'"
  proof -
    have "scbSubst c1 c2 (Dpt e body) = unflatBT (Dsym e # (s @ flatBT c2 @ b))"
      using e1 by simp
    also have "\<dots> = unflatBT (Dsym e # flatBT t')" using img by simp
    also have "\<dots> = unflatBT (flatBT (Dpt e t'))" by simp
    also have "\<dots> = Dpt e t'" by (rule unflatBT_flat)
    finally show ?thesis .
  qed
  have rhs: "Dpt e (scbSubst c1 c2 body) = Dpt e t'"
  proof -
    have "scbSubst c1 c2 body = unflatBT (flatBT t')" using e2 img by simp
    also have "\<dots> = t'" by (rule unflatBT_flat)
    finally show ?thesis by simp
  qed
  show ?thesis using lhs rhs by simp
qed

text \<open>§8.5 (E.2) FACT-2 piece 2b — \<open>spineLeaf\<close> COMMUTES with scbSubst (deep core).  For a
  spine-form term \<open>t = D\<^bsub>e\<^esub>(pre +\<^sub>B D\<^bsub>h\<^esub> x)\<close> whose marked-core \<open>c\<^sub>1\<close> lies in the deep slot \<open>x\<close>:
  \<open>spineLeaf (scbSubst c\<^sub>1 c\<^sub>2 t) = scbSubst c\<^sub>1 c\<^sub>2 (spineLeaf t)\<close>.  Push scbSubst through the head
  (@{thm [source] m_8_5_scbSubst_Dpt}) then the \<open>+\<^sub>B\<close>-spine
  (@{thm [source] m_8_5_scbSubst_addBT_commute}), then read off the deep slot
  (@{thm [source] m_8_5_spineLeaf_Dpt_addBT}).  This is the per-step spine action for the
  FACT-2 netfold; NON-circular.\<close>

lemma m_8_5_spineLeaf_scbSubst:
  fixes pre x c1 c2 :: BT and e h :: nat and sx bx :: "Sym list"
  assumes dx: "scb_decomp x sx (flatBT c1) bx"
    and xnz: "x \<noteq> Trm []"
    and c2p: "isPTB_str (flatBT c2)"
    and prene: "untrm pre \<noteq> []"
  shows "spineLeaf (scbSubst c1 c2 (Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)))
       = scbSubst c1 c2 (spineLeaf (Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)))"
proof -
  let ?BODY = "pre +\<^sub>B Dpt (enat h) x"
  have flatx: "flatBT x = sx @ flatBT c1 @ bx" using dx by (simp add: scb_decomp_def)
  have ptc1: "isPTB_str (flatBT c1)" using dx xnz by (simp add: scb_decomp_def)
  have rbx: "\<forall>z\<in>set bx. z = RP" using dx by (simp add: scb_decomp_def)
  have scbDhx: "scb_decomp (Dpt (enat h) x) (Dsym (enat h) # sx) (flatBT c1) bx"
    unfolding scb_decomp_def using flatx ptc1 rbx by simp
  have dh1: "length (untrm (Dpt (enat h) x)) = 1" by simp
  have dBODY: "scb_decomp ?BODY (liftS pre (Dsym (enat h) # sx)) (flatBT c1) (bx @ [RP])"
    by (rule scb_addBT_left[OF scbDhx dh1 prene])
  have BODYne: "?BODY \<noteq> Trm []" using prene by (cases pre) auto
  have push: "scbSubst c1 c2 (Dpt (enat e) ?BODY)
                = Dpt (enat e) (pre +\<^sub>B Dpt (enat h) (scbSubst c1 c2 x))"
  proof -
    have "scbSubst c1 c2 (Dpt (enat e) ?BODY) = Dpt (enat e) (scbSubst c1 c2 ?BODY)"
      by (rule m_8_5_scbSubst_Dpt[OF dBODY BODYne c2p])
    also have "scbSubst c1 c2 ?BODY = pre +\<^sub>B Dpt (enat h) (scbSubst c1 c2 x)"
      by (rule m_8_5_scbSubst_addBT_commute[OF dx xnz c2p prene])
    finally show ?thesis .
  qed
  have sl_t: "spineLeaf (Dpt (enat e) ?BODY) = x" by (rule m_8_5_spineLeaf_Dpt_addBT)
  have sl_push: "spineLeaf (scbSubst c1 c2 (Dpt (enat e) ?BODY)) = scbSubst c1 c2 x"
    using push by (simp add: m_8_5_spineLeaf_Dpt_addBT)
  show ?thesis using sl_push sl_t by simp
qed

text \<open>§8.5 (E.2) FACT-2 piece 3a — \<open>spineLeaf\<close> COMMUTES with the whole netfold.  Generic
  fold-commute backbone: if every fold operator commutes with \<open>spineLeaf\<close> on the maintained
  invariant \<open>P\<close> (the per-step @{thm [source] m_8_5_spineLeaf_scbSubst}) and \<open>P\<close> is preserved by
  each step, then \<open>spineLeaf\<close> pushes through the entire fold:
  \<open>spineLeaf (fold op ms acc) = fold op ms (spineLeaf acc)\<close>.  Pure structural induction on the
  fold list; NON-circular.  Instantiating \<open>op\<close> with the netfold's per-column scbSubst and \<open>P\<close>
  with the spine-form/deep-core invariant turns @{thm [source] m_8_5_scbSubst_netfold} into
  \<open>spineLeaf (Trans (Y@B)) = fold op [0..<Lng B] (spineLeaf (Trans Y))\<close> — reducing FACT 2 to the
  single fold-value identity (the period's scbSubsts net to one C-graft).\<close>

lemma m_8_5_spineLeaf_fold:
  fixes op :: "nat \<Rightarrow> BT \<Rightarrow> BT" and P :: "BT \<Rightarrow> bool" and ms :: "nat list" and acc :: BT
  assumes step: "\<And>m t. P t \<Longrightarrow> spineLeaf (op m t) = op m (spineLeaf t)"
    and inv: "\<And>m t. P t \<Longrightarrow> P (op m t)"
    and Pacc: "P acc"
  shows "spineLeaf (fold op ms acc) = fold op ms (spineLeaf acc)"
  using Pacc
proof (induction ms arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons m ms)
  have Pm: "P (op m acc)" by (rule inv[OF Cons.prems])
  have "spineLeaf (fold op (m # ms) acc) = spineLeaf (fold op ms (op m acc))" by simp
  also have "\<dots> = fold op ms (spineLeaf (op m acc))" by (rule Cons.IH[OF Pm])
  also have "\<dots> = fold op ms (op m (spineLeaf acc))" using step[OF Cons.prems] by simp
  also have "\<dots> = fold op (m # ms) (spineLeaf acc)" by simp
  finally show ?case .
qed



text \<open>§8.7 R2 equal-head tail — ORDER ENGINE.  \<open>Trans\<close> is weakly monotone along the
  \<open>take\<close>-prefix chain: a (non-empty) initial slice has \<open>Trans\<close> weakly below
  \<open>Trans M\<close>.  This is the \<open>\<le>\<close>-closure of the strict @{thm [source] Trans_take_lessBT}
  (which iterates @{thm [source] m_7_3_Pred_Trans_descend}); the \<open>n = Lng M\<close> case is
  reflexive (\<open>take (Lng M) M = M\<close>).  (\<open>leBT\<close> is an abbreviation for
  \<open>lessBT \<dots> \<or> \<dots> = \<dots>\<close>, so the disjuncts are exposed without an unfolding.)\<close>

lemma Trans_take_leBT:
  assumes M: "M \<in> RT_PS" and npos: "0 < n" and nle: "n \<le> Lng M"
  shows "leBT (Trans (take n M)) (Trans M)"
proof (cases "n < Lng M")
  case True
  have "lessBT (Trans (take n M)) (Trans M)" by (rule Trans_take_lessBT[OF M npos True])
  thus ?thesis by blast
next
  case False
  hence "n = Lng M" using nle by linarith
  hence "take n M = M" by (simp add: take_all)
  thus ?thesis by simp
qed

text \<open>§8.7 R2 equal-head tail — ORDER CORE.  The keystone equal-head \<open>tail\<close>
  obligation \<open>leBT q q\<^sub>b\<close> (the residual of @{thm [source] m_8_7_dstep_wholebody} /
  @{thm [source] m_8_7_dstep_properprefix_reduce}) is, after identifying the two
  trailing equal-head principals of \<open>Trans M\<close>'s body as the \<open>Trans\<close>-images of the
  consecutive branches, exactly the \<open>leBT\<close>-descent of those branch \<open>Trans\<close>-heads.
  EMPIRICALLY (python \<open>_r2_mark_bridge.py\<close>, \<open>_r2_eqhead_deep.py\<close>: 0 fail / 37+
  equal-head \<open>ST\<^bsub>PS\<^esub>\<close> samples): with \<open>A = Br M ! J\<^sub>1\<close> the last branch and
  \<open>B = Br M ! (J\<^sub>1-1)\<close> the previous one,
  \<^item> \<open>q = bpHeadT (Trans A)\<close>, \<open>q\<^sub>b = bpHeadT (Trans B)\<close> (the branch \<open>Trans\<close>-heads,
    both with the SAME outer head \<open>x\<close>), and
  \<^item> \<open>A\<close> is a prefix (\<open>Pred\<close>-iterate) of \<open>B\<close>  (\<open>B = A \<frown> C\<close>).
  This lemma is the order CORE: from \<open>B \<in> RT\<^bsub>PS\<^esub>\<close>, the prefix relation \<open>B = A \<frown> C\<close>,
  and the two single-principal branch \<open>Trans\<close> read-offs \<open>Trans A = D\<^bsub>x\<^esub> q\<close>,
  \<open>Trans B = D\<^bsub>x\<^esub> q\<^sub>b\<close>, the strict take-descent @{thm [source] Trans_take_lessBT}
  (or reflexivity when \<open>C = []\<close>) yields \<open>leBT (Trans A) (Trans B)\<close>, and the shared
  head \<open>x\<close> strips off (@{thm [source] lessBT_Dpt_same}) to give \<open>leBT q q\<^sub>b\<close>.  The
  remaining inputs are PURELY structural §6/§7 facts (the branch \<open>Trans\<close> read-off and
  the prefix-nesting of consecutive equal-head branches), NOT any \<open>leBT\<close>/value
  reasoning.\<close>

lemma m_8_7_eqhead_tail_from_branch_prefix:
  fixes A B C :: pairseq and x :: nat and q qb :: BT
  assumes BR: "B \<in> RT_PS"
    and Apos: "0 < Lng A"
    and Bsplit: "B = A @ C"
    and qA: "Trans A = Dpt (enat x) q"
    and qbB: "Trans B = Dpt (enat x) qb"
  shows "leBT q qb"
proof -
  have transle: "leBT (Trans A) (Trans B)"
  proof (cases "C = []")
    case True
    hence "B = A" using Bsplit by simp
    thus ?thesis by simp
  next
    case False
    hence cpos: "0 < Lng C" by (cases C) auto
    have ALB: "Lng A < Lng B" using Bsplit cpos by simp
    have takeA: "take (Lng A) B = A" using Bsplit by simp
    have "lessBT (Trans (take (Lng A) B)) (Trans B)"
      by (rule Trans_take_lessBT[OF BR Apos ALB])
    hence "lessBT (Trans A) (Trans B)" using takeA by simp
    thus ?thesis by blast
  qed
  have hstrip: "leBT (Dpt (enat x) q) (Dpt (enat x) qb)" using transle qA qbB by simp
  show "leBT q qb" using hstrip by simp
qed


lemma descP_tl: "descP (x # xs) \<Longrightarrow> descP xs"
  by (cases xs) auto

lemma descP_Cons_hd_le:
  "descP (x # xs) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> leBT (Trm [hd xs]) (Trm [x])"
  by (cases xs) auto

lemma descP_append:
  "descP as \<Longrightarrow> descP bs \<Longrightarrow>
   (as \<noteq> [] \<longrightarrow> bs \<noteq> [] \<longrightarrow> leBT (Trm [hd bs]) (Trm [last as])) \<Longrightarrow> descP (as @ bs)"
proof (induction bs arbitrary: as)
  case Nil thus ?case by simp
next
  case (Cons b bs')
  have dab: "descP (as @ [b])"
  proof (rule descP_snoc[OF Cons.prems(1)])
    show "as \<noteq> [] \<longrightarrow> leBT (Trm [b]) (Trm [last as])" using Cons.prems(3) by simp
  qed
  have dbs': "descP bs'" using descP_tl[OF Cons.prems(2)] .
  have junc: "as @ [b] \<noteq> [] \<longrightarrow> bs' \<noteq> [] \<longrightarrow> leBT (Trm [hd bs']) (Trm [last (as @ [b])])"
  proof (intro impI)
    assume "bs' \<noteq> []"
    have "leBT (Trm [hd bs']) (Trm [b])"
      using descP_Cons_hd_le[OF Cons.prems(2) \<open>bs' \<noteq> []\<close>] .
    thus "leBT (Trm [hd bs']) (Trm [last (as @ [b])])" by simp
  qed
  have "descP ((as @ [b]) @ bs')" by (rule Cons.IH[OF dab dbs' junc])
  thus ?case by simp
qed

text \<open>Full multiT \<open>Trans\<close> split (both \<open>P\<close>-tail branches), the if-form of
  @{thm [source] trans_multi_split} extracted from @{thm [source] m_7_3_Trans_monoT}'s
  inline computation: when the last \<open>P\<close>-component is \<open>[(0,0)]\<close> the appended block is
  \<open>D\<^sub>0 0\<close>, else it is \<open>Trans (drop (Pcut K) K)\<close>.\<close>

lemma trans_multi_split_full:
  fixes K :: pairseq
  assumes KR: "K \<in> RT_PS" and mu: "multiT K"
  shows "Trans K = (if drop (Pcut K) K = [(0,0)]
                    then Trans (take (Pcut K) K) +\<^sub>B Dpt 0 0\<^sub>B
                    else Trans (take (Pcut K) K) +\<^sub>B Trans (drop (Pcut K) K))"
proof -
  have KT: "K \<in> T_PS" using KR by (simp add: RT_PS_def)
  have L: "1 < Lng K" by (rule multiT_imp_Lng_gt1[OF KT mu])
  have nmono: "\<not> monoT K" using mu by (simp add: multiT_def)
  have domT: "Trans_Mark_dom (Inl K)" by (rule m_7_3_Trans_welldef[OF KR])
  let ?A = "take (Pcut K) K"  let ?PJ = "drop (Pcut K) K"
  have cut: "0 < Pcut K \<and> Pcut K \<le> Lng K - 1" using Pcut_le[OF L] by simp
  have PJeq: "P K ! (Lng (P K) - 1) = ?PJ"
    by (rule trans_multiT_last_component(1)[OF KT mu])
  have Aeq2: "seg K 0 (Lng K - 1 - Lng ?PJ + 1 - 1) = ?A"
  proof -
    have LdJ: "Lng ?PJ = Lng K - Pcut K" by simp
    have "Lng K - 1 - Lng ?PJ + 1 - 1 = Pcut K - 1" using LdJ cut by linarith
    moreover have "seg K 0 (Pcut K - 1) = take (Suc (Pcut K - 1)) K"
      by (rule seg_0_eq_take) (use cut L in linarith)
    moreover have "Suc (Pcut K - 1) = Pcut K" using cut by simp
    ultimately show ?thesis by simp
  qed
  have c1f: "(K \<notin> RT_PS) = False" using KR by simp
  have c2f: "(Lng K - 1 = 0) = False" using L by simp
  have c3f: "monoT K = False" using nmono by simp
  have raw: "Trans K =
      (if P K ! (Lng (P K) - 1) = [(0, 0)]
       then Trans (seg K 0 (Lng K - 1 - Lng (P K ! (Lng (P K) - 1)) + 1 - 1))
              +\<^sub>B Dpt 0 0\<^sub>B
       else Trans (seg K 0 (Lng K - 1 - Lng (P K ! (Lng (P K) - 1)) + 1 - 1))
              +\<^sub>B Trans (P K ! (Lng (P K) - 1)))"
    by (subst Trans.psimps[OF domT]) (simp only: c1f c2f c3f if_False Let_def)
  show "Trans K = (if ?PJ = [(0,0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B else Trans ?A +\<^sub>B Trans ?PJ)"
    unfolding raw PJeq Aeq2 ..
qed

text \<open>§8.7 NON-keystone OT branch (the \<open>nonkey\<close> hypothesis of
  @{thm [source] m_8_7_Trans_preserves_OT}), reduced.  For \<open>N \<in> ST\<^bsub>PS\<^esub>\<close> that is NOT a
  keystone (\<open>\<not>(monoT N \<and> Br N \<noteq> [] \<and> Lng N - 1 > 1)\<close>):
  \<^item> \<open>zeroT N\<close> \<Rightarrow> \<open>Trans N = 0\<^sub>B \<in> OT\<^bsub>B\<^esub>\<close> (GREEN, @{thm [source] m_7_3_Trans_zeroT}).
  \<^item> \<open>monoT N\<close>, \<open>Lng N \<le> 2\<close> \<Rightarrow> GREEN: singleton \<open>D\<^sub>v 0\<close> (@{thm [source] m_8_7_OT_ex1})
    or two-column \<open>D\<^sub>a D\<^sub>b 0\<close> (@{thm [source] m_7_3_twoColumn_Trans} +
    @{thm [source] m_8_7_OT_ex2}).
  \<^item> \<open>monoT N\<close>, \<open>Br N = []\<close> (all-trunk) \<Rightarrow> GREEN: the trunk is a diagonal
    (@{thm [source] baseU_alltrunk_diag_entry}), so \<open>N = diagSeq u v\<close> by extensionality
    and @{thm [source] m_8_7_Trans_preserves_OT_base} applies (\<open>S\<^sub>0T\<^bsub>PS\<^esub>\<close> base).
  \<^item> \<open>multiT N\<close> \<Rightarrow> the substantive case: GREEN block-recursion via
    @{thm [source] trans_multi_split_full}.  Both blocks \<open>take (Pcut N) N\<close>
    (@{thm [source] m_6_7_standard_prefix}) and \<open>drop (Pcut N) N\<close>
    (@{thm [source] m_6_7_standard_P_components}) are in \<open>ST\<^bsub>PS\<^esub>\<close> with \<open>Lng < Lng N\<close>,
    so the strong-\<open>Lng\<close> IH gives \<open>isOT_BT\<close> for each; \<open>descP\<close> of the concatenation then
    needs ONLY the junction descent (named residual \<open>multiD\<close>) — the multiT analog of
    the keystone R2.  When the last block is \<open>[(0,0)]\<close> the junction is FREE
    (\<open>D\<^sub>0 0\<close> is \<open>\<le>\<close>-minimal, @{thm [source] leBT_Dpt0_iff}).\<close>

lemma m_8_7_Trans_OT_nonkey:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and nk: "\<not> (monoT N \<and> Br N \<noteq> [] \<and> Lng N - 1 > 1)"
    and IH: "\<And>N'. N' \<in> ST_PS \<Longrightarrow> Lng N' < Lng N \<Longrightarrow> Trans N' \<in> OT_B"
    and multiD: "\<And>as bs. multiT N \<Longrightarrow> drop (Pcut N) N \<noteq> [(0,0)] \<Longrightarrow>
        Trans (take (Pcut N) N) = Trm as \<Longrightarrow> Trans (drop (Pcut N) N) = Trm bs \<Longrightarrow>
        as \<noteq> [] \<Longrightarrow> bs \<noteq> [] \<Longrightarrow> leBT (Trm [hd bs]) (Trm [last as])"
  shows "Trans N \<in> OT_B"
proof -
  have NR: "N \<in> RT_PS" using N m_6_7_ST_PS_subseteq_RT_PS by blast
  have NT: "N \<in> T_PS" using NR by (simp add: RT_PS_def)
  show ?thesis
  proof (cases "zeroT N")
    case True
    hence "Trans N = 0\<^sub>B" using m_7_3_Trans_zeroT[OF NR] by simp
    thus ?thesis using m_8_7_OT_zero by simp
  next
    case nzT: False
    show ?thesis
    proof (cases "monoT N")
      case mono: True
      have disj: "Br N = [] \<or> Lng N \<le> 2"
      proof (cases "Br N = []")
        case True thus ?thesis by simp
      next
        case False
        with nk mono have "\<not> 1 < Lng N - 1" by blast
        hence "Lng N \<le> 2" by linarith
        thus ?thesis by simp
      qed
      show ?thesis
      proof (cases "Lng N \<le> 2")
        case small: True
        have L1: "1 \<le> Lng N" using NT by (cases N) (auto simp: T_PS_def)
        show ?thesis
        proof (cases "Lng N = 1")
          case True
          obtain v where Nv: "N = [(v, v)]"
            using m_6_6_oneColumn[OF NT] NR True by auto
          have vpos: "v \<noteq> 0"
          proof -
            have "entry N 1 0 \<noteq> 0" using nzT True by (simp add: zeroT_def)
            thus ?thesis using Nv by (simp add: entry_def)
          qed
          have "Trans N = Dpt (enat v) 0\<^sub>B" using Nv Trans_singleton vpos by simp
          thus ?thesis using m_8_7_OT_ex1 by simp
        next
          case False
          hence L2: "Lng N = 2" using small L1 by linarith
          have "Trans N = Dpt (enat (entry N 1 0)) (Dpt (enat (entry N 1 1)) 0\<^sub>B)"
            by (rule m_7_3_twoColumn_Trans[OF NR mono L2])
          thus ?thesis using m_8_7_OT_ex2 by simp
        qed
      next
        case False
        hence brE: "Br N = []" using disj by simp
        have lgt: "Lng N - 1 > 1" using False by linarith
        have L1: "1 \<le> Lng N" using lgt by linarith
        \<comment> \<open>all-trunk \<open>\<Longrightarrow>\<close> diagonal \<open>\<Longrightarrow>\<close> base (article 6133)\<close>
        have tr: "TrMax N = Lng N - 1" by (rule baseU_Br_empty_TrMax[OF brE])
        define u where "u = entry N 1 0"
        define v where "v = u + (Lng N - 1)"
        have SucV: "Suc v - u = Lng N"
        proof -
          have "Suc v - u = Suc (Lng N - 1)" unfolding v_def by simp
          thus ?thesis using L1 by simp
        qed
        have Neq: "N = diagSeq u v"
        proof (rule nth_equalityI)
          show "length N = length (diagSeq u v)" using SucV by simp
        next
          fix j assume "j < length N"
          hence jL: "j < Lng N" by simp
          have e: "entry N 0 j = u + j \<and> entry N 1 j = u + j"
            unfolding u_def by (rule baseU_alltrunk_diag_entry[OF NR mono tr jL])
          have "fst (N ! j) = u + j" using e by (simp add: entry_def)
          moreover have "snd (N ! j) = u + j" using e by (simp add: entry_def)
          ultimately have "N ! j = (u + j, u + j)" by (simp add: prod_eq_iff)
          moreover have dj: "j < Suc v - u" using jL SucV by simp
          ultimately show "N ! j = diagSeq u v ! j" using diagSeq_nth[OF dj] by simp
        qed
        have inSk: "N \<in> SkT_PS 0"
        proof -
          have uv: "u \<le> v" unfolding v_def by simp
          have "\<exists>a b. N = diagSeq a b \<and> a \<le> b" using Neq uv by blast
          thus ?thesis by simp
        qed
        show ?thesis by (rule m_8_7_Trans_preserves_OT_base[OF inSk])
      qed
    next
      case False
      have mu: "multiT N" using nzT False by (simp add: multiT_def)
      have L: "1 < Lng N" by (rule multiT_imp_Lng_gt1[OF NT mu])
      have cut: "0 < Pcut N \<and> Pcut N \<le> Lng N - 1" using Pcut_le[OF L] by simp
      \<comment> \<open>both blocks are standard, with strictly smaller \<open>Lng\<close>\<close>
      have Aeq: "take (Pcut N) N = seg N 0 (Pcut N - 1)"
      proof -
        have "seg N 0 (Pcut N - 1) = take (Suc (Pcut N - 1)) N"
          by (rule seg_0_eq_take) (use cut L in linarith)
        thus ?thesis using cut by simp
      qed
      have A_ST: "take (Pcut N) N \<in> ST_PS"
        unfolding Aeq by (rule m_6_7_standard_prefix[OF N]) (use cut in linarith)
      have LA: "Lng (take (Pcut N) N) < Lng N"
      proof -
        have "Lng (take (Pcut N) N) \<le> Pcut N" by simp
        thus ?thesis using cut L by linarith
      qed
      obtain k where Nk: "N \<in> SkT_PS k" using N m_6_7_ST_eq_Union_SkT by blast
      have Pne: "Lng (P N) - 1 < Lng (P N)" using P_nonempty[of N] by (cases "P N") auto
      have PJcomp: "drop (Pcut N) N = P N ! (Lng (P N) - 1)"
        using trans_multiT_last_component(1)[OF NT mu] by simp
      have PJ_ST: "drop (Pcut N) N \<in> ST_PS"
      proof -
        have "P N ! (Lng (P N) - 1) \<in> SkT_PS k"
          using m_6_7_standard_P_components[OF Nk] Pne by blast
        hence "P N ! (Lng (P N) - 1) \<in> ST_PS"
          using m_6_7_ST_eq_Union_SkT by blast
        thus ?thesis using PJcomp by simp
      qed
      have LPJ: "Lng (drop (Pcut N) N) < Lng N"
      proof -
        have "Lng (drop (Pcut N) N) = Lng N - Pcut N" by simp
        thus ?thesis using cut L by linarith
      qed
      have isA: "isOT_BT (Trans (take (Pcut N) N))"
        using IH[OF A_ST LA] by (simp add: OT_B_def OT_def)
      have isPJ: "isOT_BT (Trans (drop (Pcut N) N))"
        using IH[OF PJ_ST LPJ] by (simp add: OT_B_def OT_def)
      obtain as where as: "Trans (take (Pcut N) N) = Trm as" by (cases "Trans (take (Pcut N) N)")
      have dAs: "descP as" using isA as by simp
      have pAs: "\<forall>p\<in>set as. isOT_BP p" using isA as by simp
      have "isOT_BT (Trans N)"
      proof (cases "drop (Pcut N) N = [(0,0)]")
        case True
        have TN: "Trans N = Trm (as @ [DB 0 0\<^sub>B])"
          using trans_multi_split_full[OF NR mu] True as by simp
        have dsnoc: "descP (as @ [DB 0 0\<^sub>B])"
        proof (rule descP_snoc[OF dAs])
          show "as \<noteq> [] \<longrightarrow> leBT (Trm [DB 0 0\<^sub>B]) (Trm [last as])"
          proof
            assume "as \<noteq> []"
            obtain w c where lc: "last as = DB w c" by (cases "last as")
            have w0: "enat 0 \<le> w" by (cases w) auto
            have le0: "leBT (Dpt (enat 0) 0\<^sub>B) (Dpt w c)"
              using leBT_Dpt0_iff[of 0 w c] w0 by simp
            show "leBT (Trm [DB 0 0\<^sub>B]) (Trm [last as])"
              unfolding lc zero_enat_def by (rule le0)
          qed
        qed
        have "\<forall>p\<in>set (as @ [DB 0 0\<^sub>B]). isOT_BP p" using pAs by simp
        thus ?thesis using TN dsnoc by simp
      next
        case PJnz: False
        obtain bs where bs: "Trans (drop (Pcut N) N) = Trm bs"
          by (cases "Trans (drop (Pcut N) N)")
        have TN: "Trans N = Trm (as @ bs)"
          using trans_multi_split[OF NR mu PJnz] as bs by simp
        have dBs: "descP bs" using isPJ bs by simp
        have pBs: "\<forall>p\<in>set bs. isOT_BP p" using isPJ bs by simp
        have junc: "as \<noteq> [] \<longrightarrow> bs \<noteq> [] \<longrightarrow> leBT (Trm [hd bs]) (Trm [last as])"
        proof (intro impI)
          assume "as \<noteq> []" and "bs \<noteq> []"
          show "leBT (Trm [hd bs]) (Trm [last as])"
            by (rule multiD[OF mu PJnz as bs \<open>as \<noteq> []\<close> \<open>bs \<noteq> []\<close>])
        qed
        have "descP (as @ bs)" by (rule descP_append[OF dAs dBs junc])
        moreover have "\<forall>p\<in>set (as @ bs). isOT_BP p" using pAs pBs by auto
        ultimately show ?thesis using TN by simp
      qed
      thus ?thesis by (rule m_8_7_OT_B_of_isOT_BT[OF N])
    qed
  qed
qed


text \<open>§8.7 OT-preservation, nonkey DISCHARGED — reduces m_8_7_Trans_preserves_OT to
  exactly the two value/junction residuals \<open>resid\<close> (= R3: the keystone newOT/GBT step,
  surgC/FACT2-entangled) and \<open>multiD\<close> (= the multiT junction descent), by plugging the
  non-keystone branch @{thm [source] m_8_7_Trans_OT_nonkey} into the \<open>nonkey\<close> slot.\<close>

lemma m_8_7_Trans_preserves_OT_modulo:
  fixes M :: pairseq
  assumes resid:
    "\<And>M x q ps r.
        M \<in> ST_PS \<Longrightarrow> monoT M \<Longrightarrow> Br M \<noteq> [] \<Longrightarrow> Lng M - 1 > 1 \<Longrightarrow>
        Trans (Pred M) = Dpt (enat (entry M 1 0)) (Trm ps +\<^sub>B r) \<Longrightarrow>
        Trans M = Dpt (enat (entry M 1 0)) (Trm ps +\<^sub>B Dpt (enat x) q) \<Longrightarrow>
        isOT_BP (DB (enat x) q)
        \<and> (ps \<noteq> [] \<longrightarrow> leBT (Dpt (enat x) q) (Trm [last ps]))
        \<and> (\<forall>y\<in>GBT (enat (entry M 1 0)) (Trm ps +\<^sub>B Dpt (enat x) q).
               lessBT y (Trm ps +\<^sub>B Dpt (enat x) q))"
  assumes multiD:
    "\<And>N as bs. N \<in> ST_PS \<Longrightarrow> multiT N \<Longrightarrow> drop (Pcut N) N \<noteq> [(0,0)] \<Longrightarrow>
        Trans (take (Pcut N) N) = Trm as \<Longrightarrow> Trans (drop (Pcut N) N) = Trm bs \<Longrightarrow>
        as \<noteq> [] \<Longrightarrow> bs \<noteq> [] \<Longrightarrow> leBT (Trm [hd bs]) (Trm [last as])"
  assumes MST: "M \<in> ST_PS"
  shows "Trans M \<in> OT_B"
proof -
  have nk: "\<And>N. N \<in> ST_PS \<Longrightarrow> \<not> (monoT N \<and> Br N \<noteq> [] \<and> Lng N - 1 > 1) \<Longrightarrow>
              (\<And>N'. N' \<in> ST_PS \<Longrightarrow> Lng N' < Lng N \<Longrightarrow> Trans N' \<in> OT_B) \<Longrightarrow>
              Trans N \<in> OT_B"
  proof -
    fix N assume a: "N \<in> ST_PS"
      and b: "\<not> (monoT N \<and> Br N \<noteq> [] \<and> Lng N - 1 > 1)"
      and c: "\<And>N'. N' \<in> ST_PS \<Longrightarrow> Lng N' < Lng N \<Longrightarrow> Trans N' \<in> OT_B"
    show "Trans N \<in> OT_B"
      by (rule m_8_7_Trans_OT_nonkey[OF a b c multiD[OF a]])
  qed
  show "Trans M \<in> OT_B"
    by (rule m_8_7_Trans_preserves_OT[OF resid nk MST])
qed


text \<open>§8.5 (E.2) MASTER CAPSTONE (netfold-route, condV-grounded).  Same surgC conclusion as
  the (dead-route) spinelaw wiring but routed through the SLICE-TRUE block identity
  \<open>blockC : spineLeaf (Trans (Y\<frown>B)) = C (spineLeaf (Trans Y))\<close> (appending the condV-deepen
  period \<open>B\<close> applies exactly ONE \<open>C\<close>-graft to the spine leaf) — NOT the intrinsic
  \<open>Pred\<^bsup>Pcut\<^esup>\<close>-spinelaw (which is a FALSE universal off the kernel slice: holds 231/283 over
  reduced terms, the genuine non-degenerate CEX \<open>X=[(0,0),(1,0),(2,1)]\<close> giving \<open>D\<^sub>1\<close> vs \<open>D\<^sub>0\<close>;
  even base-shape gating leaves 29 counterexamples).  \<open>blockC\<close> is reachable WITHOUT any
  intrinsic-spinelaw claim: \<open>Trans (Y\<frown>B) = fold op [0..<Lng B] (Trans Y)\<close> (the GREEN
  condV-grounded @{thm [source] m_8_5_Trans_netfold_condV}), \<open>spineLeaf\<close> pushed through the
  fold by @{thm [source] m_8_5_spineLeaf_fold} (3a), then the per-period fold value
  \<open>fold op [0..<Lng B] (spineLeaf (Trans Y)) = C (spineLeaf (Trans Y))\<close> (3b, the remaining
  keystone value).  Composes @{thm [source] m_8_5_endpoint_of_blockC} (blockC \<Longrightarrow> endpoint, via
  @{thm [source] m_8_5_C_body}) with @{thm [source] m_8_5_surgery_of_geom_endpoint}.  This is
  the CORRECT capstone: surgC \<Longleftarrow> blockC + base-shape + geometry, no false universal.\<close>

lemma m_8_5_surgC_of_blockC:
  fixes Y B :: pairseq and t2 :: BT and e10 vm1 v :: nat
    and s0 b0 :: "Sym list" and C :: "BT \<Rightarrow> BT"
  assumes base: "Trans Y = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (Trans Y)))"
    and gYne: "\<And>m. m < Lng B \<Longrightarrow> 0 < Lng (Y @ take m B)"
    and gMR: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> RT_PS"
    and gMP: "\<And>m. m < Lng B \<Longrightarrow> (Y @ take m B) @ [B ! m] \<in> PT_PS"
    and gBrne: "\<And>m. m < Lng B \<Longrightarrow> Br ((Y @ take m B) @ [B ! m]) \<noteq> []"
    and gj1gt: "\<And>m. m < Lng B \<Longrightarrow> Lng ((Y @ take m B) @ [B ! m]) - 1 > 1"
    and gpar: "\<And>m. m < Lng B \<Longrightarrow> parent ((Y @ take m B) @ [B ! m]) 0
                 (Lng ((Y @ take m B) @ [B ! m]) - 1) > TrMax ((Y @ take m B) @ [B ! m])"
    and ge10: "\<And>m. m < Lng B \<Longrightarrow> entry ((Y @ take m B) @ [B ! m]) 1 0 = e10"
    and Cdef: "C = (\<lambda>x. unflatBT (s0 @ Dsym (enat (v - 1)) # flatBT x @ b0))"
    and prene: "untrm t2 \<noteq> []"
    and s0eq: "s0 = liftS t2 []"
    and b0eq: "b0 = [RP]"
    and vm1eq: "vm1 = v - 1"
    and blockC: "spineLeaf (Trans (Y @ B)) = C (spineLeaf (Trans Y))"
  shows "Trans (Y @ B) = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Y)))"
proof -
  have endpoint: "spineLeaf (Trans (Y @ B)) = bpHeadT (Trans Y)"
    by (rule m_8_5_endpoint_of_blockC[OF base Cdef prene s0eq b0eq vm1eq blockC])
  show ?thesis
    by (rule m_8_5_surgery_of_geom_endpoint
          [OF base gYne gMR gMP gBrne gj1gt gpar ge10 endpoint])
qed


text \<open>§8.5 endpoint from the surgC SHAPE (outer-q frame).  Once the surgC tower-shape
  Trans (Y@B) = Dpt e10 (t2 +B Dpt vm1 (bpHeadT (Trans Y))) is in hand, the endpoint
  spineLeaf (Trans (Y@B)) = bpHeadT (Trans Y) is a trivial spine readback
  (@{thm [source] m_8_5_spineLeaf_Dpt_addBT}).  This is the frame for the outer-q induction:
  prove the closed-form bpHeadT tower (T(q+1) = C(T q)) and endpoint follows.\<close>

lemma m_8_5_endpoint_of_surgshape:
  fixes Y B :: pairseq and t2 :: BT and e10 vm1 :: nat
  assumes shape: "Trans (Y @ B)
                    = Dpt (enat e10) (t2 +\<^sub>B Dpt (enat vm1) (bpHeadT (Trans Y)))"
  shows "spineLeaf (Trans (Y @ B)) = bpHeadT (Trans Y)"
  using shape by (simp add: m_8_5_spineLeaf_Dpt_addBT)


text \<open>§8.7 multiD junction — ORDER CORE (read-off reduction).  The \<open>multiD\<close> residual
  of @{thm [source] m_8_7_Trans_OT_nonkey} — \<open>leBT (Trm [hd bs]) (Trm [last as])\<close>,
  the descP junction between the prefix block \<open>Trm as = Trans (take (Pcut N) N)\<close> and
  the last \<open>P\<close>-component \<open>Trm bs = Trans (drop (Pcut N) N)\<close> — reduces, via two
  single-principal READ-OFFS, to the consecutive-\<open>P\<close>-component \<open>Trans\<close>-descent
  \<open>leBT (Trans blockJ) (Trans blockJ\<^sub>-\<^sub>1)\<close>.  Mechanism (no value reasoning):
  \<^item> every \<open>P\<close>-component is \<open>zeroT \<or> monoT\<close> (@{thm [source] m_6_2_P_components_1}); the
    last (\<open>blockJ = drop (Pcut N) N\<close>) and second-last (\<open>blockJ\<^sub>-\<^sub>1 = P N\<^bsub>Lng(P N)-2\<^esub>\<close>) are
    BOTH \<open>monoT\<close> (\<open>\<noteq> [(0,0)]\<close>: \<open>blockJ\<close> by \<open>ne\<close>, \<open>blockJ\<^sub>-\<^sub>1\<close> derived from \<open>comple\<close>),
    hence SINGLE-principal (@{thm [source] m_7_3_Trans_monoT});
  \<^item> so \<open>Trm [hd bs] = Trans blockJ\<close> (\<open>bs\<close> singleton) and, peeling the last block off
    the prefix (@{thm [source] trans_multi_split} / @{thm [source] poper_last_P_multi}),
    \<open>Trm [last as] = Trans blockJ\<^sub>-\<^sub>1\<close>.
  The residual \<open>comple\<close> (the equal-leftend consecutive-component descent) is the
  multiT analog of the §8.2 keystone R2 step and shares its value-residual with surgC.
  EMPIRICALLY (python \<open>_r2_multiD_probe.py\<close>: 0 fail / 462 multiT \<open>ST\<^bsub>PS\<^esub>\<close> samples;
  the two component heads are ALWAYS equal — first-col diagonal + equal leftend).\<close>

lemma m_8_7_multiD_junction:
  fixes N :: pairseq and as bs :: "BP list"
  assumes N: "N \<in> ST_PS" and mu: "multiT N"
    and ne: "drop (Pcut N) N \<noteq> [(0,0)]"
    and aeq: "Trans (take (Pcut N) N) = Trm as"
    and beq: "Trans (drop (Pcut N) N) = Trm bs"
    and asne: "as \<noteq> []" and bsne: "bs \<noteq> []"
    and comple: "leBT (Trans (drop (Pcut N) N)) (Trans (P N ! (Lng (P N) - 2)))"
  shows "leBT (Trm [hd bs]) (Trm [last as])"
proof -
  let ?bJ = "drop (Pcut N) N"
  let ?pre = "take (Pcut N) N"
  let ?bJm1 = "P N ! (Lng (P N) - 2)"
  have NR: "N \<in> RT_PS" using N m_6_7_ST_PS_subseteq_RT_PS by blast
  have NT: "N \<in> T_PS" using NR by (simp add: RT_PS_def)
  have L: "1 < Lng N" by (rule multiT_imp_Lng_gt1[OF NT mu])
  have Pne: "P N \<noteq> []" by (rule P_nonempty)
  \<comment> \<open>P-decomposition: \<open>P N = P ?pre @ [?bJ]\<close>\<close>
  have split: "last (P N) = ?bJ \<and> butlast (P N) = P ?pre"
    by (rule poper_last_P_multi[OF mu L])
  have PNdec: "P N = P ?pre @ [?bJ]"
  proof -
    have "P N = butlast (P N) @ [last (P N)]" using Pne by simp
    thus ?thesis using split by simp
  qed
  have preRT: "?pre \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF NR mu])
  have Ppre_ne: "P ?pre \<noteq> []" by (rule P_nonempty)
  have lpre: "1 \<le> Lng (P ?pre)" using Ppre_ne by (cases "P ?pre") auto
  have LPN: "Lng (P N) = Lng (P ?pre) + 1" using PNdec by simp
  have LPN2: "2 \<le> Lng (P N)" using LPN lpre by linarith
  \<comment> \<open>helper: a reduced \<open>P\<close>-component \<open>\<noteq> [(0,0)]\<close> is \<open>monoT\<close> and non-zero\<close>
  have compMono: "\<And>c. c \<in> set (P N) \<Longrightarrow> c \<noteq> [(0,0)]
        \<Longrightarrow> c \<in> RT_PS \<and> monoT c \<and> \<not> zeroT c"
  proof -
    fix c assume cmem: "c \<in> set (P N)" and cne: "c \<noteq> [(0,0)]"
    obtain J where cJ: "c = P N ! J" and JL: "J < Lng (P N)"
      using cmem by (auto simp: in_set_conv_nth)
    have cRT: "c \<in> RT_PS" using m_6_6_P_reduced[OF NT] NR JL cJ by blast
    have cT: "c \<in> T_PS" using cRT by (simp add: RT_PS_def)
    have znz: "\<not> zeroT c"
    proof
      assume z: "zeroT c"
      have l1: "Lng c = 1" using z by (simp add: zeroT_def)
      obtain v where vv: "c = [(v, v)]" using m_6_6_oneColumn[OF cT] l1 cRT by blast
      have "entry c 1 0 = 0" using z by (simp add: zeroT_def)
      hence "v = 0" using vv by (simp add: entry_def)
      thus False using vv cne by simp
    qed
    have "zeroT c \<or> monoT c" using m_6_2_P_components_1[OF NT] cmem by blast
    hence "monoT c" using znz by blast
    thus "c \<in> RT_PS \<and> monoT c \<and> \<not> zeroT c" using cRT znz by blast
  qed
  \<comment> \<open>helper: a \<open>monoT\<close> \<open>P\<close>-component has a single-principal \<open>Trans\<close>\<close>
  have monoSingle: "\<And>c cs. c \<in> RT_PS \<Longrightarrow> monoT c \<Longrightarrow> \<not> zeroT c
        \<Longrightarrow> Trans c = Trm cs \<Longrightarrow> length cs = 1"
  proof -
    fix c cs assume cRT: "c \<in> RT_PS" and cmono: "monoT c" and cnz: "\<not> zeroT c"
      and ceq: "Trans c = Trm cs"
    have cP: "P c = [c]" using cmono by (intro poper_P_nonmulti) (simp add: multiT_def)
    have cP0nz: "\<not> zeroT (P c ! 0)" using cnz cP by simp
    have "Lng (PB (Trans c)) = 1" using m_7_3_Trans_monoT[OF cRT cP0nz] cmono by simp
    thus "length cs = 1" using ceq by (simp add: PB_def)
  qed
  \<comment> \<open>read-off 1: \<open>Trm [hd bs] = Trans ?bJ\<close>\<close>
  have bJmem: "?bJ \<in> set (P N)" using PNdec by simp
  from compMono[OF bJmem ne]
  have bJ_RT: "?bJ \<in> RT_PS" and bJ_mono: "monoT ?bJ" and bJ_nz: "\<not> zeroT ?bJ" by auto
  have lenbs: "length bs = 1" by (rule monoSingle[OF bJ_RT bJ_mono bJ_nz beq])
  have read1: "Trm [hd bs] = Trans ?bJ"
  proof -
    from lenbs bsne obtain b where bsb: "bs = [b]" by (cases bs) auto
    thus ?thesis using beq by simp
  qed
  \<comment> \<open>\<open>?bJm1 = last (P ?pre)\<close>, \<open>\<noteq> [(0,0)]\<close> (from \<open>comple\<close>), \<open>monoT\<close>\<close>
  have bJm1eq: "?bJm1 = last (P ?pre)"
  proof -
    have idx: "Lng (P N) - 2 = Lng (P ?pre) - 1" using LPN lpre by linarith
    have lt: "Lng (P ?pre) - 1 < Lng (P ?pre)" using lpre by linarith
    have "?bJm1 = (P ?pre @ [?bJ]) ! (Lng (P ?pre) - 1)" using PNdec idx by simp
    also have "\<dots> = P ?pre ! (Lng (P ?pre) - 1)" using lt by (simp add: nth_append)
    also have "\<dots> = last (P ?pre)" using Ppre_ne by (simp add: last_conv_nth)
    finally show ?thesis .
  qed
  have bJm1lt: "Lng (P N) - 2 < Lng (P N)" using LPN2 by linarith
  have bJm1mem: "?bJm1 \<in> set (P N)" using bJm1lt by (rule nth_mem)
  have bJm1RT: "?bJm1 \<in> RT_PS"
  proof -
    have "\<forall>J<Lng (P N). P N ! J \<in> RT_PS" using m_6_6_P_reduced[OF NT] NR by blast
    thus ?thesis using bJm1lt by blast
  qed
  have bJm1ne: "?bJm1 \<noteq> [(0,0)]"
  proof
    assume z: "?bJm1 = [(0,0)]"
    have "zeroT ?bJm1" using z by (simp add: zeroT_def entry_def)
    hence "Trans ?bJm1 = 0\<^sub>B" using m_7_3_Trans_zeroT[OF bJm1RT] by simp
    hence "leBT (Trans ?bJ) 0\<^sub>B" using comple by simp
    hence "Trans ?bJ = 0\<^sub>B" by simp
    hence "zeroT ?bJ" using m_7_3_Trans_zeroT[OF bJ_RT] by simp
    thus False using bJ_nz by simp
  qed
  from compMono[OF bJm1mem bJm1ne]
  have bJm1_RT: "?bJm1 \<in> RT_PS" and bJm1_mono: "monoT ?bJm1" and bJm1_nz: "\<not> zeroT ?bJm1" by auto
  \<comment> \<open>read-off 2: \<open>Trm [last as] = Trans ?bJm1\<close>\<close>
  have read2: "Trm [last as] = Trans ?bJm1"
  proof (cases "multiT ?pre")
    case True
    have preT: "?pre \<in> T_PS" using preRT by (simp add: RT_PS_def)
    have lastblk: "drop (Pcut ?pre) ?pre = ?bJm1"
    proof -
      have "P ?pre ! (Lng (P ?pre) - 1) = drop (Pcut ?pre) ?pre"
        by (rule trans_multiT_last_component(1)[OF preT True])
      moreover have "P ?pre ! (Lng (P ?pre) - 1) = last (P ?pre)"
        using Ppre_ne by (simp add: last_conv_nth)
      ultimately show ?thesis using bJm1eq by simp
    qed
    have nz: "drop (Pcut ?pre) ?pre \<noteq> [(0,0)]" using lastblk bJm1ne by simp
    have split2: "Trans ?pre = Trans (take (Pcut ?pre) ?pre) +\<^sub>B Trans ?bJm1"
      using trans_multi_split[OF preRT True nz] lastblk by simp
    obtain cs where cs: "Trans (take (Pcut ?pre) ?pre) = Trm cs"
      by (cases "Trans (take (Pcut ?pre) ?pre)")
    obtain ds where ds: "Trans ?bJm1 = Trm ds" by (cases "Trans ?bJm1")
    have aseq: "as = cs @ ds"
    proof -
      have "Trm as = Trans ?pre" using aeq by simp
      also have "\<dots> = Trm cs +\<^sub>B Trm ds" using split2 cs ds by simp
      also have "\<dots> = Trm (cs @ ds)" by simp
      finally have "Trm as = Trm (cs @ ds)" .
      thus ?thesis by simp
    qed
    have lends: "length ds = 1" by (rule monoSingle[OF bJm1_RT bJm1_mono bJm1_nz ds])
    from lends obtain d where dsd: "ds = [d]" by (cases ds) auto
    have "last as = d" using aseq dsd by simp
    hence "Trm [last as] = Trm ds" using dsd by simp
    thus ?thesis using ds by simp
  next
    case False
    have Ppre1: "P ?pre = [?pre]" using False by (intro poper_P_nonmulti) simp
    have preEq: "?pre = ?bJm1"
    proof -
      have "last (P ?pre) = ?pre" using Ppre1 by simp
      thus ?thesis using bJm1eq by simp
    qed
    have trEq: "Trans ?bJm1 = Trm as" using aeq preEq by simp
    have lenas: "length as = 1" by (rule monoSingle[OF bJm1_RT bJm1_mono bJm1_nz trEq])
    from lenas asne obtain a where asa: "as = [a]" by (cases as) auto
    have "last as = a" using asa by simp
    hence "Trm [last as] = Trm as" using asa by simp
    thus ?thesis using trEq by simp
  qed
  show ?thesis using read1 read2 comple by simp
qed


text \<open>§8.5 (E.2) — generic per-column FOLD telescoping (the netfold skeleton, generalised
  from \<open>Trans\<close> to ANY column-functor \<open>f\<close>).  If appending the \<open>m\<close>-th column to \<open>Y\<frown>take m B\<close>
  applies the operator \<open>op m\<close> to \<open>f\<close>, then \<open>f (Y\<frown>B)\<close> is the whole-period fold of the \<open>op\<close>'s
  over \<open>f Y\<close>.  Pure induction on the take-prefix length; this is @{thm [source]
  m_8_5_scbSubst_netfold} with \<open>Trans\<close> abstracted to \<open>f\<close>, so it instantiates BOTH to the
  Trans netfold (f = Trans) and to the MARK netfold (\<open>f = \<lambda>M. Mark M jm1\<close>, \<open>Y = M[q]\<close>,
  \<open>B\<close> the deepen period): \<open>Mark (M[Suc q]) jm1 = fold op [0..<Lng B] (Mark (M[q]) jm1)\<close> from
  the per-column @{thm [source] m_8_5_Mark_scbSubst_step}.  The Mark level is the RIGHT level
  for the §8.5 keystone — \<open>U\<^sub>q = bpHeadT (Mark (M[q]) jm1)\<close> is non-empty (unlike the dead
  spineLeaf-leaf), and the descent ladder consumes the markstep, bypassing the Trans surgery.\<close>

lemma m_8_5_fold_of_colstep:
  fixes Y B :: pairseq and op :: "nat \<Rightarrow> BT \<Rightarrow> BT" and f :: "pairseq \<Rightarrow> BT"
  assumes step: "\<And>m. m < Lng B \<Longrightarrow> f (Y @ take (Suc m) B) = op m (f (Y @ take m B))"
  shows "f (Y @ B) = fold op [0..<Lng B] (f Y)"
proof -
  have gen: "\<And>k. k \<le> Lng B \<Longrightarrow> fold op [0..<k] (f Y) = f (Y @ take k B)"
  proof -
    fix k show "k \<le> Lng B \<Longrightarrow> fold op [0..<k] (f Y) = f (Y @ take k B)"
    proof (induct k)
      case 0 thus ?case by simp
    next
      case (Suc k)
      have kle: "k \<le> Lng B" using Suc.prems by simp
      have klt: "k < Lng B" using Suc.prems by simp
      have "fold op [0..<Suc k] (f Y) = op k (fold op [0..<k] (f Y))" by simp
      also have "\<dots> = op k (f (Y @ take k B))" using Suc.hyps kle by simp
      also have "\<dots> = f (Y @ take (Suc k) B)" using step[OF klt] by (rule sym)
      finally show ?case .
    qed
  qed
  have "fold op [0..<Lng B] (f Y) = f (Y @ take (Lng B) B)" using gen by simp
  thus ?thesis by simp
qed


text \<open>§8.5 (E.2) — depth-parametric spine action, DEPTH-0 (whole) case.  \<open>scbSubst\<close> at the
  ROOT (the marked core \<open>c\<^sub>1\<close> IS the whole single-principal term) replaces it wholesale by
  \<open>c\<^sub>2\<close>: \<open>scbSubst c\<^sub>1 c\<^sub>2 c\<^sub>1 = c\<^sub>2\<close>.  The scb-decomposition is trivial (\<open>s=b=[]\<close>, \<open>b\<close> all-RP
  vacuously); valid because a single-principal \<open>Trm[p]\<close> has \<open>flatBT (Trm[p]) = flatBP p\<close> (NO
  LP/RP wrapper — @{thm [source] flatBT.simps}), hence \<open>isPTB_str (flatBT c\<^sub>1)\<close>.  So
  \<open>spineLeaf (scbSubst c\<^sub>1 c\<^sub>2 c\<^sub>1) = spineLeaf c\<^sub>2\<close> — the depth-0 instance of the rightmost-spine
  depth action (the op_0 / graft-init column of the per-period netfold).\<close>

lemma m_8_5_scbSubst_whole:
  fixes c1 c2 :: BT
  assumes c1ne: "c1 \<noteq> Trm []" and ptc1: "isPTB_str (flatBT c1)"
  shows "scbSubst c1 c2 c1 = c2"
proof -
  have d: "scb_decomp c1 [] (flatBT c1) []"
    unfolding scb_decomp_def using ptc1 by simp
  have "scbSubst c1 c2 c1 = unflatBT ([] @ flatBT c2 @ [])"
    by (rule scbSubst_eq[OF d c1ne])
  also have "\<dots> = c2" by (simp add: unflatBT_flat)
  finally show ?thesis .
qed

lemma m_8_5_spineLeaf_scbSubst_whole:
  fixes c1 c2 :: BT
  assumes c1ne: "c1 \<noteq> Trm []" and ptc1: "isPTB_str (flatBT c1)"
  shows "spineLeaf (scbSubst c1 c2 c1) = spineLeaf c2"
  using m_8_5_scbSubst_whole[OF c1ne ptc1] by simp


text \<open>§8.5 (E.2) — the PER-COLUMN bpHeadT RECURRENCE (condV case), derived IN-THEORY from the
  §7.4 Mark structure (NO empirics).  At the second basepoint, @{thm [source]
  m_7_3_Mark_rightmost2} gives \<open>Mark M (transJm1 M) = transC2 M\<close>, and the condV branch of
  @{thm [source] transC2_def} is \<open>D\<^bsub>v\<^esub>(t\<^sub>2 +\<^sub>B D\<^bsub>e\<^esub> 0)\<close> with \<open>t\<^sub>2 = transT2 M = bpHeadT (transC1 M)
  = bpHeadT (Mark (Pred M) (transJm1 M))\<close> (@{thm [source] transT2_def}/@{thm [source]
  transC1_def}) and \<open>e = entry M 1 (Lng M-1)\<close>.  Taking \<open>bpHeadT\<close> (the \<open>D\<^bsub>v\<^esub>\<close>-head is dropped):
    \<open>bpHeadT (Mark M (transJm1 M)) = bpHeadT (Mark (Pred M) (transJm1 M)) +\<^sub>B D\<^bsub>e\<^esub> 0\<close>
  — appending ONE leaf principal \<open>D\<^bsub>e\<^esub> 0\<close> per condV column.  This is the exact per-column
  marked-head action; the §8.5 keystone value content, made explicit from §7.4 (no Trans
  surgery, no slice empirics).\<close>

lemma m_8_5_Mark_bpHeadT_step_condV:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and condV: "transCondV M"
  shows "bpHeadT (Mark M (transJm1 M))
       = bpHeadT (Mark (Pred M) (transJm1 M)) +\<^sub>B Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B"
proof -
  have mk2: "Mark M (transJm1 M) = transC2 M"
    by (rule m_7_3_Mark_rightmost2[OF MR MP J1pos T1])
  have c2: "transC2 M
              = Dpt (transV M) (transT2 M +\<^sub>B Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B)"
    using condV by (simp add: transC2_def Let_def)
  have tt2: "transT2 M = bpHeadT (Mark (Pred M) (transJm1 M))"
    by (simp add: transT2_def transC1_def)
  have "bpHeadT (Mark M (transJm1 M)) = bpHeadT (transC2 M)" using mk2 by simp
  also have "\<dots> = transT2 M +\<^sub>B Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B"
    using c2 by simp
  also have "\<dots> = bpHeadT (Mark (Pred M) (transJm1 M))
                    +\<^sub>B Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B"
    using tt2 by simp
  finally show ?thesis by (simp add: transJ1_def)
qed


text \<open>§8.5 (E.2) — per-column bpHeadT action, condVI branch (in-theory, from transC2_def).
  A condVI column RESETS the marked head to a single leaf principal \<open>D\<^bsub>e\<^esub> 0\<close> (independent of
  \<open>Pred\<close>): \<open>bpHeadT (Mark M (transJm1 M)) = D\<^bsub>e\<^esub> 0\<close>, \<open>e = entry M 1 (Lng M-1)\<close>.  The condVI
  branch of @{thm [source] transC2_def} is \<open>D\<^bsub>v\<^esub>(D\<^bsub>e\<^esub> 0)\<close>; via @{thm [source]
  m_7_3_Mark_rightmost2}.  Companion to @{thm [source] m_8_5_Mark_bpHeadT_step_condV} for the
  per-column transCond case analysis.\<close>

lemma m_8_5_Mark_bpHeadT_step_condVI:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and ncond: "\<not> transCondI M \<and> \<not> transCondIII M \<and> \<not> transCondV M"
    and condVI: "transCondVI M"
  shows "bpHeadT (Mark M (transJm1 M)) = Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B"
proof -
  have mk2: "Mark M (transJm1 M) = transC2 M"
    by (rule m_7_3_Mark_rightmost2[OF MR MP J1pos T1])
  have c2: "transC2 M = Dpt (transV M) (Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B)"
    using ncond condVI by (simp add: transC2_def Let_def)
  show ?thesis using mk2 c2 by (simp add: transJ1_def)
qed


text \<open>§8.5 (E.2) — per-column bpHeadT action, \<open>t\<^sub>2=0\<close> branch (in-theory).  When the predecessor
  head \<open>transT2 M = 0\<close> and none of cond I/III/V/VI hold, transC2 nests \<open>D\<^bsub>e\<^sub>jp\<^esub>(D\<^bsub>e\<^esub> 0)\<close>:
  \<open>bpHeadT (Mark M (transJm1 M)) = D\<^bsub>entry M 1 jp\<^esub> (D\<^bsub>entry M 1 (Lng-1)\<^esub> 0)\<close>.\<close>

lemma m_8_5_Mark_bpHeadT_step_tt2zero:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and ncond: "\<not> transCondI M \<and> \<not> transCondIII M \<and> \<not> transCondV M \<and> \<not> transCondVI M"
    and tt2z: "transT2 M = 0\<^sub>B"
  shows "bpHeadT (Mark M (transJm1 M))
       = Dpt (enat (entry M 1 (transJ0 M))) (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
proof -
  have mk2: "Mark M (transJm1 M) = transC2 M"
    by (rule m_7_3_Mark_rightmost2[OF MR MP J1pos T1])
  have c2: "transC2 M
              = Dpt (transV M) (Dpt (enat (entry M 1 (transJ0 M)))
                                    (Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B))"
    using ncond tt2z by (simp add: transC2_def Let_def)
  show ?thesis using mk2 c2 by (simp add: transJ1_def)
qed


text \<open>§8.5 (E.2) — per-column bpHeadT action, ELSE branch (the NESTED / C-wrap shape, in-theory).
  When \<open>transT2 M \<noteq> 0\<close> and none of cond I/III/V/VI hold, transC2 produces the nested
  \<open>D\<^bsub>v\<^esub>(t\<^sub>3 +\<^sub>B D\<^bsub>e\<^sub>jp\<^esub>(t\<^sub>4 +\<^sub>B D\<^bsub>e\<^esub> 0))\<close>, where \<open>t\<^sub>3/t\<^sub>4\<close> are the §7.2 left-split of the predecessor
  head \<open>t\<^sub>2 = transT2 M\<close> at its last principal \<open>pj\<close> (\<open>t\<^sub>4 = bpHeadT pj\<close> when the left-\<open>D\<^bsub>jp\<^esub>\<close>
  guard fires).  Taking \<open>bpHeadT\<close>:
    \<open>bpHeadT (Mark M (transJm1 M)) = t\<^sub>3 +\<^sub>B D\<^bsub>entry M 1 jp\<^esub> (t\<^sub>4 +\<^sub>B D\<^bsub>entry M 1 (Lng-1)\<^esub> 0)\<close>.
  This is the SELF-SIMILAR reconstructor: \<open>t\<^sub>4 = bpHeadT pj\<close> = the body of the previous head's
  last principal — the source of the per-period \<open>C\<close>-wrap (the §8 keystone value).\<close>

lemma m_8_5_Mark_bpHeadT_step_else:
  fixes M :: pairseq
  defines "t2 \<equiv> transT2 M"
  defines "J1 \<equiv> Lng (PB t2) - 1"
  defines "pj \<equiv> PB t2 ! J1"
  defines "leftDj0 \<equiv> (bpHeadV pj = enat (entry M 1 (transJ0 M)))"
  defines "t3 \<equiv> (if leftDj0 then SigmaB (take J1 (PB t2)) else t2)"
  defines "t4 \<equiv> (if leftDj0 then bpHeadT pj else t2)"
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and ncond: "\<not> transCondI M \<and> \<not> transCondIII M \<and> \<not> transCondV M \<and> \<not> transCondVI M"
    and tt2nz: "transT2 M \<noteq> 0\<^sub>B"
  shows "bpHeadT (Mark M (transJm1 M))
       = t3 +\<^sub>B Dpt (enat (entry M 1 (transJ0 M)))
                   (t4 +\<^sub>B Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
proof -
  have mk2: "Mark M (transJm1 M) = transC2 M"
    by (rule m_7_3_Mark_rightmost2[OF MR MP J1pos T1])
  have c2: "transC2 M
              = Dpt (transV M)
                  (t3 +\<^sub>B Dpt (enat (entry M 1 (transJ0 M)))
                         (t4 +\<^sub>B Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B))"
    using ncond tt2nz
    by (simp add: transC2_def Let_def t2_def J1_def pj_def leftDj0_def t3_def t4_def)
  show ?thesis using mk2 c2 by (simp add: transJ1_def)
qed


text \<open>§8.5 (E.2) — RIGHTMOST-SPINE DEPTH and the DEPTH-PARAMETRIC (A) spine action.
  \<open>rspine d c\<^sub>1 t\<close>: the marked core \<open>c\<^sub>1\<close> sits at DEPTH \<open>d\<close> on the rightmost spine of \<open>t\<close> —
  i.e. \<open>t\<close> is the \<open>d\<close>-fold spine nesting \<open>D\<^bsub>e\<^esub>(pre +\<^sub>B D\<^bsub>h\<^esub> (\<dots>))\<close> bottoming at \<open>c\<^sub>1\<close>, each
  level carrying a non-empty prefix \<open>pre\<close> (so one \<open>spineLeaf\<close> step = one level down).  By
  \<open>rspine_scb_decomp\<close>, that position yields exactly the all-RP \<open>scb_decomp\<close>
  that forces \<open>c\<^sub>1\<close> on the rightmost spine.  The (A) GENERAL WRAPPER
  \<open>rspine_spineLeaf_scbSubst\<close> composes the two green endpoints — the DEEP step
  @{thm [source] m_8_5_spineLeaf_scbSubst} (2b: \<open>spineLeaf\<close> commutes with \<open>scbSubst\<close>) walked
  \<open>d\<close> times down the rightmost spine, bottoming at the WHOLE-replace
  @{thm [source] m_8_5_scbSubst_whole} (depth-0) — into the closed form
  \<open>(spineLeaf\<^bsup>d\<^esup>) (scbSubst c\<^sub>1 c\<^sub>2 t) = c\<^sub>2\<close>: substituting the depth-\<open>d\<close> marked core \<open>c\<^sub>1\<close> by
  \<open>c\<^sub>2\<close> and reading off \<open>d\<close> levels down the rightmost spine recovers \<open>c\<^sub>2\<close>.  Pure structural
  glue (no value math): the reusable per-column engine for the B3 markstep, whose condI/III
  columns sit at increasing depths \<open>d\<^sub>k = (q-1)+k\<close>.\<close>

primrec rspine :: "nat \<Rightarrow> BT \<Rightarrow> BT \<Rightarrow> bool" where
  "rspine 0 c1 t = (t = c1)"
| "rspine (Suc d) c1 t =
     (\<exists>e pre h x. t = Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)
        \<and> untrm pre \<noteq> [] \<and> rspine d c1 x)"

lemma rspine_nonempty:
  assumes "rspine d c1 t" and "c1 \<noteq> Trm []"
  shows "t \<noteq> Trm []"
proof (cases d)
  case 0 thus ?thesis using assms by simp
next
  case (Suc d')
  from assms(1)[unfolded Suc] obtain e pre h x where
    "t = Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)" by auto
  thus ?thesis by simp
qed

lemma rspine_scb_decomp:
  assumes rs: "rspine d c1 t" and c1ne: "c1 \<noteq> Trm []" and ptc1: "isPTB_str (flatBT c1)"
  shows "\<exists>s b. scb_decomp t s (flatBT c1) b \<and> (\<forall>z\<in>set b. z = RP)"
  using rs
proof (induction d arbitrary: t)
  case 0
  hence tc: "t = c1" by simp
  have d0: "scb_decomp c1 [] (flatBT c1) []"
    unfolding scb_decomp_def using ptc1 by simp
  show ?case unfolding tc
    by (rule exI[of _ "[]"], rule exI[of _ "[]"], simp add: d0)
next
  case (Suc d)
  from \<open>rspine (Suc d) c1 t\<close> obtain e pre h x where
    t: "t = Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)" and prene: "untrm pre \<noteq> []"
    and rx: "rspine d c1 x" by auto
  from Suc.IH[OF rx] obtain sx bx
    where dx: "scb_decomp x sx (flatBT c1) bx" and rbx: "\<forall>z\<in>set bx. z = RP" by auto
  have flatx: "flatBT x = sx @ flatBT c1 @ bx" using dx by (simp add: scb_decomp_def)
  have scbDhx: "scb_decomp (Dpt (enat h) x) (Dsym (enat h) # sx) (flatBT c1) bx"
    unfolding scb_decomp_def using flatx ptc1 rbx by simp
  have dh1: "length (untrm (Dpt (enat h) x)) = 1" by simp
  have dBODY: "scb_decomp (pre +\<^sub>B Dpt (enat h) x)
                  (liftS pre (Dsym (enat h) # sx)) (flatBT c1) (bx @ [RP])"
    by (rule scb_addBT_left[OF scbDhx dh1 prene])
  have flatBODY: "flatBT (pre +\<^sub>B Dpt (enat h) x)
                    = liftS pre (Dsym (enat h) # sx) @ flatBT c1 @ (bx @ [RP])"
    using dBODY by (simp add: scb_decomp_def)
  have rbB: "\<forall>z\<in>set (bx @ [RP]). z = RP" using rbx by auto
  have sc: "scb_decomp (Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x))
              (Dsym (enat e) # liftS pre (Dsym (enat h) # sx)) (flatBT c1) (bx @ [RP])"
    unfolding scb_decomp_def using flatBODY ptc1 rbB by simp
  have "\<exists>s b. scb_decomp (Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)) s (flatBT c1) b
          \<and> (\<forall>z\<in>set b. z = RP)" using sc rbB by blast
  thus ?case using t by simp
qed

lemma rspine_spineLeaf_nav:
  assumes "rspine d c1 t"
  shows "(spineLeaf ^^ d) t = c1"
  using assms
proof (induction d arbitrary: t)
  case 0 thus ?case by simp
next
  case (Suc d)
  from \<open>rspine (Suc d) c1 t\<close> obtain e pre h x where
    t: "t = Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)" and rx: "rspine d c1 x" by auto
  have "(spineLeaf ^^ Suc d) t = (spineLeaf ^^ d) (spineLeaf t)"
    by (simp only: funpow_Suc_right o_apply)
  also have "\<dots> = (spineLeaf ^^ d) x" using t by (simp add: m_8_5_spineLeaf_Dpt_addBT)
  also have "\<dots> = c1" by (rule Suc.IH[OF rx])
  finally show ?case .
qed

lemma rspine_spineLeaf_scbSubst:
  assumes rs: "rspine d c1 t" and c1ne: "c1 \<noteq> Trm []"
    and ptc1: "isPTB_str (flatBT c1)" and ptc2: "isPTB_str (flatBT c2)"
  shows "(spineLeaf ^^ d) (scbSubst c1 c2 t) = c2"
  using rs
proof (induction d arbitrary: t)
  case 0
  hence tc: "t = c1" by simp
  have "scbSubst c1 c2 c1 = c2" by (rule m_8_5_scbSubst_whole[OF c1ne ptc1])
  thus ?case using tc by simp
next
  case (Suc d)
  from \<open>rspine (Suc d) c1 t\<close> obtain e pre h x where
    t: "t = Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)" and prene: "untrm pre \<noteq> []"
    and rx: "rspine d c1 x" by auto
  obtain sx bx where dx: "scb_decomp x sx (flatBT c1) bx"
    using rspine_scb_decomp[OF rx c1ne ptc1] by auto
  have xnz: "x \<noteq> Trm []" by (rule rspine_nonempty[OF rx c1ne])
  have step2b: "spineLeaf (scbSubst c1 c2 t) = scbSubst c1 c2 x"
  proof -
    have "spineLeaf (scbSubst c1 c2 (Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)))
            = scbSubst c1 c2 (spineLeaf (Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)))"
      by (rule m_8_5_spineLeaf_scbSubst[OF dx xnz ptc2 prene])
    also have "spineLeaf (Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)) = x"
      by (rule m_8_5_spineLeaf_Dpt_addBT)
    finally show ?thesis using t by simp
  qed
  have "(spineLeaf ^^ Suc d) (scbSubst c1 c2 t)
          = (spineLeaf ^^ d) (spineLeaf (scbSubst c1 c2 t))"
    by (simp only: funpow_Suc_right o_apply)
  also have "\<dots> = (spineLeaf ^^ d) (scbSubst c1 c2 x)" using step2b by simp
  also have "\<dots> = c2" by (rule Suc.IH[OF rx])
  finally show ?case .
qed


text \<open>§8.5 (E.2) — DEPTH-PARTIAL commute (the B3b composition engine).  Generalises
  @{thm [source] rspine_spineLeaf_scbSubst} from the full depth \<open>d\<close> to ANY prefix \<open>k \<le> d\<close>:
  reading the rightmost spine down \<open>k\<close> levels COMMUTES with the depth-\<open>d\<close> \<open>scbSubst\<close> (the
  substituted core \<open>c\<^sub>1\<close> sits below level \<open>k\<close>, so the two operations are independent):
  \<open>(spineLeaf\<^bsup>k\<^esup>) (scbSubst c\<^sub>1 c\<^sub>2 t) = scbSubst c\<^sub>1 c\<^sub>2 ((spineLeaf\<^bsup>k\<^esup>) t)\<close>.  Same spine
  induction as the (A) wrapper, walking 2b \<open>k\<close> times (no whole-replace at the bottom — we stop
  ABOVE \<open>c\<^sub>1\<close>).  This is the engine that pushes a FIXED outer read-off \<open>spineLeaf\<^bsup>d\<^sub>0\<^esup>\<close> through
  EVERY period column of the markstep fold: each column's \<open>scbSubst\<close> sits at depth \<open>d\<^sub>m \<ge> d\<^sub>0\<close>,
  so \<open>spineLeaf\<^bsup>d\<^sub>0\<^esup>\<close> commutes past it, peeling the period one self-similar level at a time.
  The \<open>k = d\<close> instance recovers the (A) wrapper (\<open>scbSubst c\<^sub>1 c\<^sub>2 c\<^sub>1 = c\<^sub>2\<close> at the bottom).\<close>

lemma rspine_funpow_scbSubst_commute:
  assumes rs: "rspine d c1 t" and kd: "k \<le> d" and c1ne: "c1 \<noteq> Trm []"
    and ptc1: "isPTB_str (flatBT c1)" and ptc2: "isPTB_str (flatBT c2)"
  shows "(spineLeaf ^^ k) (scbSubst c1 c2 t) = scbSubst c1 c2 ((spineLeaf ^^ k) t)"
  using rs kd
proof (induction k arbitrary: t d)
  case 0 thus ?case by simp
next
  case (Suc k)
  from \<open>Suc k \<le> d\<close> obtain d' where d: "d = Suc d'" by (cases d) auto
  from \<open>rspine d c1 t\<close> obtain e pre h x where
    t: "t = Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)" and prene: "untrm pre \<noteq> []"
    and rx: "rspine d' c1 x" using d by auto
  have kd': "k \<le> d'" using \<open>Suc k \<le> d\<close> d by simp
  obtain sx bx where dx: "scb_decomp x sx (flatBT c1) bx"
    using rspine_scb_decomp[OF rx c1ne ptc1] by auto
  have xnz: "x \<noteq> Trm []" by (rule rspine_nonempty[OF rx c1ne])
  have slt: "spineLeaf t = x" using t by (simp add: m_8_5_spineLeaf_Dpt_addBT)
  have step2b: "spineLeaf (scbSubst c1 c2 t) = scbSubst c1 c2 x"
  proof -
    have "spineLeaf (scbSubst c1 c2 (Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)))
            = scbSubst c1 c2 (spineLeaf (Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)))"
      by (rule m_8_5_spineLeaf_scbSubst[OF dx xnz ptc2 prene])
    also have "spineLeaf (Dpt (enat e) (pre +\<^sub>B Dpt (enat h) x)) = x"
      by (rule m_8_5_spineLeaf_Dpt_addBT)
    finally show ?thesis using t by simp
  qed
  have "(spineLeaf ^^ Suc k) (scbSubst c1 c2 t)
          = (spineLeaf ^^ k) (spineLeaf (scbSubst c1 c2 t))"
    by (simp only: funpow_Suc_right o_apply)
  also have "\<dots> = (spineLeaf ^^ k) (scbSubst c1 c2 x)" using step2b by simp
  also have "\<dots> = scbSubst c1 c2 ((spineLeaf ^^ k) x)" by (rule Suc.IH[OF rx kd'])
  also have "\<dots> = scbSubst c1 c2 ((spineLeaf ^^ Suc k) t)"
    by (simp only: funpow_Suc_right o_apply slt)
  finally show ?case .
qed


text \<open>§8.5 (E.2) — the B3b FOLD-DRIVE.  Threads the depth-partial commute
  @{thm [source] rspine_funpow_scbSubst_commute} through the WHOLE markstep period fold
  \<open>fold op [0..<w]\<close> (\<open>op m = scbSubst (c\<^sub>1 m) (c\<^sub>2 m)\<close>, the per-column marked-head action of
  @{thm [source] m_8_5_Mark_scbSubst_step}): given the (B3a) DEPTH LADDER — at every column \<open>m\<close>
  the substituted core \<open>c\<^sub>1 m\<close> sits at rightmost-spine depth \<open>dd m \<ge> k\<close> in the running
  accumulator \<open>fold op [0..<m] acc\<^sub>0\<close> — the fixed outer read-off \<open>spineLeaf\<^bsup>k\<^esup>\<close> COMMUTES past
  the entire period:
    \<open>(spineLeaf\<^bsup>k\<^esup>) (fold op [0..<w] acc\<^sub>0) = fold op [0..<w] ((spineLeaf\<^bsup>k\<^esup>) acc\<^sub>0)\<close>.
  Induction on the period length, peeling one column at a time (each at depth \<open>dd m \<ge> k\<close>).
  This isolates the markstep to exactly the depth ladder (\<open>ladder\<close>) — the SOLE residual,
  the B3a geometric crux \<open>dd m = (q-1)+m\<close> (otasm-confirmed empirically).  Instantiate \<open>k\<close>
  with the fixed outer depth \<open>d\<^sub>0 = q-1\<close> and the RHS leaf-fold + \<open>bpHeadT\<close>-readback assemble
  the period \<open>C\<close>-graft.\<close>

lemma b3b_spineLeaf_fold_drive:
  fixes c1 c2 :: "nat \<Rightarrow> BT" and acc0 :: BT and k w :: nat and dd :: "nat \<Rightarrow> nat"
    and op :: "nat \<Rightarrow> BT \<Rightarrow> BT"
  defines "op \<equiv> (\<lambda>m t. scbSubst (c1 m) (c2 m) t)"
  assumes ladder: "\<And>m. m < w \<Longrightarrow> rspine (dd m) (c1 m) (fold op [0..<m] acc0)"
    and dge: "\<And>m. m < w \<Longrightarrow> k \<le> dd m"
    and c1ne: "\<And>m. m < w \<Longrightarrow> c1 m \<noteq> Trm []"
    and pt1: "\<And>m. m < w \<Longrightarrow> isPTB_str (flatBT (c1 m))"
    and pt2: "\<And>m. m < w \<Longrightarrow> isPTB_str (flatBT (c2 m))"
  shows "(spineLeaf ^^ k) (fold op [0..<w] acc0)
       = fold op [0..<w] ((spineLeaf ^^ k) acc0)"
proof -
  have gen: "\<And>n. n \<le> w \<Longrightarrow> (spineLeaf ^^ k) (fold op [0..<n] acc0)
              = fold op [0..<n] ((spineLeaf ^^ k) acc0)"
  proof -
    fix n
    show "n \<le> w \<Longrightarrow> (spineLeaf ^^ k) (fold op [0..<n] acc0)
            = fold op [0..<n] ((spineLeaf ^^ k) acc0)"
    proof (induction n)
      case 0 thus ?case by simp
    next
      case (Suc n)
      have nlew: "n \<le> w" using Suc.prems by simp
      have nw: "n < w" using Suc.prems by simp
      have foldA: "fold op [0..<Suc n] acc0 = op n (fold op [0..<n] acc0)"
        by (simp add: upt_Suc_append)
      have foldB: "fold op [0..<Suc n] ((spineLeaf ^^ k) acc0)
                     = op n (fold op [0..<n] ((spineLeaf ^^ k) acc0))"
        by (simp add: upt_Suc_append)
      have IH: "(spineLeaf ^^ k) (fold op [0..<n] acc0)
                  = fold op [0..<n] ((spineLeaf ^^ k) acc0)" by (rule Suc.IH[OF nlew])
      have opn: "op n = (\<lambda>t. scbSubst (c1 n) (c2 n) t)" by (simp add: op_def)
      have comm: "(spineLeaf ^^ k) (op n (fold op [0..<n] acc0))
                    = op n ((spineLeaf ^^ k) (fold op [0..<n] acc0))"
      proof -
        have "(spineLeaf ^^ k) (scbSubst (c1 n) (c2 n) (fold op [0..<n] acc0))
                = scbSubst (c1 n) (c2 n) ((spineLeaf ^^ k) (fold op [0..<n] acc0))"
          by (rule rspine_funpow_scbSubst_commute[OF ladder[OF nw] dge[OF nw]
                    c1ne[OF nw] pt1[OF nw] pt2[OF nw]])
        thus ?thesis using opn by simp
      qed
      have "(spineLeaf ^^ k) (fold op [0..<Suc n] acc0)
              = (spineLeaf ^^ k) (op n (fold op [0..<n] acc0))" using foldA by simp
      also have "\<dots> = op n ((spineLeaf ^^ k) (fold op [0..<n] acc0))" by (rule comm)
      also have "\<dots> = op n (fold op [0..<n] ((spineLeaf ^^ k) acc0))" using IH by simp
      also have "\<dots> = fold op [0..<Suc n] ((spineLeaf ^^ k) acc0)" using foldB by simp
      finally show ?case .
    qed
  qed
  show ?thesis using gen[of w] by simp
qed


text \<open>§8.5 (B3) — the MARKSTEP SKELETON (metric-light bpHeadT level).  Assembles the
  markstep \<open>bpHeadT (Mark (M[Suc q]) jm1) = C (bpHeadT (Mark (M[q]) jm1))\<close> from THREE
  named inputs, isolating the per-period keystone VALUE.  Writing \<open>F = fold op [0..<w]\<close>
  (the period column-substitution fold, \<open>F acc\<^sub>0 = Mark (M[Suc q]) jm1\<close> by
  @{thm [source] m_8_5_fold_of_colstep}, \<open>acc\<^sub>0 = Mark (M[q]) jm1\<close>):
  \<^item> \<open>drive\<close>: the \<open>k=1\<close> instance of @{thm [source] b3b_spineLeaf_fold_drive} (commute,
    DISCHARGED from the depth ladder \<open>dd m \<ge> 1\<close>) — \<open>spineLeaf (F acc\<^sub>0) = F (spineLeaf acc\<^sub>0)\<close>;
  \<^item> \<open>assembly\<close> (the C-ASSEMBLY, the per-period self-similar VALUE — the irreducible
    keystone, otasm-empirical 47/47, NOT mechanically reducible to the geometry):
    \<open>F (spineLeaf acc\<^sub>0) = bpHeadT acc\<^sub>0\<close> — the period's column ops, applied to \<open>U\<^sub>q\<close>'s deep
    slot, RECONSTRUCT \<open>U\<^sub>q = bpHeadT acc\<^sub>0\<close> itself;
  \<^item> \<open>shape\<close> (the TOWER-SHAPE of the new mark):
    \<open>bpHeadT (F acc\<^sub>0) = t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> (spineLeaf (F acc\<^sub>0))\<close>.
  With @{thm [source] m_8_5_C_body} (\<open>C z = t\<^sub>2 +\<^sub>B D\<^bsub>vm1\<^esub> z\<close>) the markstep follows mechanically.
  This SCOPES the §8.5 keystone to exactly \<open>assembly\<close> (the self-similar value) + \<open>shape\<close>
  (the tower form) + the GREEN depth ladder (B3a); everything else is composed.\<close>

lemma b3_markstep_skeleton:
  fixes op :: "nat \<Rightarrow> BT \<Rightarrow> BT" and acc0 t2 :: BT and w vm1 :: nat and C :: "BT \<Rightarrow> BT"
  assumes drive: "spineLeaf (fold op [0..<w] acc0) = fold op [0..<w] (spineLeaf acc0)"
    and assembly: "fold op [0..<w] (spineLeaf acc0) = bpHeadT acc0"
    and shape: "bpHeadT (fold op [0..<w] acc0)
                  = t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (fold op [0..<w] acc0))"
    and Cdef: "\<And>z. C z = t2 +\<^sub>B Dpt (enat vm1) z"
  shows "bpHeadT (fold op [0..<w] acc0) = C (bpHeadT acc0)"
proof -
  have sl: "spineLeaf (fold op [0..<w] acc0) = bpHeadT acc0"
    using drive assembly by simp
  have "bpHeadT (fold op [0..<w] acc0)
          = t2 +\<^sub>B Dpt (enat vm1) (spineLeaf (fold op [0..<w] acc0))"
    by (rule shape)
  also have "\<dots> = t2 +\<^sub>B Dpt (enat vm1) (bpHeadT acc0)" using sl by simp
  also have "\<dots> = C (bpHeadT acc0)" using Cdef by simp
  finally show ?thesis .
qed


text \<open>§8.5 (B3) — RIGHTMOST-SPINE navigation \<open>rnav\<close> (LAST-principal descent), the
  CORRECT spine for the genuine kernel.  \<open>spineLeaf\<close> (\<open>bpHeadT \<circ> last \<circ> PB \<circ> bpHeadT\<close>)
  steps into the FIRST principal's body and DIES on the multi-principal towers the kernel's
  \<open>Mark\<close> produces; \<open>rnav t = bpHeadT (Trm [last (untrm t)])\<close> descends the LAST principal's
  subtree cleanly (no first-principal step).  The whole (A)-engine re-bases mechanically on
  \<open>rnav\<close>: same whole-replace base + a last-principal-descent step
  (@{thm [source] m_8_5_scbSubst_addBT_commute} / @{thm [source] m_8_5_scbSubst_Dpt}).
  Depth ladder (otasm): \<open>k\<^sub>m = q-2\<close> (m=0) / \<open>q-1\<close> (m\<ge>1) in the \<open>rnav\<close> metric.\<close>

definition rnav :: "BT \<Rightarrow> BT" where
  "rnav t = bpHeadT (Trm [last (untrm t)])"

lemma rnav_addBT: "rnav (pre +\<^sub>B Dpt (enat h) x) = x"
proof -
  obtain ps where "pre = Trm ps" by (cases pre)
  thus ?thesis by (simp add: rnav_def)
qed

lemma rnav_Dpt: "rnav (Dpt (enat h) z) = z"
  by (simp add: rnav_def)

primrec rspine_r :: "nat \<Rightarrow> BT \<Rightarrow> BT \<Rightarrow> bool" where
  "rspine_r 0 c1 t = (t = c1)"
| "rspine_r (Suc d) c1 t =
     (\<exists>pre h x. t = pre +\<^sub>B Dpt (enat h) x \<and> rspine_r d c1 x)"

lemma rspine_r_nonempty:
  assumes "rspine_r d c1 t" and "c1 \<noteq> Trm []"
  shows "t \<noteq> Trm []"
proof (cases d)
  case 0 thus ?thesis using assms by simp
next
  case (Suc d')
  from assms(1)[unfolded Suc] obtain pre h x where
    t: "t = pre +\<^sub>B Dpt (enat h) x" by auto
  obtain ps where "pre = Trm ps" by (cases pre)
  thus ?thesis using t by simp
qed

lemma rnav_scbSubst_step:
  assumes dx: "scb_decomp x sx (flatBT c1) bx" and xnz: "x \<noteq> Trm []"
    and ptc2: "isPTB_str (flatBT c2)"
  shows "rnav (scbSubst c1 c2 (pre +\<^sub>B Dpt (enat h) x)) = scbSubst c1 c2 x"
proof (cases "untrm pre = []")
  case True
  hence preE: "pre +\<^sub>B Dpt (enat h) x = Dpt (enat h) x" by (cases pre) auto
  have "scbSubst c1 c2 (Dpt (enat h) x) = Dpt (enat h) (scbSubst c1 c2 x)"
    by (rule m_8_5_scbSubst_Dpt[OF dx xnz ptc2])
  thus ?thesis using preE by (simp add: rnav_Dpt)
next
  case False
  have "scbSubst c1 c2 (pre +\<^sub>B Dpt (enat h) x) = pre +\<^sub>B Dpt (enat h) (scbSubst c1 c2 x)"
    by (rule m_8_5_scbSubst_addBT_commute[OF dx xnz ptc2 False])
  thus ?thesis by (simp add: rnav_addBT)
qed

lemma rspine_r_scb_decomp:
  assumes rs: "rspine_r d c1 t" and c1ne: "c1 \<noteq> Trm []" and ptc1: "isPTB_str (flatBT c1)"
  shows "\<exists>s b. scb_decomp t s (flatBT c1) b \<and> (\<forall>z\<in>set b. z = RP)"
  using rs
proof (induction d arbitrary: t)
  case 0
  hence tc: "t = c1" by simp
  have d0: "scb_decomp c1 [] (flatBT c1) []"
    unfolding scb_decomp_def using ptc1 by simp
  show ?case unfolding tc
    by (rule exI[of _ "[]"], rule exI[of _ "[]"], simp add: d0)
next
  case (Suc d)
  from \<open>rspine_r (Suc d) c1 t\<close> obtain pre h x where
    t: "t = pre +\<^sub>B Dpt (enat h) x" and rx: "rspine_r d c1 x" by auto
  from Suc.IH[OF rx] obtain sx bx
    where dx: "scb_decomp x sx (flatBT c1) bx" and rbx: "\<forall>z\<in>set bx. z = RP" by auto
  have flatx: "flatBT x = sx @ flatBT c1 @ bx" using dx by (simp add: scb_decomp_def)
  have scbDhx: "scb_decomp (Dpt (enat h) x) (Dsym (enat h) # sx) (flatBT c1) bx"
    unfolding scb_decomp_def using flatx ptc1 rbx by simp
  have dh1: "length (untrm (Dpt (enat h) x)) = 1" by simp
  show ?case
  proof (cases "untrm pre = []")
    case True
    hence preE: "t = Dpt (enat h) x" using t by (cases pre) auto
    have "\<exists>s b. scb_decomp (Dpt (enat h) x) s (flatBT c1) b \<and> (\<forall>z\<in>set b. z = RP)"
      using scbDhx rbx by blast
    thus ?thesis using preE by simp
  next
    case False
    have dBODY: "scb_decomp (pre +\<^sub>B Dpt (enat h) x)
                    (liftS pre (Dsym (enat h) # sx)) (flatBT c1) (bx @ [RP])"
      by (rule scb_addBT_left[OF scbDhx dh1 False])
    have rbB: "\<forall>z\<in>set (bx @ [RP]). z = RP" using rbx by auto
    have "\<exists>s b. scb_decomp (pre +\<^sub>B Dpt (enat h) x) s (flatBT c1) b \<and> (\<forall>z\<in>set b. z = RP)"
      using dBODY rbB by blast
    thus ?thesis using t by simp
  qed
qed

lemma rspine_r_nav:
  assumes "rspine_r d c1 t"
  shows "(rnav ^^ d) t = c1"
  using assms
proof (induction d arbitrary: t)
  case 0 thus ?case by simp
next
  case (Suc d)
  from \<open>rspine_r (Suc d) c1 t\<close> obtain pre h x where
    t: "t = pre +\<^sub>B Dpt (enat h) x" and rx: "rspine_r d c1 x" by auto
  have "(rnav ^^ Suc d) t = (rnav ^^ d) (rnav t)" by (simp only: funpow_Suc_right o_apply)
  also have "\<dots> = (rnav ^^ d) x" using t by (simp add: rnav_addBT)
  also have "\<dots> = c1" by (rule Suc.IH[OF rx])
  finally show ?case .
qed

lemma rspine_r_scbSubst:
  assumes rs: "rspine_r d c1 t" and c1ne: "c1 \<noteq> Trm []"
    and ptc1: "isPTB_str (flatBT c1)" and ptc2: "isPTB_str (flatBT c2)"
  shows "(rnav ^^ d) (scbSubst c1 c2 t) = c2"
  using rs
proof (induction d arbitrary: t)
  case 0
  hence tc: "t = c1" by simp
  have "scbSubst c1 c2 c1 = c2" by (rule m_8_5_scbSubst_whole[OF c1ne ptc1])
  thus ?case using tc by simp
next
  case (Suc d)
  from \<open>rspine_r (Suc d) c1 t\<close> obtain pre h x where
    t: "t = pre +\<^sub>B Dpt (enat h) x" and rx: "rspine_r d c1 x" by auto
  obtain sx bx where dx: "scb_decomp x sx (flatBT c1) bx"
    using rspine_r_scb_decomp[OF rx c1ne ptc1] by auto
  have xnz: "x \<noteq> Trm []" by (rule rspine_r_nonempty[OF rx c1ne])
  have step: "rnav (scbSubst c1 c2 t) = scbSubst c1 c2 x"
    using rnav_scbSubst_step[OF dx xnz ptc2] t by simp
  have "(rnav ^^ Suc d) (scbSubst c1 c2 t) = (rnav ^^ d) (rnav (scbSubst c1 c2 t))"
    by (simp only: funpow_Suc_right o_apply)
  also have "\<dots> = (rnav ^^ d) (scbSubst c1 c2 x)" using step by simp
  also have "\<dots> = c2" by (rule Suc.IH[OF rx])
  finally show ?case .
qed

lemma rspine_r_funpow_scbSubst_commute:
  assumes rs: "rspine_r d c1 t" and kd: "k \<le> d" and c1ne: "c1 \<noteq> Trm []"
    and ptc1: "isPTB_str (flatBT c1)" and ptc2: "isPTB_str (flatBT c2)"
  shows "(rnav ^^ k) (scbSubst c1 c2 t) = scbSubst c1 c2 ((rnav ^^ k) t)"
  using rs kd
proof (induction k arbitrary: t d)
  case 0 thus ?case by simp
next
  case (Suc k)
  from \<open>Suc k \<le> d\<close> obtain d' where d: "d = Suc d'" by (cases d) auto
  from \<open>rspine_r d c1 t\<close> obtain pre h x where
    t: "t = pre +\<^sub>B Dpt (enat h) x" and rx: "rspine_r d' c1 x" using d by auto
  have kd': "k \<le> d'" using \<open>Suc k \<le> d\<close> d by simp
  obtain sx bx where dx: "scb_decomp x sx (flatBT c1) bx"
    using rspine_r_scb_decomp[OF rx c1ne ptc1] by auto
  have xnz: "x \<noteq> Trm []" by (rule rspine_r_nonempty[OF rx c1ne])
  have step: "rnav (scbSubst c1 c2 t) = scbSubst c1 c2 x"
    using rnav_scbSubst_step[OF dx xnz ptc2] t by simp
  have rnt: "rnav t = x" using t by (simp add: rnav_addBT)
  have "(rnav ^^ Suc k) (scbSubst c1 c2 t) = (rnav ^^ k) (rnav (scbSubst c1 c2 t))"
    by (simp only: funpow_Suc_right o_apply)
  also have "\<dots> = (rnav ^^ k) (scbSubst c1 c2 x)" using step by simp
  also have "\<dots> = scbSubst c1 c2 ((rnav ^^ k) x)" by (rule Suc.IH[OF rx kd'])
  also have "\<dots> = scbSubst c1 c2 ((rnav ^^ Suc k) t)"
    by (simp only: funpow_Suc_right o_apply rnt)
  finally show ?case .
qed

lemma b3b_rnav_fold_drive:
  fixes c1 c2 :: "nat \<Rightarrow> BT" and acc0 :: BT and k w :: nat and dd :: "nat \<Rightarrow> nat"
    and op :: "nat \<Rightarrow> BT \<Rightarrow> BT"
  defines "op \<equiv> (\<lambda>m t. scbSubst (c1 m) (c2 m) t)"
  assumes ladder: "\<And>m. m < w \<Longrightarrow> rspine_r (dd m) (c1 m) (fold op [0..<m] acc0)"
    and dge: "\<And>m. m < w \<Longrightarrow> k \<le> dd m"
    and c1ne: "\<And>m. m < w \<Longrightarrow> c1 m \<noteq> Trm []"
    and pt1: "\<And>m. m < w \<Longrightarrow> isPTB_str (flatBT (c1 m))"
    and pt2: "\<And>m. m < w \<Longrightarrow> isPTB_str (flatBT (c2 m))"
  shows "(rnav ^^ k) (fold op [0..<w] acc0) = fold op [0..<w] ((rnav ^^ k) acc0)"
proof -
  have gen: "\<And>n. n \<le> w \<Longrightarrow> (rnav ^^ k) (fold op [0..<n] acc0)
              = fold op [0..<n] ((rnav ^^ k) acc0)"
  proof -
    fix n
    show "n \<le> w \<Longrightarrow> (rnav ^^ k) (fold op [0..<n] acc0)
            = fold op [0..<n] ((rnav ^^ k) acc0)"
    proof (induction n)
      case 0 thus ?case by simp
    next
      case (Suc n)
      have nlew: "n \<le> w" using Suc.prems by simp
      have nw: "n < w" using Suc.prems by simp
      have foldA: "fold op [0..<Suc n] acc0 = op n (fold op [0..<n] acc0)"
        by (simp add: upt_Suc_append)
      have foldB: "fold op [0..<Suc n] ((rnav ^^ k) acc0)
                     = op n (fold op [0..<n] ((rnav ^^ k) acc0))"
        by (simp add: upt_Suc_append)
      have IH: "(rnav ^^ k) (fold op [0..<n] acc0)
                  = fold op [0..<n] ((rnav ^^ k) acc0)" by (rule Suc.IH[OF nlew])
      have opn: "op n = (\<lambda>t. scbSubst (c1 n) (c2 n) t)" by (simp add: op_def)
      have comm: "(rnav ^^ k) (op n (fold op [0..<n] acc0))
                    = op n ((rnav ^^ k) (fold op [0..<n] acc0))"
      proof -
        have "(rnav ^^ k) (scbSubst (c1 n) (c2 n) (fold op [0..<n] acc0))
                = scbSubst (c1 n) (c2 n) ((rnav ^^ k) (fold op [0..<n] acc0))"
          by (rule rspine_r_funpow_scbSubst_commute[OF ladder[OF nw] dge[OF nw]
                    c1ne[OF nw] pt1[OF nw] pt2[OF nw]])
        thus ?thesis using opn by simp
      qed
      have "(rnav ^^ k) (fold op [0..<Suc n] acc0)
              = (rnav ^^ k) (op n (fold op [0..<n] acc0))" using foldA by simp
      also have "\<dots> = op n ((rnav ^^ k) (fold op [0..<n] acc0))" by (rule comm)
      also have "\<dots> = op n (fold op [0..<n] ((rnav ^^ k) acc0))" using IH by simp
      also have "\<dots> = fold op [0..<Suc n] ((rnav ^^ k) acc0)" using foldB by simp
      finally show ?case .
    qed
  qed
  show ?thesis using gen[of w] by simp
qed

text \<open>§8.5 (B3) — the MARKSTEP SKELETON in the \<open>rnav\<close> metric (the kernel-correct one).
  Since each mark \<open>Mark (M[q]) jm1 = D\<^bsub>e10\<^esub>(U\<^sub>q)\<close> is SINGLE outer-principal,
  \<open>rnav (Mark _) = bpHeadT (Mark _)\<close> (the only principal's subtree).  So the markstep
  \<open>bpHeadT (F acc\<^sub>0) = C (bpHeadT acc\<^sub>0)\<close> collapses through \<open>drive\<close> (\<open>k=1\<close> of
  @{thm [source] b3b_rnav_fold_drive}) to the SINGLE keystone VALUE
  \<open>assembly\<close>: \<open>fold op [0..<w] (rnav acc\<^sub>0) = C (rnav acc\<^sub>0)\<close> — the period column ops
  applied to \<open>U\<^sub>q = rnav acc\<^sub>0\<close> rebuild \<open>C(U\<^sub>q) = U\<^bsub>q+1\<^esub>\<close> (the self-similar value crux, the
  irreducible §8.5 keystone).  \<open>bp0/bp1\<close> (\<open>bpHeadT = rnav\<close> on the single-principal marks)
  are mechanical Mark-shape facts.\<close>

lemma b3_markstep_skeleton_rnav:
  fixes op :: "nat \<Rightarrow> BT \<Rightarrow> BT" and acc0 :: BT and w :: nat and C :: "BT \<Rightarrow> BT"
  assumes drive: "rnav (fold op [0..<w] acc0) = fold op [0..<w] (rnav acc0)"
    and bp1: "bpHeadT (fold op [0..<w] acc0) = rnav (fold op [0..<w] acc0)"
    and bp0: "bpHeadT acc0 = rnav acc0"
    and assembly: "fold op [0..<w] (rnav acc0) = C (rnav acc0)"
  shows "bpHeadT (fold op [0..<w] acc0) = C (bpHeadT acc0)"
proof -
  have "bpHeadT (fold op [0..<w] acc0) = rnav (fold op [0..<w] acc0)" by (rule bp1)
  also have "\<dots> = fold op [0..<w] (rnav acc0)" by (rule drive)
  also have "\<dots> = C (rnav acc0)" by (rule assembly)
  also have "\<dots> = C (bpHeadT acc0)" using bp0 by simp
  finally show ?thesis .
qed


text \<open>§8.5 (B3) — bp0/bp1 discharge: on a SINGLE outer-principal term \<open>bpHeadT = rnav\<close>.
  The genuine kernel mark \<open>Mark (M[q]) jm1 = D\<^bsub>e10\<^esub>(U\<^sub>q)\<close> is single-principal, so \<open>bpHeadT\<close>
  (subtree of the first = only principal) coincides with \<open>rnav\<close> (subtree of the LAST = only
  principal).  This discharges the \<open>bp0\<close>/\<open>bp1\<close> hypotheses of @{thm [source]
  b3_markstep_skeleton_rnav}, leaving the markstep open modulo exactly the depth ladder (B3a)
  and the keystone value \<open>assembly\<close>.\<close>

lemma bpHeadT_eq_rnav:
  assumes "length (untrm t) = 1"
  shows "bpHeadT t = rnav t"
proof -
  obtain p where p: "untrm t = [p]" using assms by (cases "untrm t") auto
  obtain v b where vb: "p = DB v b" by (cases p)
  have t: "t = Trm [DB v b]" using p vb by (cases t) auto
  show ?thesis using t by (simp add: rnav_def)
qed


lemma bpHeadT_rnav_Dpt: "bpHeadT (Dpt (enat v) b) = rnav (Dpt (enat v) b)"
  by (rule bpHeadT_eq_rnav) simp


text \<open>§8.5 keystone anchor (DEPTH face) — the C-wrap is undone by EXACTLY ONE rnav step.
  With the otasm-confirmed clean tower \<open>C z = (D00,D00) +\<^sub>B Dpt 0 z\<close> (the §8.5
  @{thm [source] m_8_5_C_body} shape, \<open>t2 = (D00,D00)\<close>, \<open>vm1 = 0\<close>), \<open>rnav (C z) = z\<close>.
  This is the structural target of the one-oper-step deepening: each C-wrap (= one
  oper-step) adds exactly one rnav-level, so \<open>rnav\<^bsup>k\<^esup> (C\<^bsup>k\<^esup> z) = z\<close> — the tower's
  clean self-similar rnav-nest.  Non-circular (pure @{thm [source] m_8_5_C_body} +
  @{thm [source] rnav_addBT}; does not invoke the markstep).\<close>

lemma m_8_5_C_rnav:
  fixes t2 z :: BT and vm1 v :: nat and s0 b0 :: "Sym list" and C :: "BT \<Rightarrow> BT"
  assumes Cdef: "C = (\<lambda>x. unflatBT (s0 @ Dsym (enat (v - 1)) # flatBT x @ b0))"
    and prene: "untrm t2 \<noteq> []"
    and s0eq: "s0 = liftS t2 []"
    and b0eq: "b0 = [RP]"
    and vm1eq: "vm1 = v - 1"
  shows "rnav (C z) = z"
proof -
  have "C z = t2 +\<^sub>B Dpt (enat vm1) z"
    by (rule m_8_5_C_body[OF Cdef prene s0eq b0eq vm1eq])
  thus ?thesis by (simp add: rnav_addBT)
qed


text \<open>The k-fold C-wrap is undone by k rnav steps — the clean tower rnav-descent
  \<open>rnav\<^bsup>k\<^esup> (C\<^bsup>k\<^esup> z) = z\<close>.  Iterated @{thm [source] m_8_5_C_rnav}; the geometric
  backbone of the depth ladder (each oper-step = one C-wrap = one rnav-level).\<close>

lemma m_8_5_C_rnav_funpow:
  fixes t2 :: BT and v :: nat and s0 b0 :: "Sym list" and C :: "BT \<Rightarrow> BT"
  assumes Cdef: "C = (\<lambda>x. unflatBT (s0 @ Dsym (enat (v - 1)) # flatBT x @ b0))"
    and prene: "untrm t2 \<noteq> []"
    and s0eq: "s0 = liftS t2 []"
    and b0eq: "b0 = [RP]"
  shows "(rnav ^^ k) ((C ^^ k) z) = z"
proof (induction k arbitrary: z)
  case 0 thus ?case by simp
next
  case (Suc k)
  have step: "rnav (C w) = w" for w
    by (rule m_8_5_C_rnav[OF Cdef prene s0eq b0eq refl])
  have "(rnav ^^ Suc k) ((C ^^ Suc k) z) = (rnav ^^ k) (rnav (C ((C ^^ k) z)))"
    by (simp add: funpow_Suc_right funpow_swap1)
  also have "\<dots> = (rnav ^^ k) ((C ^^ k) z)" using step by simp
  also have "\<dots> = z" by (rule Suc.IH)
  finally show ?case .
qed


text \<open>§8.5 EXPOSED-IDENTITY FRAME — the whole pair-sequence termination markstep,
  reduced (mechanized, faithfully) to ONE named, otasm-confirmed, q-independent
  self-similar identity: the WHOLE-PERIOD Trans recurrence
  \<open>bpHeadT (Trans (slice\<^sub>q \<frown> B)) = C (bpHeadT (Trans slice\<^sub>q))\<close>  (= \<open>U\<^bsub>q+1\<^esub> = C(U\<^sub>q)\<close>),
  where \<open>slice\<^sub>q = seg (M[q]) jm1 (Lng (M[q]) - 1)\<close> and \<open>C\<close> is the fixed one-hole
  context of @{thm [source] m_8_5_C_body}.  NO single-column/sub-block decomposition
  works (Mark-core re-deposit, butlast-B preservation, closing-graft \<open>+1\<close> — ALL
  refuted by otasm: every column deepens, so the \<open>+1\<close> nesting EMERGES from the full
  \<open>w\<close>-column composition, owned by no single column).  The identity is EXPOSED as the
  hypothesis \<open>keystone\<close> (not buried): the markstep follows by the GREEN §7.4
  Mark\<open>\<leftrightarrow>\<close>Trans bridge — @{thm [source] m_7_4_Mark_Trans_repr} (\<open>Mark (M[q]) jm1
  = Trans slice\<^sub>q\<close>) and @{thm [source] Mark_iterate_slice_append} (\<open>Mark (M[Suc q]) jm1
  = Trans (slice\<^sub>q \<frown> B)\<close>) — both proven.  So the entire termination descent is
  green-modulo this ONE exposed identity, with no second hidden open.\<close>

lemma m_8_5_markstep_of_Trans_keystone:
  fixes M B :: pairseq and q jm1 :: nat and C :: "BT \<Rightarrow> BT"
  assumes mk_q:  "((M::pairseq)[q], jm1) \<in> Marked"
    and MR_q:    "(M::pairseq)[q] \<in> RT_PS"
    and rng_q:   "jm1 < Lng ((M::pairseq)[q]) - 1"
    and mk_sq:   "((M::pairseq)[Suc q], jm1) \<in> Marked"
    and MR_sq:   "(M::pairseq)[Suc q] \<in> RT_PS"
    and rng_sq:  "jm1 < Lng ((M::pairseq)[Suc q]) - 1"
    and app:     "(M::pairseq)[Suc q] = (M::pairseq)[q] @ B"
    and Mpne:    "0 < Lng ((M::pairseq)[q])"
    and jle:     "jm1 \<le> Lng ((M::pairseq)[q])"
    and keystone: "bpHeadT (Trans (seg ((M::pairseq)[q]) jm1 (Lng ((M::pairseq)[q]) - 1) @ B))
                     = C (bpHeadT (Trans (seg ((M::pairseq)[q]) jm1 (Lng ((M::pairseq)[q]) - 1))))"
  shows "bpHeadT (Mark ((M::pairseq)[Suc q]) jm1) = C (bpHeadT (Mark ((M::pairseq)[q]) jm1))"
proof -
  have r1: "Mark ((M::pairseq)[q]) jm1
              = Trans (seg ((M::pairseq)[q]) jm1 (Lng ((M::pairseq)[q]) - 1))"
    by (rule m_7_4_Mark_Trans_repr[OF mk_q MR_q rng_q])
  have r2: "Mark ((M::pairseq)[Suc q]) jm1
              = Trans (seg ((M::pairseq)[q]) jm1 (Lng ((M::pairseq)[q]) - 1) @ B)"
    by (rule Mark_iterate_slice_append[OF mk_sq MR_sq rng_sq app Mpne jle])
  show ?thesis using keystone r1 r2 by simp
qed

text \<open>§8.5 KEYSTONE\<open>\<rightarrow>\<close>KERNEL bridge — the descent-kernel hypothesis
  @{thm [source] m_8_5_TransCondV_descend_kernel} carries free, namely
  \<open>surgC\<close>: \<open>Trans (slice \<frown> B) = Dpt u (C (bpHeadT (Trans slice)))\<close>, DECOMPOSES
  EXACTLY into the whole-period keystone identity (the bpHeadT face — the EXPOSED
  open of @{thm [source] m_8_5_markstep_of_Trans_keystone}) AND the single-outer-
  principal shape \<open>op\<close> (\<open>Trans (slice \<frown> B)\<close> is one principal of value \<open>u\<close>, body =
  its own bpHeadT — the surgshape face, the marked head \<open>Mark (M[Suc q]) jm1 =
  Dpt e\<^sub>1\<^sub>0 (\<dots>)\<close>).  Pure projection glue: the bpHeadT of a single principal is its
  body, so \<open>op\<close> + keystone \<open>\<Longrightarrow>\<close> surgC.  This pins the §8.5 descent kernel's surgC to
  the SAME single whole-period identity the markstep faithful-close exposes — no
  second value open beyond the marked-head shape \<open>op\<close>.\<close>

lemma m_8_5_surgC_of_keystone:
  fixes X Y\<^sub>0 :: BT and u :: nat and C :: "BT \<Rightarrow> BT"
  assumes op: "X = Dpt (enat u) (bpHeadT X)"
    and keystone: "bpHeadT X = C Y\<^sub>0"
  shows "X = Dpt (enat u) (C Y\<^sub>0)"
proof -
  have "X = Dpt (enat u) (bpHeadT X)" by (rule op)
  also have "Dpt (enat u) (bpHeadT X) = Dpt (enat u) (C Y\<^sub>0)"
    using keystone by simp
  finally show ?thesis .
qed

text \<open>§8.5 op (marked-head single-outer-principal shape) FROM monoT — the SECOND face
  of the descent-kernel's surgC decomposition (@{thm [source] m_8_5_surgC_of_keystone}):
  for a monoT reduced sequence, @{thm [source] m_7_3_Trans_monoT} makes \<open>Trans\<close>
  single-principal and @{thm [source] principal_reconstruct} reads off the
  \<open>Dpt\<close>-shape \<open>op\<close>.  Applied to the marked slice \<open>X = slice \<frown> B\<close>, this discharges the
  kernel's \<open>op\<close> residual down to \<open>monoT (slice \<frown> B)\<close> (the marked-slice monoT, the
  one remaining structural fact besides the keystone).\<close>

lemma m_8_5_op_of_monoT:
  fixes X :: pairseq
  assumes MR: "X \<in> RT_PS" and P0nz: "\<not> zeroT (P X ! 0)" and mono: "monoT X"
  shows "Trans X = Dpt (bpHeadV (Trans X)) (bpHeadT (Trans X))"
proof -
  have "Lng (PB (Trans X)) = 1"
    using m_7_3_Trans_monoT[OF MR P0nz] mono by simp
  thus ?thesis by (rule principal_reconstruct)
qed

end

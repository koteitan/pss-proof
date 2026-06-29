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


end

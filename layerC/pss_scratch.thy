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

end

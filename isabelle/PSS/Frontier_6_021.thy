theory Frontier_6_021
  imports Support_6_004
begin

text \<open>\<open>Joints M ! J\<close> is the (unique) row-0 parent of \<open>FirstNodes M ! J\<close>:
  \<open>(0, Joints M ! J) <\<^bsub>M\<^esub>\<^sup>Next (0, FirstNodes M ! J)\<close>.  (Extracted from the
  \<open>m_6_4_FirstNodes_Joints_mono\<close> development.)\<close>

lemma Joints_parent_nextR:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "nextR M 0 (Joints M ! J) (FirstNodes M ! J)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using JBr by auto
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with brne show False by simp
  qed
  with tb have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have JQ: "J \<le> Lng (P ?N) - 1" using JBr brQ by (cases "P ?N") auto
  have hp: "hasParent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J)"
    using m_6_4_mono_slice_next[OF M _ _ JQ] trlt by auto
  have fnJ: "TrMax M + 1 + IdxSum (P ?N) ! J = FirstNodes M ! J"
    using FirstNodes_nth[OF JBr] brQ by simp
  have hpf: "hasParent M 0 (FirstNodes M ! J)" using hp fnJ by simp
  have aJ_eq: "Joints M ! J = parent M 0 (FirstNodes M ! J)" by (rule Joints_nth[OF JBr])
  have "\<exists>!j0. nextR M 0 j0 (FirstNodes M ! J)" using hpf by (simp add: hasParent_def)
  hence "nextR M 0 (THE j0. nextR M 0 j0 (FirstNodes M ! J)) (FirstNodes M ! J)"
    by (rule theI')
  thus ?thesis using aJ_eq by (simp add: parent_def)
qed

text \<open>m: article [13] key inequality — \<open>M\<^bsub>0,0\<^esub> + Joints M ! J + 1 \<le> (Br M ! J)\<^bsub>0,0\<^esub>\<close>.
  Combines the trunk row-0 growth up to \<open>Joints M ! J\<close>, the strict row-0 jump
  across the parent edge to \<open>FirstNodes M ! J\<close>, and
  @{thm [source] entry_FirstNodes_eq_component}.  This is what keeps \<open>N\<^sub>J\<close>'s new
  first entry strictly below the rest of the branch, i.e. \<open>N\<^sub>J\<close> mono.\<close>

lemma joints_lt_branch_first:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "entry M 0 0 + Joints M ! J + 1 \<le> entry (Br M ! J) 0 0"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have aJTr: "Joints M ! J \<le> TrMax M"
    using m_6_4_FirstNodes_TrMax_Joints[OF M JBr] by simp
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have jL: "Joints M ! J < Lng M" using aJTr tb LMpos by linarith
  have trunk: "entry M 0 0 + Joints M ! J \<le> entry M 0 (Joints M ! J)"
    by (rule trunk_row0_inc[OF MT aJTr jL])
  have nx: "nextR M 0 (Joints M ! J) (FirstNodes M ! J)" by (rule Joints_parent_nextR[OF M JBr])
  have strict: "entry M 0 (Joints M ! J) < entry M 0 (FirstNodes M ! J)"
    using nx by (simp add: nextR_def nextrel0_def)
  have ec: "entry M 0 (FirstNodes M ! J) = entry (Br M ! J) 0 0"
    by (rule entry_FirstNodes_eq_component[OF M JBr])
  show ?thesis using trunk strict ec by simp
qed

text \<open>Each branch component is non-empty and non-multi (it is a \<open>P\<close>-block of the
  branch segment).\<close>

lemma Br_component_nonempty:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "Br M ! J \<noteq> []"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using JBr by auto
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with brne show False by simp
  qed
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  with trne TrMax_bound[OF MT] have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have NL: "0 < Lng ?N" using trlt LMpos by (simp add: Lng_seg)
  have Nne: "?N \<noteq> []" using NL by (metis length_greater_0_conv)
  have mem: "Br M ! J \<in> set (Br M)" using JBr by (simp add: nth_mem)
  show ?thesis using P_blocks_nonempty[OF Nne] brQ mem by auto
qed

lemma Br_component_nonmulti:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "zeroT (Br M ! J) \<or> monoT (Br M ! J)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using JBr by auto
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with brne show False by simp
  qed
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  with trne TrMax_bound[OF MT] have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have NL: "0 < Lng ?N" using trlt LMpos by (simp add: Lng_seg)
  have Nne: "?N \<noteq> []" using NL by (metis length_greater_0_conv)
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have mem: "Br M ! J \<in> set (Br M)" using JBr by (simp add: nth_mem)
  show ?thesis using m_6_2_P_components_1[OF NT] brQ mem by auto
qed

text \<open>List fact: replacing the head leaves later entries unchanged.\<close>

lemma nth_Cons_tl:
  assumes "0 < j" "j < length ys"
  shows "(x # tl ys) ! j = ys ! j"
proof -
  from assms(1) obtain i where i: "j = Suc i" using gr0_implies_Suc by blast
  have "i < length (tl ys)" using assms(2) i by simp
  hence "(tl ys) ! i = ys ! Suc i" by (simp add: nth_tl)
  thus ?thesis using i by simp
qed

text \<open>\<open>N\<^sub>J\<close> (the core-case recursion argument of @{const Red}) and the encoding
  \<open>npJ = n\<^sub>J + 1\<close>.\<close>

definition npJ :: "pairseq \<Rightarrow> nat \<Rightarrow> nat" where
  "npJ M J = (if entry (Br M ! J) 1 0 = 0 then 0
              else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))"

definition NJ :: "pairseq \<Rightarrow> nat \<Rightarrow> pairseq" where
  "NJ M J = (entry M 0 0 + Joints M ! J + 1, entry M 1 0 + npJ M J) # tl (Br M ! J)"

lemma Lng_NJ: "Br M ! J \<noteq> [] \<Longrightarrow> Lng (NJ M J) = Lng (Br M ! J)"
  by (simp add: NJ_def)

lemma entry_NJ_0_0: "entry (NJ M J) 0 0 = entry M 0 0 + Joints M ! J + 1"
  by (simp add: NJ_def entry_def)

lemma entry_NJ_1_0: "entry (NJ M J) 1 0 = entry M 1 0 + npJ M J"
  by (simp add: NJ_def entry_def)

lemma entry_NJ_hi:
  assumes "0 < j" "j < Lng (Br M ! J)"
  shows "entry (NJ M J) 0 j = entry (Br M ! J) 0 j"
proof -
  have "NJ M J ! j = Br M ! J ! j"
    unfolding NJ_def using assms by (rule nth_Cons_tl)
  thus ?thesis by (simp add: entry_def)
qed

text \<open>m: \<open>N\<^sub>J\<close> is non-multi (article [13]): for a core mono \<open>M\<close> and a branch
  index \<open>J\<close>, \<open>\<not> multiT (N\<^sub>J)\<close>.  If \<open>Br M ! J\<close> is zero, \<open>N\<^sub>J\<close> is a length-1 zero
  (core: \<open>M\<^bsub>1,0\<^esub> = 0\<close>, \<open>n\<^sub>J = -1\<close>); otherwise it is mono — its new first entry
  \<open>Joints M ! J + 1 \<le> (Br M ! J)\<^bsub>0,0\<^esub>\<close> stays strictly below the rest of the
  branch (@{thm [source] joints_lt_branch_first} + @{thm [source] monoT_row0_min}).\<close>

lemma NJ_nonmulti:
  assumes M: "M \<in> PT_PS" and core: "entry M 0 0 = 0" "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
  shows "\<not> multiT (NJ M J)"
proof -
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
  have lenNJ: "Lng (NJ M J) = Lng (Br M ! J)" using brJne by (rule Lng_NJ)
  from Br_component_nonmulti[OF M JBr] show ?thesis
  proof
    assume z: "zeroT (Br M ! J)"
    have l1: "Lng (NJ M J) = 1" using z lenNJ by (simp add: zeroT_def)
    have np0: "npJ M J = 0" using z by (simp add: npJ_def zeroT_def)
    have "entry (NJ M J) 1 0 = 0" using core(2) np0 by (simp add: NJ_def entry_def)
    hence "zeroT (NJ M J)" using l1 by (simp add: zeroT_def)
    thus ?thesis by (simp add: multiT_def)
  next
    assume mo: "monoT (Br M ! J)"
    have brJTPS: "Br M ! J \<in> T_PS" using brJne by (simp add: T_PS_def)
    have NJTPS: "NJ M J \<in> T_PS" using brJne by (simp add: T_PS_def NJ_def)
    show ?thesis
    proof (cases "Lng (Br M ! J) = 1")
      case True
      \<comment> \<open>mono length-1 branch: \<open>(Br M ! J)\<^bsub>1,0\<^esub> \<noteq> 0\<close>, so \<open>npJ > 0\<close> and \<open>N\<^sub>J\<close> is a
        length-1 mono.\<close>
      have e10: "entry (Br M ! J) 1 0 \<noteq> 0" using mo True by (auto simp: monoT_def zeroT_def)
      hence np_pos: "0 < npJ M J" by (simp add: npJ_def)
      have l1: "Lng (NJ M J) = 1" using True lenNJ by simp
      have "entry (NJ M J) 1 0 = npJ M J" using core(2) by (simp add: NJ_def entry_def)
      hence nz: "\<not> zeroT (NJ M J)" using np_pos by (simp add: zeroT_def)
      have "leR (NJ M J) 0 0 (Lng (NJ M J) - 1)"
        using l1 by (simp add: leR_def le0_refl)
      hence "monoT (NJ M J)" using nz by (simp add: monoT_def)
      thus ?thesis by (simp add: multiT_def)
    next
      case False
      have brL2: "Lng (Br M ! J) > 1" using brJne False by (cases "Br M ! J") auto
      have nz: "\<not> zeroT (NJ M J)" using lenNJ brL2 by (simp add: zeroT_def)
      have key: "\<forall>j. 0 < j \<and> j \<le> Lng (NJ M J) - 1
                   \<longrightarrow> entry (NJ M J) 0 0 < entry (NJ M J) 0 j"
      proof (intro allI impI)
        fix j assume jb: "0 < j \<and> j \<le> Lng (NJ M J) - 1"
        hence j0: "0 < j" and jle: "j \<le> Lng (NJ M J) - 1" by simp_all
        have jlt: "j < Lng (Br M ! J)" using jle lenNJ brL2 by linarith
        have eNJ0: "entry (NJ M J) 0 0 = Joints M ! J + 1"
          using core(1) by (simp add: NJ_def entry_def)
        have eNJj: "entry (NJ M J) 0 j = entry (Br M ! J) 0 j" using j0 jlt by (rule entry_NJ_hi)
        have K: "Joints M ! J + 1 \<le> entry (Br M ! J) 0 0"
          using joints_lt_branch_first[OF M JBr] core(1) by simp
        have mn: "entry (Br M ! J) 0 0 < entry (Br M ! J) 0 j"
          by (rule monoT_row0_min[OF brJTPS mo j0 jlt])
        show "entry (NJ M J) 0 0 < entry (NJ M J) 0 j" using eNJ0 eNJj K mn by simp
      qed
      have Lpos: "0 < Lng (NJ M J) - 1" using lenNJ brL2 by linarith
      have Llt: "Lng (NJ M J) - 1 < Lng (NJ M J)" using lenNJ brL2 by linarith
      have NJpos: "0 < Lng (NJ M J)" using lenNJ brL2 by linarith
      have "(nextrel0 (NJ M J))\<^sup>*\<^sup>* 0 (Lng (NJ M J) - 1)"
        by (rule le0_build[OF NJTPS Llt Lpos]) (use key in simp)
      hence "le0 (NJ M J) 0 (Lng (NJ M J) - 1)" using Llt NJpos by (simp add: le0_def)
      hence "leR (NJ M J) 0 0 (Lng (NJ M J) - 1)" by (simp add: leR_def)
      hence "monoT (NJ M J)" using nz by (simp add: monoT_def)
      thus ?thesis by (simp add: multiT_def)
    qed
  qed
qed

subsection \<open>The termination measure \<open>\<nu>\<close>\<close>

text \<open>\<open>muMono M\<close>: the core measure for mono/zero sequences.  Core (\<open>hd = (0,0)\<close>):
  \<open>2\<beta>\<close>.  Non-core: \<open>2\<beta>(coreReduce M) + 1\<close>, one above the core element it reduces
  to.  \<open>nu M\<close> lifts it over multi via the \<open>P\<close>-blocks (which are zero/mono by
  @{thm [source] m_6_2_P_components_1}, so \<open>nu\<close> needs no recursion).\<close>

definition muMono :: "pairseq \<Rightarrow> nat" where
  "muMono M = (if entry M 0 0 = 0 \<and> entry M 1 0 = 0 then 2 * betaM M
               else 2 * betaM (coreReduce M) + 1)"

definition nu :: "pairseq \<Rightarrow> nat" where
  "nu M = (if multiT M then 1 + sum_list (map muMono (P M)) else muMono M)"

lemma betaM_pos:
  assumes "M \<in> T_PS"
  shows "1 \<le> betaM M"
proof -
  have L: "Lng M > 0" using assms by (cases M) (auto simp: T_PS_def)
  have T: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF assms])
  from L T show ?thesis unfolding betaM_def by linarith
qed

text \<open>Per-case descent of \<open>nu\<close> along @{const Red}'s recursive calls.\<close>

lemma nu_Pblock_lt:
  assumes M: "M \<in> T_PS" and multi: "multiT M" and x: "x \<in> set (P M)"
  shows "nu x < nu M"
proof -
  have nuM: "nu M = 1 + sum_list (map muMono (P M))" using multi by (simp add: nu_def)
  have x_nm: "\<not> multiT x" using m_6_2_P_components_1[OF M] x by (auto simp: multiT_def)
  have mem: "muMono x \<in> set (map muMono (P M))" using x by simp
  have "nu x = muMono x" using x_nm by (simp add: nu_def)
  also have "muMono x \<le> sum_list (map muMono (P M))" by (rule member_le_sum_list[OF mem]) simp
  finally show ?thesis using nuM by linarith
qed

lemma nu_coreReduce_lt:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
    and noncore: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)"
  shows "nu (coreReduce M) < nu M"
proof -
  have nmM: "\<not> multiT M" using mono by (simp add: multiT_def)
  have muM: "muMono M = 2 * betaM (coreReduce M) + 1"
    unfolding muMono_def by (rule if_not_P[OF noncore])
  have nuM: "nu M = 2 * betaM (coreReduce M) + 1" using nmM muM by (simp add: nu_def)
  have cr_nm: "\<not> multiT (coreReduce M)" by (rule coreReduce_nonmulti[OF M mono])
  have cr_core: "entry (coreReduce M) 0 0 = 0 \<and> entry (coreReduce M) 1 0 = 0"
    by (rule coreReduce_core[OF M])
  have "nu (coreReduce M) = muMono (coreReduce M)" using cr_nm by (simp add: nu_def)
  also have "\<dots> = 2 * betaM (coreReduce M)" using cr_core by (simp add: muMono_def)
  finally show ?thesis using nuM by simp
qed

lemma nu_NJ_lt:
  assumes M: "M \<in> PT_PS" and core: "entry M 0 0 = 0" "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
  shows "nu (NJ M J) < nu M"
proof -
  have MT: "M \<in> T_PS" and mono: "monoT M" using M by (simp_all add: PT_PS_def)
  have nmM: "\<not> multiT M" using mono by (simp add: multiT_def)
  have nuM: "nu M = 2 * betaM M" using nmM core by (simp add: nu_def muMono_def)
  have nj_nm: "\<not> multiT (NJ M J)" by (rule NJ_nonmulti[OF M core JBr])
  have nj_noncore: "\<not> (entry (NJ M J) 0 0 = 0 \<and> entry (NJ M J) 1 0 = 0)"
  proof -
    have "entry (NJ M J) 0 0 = entry M 0 0 + Joints M ! J + 1" by (simp add: NJ_def entry_def)
    thus ?thesis by simp
  qed
  have muNJ: "muMono (NJ M J) = 2 * betaM (coreReduce (NJ M J)) + 1"
    unfolding muMono_def by (rule if_not_P[OF nj_noncore])
  have nuNJ: "nu (NJ M J) = 2 * betaM (coreReduce (NJ M J)) + 1"
    using nj_nm muNJ by (simp add: nu_def)
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
  have NJTPS: "NJ M J \<in> T_PS" using brJne by (simp add: T_PS_def NJ_def)
  have bcr: "betaM (coreReduce (NJ M J)) \<le> Lng (NJ M J)" by (rule betaM_coreReduce_le[OF NJTPS])
  have lenNJ: "Lng (NJ M J) = Lng (Br M ! J)" using brJne by (rule Lng_NJ)
  have brbound: "Lng (Br M ! J) \<le> Lng M - TrMax M - 1" by (rule Lng_Br_le[OF JBr])
  have bpos: "1 \<le> betaM M" by (rule betaM_pos[OF MT])
  have "Lng (NJ M J) \<le> betaM M - 1" using lenNJ brbound by (simp add: betaM_def)
  with bcr bpos show ?thesis using nuNJ nuM by linarith
qed

end

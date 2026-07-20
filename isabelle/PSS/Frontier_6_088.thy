theory Frontier_6_088
  imports P_6_7_standard_reduced
begin

text \<open>§6.5 Front A's stdCA residual and the §6.7 joint RedCond invariant, both now
  unconditional via the same discharged oper-tiling bricks.\<close>

lemma stdCA_ST_PS:
  assumes "M \<in> ST_PS"
  shows "RedCondA M"
  by (rule m_6_5_ST_PS_imp_RedCondA[OF assms operCA_tiling_full operCB_tiling])

section \<open>§6.5 monoCong bricks (towards m_6_5_congR_self_Red_monoT)\<close>

text \<open>§6.5 monoCong, trunk-whole structure brick: a whole-trunk (TrMax = j1)
  RedCondA sequence with zero left end IS the diagonal.  The trunk steps
  @{thm [source] TrMax_trunk_step} give row-1 Next edges j -> j+1; RedCondA pins
  entry1 j = j; the edge's le0 collapses to the single adjacent nextrel0 step
  (index-monotonicity), whose valley at j kills all earlier row-0 parent
  candidates, so RedCondA also pins entry0 j = j.  Closes the trunk-whole branch
  of monoCong: Red M = diagSeq 0 j1 = M, congR by reflexivity.  Verified
  empirically (len <= 4, e <= 3: 0 non-diagSeq trunk-whole instances).\<close>

lemma le0_adjacent_step:
  assumes le: "le0 M j (Suc j)"
  shows "nextrel0 M j (Suc j)"
proof -
  have "(nextrel0 M)\<^sup>*\<^sup>* j (Suc j)" using le by (simp add: le0_def)
  thus ?thesis
  proof (cases rule: converse_rtranclpE)
    case base thus ?thesis by simp
  next
    case (step z)
    have jz: "j < z" using step(1) by (simp add: nextrel0_def)
    have "z \<le> Suc j" by (rule nextrel0_rtrancl_mono[OF step(2)])
    hence zeq: "z = Suc j" using jz by simp
    show ?thesis using step(1) zeq by simp
  qed
qed

text \<open>§6.5 monoCong, shift brick: RedCondA survives the row-0 offset normalization
  shiftRow0 (the m10 = 0, m00 > 0 branch of Red).  Parents are literally equal
  (@{thm [source] congR_nextR} on @{thm [source] congR_self_shiftRow0}); the row-0
  \<open>+1\<close> condition transfers because the uniform subtraction does not truncate
  (@{thm [source] entry0_ge_min}: every row-0 entry is \<ge> the left end).\<close>

lemma RedCondA_shiftRow0:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and condA: "RedCondA M"
  shows "RedCondA (shiftRow0 M)"
proof -
  let ?S = "shiftRow0 M"
  have cong: "congR M ?S" by (rule congR_self_shiftRow0[OF MT mono])
  have nxt: "nextR M = nextR ?S" by (rule congR_nextR[OF cong])
  have hpa: "\<And>i j. hasParent ?S i j = hasParent M i j"
    unfolding hasParent_def using nxt by simp
  have par: "\<And>i j. parent ?S i j = parent M i j"
    unfolding parent_def using nxt by simp
  show ?thesis
  unfolding RedCondA_def
  proof (intro allI impI)
    fix i j1' assume i1: "i \<le> 1" and hpS: "hasParent ?S i j1'"
    have hpM: "hasParent M i j1'" using hpS hpa by simp
    have parR: "nextR M i (parent M i j1') j1'"
      using hpM unfolding hasParent_def parent_def by (rule theI')
    have pj_jL: "parent M i j1' < j1' \<and> j1' < Lng M"
    proof (cases "i = 0")
      case True
      have "nextrel0 M (parent M i j1') j1'" using parR True by (simp add: nextR_def)
      thus ?thesis by (simp add: nextrel0_def)
    next
      case False
      have "nextrel1 M (parent M i j1') j1'" using parR False by (simp add: nextR_def)
      thus ?thesis by (simp add: nextrel1_def)
    qed
    have pj: "parent M i j1' < j1'" and jL: "j1' < Lng M" using pj_jL by auto
    have pL: "parent M i j1' < Lng M" using pj jL by linarith
    have plus1: "entry M i (parent M i j1') + 1 = entry M i j1'"
      using condA i1 hpM unfolding RedCondA_def by blast
    have goal: "entry ?S i (parent M i j1') + 1 = entry ?S i j1'"
    proof (cases "i = 0")
      case True
      have lo_p: "entry M 0 0 \<le> entry M 0 (parent M i j1')"
        by (rule entry0_ge_min[OF MT mono pL])
      have eS_p: "entry ?S 0 (parent M i j1') = entry M 0 (parent M i j1') - entry M 0 0"
        by (rule entry_shiftRow0_0[OF pL])
      have eS_j: "entry ?S 0 j1' = entry M 0 j1' - entry M 0 0"
        by (rule entry_shiftRow0_0[OF jL])
      show ?thesis using True plus1 lo_p eS_p eS_j by simp
    next
      case False
      hence i1': "i = 1" using i1 by simp
      have eS_p: "entry ?S 1 (parent M i j1') = entry M 1 (parent M i j1')"
        by (rule entry_shiftRow0_1[OF pL])
      have eS_j: "entry ?S 1 j1' = entry M 1 j1'"
        by (rule entry_shiftRow0_1[OF jL])
      show ?thesis using i1' plus1 eS_p eS_j by simp
    qed
    show "entry ?S i (parent ?S i j1') + 1 = entry ?S i j1'" using goal par by simp
  qed
qed

lemma trunk_entries_offset:
  assumes MT: "M \<in> T_PS"
    and condA: "RedCondA M"
    and jle: "j \<le> TrMax M"
  shows "entry M 0 j = entry M 0 0 + j \<and> entry M 1 j = entry M 1 0 + j"
proof -
  have step1: "\<And>j'. j' < TrMax M \<Longrightarrow> nextR M 1 j' (j' + 1)"
    by (rule TrMax_trunk_step[OF MT])
  have condA1: "\<And>j. hasParent M 1 j \<Longrightarrow> entry M 1 (parent M 1 j) + 1 = entry M 1 j"
    using condA unfolding RedCondA_def by blast
  have condA0: "\<And>j. hasParent M 0 j \<Longrightarrow> entry M 0 (parent M 0 j) + 1 = entry M 0 j"
    using condA unfolding RedCondA_def by blast
  \<comment> \<open>row-1 entries are the diagonal on the trunk\<close>
  have e1: "\<And>j. j \<le> TrMax M \<Longrightarrow> entry M 1 j = entry M 1 0 + j"
  proof -
    fix j show "j \<le> TrMax M \<Longrightarrow> entry M 1 j = entry M 1 0 + j"
    proof (induct j)
      case 0 show ?case by simp
    next
      case (Suc j)
      have jlt: "j < TrMax M" using Suc.prems by simp
      have nr: "nextR M 1 j (j + 1)" by (rule step1[OF jlt])
      have hp: "hasParent M 1 (j + 1)"
        unfolding hasParent_def using nr nextR1_unique by blast
      have parR: "nextR M 1 (parent M 1 (j + 1)) (j + 1)"
        using hp unfolding hasParent_def parent_def by (rule theI')
      have par: "parent M 1 (j + 1) = j" using parR nr by (rule nextR1_unique)
      have "entry M 1 (parent M 1 (j + 1)) + 1 = entry M 1 (j + 1)" by (rule condA1[OF hp])
      hence "entry M 1 j + 1 = entry M 1 (j + 1)" using par by simp
      thus ?case using Suc.hyps Suc.prems by simp
    qed
  qed
  \<comment> \<open>the trunk edge collapses to the adjacent row-0 step\<close>
  have step0: "\<And>j. j < TrMax M \<Longrightarrow> nextrel0 M j (j + 1)"
  proof -
    fix j assume jlt: "j < TrMax M"
    have nr1: "nextrel1 M j (j + 1)" using step1[OF jlt] by (simp add: nextR_def)
    have "le0 M j (j + 1)" using nr1 by (simp add: nextrel1_def)
    thus "nextrel0 M j (j + 1)" using le0_adjacent_step by simp
  qed
  \<comment> \<open>row-0 entries are the diagonal on the trunk\<close>
  have e0: "\<And>j. j \<le> TrMax M \<Longrightarrow> entry M 0 j = entry M 0 0 + j"
  proof -
    fix j show "j \<le> TrMax M \<Longrightarrow> entry M 0 j = entry M 0 0 + j"
    proof (induct j)
      case 0 show ?case by simp
    next
      case (Suc j)
      have jlt: "j < TrMax M" using Suc.prems by simp
      have nr0: "nextrel0 M j (j + 1)" by (rule step0[OF jlt])
      have e_lt: "entry M 0 j < entry M 0 (j + 1)" using nr0 by (simp add: nextrel0_def)
      have uniq: "\<And>a. nextrel0 M a (j + 1) \<Longrightarrow> a = j"
      proof -
        fix a assume nra: "nextrel0 M a (j + 1)"
        have alt: "a < j + 1" using nra by (simp add: nextrel0_def)
        show "a = j"
        proof (rule ccontr)
          assume "a \<noteq> j"
          hence aj: "a < j" using alt by simp
          have vall: "\<forall>j'. a < j' \<and> j' < j + 1 \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j + 1)"
            using nra unfolding nextrel0_def by blast
          have cond: "a < j \<and> j < j + 1" using aj by simp
          have "entry M 0 j \<ge> entry M 0 (j + 1)" using vall cond by blast
          thus False using e_lt by simp
        qed
      qed
      have nrR: "nextR M 0 j (j + 1)" using nr0 by (simp add: nextR_def)
      have ex1: "\<exists>!a. nextR M 0 a (j + 1)"
      proof (rule ex1I)
        show "nextR M 0 j (j + 1)" by (rule nrR)
      next
        fix a assume "nextR M 0 a (j + 1)"
        hence "nextrel0 M a (j + 1)" by (simp add: nextR_def)
        thus "a = j" by (rule uniq)
      qed
      have hp: "hasParent M 0 (j + 1)" unfolding hasParent_def by (rule ex1)
      have parR: "nextR M 0 (parent M 0 (j + 1)) (j + 1)"
        using hp unfolding hasParent_def parent_def by (rule theI')
      have par: "parent M 0 (j + 1) = j" using parR nrR by (rule idxsum_parent0_unique)
      have "entry M 0 (parent M 0 (j + 1)) + 1 = entry M 0 (j + 1)" by (rule condA0[OF hp])
      hence "entry M 0 j + 1 = entry M 0 (j + 1)" using par by simp
      thus ?case using Suc.hyps Suc.prems by simp
    qed
  qed
  show ?thesis using e0[OF jle] e1[OF jle] by simp
qed

lemma trunk_entries_diag:
  assumes MT: "M \<in> T_PS"
    and condA: "RedCondA M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and jle: "j \<le> TrMax M"
  shows "entry M 0 j = j \<and> entry M 1 j = j"
  using trunk_entries_offset[OF MT condA jle] m00 m10 by simp

lemma monoT_condA_trunkwhole_eq_diagSeq:
  assumes MT: "M \<in> T_PS"
    and condA: "RedCondA M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and tw: "TrMax M = Lng M - 1"
  shows "M = diagSeq 0 (Lng M - 1)"
proof -
  let ?j1 = "Lng M - 1"
  have LM: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  show ?thesis
  proof (rule nth_equalityI)
    show "length M = length (diagSeq 0 ?j1)" using LM by (simp add: diagSeq_def)
  next
    fix j assume jL: "j < length M"
    have jle: "j \<le> ?j1" using jL by (cases M) auto
    have jTr: "j \<le> TrMax M" using jle tw by simp
    have ent: "entry M 0 j = j \<and> entry M 1 j = j"
      by (rule trunk_entries_diag[OF MT condA m00 m10 jTr])
    have fstj: "fst (M ! j) = j" using ent by (simp add: entry_def)
    have sndj: "snd (M ! j) = j" using ent by (simp add: entry_def)
    have Mj: "M ! j = (j, j)" using fstj sndj by (simp add: prod_eq_iff)
    have jlt': "j < Suc ?j1" using jle by simp
    have dj: "diagSeq 0 ?j1 ! j = (j, j)"
      using jlt' by (simp add: diagSeq_def del: upt_Suc)
    show "M ! j = diagSeq 0 ?j1 ! j" using Mj dj by simp
  qed
qed

text \<open>§6.5 monoCong, branches brick: under RedCondA and a zero left end the
  head replacement of \<open>N\<^sub>J\<close> is the IDENTITY -- \<open>NJ M J = Br M ! J\<close>.  The joint
  sits on the trunk (@{thm [source] m_6_4_FirstNodes_TrMax_Joints}) where entries
  equal indices (@{thm [source] trunk_entries_diag}), so RedCondA at the first
  node pins its row-0 value to \<open>Joints!J + 1\<close>; likewise the row-1 parent of the
  first node lies at \<open>p\<^sub>1 \<le> Joints!J \<le> TrMax\<close>
  (@{thm [source] nextR0_largest_below}), so RedCondA pins the row-1 value to
  \<open>Suc p\<^sub>1 = npJ M J\<close>.  Verified empirically (802 branch instances, 0 mismatches).
  This collapses the branches case of monoCong to the branch components
  themselves.\<close>

lemma NJ_eq_BrJ:
  assumes M: "M \<in> PT_PS"
    and condA: "RedCondA M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
  shows "NJ M J = Br M ! J"
proof -
  have MT: "M \<in> T_PS" and monoM: "monoT M" using M by (simp_all add: PT_PS_def)
  let ?f = "FirstNodes M ! J"  let ?jn = "Joints M ! J"
  have fnTr: "?jn \<le> TrMax M \<and> TrMax M < ?f"
    by (rule m_6_4_FirstNodes_TrMax_Joints[OF M JBr])
  have jnTr: "?jn \<le> TrMax M" using fnTr by blast
  have nxJ: "nextR M 0 ?jn ?f" by (rule Joints_parent_nextR[OF M JBr])
  have fL: "?f < Lng M" using nxJ by (simp add: nextR_def nextrel0_def)
  have brne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
  \<comment> \<open>row-0 head value\<close>
  have hp0: "hasParent M 0 ?f"
    unfolding hasParent_def using nxJ idxsum_parent0_unique by blast
  have par0: "parent M 0 ?f = ?jn"
  proof -
    have "nextR M 0 (parent M 0 ?f) ?f"
      using hp0 unfolding hasParent_def parent_def by (rule theI')
    thus ?thesis using nxJ by (rule idxsum_parent0_unique)
  qed
  have e0jn: "entry M 0 ?jn = ?jn"
    using trunk_entries_diag[OF MT condA m00 m10 jnTr] by blast
  have cA0: "entry M 0 (parent M 0 ?f) + 1 = entry M 0 ?f"
    using condA hp0 unfolding RedCondA_def by blast
  have e0f: "entry M 0 ?f = ?jn + 1" using cA0 par0 e0jn by simp
  have head0: "entry (Br M ! J) 0 0 = ?jn + 1"
    using entry_FirstNodes_eq_component_gen[OF M] JBr e0f by simp
  \<comment> \<open>row-1 head value\<close>
  have eBf1: "entry M 1 ?f = entry (Br M ! J) 1 0"
    using entry_FirstNodes_eq_component_gen[OF M] JBr by simp
  have head1: "entry (Br M ! J) 1 0 = npJ M J"
  proof (cases "entry (Br M ! J) 1 0 = 0")
    case True thus ?thesis by (simp add: npJ_def)
  next
    case nzbr: False
    have fpos: "0 < ?f" using fnTr by linarith
    have f1pos: "0 < entry M 1 ?f" using eBf1 nzbr by simp
    have e10_lt: "entry M 1 0 < entry M 1 ?f" using m10 f1pos by simp
    have le00f: "leR M 0 0 ?f"
    proof -
      have root: "leR M 0 0 (Lng M - 1)" using monoM by (simp add: monoT_def)
      have fle: "?f \<le> Lng M - 1" using fL by simp
      show ?thesis by (rule m_5_1_ancestor_tree_1[OF MT root _ fle]) simp
    qed
    obtain p1 where p1b: "p1 < ?f" and p1c: "nextR M 1 p1 ?f"
      using m_5_1_parent_exists_2[OF MT fpos fL e10_lt le00f] by blast
    have ex1: "\<exists>!j. nextR M 1 j ?f" using p1c nextR1_unique by blast
    have the_p1: "(THE j. nextR M 1 j ?f) = p1" by (rule the1_equality[OF ex1 p1c])
    have np: "npJ M J = Suc p1" using nzbr the_p1 by (simp add: npJ_def)
    have le0p1f: "leR M 0 p1 ?f" using p1c by (simp add: nextR_def nextrel1_def leR_def)
    have e0_p1f: "entry M 0 p1 < entry M 0 ?f"
      by (rule m_5_1_ancestor_basic_1[OF MT p1b order.refl le0p1f])
    have p1_le: "p1 \<le> ?jn" by (rule nextR0_largest_below[OF nxJ p1b e0_p1f])
    have p1Tr: "p1 \<le> TrMax M" using p1_le jnTr by linarith
    have e1p1: "entry M 1 p1 = p1"
      using trunk_entries_diag[OF MT condA m00 m10 p1Tr] by blast
    have hp1: "hasParent M 1 ?f" unfolding hasParent_def by (rule ex1)
    have par1: "parent M 1 ?f = p1"
    proof -
      have "nextR M 1 (parent M 1 ?f) ?f"
        using hp1 unfolding hasParent_def parent_def by (rule theI')
      thus ?thesis using p1c by (rule nextR1_unique)
    qed
    have cA1: "entry M 1 (parent M 1 ?f) + 1 = entry M 1 ?f"
      using condA hp1 unfolding RedCondA_def by blast
    have e1f: "entry M 1 ?f = Suc p1" using cA1 par1 e1p1 by simp
    show ?thesis using eBf1 e1f np by simp
  qed
  \<comment> \<open>assemble\<close>
  have hdBr: "Br M ! J = (entry (Br M ! J) 0 0, entry (Br M ! J) 1 0) # tl (Br M ! J)"
  proof -
    have c: "Br M ! J = hd (Br M ! J) # tl (Br M ! J)" using brne by simp
    have "hd (Br M ! J) = (entry (Br M ! J) 0 0, entry (Br M ! J) 1 0)"
      using brne by (cases "Br M ! J") (auto simp: entry_def)
    thus ?thesis using c by simp
  qed
  show ?thesis unfolding NJ_def using m00 m10 head0 head1 hdBr by simp
qed

text \<open>§6.5 monoCong, segment brick: RedCondA restricts to ANY in-bounds segment.
  Parents inside a segment coincide with the ambient parents: the seg nextrel is
  the verbatim restriction (@{thm [source] adm_nextrel0_seg} /
  @{thm [source] adm_nextrel1_seg} -- le0 paths are index-increasing, hence
  window-confined) and parents are globally unique
  (@{thm [source] wf17_nextR_unique}), so the +1 condition transfers through
  @{thm [source] entry_seg}.\<close>

lemma RedCondA_seg:
  assumes bnd: "j1' < Lng M" and condA: "RedCondA M"
  shows "RedCondA (seg M j0' j1')"
proof -
  let ?S = "seg M j0' j1'"
  show ?thesis
  unfolding RedCondA_def
  proof (intro allI impI)
    fix i q assume i1: "i \<le> 1" and hpS: "hasParent ?S i q"
    let ?p = "parent ?S i q"
    have parRS: "nextR ?S i ?p q"
      using hpS unfolding hasParent_def parent_def by (rule theI')
    have pq_b: "?p < q \<and> q < Lng ?S"
    proof (cases "i = 0")
      case True
      have "nextrel0 ?S ?p q" using parRS True by (simp add: nextR_def)
      thus ?thesis by (simp add: nextrel0_def)
    next
      case False
      have "nextrel1 ?S ?p q" using parRS False by (simp add: nextR_def)
      thus ?thesis by (simp add: nextrel1_def)
    qed
    have qS: "q < Lng ?S" and pq: "?p < q" using pq_b by auto
    have pS: "?p < Lng ?S" using pq qS by linarith
    have nrM: "nextR M i (j0' + ?p) (j0' + q)"
    proof (cases "i = 0")
      case True
      have "nextrel0 ?S ?p q" using parRS True by (simp add: nextR_def)
      hence "nextrel0 M (j0' + ?p) (j0' + q)"
        using adm_nextrel0_seg[OF bnd pS qS] by simp
      thus ?thesis using True by (simp add: nextR_def)
    next
      case False
      have "nextrel1 ?S ?p q" using parRS False by (simp add: nextR_def)
      hence "nextrel1 M (j0' + ?p) (j0' + q)"
        using adm_nextrel1_seg[OF bnd pS qS] by simp
      thus ?thesis using False by (simp add: nextR_def)
    qed
    have ex1M: "\<exists>!x. nextR M i x (j0' + q)"
    proof (rule ex1I)
      show "nextR M i (j0' + ?p) (j0' + q)" by (rule nrM)
    next
      fix x assume "nextR M i x (j0' + q)"
      thus "x = j0' + ?p" using nrM by (rule wf17_nextR_unique[OF i1])
    qed
    have hpM: "hasParent M i (j0' + q)" unfolding hasParent_def by (rule ex1M)
    have parM: "parent M i (j0' + q) = j0' + ?p"
      using the1_equality[OF ex1M nrM] by (simp add: parent_def)
    have plus1: "entry M i (parent M i (j0' + q)) + 1 = entry M i (j0' + q)"
      using condA i1 hpM unfolding RedCondA_def by blast
    have eq_p: "entry ?S i ?p = entry M i (j0' + ?p)" using pS by (simp add: entry_seg)
    have eq_q: "entry ?S i q = entry M i (j0' + q)" using qS by (simp add: entry_seg)
    show "entry ?S i (parent ?S i q) + 1 = entry ?S i q"
      using plus1 parM eq_p eq_q by simp
  qed
qed

text \<open>§6.5 monoCong, branch-component brick: RedCondA descends to every branch
  component -- Br M ! J is a segment of a segment of M
  (@{thm [source] m_6_4_P_IdxSum}), so @{thm [source] RedCondA_seg} twice.\<close>

lemma RedCondA_BrJ:
  assumes M: "M \<in> PT_PS"
    and condA: "RedCondA M"
    and JBr: "J < Lng (Br M)"
  shows "RedCondA (Br M ! J)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using JBr by (cases "Br M") auto
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    thus False using brne by simp
  qed
  have trlt: "TrMax M < Lng M - 1" using tb trne by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have LM: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have bndN: "Lng M - 1 < Lng M" using LM by simp
  have condAN: "RedCondA ?N" by (rule RedCondA_seg[OF bndN condA])
  have NL: "Lng ?N = Lng M - 1 - TrMax M" using trlt by simp
  have NLpos: "0 < Lng ?N" using trlt NL by simp
  have Nne: "?N \<noteq> []" using NLpos length_greater_0_conv by blast
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have JN: "J < length (P ?N)" using JBr brQ by simp
  have Jle: "J \<le> Lng (P ?N) - 1" using JN by (cases "P ?N") auto
  have comp: "(P ?N) ! J = seg ?N (IdxSum (P ?N) ! J) (IdxSum (P ?N) ! (J + 1) - 1)"
    by (rule m_6_4_P_IdxSum[OF NT Jle])
  have ub: "IdxSum (P ?N) ! (J + 1) - 1 < Lng ?N"
  proof -
    have j1len: "J + 1 \<le> length (P ?N)" using JN by simp
    have val: "IdxSum (P ?N) ! (J + 1) = sum_list (map length (take (J + 1) (P ?N)))"
      by (rule idxsum_nth[OF j1len])
    have split: "sum_list (map length (P ?N))
                 = sum_list (map length (take (J + 1) (P ?N)))
                   + sum_list (map length (drop (J + 1) (P ?N)))"
      by (metis append_take_drop_id map_append sum_list_append)
    have tot: "sum_list (map length (P ?N)) = Lng ?N"
      using idxsum_concat_P[of ?N] by (metis length_concat)
    have le: "IdxSum (P ?N) ! (J + 1) \<le> Lng ?N" using val split tot by linarith
    show ?thesis using le NLpos by linarith
  qed
  have condABr: "RedCondA ((P ?N) ! J)"
    using comp RedCondA_seg[OF ub condAN] by simp
  show ?thesis using condABr brQ by simp
qed

text \<open>Head values of a branch component, read off @{thm [source] NJ_eq_BrJ}.\<close>

lemma BrJ_head0:
  assumes M: "M \<in> PT_PS"
    and condA: "RedCondA M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
  shows "entry (Br M ! J) 0 0 = Joints M ! J + 1"
  using NJ_eq_BrJ[OF M condA m00 m10 JBr] entry_NJ_0_0[of M J] m00 by simp

lemma BrJ_head1:
  assumes M: "M \<in> PT_PS"
    and condA: "RedCondA M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
  shows "entry (Br M ! J) 1 0 = npJ M J"
  using NJ_eq_BrJ[OF M condA m00 m10 JBr] entry_NJ_1_0[of M J] m10 by simp

text \<open>§6.5 monoCong, per-block identity (the branches-case engine): if the branch
  component satisfies the row-0 rebase closed form (the inductive hypothesis of
  the upcoming m_6_5_Red_rebase), then its \<open>IncrFirst\<close>-lifted reduction is the
  component VERBATIM -- the lift exponent \<open>e\<^sub>J = Joints!J + 1 - npJ = head\<^sub>0 - head\<^sub>1\<close>
  exactly undoes the rebase (@{thm [source] BrJ_head0}, @{thm [source] BrJ_head1},
  bounds @{thm [source] npJ_le_Joints_Suc} and @{thm [source] entry0_ge_min}).\<close>

lemma BrJ_block_identity:
  assumes M: "M \<in> PT_PS"
    and condA: "RedCondA M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
    and IH: "Red (Br M ! J)
             = map (\<lambda>j. (entry (Br M ! J) 0 j - entry (Br M ! J) 0 0
                           + entry (Br M ! J) 1 0,
                         entry (Br M ! J) 1 j))
                   [0..<Lng (Br M ! J)]"
  shows "(IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (Br M ! J)) = Br M ! J"
proof -
  let ?B = "Br M ! J"  let ?h0 = "entry ?B 0 0"  let ?h1 = "entry ?B 1 0"
  let ?e = "Joints M ! J + 1 - npJ M J"
  have h0: "?h0 = Joints M ! J + 1" by (rule BrJ_head0[OF M condA m00 m10 JBr])
  have h1: "?h1 = npJ M J" by (rule BrJ_head1[OF M condA m00 m10 JBr])
  have nple: "npJ M J \<le> Joints M ! J + 1" by (rule npJ_le_Joints_Suc[OF M m10 JBr])
  have h1h0: "?h1 \<le> ?h0" using h0 h1 nple by simp
  have eEq: "?e = ?h0 - ?h1" using h0 h1 by simp
  have brne: "?B \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
  have BT: "?B \<in> T_PS" using brne by (simp add: T_PS_def)
  have Lpos: "0 < Lng ?B" using brne by (cases ?B) auto
  have ge_h0: "\<And>j. j < Lng ?B \<Longrightarrow> ?h0 \<le> entry ?B 0 j"
  proof -
    fix j assume jL: "j < Lng ?B"
    from Br_component_nonmulti[OF M JBr] show "?h0 \<le> entry ?B 0 j"
    proof
      assume "zeroT ?B"
      hence "Lng ?B = 1" by (simp add: zeroT_def)
      hence "j = 0" using jL by simp
      thus ?thesis by simp
    next
      assume "monoT ?B"
      thus ?thesis using entry0_ge_min[OF BT _ jL] by simp
    qed
  qed
  have LRed: "Lng (Red ?B) = Lng ?B" using IH by simp
  show ?thesis
  proof (rule nth_equalityI)
    show "length ((IncrFirst ^^ ?e) (Red ?B)) = length ?B"
      using LRed Lng_funpow_IncrFirst by simp
  next
    fix j assume jL: "j < length ((IncrFirst ^^ ?e) (Red ?B))"
    have jB: "j < Lng ?B" using jL LRed by simp
    have jR: "j < Lng (Red ?B)" using jB LRed by simp
    \<comment> \<open>entries of the reduced component (from the closed form)\<close>
    have eR0: "entry (Red ?B) 0 j = entry ?B 0 j - ?h0 + ?h1"
    proof -
      have "(Red ?B) ! j = (entry ?B 0 j - ?h0 + ?h1, entry ?B 1 j)"
        using IH jB by (simp del: upt_Suc)
      thus ?thesis by (simp add: entry_def)
    qed
    have eR1: "entry (Red ?B) 1 j = entry ?B 1 j"
    proof -
      have "(Red ?B) ! j = (entry ?B 0 j - ?h0 + ?h1, entry ?B 1 j)"
        using IH jB by (simp del: upt_Suc)
      thus ?thesis by (simp add: entry_def)
    qed
    \<comment> \<open>entries after the lift\<close>
    have eL0: "entry ((IncrFirst ^^ ?e) (Red ?B)) 0 j = entry ?B 0 j - ?h0 + ?h1 + ?e"
      using entry_funpow_IncrFirst0[OF jR] eR0 by simp
    have eL1: "entry ((IncrFirst ^^ ?e) (Red ?B)) 1 j = entry ?B 1 j"
      using entry_funpow_IncrFirst1[OF jR] eR1 by simp
    have arith: "entry ?B 0 j - ?h0 + ?h1 + ?e = entry ?B 0 j"
      using ge_h0[OF jB] h1h0 eEq by linarith
    have fstj: "fst (((IncrFirst ^^ ?e) (Red ?B)) ! j) = entry ?B 0 j"
      using eL0 arith by (simp add: entry_def)
    have sndj: "snd (((IncrFirst ^^ ?e) (Red ?B)) ! j) = entry ?B 1 j"
      using eL1 by (simp add: entry_def)
    have rhs: "?B ! j = (entry ?B 0 j, entry ?B 1 j)" by (simp add: entry_def)
    show "((IncrFirst ^^ ?e) (Red ?B)) ! j = ?B ! j"
      using fstj sndj rhs by (simp add: prod_eq_iff)
  qed
qed


text \<open>List reconstruction from entries, and the trunk prefix as a diagonal.\<close>

lemma map_entry_id: "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<Lng M] = M"
proof (rule nth_equalityI)
  show "length (map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<Lng M]) = length M" by simp
next
  fix j assume jL: "j < length (map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<Lng M])"
  have jM: "j < Lng M" using jL by simp
  have "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<Lng M] ! j = (entry M 0 j, entry M 1 j)"
    using jM by (simp del: upt_Suc)
  thus "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<Lng M] ! j = M ! j"
    by (simp add: entry_def prod_eq_iff)
qed

lemma trunk_take_eq_diagSeq:
  assumes MT: "M \<in> T_PS"
    and condA: "RedCondA M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and tlt: "TrMax M < Lng M"
  shows "take (TrMax M + 1) M = diagSeq 0 (TrMax M)"
proof (rule nth_equalityI)
  show "length (take (TrMax M + 1) M) = length (diagSeq 0 (TrMax M))"
    using tlt by (simp add: diagSeq_def)
next
  fix j assume jL: "j < length (take (TrMax M + 1) M)"
  have jle: "j \<le> TrMax M" using jL by simp
  have jM: "j < Lng M" using jle tlt by simp
  have ent: "entry M 0 j = j \<and> entry M 1 j = j"
    by (rule trunk_entries_diag[OF MT condA m00 m10 jle])
  have Mj: "M ! j = (j, j)"
    using ent by (simp add: entry_def prod_eq_iff)
  have tj: "take (TrMax M + 1) M ! j = M ! j" using jL by simp
  have jlt': "j < Suc (TrMax M)" using jle by simp
  have dj: "diagSeq 0 (TrMax M) ! j = (j, j)"
    using jlt' by (simp add: diagSeq_def del: upt_Suc)
  show "take (TrMax M + 1) M ! j = diagSeq 0 (TrMax M) ! j" using tj Mj dj by simp
qed

text \<open>§6.5 monoCong CORE assembly: for a core mono RedCondA sequence, Red is the
  IDENTITY.  Trunk-whole: M is the diagonal (the trunk-whole brick) and Red M is
  that same diagonal.  Branches: each lifted block is the branch component
  verbatim (@{thm [source] NJ_eq_BrJ} + @{thm [source] BrJ_block_identity}, the
  rebase closed form for the strictly shorter component supplied by the
  hypothesis IH), so Red M = take (TrMax+1) M @ drop (TrMax+1) M = M
  (@{thm [source] trunk_take_eq_diagSeq}, @{thm [source] idxsum_concat_P},
  @{thm [source] seg_to_last_eq_drop}).\<close>

lemma Red_rebase_core:
  assumes MT: "M \<in> T_PS"
    and condA: "RedCondA M"
    and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and IH: "\<And>X. Lng X < Lng M \<Longrightarrow> X \<in> T_PS \<Longrightarrow> RedCondA X \<Longrightarrow> \<not> multiT X
              \<Longrightarrow> Red X = map (\<lambda>j. (entry X 0 j - entry X 0 0 + entry X 1 0,
                                     entry X 1 j)) [0..<Lng X]"
  shows "Red M = M"
proof -
  let ?j1 = "Lng M - 1"
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have MPT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  show ?thesis
  proof (cases "TrMax M = ?j1")
    case tw: True
    have Meq: "M = diagSeq 0 ?j1"
      by (rule monoT_condA_trunkwhole_eq_diagSeq[OF MT condA c0 c1 tw])
    have rM: "Red M = diagSeq (entry M 1 0) (entry M 1 0 + ?j1)"
      using Red.psimps[OF dom] nz nmu c0 c1 tw by (simp add: Let_def)
    show ?thesis using rM c1 Meq by simp
  next
    case tne: False
    have tb: "TrMax M \<le> ?j1" by (rule TrMax_bound[OF MT])
    have tlt: "TrMax M < ?j1" using tb tne by linarith
    have tltL: "TrMax M < Lng M" using tlt by linarith
    let ?N = "seg M (TrMax M + 1) ?j1"
    have brQ: "Br M = P ?N" using tne by (simp add: Br_def)
    have NL: "Lng ?N = Lng M - 1 - TrMax M" using tlt by simp
    \<comment> \<open>the psimps branches form, with the blocks folded to npJ/NJ\<close>
    have rM: "Red M = diagSeq 0 (TrMax M)
                @ concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                     (Red (NJ M J))) [0..<Lng (Br M)])"
      using Red.psimps[OF dom] nz nmu c0 c1 tne
      by (simp add: Let_def NJ_def npJ_def)
    \<comment> \<open>each lifted block is the branch component verbatim\<close>
    have blk: "\<And>J. J < Lng (Br M) \<Longrightarrow>
                 (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) = Br M ! J"
    proof -
      fix J assume JBr: "J < Lng (Br M)"
      have brne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF MPT JBr])
      have BT: "Br M ! J \<in> T_PS" using brne by (simp add: T_PS_def)
      have condABr: "RedCondA (Br M ! J)" by (rule RedCondA_BrJ[OF MPT condA JBr])
      have nmBr: "\<not> multiT (Br M ! J)"
        using Br_component_nonmulti[OF MPT JBr] by (auto simp: multiT_def)
      have lb: "Lng (Br M ! J) < Lng M"
      proof -
        have JP: "J < length (P ?N)" using JBr brQ by simp
        have "Lng (Br M ! J) \<le> Lng (concat (P ?N))"
          using length_nth_le_concat[OF JP] brQ by simp
        also have "\<dots> = Lng ?N" using idxsum_concat_P[of ?N] by simp
        also have "\<dots> < Lng M" using NL tlt by linarith
        finally show ?thesis .
      qed
      have IHJ: "Red (Br M ! J)
                 = map (\<lambda>j. (entry (Br M ! J) 0 j - entry (Br M ! J) 0 0
                               + entry (Br M ! J) 1 0,
                             entry (Br M ! J) 1 j)) [0..<Lng (Br M ! J)]"
        by (rule IH[OF lb BT condABr nmBr])
      have nj: "NJ M J = Br M ! J" by (rule NJ_eq_BrJ[OF MPT condA c0 c1 JBr])
      show "(IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) = Br M ! J"
        using BrJ_block_identity[OF MPT condA c0 c1 JBr IHJ] nj by simp
    qed
    have maps: "map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))
                    [0..<Lng (Br M)]
                = map (\<lambda>J. Br M ! J) [0..<Lng (Br M)]"
      by (rule map_cong[OF refl]) (use blk in simp)
    have mapsBr: "map (\<lambda>J. Br M ! J) [0..<Lng (Br M)] = Br M"
      by (simp add: map_nth)
    have ccBr: "concat (Br M) = ?N" using brQ idxsum_concat_P[of ?N] by simp
    have diagTake: "diagSeq 0 (TrMax M) = take (TrMax M + 1) M"
      using trunk_take_eq_diagSeq[OF MT condA c0 c1 tltL] by simp
    have Ndrop: "?N = drop (TrMax M + 1) M"
      by (rule seg_to_last_eq_drop[OF LMpos])
    have "Red M = take (TrMax M + 1) M @ drop (TrMax M + 1) M"
      using rM maps mapsBr ccBr diagTake Ndrop by simp
    thus ?thesis by simp
  qed
qed


text \<open>§6.5 m10>0 bricks (b1, b2): nextrel and RedCondA are invariant under
  iterated IncrFirst (uniform row-0 shift).\<close>

lemma nextrel0_funpow_IncrFirst_eq: "nextrel0 ((IncrFirst ^^ k) M) = nextrel0 M"
  by (induction k) (simp_all add: nextrel0_IncrFirst_eq)

lemma nextrel1_funpow_IncrFirst_eq: "nextrel1 ((IncrFirst ^^ k) M) = nextrel1 M"
  by (induction k) (simp_all add: nextrel1_IncrFirst_eq)

lemma nextR_funpow_IncrFirst_eq: "nextR ((IncrFirst ^^ k) M) = nextR M"
proof (intro ext)
  fix i a b
  show "nextR ((IncrFirst ^^ k) M) i a b = nextR M i a b"
    by (simp add: nextR_def nextrel0_funpow_IncrFirst_eq nextrel1_funpow_IncrFirst_eq)
qed

lemma RedCondA_funpow_IncrFirst:
  assumes condA: "RedCondA M"
  shows "RedCondA ((IncrFirst ^^ k) M)"
proof -
  let ?X = "(IncrFirst ^^ k) M"
  have nxt: "nextR ?X = nextR M" by (rule nextR_funpow_IncrFirst_eq)
  have hpa: "\<And>i j. hasParent ?X i j = hasParent M i j"
    unfolding hasParent_def using nxt by simp
  have par: "\<And>i j. parent ?X i j = parent M i j"
    unfolding parent_def using nxt by simp
  show ?thesis
  unfolding RedCondA_def
  proof (intro allI impI)
    fix i q assume i1: "i \<le> 1" and hpX: "hasParent ?X i q"
    have hpM: "hasParent M i q" using hpX hpa by simp
    have parR: "nextR M i (parent M i q) q"
      using hpM unfolding hasParent_def parent_def by (rule theI')
    have pq_b: "parent M i q < q \<and> q < Lng M"
    proof (cases "i = 0")
      case True
      have "nextrel0 M (parent M i q) q" using parR True by (simp add: nextR_def)
      thus ?thesis by (simp add: nextrel0_def)
    next
      case False
      have "nextrel1 M (parent M i q) q" using parR False by (simp add: nextR_def)
      thus ?thesis by (simp add: nextrel1_def)
    qed
    have qL: "q < Lng M" and pq: "parent M i q < q" using pq_b by auto
    have pL: "parent M i q < Lng M" using pq qL by linarith
    have plus1: "entry M i (parent M i q) + 1 = entry M i q"
      using condA i1 hpM unfolding RedCondA_def by blast
    have goal: "entry ?X i (parent M i q) + 1 = entry ?X i q"
    proof (cases "i = 0")
      case True
      show ?thesis
        using entry_funpow_IncrFirst0[OF pL, of k] entry_funpow_IncrFirst0[OF qL, of k]
              plus1 True by simp
    next
      case False
      hence i1': "i = 1" using i1 by simp
      show ?thesis
        using entry_funpow_IncrFirst1[OF pL, of k] entry_funpow_IncrFirst1[OF qL, of k]
              plus1 i1' by simp
    qed
    show "entry ?X i (parent ?X i q) + 1 = entry ?X i q" using goal par by simp
  qed
qed


text \<open>§6.5 m10>0 brick (b3): TrMax characterization and the trunk of coreReduce.
  The set in TrMax_def is a downward-closed interval, so TrMax is pinned by
  "all steps below t" plus "stop at t"; the stop at TrMax itself is automatic.
  For arg = diagSeq 0 (m-1) @ IncrFirst^m M the trunk runs through the diagonal,
  the junction, and the IncrFirst-shifted image of M's trunk, giving
  TrMax arg = m + TrMax M.\<close>

lemma TrMax_bound_set:
  assumes MT: "M \<in> T_PS"
  shows "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)} \<subseteq> {..Lng M - 1}"
proof
  fix j assume "j \<in> {j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  hence H: "\<forall>j'<j. nextR M 1 j' (j' + 1)" by simp
  have LM: "Lng M > 0" using MT by (cases M) (auto simp: T_PS_def)
  show "j \<in> {..Lng M - 1}"
  proof (rule ccontr)
    assume "j \<notin> {..Lng M - 1}"
    hence "Lng M - 1 < j" by simp
    hence "nextR M 1 (Lng M - 1) ((Lng M - 1) + 1)" using H by blast
    hence "(Lng M - 1) + 1 < Lng M" by (simp add: nextR_def nextrel1_def)
    thus False using LM by simp
  qed
qed

lemma TrMax_eqI_endpoint:
  assumes MT: "M \<in> T_PS"
    and steps: "\<And>j'. j' < t \<Longrightarrow> nextR M 1 j' (j' + 1)"
    and stop: "t = Lng M - 1 \<or> \<not> nextR M 1 t (t + 1)"
  shows "TrMax M = t"
proof -
  let ?S = "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  have sub: "?S \<subseteq> {..Lng M - 1}" by (rule TrMax_bound_set[OF MT])
  have fin: "finite ?S" using sub by (rule finite_subset) simp
  have tS: "t \<in> ?S" using steps by simp
  have ne: "?S \<noteq> {}" using tS by blast
  have tmax: "TrMax M = Max ?S" by (simp add: TrMax_def)
  have ge: "t \<le> Max ?S" using fin tS by (rule Max_ge)
  have le: "Max ?S \<le> t"
  proof (rule ccontr)
    assume "\<not> Max ?S \<le> t"
    hence tlt: "t < Max ?S" by simp
    have MS: "Max ?S \<in> ?S" using fin ne by (rule Max_in)
    hence allst: "\<forall>j'<Max ?S. nextR M 1 j' (j' + 1)" by simp
    have stept: "nextR M 1 t (t + 1)" using allst tlt by blast
    from stop show False
    proof
      assume tj1: "t = Lng M - 1"
      have "Max ?S \<le> Lng M - 1" using MS sub by auto
      thus False using tlt tj1 by simp
    next
      assume "\<not> nextR M 1 t (t + 1)"
      thus False using stept by simp
    qed
  qed
  show ?thesis using tmax ge le by simp
qed

lemma TrMax_stop_uncond:
  assumes MT: "M \<in> T_PS"
  shows "\<not> nextR M 1 (TrMax M) (TrMax M + 1)"
proof
  assume step: "nextR M 1 (TrMax M) (TrMax M + 1)"
  let ?S = "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  have sub: "?S \<subseteq> {..Lng M - 1}" by (rule TrMax_bound_set[OF MT])
  have fin: "finite ?S" using sub by (rule finite_subset) simp
  have ne: "?S \<noteq> {}" by blast
  have MS: "Max ?S \<in> ?S" using fin ne by (rule Max_in)
  have tmax: "TrMax M = Max ?S" by (simp add: TrMax_def)
  have allst: "\<forall>j'<TrMax M. nextR M 1 j' (j' + 1)" using MS tmax by simp
  have inS: "TrMax M + 1 \<in> ?S"
  proof -
    have "\<forall>j'<TrMax M + 1. nextR M 1 j' (j' + 1)"
    proof (intro allI impI)
      fix j' assume "j' < TrMax M + 1"
      hence "j' < TrMax M \<or> j' = TrMax M" by linarith
      thus "nextR M 1 j' (j' + 1)" using allst step by blast
    qed
    thus ?thesis by simp
  qed
  have "TrMax M + 1 \<le> Max ?S" using fin inS by (rule Max_ge)
  thus False using tmax by simp
qed

lemma TrMax_coreReduce:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M" and mono: "monoT M"
    and pos: "0 < entry M 1 0"
  shows "TrMax (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M)
         = entry M 1 0 + TrMax M"
proof -
  let ?m = "entry M 1 0"
  let ?Y = "(IncrFirst ^^ ?m) M"
  let ?A = "diagSeq 0 (?m - 1) @ ?Y"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
  have LY: "Lng ?Y = Lng M" by simp
  have LA: "Lng ?A = ?m + Lng M" using Ld LY by simp
  have LApos: "0 < Lng ?A" using LA LMpos by simp
  have Ane: "?A \<noteq> []" using LApos length_greater_0_conv by blast
  have AT: "?A \<in> T_PS" using Ane by (simp add: T_PS_def)
  \<comment> \<open>entries of A: diagonal prefix and shifted tail\<close>
  have eApre: "\<And>i p. p < ?m \<Longrightarrow> entry ?A i p = p"
  proof -
    fix i p assume pm: "p < ?m"
    have "?A ! p = diagSeq 0 (?m - 1) ! p" using pm Ld by (simp add: nth_append)
    also have "\<dots> = (p, p)" using pm pos by (simp add: diagSeq_def del: upt_Suc)
    finally show "entry ?A i p = p" by (simp add: entry_def)
  qed
  have eAtail: "\<And>i k. k < Lng M \<Longrightarrow> entry ?A i (?m + k) = entry ?Y i k"
  proof -
    fix i k assume kM: "k < Lng M"
    have "?A ! (?m + k) = ?Y ! k" using Ld by (simp add: nth_append)
    thus "entry ?A i (?m + k) = entry ?Y i k" by (simp add: entry_def)
  qed
  \<comment> \<open>the M-part steps transfer through seg = drop and the IncrFirst invariance\<close>
  have dropA: "drop ?m ?A = ?Y" using Ld by simp
  have segA: "seg ?A ?m (Lng ?A - 1) = ?Y"
    using seg_to_last_eq_drop[of ?A ?m] LA LMpos dropA by simp
  have transfer: "\<And>k k'. k < Lng M \<Longrightarrow> k' < Lng M \<Longrightarrow>
                   nextrel1 ?A (?m + k) (?m + k') = nextrel1 M k k'"
  proof -
    fix k k' assume kM: "k < Lng M" and kM': "k' < Lng M"
    have bnd: "Lng ?A - 1 < Lng ?A" using LA LMpos by simp
    have kS: "k < Lng (seg ?A ?m (Lng ?A - 1))" using segA kM by simp
    have kS': "k' < Lng (seg ?A ?m (Lng ?A - 1))" using segA kM' by simp
    have "nextrel1 (seg ?A ?m (Lng ?A - 1)) k k' = nextrel1 ?A (?m + k) (?m + k')"
      by (rule adm_nextrel1_seg[OF bnd kS kS'])
    moreover have "nextrel1 (seg ?A ?m (Lng ?A - 1)) k k' = nextrel1 M k k'"
      using segA nextrel1_funpow_IncrFirst_eq[of ?m M] by simp
    ultimately show "nextrel1 ?A (?m + k) (?m + k') = nextrel1 M k k'" by simp
  qed
  \<comment> \<open>steps below m + TrMax M\<close>
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have steps: "\<And>j'. j' < ?m + TrMax M \<Longrightarrow> nextR ?A 1 j' (j' + 1)"
  proof -
    fix j' assume jlt: "j' < ?m + TrMax M"
    show "nextR ?A 1 j' (j' + 1)"
    proof (cases "j' + 1 < ?m")
      case True
      \<comment> \<open>inside the diagonal prefix\<close>
      have jA: "j' < Lng ?A" and jA1: "j' + 1 < Lng ?A" using True LA by simp_all
      have e0: "entry ?A 0 j' = j'" and e0': "entry ?A 0 (j' + 1) = j' + 1"
        using eApre True by simp_all
      have e1: "entry ?A 1 j' = j'" and e1': "entry ?A 1 (j' + 1) = j' + 1"
        using eApre True by simp_all
      have nr0: "nextrel0 ?A j' (j' + 1)"
        unfolding nextrel0_def using jA jA1 e0 e0' by simp
      have le0j: "le0 ?A j' (j' + 1)"
        unfolding le0_def using jA jA1 nr0 by (blast intro: r_into_rtranclp)
      have vall: "\<forall>j''. j' < j'' \<and> le0 ?A j'' (j' + 1) \<longrightarrow>
                    entry ?A 1 j'' \<ge> entry ?A 1 (j' + 1)"
      proof (intro allI impI)
        fix j'' assume H: "j' < j'' \<and> le0 ?A j'' (j' + 1)"
        have "j'' \<le> j' + 1" using H nextrel0_rtrancl_mono[of ?A j'' "j' + 1"]
          by (simp add: le0_def)
        hence "j'' = j' + 1" using H by simp
        thus "entry ?A 1 j'' \<ge> entry ?A 1 (j' + 1)" by simp
      qed
      have "nextrel1 ?A j' (j' + 1)"
        unfolding nextrel1_def using jA jA1 e1 e1' le0j vall by simp
      thus ?thesis by (simp add: nextR_def)
    next
      case False
      show ?thesis
      proof (cases "j' < ?m")
        case True
        \<comment> \<open>the junction step m-1 -> m\<close>
        have jeq: "j' = ?m - 1" using True False by linarith
        have j1eq: "j' + 1 = ?m" using jeq pos by simp
        have jA: "j' < Lng ?A" using True LA by simp
        have jA1: "j' + 1 < Lng ?A" using j1eq LA LMpos by simp
        have e0: "entry ?A 0 j' = j'" and e1: "entry ?A 1 j' = j'"
          using eApre True by simp_all
        have e0': "entry ?A 0 (j' + 1) = entry M 0 0 + ?m"
          using eAtail[OF LMpos, of 0] j1eq entry_funpow_IncrFirst0[OF LMpos] by simp
        have e1': "entry ?A 1 (j' + 1) = ?m"
          using eAtail[OF LMpos, of 1] j1eq entry_funpow_IncrFirst1[OF LMpos] by simp
        have lt0: "entry ?A 0 j' < entry ?A 0 (j' + 1)" using e0 e0' jeq pos by simp
        have lt1: "entry ?A 1 j' < entry ?A 1 (j' + 1)" using e1 e1' jeq pos by simp
        have nr0: "nextrel0 ?A j' (j' + 1)"
          unfolding nextrel0_def using jA jA1 lt0 by simp
        have le0j: "le0 ?A j' (j' + 1)"
          unfolding le0_def using jA jA1 nr0 by (blast intro: r_into_rtranclp)
        have vall: "\<forall>j''. j' < j'' \<and> le0 ?A j'' (j' + 1) \<longrightarrow>
                      entry ?A 1 j'' \<ge> entry ?A 1 (j' + 1)"
        proof (intro allI impI)
          fix j'' assume H: "j' < j'' \<and> le0 ?A j'' (j' + 1)"
          have "j'' \<le> j' + 1" using H nextrel0_rtrancl_mono[of ?A j'' "j' + 1"]
            by (simp add: le0_def)
          hence "j'' = j' + 1" using H by simp
          thus "entry ?A 1 j'' \<ge> entry ?A 1 (j' + 1)" by simp
        qed
        have "nextrel1 ?A j' (j' + 1)"
          unfolding nextrel1_def using jA jA1 lt1 le0j vall by simp
        thus ?thesis by (simp add: nextR_def)
      next
        case mle: False
        \<comment> \<open>inside the M-part: transfer M's trunk step\<close>
        have jge: "?m \<le> j'" using mle by simp
        define k where "k = j' - ?m"
        have jk: "j' = ?m + k" using jge k_def by simp
        have klt: "k < TrMax M" using jlt jk by simp
        have kM: "k < Lng M" using klt tb LMpos by linarith
        have kM1: "k + 1 < Lng M"
        proof -
          have "k + 1 \<le> TrMax M" using klt by simp
          thus ?thesis using tb LMpos
            using TrMax_trunk_step[OF MT klt] by (simp add: nextR_def nextrel1_def)
        qed
        have stepM: "nextR M 1 k (k + 1)" by (rule TrMax_trunk_step[OF MT klt])
        have "nextrel1 M k (k + 1)" using stepM by (simp add: nextR_def)
        hence "nextrel1 ?A (?m + k) (?m + k + 1)"
          using transfer[OF kM kM1] by simp
        thus ?thesis using jk by (simp add: nextR_def)
      qed
    qed
  qed
  \<comment> \<open>stop at m + TrMax M\<close>
  have stop: "?m + TrMax M = Lng ?A - 1 \<or> \<not> nextR ?A 1 (?m + TrMax M) (?m + TrMax M + 1)"
  proof (cases "TrMax M = Lng M - 1")
    case True
    have "?m + TrMax M = Lng ?A - 1" using True LA LMpos by linarith
    thus ?thesis by blast
  next
    case False
    have tlt: "TrMax M < Lng M - 1" using tb False by linarith
    have tM: "TrMax M < Lng M" using tlt by linarith
    have tM1: "TrMax M + 1 < Lng M" using tlt by linarith
    have nstepM: "\<not> nextR M 1 (TrMax M) (TrMax M + 1)" by (rule TrMax_stop_uncond[OF MT])
    have "\<not> nextrel1 ?A (?m + TrMax M) (?m + TrMax M + 1)"
      using transfer[OF tM tM1] nstepM by (simp add: nextR_def)
    thus ?thesis by (simp add: nextR_def)
  qed
  show ?thesis by (rule TrMax_eqI_endpoint[OF AT steps stop])
qed


text \<open>§6.5 m10>0 brick (b4): the branch decomposition of coreReduce is the
  IncrFirst-shifted branch decomposition of M, with FirstNodes and Joints
  shifted by m.\<close>

lemma funpow_IncrFirst_drop:
  "drop k ((IncrFirst ^^ n) X) = (IncrFirst ^^ n) (drop k X)"
  by (induction n) (simp_all add: IncrFirst_def drop_map)

lemma length_funpow_IncrFirst: "length ((IncrFirst ^^ n) X) = length X"
  by (induction n) (simp_all add: IncrFirst_def)

lemma IdxSum_map_funpow_IncrFirst:
  "IdxSum (map (IncrFirst ^^ n) Q) = IdxSum Q"
proof -
  have lens: "map length (map (IncrFirst ^^ n) Q) = map length Q"
  proof (rule nth_equalityI)
    show "length (map length (map (IncrFirst ^^ n) Q)) = length (map length Q)" by simp
  next
    fix i assume "i < length (map length (map (IncrFirst ^^ n) Q))"
    hence iQ: "i < length Q" by simp
    show "map length (map (IncrFirst ^^ n) Q) ! i = map length Q ! i"
      using iQ length_funpow_IncrFirst by simp
  qed
  show ?thesis
    unfolding IdxSum_def
  proof (rule map_cong)
    show "[0..<Suc (length (map (IncrFirst ^^ n) Q))] = [0..<Suc (length Q)]" by simp
  next
    fix J assume "J \<in> set [0..<Suc (length Q)]"
    have "map length (take J (map (IncrFirst ^^ n) Q))
          = take J (map length (map (IncrFirst ^^ n) Q))" by (simp add: take_map)
    also have "\<dots> = take J (map length Q)" by (rule arg_cong[OF lens])
    also have "\<dots> = map length (take J Q)" by (simp add: take_map)
    finally show "sum_list (map length (take J (map (IncrFirst ^^ n) Q)))
                  = sum_list (map length (take J Q))" by simp
  qed
qed

lemma Br_coreReduce:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M" and mono: "monoT M"
    and pos: "0 < entry M 1 0"
  shows "Br (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M)
         = map (IncrFirst ^^ entry M 1 0) (Br M)"
proof -
  let ?m = "entry M 1 0"
  let ?Y = "(IncrFirst ^^ ?m) M"
  let ?A = "diagSeq 0 (?m - 1) @ ?Y"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
  have LA: "Lng ?A = ?m + Lng M" using Ld by simp
  have trA: "TrMax ?A = ?m + TrMax M" by (rule TrMax_coreReduce[OF MT condA mono pos])
  show ?thesis
  proof (cases "TrMax M = Lng M - 1")
    case True
    have aw: "TrMax ?A = Lng ?A - 1" using trA True LA LMpos by linarith
    have "Br ?A = []" using aw by (simp add: Br_def)
    moreover have "Br M = []" using True by (simp add: Br_def)
    ultimately show ?thesis by simp
  next
    case False
    have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
    have tlt: "TrMax M < Lng M - 1" using tb False by linarith
    have awne: "TrMax ?A \<noteq> Lng ?A - 1" using trA LA LMpos tlt by linarith
    have brA: "Br ?A = P (seg ?A (TrMax ?A + 1) (Lng ?A - 1))"
      using awne by (simp add: Br_def)
    have LApos: "0 < Lng ?A" using LA LMpos by simp
    have segdropA: "seg ?A (TrMax ?A + 1) (Lng ?A - 1) = drop (TrMax ?A + 1) ?A"
      by (rule seg_to_last_eq_drop[OF LApos])
    have dropsplit: "drop (TrMax ?A + 1) ?A = drop (TrMax M + 1) ?Y"
      using trA Ld by simp
    have dropY: "drop (TrMax M + 1) ?Y = (IncrFirst ^^ ?m) (drop (TrMax M + 1) M)"
      by (rule funpow_IncrFirst_drop)
    have segdropM: "seg M (TrMax M + 1) (Lng M - 1) = drop (TrMax M + 1) M"
      by (rule seg_to_last_eq_drop[OF LMpos])
    have brM: "Br M = P (seg M (TrMax M + 1) (Lng M - 1))"
      using False by (simp add: Br_def)
    have "Br ?A = P ((IncrFirst ^^ ?m) (seg M (TrMax M + 1) (Lng M - 1)))"
      using brA segdropA dropsplit dropY segdropM by simp
    also have "\<dots> = map (IncrFirst ^^ ?m) (P (seg M (TrMax M + 1) (Lng M - 1)))"
      by (rule P_funpow_IncrFirst)
    finally show ?thesis using brM by simp
  qed
qed

lemma FirstNodes_coreReduce:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M" and mono: "monoT M"
    and pos: "0 < entry M 1 0"
  shows "FirstNodes (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M)
         = map ((+) (entry M 1 0)) (FirstNodes M)"
proof -
  let ?m = "entry M 1 0"
  let ?A = "diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
  have brA: "Br ?A = map (IncrFirst ^^ ?m) (Br M)"
    by (rule Br_coreReduce[OF MT condA mono pos])
  have idx: "IdxSum (Br ?A) = IdxSum (Br M)"
    using brA IdxSum_map_funpow_IncrFirst by simp
  have trA: "TrMax ?A = ?m + TrMax M" by (rule TrMax_coreReduce[OF MT condA mono pos])
  have "FirstNodes ?A = map (\<lambda>x. TrMax ?A + 1 + x) (IdxSum (Br ?A))"
    by (simp add: FirstNodes_def)
  also have "\<dots> = map (\<lambda>x. TrMax ?A + 1 + x) (IdxSum (Br M))"
    using idx by simp
  also have "\<dots> = map (\<lambda>x. (?m + TrMax M) + 1 + x) (IdxSum (Br M))"
    using trA by simp
  also have "\<dots> = map (\<lambda>x. ?m + (TrMax M + 1 + x)) (IdxSum (Br M))"
    by (rule map_cong[OF refl]) simp
  also have "\<dots> = map ((+) ?m) (map (\<lambda>x. TrMax M + 1 + x) (IdxSum (Br M)))"
    by (simp add: o_def)
  finally show ?thesis by (simp add: FirstNodes_def)
qed

lemma coreReduce_nextrel0_transfer:
  assumes MT: "M \<in> T_PS" and pos: "0 < entry M 1 0"
    and kM: "k < Lng M" and kM': "k' < Lng M"
  shows "nextrel0 (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M)
            (entry M 1 0 + k) (entry M 1 0 + k')
         = nextrel0 M k k'"
proof -
  let ?m = "entry M 1 0"
  let ?Y = "(IncrFirst ^^ ?m) M"
  let ?A = "diagSeq 0 (?m - 1) @ ?Y"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
  have LA: "Lng ?A = ?m + Lng M" using Ld by simp
  have dropA: "drop ?m ?A = ?Y" using Ld by simp
  have segA: "seg ?A ?m (Lng ?A - 1) = ?Y"
    using seg_to_last_eq_drop[of ?A ?m] LA LMpos dropA by simp
  have bnd: "Lng ?A - 1 < Lng ?A" using LA LMpos by simp
  have kS: "k < Lng (seg ?A ?m (Lng ?A - 1))" using segA kM by simp
  have kS': "k' < Lng (seg ?A ?m (Lng ?A - 1))" using segA kM' by simp
  have "nextrel0 (seg ?A ?m (Lng ?A - 1)) k k' = nextrel0 ?A (?m + k) (?m + k')"
    by (rule adm_nextrel0_seg[OF bnd kS kS'])
  moreover have "nextrel0 (seg ?A ?m (Lng ?A - 1)) k k' = nextrel0 M k k'"
    using segA nextrel0_funpow_IncrFirst_eq[of ?m M] by simp
  ultimately show ?thesis by simp
qed

lemma Joints_coreReduce:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M" and mono: "monoT M"
    and pos: "0 < entry M 1 0"
    and JBr: "J < Lng (Br M)"
  shows "Joints (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M) ! J
         = entry M 1 0 + Joints M ! J"
proof -
  let ?m = "entry M 1 0"
  let ?A = "diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
  have MPT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  let ?fn = "FirstNodes M ! J"  let ?jn = "Joints M ! J"
  have nxM: "nextR M 0 ?jn ?fn" by (rule Joints_parent_nextR[OF MPT JBr])
  have nr0M: "nextrel0 M ?jn ?fn" using nxM by (simp add: nextR_def)
  have jnM: "?jn < Lng M" and fnM: "?fn < Lng M"
    using nr0M by (simp_all add: nextrel0_def)
  have nr0A: "nextrel0 ?A (?m + ?jn) (?m + ?fn)"
    using coreReduce_nextrel0_transfer[OF MT pos jnM fnM] nr0M by simp
  have nxA: "nextR ?A 0 (?m + ?jn) (?m + ?fn)" using nr0A by (simp add: nextR_def)
  have ex1A: "\<exists>!x. nextR ?A 0 x (?m + ?fn)"
  proof (rule ex1I)
    show "nextR ?A 0 (?m + ?jn) (?m + ?fn)" by (rule nxA)
  next
    fix x assume "nextR ?A 0 x (?m + ?fn)"
    thus "x = ?m + ?jn" using nxA by (rule idxsum_parent0_unique)
  qed
  have brA: "Br ?A = map (IncrFirst ^^ ?m) (Br M)"
    by (rule Br_coreReduce[OF MT condA mono pos])
  have JA: "J < length (Br ?A)" using JBr brA by simp
  have fnA: "FirstNodes ?A ! J = ?m + ?fn"
  proof -
    have fnmap: "FirstNodes ?A = map ((+) ?m) (FirstNodes M)"
      by (rule FirstNodes_coreReduce[OF MT condA mono pos])
    have lenFN: "J < length (FirstNodes M)"
      using JBr by (simp add: FirstNodes_def IdxSum_def)
    show ?thesis using fnmap lenFN by simp
  qed
  have "Joints ?A ! J = (THE x. nextR ?A 0 x (FirstNodes ?A ! J))"
    using JA by (simp add: Joints_def)
  also have "\<dots> = (THE x. nextR ?A 0 x (?m + ?fn))" using fnA by simp
  also have "\<dots> = ?m + ?jn" by (rule the1_equality[OF ex1A nxA])
  finally show ?thesis .
qed


text \<open>§6.5 m10>0 helpers for b5: le0 transfers between the M-part of coreReduce
  and M, the trunk of coreReduce is a row-0 chain, and trunk row-1 entries of
  coreReduce equal their index.\<close>

lemma coreReduce_le0_back:
  assumes MT: "M \<in> T_PS" and pos: "0 < entry M 1 0"
    and kM': "k' < Lng M"
    and r: "le0 (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M)
              (entry M 1 0 + k) (entry M 1 0 + k')"
  shows "le0 M k k'"
proof -
  let ?m = "entry M 1 0"
  let ?A = "diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have bndA: "?m + k < Lng ?A \<and> ?m + k' < Lng ?A \<and> (nextrel0 ?A)\<^sup>*\<^sup>* (?m + k) (?m + k')"
    using r by (simp add: le0_def)
  have kM: "k < Lng M"
  proof -
    have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
    have "?m + k < ?m + Lng M" using bndA Ld by simp
    thus ?thesis by simp
  qed
  have main: "\<And>z. (nextrel0 ?A)\<^sup>*\<^sup>* z (?m + k')
                \<Longrightarrow> ?m \<le> z \<longrightarrow> (nextrel0 M)\<^sup>*\<^sup>* (z - ?m) k'"
  proof -
    fix z assume "(nextrel0 ?A)\<^sup>*\<^sup>* z (?m + k')"
    thus "?m \<le> z \<longrightarrow> (nextrel0 M)\<^sup>*\<^sup>* (z - ?m) k'"
    proof (induction rule: converse_rtranclp_induct)
      case base show ?case by simp
    next
      case (step z w)
      show ?case
      proof (intro impI)
        assume mz: "?m \<le> z"
        have zw: "z < w" using step.hyps(1) by (simp add: nextrel0_def)
        have wb: "w \<le> ?m + k'" using step.hyps(2) nextrel0_rtrancl_mono by blast
        have mw: "?m \<le> w" using mz zw by linarith
        have zM: "z - ?m < Lng M" using zw wb kM' mz by linarith
        have wM: "w - ?m < Lng M" using wb kM' mw by linarith
        have zsplit: "z = ?m + (z - ?m)" using mz by simp
        have wsplit: "w = ?m + (w - ?m)" using mw by simp
        have st: "nextrel0 ?A (?m + (z - ?m)) (?m + (w - ?m))"
          using step.hyps(1) zsplit wsplit by simp
        have "nextrel0 M (z - ?m) (w - ?m)"
          using coreReduce_nextrel0_transfer[OF MT pos zM wM] st by simp
        moreover have "(nextrel0 M)\<^sup>*\<^sup>* (w - ?m) k'" using step.IH mw by simp
        ultimately show "(nextrel0 M)\<^sup>*\<^sup>* (z - ?m) k'"
          by (rule converse_rtranclp_into_rtranclp)
      qed
    qed
  qed
  have "(nextrel0 M)\<^sup>*\<^sup>* k k'"
  proof -
    have "?m \<le> ?m + k" by simp
    moreover have "(nextrel0 ?A)\<^sup>*\<^sup>* (?m + k) (?m + k')" using bndA by blast
    ultimately have "(nextrel0 M)\<^sup>*\<^sup>* ((?m + k) - ?m) k'" using main by blast
    thus ?thesis by simp
  qed
  thus ?thesis using kM kM' by (simp add: le0_def)
qed

end

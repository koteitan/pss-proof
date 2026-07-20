theory Frontier_6_068
  imports Support_6_047
begin

text \<open>\<S>6.6 KEYSTONE BACKWARD core-nontrunk per-branch, BRICK 1a (Front A,
  tag pss-bwdcore).  For a monoT-core reduced-criterion \<open>M\<close> (\<open>M \<in> T_PS\<close>,
  \<open>monoT M\<close>, core \<open>(0,0)\<close>, \<open>RedCondA M\<close>, \<open>TrMax M \<noteq> Lng M - 1\<close>) and a branch
  index \<open>J\<close>, the row-0 head of the \<open>J\<close>-th branch block equals \<open>Joints M ! J + 1\<close>:
  \<open>entry (Br M ! J) 0 0 = Joints M ! J + 1\<close>.

  EMPIRICALLY TRUE: 96/96 over the core A&B nontrunk sequences at vals\<le>3 /
  lengths\<le>4, 0 counterexamples (\<open>/tmp/check_brick1.py\<close>, this worktree).

  Route: the branch head is \<open>M\<close>'s entry at the first node
  (@{thm [source] entry_FirstNodes_eq_component}); that node has a row-0 parent
  \<open>Joints M ! J\<close> (@{thm [source] a1_FN_hasParent} +
  @{thm [source] Joints_nth}), which lies on the trunk
  (\<open>Joints M ! J \<le> TrMax M\<close>, @{thm [source] m_6_4_FirstNodes_TrMax_Joints});
  \<open>RedCondA\<close> bumps the parent's row-0 value by one, and on the consecutive-diagonal
  trunk (@{thm [source] kst_bwdcore_trunkdiag}) that parent value is its own index
  \<open>Joints M ! J\<close>.  Cites only GREEN facts (no \<open>p_*\<close> stub, no goal self-reference).\<close>

lemma kst_bwdcore_branch_head_row0:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and condA: "RedCondA M"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and JBr: "J < Lng (Br M)"
  shows "entry (Br M ! J) 0 0 = Joints M ! J + 1"
proof -
  have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  let ?t = "TrMax M"
  let ?fn = "FirstNodes M ! J"
  \<comment> \<open>trunk is the consecutive diagonal; extract \<open>entry M 0 j = j\<close> for \<open>j \<le> ?t\<close>.\<close>
  have trunkdiag: "seg M 0 ?t = diagSeq 0 ?t"
    by (rule kst_bwdcore_trunkdiag[OF MT mono c0 c1 condA])
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have tb: "?t \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have tlt: "?t < Lng M" using tb LMpos by linarith
  have row0_trunk: "\<And>j. j \<le> ?t \<Longrightarrow> entry M 0 j = j"
  proof -
    fix j assume hj: "j \<le> ?t"
    have jseg: "j < Lng (seg M 0 ?t)" using hj tlt by (simp add: Lng_seg)
    have "entry M 0 j = entry (seg M 0 ?t) 0 j" using entry_seg[OF jseg, of 0] by simp
    also have "\<dots> = entry (diagSeq 0 ?t) 0 j" by (simp only: trunkdiag)
    also have "\<dots> = j" using hj tlt by (simp add: entry_diagSeq)
    finally show "entry M 0 j = j" .
  qed
  \<comment> \<open>branch head equals \<open>M\<close>'s entry at the first node.\<close>
  have JBr': "J < length (Br M)" using JBr by simp
  have head_fn: "entry (Br M ! J) 0 0 = entry M 0 ?fn"
    by (rule entry_FirstNodes_eq_component[OF M_PT JBr', symmetric])
  \<comment> \<open>the first node has a row-0 parent \<open>Joints M ! J\<close> on the trunk.\<close>
  have hpFN: "hasParent M 0 ?fn" by (rule a1_FN_hasParent[OF M_PT JBr])
  have par_eq: "Joints M ! J = parent M 0 ?fn" by (rule Joints_nth[OF JBr'])
  have jntle: "Joints M ! J \<le> ?t"
    using m_6_4_FirstNodes_TrMax_Joints[OF M_PT JBr] by simp
  \<comment> \<open>RedCondA bumps the parent's row-0 value by one.\<close>
  have condA0: "entry M 0 (parent M 0 ?fn) + 1 = entry M 0 ?fn"
    using condA hpFN unfolding RedCondA_def by blast
  \<comment> \<open>on the diagonal trunk the parent value is its index.\<close>
  have parval: "entry M 0 (parent M 0 ?fn) = Joints M ! J"
    using row0_trunk[OF jntle] par_eq by simp
  have "entry M 0 ?fn = Joints M ! J + 1" using condA0 parval by simp
  thus ?thesis using head_fn by simp
qed

text \<open>\<S>6.6 KEYSTONE BACKWARD core-nontrunk per-branch, BRICK 1b (Front A,
  tag pss-bwdcore).  Companion of @{thm [source] kst_bwdcore_branch_head_row0}:
  the row-1 head of the \<open>J\<close>-th branch block equals \<open>npJ M J\<close>:
  \<open>entry (Br M ! J) 1 0 = npJ M J\<close>.

  EMPIRICALLY TRUE: 96/96 over the core A&B nontrunk sequences at vals\<le>3 /
  lengths\<le>4, 0 counterexamples (\<open>/tmp/check_brick1.py\<close>, this worktree).

  Route: if the head row-1 value is \<open>0\<close>, \<open>npJ M J = 0\<close> by definition.  Otherwise
  the first node \<open>?f\<close> has a unique row-1 parent \<open>p\<^sub>1\<close> with \<open>npJ M J = Suc p\<^sub>1\<close>
  (the \<open>nzbr\<close> branch of @{thm [source] npJ_le_Joints_Suc}, which also gives
  \<open>p\<^sub>1 \<le> Joints M ! J \<le> TrMax M\<close>); \<open>RedCondA\<close> bumps the parent's row-1 value by one,
  and on the consecutive-diagonal trunk (@{thm [source] kst_bwdcore_trunkdiag})
  that parent value is its own index \<open>p\<^sub>1\<close>.  Cites only GREEN facts.\<close>

lemma kst_bwdcore_branch_head_row1:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and condA: "RedCondA M"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and JBr: "J < Lng (Br M)"
  shows "entry (Br M ! J) 1 0 = npJ M J"
proof (cases "entry (Br M ! J) 1 0 = 0")
  case True
  thus ?thesis by (simp add: npJ_def)
next
  case nzbr: False
  have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  let ?t = "TrMax M"
  let ?f = "FirstNodes M ! J"
  \<comment> \<open>trunk is the consecutive diagonal; extract \<open>entry M 1 j = j\<close> for \<open>j \<le> ?t\<close>.\<close>
  have trunkdiag: "seg M 0 ?t = diagSeq 0 ?t"
    by (rule kst_bwdcore_trunkdiag[OF MT mono c0 c1 condA])
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have tb: "?t \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have tlt: "?t < Lng M" using tb LMpos by linarith
  have row1_trunk: "\<And>j. j \<le> ?t \<Longrightarrow> entry M 1 j = j"
  proof -
    fix j assume hj: "j \<le> ?t"
    have jseg: "j < Lng (seg M 0 ?t)" using hj tlt by (simp add: Lng_seg)
    have "entry M 1 j = entry (seg M 0 ?t) 1 j" using entry_seg[OF jseg, of 1] by simp
    also have "\<dots> = entry (diagSeq 0 ?t) 1 j" by (simp only: trunkdiag)
    also have "\<dots> = j" using hj tlt by (simp add: entry_diagSeq)
    finally show "entry M 1 j = j" .
  qed
  \<comment> \<open>reconstruct the unique row-1 parent \<open>p\<^sub>1\<close> of \<open>?f\<close> as in @{thm [source] npJ_le_Joints_Suc}.\<close>
  have fnTr: "Joints M ! J \<le> TrMax M \<and> TrMax M < ?f"
    by (rule m_6_4_FirstNodes_TrMax_Joints[OF M_PT JBr])
  have nxJ: "nextR M 0 (Joints M ! J) ?f" by (rule Joints_parent_nextR[OF M_PT JBr])
  have fL: "?f < Lng M" using nxJ by (simp add: nextR_def nextrel0_def)
  have fpos: "0 < ?f" using fnTr by linarith
  have eBf1: "entry M 1 ?f = entry (Br M ! J) 1 0"
    by (rule entry_FirstNodes_eq_component_gen[OF M_PT JBr])
  have f1pos: "0 < entry M 1 ?f" using eBf1 nzbr by simp
  have e10_lt: "entry M 1 0 < entry M 1 ?f" using c1 f1pos by simp
  have le00f: "leR M 0 0 ?f"
  proof -
    have root: "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
    have fle: "?f \<le> Lng M - 1" using fL by simp
    show ?thesis by (rule m_5_1_ancestor_tree_1[OF MT root _ fle]) simp
  qed
  obtain p1 where p1: "0 \<le> p1" "p1 < ?f" "nextR M 1 p1 ?f"
    using m_5_1_parent_exists_2[OF MT fpos fL e10_lt le00f] by blast
  have ex1: "\<exists>!j. nextR M 1 j ?f" using p1(3) nextR1_unique by blast
  have the_p1: "(THE j. nextR M 1 j ?f) = p1" using p1(3) by (rule the1_equality[OF ex1])
  have np: "npJ M J = Suc p1" using nzbr the_p1 by (simp add: npJ_def)
  \<comment> \<open>\<open>p\<^sub>1 \<le> Joints M ! J \<le> TrMax M\<close>, so \<open>p\<^sub>1\<close> is on the trunk.\<close>
  have le0p1f: "leR M 0 p1 ?f"
    using p1(3) by (simp add: nextR_def nextrel1_def leR_def)
  have e0_p1f: "entry M 0 p1 < entry M 0 ?f"
    by (rule m_5_1_ancestor_basic_1[OF MT p1(2) order.refl le0p1f])
  have p1_le_J: "p1 \<le> Joints M ! J" by (rule nextR0_largest_below[OF nxJ p1(2) e0_p1f])
  have p1_le_t: "p1 \<le> ?t" using p1_le_J fnTr by simp
  \<comment> \<open>\<open>RedCondA\<close> on row 1 bumps the parent value by one; on the trunk it is the index.\<close>
  have hpf1: "hasParent M 1 ?f" unfolding hasParent_def using ex1 .
  have par_eq1: "parent M 1 ?f = p1" using the_p1 by (simp add: parent_def)
  have condA1: "entry M 1 (parent M 1 ?f) + 1 = entry M 1 ?f"
    using condA hpf1 unfolding RedCondA_def by blast
  have "entry (Br M ! J) 1 0 = entry M 1 ?f" using eBf1 by simp
  also have "\<dots> = entry M 1 p1 + 1" using condA1 par_eq1 by simp
  also have "\<dots> = p1 + 1" using row1_trunk[OF p1_le_t] by simp
  also have "\<dots> = npJ M J" using np by simp
  finally show ?thesis .
qed

text \<open>\<S>6.6 KEYSTONE BACKWARD core-nontrunk per-branch, BRICK 1 (Front A,
  tag pss-bwdcore).  For a monoT-core reduced-criterion \<open>M\<close> the head-renormalized
  branch \<open>N\<^sub>J M J\<close> coincides with the raw branch block \<open>Br M ! J\<close>:
  \<open>NJ M J = Br M ! J\<close>.

  EMPIRICALLY TRUE: 96/96 over the core A&B nontrunk sequences at vals\<le>3 /
  lengths\<le>4, 0 counterexamples (\<open>/tmp/check_a1.py\<close>, this worktree).

  \<open>NJ M J\<close> replaces the head of \<open>Br M ! J\<close> with \<open>(M\<^bsub>0,0\<^esub>+Joints+1, M\<^bsub>1,0\<^esub>+npJ)\<close>,
  which for a core \<open>M\<close> is \<open>(Joints+1, npJ)\<close>; that already equals the raw head by
  @{thm [source] kst_bwdcore_branch_head_row0} /
  @{thm [source] kst_bwdcore_branch_head_row1}, so the replacement is the identity.
  This collapses the core-nontrunk per-branch obligation
  \<open>(IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red (N\<^sub>J M J)) = Br M ! J\<close> to the IncrFirst-restore residual
  \<open>(IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red (N\<^sub>J M J)) = N\<^sub>J M J\<close>.  Cites only GREEN facts.\<close>

lemma kst_bwdcore_NJ_eq_Br:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and condA: "RedCondA M"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and JBr: "J < Lng (Br M)"
  shows "NJ M J = Br M ! J"
proof -
  have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M_PT JBr])
  have h0: "entry (Br M ! J) 0 0 = Joints M ! J + 1"
    by (rule kst_bwdcore_branch_head_row0[OF MT mono c0 c1 condA tne JBr])
  have h1: "entry (Br M ! J) 1 0 = npJ M J"
    by (rule kst_bwdcore_branch_head_row1[OF MT mono c0 c1 condA tne JBr])
  \<comment> \<open>the raw head pair of \<open>Br M ! J\<close>.\<close>
  have hfst: "fst (Br M ! J ! 0) = Joints M ! J + 1"
    using h0 by (simp add: entry_def)
  have hsnd: "snd (Br M ! J ! 0) = npJ M J"
    using h1 by (simp add: entry_def)
  have rawhd: "Br M ! J ! 0 = (Joints M ! J + 1, npJ M J)"
    by (rule prod_eqI) (simp_all add: hfst hsnd)
  have brcons: "Br M ! J = (Joints M ! J + 1, npJ M J) # tl (Br M ! J)"
    using brJne rawhd by (cases "Br M ! J") auto
  \<comment> \<open>\<open>NJ\<close>'s head for a core \<open>M\<close> is exactly this pair.\<close>
  have njhd: "entry M 0 0 + Joints M ! J + 1 = Joints M ! J + 1"
            "entry M 1 0 + npJ M J = npJ M J" using c0 c1 by simp_all
  have "NJ M J = (entry M 0 0 + Joints M ! J + 1, entry M 1 0 + npJ M J) # tl (Br M ! J)"
    by (simp add: NJ_def)
  also have "\<dots> = (Joints M ! J + 1, npJ M J) # tl (Br M ! J)" using njhd by simp
  also have "\<dots> = Br M ! J" using brcons by simp
  finally show ?thesis .
qed


text \<open>\<S>6.6 KEYSTONE BACKWARD monoT-core, MASTER REDUCTION (Front B, tag
  pss-bwdcore-master).  Reduces the full core target \<open>kst_condAB_imp_reduced_monoT_core\<close>
  to the SINGLE per-branch obligation
    \<open>\<And>J. J < Lng (Br M) \<Longrightarrow>
        (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) = Br M ! J\<close>
  by splicing the GREEN trunk subcase (@{thm [source] kst_bwdcore_trunk}), the
  GREEN trunk-diagonal brick (@{thm [source] kst_bwdcore_trunkdiag}) and the
  GREEN structural nontrunk reduction (@{thm [source] kst_bwdcore_nontrunk_of_blocks}).
  After this lemma, the ONLY residual of the entire \<S>6.6 keystone backward
  direction is the per-branch obligation, supplied as the \<open>blocks\<close> premise.

  EMPIRICAL STATUS (this worktree, \<open>python/check_backward_frontA.py\<close> and the
  per-branch probe \<open>/tmp/frontb_bricks.py\<close>): backward monoT-core A&B \<open>\<Longrightarrow>
  Red M = M\<close> is 0-fail over 66 cases (len\<le>4, vals\<le>3); the per-branch obligation
  is 96/96 over the 63 core-NONTRUNK A&B sequences (96 branches).  NOTE (correction
  to the prior round's framing): \<open>N\<^sub>J M J\<close> is NEVER core and NEVER \<open>m\<^sub>1\<^sub>0>0\<close>;
  it is 37/96 \<open>zeroT\<close> and 59/96 row-0-SHIFTED (entry00>0), satisfies \<open>RedCondA\<close>
  (96/96) but FAILS \<open>RedCondB\<close> (72/96), and is NOT reduced (72/96 have
  \<open>Red (N\<^sub>J M J) \<noteq> N\<^sub>J M J\<close>).  Hence the per-branch obligation is NOT
  reducible to ``\<open>N\<^sub>J M J\<close> reduced'': \<open>Red (N\<^sub>J M J)\<close> is the row-0-shifted-DOWN
  (by \<open>e\<^sub>J = Joints M!J+1-npJ M J\<close>) form of \<open>Br M!J\<close> (96/96
  \<open>Red (N\<^sub>J M J) = IncrFirst\<^bsup>-e\<^sub>J\<^esup>(Br M!J)\<close>), which requires characterising the
  general SHIFTED backward \<open>Red\<close>-output on the nu-smaller \<open>N\<^sub>J M J\<close>, NOT a
  heredity-of-A&B argument.\<close>

lemma kst_bwdcore_master:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and condA: "RedCondA M"
    and blocks: "\<And>J. J < Lng (Br M) \<Longrightarrow>
        (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) = Br M ! J"
  shows "Red M = M"
proof (cases "TrMax M = Lng M - 1")
  case True
  show ?thesis by (rule kst_bwdcore_trunk[OF MT mono c0 c1 True condA])
next
  case False
  have trunkdiag: "diagSeq 0 (TrMax M) = seg M 0 (TrMax M)"
    by (rule kst_bwdcore_trunkdiag[OF MT mono c0 c1 condA, symmetric])
  show ?thesis
    by (rule kst_bwdcore_nontrunk_of_blocks[OF MT mono c0 c1 False trunkdiag blocks])
qed


text \<open>\<S>6.6 KEYSTONE BACKWARD monoT-core, GENERALIZED-INVARIANT REFORMULATION
  (Front A, tag pss-bwdcore-G).  This banks the precise reduction of the SINGLE
  residual of the entire \<S>6.6 keystone to a CLEAN, self-contained,
  single-sequence identity \<open>G\<close> about the recursive arguments \<open>N\<^sub>J M J\<close>.

  EMPIRICAL DISCOVERY (this worktree, \<open>/tmp/frontA_gen.py\<close>, \<open>/tmp/frontA_clean.py\<close>;
  also \<open>/tmp/frontA_check2.py\<close> for the FALSE alternative):

    G (TRUE, 0-fail / 392 cases, len\<le>4 vals\<le>3):
      \<open>N \<in> T_PS\<close>, \<open>monoT N\<close>, \<open>RedCondA N\<close>, \<open>entry N 1 0 \<le> entry N 0 0\<close>
        \<Longrightarrow> (IncrFirst ^^ (entry N 0 0 - entry N 1 0)) (Red N) = N.

  G is the inverse-shift / IncrFirst-restore identity: \<open>Red\<close> lowers row 0 of a
  monoT RedCondA-sequence by exactly \<open>e = entry N 0 0 - entry N 1 0\<close>, and
  re-applying \<open>IncrFirst\<close> \<open>e\<close> times restores \<open>N\<close>.  Both hypotheses are essential:
  WITHOUT \<open>RedCondA\<close> it fails 2918/3310 (\<open>/tmp/frontA_gen2.py\<close>).  Note the prior
  round's suggested generalization \<open>Br (Red M) = Br M for monoT M with RedCondA M\<close>
  (B not assumed) is FALSE: 285/384 fail on the row-shifted non-core sequences
  (\<open>/tmp/frontA_check2.py\<close>); the correct invariant is the single-sequence G above,
  which stays valid precisely because the \<open>e\<close> in the IncrFirst-power is tied to
  \<open>N\<close>'s own head \<open>entry N 0 0 - entry N 1 0\<close>.

  This lemma packages the keystone so that the ONLY remaining obligation is G
  applied to each \<open>N\<^sub>J M J\<close>.  Cites only GREEN facts (@{thm [source]
  entry_NJ_0_0}, @{thm [source] entry_NJ_1_0}, @{thm [source]
  kst_bwdcore_master}); cites neither the goal nor any \<open>p_*\<close> stub.\<close>

lemma kst_bwdcore_master_via_G:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and condA: "RedCondA M"
    and G: "\<And>J. J < Lng (Br M) \<Longrightarrow>
        (IncrFirst ^^ (entry (NJ M J) 0 0 - entry (NJ M J) 1 0)) (Red (NJ M J)) = NJ M J"
  shows "Red M = M"
proof -
  have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have blocks: "\<And>J. J < Lng (Br M) \<Longrightarrow>
      (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) = Br M ! J"
  proof -
    fix J assume JBr: "J < Lng (Br M)"
    \<comment> \<open>the IncrFirst-power index matches \<open>entry (NJ M J) 0 0 - entry (NJ M J) 1 0\<close>
        for a core \<open>M\<close>.\<close>
    have e0: "entry (NJ M J) 0 0 = Joints M ! J + 1"
      using entry_NJ_0_0[of M J] c0 by simp
    have e1: "entry (NJ M J) 1 0 = npJ M J"
      using entry_NJ_1_0[of M J] c1 by simp
    have pow_eq: "entry (NJ M J) 0 0 - entry (NJ M J) 1 0 = Joints M ! J + 1 - npJ M J"
      using e0 e1 by simp
    \<comment> \<open>G applied to \<open>N\<^sub>J M J\<close> gives the IncrFirst-restore identity; \<open>NJ M J = Br M ! J\<close>.\<close>
    have restore: "(IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) = NJ M J"
      using G[OF JBr] pow_eq by simp
    have njbr: "NJ M J = Br M ! J"
    proof (cases "TrMax M = Lng M - 1")
      case True
      \<comment> \<open>trunk subcase: \<open>Br M = []\<close>, so the branch index is vacuous.\<close>
      have "Br M = []" using True by (simp add: Br_def)
      hence "Lng (Br M) = 0" by simp
      thus ?thesis using JBr by simp
    next
      case False
      show ?thesis by (rule kst_bwdcore_NJ_eq_Br[OF MT mono c0 c1 condA False JBr])
    qed
    show "(IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) = Br M ! J"
      using restore njbr by simp
  qed
  show ?thesis by (rule kst_bwdcore_master[OF MT mono c0 c1 condA blocks])
qed

end

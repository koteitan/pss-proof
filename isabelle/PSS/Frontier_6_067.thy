theory Frontier_6_067
  imports P_6_6_reduced_coeff
begin

text \<open>\<S>6.6 KEYSTONE BACKWARD monoT-core (Front A, tag pss-bwdcore).

  Goal: \<open>kst_condAB_imp_reduced_monoT_core\<close> — for \<open>M \<in> T_PS\<close>, \<open>monoT M\<close>,
  \<open>entry M 0 0 = 0\<close>, \<open>entry M 1 0 = 0\<close>, \<open>RedCondA M\<close>, \<open>RedCondB M\<close>: \<open>Red M = M\<close>.
  EMPIRICALLY TRUE: 66 monoT-core A&B sequences at vals\<le>3 / lengths\<le>4, 0
  counterexamples (\<open>python/check_backward_frontA.py\<close>, this worktree).

  This is the LAST residual of the entire \<S>6.6 keystone backward direction
  (the forward direction, the general-\<open>M\<close> lift, and the full iff are GREEN at
  HEAD, conditional only on this core lemma and the \<open>m\<^sub>1\<^sub>0 > 0\<close> case).

  TRUNK subcase below (\<open>TrMax M = Lng M - 1\<close>): \<open>RedCondA M\<close> forces \<open>M\<close> to be the
  consecutive diagonal \<open>diagSeq 0 (Lng M - 1)\<close> (@{thm [source]
  m_6_6_RedCondA_core_diag}), and the \<open>Red\<close> core-trunk branch outputs exactly
  \<open>diagSeq m\<^sub>1\<^sub>0 (m\<^sub>1\<^sub>0 + (Lng M - 1)) = diagSeq 0 (Lng M - 1)\<close> (\<open>m\<^sub>1\<^sub>0 = 0\<close>),
  hence \<open>Red M = M\<close>.\<close>

lemma kst_bwdcore_trunk:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and trmax: "TrMax M = Lng M - 1"
    and condA: "RedCondA M"
  shows "Red M = M"
proof -
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  \<comment> \<open>\<open>M\<close> is the consecutive diagonal from \<open>RedCondA\<close>.\<close>
  have Mdiag: "M = diagSeq 0 (Lng M - 1)"
    by (rule m_6_6_RedCondA_core_diag[OF MT mono c0 c1 trmax condA])
  \<comment> \<open>The \<open>Red\<close> core-trunk branch outputs \<open>diagSeq m\<^sub>1\<^sub>0 (m\<^sub>1\<^sub>0 + (Lng M - 1))\<close>.\<close>
  have rM: "Red M = diagSeq (entry M 1 0) (entry M 1 0 + (Lng M - 1))"
    using Red.psimps[OF dom] nz nmu c0 c1 trmax by (simp add: Let_def)
  have rM': "Red M = diagSeq 0 (Lng M - 1)" using rM c1 by simp
  show ?thesis using rM' Mdiag by simp
qed


text \<open>BWD core-nontrunk STRUCTURAL REDUCTION (Front A, tag pss-bwdcore).
  For a core-nontrunk \<open>M\<close> (\<open>M \<in> T_PS\<close>, \<open>monoT M\<close>, core \<open>(0,0)\<close>,
  \<open>TrMax M \<noteq> Lng M - 1\<close>), assuming the trunk is the consecutive diagonal
  (\<open>diagSeq 0 (TrMax M) = seg M 0 (TrMax M)\<close>) and each branch block restores
  (\<open>IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red (NJ M J)) = Br M ! J\<close>), \<open>Red M = M\<close>.

  PURELY STRUCTURAL concat/seg algebra on top of @{thm [source]
  d_Red_core_nontrunk_unfold}: the diagonal prefix is the trunk slice
  \<open>seg M 0 (TrMax M)\<close>, the branch blocks reassemble \<open>concat (Br M)
  = seg M (TrMax M + 1) (Lng M - 1)\<close> (@{thm [source] poper_concat_P} +
  @{const Br}-def), and \<open>take (Suc (TrMax M)) M @ drop (TrMax M + 1) M = M\<close>.
  Isolates the two genuine obligations (trunk-diagonal and per-branch restore)
  from the bookkeeping.\<close>

lemma kst_bwdcore_nontrunk_of_blocks:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and trunkdiag: "diagSeq 0 (TrMax M) = seg M 0 (TrMax M)"
    and blocks: "\<And>J. J < Lng (Br M) \<Longrightarrow>
        (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) = Br M ! J"
  shows "Red M = M"
proof -
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  let ?t = "TrMax M"
  let ?nM = "Lng (Br M)"
  let ?BL = "\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))"
  \<comment> \<open>\<open>?t < Lng M - 1\<close>.\<close>
  have tlt: "?t < Lng M - 1" using TrMax_bound[OF MT] tne by linarith
  \<comment> \<open>unfold \<open>Red M\<close>.\<close>
  have unfoldR: "Red M = diagSeq 0 ?t @ concat (map ?BL [0..<?nM])"
    by (rule d_Red_core_nontrunk_unfold[OF MT nz nmu c0 c1 tne])
  \<comment> \<open>branch blocks reassemble: \<open>map ?BL [0..<?nM] = Br M\<close>.\<close>
  have mapBL: "map ?BL [0..<?nM] = Br M"
  proof (rule nth_equalityI)
    show "length (map ?BL [0..<?nM]) = length (Br M)" by simp
  next
    fix J assume "J < length (map ?BL [0..<?nM])"
    hence JB: "J < ?nM" by simp
    have "map ?BL [0..<?nM] ! J = ?BL J" using JB by simp
    also have "\<dots> = Br M ! J" by (rule blocks[OF JB])
    finally show "map ?BL [0..<?nM] ! J = Br M ! J" .
  qed
  \<comment> \<open>\<open>concat (Br M) = seg M (?t + 1) (Lng M - 1)\<close>.\<close>
  have concatBr: "concat (Br M) = seg M (?t + 1) (Lng M - 1)"
  proof -
    have "Br M = P (seg M (?t + 1) (Lng M - 1))" using tne by (simp add: Br_def)
    thus ?thesis by (simp add: poper_concat_P)
  qed
  \<comment> \<open>assemble: trunk slice @ branch slice = \<open>M\<close>.\<close>
  have segt: "seg M 0 ?t = take (Suc ?t) M"
    by (rule seg_0_eq_take) (use tlt LMpos in linarith)
  have segb: "seg M (?t + 1) (Lng M - 1) = drop (?t + 1) M"
    by (rule seg_to_last_eq_drop[OF LMpos])
  have takedrop: "take (Suc ?t) M @ drop (?t + 1) M = M"
  proof -
    have "drop (?t + 1) M = drop (Suc ?t) M" by (simp only: Suc_eq_plus1)
    thus ?thesis using append_take_drop_id[of "Suc ?t" M] by simp
  qed
  have "Red M = diagSeq 0 ?t @ concat (map ?BL [0..<?nM])" by (rule unfoldR)
  also have "\<dots> = diagSeq 0 ?t @ concat (Br M)" by (simp only: mapBL)
  also have "\<dots> = seg M 0 ?t @ seg M (?t + 1) (Lng M - 1)"
    by (simp only: trunkdiag concatBr)
  also have "\<dots> = take (Suc ?t) M @ drop (?t + 1) M" by (simp only: segt segb)
  also have "\<dots> = M" by (rule takedrop)
  finally show ?thesis .
qed


text \<open>BWD core trunk-diagonal (Front A, tag pss-bwdcore): for a monoT-core \<open>M\<close>
  with \<open>RedCondA M\<close>, the trunk slice is the consecutive diagonal
  \<open>seg M 0 (TrMax M) = diagSeq 0 (TrMax M)\<close>.  EMPIRICALLY 63/63 over the
  core-nontrunk A&B sequences (\<open>python/check_trunkdiag.py\<close>).

  Row 1 is the index on the trunk by @{thm [source] TrMax_trunk_step}
  (each trunk column \<open>j>0\<close> has the unique row-1 parent \<open>j-1\<close>) and \<open>RedCondA M\<close>
  (which pins \<open>entry M 1 j = entry M 1 (j-1) + 1\<close>); row 0 is squeezed between
  the coefficient bound \<open>\<le> j\<close> (@{thm [source] m_6_6_condAB_coeff}) and the
  strict trunk increase \<open>\<ge> j\<close>.  Adapts @{thm [source] m_6_6_RedCondA_core_diag}
  to the trunk prefix, with no \<open>TrMax = Lng - 1\<close> hypothesis.\<close>

lemma kst_bwdcore_trunkdiag:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and condA: "RedCondA M"
  shows "seg M 0 (TrMax M) = diagSeq 0 (TrMax M)"
proof -
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  let ?t = "TrMax M"
  have tb: "?t \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have tlt: "?t < Lng M" using tb LMpos by linarith
  \<comment> \<open>trunk step holds below \<open>?t\<close>.\<close>
  have trunk_step: "\<And>j'. j' < ?t \<Longrightarrow> nextR M 1 j' (j' + 1)"
    by (rule TrMax_trunk_step[OF MT])
  have inc1: "\<And>j'. j' < ?t \<Longrightarrow> entry M 1 j' < entry M 1 (j' + 1)"
  proof -
    fix j' assume hj: "j' < ?t"
    have "nextrel1 M j' (j' + 1)" using trunk_step[OF hj] by (simp add: nextR_def)
    thus "entry M 1 j' < entry M 1 (j' + 1)" by (simp add: nextrel1_def)
  qed
  \<comment> \<open>row-0 strict increase on the trunk (\<open>nextrel0\<close> collapse, as in \<open>m_6_6_RedCondA_core_diag\<close>).\<close>
  have nr0_step: "\<And>j'. j' < ?t \<Longrightarrow> nextrel0 M j' (j' + 1)"
  proof -
    fix j' assume hj: "j' < ?t"
    have "nextrel1 M j' (j' + 1)" using trunk_step[OF hj] by (simp add: nextR_def)
    hence le0: "le0 M j' (j' + 1)" by (simp add: nextrel1_def)
    hence rt: "(nextrel0 M)\<^sup>*\<^sup>* j' (j' + 1)" by (simp add: le0_def)
    from rt show "nextrel0 M j' (j' + 1)"
    proof (cases rule: rtranclp.cases)
      case rtrancl_refl thus ?thesis by simp
    next
      case (rtrancl_into_rtrancl b)
      have rtb: "(nextrel0 M)\<^sup>*\<^sup>* j' b" using rtrancl_into_rtrancl by simp
      have laststep: "nextrel0 M b (j' + 1)" using rtrancl_into_rtrancl by simp
      have "j' \<le> b" using rtb by (rule nextrel0_rtrancl_mono)
      moreover have "b < j' + 1" using laststep by (simp add: nextrel0_def)
      ultimately have "b = j'" by linarith
      thus ?thesis using laststep by simp
    qed
  qed
  have inc0: "\<And>j'. j' < ?t \<Longrightarrow> entry M 0 j' < entry M 0 (j' + 1)"
    using nr0_step by (simp add: nextrel0_def)
  \<comment> \<open>from-zero strict increase gives \<open>\<ge> j\<close> on the trunk.\<close>
  have ge_idx0: "\<And>j. j \<le> ?t \<Longrightarrow> j \<le> entry M 0 j"
  proof -
    fix j assume "j \<le> ?t"
    thus "j \<le> entry M 0 j"
    proof (induction j)
      case 0 thus ?case by simp
    next
      case (Suc n)
      have nlt: "n < ?t" using Suc.prems by linarith
      have "n \<le> entry M 0 n" using Suc.IH nlt by linarith
      moreover have "entry M 0 n < entry M 0 (n + 1)" using inc0[OF nlt] by simp
      ultimately show ?case by simp
    qed
  qed
  \<comment> \<open>row-0 upper bound \<open>\<le> j\<close> from coefficient brick.\<close>
  have le0_idx: "\<And>j. j \<le> Lng M - 1 \<Longrightarrow> entry M 0 j \<le> j"
    using m_6_6_condAB_coeff[OF MT e00 e10 condA] by blast
  have row0: "\<And>j. j \<le> ?t \<Longrightarrow> entry M 0 j = j"
  proof -
    fix j assume hj: "j \<le> ?t"
    have "j \<le> entry M 0 j" using ge_idx0[OF hj] .
    moreover have "entry M 0 j \<le> j" using le0_idx hj tb by simp
    ultimately show "entry M 0 j = j" by simp
  qed
  \<comment> \<open>row 1 = index on the trunk via uniqueness of the row-1 trunk parent + \<open>RedCondA\<close>.\<close>
  have par1_val: "\<And>j. 0 < j \<Longrightarrow> j \<le> ?t \<Longrightarrow> parent M 1 j = j - 1 \<and> hasParent M 1 j"
  proof -
    fix j assume jpos: "0 < j" and jle: "j \<le> ?t"
    have jm1: "j - 1 < ?t" using jpos jle by linarith
    have step: "nextR M 1 (j - 1) j" using trunk_step[OF jm1] jpos by simp
    have jlt: "j < Lng M" using jle tlt by linarith
    \<comment> \<open>uniqueness: any other row-1 parent of \<open>j\<close> equals \<open>j-1\<close>.\<close>
    have uniq: "\<And>c. nextR M 1 c j \<Longrightarrow> c = j - 1"
    proof -
      fix c assume nc: "nextR M 1 c j"
      have na: "nextrel1 M (j - 1) j" using step by (simp add: nextR_def)
      have nc1: "nextrel1 M c j" using nc by (simp add: nextR_def)
      \<comment> \<open>row-1 parent monotone-uniqueness (as in \<open>m_6_6_RedCondA_core_diag\<close>).\<close>
      have key: "\<And>x y. nextrel1 M x j \<Longrightarrow> nextrel1 M y j \<Longrightarrow> x < y \<Longrightarrow> False"
      proof -
        fix x y assume nx: "nextrel1 M x j" and ny: "nextrel1 M y j" and xy: "x < y"
        have ymin: "\<forall>k. x < k \<and> le0 M k j \<longrightarrow> entry M 1 k \<ge> entry M 1 j"
          using nx by (simp add: nextrel1_def)
        have leyk: "le0 M y j" using ny by (simp add: nextrel1_def)
        have "entry M 1 y \<ge> entry M 1 j" using ymin xy leyk by simp
        moreover have "entry M 1 y < entry M 1 j" using ny by (simp add: nextrel1_def)
        ultimately show False by simp
      qed
      show "c = j - 1"
      proof (rule ccontr)
        assume "c \<noteq> j - 1"
        then consider "c < j - 1" | "j - 1 < c" by linarith
        thus False using key[OF nc1 na] key[OF na nc1] by cases simp_all
      qed
    qed
    have hp: "hasParent M 1 j"
      unfolding hasParent_def using step uniq by blast
    have pv: "parent M 1 j = j - 1"
      unfolding parent_def using step uniq by (blast intro: the1_equality)
    show "parent M 1 j = j - 1 \<and> hasParent M 1 j" using pv hp by simp
  qed
  have condA1: "\<And>j. j \<le> Lng M - 1 \<Longrightarrow> hasParent M 1 j \<Longrightarrow>
      entry M 1 (parent M 1 j) + 1 = entry M 1 j"
    using condA unfolding RedCondA_def by simp
  have row1: "\<And>j. j \<le> ?t \<Longrightarrow> entry M 1 j = j"
  proof -
    fix j assume hj: "j \<le> ?t"
    thus "entry M 1 j = j"
    proof (induction j)
      case 0 thus ?case using e10 by simp
    next
      case (Suc n)
      have nle: "Suc n \<le> ?t" using Suc.prems by simp
      have npos: "0 < Suc n" by simp
      have pp: "parent M 1 (Suc n) = n \<and> hasParent M 1 (Suc n)"
        using par1_val[OF npos nle] by simp
      have hp: "hasParent M 1 (Suc n)" using pp by simp
      have pv: "parent M 1 (Suc n) = n" using pp by simp
      have nleL: "Suc n \<le> Lng M - 1" using nle tb by linarith
      have "entry M 1 n + 1 = entry M 1 (Suc n)"
        using condA1[OF nleL hp] pv by simp
      moreover have "entry M 1 n = n" using Suc.IH Suc.prems by simp
      ultimately show ?case by simp
    qed
  qed
  \<comment> \<open>assemble: each trunk pair is \<open>(j,j)\<close>.\<close>
  show ?thesis
  proof (rule nth_equalityI)
    have Lseg: "Lng (seg M 0 ?t) = Suc ?t" using tlt by (simp add: Lng_seg)
    have Ldiag: "Lng (diagSeq 0 ?t) = Suc ?t" by simp
    show "length (seg M 0 ?t) = length (diagSeq 0 ?t)" using Lseg Ldiag by simp
  next
    fix j assume "j < length (seg M 0 ?t)"
    hence jseg: "j < Lng (seg M 0 ?t)" by simp
    have jle: "j \<le> ?t" using jseg tlt by (simp add: Lng_seg)
    have e0: "entry (seg M 0 ?t) 0 j = entry M 0 j"
      using entry_seg[OF jseg, of 0] by simp
    have e1: "entry (seg M 0 ?t) 1 j = entry M 1 j"
      using entry_seg[OF jseg, of 1] by simp
    have "seg M 0 ?t ! j = (entry (seg M 0 ?t) 0 j, entry (seg M 0 ?t) 1 j)"
      by (simp add: entry_def)
    also have "\<dots> = (entry M 0 j, entry M 1 j)" using e0 e1 by simp
    also have "\<dots> = (j, j)" using row0[OF jle] row1[OF jle] by simp
    also have "\<dots> = diagSeq 0 ?t ! j"
      using diagSeq_nth[of j ?t 0] jle by simp
    finally show "seg M 0 ?t ! j = diagSeq 0 ?t ! j" .
  qed
qed

text \<open>\<S>6.6 KEYSTONE BACKWARD (monoT, m10>0) — the monoT_m10pos residual of
  kst_condAB_imp_reduced_cond, DISCHARGED BY REDUCTION to the keystone CORE
  (tag pss-wf25-bwd, Front B).  See _frontb_*.py for the empirical confirmation.\<close>

lemma frontb_rebaseNp_whole:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and eq00: "entry M 0 0 = entry M 1 0"
  shows "rebaseNp M 0 (Lng M - 1) = M"
proof (rule nth_equalityI)
  have L0: "0 < Lng M" using MT by (simp add: T_PS_def)
  show LenEq: "length (rebaseNp M 0 (Lng M - 1)) = length M"
    using L0 by simp
  fix j assume jlt: "j < length (rebaseNp M 0 (Lng M - 1))"
  have jlt': "j < Suc (Lng M - 1 - 0)" using jlt by simp
  have jLM: "j < Lng M" using jlt' L0 by simp
  have dom0: "entry M 0 0 \<le> entry M 0 j" by (rule entry0_ge_min[OF MT mono jLM])
  have arith0: "entry M 0 j - entry M 0 0 + entry M 1 0 = entry M 0 j"
    using eq00 dom0 by simp
  have "rebaseNp M 0 (Lng M - 1) ! j
          = (entry M 0 (0 + j) - entry M 0 0 + entry M 1 0, entry M 1 (0 + j))"
    by (rule rebaseNp_nth[OF jlt'])
  also have "\<dots> = (entry M 0 j, entry M 1 j)" using arith0 by simp
  also have "\<dots> = M ! j"
    using jLM by (simp add: entry_def)
  finally show "rebaseNp M 0 (Lng M - 1) ! j = M ! j" .
qed

lemma frontb_bwdN_whole_eq_Q:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
    and eq00: "entry M 0 0 = entry M 1 0"
  shows "bwdN M 0 (Lng M - 1) = diagSeq 0 (entry M 1 0 - 1) @ M"
proof -
  have "bwdN M 0 (Lng M - 1)
          = diagPre (entry M 1 0) @ rebaseNp M 0 (Lng M - 1)"
    by (simp add: bwdN_def)
  also have "diagPre (entry M 1 0) = diagSeq 0 (entry M 1 0 - 1)"
    by (rule diagPre_eq_diagSeq[OF pos])
  also have "rebaseNp M 0 (Lng M - 1) = M"
    by (rule frontb_rebaseNp_whole[OF MT mono eq00])
  finally show ?thesis .
qed

lemma kst_condAB_imp_reduced_monoT_m10pos:
  assumes core:
    "\<And>N. N \<in> T_PS \<Longrightarrow> monoT N \<Longrightarrow> entry N 0 0 = 0 \<Longrightarrow> entry N 1 0 = 0
       \<Longrightarrow> RedCondA N \<Longrightarrow> RedCondB N \<Longrightarrow> Red N = N"
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and m10pos: "0 < entry M 1 0"
    and condA: "RedCondA M" and condB: "RedCondB M"
  shows "Red M = M"
proof -
  let ?m = "entry M 1 0"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have L0: "0 < Lng M" using MT by (simp add: T_PS_def)
  have eq00: "entry M 0 0 = entry M 1 0"
    by (rule m_6_6_RedCondB_row0_eq_row1_at0[OF MT condB])
  have dom_m: "?m - 1 < entry M 0 0" using m10pos eq00 by simp
  let ?Q = "diagSeq 0 (?m - 1) @ M"
  have segM: "seg M 0 (Lng M - 1) = M"
    using L0 seg_to_last_eq_drop[OF L0] by simp
  have segmono: "monoT (seg M 0 (Lng M - 1))" using segM mono by simp
  have jord: "(0::nat) \<le> Lng M - 1" by simp
  have j1LM: "Lng M - 1 < Lng M" using L0 by simp
  have c2: "entry M 1 0 \<le> entry M 0 0" using eq00 by simp
  have rmono: "\<forall>k \<le> (Lng M - 1) - 0. entry M 0 0 \<le> entry M 0 (0 + k)"
    by (rule seg_rmono_of_monoT[OF jord j1LM segmono])
  have bwdQ: "bwdN M 0 (Lng M - 1) = ?Q"
    by (rule frontb_bwdN_whole_eq_Q[OF MT mono m10pos eq00])
  have Qne: "?Q \<noteq> []" using Mne by simp
  have QT: "?Q \<in> T_PS" using Qne by (simp add: T_PS_def)
  have QmonoT: "monoT ?Q"
    using monoT_bwdN[OF jord c2 rmono segmono] bwdQ by simp
  have Qe00: "entry ?Q 0 0 = 0" using m10pos by (simp add: entry_diagSeq_append_lo)
  have Qe10: "entry ?Q 1 0 = 0" using m10pos by (simp add: entry_diagSeq_append_lo)
  have QcondA: "RedCondA ?Q"
    using RedCondA_bwdN[OF MT condA jord j1LM segmono] bwdQ by simp
  have QcondB: "RedCondB ?Q"
    using RedCondB_bwdN[OF jord c2 rmono segmono] bwdQ by simp
  have RedQ: "Red ?Q = ?Q"
    by (rule core[OF QT QmonoT Qe00 Qe10 QcondA QcondB])
  let ?arg = "diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
  have arg_eq_cr: "?arg = coreReduce M"
    using coreReduce_m10pos_form[OF m10pos] by simp
  have RedArg: "Red ?arg = ?Q"
  proof -
    have "Red ?arg = Red (coreReduce M)" using arg_eq_cr by simp
    also have "\<dots> = Red (diagSeq 0 (?m - 1) @ M)"
      by (rule ecrux_Red_diag_eq_Red_coreReduce[OF MT mono dom_m m10pos, symmetric])
    also have "\<dots> = ?Q" using RedQ by simp
    finally show ?thesis .
  qed
  have LQ: "Lng ?Q = ?m + Lng M" using m10pos by simp
  have LRA: "Lng (Red ?arg) = ?m + Lng M" using RedArg LQ by simp
  have jN_eq: "Lng (Red ?arg) - 1 = ?m + (Lng M - 1)"
  proof -
    have sucL: "Lng M = Suc (Lng M - 1)" using L0 by simp
    have "Lng (Red ?arg) - 1 = (?m + Lng M) - 1" using LRA by simp
    also have "\<dots> = (?m + Suc (Lng M - 1)) - 1" using sucL by simp
    also have "\<dots> = ?m + (Lng M - 1)" by simp
    finally show ?thesis .
  qed
  have m10_le: "?m \<le> Lng (Red ?arg) - 1" using jN_eq by simp
  have LRedArg: "0 < Lng (Red ?arg)" using RedArg LQ L0 by simp
  have segNi: "seg (Red ?arg) ?m (Lng (Red ?arg) - 1) = M"
  proof -
    have "seg (Red ?arg) ?m (Lng (Red ?arg) - 1) = drop ?m (Red ?arg)"
      by (rule seg_to_last_eq_drop[OF LRedArg])
    also have "\<dots> = drop ?m ?Q" using RedArg by simp
    also have "\<dots> = M"
    proof -
      have "length (diagSeq 0 (?m - 1)) = ?m" using m10pos by (simp add: diagSeq_def)
      thus ?thesis by simp
    qed
    finally show ?thesis .
  qed
  have segPT: "seg (Red ?arg) ?m (Lng (Red ?arg) - 1) \<in> PT_PS"
    using segNi MT mono by (simp add: PT_PS_def)
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have nc: "\<not> (entry M 0 0 = 0 \<and> ?m = 0)" using m10pos by simp
  have rM: "Red M = (let N = Red ?arg; jN = Lng N - 1 in
             if ?m \<le> jN \<and> seg N ?m jN \<in> PT_PS then
               map (\<lambda>j. (entry N 0 j - entry N 0 ?m + entry N 1 ?m, entry N 1 j))
                   [?m..<Suc jN]
             else M)"
    using Red.psimps[OF domM] nz nmu nc m10pos by (simp add: Let_def)
  have rM2: "Red M = map (\<lambda>j. (entry (Red ?arg) 0 j - entry (Red ?arg) 0 ?m
                                + entry (Red ?arg) 1 ?m, entry (Red ?arg) 1 j))
                          [?m..<Suc (Lng (Red ?arg) - 1)]"
    using rM m10_le segPT by (simp add: Let_def)
  have junc0: "entry (Red ?arg) 0 ?m = ?m"
  proof -
    have "entry (Red ?arg) 0 ?m = entry (diagSeq 0 (?m - 1) @ M) 0 ?m"
      using RedArg by simp
    also have "\<dots> = entry M 0 0" by (rule cAm10_entry_junction[OF m10pos])
    also have "\<dots> = ?m" using eq00 by simp
    finally show ?thesis .
  qed
  have junc1: "entry (Red ?arg) 1 ?m = ?m"
  proof -
    have "entry (Red ?arg) 1 ?m = entry (diagSeq 0 (?m - 1) @ M) 1 ?m"
      using RedArg by simp
    also have "\<dots> = entry M 1 0" by (rule cAm10_entry_junction[OF m10pos])
    finally show ?thesis .
  qed
  have jNsuc: "Suc (Lng (Red ?arg) - 1) = ?m + Lng M"
  proof -
    have "Suc (Lng (Red ?arg) - 1) = Suc (?m + (Lng M - 1))" using jN_eq by simp
    also have "\<dots> = ?m + Suc (Lng M - 1)" by simp
    also have "\<dots> = ?m + Lng M" using L0 by simp
    finally show ?thesis .
  qed
  have lenupt: "length [?m..<Suc (Lng (Red ?arg) - 1)] = Lng M"
  proof -
    have "length [?m..<Suc (Lng (Red ?arg) - 1)] = length [?m..<(?m + Lng M)]"
      using jNsuc by simp
    also have "\<dots> = Lng M" by simp
    finally show ?thesis .
  qed
  show "Red M = M"
  proof (rule nth_equalityI)
    have Lmap: "length (map (\<lambda>j. (entry (Red ?arg) 0 j - entry (Red ?arg) 0 ?m
                                + entry (Red ?arg) 1 ?m, entry (Red ?arg) 1 j))
                          [?m..<Suc (Lng (Red ?arg) - 1)]) = Lng M"
      using lenupt by simp
    show "length (Red M) = length M" using rM2 Lmap by simp
    fix t assume tlt: "t < length (Red M)"
    have tLM: "t < Lng M" using tlt rM2 Lmap by simp
    have tlen: "t < length [?m..<Suc (Lng (Red ?arg) - 1)]"
      using tLM lenupt by simp
    have jset: "[?m..<Suc (Lng (Red ?arg) - 1)] ! t = ?m + t"
    proof -
      have "[?m..<Suc (Lng (Red ?arg) - 1)] = [?m..<(?m + Lng M)]" using jNsuc by simp
      moreover have "[?m..<(?m + Lng M)] ! t = ?m + t" using tLM by simp
      ultimately show ?thesis by simp
    qed
    have entA0: "entry (Red ?arg) 0 (?m + t) = entry M 0 t"
    proof -
      have "entry (Red ?arg) 0 (?m + t) = entry (diagSeq 0 (?m - 1) @ M) 0 (?m + t)"
        using RedArg by simp
      also have "\<dots> = entry M 0 t" by (rule cAm10_entry_transfer[OF m10pos tLM])
      finally show ?thesis .
    qed
    have entA1: "entry (Red ?arg) 1 (?m + t) = entry M 1 t"
    proof -
      have "entry (Red ?arg) 1 (?m + t) = entry (diagSeq 0 (?m - 1) @ M) 1 (?m + t)"
        using RedArg by simp
      also have "\<dots> = entry M 1 t" by (rule cAm10_entry_transfer[OF m10pos tLM])
      finally show ?thesis .
    qed
    have dom0t: "?m \<le> entry M 0 t"
    proof -
      have "?m = entry M 0 0" using eq00 by simp
      also have "\<dots> \<le> entry M 0 t" by (rule entry0_ge_min[OF MT mono tLM])
      finally show ?thesis .
    qed
    have arithT: "entry M 0 t - ?m + ?m = entry M 0 t" using dom0t by simp
    have "Red M ! t = (entry (Red ?arg) 0 (?m + t) - entry (Red ?arg) 0 ?m
                        + entry (Red ?arg) 1 ?m, entry (Red ?arg) 1 (?m + t))"
      using rM2 tlen jset by (simp add: nth_map del: upt_Suc)
    also have "\<dots> = (entry M 0 t - ?m + ?m, entry M 1 t)"
      using entA0 entA1 junc0 junc1 by simp
    also have "\<dots> = (entry M 0 t, entry M 1 t)" using arithT by simp
    also have "\<dots> = M ! t" using tLM by (simp add: entry_def)
    finally show "Red M ! t = M ! t" .
  qed
qed

end

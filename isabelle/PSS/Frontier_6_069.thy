theory Frontier_6_069
  imports Support_6_048
begin

text \<open>The uniform inverse-shift entry algebra: raising row 0 back up by \<open>e\<close> via
  @{const IncrFirst} undoes a uniform row-0 down-shift @{term "rebaseRow0 e 0 X"},
  provided \<open>e\<close> is a row-0 lower bound of \<open>X\<close> (no nat-truncation).  This
  generalises @{thm [source] bwd_IncrFirst_m00_shiftRow0_monoT} to an arbitrary
  uniform shift amount \<open>e\<close>.\<close>

lemma bwd_IncrFirst_e_rebaseRow0:
  assumes lb: "\<And>j. j < Lng X \<Longrightarrow> e \<le> entry X 0 j"
  shows "(IncrFirst ^^ e) (rebaseRow0 e 0 X) = X"
proof (rule nth_equalityI)
  show "Lng ((IncrFirst ^^ e) (rebaseRow0 e 0 X)) = Lng X" by simp
next
  fix j assume jl0: "j < Lng ((IncrFirst ^^ e) (rebaseRow0 e 0 X))"
  have jl: "j < Lng X" using jl0 by simp
  have jre: "j < Lng (rebaseRow0 e 0 X)" using jl by simp
  have e0: "entry ((IncrFirst ^^ e) (rebaseRow0 e 0 X)) 0 j = entry X 0 j"
  proof -
    have "entry ((IncrFirst ^^ e) (rebaseRow0 e 0 X)) 0 j
        = entry (rebaseRow0 e 0 X) 0 j + e"
      by (rule entry_funpow_IncrFirst0[OF jre])
    also have "\<dots> = (entry X 0 j - e + 0) + e"
      using entry_rebaseRow0_0[OF jl] by simp
    also have "\<dots> = entry X 0 j" using lb[OF jl] by simp
    finally show ?thesis .
  qed
  have e1: "entry ((IncrFirst ^^ e) (rebaseRow0 e 0 X)) 1 j = entry X 1 j"
  proof -
    have "entry ((IncrFirst ^^ e) (rebaseRow0 e 0 X)) 1 j
        = entry (rebaseRow0 e 0 X) 1 j"
      by (rule entry_funpow_IncrFirst1[OF jre])
    also have "\<dots> = entry X 1 j" using entry_rebaseRow0_1[OF jl] by simp
    finally show ?thesis .
  qed
  show "(IncrFirst ^^ e) (rebaseRow0 e 0 X) ! j = X ! j"
  proof -
    have "fst ((IncrFirst ^^ e) (rebaseRow0 e 0 X) ! j) = fst (X ! j)"
      using e0 by (simp add: entry_def)
    moreover have "snd ((IncrFirst ^^ e) (rebaseRow0 e 0 X) ! j) = snd (X ! j)"
      using e1 by (simp add: entry_def)
    ultimately show ?thesis by (simp add: prod_eq_iff)
  qed
qed

text \<open>\<S>6.6 KEYSTONE BACKWARD INVERSE-SHIFT, UNIFIED REDUCTION (Front B, tag
  pss-bwdcore-invshift).  The CLEAN reduction of the inverse-shift identity to the
  REDUCEDNESS of the rebased sequence \<open>Y = rebaseRow0 e 0 X\<close> (\<open>X\<close> with row 0
  lowered uniformly by \<open>e = m\<^sub>0\<^sub>0 - m\<^sub>1\<^sub>0\<close>).  The mechanism, valid for BOTH
  \<open>m\<^sub>1\<^sub>0 = 0\<close> and \<open>m\<^sub>1\<^sub>0 > 0\<close>:
    \<^item> \<open>X = IncrFirst\<^bsup>e\<^esup> Y\<close>     (@{thm [source] bwd_IncrFirst_e_rebaseRow0}, pure
       entry algebra, given \<open>e\<close> is a row-0 lower bound),
    \<^item> \<open>Red X = Red (IncrFirst\<^bsup>e\<^esup> Y) = Red Y\<close>  (@{thm [source] a1_Red_funpow_IncrFirst}:
       \<open>Red\<close> is \<open>IncrFirst\<close>-invariant),
    \<^item> hence \<open>IncrFirst\<^bsup>e\<^esup> (Red X) = IncrFirst\<^bsup>e\<^esup> (Red Y) = IncrFirst\<^bsup>e\<^esup> Y = X\<close>,
      using the supplied \<open>Red Y = Y\<close>.
  This localises the ENTIRE per-branch obligation to: \<open>Red Y = Y\<close> for the rebased
  \<open>Y\<close>.  EMPIRICAL (\<open>/tmp/fb_Yprops.py\<close>): over all 396 inverse-shift sequences,
  \<open>Y = rebaseRow0 (m\<^sub>0\<^sub>0-m\<^sub>1\<^sub>0) 0 X\<close> is non-multi, has \<open>m\<^sub>0\<^sub>0(Y) = m\<^sub>1\<^sub>0(Y)\<close> (=
  \<open>m\<^sub>1\<^sub>0(X)\<close>), satisfies \<open>RedCondA\<close> AND \<open>RedCondB\<close>, and is reduced
  (\<open>Red Y = Y\<close>) 396/396.  So \<open>Red Y = Y\<close> is exactly the keystone-on-A&B
  (@{thm [source] kst_condAB_imp_reduced_core_only}), conditional only on the
  core-keystone \<open>core\<close>: for \<open>m\<^sub>1\<^sub>0(Y) = m\<^sub>1\<^sub>0(X) > 0\<close> the \<open>m\<^sub>1\<^sub>0>0\<close> branch
  (@{thm [source] kst_condAB_imp_reduced_monoT_m10pos}); for \<open>m\<^sub>1\<^sub>0(X) = 0\<close>, \<open>Y\<close>
  is core and \<open>Red Y = Y\<close> IS the core-keystone instance.\<close>

lemma bwd_invshift_via_rebase:
  assumes XT: "X \<in> T_PS"
    and lb: "\<And>j. j < Lng X \<Longrightarrow> entry X 0 0 - entry X 1 0 \<le> entry X 0 j"
    and Yred: "Red (rebaseRow0 (entry X 0 0 - entry X 1 0) 0 X)
             = rebaseRow0 (entry X 0 0 - entry X 1 0) 0 X"
  shows "(IncrFirst ^^ (entry X 0 0 - entry X 1 0)) (Red X) = X"
proof -
  let ?e = "entry X 0 0 - entry X 1 0"
  let ?Y = "rebaseRow0 ?e 0 X"
  \<comment> \<open>\<open>X = IncrFirst\<^bsup>e\<^esup> Y\<close> (pure entry algebra).\<close>
  have XeqIY: "(IncrFirst ^^ ?e) ?Y = X" by (rule bwd_IncrFirst_e_rebaseRow0[OF lb])
  \<comment> \<open>\<open>?Y \<in> T_PS\<close> (same length as \<open>X\<close>, which is nonempty).\<close>
  have Xne: "X \<noteq> []" using XT by (simp add: T_PS_def)
  have Yne: "?Y \<noteq> []"
  proof
    assume "?Y = []"
    hence "Lng ?Y = 0" by simp
    hence "Lng X = 0" by simp
    thus False using Xne by simp
  qed
  have YT: "?Y \<in> T_PS" using Yne by (simp add: T_PS_def)
  \<comment> \<open>\<open>Red X = Red Y\<close>: \<open>Red\<close> is \<open>IncrFirst\<close>-invariant.\<close>
  have RedXeq: "Red X = Red ?Y"
  proof -
    have "Red X = Red ((IncrFirst ^^ ?e) ?Y)" using XeqIY by simp
    also have "\<dots> = Red ?Y" by (rule a1_Red_funpow_IncrFirst[OF YT])
    finally show ?thesis .
  qed
  \<comment> \<open>conclude.\<close>
  have "(IncrFirst ^^ ?e) (Red X) = (IncrFirst ^^ ?e) (Red ?Y)" using RedXeq by simp
  also have "\<dots> = (IncrFirst ^^ ?e) ?Y" using Yred by simp
  also have "\<dots> = X" by (rule XeqIY)
  finally show ?thesis .
qed


(* === Front B: rebaseRow0 preservation bricks === *)
text \<open>\<S>6.6 KEYSTONE BACKWARD, rebaseRow0 PRESERVATION BRICKS (Front B, tag
  pss-bwdcore-rebase).  A uniform row-0 down-shift @{term "rebaseRow0 c d X"}
  with \<open>c\<close> a row-0 lower bound preserves \<open>nextR\<close> (rows \<open>\<le> 1\<close>), hence \<open>hasParent\<close>,
  \<open>parent\<close> and \<open>RedCondA\<close>.  EMPIRICAL (\<open>/tmp/fb_Yprops.py\<close>): over all inverse-shift
  sequences \<open>Y = rebaseRow0 (m\<^sub>0\<^sub>0-m\<^sub>1\<^sub>0) 0 X\<close>, \<open>RedCondA\<close> holds 396/396.\<close>

lemma nextR_rebaseRow0_eq:
  assumes lb: "\<And>j. j < Lng M \<Longrightarrow> c \<le> entry M 0 j" and i: "i \<le> 1"
  shows "nextR (rebaseRow0 c d M) i j0 j1 = nextR M i j0 j1"
proof (cases "i = 0")
  case True
  thus ?thesis by (simp add: nextR_def nextrel0_rebaseRow0_eq[OF lb])
next
  case False
  hence "i = 1" using i by simp
  thus ?thesis by (simp add: nextR_def nextrel1_rebaseRow0_eq[OF lb])
qed

lemma hasParent_rebaseRow0_eq:
  assumes lb: "\<And>j. j < Lng M \<Longrightarrow> c \<le> entry M 0 j" and i: "i \<le> 1"
  shows "hasParent (rebaseRow0 c d M) i j = hasParent M i j"
  unfolding hasParent_def by (simp add: nextR_rebaseRow0_eq[OF lb i])

lemma parent_rebaseRow0_eq:
  assumes lb: "\<And>j. j < Lng M \<Longrightarrow> c \<le> entry M 0 j" and i: "i \<le> 1"
  shows "parent (rebaseRow0 c d M) i j = parent M i j"
  unfolding parent_def by (simp add: nextR_rebaseRow0_eq[OF lb i])

text \<open>\<open>RedCondA\<close> is preserved: row-1 entries are unchanged, and row-0 entries are
  uniformly lowered by \<open>c\<close> (a row-0 lower bound), so the \<open>+1\<close> parent identity
  survives the no-underflow shift.\<close>

lemma RedCondA_rebaseRow0:
  assumes lb: "\<And>j. j < Lng M \<Longrightarrow> c \<le> entry M 0 j" and condA: "RedCondA M"
  shows "RedCondA (rebaseRow0 c 0 M)"
  unfolding RedCondA_def
proof (intro allI impI)
  fix i j1 assume i1: "i \<le> (1::nat)" and hp: "hasParent (rebaseRow0 c 0 M) i j1"
  have hpM: "hasParent M i j1" using hp hasParent_rebaseRow0_eq[OF lb i1] by simp
  have pareq: "parent (rebaseRow0 c 0 M) i j1 = parent M i j1"
    by (rule parent_rebaseRow0_eq[OF lb i1])
  have base: "entry M i (parent M i j1) + 1 = entry M i j1"
    using condA i1 hpM unfolding RedCondA_def by blast
  have parnextR: "nextR M i (parent M i j1) j1"
    using hpM unfolding hasParent_def parent_def by (rule theI')
  have pL: "parent M i j1 < Lng M" and j1L: "j1 < Lng M"
    using parnextR unfolding nextR_def nextrel0_def nextrel1_def by (cases "i=0"; simp_all)+
  show "entry (rebaseRow0 c 0 M) i (parent (rebaseRow0 c 0 M) i j1) + 1
          = entry (rebaseRow0 c 0 M) i j1"
  proof (cases "i = 0")
    case True
    have lbp: "c \<le> entry M 0 (parent M i j1)" using lb[OF pL] True by simp
    have e_par: "entry (rebaseRow0 c 0 M) 0 (parent M i j1) = entry M 0 (parent M i j1) - c"
      using entry_rebaseRow0_0[OF pL] by simp
    have e_j1: "entry (rebaseRow0 c 0 M) 0 j1 = entry M 0 j1 - c"
      using entry_rebaseRow0_0[OF j1L] by simp
    show ?thesis using True pareq e_par e_j1 base lbp by simp
  next
    case False
    hence i1eq: "i = 1" using i1 by simp
    have e_par: "entry (rebaseRow0 c 0 M) 1 (parent M i j1) = entry M 1 (parent M i j1)"
      using entry_rebaseRow0_1[OF pL] by simp
    have e_j1: "entry (rebaseRow0 c 0 M) 1 j1 = entry M 1 j1"
      using entry_rebaseRow0_1[OF j1L] by simp
    show ?thesis using i1eq pareq e_par e_j1 base by simp
  qed
qed

text \<open>\<open>monoT\<close> is preserved by a row-0 lower-bound shift: \<open>zeroT\<close> depends only on
  row 1 (unchanged) and \<open>Lng\<close> (unchanged), and \<open>le0 0 (Lng-1)\<close> is rebase-invariant
  (@{thm [source] le0_rebaseRow0_eq}).\<close>

lemma monoT_rebaseRow0:
  assumes lb: "\<And>j. j < Lng M \<Longrightarrow> c \<le> entry M 0 j" and mono: "monoT M"
  shows "monoT (rebaseRow0 c d M)"
proof -
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have zeq: "zeroT (rebaseRow0 c d M) = zeroT M"
  proof (cases "Lng M = 1")
    case True
    hence L0: "0 < Lng M" by simp
    have "entry (rebaseRow0 c d M) 1 0 = entry M 1 0" by (rule entry_rebaseRow0_1[OF L0])
    thus ?thesis by (simp add: zeroT_def)
  next
    case False
    thus ?thesis by (simp add: zeroT_def)
  qed
  have nzR: "\<not> zeroT (rebaseRow0 c d M)" using nz zeq by simp
  have le0M: "le0 M 0 (Lng M - 1)" using mono nz by (simp add: monoT_def leR_def)
  have "le0 (rebaseRow0 c d M) 0 (Lng (rebaseRow0 c d M) - 1)"
    using le0_rebaseRow0_eq[OF lb, of d 0 "Lng M - 1"] le0M by simp
  thus ?thesis using nzR by (simp add: monoT_def leR_def)
qed


(* === Front B: nu-descent brick === *)
text \<open>\<S>6.6 KEYSTONE BACKWARD, nu-DESCENT BRICK (Front B, tag pss-bwdcore-nu).
  For a monoT sequence \<open>Y\<close> with \<open>m\<^sub>1\<^sub>0 > 0\<close> and \<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0\<close> (so \<open>Y\<close> is the
  \<open>m\<^sub>1\<^sub>0 > 0\<close> A&B sequence whose reducedness the m10pos branch needs), the core
  sequence \<open>Q = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ Y\<close> that the m10pos \<open>Red\<close>-step lands on is
  nu-STRICTLY-smaller than \<open>Y\<close>.  Mechanism: both \<open>Q\<close> and \<open>coreReduce Y\<close> prepend
  the SAME diagonal \<open>diagSeq 0 (m-1)\<close>, so (by @{thm [source] ecrux_TrMax_diag_prefix}
  / @{thm [source] ecrux_Lng}) \<open>betaM Q = betaM Y = betaM (coreReduce Y)\<close>; hence
  \<open>nu Q = 2 betaM Y\<close> while \<open>nu Y = 2 betaM (coreReduce Y) + 1 = 2 betaM Y + 1\<close>.
  EMPIRICAL (\<open>/tmp/fb_nuQ.py\<close>, \<open>/tmp/fb_betaQ.py\<close>): \<open>nu Q = nu Y - 1\<close> 1152/1152
  over the m10pos A&B population.\<close>

lemma nu_diagSeq_m10pos_lt:
  assumes mono: "monoT Y" and m10pos: "0 < entry Y 1 0"
    and eq00: "entry Y 0 0 = entry Y 1 0"
  shows "nu (diagSeq 0 (entry Y 1 0 - 1) @ Y) < nu Y"
proof -
  let ?m = "entry Y 1 0"
  let ?k = "?m - 1"
  let ?Q = "diagSeq 0 ?k @ Y"
  have YT: "Y \<in> T_PS" using mono by (simp add: monoT_def leR_def le0_def T_PS_def)
  have L0: "0 < Lng Y" using YT by (simp add: T_PS_def)
  have Yne: "Y \<noteq> []" using YT by (simp add: T_PS_def)
  have Ynm: "\<not> multiT Y" using mono by (simp add: multiT_def)
  have m00: "entry Y 0 0 = ?m" using eq00 by simp
  \<comment> \<open>diagonal-prefix hypotheses: \<open>k = m-1 < m = m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0\<close>.\<close>
  have kr0: "?k < entry Y 0 0" using m10pos m00 by simp
  have kr1: "?k < entry Y 1 0" using m10pos by simp
  have suck: "Suc ?k = ?m" using m10pos by simp
  \<comment> \<open>\<open>TrMax Q = m + TrMax Y\<close> and \<open>Lng Q = m + Lng Y\<close>, so \<open>betaM Q = betaM Y\<close>.\<close>
  have trQ: "TrMax ?Q = ?m + TrMax Y"
    using ecrux_TrMax_diag_prefix[OF mono kr0 kr1] suck by simp
  have lnQ: "Lng ?Q = ?m + Lng Y" using ecrux_Lng[of ?k Y] suck by simp
  have betaTrM: "TrMax Y \<le> Lng Y" using TrMax_bound[OF YT] L0 by simp
  have betaQ: "betaM ?Q = betaM Y"
    using trQ lnQ betaTrM by (simp add: betaM_def)
  \<comment> \<open>\<open>Q\<close> is core and non-multi, so \<open>nu Q = 2 betaM Q = 2 betaM Y\<close>.\<close>
  have Qe00: "entry ?Q 0 0 = 0" using entry_diagSeq_append_lo[where i=0 and k="?k" and rest=Y] by simp
  have Qe10: "entry ?Q 1 0 = 0" using entry_diagSeq_append_lo[where i=0 and k="?k" and rest=Y] by simp
  have Qmono: "monoT ?Q" using monoT_diagSeq_append[OF Yne mono YT kr0] .
  have Qnm: "\<not> multiT ?Q" using Qmono by (simp add: multiT_def)
  have nuQ: "nu ?Q = 2 * betaM Y"
    using Qnm Qe00 Qe10 betaQ by (simp add: nu_def muMono_def)
  \<comment> \<open>\<open>coreReduce Y = diagSeq 0 (m-1) @ (IncrFirst^m) Y\<close>; same diagonal, so
      \<open>betaM (coreReduce Y) = betaM Y\<close>.\<close>
  let ?R = "(IncrFirst ^^ ?m) Y"
  have crY: "coreReduce Y = diagSeq 0 ?k @ ?R" using coreReduce_m10pos_form[OF m10pos] .
  have Rmono: "monoT ?R" using mono by simp
  have RL0: "0 < Lng ?R" using L0 by simp
  have Re0: "entry ?R 0 0 = entry Y 0 0 + ?m" using entry_funpow_IncrFirst0[OF L0] .
  have Re1: "entry ?R 1 0 = entry Y 1 0" using entry_funpow_IncrFirst1[OF L0] .
  have kr0R: "?k < entry ?R 0 0" using Re0 m00 m10pos by simp
  have kr1R: "?k < entry ?R 1 0" using Re1 m10pos by simp
  have trcr: "TrMax (coreReduce Y) = ?m + TrMax Y"
    using ecrux_TrMax_diag_prefix[OF Rmono kr0R kr1R] crY suck by simp
  have lncr: "Lng (coreReduce Y) = ?m + Lng Y" using crY ecrux_Lng[of ?k ?R] suck by simp
  have betacr: "betaM (coreReduce Y) = betaM Y"
    using trcr lncr betaTrM by (simp add: betaM_def)
  \<comment> \<open>\<open>Y\<close> non-core (\<open>m\<^sub>1\<^sub>0 > 0\<close>), non-multi, so \<open>nu Y = 2 betaM (coreReduce Y) + 1 = 2 betaM Y + 1\<close>.\<close>
  have noncore: "\<not> (entry Y 0 0 = 0 \<and> entry Y 1 0 = 0)" using m10pos by simp
  have nuY: "nu Y = 2 * betaM Y + 1"
    using Ynm noncore betacr by (simp add: nu_def muMono_def)
  show ?thesis using nuQ nuY by simp
qed


(* === Front B: nu-bounded m10pos variant === *)
lemma kst_condAB_imp_reduced_monoT_m10pos_nu:
  assumes core:
    "\<And>N. nu N < B \<Longrightarrow> N \<in> T_PS \<Longrightarrow> monoT N \<Longrightarrow> entry N 0 0 = 0 \<Longrightarrow> entry N 1 0 = 0
       \<Longrightarrow> RedCondA N \<Longrightarrow> RedCondB N \<Longrightarrow> Red N = N"
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and m10pos: "0 < entry M 1 0"
    and condA: "RedCondA M" and condB: "RedCondB M"
    and nuQ: "nu (diagSeq 0 (entry M 1 0 - 1) @ M) < B"
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
    by (rule core[OF nuQ QT QmonoT Qe00 Qe10 QcondA QcondB])
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

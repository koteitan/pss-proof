theory Support_7_051
  imports Frontier_7_055
begin

text \<open>The bridge to a full \<open>T\<^bsub>PS\<^esub>\<close> statement: the SINGLE remaining obligation is the
  purely \<section>6 fact \<open>Red (Red M) \<in> RT\<^bsub>PS\<^esub>\<close> (\<open>Red\<close> is idempotent on its own image),
  empirically true with 0 counterexamples.\<close>

lemma y3s_RedStab_of_Red2:
  assumes "Red (Red M) \<in> RT_PS" shows "RedStab M"
  unfolding RedStab_def by (rule exI[of _ 2]) (use assms in \<open>simp add: numeral_2_eq_2\<close>)

lemma y3s_Trans_dom_iter:
  "(Red ^^ k) M \<in> RT_PS \<Longrightarrow> Trans_Mark_dom (Inl M)"
proof (induction k arbitrary: M)
  case 0 thus ?case by (simp add: m_7_3_Trans_welldef)
next
  case (Suc k)
  have h: "(Red ^^ k) (Red M) \<in> RT_PS" using Suc.prems by (simp add: funpow_swap1)
  have domR: "Trans_Mark_dom (Inl (Red M))" by (rule Suc.IH[OF h])
  show ?case
  proof (cases "M \<in> RT_PS")
    case True thus ?thesis by (simp add: m_7_3_Trans_welldef)
  next
    case False
    show ?thesis by (rule Trans_Mark.domintros(1)) (use False domR in \<open>simp_all\<close>)
  qed
qed

lemma y3s_Mark_dom_iter:
  "(Red ^^ k) M \<in> RT_PS \<Longrightarrow> Trans_Mark_dom (Inr (M, m))"
proof (induction k arbitrary: M)
  case 0 thus ?case by (simp add: m_7_3_Mark_welldef)
next
  case (Suc k)
  have h: "(Red ^^ k) (Red M) \<in> RT_PS" using Suc.prems by (simp add: funpow_swap1)
  have domR: "Trans_Mark_dom (Inr (Red M, m))" by (rule Suc.IH[OF h])
  show ?case
  proof (cases "M \<in> RT_PS")
    case True thus ?thesis by (simp add: m_7_3_Mark_welldef)
  next
    case False
    show ?thesis by (rule Trans_Mark.domintros(2)) (use False domR in \<open>simp_all\<close>)
  qed
qed

lemma y3s_Trans_funpow_Red:
  "(Red ^^ k) M \<in> RT_PS \<Longrightarrow> Trans M = Trans ((Red ^^ k) M)"
proof (induction k arbitrary: M)
  case 0 thus ?case by simp
next
  case (Suc k)
  have h: "(Red ^^ k) (Red M) \<in> RT_PS" using Suc.prems by (simp add: funpow_swap1)
  have IH: "Trans (Red M) = Trans ((Red ^^ k) (Red M))" by (rule Suc.IH[OF h])
  have domM: "Trans_Mark_dom (Inl M)" by (rule y3s_Trans_dom_iter[OF Suc.prems])
  have step: "Trans M = Trans (Red M)"
  proof (cases "M \<in> RT_PS")
    case True
    hence "Red M = M" by (simp add: RT_PS_def)
    thus ?thesis by simp
  next
    case False
    show ?thesis using Trans.psimps[OF domM] False by simp
  qed
  show ?case using step IH by (simp add: funpow_swap1)
qed

lemma y3s_Mark_funpow_Red:
  "(Red ^^ k) M \<in> RT_PS \<Longrightarrow> Mark M m = Mark ((Red ^^ k) M) m"
proof (induction k arbitrary: M)
  case 0 thus ?case by simp
next
  case (Suc k)
  have h: "(Red ^^ k) (Red M) \<in> RT_PS" using Suc.prems by (simp add: funpow_swap1)
  have IH: "Mark (Red M) m = Mark ((Red ^^ k) (Red M)) m" by (rule Suc.IH[OF h])
  have domM: "Trans_Mark_dom (Inr (M, m))" by (rule y3s_Mark_dom_iter[OF Suc.prems])
  have step: "Mark M m = Mark (Red M) m"
  proof (cases "M \<in> RT_PS")
    case True
    hence "Red M = M" by (simp add: RT_PS_def)
    thus ?thesis by simp
  next
    case False
    show ?thesis using Mark.psimps[OF domM] False by simp
  qed
  show ?case using step IH by (simp add: funpow_swap1)
qed

lemma y3s_RightAnces_dom_iter:
  "(Red ^^ k) M \<in> RT_PS \<Longrightarrow> RightAnces_dom M"
proof (induction k arbitrary: M)
  case 0 thus ?case by (simp add: RightAnces_dom_RT[rule_format])
next
  case (Suc k)
  have h: "(Red ^^ k) (Red M) \<in> RT_PS" using Suc.prems by (simp add: funpow_swap1)
  have domR: "RightAnces_dom (Red M)" by (rule Suc.IH[OF h])
  show ?case
  proof (cases "M \<in> RT_PS")
    case True thus ?thesis by (simp add: RightAnces_dom_RT[rule_format])
  next
    case False
    show ?thesis by (rule RightAnces.domintros) (use False domR in \<open>simp_all\<close>)
  qed
qed

lemma y3s_RightAnces_funpow_Red:
  "(Red ^^ k) M \<in> RT_PS \<Longrightarrow> RightAnces M = RightAnces ((Red ^^ k) M)"
proof (induction k arbitrary: M)
  case 0 thus ?case by simp
next
  case (Suc k)
  have h: "(Red ^^ k) (Red M) \<in> RT_PS" using Suc.prems by (simp add: funpow_swap1)
  have IH: "RightAnces (Red M) = RightAnces ((Red ^^ k) (Red M))" by (rule Suc.IH[OF h])
  have domM: "RightAnces_dom M" by (rule y3s_RightAnces_dom_iter[OF Suc.prems])
  have step: "RightAnces M = RightAnces (Red M)"
  proof (cases "M \<in> RT_PS")
    case True
    hence "Red M = M" by (simp add: RT_PS_def)
    thus ?thesis by simp
  next
    case False
    show ?thesis using RightAnces.psimps[OF domM] False by simp
  qed
  show ?case using step IH by (simp add: funpow_swap1)
qed

subsection \<open>The article propositions, on \<open>T\<^bsub>PS\<^esub> \<inter> RedStab\<close>\<close>

text \<open>(1) \<open>p_7_3_Trans_zeroT\<close>.  \<open>zeroT\<close> IS \<open>Red\<close>-invariant on all of \<open>T\<^bsub>PS\<^esub>\<close>
  (@{thm [source] m_6_5_Red_zeroT}), so the \<open>RT\<^bsub>PS\<^esub>\<close> form
  @{thm [source] m_7_3_Trans_zeroT} transports along the \<open>Red\<close>-iteration verbatim.\<close>

theorem y3s_7_3_Trans_zeroT_TPS:
  assumes MT: "M \<in> T_PS" and RS: "RedStab M"
  shows "zeroT M \<longleftrightarrow> Trans M = 0\<^sub>B"
proof -
  obtain k where F: "(Red ^^ k) M \<in> RT_PS" using RS unfolding RedStab_def by blast
  have "Trans M = Trans ((Red ^^ k) M)" by (rule y3s_Trans_funpow_Red[OF F])
  moreover have "zeroT M \<longleftrightarrow> zeroT ((Red ^^ k) M)" by (rule y3s_zeroT_funpow_Red[OF MT])
  moreover have "zeroT ((Red ^^ k) M) \<longleftrightarrow> Trans ((Red ^^ k) M) = 0\<^sub>B"
    by (rule m_7_3_Trans_zeroT[OF F])
  ultimately show ?thesis by simp
qed

text \<open>(2) \<open>p_7_3_Pred_Trans_descend\<close>.  \<open>Pred\<close> commutes with \<open>Red\<close> on all of \<open>T\<^bsub>PS\<^esub>\<close>
  (@{thm [source] m_6_5_Red_Pred}, unconditional), so \<open>(Red\<^sup>k)(Pred M) = Pred ((Red\<^sup>k) M)\<close>,
  which is again reduced (@{thm [source] y3s_Pred_RT_PS}); both sides transport and
  @{thm [source] m_7_3_Pred_Trans_descend} applies at the reduct.\<close>

theorem y3s_7_3_Pred_Trans_descend_TPS:
  assumes MT: "M \<in> T_PS" and RS: "RedStab M" and L: "1 < Lng M"
  shows "lessBT (Trans (Pred M)) (Trans M)"
proof -
  obtain k where F: "(Red ^^ k) M \<in> RT_PS" using RS unfolding RedStab_def by blast
  have LF: "1 < Lng ((Red ^^ k) M)" using y3s_Lng_funpow_Red[OF MT] L by simp
  have PF: "Pred ((Red ^^ k) M) \<in> RT_PS" by (rule y3s_Pred_RT_PS[OF F LF])
  have e: "(Red ^^ k) (Pred M) = Pred ((Red ^^ k) M)" by (rule y3s_Pred_funpow_Red[OF MT])
  have PFR: "(Red ^^ k) (Pred M) \<in> RT_PS" using e PF by simp
  have tp: "Trans (Pred M) = Trans (Pred ((Red ^^ k) M))"
    using y3s_Trans_funpow_Red[OF PFR] e by simp
  have tm: "Trans M = Trans ((Red ^^ k) M)" by (rule y3s_Trans_funpow_Red[OF F])
  show ?thesis
    using m_7_3_Pred_Trans_descend[rule_format, OF F LF] tp tm by simp
qed

text \<open>(3) \<open>p_7_4_RightAnces_RightNodes\<close>.  \<open>RightAnces\<close> has the SAME non-reduced
  branch \<open>RightAnces M := RightAnces (Red M)\<close>, so both sides transport along the
  same iteration.\<close>

theorem y3s_7_4_RightAnces_RightNodes_TPS:
  assumes RS: "RedStab M"
  shows "RightAnces M = RightNodes (Trans M)"
proof -
  obtain k where F: "(Red ^^ k) M \<in> RT_PS" using RS unfolding RedStab_def by blast
  have "RightAnces M = RightAnces ((Red ^^ k) M)" by (rule y3s_RightAnces_funpow_Red[OF F])
  also have "\<dots> = RightNodes (Trans ((Red ^^ k) M))"
    by (rule m_7_4_RightAnces_RightNodes[OF F])
  also have "\<dots> = RightNodes (Trans M)" using y3s_Trans_funpow_Red[OF F] by simp
  finally show ?thesis .
qed

text \<open>(4) \<open>p_7_4_RightAnces_zeroT\<close>.\<close>

theorem y3s_7_4_RightAnces_zeroT_TPS:
  assumes MT: "M \<in> T_PS" and RS: "RedStab M"
  shows "zeroT M \<longleftrightarrow> RightAnces M = []"
proof -
  have "RightAnces M = RightNodes (Trans M)"
    by (rule y3s_7_4_RightAnces_RightNodes_TPS[OF RS])
  moreover have "RightNodes (Trans M) = [] \<longleftrightarrow> Trans M = 0\<^sub>B"
    by (rule rnsub_RightNodes_empty_iff)
  moreover have "zeroT M \<longleftrightarrow> Trans M = 0\<^sub>B" by (rule y3s_7_3_Trans_zeroT_TPS[OF MT RS])
  ultimately show ?thesis by simp
qed

section \<open>r75: RED2 --- \<open>Red (Red M) \<in> RT\<^bsub>PS\<^esub>\<close> for every \<open>M \<in> T\<^bsub>PS\<^esub>\<close>\<close>

text \<open>
  \<open>Red\<close> is NOT idempotent on \<open>T\<^bsub>PS\<^esub>\<close> (correction A4, \<open>M = (0,0)(0,2)\<close>), but TWO
  steps always suffice: \<open>Red (Red M)\<close> is reduced.  This closes the \<section>7 scope gap,
  because \<open>RedStab = T\<^bsub>PS\<^esub>\<close> follows (@{thm [source] y3s_RedStab_of_Red2}).

  \<^bold>\<open>Mechanism.\<close>  For multi \<open>M\<close>, \<open>Red M = \<Oplus>\<^bsub>J\<^esub> Red (P M\<^sub>J)\<close> concatenates the
  reduced components; the concatenation need NOT be reduced, because the
  \<open>P\<close>-boundaries can MOVE (components merge: \<open>(0,0) \<oplus> (2,2)\<close> is mono, not the
  two-component \<open>(0,0),(2,2)\<close>).  What survives the first \<open>Red\<close> is the single
  invariant that makes the SECOND \<open>Red\<close> stable:

    \<^bold>\<open>(D)\<close> every \<open>P\<close>-component of \<open>Red M\<close> has a \<^emph>\<open>diagonal left end\<close>
        (\<open>C\<^bsub>0,0\<^esub> = C\<^bsub>1,0\<^esub>\<close>).

  Indeed the left end of \<open>Red C\<close> is \<open>C\<^bsub>1,0\<^esub>\<close> in BOTH rows
  (@{thm [source] fin_Red_leftend_row0_eq_m10}, @{thm [source] m_6_6_Red_leftend_1}),
  and the \<open>P\<close>-components' left ends are exactly the row-0 left-minima
  (@{thm [source] idxsum_leftend_lmin}), which for a concatenation of \<open>Red\<close>-blocks
  can only sit at a block boundary (each \<open>Red\<close>-block attains its row-0 minimum
  \<^emph>\<open>strictly\<close> at its own left end).

  Given (D), the second \<open>Red\<close> cannot merge anything: the new blocks
  \<open>Red (P X\<^sub>I)\<close> have left ends \<open>(P X\<^sub>I)\<^bsub>1,0\<^esub> = (P X\<^sub>I)\<^bsub>0,0\<^esub>\<close>, which are
  non-increasing in \<open>I\<close> (@{thm [source] m_6_4_P_leftend_mono}); so every block
  boundary is still a row-0 left-minimum, \<open>P\<close> splits exactly there
  (@{thm [source] m_6_2_P_additive}), and each block is reduced
  (@{thm [source] idem_nonmulti}).  @{thm [source] m_6_6_P_reduced} concludes.

  Empirically stress-tested before proving: (D) exercised at 141653 no-parent
  indices with 0 violations; the main lemma \<open>y3r_Red_reduced_of_diag\<close> below
  exercised on 3305 \<^emph>\<open>non-reduced\<close> \<open>X\<close> (i.e. genuinely non-vacuous) with 0
  violations; and no counterexample to RED2 itself in a fresh exhaustive sweep.
\<close>

lemma y3r_Red_TPS:
  assumes MT: "M \<in> T_PS" shows "Red M \<in> T_PS"
proof -
  have "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  moreover have "0 < Lng M" using MT by (auto simp: T_PS_def)
  ultimately show ?thesis by (auto simp: T_PS_def)
qed

text \<open>\<open>Red\<close> preserves non-multiness on ALL of \<open>T\<^bsub>PS\<^esub>\<close> (the \<open>anchored_slice\<close>
  version @{thm [source] m_6_5_Red_not_multiT} is not needed: \<open>zeroT\<close>- and
  \<open>monoT\<close>-preservation are already unconditional).\<close>

lemma y3r_Red_nonmulti:
  assumes MT: "M \<in> T_PS" and nm: "\<not> multiT M"
  shows "\<not> multiT (Red M)"
proof (cases "zeroT M")
  case True
  hence "zeroT (Red M)" using m_6_5_Red_zeroT[OF MT] by simp
  thus ?thesis by (simp add: multiT_def)
next
  case False
  hence "monoT M" using nm by (simp add: multiT_def)
  hence "M \<in> PT_PS" using MT by (simp add: PT_PS_def)
  hence "monoT (Red M)" by (rule m_6_5_Red_preserves_monoT)
  thus ?thesis by (simp add: multiT_def)
qed

lemma y3r_P_nonmulti:
  assumes MT: "M \<in> T_PS" and nm: "\<not> multiT M"
  shows "P M = [M]"
proof -
  have "\<not> (1 < length (P M))" using m_6_2_P_components_2[OF MT] nm by simp
  moreover have "P M \<noteq> []" by (rule P_nonempty)
  ultimately obtain A where PA: "P M = [A]" by (cases "P M") auto
  have "concat (P M) = M" by (rule idxsum_concat_P)
  thus ?thesis using PA by simp
qed

text \<open>In a non-multi sequence the ONLY row-0 left-minimum is the left end
  (a left-minimum would be a \<open>P\<close>-component left end, and there is only one
  component).\<close>

lemma y3r_nonmulti_lmin0:
  assumes MT: "M \<in> T_PS" and nm: "\<not> multiT M"
    and rl: "r < Lng M" and lmin: "\<forall>j<r. entry M 0 r \<le> entry M 0 j"
  shows "r = 0"
proof -
  have rle: "r \<le> Lng M - 1" using rl by simp
  obtain J where JL: "J < length (P M)" and Jr: "IdxSum (P M) ! J = r"
    using idxsum_lmin_leftend[OF MT rle] lmin by auto
  have "P M = [M]" by (rule y3r_P_nonmulti[OF MT nm])
  hence "J = 0" using JL by simp
  hence "r = IdxSum (P M) ! 0" using Jr by simp
  also have "\<dots> = 0" by (simp add: idxsum_nth)
  finally show ?thesis .
qed

text \<open>The left end of \<open>Red M\<close> is \<open>M\<^bsub>1,0\<^esub>\<close> in both rows, for non-multi \<open>M\<close>
  (\<open>zeroT\<close> case: \<open>Red M = ((0,0))\<close> and \<open>M\<^bsub>1,0\<^esub> = 0\<close>).\<close>

lemma y3r_Red_head:
  assumes MT: "M \<in> T_PS" and nm: "\<not> multiT M"
  shows "entry (Red M) 0 0 = entry M 1 0 \<and> entry (Red M) 1 0 = entry M 1 0"
proof (cases "zeroT M")
  case True
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have r: "Red M = [(0,0)]" using Red.psimps[OF dom] True by simp
  have "entry M 1 0 = 0" using True by (simp add: zeroT_def)
  thus ?thesis using r by (simp add: entry_def)
next
  case False
  hence mono: "monoT M" using nm by (simp add: multiT_def)
  have a: "entry (Red M) 0 0 = entry M 1 0" by (rule fin_Red_leftend_row0_eq_m10[OF MT mono])
  have b: "entry (Red M) 1 0 = entry M 1 0" by (rule m_6_6_Red_leftend_1[OF MT])
  from a b show ?thesis by simp
qed

text \<open>\<open>Red\<close> of a non-multi sequence attains its row-0 minimum \<^bold>\<open>strictly\<close> at the
  left end.  This is what forbids a \<open>P\<close>-cut inside a \<open>Red\<close>-block.\<close>

lemma y3r_Red_strict_min:
  assumes MT: "M \<in> T_PS" and nm: "\<not> multiT M"
    and r0: "0 < r" and rl: "r < Lng (Red M)"
  shows "entry (Red M) 0 0 < entry (Red M) 0 r"
proof (rule ccontr)
  assume ne: "\<not> entry (Red M) 0 0 < entry (Red M) 0 r"
  have RT: "Red M \<in> T_PS" by (rule y3r_Red_TPS[OF MT])
  have Rnm: "\<not> multiT (Red M)" by (rule y3r_Red_nonmulti[OF MT nm])
  have nz: "\<not> zeroT M"
  proof
    assume "zeroT M"
    hence "zeroT (Red M)" using m_6_5_Red_zeroT[OF MT] by simp
    hence "Lng (Red M) = 1" by (simp add: zeroT_def)
    thus False using r0 rl by simp
  qed
  hence mono: "monoT M" using nm by (simp add: multiT_def)
  have minr: "\<forall>k < Lng (Red M). entry (Red M) 0 0 \<le> entry (Red M) 0 k"
    by (rule m_6_5_Red_leftend_row0_min[OF MT mono])
  have lmin: "\<forall>j<r. entry (Red M) 0 r \<le> entry (Red M) 0 j"
  proof (intro allI impI)
    fix j assume jr: "j < r"
    have "entry (Red M) 0 r \<le> entry (Red M) 0 0" using ne by simp
    also have "\<dots> \<le> entry (Red M) 0 j" using minr jr rl by simp
    finally show "entry (Red M) 0 r \<le> entry (Red M) 0 j" .
  qed
  have "r = 0" by (rule y3r_nonmulti_lmin0[OF RT Rnm rl lmin])
  thus False using r0 by simp
qed

subsection \<open>Two list-level lemmas about concatenations of \<open>Red\<close>-blocks\<close>

text \<open>If the blocks are non-multi, attain their row-0 minimum strictly at their own
  left end, and have non-increasing left ends, then \<open>P\<close> of the concatenation
  recovers exactly the blocks.  (Pure list induction via
  @{thm [source] m_6_2_P_additive}; no \<open>Lng\<close>-induction on \<open>Red\<close>.)\<close>

lemma y3r_P_concat:
  assumes "R \<noteq> []"
    and "\<forall>I<length R. R!I \<in> T_PS"
    and "\<forall>I<length R. \<not> multiT (R!I)"
    and "\<forall>I<length R. \<forall>r. 0 < r \<longrightarrow> r < Lng (R!I) \<longrightarrow> entry (R!I) 0 0 < entry (R!I) 0 r"
    and "\<forall>I. Suc I < length R \<longrightarrow> entry (R!(Suc I)) 0 0 \<le> entry (R!I) 0 0"
  shows "P (concat R) = R"
  using assms
proof (induction R)
  case Nil thus ?case by simp
next
  case (Cons C Rs)
  have CT: "C \<in> T_PS" using Cons.prems(2) by (metis nth_Cons_0 length_greater_0_conv list.discI)
  have Cnm: "\<not> multiT C" using Cons.prems(3) by (metis nth_Cons_0 length_greater_0_conv list.discI)
  have Cmin: "\<forall>r. 0 < r \<longrightarrow> r < Lng C \<longrightarrow> entry C 0 0 < entry C 0 r"
    using Cons.prems(4) by (metis nth_Cons_0 length_greater_0_conv list.discI)
  have LC: "0 < Lng C" using CT by (auto simp: T_PS_def)
  show ?case
  proof (cases "Rs = []")
    case True
    have "concat (C # Rs) = C" using True by simp
    thus ?thesis using y3r_P_nonmulti[OF CT Cnm] True by simp
  next
    case False
    then obtain D Rs' where RsD: "Rs = D # Rs'" by (cases Rs) auto
    let ?W = "concat (C # Rs)"
    have Wdec: "?W = C @ concat Rs" by simp
    have DT: "D \<in> T_PS"
      using Cons.prems(2)[rule_format, of "Suc 0"] RsD by simp
    have LD: "0 < Lng D" using DT by (auto simp: T_PS_def)
    have LRs: "0 < Lng (concat Rs)" using RsD LD by simp
    have WT: "?W \<in> T_PS" using LC by (auto simp: T_PS_def)
    \<comment> \<open>the cut point\<close>
    let ?j0 = "Lng C"
    have j0pos: "0 < ?j0" using LC by simp
    have LW: "Lng ?W = Lng C + Lng (concat Rs)" using Wdec by (metis length_append)
    have j0lt: "?j0 < Lng ?W" using LW LRs by linarith
    have j0le: "?j0 \<le> Lng ?W - 1" using j0lt by linarith
    \<comment> \<open>entries of the concatenation\<close>
    have eC: "\<And>i j. j < Lng C \<Longrightarrow> entry ?W i j = entry C i j"
      by (simp add: entry_def nth_append)
    have eD: "\<And>i. entry ?W i ?j0 = entry D i 0"
      using RsD LD by (simp add: entry_def nth_append)
    \<comment> \<open>adjacency: the left end of \<open>D\<close> is \<open>\<le>\<close> the left end of \<open>C\<close>\<close>
    have adj: "entry D 0 0 \<le> entry C 0 0"
      using Cons.prems(5)[rule_format, of 0] RsD by simp
    have lmin: "\<forall>j<?j0. entry ?W 0 ?j0 \<le> entry ?W 0 j"
    proof (intro allI impI)
      fix j assume jl: "j < ?j0"
      have step: "entry C 0 0 \<le> entry C 0 j"
      proof (cases "j = 0")
        case True thus ?thesis by simp
      next
        case False
        hence jpos: "0 < j" by simp
        have "entry C 0 0 < entry C 0 j" by (rule Cmin[rule_format, OF jpos jl])
        thus ?thesis by simp
      qed
      have "entry ?W 0 ?j0 = entry D 0 0" by (rule eD)
      also have "\<dots> \<le> entry C 0 0" by (rule adj)
      also have "\<dots> \<le> entry C 0 j" by (rule step)
      also have "entry C 0 j = entry ?W 0 j" using jl by (simp add: entry_def nth_append)
      finally show "entry ?W 0 ?j0 \<le> entry ?W 0 j" .
    qed
    have split: "P ?W = P (seg ?W 0 (?j0 - 1)) @ P (seg ?W ?j0 (Lng ?W - 1))"
      by (rule m_6_2_P_additive[OF WT j0pos j0le]) (use lmin in auto)
    have segL: "seg ?W 0 (?j0 - 1) = C"
    proof -
      have "seg ?W 0 (?j0 - 1) = take (Suc (?j0 - 1)) ?W"
        by (rule seg_0_eq_take) (use LC j0lt in linarith)
      also have "Suc (?j0 - 1) = ?j0" using LC by simp
      also have "take ?j0 ?W = C" using Wdec by simp
      finally show ?thesis .
    qed
    have segR: "seg ?W ?j0 (Lng ?W - 1) = concat Rs"
    proof -
      have "seg ?W ?j0 (Lng ?W - 1) = drop ?j0 ?W"
        by (rule seg_to_last_eq_drop) (use LC j0lt in linarith)
      also have "drop ?j0 ?W = concat Rs" using Wdec by simp
      finally show ?thesis .
    qed
    have PC: "P C = [C]" by (rule y3r_P_nonmulti[OF CT Cnm])
    have IH: "P (concat Rs) = Rs"
    proof (rule Cons.IH)
      show "Rs \<noteq> []" using RsD by simp
      show "\<forall>I<length Rs. Rs ! I \<in> T_PS" using Cons.prems(2) by auto
      show "\<forall>I<length Rs. \<not> multiT (Rs ! I)" using Cons.prems(3) by auto
      show "\<forall>I<length Rs. \<forall>r. 0 < r \<longrightarrow> r < Lng (Rs ! I)
              \<longrightarrow> entry (Rs ! I) 0 0 < entry (Rs ! I) 0 r"
        using Cons.prems(4) by auto
      show "\<forall>I. Suc I < length Rs \<longrightarrow> entry (Rs ! Suc I) 0 0 \<le> entry (Rs ! I) 0 0"
        using Cons.prems(5) by auto
    qed
    show ?thesis using split segL segR PC IH by simp
  qed
qed

text \<open>In a concatenation of blocks that each have a diagonal left end and a strict
  row-0 minimum there, EVERY row-0 left-minimum of the concatenation is a block
  left end --- hence carries a diagonal.\<close>

lemma y3r_concat_lmin_diag:
  assumes "\<forall>I<length R. R!I \<in> T_PS"
    and "\<forall>I<length R. entry (R!I) 0 0 = entry (R!I) 1 0"
    and "\<forall>I<length R. \<forall>r. 0 < r \<longrightarrow> r < Lng (R!I) \<longrightarrow> entry (R!I) 0 0 < entry (R!I) 0 r"
    and "p < Lng (concat R)"
    and "\<forall>j<p. entry (concat R) 0 p \<le> entry (concat R) 0 j"
  shows "entry (concat R) 0 p = entry (concat R) 1 p"
  using assms
proof (induction R arbitrary: p)
  case Nil thus ?case by simp
next
  case (Cons C Rs)
  have CT: "C \<in> T_PS" using Cons.prems(1) by (metis nth_Cons_0 length_greater_0_conv list.discI)
  have Cdiag: "entry C 0 0 = entry C 1 0"
    using Cons.prems(2) by (metis nth_Cons_0 length_greater_0_conv list.discI)
  have Cmin: "\<forall>r. 0 < r \<longrightarrow> r < Lng C \<longrightarrow> entry C 0 0 < entry C 0 r"
    using Cons.prems(3) by (metis nth_Cons_0 length_greater_0_conv list.discI)
  have LC: "0 < Lng C" using CT by (auto simp: T_PS_def)
  have Wdec: "concat (C # Rs) = C @ concat Rs" by simp
  have eC: "\<And>i j. j < Lng C \<Longrightarrow> entry (C @ concat Rs) i j = entry C i j"
    by (simp add: entry_def nth_append)
  have eR: "\<And>i j. entry (C @ concat Rs) i (Lng C + j) = entry (concat Rs) i j"
    by (simp add: entry_def nth_append)
  have lmA: "\<forall>j<p. entry (C @ concat Rs) 0 p \<le> entry (C @ concat Rs) 0 j"
    using Cons.prems(5) Wdec by simp
  have pltA: "p < Lng (C @ concat Rs)" using Cons.prems(4) Wdec by simp
  show ?case
  proof (cases "p < Lng C")
    case True
    have p0: "p = 0"
    proof (rule ccontr)
      assume "p \<noteq> 0"
      hence pp: "0 < p" by simp
      have lt: "entry C 0 0 < entry C 0 p" by (rule Cmin[rule_format, OF pp True])
      have "entry (C @ concat Rs) 0 p \<le> entry (C @ concat Rs) 0 0"
        using lmA pp by simp
      hence "entry C 0 p \<le> entry C 0 0" using eC[OF True] eC[OF LC] by simp
      thus False using lt by simp
    qed
    have "entry (C @ concat Rs) 0 p = entry (C @ concat Rs) 1 p"
      using p0 Cdiag eC[OF LC] by simp
    thus ?thesis using Wdec by simp
  next
    case False
    hence pge: "Lng C \<le> p" by simp
    let ?p' = "p - Lng C"
    have pe: "p = Lng C + ?p'" using pge by simp
    have p'lt: "?p' < Lng (concat Rs)" using pltA pge by simp
    have lmin': "\<forall>j<?p'. entry (concat Rs) 0 ?p' \<le> entry (concat Rs) 0 j"
    proof (intro allI impI)
      fix j assume jp: "j < ?p'"
      have jl2: "Lng C + j < p" using jp pe by simp
      have "entry (concat Rs) 0 ?p' = entry (C @ concat Rs) 0 p"
        using eR[of 0 ?p'] pe by simp
      also have "\<dots> \<le> entry (C @ concat Rs) 0 (Lng C + j)"
        using lmA jl2 by simp
      also have "\<dots> = entry (concat Rs) 0 j" using eR[of 0 j] by simp
      finally show "entry (concat Rs) 0 ?p' \<le> entry (concat Rs) 0 j" .
    qed
    have IHres: "entry (concat Rs) 0 ?p' = entry (concat Rs) 1 ?p'"
    proof (rule Cons.IH)
      show "\<forall>I<length Rs. Rs ! I \<in> T_PS" using Cons.prems(1) by auto
      show "\<forall>I<length Rs. entry (Rs ! I) 0 0 = entry (Rs ! I) 1 0" using Cons.prems(2) by auto
      show "\<forall>I<length Rs. \<forall>r. 0 < r \<longrightarrow> r < Lng (Rs ! I)
              \<longrightarrow> entry (Rs ! I) 0 0 < entry (Rs ! I) 0 r" using Cons.prems(3) by auto
      show "?p' < Lng (concat Rs)" by (rule p'lt)
      show "\<forall>j<?p'. entry (concat Rs) 0 ?p' \<le> entry (concat Rs) 0 j" by (rule lmin')
    qed
    have "entry (C @ concat Rs) 0 p = entry (C @ concat Rs) 1 p"
      using eR[of 0 ?p'] eR[of 1 ?p'] IHres pe by simp
    thus ?thesis using Wdec by simp
  qed
qed

subsection \<open>The \<open>P\<close>-component left ends, and invariant (D)\<close>

lemma y3r_comp_head:
  assumes MT: "M \<in> T_PS" and IL: "I < length (P M)"
  shows "entry (P M ! I) i 0 = entry M i (IdxSum (P M) ! I)"
proof -
  let ?s = "IdxSum (P M) ! I"
  have sdef: "?s = sum_list (map length (take I (P M)))"
    using IL by (simp add: idxsum_nth)
  have blk: "P M ! I = take (Lng (P M ! I)) (drop ?s (concat (P M)))"
    using idxsum_concat_block[OF IL] sdef by simp
  have cc: "concat (P M) = M" by (rule idxsum_concat_P)
  have pos: "0 < Lng (P M ! I)" by (rule idxsum_P_component_nonempty[OF MT IL])
  have sle: "?s \<le> Lng M - 1" using idxsum_leftend_lmin[OF MT IL] by simp
  have LM: "0 < Lng M" using MT by (auto simp: T_PS_def)
  have slt: "?s < Lng M" using sle LM by linarith
  define k where "k = Lng (P M ! I)"
  have kpos: "0 < k" using pos k_def by simp
  have blk': "P M ! I = take k (drop ?s M)" using blk cc k_def by simp
  have "(P M ! I) ! 0 = (drop ?s M) ! 0" using blk' kpos by simp
  also have "\<dots> = M ! ?s" using slt by simp
  finally have h: "(P M ! I) ! 0 = M ! ?s" .
  show ?thesis by (simp add: entry_def h)
qed

text \<open>\<^bold>\<open>Invariant (D)\<close>: every \<open>P\<close>-component of \<open>Red M\<close> has a diagonal left end.\<close>

lemma y3r_Red_comp_diag:
  assumes MT: "M \<in> T_PS"
  shows "\<forall>I < length (P (Red M)). entry (P (Red M) ! I) 0 0 = entry (P (Red M) ! I) 1 0"
proof -
  let ?X = "Red M"
  have XT: "?X \<in> T_PS" by (rule y3r_Red_TPS[OF MT])
  \<comment> \<open>the left-minimum-diagonal property of \<open>X\<close> itself\<close>
  have LMD: "\<And>p. p < Lng ?X \<Longrightarrow> (\<forall>j<p. entry ?X 0 p \<le> entry ?X 0 j)
                 \<Longrightarrow> entry ?X 0 p = entry ?X 1 p"
  proof -
    fix p assume plt: "p < Lng ?X" and lm: "\<forall>j<p. entry ?X 0 p \<le> entry ?X 0 j"
    show "entry ?X 0 p = entry ?X 1 p"
    proof (cases "multiT M")
      case False
      \<comment> \<open>\<open>X\<close> is non-multi, so \<open>p = 0\<close>, and the left end is diagonal.\<close>
      have Xnm: "\<not> multiT ?X" by (rule y3r_Red_nonmulti[OF MT False])
      have "p = 0" by (rule y3r_nonmulti_lmin0[OF XT Xnm plt lm])
      thus ?thesis using y3r_Red_head[OF MT False] by simp
    next
      case True
      have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
      have nz: "\<not> zeroT M" using True by (simp add: multiT_def)
      have RX: "?X = concat (map Red (P M))"
        using Red.psimps[OF dom] nz True by simp
      let ?R = "map Red (P M)"
      have comp: "\<And>I. I < length (P M) \<Longrightarrow> P M ! I \<in> T_PS \<and> \<not> multiT (P M ! I)"
      proof -
        fix I assume IL: "I < length (P M)"
        have mem: "P M ! I \<in> set (P M)" using IL by (rule nth_mem)
        have zm: "zeroT (P M ! I) \<or> monoT (P M ! I)"
          using m_6_2_P_components_1[OF MT] mem by blast
        have pos: "0 < Lng (P M ! I)" by (rule idxsum_P_component_nonempty[OF MT IL])
        thus "P M ! I \<in> T_PS \<and> \<not> multiT (P M ! I)"
          using zm by (auto simp: T_PS_def multiT_def)
      qed
      have h1: "\<forall>I<length ?R. ?R!I \<in> T_PS"
        using comp y3r_Red_TPS by auto
      have h2: "\<forall>I<length ?R. entry (?R!I) 0 0 = entry (?R!I) 1 0"
      proof (intro allI impI)
        fix I assume IL: "I < length ?R"
        hence IL': "I < length (P M)" by simp
        have "?R!I = Red (P M ! I)" using IL' by simp
        thus "entry (?R!I) 0 0 = entry (?R!I) 1 0"
          using y3r_Red_head[of "P M ! I"] comp[OF IL'] by simp
      qed
      have h3: "\<forall>I<length ?R. \<forall>r. 0 < r \<longrightarrow> r < Lng (?R!I)
                    \<longrightarrow> entry (?R!I) 0 0 < entry (?R!I) 0 r"
      proof (intro allI impI)
        fix I r
        assume IL: "I < length ?R" and r0: "0 < r" and rl: "r < Lng (?R!I)"
        have IL': "I < length (P M)" using IL by simp
        have eq: "?R!I = Red (P M ! I)" using IL' by simp
        have c: "P M ! I \<in> T_PS \<and> \<not> multiT (P M ! I)" by (rule comp[OF IL'])
        have rl': "r < Lng (Red (P M ! I))" using rl eq by simp
        have "entry (Red (P M ! I)) 0 0 < entry (Red (P M ! I)) 0 r"
          by (rule y3r_Red_strict_min[OF conjunct1[OF c] conjunct2[OF c] r0 rl'])
        thus "entry (?R!I) 0 0 < entry (?R!I) 0 r" using eq by simp
      qed
      have plt': "p < Lng (concat ?R)" using plt RX by simp
      have lm': "\<forall>j<p. entry (concat ?R) 0 p \<le> entry (concat ?R) 0 j" using lm RX by simp
      have "entry (concat ?R) 0 p = entry (concat ?R) 1 p"
        by (rule y3r_concat_lmin_diag[OF h1 h2 h3 plt' lm'])
      thus ?thesis using RX by simp
    qed
  qed
  show ?thesis
  proof (intro allI impI)
    fix I assume IL: "I < length (P ?X)"
    let ?s = "IdxSum (P ?X) ! I"
    have lm: "?s \<le> Lng ?X - 1 \<and> (\<forall>j < ?s. entry ?X 0 ?s \<le> entry ?X 0 j)"
      using idxsum_leftend_lmin[OF XT IL] by simp
    have LX: "0 < Lng ?X" using XT by (auto simp: T_PS_def)
    have sle: "?s \<le> Lng ?X - 1" using lm by simp
    have slt: "?s < Lng ?X" using sle LX by linarith
    have "entry ?X 0 ?s = entry ?X 1 ?s" using LMD[OF slt] lm by simp
    thus "entry (P ?X ! I) 0 0 = entry (P ?X ! I) 1 0"
      using y3r_comp_head[OF XT IL, of 0] y3r_comp_head[OF XT IL, of 1] by simp
  qed
qed

subsection \<open>The main lemma and RED2\<close>

text \<open>If every \<open>P\<close>-component of \<open>X\<close> has a diagonal left end, then \<open>Red X\<close> is
  reduced.  (\<^bold>\<open>Not\<close> vacuous: exercised on 3305 non-reduced \<open>X\<close> in the sweep.)\<close>

lemma y3r_Red_reduced_of_diag:
  assumes XT: "X \<in> T_PS"
    and H: "\<forall>I < length (P X). entry (P X ! I) 0 0 = entry (P X ! I) 1 0"
  shows "Red X \<in> RT_PS"
proof (cases "multiT X")
  case False
  have "Red (Red X) = Red X" by (rule idem_nonmulti[OF XT False])
  thus ?thesis using y3r_Red_TPS[OF XT] by (simp add: RT_PS_def)
next
  case True
  let ?Q = "P X"  let ?R = "map Red ?Q"
  have dom: "Red_dom X" by (rule m_6_5_Red_welldef[OF XT])
  have nz: "\<not> zeroT X" using True by (simp add: multiT_def)
  have RX: "Red X = concat ?R" using Red.psimps[OF dom] nz True by simp
  have RXT: "Red X \<in> T_PS" by (rule y3r_Red_TPS[OF XT])
  have comp: "\<And>I. I < length ?Q \<Longrightarrow> ?Q ! I \<in> T_PS \<and> \<not> multiT (?Q ! I)"
  proof -
    fix I assume IL: "I < length ?Q"
    have mem: "?Q ! I \<in> set ?Q" using IL by (rule nth_mem)
    have zm: "zeroT (?Q ! I) \<or> monoT (?Q ! I)"
      using m_6_2_P_components_1[OF XT] mem by blast
    have pos: "0 < Lng (?Q ! I)" by (rule idxsum_P_component_nonempty[OF XT IL])
    thus "?Q ! I \<in> T_PS \<and> \<not> multiT (?Q ! I)"
      using zm by (auto simp: T_PS_def multiT_def)
  qed
  have h0: "?R \<noteq> []" using P_nonempty by simp
  have h1: "\<forall>I<length ?R. ?R!I \<in> T_PS" using comp y3r_Red_TPS by auto
  have h2: "\<forall>I<length ?R. \<not> multiT (?R!I)"
    using comp y3r_Red_nonmulti by auto
  have h3: "\<forall>I<length ?R. \<forall>r. 0 < r \<longrightarrow> r < Lng (?R!I)
                \<longrightarrow> entry (?R!I) 0 0 < entry (?R!I) 0 r"
  proof (intro allI impI)
    fix I r
    assume IL: "I < length ?R" and r0: "0 < r" and rl: "r < Lng (?R!I)"
    have IL': "I < length ?Q" using IL by simp
    have eq: "?R!I = Red (?Q ! I)" using IL' by simp
    have c: "?Q ! I \<in> T_PS \<and> \<not> multiT (?Q ! I)" by (rule comp[OF IL'])
    have rl': "r < Lng (Red (?Q ! I))" using rl eq by simp
    have "entry (Red (?Q ! I)) 0 0 < entry (Red (?Q ! I)) 0 r"
      by (rule y3r_Red_strict_min[OF conjunct1[OF c] conjunct2[OF c] r0 rl'])
    thus "entry (?R!I) 0 0 < entry (?R!I) 0 r" using eq by simp
  qed
  \<comment> \<open>the key monotonicity: block left ends are non-increasing, BECAUSE of (D)\<close>
  have h4: "\<forall>I. Suc I < length ?R \<longrightarrow> entry (?R!(Suc I)) 0 0 \<le> entry (?R!I) 0 0"
  proof (intro allI impI)
    fix I assume IL: "Suc I < length ?R"
    hence SL: "Suc I < length ?Q" and IL': "I < length ?Q" by simp_all
    have e1: "entry (?R!(Suc I)) 0 0 = entry (?Q!(Suc I)) 1 0"
      using y3r_Red_head[of "?Q ! (Suc I)"] comp[OF SL] SL by simp
    have e2: "entry (?R!I) 0 0 = entry (?Q!I) 1 0"
      using y3r_Red_head[of "?Q ! I"] comp[OF IL'] IL' by simp
    have d1: "entry (?Q!(Suc I)) 1 0 = entry (?Q!(Suc I)) 0 0" using H SL by simp
    have d2: "entry (?Q!I) 1 0 = entry (?Q!I) 0 0" using H IL' by simp
    have mono: "entry (?Q!(Suc I)) 0 0 \<le> entry (?Q!I) 0 0"
      using m_6_4_P_leftend_mono[OF XT, of I "Suc I"] SL by simp
    show "entry (?R!(Suc I)) 0 0 \<le> entry (?R!I) 0 0"
      using e1 e2 d1 d2 mono by simp
  qed
  have PR: "P (Red X) = ?R" using y3r_P_concat[OF h0 h1 h2 h3 h4] RX by simp
  \<comment> \<open>each block is reduced\<close>
  have "\<forall>J < Lng (P (Red X)). P (Red X) ! J \<in> RT_PS"
  proof (intro allI impI)
    fix J assume JL: "J < Lng (P (Red X))"
    hence JL': "J < length ?Q" using PR by simp
    have eq: "P (Red X) ! J = Red (?Q ! J)" using PR JL' by simp
    have "Red (Red (?Q ! J)) = Red (?Q ! J)"
      using idem_nonmulti[of "?Q ! J"] comp[OF JL'] by simp
    thus "P (Red X) ! J \<in> RT_PS"
      using eq y3r_Red_TPS comp[OF JL'] by (simp add: RT_PS_def)
  qed
  thus ?thesis using m_6_6_P_reduced[OF RXT] by blast
qed

end

theory Frontier_6_051
  imports Support_6_033
begin

subsection \<open>§6.5 engine: \<open>Red (IncrFirst M) = Red M\<close> — bankable branch lemmas\<close>

text \<open>m: the \<open>zeroT\<close> branch.  \<open>IncrFirst\<close> preserves \<open>zeroT\<close> (row 1 is unchanged),
  so both sides unfold to \<open>[(0,0)]\<close>.\<close>

lemma eng_Red_IncrFirst_zeroT:
  assumes MT: "M \<in> T_PS" and z: "zeroT M"
  shows "Red (IncrFirst M) = Red M"
proof -
  have IT: "IncrFirst M \<in> T_PS" using MT by (simp add: T_PS_def IncrFirst_def)
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have domI: "Red_dom (IncrFirst M)" by (rule m_6_5_Red_welldef[OF IT])
  have zI: "zeroT (IncrFirst M)" using z by (simp add: IncrFirst_zeroT_eq)
  have "Red (IncrFirst M) = [(0,0)]" using Red.psimps[OF domI] zI by simp
  moreover have "Red M = [(0,0)]" using Red.psimps[OF domM] z by simp
  ultimately show ?thesis by simp
qed

text \<open>m: the core branch (\<open>monoT\<close>, \<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close>).  \<open>IncrFirst M\<close> is then
  \<open>monoT\<close> with \<open>m\<^sub>0\<^sub>0 = 1, m\<^sub>1\<^sub>0 = 0\<close>, so it takes the shift branch (case 4); the
  shift subtracts \<open>1\<close> from row 0, which exactly cancels the \<open>IncrFirst\<close> bump and
  recovers \<open>M\<close>.  Hence \<open>Red (IncrFirst M) = Red M\<close> directly (no induction).\<close>

lemma eng_Red_IncrFirst_core:
  assumes MT: "M \<in> T_PS" and nz: "\<not> zeroT M" and nmu: "\<not> multiT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
  shows "Red (IncrFirst M) = Red M"
proof -
  let ?I = "IncrFirst M"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have IT: "?I \<in> T_PS" using MT by (simp add: T_PS_def IncrFirst_def)
  have domI: "Red_dom ?I" by (rule m_6_5_Red_welldef[OF IT])
  have Inz: "\<not> zeroT ?I" using nz by (simp add: IncrFirst_zeroT_eq)
  have Inmu: "\<not> multiT ?I" using nmu by (simp add: IncrFirst_multiT_eq)
  \<comment> \<open>row-0 head becomes 1, row-1 head stays 0.\<close>
  have Ic0: "entry ?I 0 0 = Suc 0" using c0 entry_IncrFirst[OF LMpos, of 0] by simp
  have Ic1: "entry ?I 1 0 = 0" using c1 entry_IncrFirst[OF LMpos, of 1] by simp
  have Inc: "\<not> (entry ?I 0 0 = 0 \<and> entry ?I 1 0 = 0)" using Ic0 by simp
  \<comment> \<open>the shift branch: subtract \<open>entry ?I 0 0 = 1\<close>.\<close>
  let ?j1 = "Lng ?I - 1"
  have rI: "Red ?I = Red (map (\<lambda>j. (entry ?I 0 j - entry ?I 0 0, entry ?I 1 j))
                                [0..<Suc ?j1])"
    using Red.psimps[OF domI] Inz Inmu Inc Ic1 by (simp add: Let_def)
  \<comment> \<open>that map equals \<open>M\<close>.\<close>
  have shifteq: "map (\<lambda>j. (entry ?I 0 j - entry ?I 0 0, entry ?I 1 j)) [0..<Suc ?j1] = M"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>j. (entry ?I 0 j - entry ?I 0 0, entry ?I 1 j)) [0..<Suc ?j1])
        = length M" using LMpos by simp
  next
    fix p assume p: "p < length (map (\<lambda>j. (entry ?I 0 j - entry ?I 0 0, entry ?I 1 j))
                                       [0..<Suc ?j1])"
    have plen: "p < length [0..<Suc ?j1]" using p by simp
    have pl: "p < Lng M" using p LMpos by simp
    have idx: "[0..<Suc ?j1] ! p = p" using pl by (simp add: nth_upt del: upt_Suc)
    have e0: "entry ?I 0 p = Suc (entry M 0 p)" using entry_IncrFirst[OF pl, of 0] by simp
    have e1: "entry ?I 1 p = entry M 1 p" using entry_IncrFirst[OF pl, of 1] by simp
    have "map (\<lambda>j. (entry ?I 0 j - entry ?I 0 0, entry ?I 1 j)) [0..<Suc ?j1] ! p
           = (entry ?I 0 p - entry ?I 0 0, entry ?I 1 p)"
      using nth_map[OF plen] idx by simp
    also have "\<dots> = (entry M 0 p, entry M 1 p)" using e0 e1 Ic0 by simp
    also have "\<dots> = M ! p" using pl by (simp add: entry_def)
    finally show "map (\<lambda>j. (entry ?I 0 j - entry ?I 0 0, entry ?I 1 j)) [0..<Suc ?j1] ! p
                = M ! p" .
  qed
  show ?thesis using rI by (simp only: shifteq)
qed

text \<open>m: the shift branch (\<open>monoT\<close>, \<open>m\<^sub>1\<^sub>0 = 0, m\<^sub>0\<^sub>0 > 0\<close>).  Both \<open>M\<close> and
  \<open>IncrFirst M\<close> take the shift branch; the shift subtracts \<open>m\<^sub>0\<^sub>0\<close> resp.
  \<open>m\<^sub>0\<^sub>0 + 1\<close>, landing on the SAME core sequence, so \<open>Red\<close> agrees (no induction).\<close>

lemma eng_Red_IncrFirst_shift:
  assumes MT: "M \<in> T_PS" and nz: "\<not> zeroT M" and nmu: "\<not> multiT M"
    and nc: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" and c1: "entry M 1 0 = 0"
  shows "Red (IncrFirst M) = Red M"
proof -
  let ?I = "IncrFirst M"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have IT: "?I \<in> T_PS" using MT by (simp add: T_PS_def IncrFirst_def)
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have domI: "Red_dom ?I" by (rule m_6_5_Red_welldef[OF IT])
  have c0p: "0 < entry M 0 0" using nc c1 by simp
  \<comment> \<open>shift output of \<open>M\<close>.\<close>
  let ?j1 = "Lng M - 1"
  have rM: "Red M = Red (map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j))
                              [0..<Suc ?j1])"
    using Red.psimps[OF domM] nz nmu nc c1 by (simp add: Let_def)
  \<comment> \<open>\<open>IncrFirst M\<close>: still mono, row-1 head 0, row-0 head \<open>m\<^sub>0\<^sub>0 + 1 > 0\<close>.\<close>
  have Inz: "\<not> zeroT ?I" using nz by (simp add: IncrFirst_zeroT_eq)
  have Inmu: "\<not> multiT ?I" using nmu by (simp add: IncrFirst_multiT_eq)
  have Ic1: "entry ?I 1 0 = 0" using c1 entry_IncrFirst[OF LMpos, of 1] by simp
  have Ic0: "entry ?I 0 0 = Suc (entry M 0 0)" using entry_IncrFirst[OF LMpos, of 0] by simp
  have Inc: "\<not> (entry ?I 0 0 = 0 \<and> entry ?I 1 0 = 0)" using Ic0 by simp
  have LI: "Lng ?I = Lng M" by simp
  have rI: "Red ?I = Red (map (\<lambda>j. (entry ?I 0 j - entry ?I 0 0, entry ?I 1 j))
                               [0..<Suc ?j1])"
    using Red.psimps[OF domI] Inz Inmu Inc Ic1 LI by (simp add: Let_def)
  \<comment> \<open>both shift maps coincide.\<close>
  have mapeq: "map (\<lambda>j. (entry ?I 0 j - entry ?I 0 0, entry ?I 1 j)) [0..<Suc ?j1]
             = map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Suc ?j1]"
  proof (rule map_cong[OF refl])
    fix p assume "p \<in> set [0..<Suc ?j1]"
    hence pl: "p < Lng M" using LMpos by auto
    have e0: "entry ?I 0 p = Suc (entry M 0 p)" using entry_IncrFirst[OF pl, of 0] by simp
    have e1: "entry ?I 1 p = entry M 1 p" using entry_IncrFirst[OF pl, of 1] by simp
    show "(entry ?I 0 p - entry ?I 0 0, entry ?I 1 p)
        = (entry M 0 p - entry M 0 0, entry M 1 p)"
      using e0 e1 Ic0 by simp
  qed
  show ?thesis using rI rM by (simp only: mapeq)
qed

text \<open>m: the multi branch, as a REDUCTION.  When \<open>M\<close> is multi, \<open>Red M\<close> is the
  concatenation of the block reductions, and \<open>P (IncrFirst M) = map IncrFirst (P M)\<close>
  (@{thm [source] m_6_2_P_IncrFirst}).  Hence if the goal holds on every block of
  \<open>P M\<close> it holds on \<open>M\<close>.  (Bankable: the multi branch of the @{const Red}-induction
  closes once the per-block instances are available.)\<close>

lemma eng_Red_IncrFirst_multi_reduce:
  assumes MT: "M \<in> T_PS" and mu: "multiT M"
    and blocks: "\<And>y. y \<in> set (P M) \<Longrightarrow> Red (IncrFirst y) = Red y"
  shows "Red (IncrFirst M) = Red M"
proof -
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have IT: "IncrFirst M \<in> T_PS" using MT by (simp add: T_PS_def IncrFirst_def)
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have domI: "Red_dom (IncrFirst M)" by (rule m_6_5_Red_welldef[OF IT])
  have nzM: "\<not> zeroT M" using mu by (simp add: multiT_def)
  have muI: "multiT (IncrFirst M)" using mu by (simp add: IncrFirst_multiT_eq)
  have nzI: "\<not> zeroT (IncrFirst M)" using muI by (simp add: multiT_def)
  have rM: "Red M = concat (map Red (P M))"
    using Red.psimps[OF domM] nzM mu by simp
  have rI: "Red (IncrFirst M) = concat (map Red (P (IncrFirst M)))"
    using Red.psimps[OF domI] nzI muI by simp
  have PI: "P (IncrFirst M) = map IncrFirst (P M)" by (rule m_6_2_P_IncrFirst)
  have "Red (IncrFirst M) = concat (map Red (map IncrFirst (P M)))"
    using rI PI by simp
  also have "\<dots> = concat (map (\<lambda>y. Red (IncrFirst y)) (P M))"
    by (simp add: comp_def)
  also have "\<dots> = concat (map Red (P M))"
    by (rule arg_cong[where f=concat], rule map_cong[OF refl]) (simp add: blocks)
  also have "\<dots> = Red M" using rM by simp
  finally show ?thesis .
qed

text \<open>m: the \<open>m\<^sub>1\<^sub>0 > 0\<close> branch, as a REDUCTION onto the single \<open>coreReduce\<close>
  obligation \<open>(B2)\<close>.  For a \<open>monoT\<close> \<open>M\<close> with \<open>m\<^sub>1\<^sub>0 = entry M 1 0 > 0\<close>, both
  \<open>Red M\<close> and \<open>Red (IncrFirst M)\<close> are read off, via the SAME output map, from
  \<open>N = Red (coreReduce M)\<close> resp. \<open>N' = Red (coreReduce (IncrFirst M))\<close>; the
  productive (then) branch is taken on both sides (by @{thm [source]
  m_6_5_monoT_Red_m10pos} and @{thm [source] m_6_5_Lng_Red}).  Hence \<open>N' = N\<close>
  — i.e. the single fact (B2) \<open>Red (coreReduce (IncrFirst M)) = Red (coreReduce M)\<close>
  — suffices to conclude \<open>Red (IncrFirst M) = Red M\<close>.

  (B2) is the residual cut-anchored \<open>Red_IncrFirst\<close> engine instance; \<open>coreReduce M\<close>
  and \<open>coreReduce (IncrFirst M)\<close> share the length-\<open>m\<^sub>1\<^sub>0\<close> diagonal prefix and
  differ only by one extra @{const IncrFirst} on the tail past the prefix (the
  @{const tail_bump} / @{thm [source] njA_Br_eq} cut).\<close>

lemma eng_Red_IncrFirst_m10pos_reduce:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
    and B2: "Red (coreReduce (IncrFirst M)) = Red (coreReduce M)"
  shows "Red (IncrFirst M) = Red M"
proof -
  let ?m10 = "entry M 1 0"
  let ?I = "IncrFirst M"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have IT: "?I \<in> T_PS" using MT by (simp add: T_PS_def IncrFirst_def)
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have domI: "Red_dom ?I" by (rule m_6_5_Red_welldef[OF IT])
  have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  \<comment> \<open>structural data shared by \<open>M\<close> and \<open>IncrFirst M\<close>.\<close>
  have nzM: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmuM: "\<not> multiT M" using mono by (simp add: multiT_def)
  have ncM: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" using pos by simp
  have monoI: "monoT ?I" using mono by (simp add: IncrFirst_monoT_eq)
  have posI: "0 < entry ?I 1 0" using pos entry_IncrFirst[OF LMpos, of 1] by simp
  have nzI: "\<not> zeroT ?I" using monoI by (simp add: monoT_def)
  have nmuI: "\<not> multiT ?I" using monoI by (simp add: multiT_def)
  have m10I: "entry ?I 1 0 = ?m10" using entry_IncrFirst[OF LMpos, of 1] by simp
  have ncI: "\<not> (entry ?I 0 0 = 0 \<and> entry ?I 1 0 = 0)" using posI by simp
  \<comment> \<open>the \<open>m\<^sub>1\<^sub>0 > 0\<close> recursion argument is \<open>coreReduce\<close>.\<close>
  let ?argM = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
  let ?argI = "diagSeq 0 (entry ?I 1 0 - 1) @ (IncrFirst ^^ (entry ?I 1 0)) ?I"
  have argM_cr: "?argM = coreReduce M" using pos by (simp add: coreReduce_def)
  have argI_cr: "?argI = coreReduce ?I" using posI by (simp add: coreReduce_def)
  let ?N  = "Red ?argM"
  let ?N' = "Red ?argI"
  \<comment> \<open>(B2): the two recursive \<open>Red\<close>s agree.\<close>
  have NN: "?N' = ?N"
    using B2 argM_cr argI_cr by simp
  \<comment> \<open>geometry: both args are in \<open>T_PS\<close>; \<open>Lng N = m10 + Lng M\<close>.\<close>
  have funM_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
    using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
  have argM_T: "?argM \<in> T_PS" using funM_ne by (simp add: T_PS_def)
  have LN: "Lng ?N = ?m10 + Lng M"
    using m_6_5_monoT_Red_fact1_Lng[OF MT pos] by simp
  have jN_ge: "?m10 \<le> Lng ?N - 1" using LN LMpos by linarith
  have segN_PT: "seg ?N ?m10 (Lng ?N - 1) \<in> PT_PS"
    using m_6_5_monoT_Red_m10pos[OF M_PT pos] by simp
  have thenM: "?m10 \<le> Lng ?N - 1 \<and> seg ?N ?m10 (Lng ?N - 1) \<in> PT_PS"
    using jN_ge segN_PT by simp
  \<comment> \<open>unfold \<open>Red M\<close> on the productive branch.\<close>
  have rM: "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                              entry ?N 1 j))
                        [?m10..<Suc (Lng ?N - 1)]"
    using Red.psimps[OF domM] nzM nmuM ncM pos thenM by (simp add: Let_def)
  \<comment> \<open>unfold \<open>Red (IncrFirst M)\<close>: same shape, with \<open>N'\<close>, \<open>m10 (IncrFirst M) = m10\<close>.\<close>
  have thenI: "entry ?I 1 0 \<le> Lng ?N' - 1 \<and> seg ?N' (entry ?I 1 0) (Lng ?N' - 1) \<in> PT_PS"
    using thenM NN m10I by simp
  have rI: "Red ?I = map (\<lambda>j. (entry ?N' 0 j - entry ?N' 0 (entry ?I 1 0)
                                + entry ?N' 1 (entry ?I 1 0), entry ?N' 1 j))
                          [entry ?I 1 0..<Suc (Lng ?N' - 1)]"
    using Red.psimps[OF domI] nzI nmuI ncI posI thenI by (simp add: Let_def)
  show ?thesis using rI rM NN m10I by simp
qed

text \<open>m: assembled \<open>Red (IncrFirst M) = Red M\<close>, MODULO the single cut-anchored
  obligation \<open>(B2)\<close>.  By @{thm [source] Red.pinduct} on \<open>M\<close>, all branches close
  from the green branch bricks above except the \<open>monoT, m\<^sub>1\<^sub>0 > 0\<close> one, which
  @{thm [source] eng_Red_IncrFirst_m10pos_reduce} reduces to \<open>(B2)\<close>
  \<open>Red (coreReduce (IncrFirst X)) = Red (coreReduce X)\<close>.  The latter is the
  residual cut-anchored \<open>Red_IncrFirst\<close> engine instance (\<open>coreReduce X\<close> and
  \<open>coreReduce (IncrFirst X)\<close> share a length-\<open>m\<^sub>1\<^sub>0\<close> diagonal prefix and differ by
  one @{const IncrFirst} on the tail past it; the @{const tail_bump} / @{thm
  [source] njA_Br_eq} family is the cut machinery for it).  Discharging \<open>(B2)\<close>
  for every \<open>monoT\<close> \<open>X\<close> with \<open>entry X 1 0 > 0\<close> yields the §6.5 \<open>Red\<close>/\<open>IncrFirst\<close>
  invariance (the article proposition \<open>p_6_5_Red_IncrFirst\<close>).\<close>

lemma eng_Red_IncrFirst_modB2:
  assumes B2: "\<And>X. X \<in> T_PS \<Longrightarrow> monoT X \<Longrightarrow> 0 < entry X 1 0 \<Longrightarrow>
                  Red (coreReduce (IncrFirst X)) = Red (coreReduce X)"
  assumes MT: "M \<in> T_PS"
  shows "Red (IncrFirst M) = Red M"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have "M \<in> T_PS \<longrightarrow> Red (IncrFirst M) = Red M"
    using domM
  proof (induction M rule: Red.pinduct)
    case (1 M)
    note dom    = 1(1)
    note IH_mu  = 1(2)
    show ?case
    proof (rule impI)
      assume MT': "M \<in> T_PS"
      show "Red (IncrFirst M) = Red M"
      proof (cases "zeroT M")
        case True
        thus ?thesis by (rule eng_Red_IncrFirst_zeroT[OF MT'])
      next
        case nz: False
        show ?thesis
        proof (cases "multiT M")
          case mu: True
          \<comment> \<open>per-block IH from the multiT branch of the recursion.\<close>
          have blocks: "\<And>y. y \<in> set (P M) \<Longrightarrow> Red (IncrFirst y) = Red y"
          proof -
            fix y assume y: "y \<in> set (P M)"
            have Mne: "M \<noteq> []" using MT' by (simp add: T_PS_def)
            have yT: "y \<in> T_PS"
              using P_blocks_nonempty[OF Mne] y by (auto simp: T_PS_def)
            have ih: "y \<in> T_PS \<longrightarrow> Red (IncrFirst y) = Red y"
              by (rule IH_mu[OF nz mu y])
            thus "Red (IncrFirst y) = Red y" using yT by blast
          qed
          show ?thesis by (rule eng_Red_IncrFirst_multi_reduce[OF MT' mu blocks])
        next
          case nmu: False
          have mono: "monoT M" using nz nmu by (simp add: multiT_def)
          show ?thesis
          proof (cases "entry M 0 0 = 0 \<and> entry M 1 0 = 0")
            case core: True
            hence c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0" by simp_all
            show ?thesis by (rule eng_Red_IncrFirst_core[OF MT' nz nmu c0 c1])
          next
            case nc: False
            show ?thesis
            proof (cases "entry M 1 0 = 0")
              case c1z: True
              show ?thesis by (rule eng_Red_IncrFirst_shift[OF MT' nz nmu nc c1z])
            next
              case c1p: False
              hence pos: "0 < entry M 1 0" by simp
              have b2: "Red (coreReduce (IncrFirst M)) = Red (coreReduce M)"
                by (rule B2[OF MT' mono pos])
              show ?thesis
                by (rule eng_Red_IncrFirst_m10pos_reduce[OF MT' mono pos b2])
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using MT by blast
qed


subsection \<open>The cut-anchored \<open>Red_IncrFirst\<close> engine (B2 deliverable)\<close>

text \<open>\<open>bumpAt M n\<close>: bump every row-0 value at or above the cut \<open>n\<close> by one (an
  order isomorphism on row 0), leaving row 1 alone.  This is the abstract suffix
  bump underlying both the top-level @{const coreReduce} cut and the recursive
  branch cuts (uniform on @{const IncrFirst} suffixes).\<close>

definition bumpAt :: "pairseq \<Rightarrow> nat \<Rightarrow> pairseq" where
  "bumpAt M n = map (\<lambda>p. (bumpv n (fst p), snd p)) M"

lemma Lng_bumpAt[simp]: "Lng (bumpAt M n) = Lng M"
  by (simp add: bumpAt_def)

lemma entry_bumpAt0:
  "j < Lng M \<Longrightarrow> entry (bumpAt M n) 0 j = bumpv n (entry M 0 j)"
  by (simp add: bumpAt_def entry_def)

lemma entry_bumpAt1:
  "j < Lng M \<Longrightarrow> entry (bumpAt M n) 1 j = entry M 1 j"
  by (simp add: bumpAt_def entry_def)

text \<open>For any cut \<open>n\<close>, \<open>(bumpAt X n, X)\<close> satisfies the @{locale tail_bump}
  hypotheses — all structural data (\<open>Lng\<close>, \<open>nextR\<close>, \<open>le0\<close>, \<open>le1\<close>, \<open>leR\<close>,
  \<open>TrMax\<close>, \<open>zeroT\<close>, \<open>monoT\<close>, \<open>multiT\<close>, \<open>Pcut\<close>) is shared.\<close>

lemma tail_bump_bumpAt: "tail_bump (bumpAt X n) X n"
proof
  show "Lng (bumpAt X n) = Lng X" by simp
next
  fix j assume "j < Lng X" thus "entry (bumpAt X n) 0 j = bumpv n (entry X 0 j)"
    by (rule entry_bumpAt0)
next
  fix j assume "j < Lng X" thus "entry (bumpAt X n) 1 j = entry X 1 j"
    by (rule entry_bumpAt1)
qed

text \<open>The cut-anchored relation locale: \<open>tail_bump\<close> plus the \<open>tail_low\<close> condition
  that, past the trunk right-end \<open>TrMax X\<close>, every row-0 value is at least the cut
  \<open>n\<close>.  Under \<open>tail_low\<close> the suffix bump acts as a uniform @{const IncrFirst} on the
  branch region, which is what lets @{const Red} collapse.  (\<open>tail_low\<close> is preserved
  by all three recursive descents — branch \<open>N\<^sub>J\<close>, shift, \<open>m\<^sub>1\<^sub>0>0\<close> — empirically
  3034/0; the relation itself is a valid \<open>Red\<close>-collapse condition 8480/0.)\<close>

locale cut_bump = tail_bump +
  assumes tail_low: "\<And>j. TrMax X < j \<Longrightarrow> j < Lng X \<Longrightarrow> n \<le> entry X 0 j"
begin

text \<open>On the branch region (indices \<open>> TrMax X\<close>) the bump is a uniform +1, so a
  segment of \<open>A\<close> there is the @{const IncrFirst}-image of the same segment of \<open>X\<close>.\<close>

lemma cb_branch_entry0:
  assumes a: "TrMax X < j" and b: "j < Lng X"
  shows "entry A 0 j = Suc (entry X 0 j)"
proof -
  have "entry A 0 j = bumpv n (entry X 0 j)" using row0_bump[OF b] .
  also have "\<dots> = Suc (entry X 0 j)"
    using tail_low[OF a b] by (simp add: bumpv_def)
  finally show ?thesis .
qed

lemma cb_seg_IncrFirst:
  assumes a: "TrMax X < aa" and b: "bb < Lng X"
  shows "seg A aa bb = IncrFirst (seg X aa bb)"
proof (rule nth_equalityI)
  show "length (seg A aa bb) = length (IncrFirst (seg X aa bb))"
    by (simp add: seg_def IncrFirst_def len_eq)
next
  fix p assume p: "p < length (seg A aa bb)"
  have pb: "p < Suc bb - aa" using p by (simp add: seg_def len_eq del: upt_Suc)
  let ?j = "aa + p"
  have idx: "[aa..<Suc bb] ! p = ?j" using pb by (simp add: nth_upt del: upt_Suc)
  have jge: "TrMax X < ?j" using a by simp
  have jb: "?j \<le> bb" using pb by simp
  have jlt: "?j < Lng X" using jb b by simp
  have lhs: "seg A aa bb ! p = A ! ?j"
    using pb idx by (simp add: seg_def len_eq del: upt_Suc)
  have rhs0: "seg X aa bb ! p = X ! ?j"
    using pb idx by (simp add: seg_def del: upt_Suc)
  have e0: "entry A 0 ?j = Suc (entry X 0 ?j)" by (rule cb_branch_entry0[OF jge jlt])
  have e1: "entry A 1 ?j = entry X 1 ?j" using row1_eq[OF jlt] .
  have jA: "?j < Lng A" using jlt len_eq by simp
  have Ap: "A ! ?j = (Suc (fst (X ! ?j)), snd (X ! ?j))"
  proof -
    have "fst (A ! ?j) = Suc (fst (X ! ?j))" using e0 by (simp add: entry_def)
    moreover have "snd (A ! ?j) = snd (X ! ?j)" using e1 by (simp add: entry_def)
    ultimately show ?thesis by (cases "A ! ?j") simp
  qed
  have inc: "IncrFirst (seg X aa bb) ! p
              = (Suc (fst (seg X aa bb ! p)), snd (seg X aa bb ! p))"
    using p by (simp add: IncrFirst_def seg_def len_eq)
  show "seg A aa bb ! p = IncrFirst (seg X aa bb) ! p"
    using lhs rhs0 Ap inc by (simp add: seg_def del: upt_Suc)
qed

text \<open>The branches of \<open>A\<close> are the @{const IncrFirst}-images of the branches of
  \<open>X\<close> (same shape, +1 on the tail).\<close>

lemma cb_Br_eq: "Br A = map IncrFirst (Br X)"
proof -
  have trEq: "TrMax A = TrMax X" by (rule TrMax_eq)
  show ?thesis
  proof (cases "TrMax X = Lng X - 1")
    case True
    hence "Br A = []" "Br X = []" using trEq len_eq by (simp_all add: Br_def)
    thus ?thesis by simp
  next
    case False
    have Lpos: "0 < Lng X"
    proof (rule ccontr)
      assume "\<not> 0 < Lng X"
      hence L0: "Lng X = 0" by simp
      have "{j. \<forall>j'<j. nextR X 1 j' (j' + 1)} = {0}"
      proof
        show "{j. \<forall>j'<j. nextR X 1 j' (j' + 1)} \<subseteq> {0}"
        proof
          fix j assume "j \<in> {j. \<forall>j'<j. nextR X 1 j' (j' + 1)}"
          hence H: "\<forall>j'<j. nextR X 1 j' (j' + 1)" by simp
          show "j \<in> {0}"
          proof (rule ccontr)
            assume "j \<notin> {0}"
            hence "0 < j" by simp
            from H this have "nextR X 1 0 (0 + 1)" by blast
            thus False using L0 by (simp add: nextR_def nextrel1_def)
          qed
        qed
      next
        show "{0} \<subseteq> {j. \<forall>j'<j. nextR X 1 j' (j' + 1)}" by auto
      qed
      hence "TrMax X = 0" by (simp add: TrMax_def)
      thus False using False L0 by simp
    qed
    have bb: "Lng X - 1 < Lng X" using Lpos by simp
    have aa: "TrMax X < TrMax X + 1" by simp
    have segEq: "seg A (TrMax X + 1) (Lng X - 1)
               = IncrFirst (seg X (TrMax X + 1) (Lng X - 1))"
      by (rule cb_seg_IncrFirst[OF aa bb])
    have "Br A = P (seg A (TrMax A + 1) (Lng A - 1))"
      using False trEq len_eq by (simp add: Br_def)
    also have "\<dots> = P (seg A (TrMax X + 1) (Lng X - 1))" using trEq len_eq by simp
    also have "\<dots> = P (IncrFirst (seg X (TrMax X + 1) (Lng X - 1)))" using segEq by simp
    also have "\<dots> = map IncrFirst (P (seg X (TrMax X + 1) (Lng X - 1)))"
      by (rule m_6_2_P_IncrFirst)
    also have "\<dots> = map IncrFirst (Br X)" using False by (simp add: Br_def)
    finally show ?thesis .
  qed
qed

lemma cb_length_Br_eq: "length (Br A) = length (Br X)"
  by (simp add: cb_Br_eq)

lemma cb_FirstNodes_eq: "FirstNodes A = FirstNodes X"
proof -
  have "IdxSum (Br A) = IdxSum (Br X)"
    by (simp add: cb_Br_eq IdxSum_map_IncrFirst)
  thus ?thesis by (simp add: FirstNodes_def TrMax_eq)
qed

lemma cb_Joints_eq: "Joints A = Joints X"
  by (simp add: Joints_def nextR_eq cb_FirstNodes_eq cb_length_Br_eq)

lemma cb_npJ_eq:
  assumes J: "J < length (Br X)"
  shows "npJ A J = npJ X J"
proof -
  have br: "Br A = map IncrFirst (Br X)" by (rule cb_Br_eq)
  have brJ: "Br A ! J = IncrFirst (Br X ! J)" using J br by simp
  have e1: "entry (Br A ! J) 1 0 = entry (Br X ! J) 1 0"
  proof (cases "Lng (Br X ! J) = 0")
    case True
    hence "Br X ! J = []" by simp
    thus ?thesis using brJ by (simp add: IncrFirst_def)
  next
    case False
    hence L0: "0 < Lng (Br X ! J)" by simp
    show ?thesis using entry_IncrFirst[OF L0, of 1] by (simp add: brJ)
  qed
  have theEq: "(THE j. nextR A 1 j (FirstNodes A ! J))
             = (THE j. nextR X 1 j (FirstNodes X ! J))"
    by (simp add: nextR_eq cb_FirstNodes_eq)
  show ?thesis unfolding npJ_def by (simp only: e1 theEq)
qed

text \<open>The branch recursion argument \<open>N\<^sub>J\<close> of \<open>A\<close> is the \<open>bumpAt\<close>-image of that of
  \<open>X\<close>, at the fresh cut \<open>Joints!J + 2\<close>: the head node \<open>(Joints!J+1, np)\<close> is fixed
  (its row-0 value \<open>Joints!J+1\<close> is below the new cut), and the rest of the branch
  is bumped uniformly.  Here \<open>n \<ge> 1\<close> and \<open>X\<close> core (\<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close>), so the
  head row-0/row-1 of \<open>A\<close> match \<open>X\<close>.\<close>

lemma cb_NJ_bumpAt:
  assumes XP: "X \<in> PT_PS" and n1: "1 \<le> n" and c0: "entry X 0 0 = 0" and c1: "entry X 1 0 = 0"
    and J: "J < length (Br X)"
  shows "NJ A J = bumpAt (NJ X J) (Joints X ! J + 2)"
proof -
  let ?np = "Joints X ! J + 2"
  have XT: "X \<in> T_PS" using XP by (simp add: PT_PS_def)
  have Lpos: "0 < Lng X" using XT by (cases X) (auto simp: T_PS_def)
  have JBr: "J < Lng (Br X)" using J by simp
  \<comment> \<open>tail-cleanness of the branch: past the head, row-0 \<ge> \<open>Joints!J + 2\<close>.\<close>
  have cb_NJ_tail_ge: "\<And>p. p < Lng (Br X ! J) \<Longrightarrow> 0 < p \<Longrightarrow> ?np \<le> fst (Br X ! J ! p)"
  proof -
    fix p assume pBrX: "p < Lng (Br X ! J)" and pq: "0 < p"
    have brJne: "Br X ! J \<noteq> []" by (rule Br_component_nonempty[OF XP JBr])
    have brJTPS: "Br X ! J \<in> T_PS" using brJne by (simp add: T_PS_def)
    have mo: "monoT (Br X ! J)"
    proof -
      have "zeroT (Br X ! J) \<or> monoT (Br X ! J)" by (rule Br_component_nonmulti[OF XP JBr])
      moreover have "\<not> zeroT (Br X ! J)"
        using pBrX pq by (auto simp: zeroT_def)
      ultimately show ?thesis by blast
    qed
    have K: "Joints X ! J + 1 \<le> entry (Br X ! J) 0 0"
      using joints_lt_branch_first[OF XP JBr] c0 by simp
    have mn: "entry (Br X ! J) 0 0 < entry (Br X ! J) 0 p"
      by (rule monoT_row0_min[OF brJTPS mo pq pBrX])
    have "?np \<le> entry (Br X ! J) 0 p" using K mn by simp
    thus "?np \<le> fst (Br X ! J ! p)" by (simp add: entry_def)
  qed
  \<comment> \<open>head of A matches X (core, n\<ge>1): bumpv leaves 0 fixed.\<close>
  have A00: "entry A 0 0 = 0" using row0_bump[OF Lpos] c0 n1 by (simp add: bumpv_def)
  have A10: "entry A 1 0 = 0" using row1_eq[OF Lpos] c1 by simp
  have jt: "Joints A = Joints X" by (rule cb_Joints_eq)
  have np: "npJ A J = npJ X J" by (rule cb_npJ_eq[OF J])
  have br: "Br A ! J = IncrFirst (Br X ! J)" using J cb_Br_eq by simp
  \<comment> \<open>head node value.\<close>
  let ?hv = "Joints X ! J + 1"
  have brXne: "Br X ! J \<noteq> []" by (rule Br_component_nonempty[OF XP JBr])
  have brAne: "Br A ! J \<noteq> []" using br brXne by (simp add: IncrFirst_def)
  have lA: "Lng (NJ A J) = Lng (Br A ! J)" using brAne by (rule Lng_NJ)
  have lX: "Lng (NJ X J) = Lng (Br X ! J)" using brXne by (rule Lng_NJ)
  show ?thesis
  proof (rule nth_equalityI)
    show "length (NJ A J) = length (bumpAt (NJ X J) ?np)"
      using lA lX br by (simp add: IncrFirst_def)
  next
    fix p assume p: "p < length (NJ A J)"
    show "NJ A J ! p = bumpAt (NJ X J) ?np ! p"
    proof (cases p)
      case 0
      have hA: "NJ A J ! 0 = (entry A 0 0 + Joints A ! J + 1, entry A 1 0 + npJ A J)"
        by (simp add: NJ_def)
      have hX: "NJ X J ! 0 = (entry X 0 0 + Joints X ! J + 1, entry X 1 0 + npJ X J)"
        by (simp add: NJ_def)
      have bv: "bumpv ?np (fst (NJ X J ! 0)) = fst (NJ X J ! 0)"
        using hX c0 by (simp add: bumpv_def)
      have njXpos: "0 < length (NJ X J)" by (simp add: NJ_def)
      have "bumpAt (NJ X J) ?np ! 0
              = (\<lambda>pp. (bumpv ?np (fst pp), snd pp)) (NJ X J ! 0)"
        unfolding bumpAt_def by (rule nth_map[OF njXpos])
      hence "bumpAt (NJ X J) ?np ! 0 = (bumpv ?np (fst (NJ X J ! 0)), snd (NJ X J ! 0))"
        by simp
      also have "\<dots> = NJ X J ! 0" using bv by (cases "NJ X J ! 0") simp
      also have "\<dots> = NJ A J ! 0" using hA hX A00 A10 jt np c0 c1 by simp
      finally have "bumpAt (NJ X J) ?np ! 0 = NJ A J ! 0" .
      thus ?thesis using 0 by simp
    next
      case (Suc q)
      have pBr: "p < Lng (Br A ! J)" using p Lng_NJ[OF brAne] by simp
      have pBrX: "p < Lng (Br X ! J)" using pBr br by (simp add: IncrFirst_def)
      have pq: "0 < p" using Suc by simp
      \<comment> \<open>tail entry: NJ reads Br at p; A side is IncrFirst (+1) of X side.\<close>
      have tlA: "p - 1 < length (tl (Br A ! J))" using pBr pq by simp
      have tlX: "p - 1 < length (tl (Br X ! J))" using pBrX pq by simp
      have tA: "NJ A J ! p = Br A ! J ! p"
      proof -
        have "NJ A J ! p = tl (Br A ! J) ! (p - 1)"
          unfolding NJ_def using pq by (cases p) auto
        also have "\<dots> = Br A ! J ! Suc (p - 1)" using nth_tl[OF tlA] .
        also have "\<dots> = Br A ! J ! p" using pq by simp
        finally show ?thesis .
      qed
      have tX: "NJ X J ! p = Br X ! J ! p"
      proof -
        have "NJ X J ! p = tl (Br X ! J) ! (p - 1)"
          unfolding NJ_def using pq by (cases p) auto
        also have "\<dots> = Br X ! J ! Suc (p - 1)" using nth_tl[OF tlX] .
        also have "\<dots> = Br X ! J ! p" using pq by simp
        finally show ?thesis .
      qed
      have brp: "Br A ! J ! p = (Suc (fst (Br X ! J ! p)), snd (Br X ! J ! p))"
        using br pBrX by (simp add: IncrFirst_def)
      \<comment> \<open>the bump at \<open>?np\<close> is a +1 on this tail position (row-0 value \<ge> ?np).\<close>
      have ge: "?np \<le> fst (Br X ! J ! p)"
        by (rule cb_NJ_tail_ge[OF pBrX pq])
      have pNJX: "p < length (NJ X J)" using pBrX lX by simp
      have "bumpAt (NJ X J) ?np ! p
              = (\<lambda>pp. (bumpv ?np (fst pp), snd pp)) (NJ X J ! p)"
        unfolding bumpAt_def by (rule nth_map[OF pNJX])
      hence "bumpAt (NJ X J) ?np ! p = (bumpv ?np (fst (NJ X J ! p)), snd (NJ X J ! p))"
        by simp
      also have "\<dots> = (Suc (fst (Br X ! J ! p)), snd (Br X ! J ! p))"
        using tX ge by (simp add: bumpv_def)
      also have "\<dots> = NJ A J ! p" using tA brp by simp
      finally show ?thesis by (rule sym)
    qed
  qed
qed

end


text \<open>@{const bumpAt} is a per-component map, so it commutes with \<open>take\<close>/\<open>drop\<close>
  and (preserving \<open>multiT\<close>/\<open>Pcut\<close>) with the block decomposition \<open>P\<close>.\<close>

lemma bumpAt_take: "bumpAt (take k M) n = take k (bumpAt M n)"
  by (simp add: bumpAt_def take_map)

lemma bumpAt_drop: "bumpAt (drop k M) n = drop k (bumpAt M n)"
  by (simp add: bumpAt_def drop_map)

lemma bumpAt_multiT_eq: "multiT (bumpAt M n) = multiT M"
  by (rule tail_bump.multiT_eq[OF tail_bump_bumpAt])

lemma bumpAt_Pcut_eq: "Pcut (bumpAt M n) = Pcut M"
  by (rule tail_bump.Pcut_eq[OF tail_bump_bumpAt])

lemma P_bumpAt: "P (bumpAt M n) = map (\<lambda>b. bumpAt b n) (P M)"
proof (induction M rule: P.induct)
  case (1 M)
  show ?case
  proof (cases "multiT M \<and> 1 < Lng M")
    case True
    hence step: "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
      by (subst P.simps) simp
    from True have stepB:
      "P (bumpAt M n)
         = P (take (Pcut M) (bumpAt M n)) @ [drop (Pcut M) (bumpAt M n)]"
      by (subst P.simps) (simp add: bumpAt_multiT_eq bumpAt_Pcut_eq)
    have IH: "P (bumpAt (take (Pcut M) M) n) = map (\<lambda>b. bumpAt b n) (P (take (Pcut M) M))"
      using True 1 by blast
    show ?thesis
      using stepB step IH by (simp add: bumpAt_take bumpAt_drop)
  next
    case False
    have ncM: "\<not> (multiT M \<and> 1 < Lng M)" using False by simp
    have pM: "P M = [M]" by (subst P.simps) (rule if_not_P[OF ncM])
    moreover have "P (bumpAt M n) = [bumpAt M n]"
    proof -
      have nc: "\<not> (multiT (bumpAt M n) \<and> 1 < Lng (bumpAt M n))"
        using False by (simp add: bumpAt_multiT_eq)
      show ?thesis by (subst P.simps) (rule if_not_P[OF nc])
    qed
    ultimately show ?thesis by simp
  qed
qed


text \<open>bumpv interacts with a uniform \<open>+m\<close> shift by shifting the cut: this is the
  algebraic identity underlying the \<open>m\<^sub>1\<^sub>0>0\<close> recursion step.\<close>

lemma bumpv_shift: "bumpv (n + m) (v + m) = bumpv n v + m"
  by (simp add: bumpv_def)

lemma entry_diag_funpow_bumpAt0:
  assumes k: "k < m" and j: "j < Lng (diagSeq 0 k @ (IncrFirst ^^ m) X)"
  shows "entry (bumpAt (diagSeq 0 k @ (IncrFirst ^^ m) X) (n + m)) 0 j
       = entry (diagSeq 0 k @ (IncrFirst ^^ m) (bumpAt X n)) 0 j"
proof -
  let ?D = "diagSeq 0 k"
  have lenD: "length ?D = Suc k" by simp
  have jlt: "j < Suc k + Lng X" using j by simp
  show ?thesis
  proof (cases "j < Suc k")
    case True
    have eL: "entry (bumpAt (?D @ (IncrFirst ^^ m) X) (n + m)) 0 j = bumpv (n+m) j"
      using True j by (simp add: entry_bumpAt0 entry_diagSeq_append_lo)
    have eR: "entry (?D @ (IncrFirst ^^ m) (bumpAt X n)) 0 j = j"
      using True by (simp add: entry_diagSeq_append_lo)
    have "bumpv (n+m) j = j" using True k by (simp add: bumpv_def)
    thus ?thesis using eL eR by simp
  next
    case False
    have jge: "Suc k \<le> j" using False by simp
    have jX: "j - Suc k < Lng X" using jlt jge by simp
    have eX: "entry (?D @ (IncrFirst ^^ m) X) 0 j = entry ((IncrFirst ^^ m) X) 0 (j - Suc k)"
      using jge lenD jX by (simp add: nth_append entry_def)
    have eL: "entry (bumpAt (?D @ (IncrFirst ^^ m) X) (n+m)) 0 j
            = bumpv (n+m) (entry X 0 (j - Suc k) + m)"
      using j eX entry_bumpAt0[of j "?D @ (IncrFirst ^^ m) X" "n+m"]
            entry_funpow_IncrFirst0[OF jX] by simp
    have eR0: "entry (?D @ (IncrFirst ^^ m) (bumpAt X n)) 0 j
             = entry ((IncrFirst ^^ m) (bumpAt X n)) 0 (j - Suc k)"
      using jge lenD jX by (simp add: nth_append entry_def)
    have jXb: "j - Suc k < Lng (bumpAt X n)" using jX by simp
    have eR: "entry (?D @ (IncrFirst ^^ m) (bumpAt X n)) 0 j
            = bumpv n (entry X 0 (j - Suc k)) + m"
      using eR0 entry_funpow_IncrFirst0[OF jXb] entry_bumpAt0[OF jX] by simp
    show ?thesis using eL eR bumpv_shift by simp
  qed
qed

lemma bumpAt_diag_funpow:
  assumes k: "k < m"
  shows "bumpAt (diagSeq 0 k @ (IncrFirst ^^ m) X) (n + m)
       = diagSeq 0 k @ (IncrFirst ^^ m) (bumpAt X n)"
proof (rule nth_equalityI)
  show "length (bumpAt (diagSeq 0 k @ (IncrFirst ^^ m) X) (n + m))
      = length (diagSeq 0 k @ (IncrFirst ^^ m) (bumpAt X n))"
    by (simp add: bumpAt_def)
next
  fix j assume j: "j < length (bumpAt (diagSeq 0 k @ (IncrFirst ^^ m) X) (n + m))"
  have jL: "j < Lng (diagSeq 0 k @ (IncrFirst ^^ m) X)" using j by (simp add: bumpAt_def)
  let ?L = "bumpAt (diagSeq 0 k @ (IncrFirst ^^ m) X) (n + m)"
  let ?R = "diagSeq 0 k @ (IncrFirst ^^ m) (bumpAt X n)"
  have row0: "entry ?L 0 j = entry ?R 0 j" by (rule entry_diag_funpow_bumpAt0[OF k jL])
  \<comment> \<open>row 1: both leave row 1 alone; \<open>bumpAt\<close>/\<open>IncrFirst\<close> preserve row 1.\<close>
  have lenD: "length (diagSeq 0 k) = Suc k" by simp
  have jlt: "j < Suc k + Lng X" using jL by simp
  have row1: "entry ?L 1 j = entry ?R 1 j"
  proof (cases "j < Suc k")
    case True
    have e1: "entry ?L 1 j = entry (diagSeq 0 k @ (IncrFirst ^^ m) X) 1 j"
      using jL by (rule entry_bumpAt1)
    have "entry ?L 1 j = j" using e1 True by (simp add: entry_diagSeq_append_lo)
    moreover have "entry ?R 1 j = j" using True by (simp add: entry_diagSeq_append_lo)
    ultimately show ?thesis by simp
  next
    case False
    have jge: "Suc k \<le> j" using False by simp
    have jX: "j - Suc k < Lng X" using jlt jge by simp
    have eLb: "entry ?L 1 j = entry (diagSeq 0 k @ (IncrFirst ^^ m) X) 1 j"
      using jL by (rule entry_bumpAt1)
    have eLf: "entry (diagSeq 0 k @ (IncrFirst ^^ m) X) 1 j
             = entry ((IncrFirst ^^ m) X) 1 (j - Suc k)"
      using jge lenD jX by (simp add: nth_append entry_def)
    have eL: "entry ?L 1 j = entry X 1 (j - Suc k)"
      using eLb eLf entry_funpow_IncrFirst1[OF jX] by simp
    have jXb: "j - Suc k < Lng (bumpAt X n)" using jX by simp
    have eR1: "entry ?R 1 j = entry ((IncrFirst ^^ m) (bumpAt X n)) 1 (j - Suc k)"
      using jge lenD jXb by (simp add: nth_append entry_def)
    have eR: "entry ?R 1 j = entry (bumpAt X n) 1 (j - Suc k)"
      using eR1 entry_funpow_IncrFirst1[OF jXb] by simp
    show ?thesis using eL eR entry_bumpAt1[OF jX] by simp
  qed
  have "?L ! j = (entry ?L 0 j, entry ?L 1 j)" using jL by (cases "?L ! j") (simp add: entry_def bumpAt_def)
  moreover have "?R ! j = (entry ?R 0 j, entry ?R 1 j)" using jL by (cases "?R ! j") (simp add: entry_def)
  ultimately show "?L ! j = ?R ! j" using row0 row1 by simp
qed

text \<open>\<open>cutOK X n\<close>: the cut hypothesis (\<open>n \<ge> 1\<close> and the branch region past
  \<open>TrMax X\<close> has row-0 \<open>\<ge> n\<close>) under which the suffix bump @{const bumpAt} preserves
  @{const Red}.  It is exactly the @{locale cut_bump} \<open>tail_low\<close> axiom plus
  \<open>1 \<le> n\<close>; \<open>cut_bump (bumpAt X n) X n\<close> holds whenever \<open>cutOK X n\<close>.\<close>

definition cutOK :: "pairseq \<Rightarrow> nat \<Rightarrow> bool" where
  "cutOK X n \<longleftrightarrow> 1 \<le> n \<and> (\<forall>j. TrMax X < j \<longrightarrow> j < Lng X \<longrightarrow> n \<le> entry X 0 j)"

lemma cut_bump_bumpAt:
  assumes "cutOK X n" shows "cut_bump (bumpAt X n) X n"
  using assms
  by (intro cut_bump.intro cut_bump_axioms.intro tail_bump_bumpAt) (simp_all add: cutOK_def)

text \<open>Concrete cut for the top-level @{const coreReduce} pair: it satisfies the
  \<open>cut_bump\<close> hypotheses with cut \<open>m\<^sub>1\<^sub>0\<close> (the tail past \<open>TrMax\<close> has row-0 \<open>\<ge> m\<^sub>1\<^sub>0\<close>
  because the whole post-prefix tail does, by @{thm [source] njA_TrMax_ge_m10}).\<close>

lemma cut_bump_coreReduce:
  assumes T: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "cut_bump (coreReduce (IncrFirst M)) (coreReduce M) (entry M 1 0)"
proof -
  let ?m = "entry M 1 0"
  let ?R = "(IncrFirst ^^ ?m) M"
  have tb: "tail_bump (coreReduce (IncrFirst M)) (coreReduce M) ?m"
    by (rule tail_bump_coreReduce[OF T pos])
  have crX: "coreReduce M = diagSeq 0 (?m - 1) @ ?R" by (rule coreReduce_m10pos_form[OF pos])
  have lenD: "length (diagSeq 0 (?m - 1)) = ?m" using pos by simp
  show ?thesis
  proof (intro cut_bump.intro cut_bump_axioms.intro tb)
    fix j assume a: "TrMax (coreReduce M) < j" and b: "j < Lng (coreReduce M)"
    have m10le: "?m \<le> TrMax (coreReduce M)" by (rule njA_TrMax_ge_m10[OF T pos])
    have jge: "?m \<le> j" using a m10le by simp
    have jR: "j - ?m < Lng ?R" using b crX lenD jge by simp
    have eX: "entry (coreReduce M) 0 j = entry ?R 0 (j - ?m)"
      using crX jge lenD jR by (simp add: nth_append entry_def)
    have "?m \<le> entry ?R 0 (j - ?m)"
      using entry_funpow_IncrFirst0[OF jR[unfolded Lng_funpow_IncrFirst]] by simp
    thus "?m \<le> entry (coreReduce M) 0 j" using eX by simp
  qed
qed


subsection \<open>The \<open>cut_bump\<close> \<open>Red\<close>-collapse engine lemma\<close>

text \<open>Auxiliary: the shift recursion argument of \<open>bumpAt X n\<close> in the
  \<open>monoT, m\<^sub>1\<^sub>0 = 0\<close> branch equals @{const bumpAt} (at the shifted cut \<open>n - m\<^sub>0\<^sub>0\<close>)
  of the shift recursion argument of \<open>X\<close>.  Here \<open>X\<close> is \<open>monoT\<close> so \<open>m\<^sub>0\<^sub>0 =
  entry X 0 0\<close> is the row-0 minimum (@{thm [source] monoT_row0_min}), and the
  \<open>bumpv\<close>/shift algebra below holds pointwise.\<close>

lemma fin_shift_bumpv:
  assumes mle: "m \<le> v" and mn: "m < n"
  shows "bumpv n v - bumpv n m = bumpv (n - m) (v - m)"
proof (cases "v < n")
  case True
  hence "v - m < n - m" using mle mn by simp
  thus ?thesis using True mn mle by (simp add: bumpv_def)
next
  case False
  hence "\<not> v - m < n - m" using mn by simp
  thus ?thesis using False mn mle by (simp add: bumpv_def)
qed

text \<open>\<open>TrMax\<close> of the shift argument equals \<open>TrMax X\<close> (row-0 shift preserves
  the trunk structure).\<close>

lemma fin_TrMax_shiftRow0:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "TrMax (shiftRow0 M) = TrMax M"
proof -
  have n0: "nextrel0 (shiftRow0 M) = nextrel0 M"
    by (intro ext) (rule nextrel0_shiftRow0_eq[OF M mono])
  have n1: "nextrel1 (shiftRow0 M) = nextrel1 M"
    by (rule nextrel1_shiftRow0_eq[OF M mono])
  have "nextR (shiftRow0 M) = nextR M"
    by (intro ext) (simp add: nextR_def n0 n1)
  thus ?thesis by (simp add: TrMax_def)
qed

text \<open>Multi-branch cut survival: for a multiT \<open>X\<close> with @{const cutOK}, every
  operand block \<open>y \<in> P X\<close> inherits the cut.  A position \<open>j\<close> of \<open>y\<close> past the
  block trunk \<open>TrMax y\<close> maps to an \<open>X\<close>-position \<open>s + j\<close> past \<open>TrMax X\<close> (otherwise
  the steps \<open>0..j\<close> would all be trunk steps of \<open>y\<close>, forcing \<open>j \<le> TrMax y\<close>), so the
  row-0 cut \<open>n \<le> entry X 0 (s+j) = entry y 0 j\<close> transfers.\<close>

lemma fin_cut_block_tail:
  assumes XT: "X \<in> T_PS" and mu: "multiT X" and cut: "cutOK X n"
    and y: "y \<in> set (P X)" and jtr: "TrMax y < j" and jl: "j < Lng y"
  shows "n \<le> entry y 0 j"
proof -
  have ne: "P X \<noteq> []" by (rule P_nonempty)
  obtain J where JL: "J < length (P X)" and yJ: "y = P X ! J"
    using y by (metis in_set_conv_nth)
  let ?s = "IdxSum (P X) ! J"
  let ?e = "IdxSum (P X) ! (J + 1) - 1"
  have Jle: "J \<le> Lng (P X) - 1" using JL by simp
  have yseg: "y = seg X ?s ?e" using m_6_4_P_IdxSum[OF XT Jle] yJ by simp
  have srange: "?s \<le> Lng X - 1 \<and> (\<forall>j' < ?s. entry X 0 j' \<ge> entry X 0 ?s)"
    by (rule idxsum_leftend_lmin[OF XT JL])
  \<comment> \<open>block endpoints inside X.\<close>
  have Ly: "Lng y = Suc ?e - ?s" using yseg by (simp only: Lng_seg)
  have jly: "j < Suc ?e - ?s" using jl Ly by simp
  have nonempty: "0 < Lng y" using jl by linarith
  have eltX: "?e < Lng X"
  proof -
    have "concat (P X) = X" by (rule idxsum_concat_P)
    hence lensum: "Lng X = sum_list (map length (P X))"
      by (metis length_concat)
    have J1: "J + 1 \<le> length (P X)" using JL by simp
    have idx1: "IdxSum (P X) ! (J + 1) = sum_list (map length (take (J + 1) (P X)))"
      using J1 by (rule idxsum_nth)
    have mono': "sum_list (map length (take (J + 1) (P X)))
                  \<le> sum_list (map length (take (length (P X)) (P X)))"
      using idxsum_sum_take_mono[OF J1, of "P X"] by simp
    have "sum_list (map length (take (J + 1) (P X))) \<le> sum_list (map length (P X))"
      using mono' by (simp add: take_all)
    hence le1: "IdxSum (P X) ! (J + 1) \<le> Lng X" using idx1 lensum by simp
    \<comment> \<open>block nonempty: IdxSum!(J+1) = s + Lng y \<ge> 1.\<close>
    have diff: "IdxSum (P X) ! (J + 1) = ?s + length (P X ! J)" by (rule idxsum_diff[OF JL])
    have "length (P X ! J) = Lng y" using yJ by simp
    hence "IdxSum (P X) ! (J + 1) = ?s + Lng y" using diff by simp
    hence "0 < IdxSum (P X) ! (J + 1)" using nonempty by simp
    thus ?thesis using le1 by simp
  qed
  \<comment> \<open>map block-trunk position to X-position.\<close>
  have sj_pos: "?s + j > TrMax X"
  proof (rule ccontr)
    assume "\<not> ?s + j > TrMax X"
    hence sjle: "?s + j \<le> TrMax X" by simp
    \<comment> \<open>then steps 0..j of y are all trunk steps, so j \<le> TrMax y.\<close>
    have allstep: "\<forall>j'<j. nextR y 1 j' (j' + 1)"
    proof (intro allI impI)
      fix j' assume j'lt: "j' < j"
      have j'l: "j' < Lng y" using j'lt jl by simp
      have sj'1l: "j' + 1 < Lng y" using j'lt jl by linarith
      have sX: "?s + j' < Lng X" using j'l Ly eltX by linarith
      have sX1: "?s + (j' + 1) < Lng X" using sj'1l Ly eltX by linarith
      have trstep: "nextR X 1 (?s + j') (?s + j' + 1)"
      proof -
        have "?s + j' + 1 \<le> TrMax X" using j'lt sjle by simp
        hence "?s + j' < TrMax X" by simp
        thus ?thesis using TrMax_in_S[OF XT] by simp
      qed
      have aseg: "j' < Lng (seg X ?s ?e)" using j'l yseg by simp
      have bseg: "j' + 1 < Lng (seg X ?s ?e)" using sj'1l yseg by simp
      have rel: "nextR (seg X ?s ?e) 1 j' (j' + 1)
                  \<longleftrightarrow> nextR X 1 (?s + j') (?s + (j' + 1))"
        by (rule adm_nextR1_seg[OF eltX aseg bseg])
      have "nextR y 1 j' (j' + 1) \<longleftrightarrow> nextR X 1 (?s + j') (?s + (j' + 1))"
        using rel yseg by simp
      thus "nextR y 1 j' (j' + 1)" using trstep by simp
    qed
    \<comment> \<open>j \<in> S_y, so j \<le> TrMax y = Max S_y.\<close>
    have yne: "y \<noteq> []" using nonempty length_greater_0_conv by blast
    have yT: "y \<in> T_PS" using yne by (simp add: T_PS_def)
    let ?Sy = "{k. \<forall>j'<k. nextR y 1 j' (j' + 1)}"
    have Lypos: "0 < Lng y" using nonempty .
    have suby: "?Sy \<subseteq> {..Lng y - 1}"
    proof
      fix k assume "k \<in> ?Sy"
      hence H: "\<forall>j'<k. nextR y 1 j' (j' + 1)" by simp
      show "k \<in> {..Lng y - 1}"
      proof (rule ccontr)
        assume "k \<notin> {..Lng y - 1}"
        hence "Lng y - 1 < k" by simp
        hence "nextR y 1 (Lng y - 1) ((Lng y - 1) + 1)" using H by blast
        hence "(Lng y - 1) + 1 < Lng y" by (simp add: nextR_def nextrel1_def)
        thus False using Lypos by simp
      qed
    qed
    hence finy: "finite ?Sy" by (rule finite_subset) simp
    have jIn: "j \<in> ?Sy" using allstep by simp
    have "j \<le> Max ?Sy" by (rule Max_ge[OF finy jIn])
    hence "j \<le> TrMax y" by (simp add: TrMax_def)
    thus False using jtr by simp
  qed
  \<comment> \<open>now the cut on X gives the bound, transferred to y by entry_seg.\<close>
  have sjl: "?s + j < Lng X" using jl Ly eltX by linarith
  have nle: "n \<le> entry X 0 (?s + j)" using cut sj_pos sjl by (simp add: cutOK_def)
  have ey: "entry y 0 j = entry X 0 (?s + j)"
    using yseg jl by (simp add: entry_seg)
  show ?thesis using nle ey by simp
qed

text \<open>\<open>TrMax\<close> of the \<open>m\<^sub>1\<^sub>0>0\<close> recursion argument \<open>diagSeq 0 (m\<^sub>1\<^sub>0-1) @ (IncrFirst^m\<^sub>1\<^sub>0) X\<close>
  dominates \<open>TrMax X + m\<^sub>1\<^sub>0\<close>: the whole prefix region (diagonal of length \<open>m\<^sub>1\<^sub>0\<close> then
  the shifted trunk of \<open>X\<close>) is itself a trunk.\<close>

lemma fin_TrMax_argX_ge:
  assumes XT: "X \<in> T_PS" and mono: "monoT X" and pos: "0 < entry X 1 0"
  shows "TrMax X + entry X 1 0 \<le> TrMax (diagSeq 0 (entry X 1 0 - 1) @ (IncrFirst ^^ (entry X 1 0)) X)"
proof -
  let ?m = "entry X 1 0"
  let ?rest = "(IncrFirst ^^ ?m) X"
  let ?D = "diagSeq 0 (?m - 1)"
  let ?arg = "?D @ ?rest"
  have Xne: "X \<noteq> []" using XT by (simp add: T_PS_def)
  have L0: "0 < Lng X" using Xne by (cases X) auto
  have restne: "?rest \<noteq> []" using Xne by (metis Lng_funpow_IncrFirst length_0_conv)
  have argT: "?arg \<in> T_PS" using restne by (simp add: T_PS_def)
  have lenD: "length ?D = ?m" using pos by simp
  have lenDLng: "Lng ?D = ?m" using lenD by simp
  have restT: "?rest \<in> T_PS" using restne by (simp add: T_PS_def)
  have Lrest: "Lng ?rest = Lng X" by simp
  have trRest: "TrMax ?rest = TrMax X" by simp
  have dropEq: "drop ?m ?arg = ?rest" using lenD by simp
  have Larg: "Lng ?arg = ?m + Lng X" using lenDLng by simp
  \<comment> \<open>the trunk reaches m + TrMax X: all steps below are trunk steps.\<close>
  have allstep: "\<forall>j'<?m + TrMax X. nextR ?arg 1 j' (j' + 1)"
  proof (intro allI impI)
    fix j' assume j'lt: "j' < ?m + TrMax X"
    show "nextR ?arg 1 j' (j' + 1)"
    proof (cases "j' < ?m")
      case True
      have r0: "?m - 1 < entry ?rest 0 0"
        using entry_funpow_IncrFirst0[OF L0] pos by simp
      have r1: "?m - 1 < entry ?rest 1 0"
        using entry_funpow_IncrFirst1[OF L0] pos by simp
      have jk: "j' \<le> ?m - 1" using True pos by simp
      have "nextR (diagSeq 0 (?m - 1) @ ?rest) 1 j' (Suc j')"
        by (rule nextR1_diagSeq_append[OF restne r0 r1 jk])
      thus ?thesis by simp
    next
      case False
      hence jge: "?m \<le> j'" by simp
      let ?a = "j' - ?m"
      have aTr: "?a < TrMax X" using j'lt jge by simp
      have aLrest: "?a < Lng ?rest - 0" using aTr trRest TrMax_bound[OF restT] Lrest by linarith
      have a1Lrest: "?a + 1 < Lng ?rest"
        using aTr trRest TrMax_bound[OF restT] Lrest by linarith
      \<comment> \<open>trunk step in rest (rest shares X's trunk).\<close>
      have restStep: "nextR ?rest 1 ?a (?a + 1)"
        using TrMax_in_S[OF restT] aTr trRest by simp
      \<comment> \<open>transfer to arg via drop.\<close>
      have aLa: "?a < Lng ?arg - ?m" using aLrest Lrest Larg by simp
      have a1La: "?a + 1 < Lng ?arg - ?m" using a1Lrest Lrest Larg by simp
      have rel: "nextrel1 (drop ?m ?arg) ?a (?a + 1)
                  \<longleftrightarrow> nextrel1 ?arg (?m + ?a) (?m + (?a + 1))"
        by (rule poper_nextrel1_drop[OF aLa a1La])
      have lhs: "nextrel1 ?rest ?a (?a + 1)"
        using restStep by (simp add: nextR_def)
      have "nextrel1 ?arg (?m + ?a) (?m + (?a + 1))"
        using rel lhs dropEq by simp
      hence "nextrel1 ?arg j' (j' + 1)" using jge by simp
      thus ?thesis by (simp add: nextR_def)
    qed
  qed
  have "?m + TrMax X \<le> TrMax ?arg" by (rule le_TrMax_intro[OF argT allstep])
  thus ?thesis by simp
qed

text \<open>THE ENGINE LEMMA.  For every cut \<open>n\<close> with @{const cutOK}, the suffix bump
  @{const bumpAt} preserves @{const Red}.  Proved by @{thm [source] Red.pinduct}
  on \<open>X\<close> with the cut universally quantified, so the IH instantiates at the
  branch-specific cuts (\<open>Joints!J + 2\<close> for the branch descent, \<open>n - m\<^sub>0\<^sub>0\<close> for the
  shift descent, \<open>n + m\<^sub>1\<^sub>0\<close> for the \<open>m\<^sub>1\<^sub>0 > 0\<close> descent).\<close>

lemma fin_cut_bump_Red:
  "\<And>n. cutOK X n \<Longrightarrow> X \<in> T_PS \<Longrightarrow> Red (bumpAt X n) = Red X"
proof -
  have "X \<in> T_PS \<longrightarrow> (\<forall>n. cutOK X n \<longrightarrow> Red (bumpAt X n) = Red X)"
  proof (cases "X \<in> T_PS")
    case False thus ?thesis by simp
  next
    case XT0: True
    have domX: "Red_dom X" by (rule m_6_5_Red_welldef[OF XT0])
    show ?thesis
      using domX
    proof (induction X rule: Red.pinduct)
      case (1 X)
      note dom    = 1(1)
      note IH_mu  = 1(2)  \<comment> \<open>multiT IH\<close>
      note IH_bz  = 1(3)  \<comment> \<open>core-branch NJ IH\<close>
      note IH_sh  = 1(4)  \<comment> \<open>shift m10=0 IH\<close>
      note IH_m1  = 1(5)  \<comment> \<open>m10>0 IH\<close>
      show ?case
      proof (rule impI)
        assume XT: "X \<in> T_PS"
        show "\<forall>n. cutOK X n \<longrightarrow> Red (bumpAt X n) = Red X"
        proof (rule allI, rule impI)
        fix n :: nat
        assume cut: "cutOK X n"
        let ?A = "bumpAt X n"
        have n1: "1 \<le> n" using cut by (simp add: cutOK_def)
        have Xne: "X \<noteq> []" using XT by (simp add: T_PS_def)
        have LXpos: "0 < Lng X" using Xne by (cases X) auto
        have tb: "tail_bump ?A X n" by (rule tail_bump_bumpAt)
        have cb: "cut_bump ?A X n" by (rule cut_bump_bumpAt[OF cut])
        have AT: "?A \<in> T_PS" using Xne by (simp add: T_PS_def bumpAt_def)
        have domA: "Red_dom ?A" by (rule m_6_5_Red_welldef[OF AT])
        have zE: "zeroT ?A = zeroT X" by (rule tail_bump.zeroT_eq[OF tb])
        have muE: "multiT ?A = multiT X" by (rule tail_bump.multiT_eq[OF tb])
        have trE: "TrMax ?A = TrMax X" by (rule tail_bump.TrMax_eq[OF tb])
        show "Red ?A = Red X"
        proof (cases "zeroT X")
          case True
          have "Red ?A = [(0,0)]" using Red.psimps[OF domA] zE True by simp
          moreover have "Red X = [(0,0)]" using Red.psimps[OF dom] True by simp
          ultimately show ?thesis by simp
        next
          case nz: False
          show ?thesis
          proof (cases "multiT X")
            case mu: True
            \<comment> \<open>multi branch: align block by block; the blocks of A are bumpAt of blocks of X.\<close>
            have nzA: "\<not> zeroT ?A" using zE nz by simp
            have muA: "multiT ?A" using muE mu by simp
            have rX: "Red X = concat (map Red (P X))"
              using Red.psimps[OF dom] nz mu by simp
            have rA: "Red ?A = concat (map Red (P ?A))"
              using Red.psimps[OF domA] nzA muA by simp
            have PA: "P ?A = map (\<lambda>b. bumpAt b n) (P X)" by (rule P_bumpAt)
            \<comment> \<open>per-block IH at the SAME cut n.\<close>
            have blocks: "\<And>y. y \<in> set (P X) \<Longrightarrow> Red (bumpAt y n) = Red y"
            proof -
              fix y assume y: "y \<in> set (P X)"
              have yT: "y \<in> T_PS"
                using P_blocks_nonempty[OF Xne] y by (auto simp: T_PS_def)
              \<comment> \<open>cut survives on the block: y is a sub-block of X, its branch region
                  lies inside X's branch region, where row-0 \<ge> n.\<close>
              have cuty: "cutOK y n"
              proof -
                have "1 \<le> n" by (rule n1)
                moreover have "\<forall>j. TrMax y < j \<longrightarrow> j < Lng y \<longrightarrow> n \<le> entry y 0 j"
                proof (intro allI impI)
                  fix j assume jtr: "TrMax y < j" and jl: "j < Lng y"
                  \<comment> \<open>blocks of a multiT X are sub-trees; a block is itself a tree, so
                      its own branch region inherits the cut via membership in P X.\<close>
                  show "n \<le> entry y 0 j" by (rule fin_cut_block_tail[OF XT mu cut y jtr jl])
                qed
                ultimately show ?thesis by (simp add: cutOK_def)
              qed
              have ih: "y \<in> T_PS \<longrightarrow> (\<forall>m. cutOK y m \<longrightarrow> Red (bumpAt y m) = Red y)"
                by (rule IH_mu[OF nz mu y])
              thus "Red (bumpAt y n) = Red y" using yT cuty by blast
            qed
            have "Red ?A = concat (map Red (map (\<lambda>b. bumpAt b n) (P X)))"
              using rA PA by simp
            also have "\<dots> = concat (map (\<lambda>y. Red (bumpAt y n)) (P X))"
              by (simp add: comp_def)
            also have "\<dots> = concat (map Red (P X))"
              by (rule arg_cong[where f=concat], rule map_cong[OF refl]) (simp add: blocks)
            also have "\<dots> = Red X" using rX by simp
            finally show ?thesis .
          next
            case nmu: False
            have mono: "monoT X" using nz nmu by (simp add: multiT_def)
            have Xpt: "X \<in> PT_PS" using XT mono by (simp add: PT_PS_def)
            have nzA: "\<not> zeroT ?A" using zE nz by simp
            have nmuA: "\<not> multiT ?A" using muE nmu by simp
            let ?j1  = "Lng X - 1"
            let ?j1' = "TrMax X"
            let ?m00 = "entry X 0 0"
            let ?m10 = "entry X 1 0"
            \<comment> \<open>row-1 head is shared; row-0 head is bumped.\<close>
            have A10: "entry ?A 1 0 = ?m10" using entry_bumpAt1[OF LXpos] .
            have A00: "entry ?A 0 0 = bumpv n ?m00" using entry_bumpAt0[OF LXpos] .
            show ?thesis
            proof (cases "?m00 = 0 \<and> ?m10 = 0")
              case core: True
              hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
              have Ac0: "entry ?A 0 0 = 0" using A00 c0 n1 by (simp add: bumpv_def)
              have Ac1: "entry ?A 1 0 = 0" using A10 c1 by simp
              show ?thesis
              proof (cases "?j1' = ?j1")
                case trunk: True
                \<comment> \<open>core-trunk: both diagonal outputs, shared Lng/TrMax/m10.\<close>
                have rX: "Red X = diagSeq ?m10 (?m10 + ?j1)"
                  using Red.psimps[OF dom] nz nmu c0 c1 trunk by (simp add: Let_def)
                have AtrE: "TrMax ?A = Lng ?A - 1" using trE trunk by simp
                have rA: "Red ?A = diagSeq (entry ?A 1 0) (entry ?A 1 0 + (Lng ?A - 1))"
                  using Red.psimps[OF domA] nzA nmuA Ac0 Ac1 AtrE by (simp add: Let_def)
                show ?thesis using rA rX Ac1 c1 by simp
              next
                case tne: False
                \<comment> \<open>core-nontrunk: diagonal prefix + branch concat.  Align term by term.\<close>
                have Atrne: "TrMax ?A \<noteq> Lng ?A - 1" using trE tne by simp
                have rX: "Red X = diagSeq 0 ?j1' @
                      concat (map (\<lambda>J.
                          (IncrFirst ^^ (Joints X ! J + 1
                              - (if entry (Br X ! J) 1 0 = 0 then 0
                                 else Suc (THE j. nextR X 1 j (FirstNodes X ! J)))))
                            (Red ((entry X 0 0 + Joints X ! J + 1,
                                   entry X 1 0 + (if entry (Br X ! J) 1 0 = 0 then 0
                                          else Suc (THE j. nextR X 1 j (FirstNodes X ! J))))
                                  # tl (Br X ! J))))
                        [0..<Lng (Br X)])"
                  using Red.psimps[OF dom] nz nmu c0 c1 tne by (simp add: Let_def)
                have rA: "Red ?A = diagSeq 0 (TrMax ?A) @
                      concat (map (\<lambda>J.
                          (IncrFirst ^^ (Joints ?A ! J + 1
                              - (if entry (Br ?A ! J) 1 0 = 0 then 0
                                 else Suc (THE j. nextR ?A 1 j (FirstNodes ?A ! J)))))
                            (Red ((entry ?A 0 0 + Joints ?A ! J + 1,
                                   entry ?A 1 0 + (if entry (Br ?A ! J) 1 0 = 0 then 0
                                          else Suc (THE j. nextR ?A 1 j (FirstNodes ?A ! J))))
                                  # tl (Br ?A ! J))))
                        [0..<Lng (Br ?A)])"
                  using Red.psimps[OF domA] nzA nmuA Ac0 Ac1 Atrne by (simp add: Let_def)
                \<comment> \<open>structural equalities from the cut_bump locale.\<close>
                have brE: "Br ?A = map IncrFirst (Br X)" by (rule cut_bump.cb_Br_eq[OF cb])
                have LbrE: "Lng (Br ?A) = Lng (Br X)" by (simp add: brE)
                have jtE: "Joints ?A = Joints X" by (rule cut_bump.cb_Joints_eq[OF cb])
                have fnE: "FirstNodes ?A = FirstNodes X" by (rule cut_bump.cb_FirstNodes_eq[OF cb])
                have nxE: "nextR ?A = nextR X" by (rule tail_bump.nextR_eq[OF tb])
                \<comment> \<open>the branch-concat maps agree pointwise.\<close>
                have concatEq:
                  "concat (map (\<lambda>J.
                       (IncrFirst ^^ (Joints ?A ! J + 1
                           - (if entry (Br ?A ! J) 1 0 = 0 then 0
                              else Suc (THE j. nextR ?A 1 j (FirstNodes ?A ! J)))))
                         (Red ((entry ?A 0 0 + Joints ?A ! J + 1,
                                entry ?A 1 0 + (if entry (Br ?A ! J) 1 0 = 0 then 0
                                       else Suc (THE j. nextR ?A 1 j (FirstNodes ?A ! J))))
                               # tl (Br ?A ! J))))
                     [0..<Lng (Br ?A)])
                 = concat (map (\<lambda>J.
                       (IncrFirst ^^ (Joints X ! J + 1
                           - (if entry (Br X ! J) 1 0 = 0 then 0
                              else Suc (THE j. nextR X 1 j (FirstNodes X ! J)))))
                         (Red ((entry X 0 0 + Joints X ! J + 1,
                                entry X 1 0 + (if entry (Br X ! J) 1 0 = 0 then 0
                                       else Suc (THE j. nextR X 1 j (FirstNodes X ! J))))
                               # tl (Br X ! J))))
                     [0..<Lng (Br X)])"
                proof (rule arg_cong[where f=concat],
                       simp only: LbrE, rule map_cong[OF refl])
                  fix J assume "J \<in> set [0..<Lng (Br X)]"
                  hence JBr: "J < Lng (Br X)" by simp
                  hence JBr': "J < length (Br X)" by simp
                  \<comment> \<open>recursion arg of A's branch = bumpAt of recursion arg of X's branch.\<close>
                  let ?npX = "if entry (Br X ! J) 1 0 = 0 then 0
                              else Suc (THE j. nextR X 1 j (FirstNodes X ! J))"
                  have npXeq: "?npX = npJ X J" unfolding npJ_def by (rule refl)
                  have argXeq: "(entry X 0 0 + Joints X ! J + 1, entry X 1 0 + npJ X J)
                                # tl (Br X ! J) = NJ X J"
                    unfolding NJ_def by (rule refl)
                  have npE: "npJ ?A J = npJ X J" by (rule cut_bump.cb_npJ_eq[OF cb JBr'])
                  have npAeq: "(if entry (Br ?A ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR ?A 1 j (FirstNodes ?A ! J))) = npJ ?A J"
                    unfolding npJ_def by (rule refl)
                  have argAeq: "(entry ?A 0 0 + Joints ?A ! J + 1, entry ?A 1 0 + npJ ?A J)
                                # tl (Br ?A ! J) = NJ ?A J"
                    unfolding NJ_def by (rule refl)
                  \<comment> \<open>the NJ relation from cb_NJ_bumpAt.\<close>
                  have NJrel: "NJ ?A J = bumpAt (NJ X J) (Joints X ! J + 2)"
                    by (rule cut_bump.cb_NJ_bumpAt[OF cb Xpt n1 c0 c1 JBr'])
                  \<comment> \<open>side conditions for the IH.\<close>
                  have brJne: "Br X ! J \<noteq> []" by (rule Br_component_nonempty[OF Xpt JBr])
                  have NJXne: "NJ X J \<noteq> []" by (simp add: NJ_def)
                  have NJXT: "NJ X J \<in> T_PS" using NJXne by (simp add: T_PS_def)
                  \<comment> \<open>cutOK (NJ X J) (Joints X!J + 2): the branch tail (j>0) is row-0 \<ge> Joints!J+2.\<close>
                  have cutNJ: "cutOK (NJ X J) (Joints X ! J + 2)"
                  proof -
                    have ge1: "1 \<le> Joints X ! J + 2" by simp
                    have tail: "\<forall>j. TrMax (NJ X J) < j \<longrightarrow> j < Lng (NJ X J)
                                  \<longrightarrow> Joints X ! J + 2 \<le> entry (NJ X J) 0 j"
                    proof (intro allI impI)
                      fix j assume jtr: "TrMax (NJ X J) < j" and jl: "j < Lng (NJ X J)"
                      have jpos: "0 < j" using jtr by simp
                      have jBrX: "j < Lng (Br X ! J)" using jl Lng_NJ[OF brJne] by simp
                      \<comment> \<open>NJ tail (j>0) equals Br tail: NJ X J ! j = Br X ! J ! j.\<close>
                      have brJTPS: "Br X ! J \<in> T_PS" using brJne by (simp add: T_PS_def)
                      have moBr: "monoT (Br X ! J)"
                      proof -
                        have "zeroT (Br X ! J) \<or> monoT (Br X ! J)"
                          by (rule Br_component_nonmulti[OF Xpt JBr])
                        moreover have "\<not> zeroT (Br X ! J)"
                          using jBrX jpos by (auto simp: zeroT_def)
                        ultimately show ?thesis by blast
                      qed
                      have K: "Joints X ! J + 1 \<le> entry (Br X ! J) 0 0"
                        using joints_lt_branch_first[OF Xpt JBr] c0 by simp
                      have mn: "entry (Br X ! J) 0 0 < entry (Br X ! J) 0 j"
                        by (rule monoT_row0_min[OF brJTPS moBr jpos jBrX])
                      have ge: "Joints X ! J + 2 \<le> entry (Br X ! J) 0 j" using K mn by simp
                      have eNJ: "entry (NJ X J) 0 j = entry (Br X ! J) 0 j"
                        by (rule entry_NJ_hi[OF jpos jBrX])
                      show "Joints X ! J + 2 \<le> entry (NJ X J) 0 j" using ge eNJ by simp
                    qed
                    show ?thesis using ge1 tail by (simp add: cutOK_def)
                  qed
                  \<comment> \<open>apply the IH at the branch cut.\<close>
                  have ih: "NJ X J \<in> T_PS \<longrightarrow>
                              (\<forall>m. cutOK (NJ X J) m \<longrightarrow> Red (bumpAt (NJ X J) m) = Red (NJ X J))"
                    using IH_bz[OF nz nmu refl refl refl refl _ tne, of J] c0 c1
                          npXeq argXeq JBr by (simp only: npXeq argXeq) (simp add: c0 c1 NJ_def npJ_def)
                  have RedNJ: "Red (NJ ?A J) = Red (NJ X J)"
                    using ih NJXT cutNJ NJrel by simp
                  \<comment> \<open>the IncrFirst exponents agree (Joints/npJ shared).\<close>
                  have expE: "Joints ?A ! J + 1 - npJ ?A J = Joints X ! J + 1 - npJ X J"
                    using jtE npE by simp
                  show "(IncrFirst ^^ (Joints ?A ! J + 1
                            - (if entry (Br ?A ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR ?A 1 j (FirstNodes ?A ! J)))))
                          (Red ((entry ?A 0 0 + Joints ?A ! J + 1,
                                 entry ?A 1 0 + (if entry (Br ?A ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR ?A 1 j (FirstNodes ?A ! J))))
                                # tl (Br ?A ! J)))
                      = (IncrFirst ^^ (Joints X ! J + 1
                            - (if entry (Br X ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR X 1 j (FirstNodes X ! J)))))
                          (Red ((entry X 0 0 + Joints X ! J + 1,
                                 entry X 1 0 + (if entry (Br X ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR X 1 j (FirstNodes X ! J))))
                                # tl (Br X ! J)))"
                    by (simp only: npAeq npXeq argAeq argXeq expE RedNJ)
                qed
                have prefE: "diagSeq 0 (TrMax ?A) = diagSeq 0 ?j1'" using trE by simp
                show ?thesis using rA rX prefE concatEq by simp
              qed
            next
              case nc: False
              show ?thesis
              proof (cases "?m10 = 0")
                case c1z: True
                \<comment> \<open>shift branch (m10=0, m00>0): both take shift; recursion args related by bumpAt.\<close>
                have c0p: "0 < ?m00" using nc c1z by simp
                have Ac1: "entry ?A 1 0 = 0" using A10 c1z by simp
                have Anc: "\<not> (entry ?A 0 0 = 0 \<and> entry ?A 1 0 = 0)"
                proof -
                  have "entry ?A 0 0 = bumpv n ?m00" using A00 .
                  hence "0 < entry ?A 0 0" using c0p by (simp add: bumpv_def)
                  thus ?thesis by simp
                qed
                let ?SX = "map (\<lambda>j. (entry X 0 j - ?m00, entry X 1 j)) [0..<Suc ?j1]"
                let ?SA = "map (\<lambda>j. (entry ?A 0 j - entry ?A 0 0, entry ?A 1 j))
                               [0..<Suc (Lng ?A - 1)]"
                have rX: "Red X = Red ?SX"
                  using Red.psimps[OF dom] nz nmu nc c1z by (simp add: Let_def)
                have rA: "Red ?A = Red ?SA"
                  using Red.psimps[OF domA] nzA nmuA Anc Ac1 by (simp add: Let_def)
                have LAj: "Lng ?A - 1 = ?j1" by simp
                \<comment> \<open>X is monoT so m00 is the row-0 minimum: entry X 0 j \<ge> m00 for all j.\<close>
                have minrow0: "\<And>j. j < Lng X \<Longrightarrow> ?m00 \<le> entry X 0 j"
                proof -
                  fix j assume jl: "j < Lng X"
                  show "?m00 \<le> entry X 0 j"
                  proof (cases "j = 0")
                    case True thus ?thesis by simp
                  next
                    case False
                    hence jpos: "0 < j" by simp
                    show ?thesis using monoT_row0_min[OF XT mono jpos jl] by simp
                  qed
                qed
                \<comment> \<open>shift arg of A = bumpAt of shift arg of X at cut (n - m00).\<close>
                have SXeq: "?SX = shiftRow0 X"
                proof -
                  have "Suc ?j1 = Lng X" using LXpos by simp
                  thus ?thesis by (simp add: shiftRow0_def)
                qed
                have SXT: "?SX \<in> T_PS" by (simp add: T_PS_def)
                have monoSX: "monoT ?SX" using monoT_shiftRow0[OF XT mono] SXeq by simp
                show ?thesis
                proof (cases "n \<le> ?m00")
                  case nle: True
                  \<comment> \<open>cut absorbed: \<open>n \<le> m00\<close>, so the bump on the shifted values vanishes (both
                      \<open>v\<close> and \<open>m00\<close> are \<open>\<ge> n\<close>, so each is bumped and the difference is unchanged):
                      \<open>SA = SX\<close>.\<close>
                  have SAeqSX: "?SA = ?SX"
                  proof (rule nth_equalityI)
                    show "length ?SA = length ?SX" by simp
                  next
                    fix p assume p: "p < length ?SA"
                    have plen: "p < Suc ?j1" using p by simp
                    have pl: "p < Lng X" using plen LXpos by simp
                    have idx: "[0..<Suc ?j1] ! p = p" using pl by (simp add: nth_upt del: upt_Suc)
                    have eA0: "entry ?A 0 p = bumpv n (entry X 0 p)" by (rule entry_bumpAt0[OF pl])
                    have eA1: "entry ?A 1 p = entry X 1 p" by (rule entry_bumpAt1[OF pl])
                    have vmin: "?m00 \<le> entry X 0 p" by (rule minrow0[OF pl])
                    have vge: "n \<le> entry X 0 p" using vmin nle by simp
                    have shp: "bumpv n (entry X 0 p) - bumpv n ?m00 = entry X 0 p - ?m00"
                      using vge nle by (simp add: bumpv_def)
                    have lhs: "?SA ! p = (bumpv n (entry X 0 p) - bumpv n ?m00, entry X 1 p)"
                      using p eA0 eA1 A00 idx LAj by (simp del: upt_Suc)
                    have SXp: "?SX ! p = (entry X 0 p - ?m00, entry X 1 p)"
                      using plen idx by (simp del: upt_Suc)
                    show "?SA ! p = ?SX ! p" using lhs shp SXp by simp
                  qed
                  show ?thesis by (simp only: rA rX SAeqSX)
                next
                  case nle: False
                  hence ngt: "?m00 < n" by simp
                  have cut1: "1 \<le> n - ?m00" using ngt by simp
                  \<comment> \<open>shift arg of A = bumpAt of shift arg of X at cut (n - m00).\<close>
                  have SAbump: "?SA = bumpAt ?SX (n - ?m00)"
                  proof (rule nth_equalityI)
                    show "length ?SA = length (bumpAt ?SX (n - ?m00))"
                      by (simp add: bumpAt_def)
                  next
                    fix p assume p: "p < length ?SA"
                    have plen: "p < Suc ?j1" using p by simp
                    have pl: "p < Lng X" using plen LXpos by simp
                    have idx: "[0..<Suc ?j1] ! p = p" using pl by (simp add: nth_upt del: upt_Suc)
                    have eA0: "entry ?A 0 p = bumpv n (entry X 0 p)" by (rule entry_bumpAt0[OF pl])
                    have eA1: "entry ?A 1 p = entry X 1 p" by (rule entry_bumpAt1[OF pl])
                    have vmin: "?m00 \<le> entry X 0 p" by (rule minrow0[OF pl])
                    have lhs: "?SA ! p = (bumpv n (entry X 0 p) - bumpv n ?m00, entry X 1 p)"
                      using p eA0 eA1 A00 idx LAj by (simp del: upt_Suc)
                    have shp: "bumpv n (entry X 0 p) - bumpv n ?m00
                                 = bumpv (n - ?m00) (entry X 0 p - ?m00)"
                      by (rule fin_shift_bumpv[OF vmin ngt])
                    have SXp: "?SX ! p = (entry X 0 p - ?m00, entry X 1 p)"
                      using plen idx by (simp del: upt_Suc)
                    have pSX: "p < length ?SX" using plen by simp
                    have "bumpAt ?SX (n - ?m00) ! p
                            = (\<lambda>pp. (bumpv (n - ?m00) (fst pp), snd pp)) (?SX ! p)"
                      unfolding bumpAt_def by (rule nth_map[OF pSX])
                    also have "\<dots> = (bumpv (n - ?m00) (entry X 0 p - ?m00), entry X 1 p)"
                      using SXp by simp
                    also have "\<dots> = ?SA ! p" using lhs shp by simp
                    finally show "?SA ! p = bumpAt ?SX (n - ?m00) ! p" by (rule sym)
                  qed
                  \<comment> \<open>cutOK (shift arg) (n - m00): TrMax preserved, tail row-0 \<ge> n - m00.\<close>
                  have trSX: "TrMax ?SX = TrMax X"
                    using fin_TrMax_shiftRow0[OF XT mono] SXeq by simp
                  have cutSX: "cutOK ?SX (n - ?m00)"
                  proof -
                    have tail: "\<forall>j. TrMax ?SX < j \<longrightarrow> j < Lng ?SX
                                  \<longrightarrow> n - ?m00 \<le> entry ?SX 0 j"
                    proof (intro allI impI)
                      fix j assume jtr: "TrMax ?SX < j" and jl: "j < Lng ?SX"
                      have jlX: "j < Lng X" using jl LXpos by simp
                      have jtrX: "TrMax X < j" using jtr trSX by simp
                      have e: "entry ?SX 0 j = entry X 0 j - ?m00"
                        using SXeq entry_shiftRow0_0[OF jlX] by simp
                      have ge: "n \<le> entry X 0 j" using cut jtrX jlX by (simp add: cutOK_def)
                      show "n - ?m00 \<le> entry ?SX 0 j" using e ge by simp
                    qed
                    show ?thesis using cut1 tail by (simp add: cutOK_def)
                  qed
                  \<comment> \<open>apply the shift IH.\<close>
                  have ih: "?SX \<in> T_PS \<longrightarrow>
                              (\<forall>m. cutOK ?SX m \<longrightarrow> Red (bumpAt ?SX m) = Red ?SX)"
                    using IH_sh[OF nz nmu refl refl refl refl nc c1z] by simp
                  have SS: "Red ?SA = Red ?SX" using ih SXT cutSX SAbump by simp
                  show ?thesis by (simp only: rA rX SS)
                qed
              next
                case c1p: False
                hence pos: "0 < ?m10" by simp
                \<comment> \<open>m10>0 branch: recursion arg of A is the diag-funpow bump at cut (n + m10).\<close>
                have Apos: "0 < entry ?A 1 0" using A10 pos by simp
                have Anc: "\<not> (entry ?A 0 0 = 0 \<and> entry ?A 1 0 = 0)" using Apos by simp
                have Am10: "entry ?A 1 0 = ?m10" using A10 .
                let ?argX = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) X"
                let ?argA = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) ?A"
                have funX_ne: "(IncrFirst ^^ ?m10) X \<noteq> []"
                  using Xne by (metis Lng_funpow_IncrFirst length_0_conv)
                have argXT: "?argX \<in> T_PS" using funX_ne by (simp add: T_PS_def)
                have Ane: "?A \<noteq> []" using Xne by (simp add: bumpAt_def)
                have funA_ne: "(IncrFirst ^^ ?m10) ?A \<noteq> []"
                  using Ane by (metis Lng_funpow_IncrFirst length_0_conv)
                have argAT: "?argA \<in> T_PS" using funA_ne by (simp add: T_PS_def)
                \<comment> \<open>recursion arg of A equals bumpAt of recursion arg of X at cut (n + m10).\<close>
                have kpos: "?m10 - 1 < ?m10" using pos by simp
                have bumpFun: "bumpAt ?argX (n + ?m10) = ?argA"
                  using bumpAt_diag_funpow[OF kpos, of X n] by simp
                \<comment> \<open>cutOK (?argX) (n + m10): tail past TrMax has row-0 \<ge> n + m10.\<close>
                have cutArg: "cutOK ?argX (n + ?m10)"
                proof -
                  let ?D = "diagSeq 0 (?m10 - 1)"
                  let ?R = "(IncrFirst ^^ ?m10) X"
                  have lenD: "length ?D = ?m10" using pos by simp
                  have m10le: "?m10 \<le> TrMax ?argX"
                    using njA_TrMax_ge_m10[OF XT pos] coreReduce_m10pos_form[OF pos] by simp
                  have ge1: "1 \<le> n + ?m10" using n1 by simp
                  have tail: "\<forall>j. TrMax ?argX < j \<longrightarrow> j < Lng ?argX
                                \<longrightarrow> n + ?m10 \<le> entry ?argX 0 j"
                  proof (intro allI impI)
                    fix j assume jtr: "TrMax ?argX < j" and jl: "j < Lng ?argX"
                    have jge: "?m10 \<le> j" using jtr m10le by simp
                    have jR: "j - ?m10 < Lng ?R" using jl lenD jge by simp
                    have jRX: "j - ?m10 < Lng X" using jR by simp
                    have eX: "entry ?argX 0 j = entry ?R 0 (j - ?m10)"
                      using jge lenD jR by (simp add: nth_append entry_def)
                    have eR: "entry ?R 0 (j - ?m10) = entry X 0 (j - ?m10) + ?m10"
                      by (rule entry_funpow_IncrFirst0[OF jRX])
                    \<comment> \<open>need entry X 0 (j-m10) \<ge> n.  The original tail-low gives this past TrMax X;
                        but here j-m10 ranges over all of X.  Use: row-0 of the funpow shift
                        is \<ge> m10 already; combined with cut on X.\<close>
                    have jtrX: "TrMax X < j - ?m10 \<or> j - ?m10 \<le> TrMax X" by linarith
                    show "n + ?m10 \<le> entry ?argX 0 j"
                    proof (cases "TrMax X < j - ?m10")
                      case True
                      have "n \<le> entry X 0 (j - ?m10)"
                        using cut True jRX by (simp add: cutOK_def)
                      thus ?thesis using eX eR by simp
                    next
                      case False
                      \<comment> \<open>j - m10 \<le> TrMax X: the trunk of argX past its own TrMax cannot lie
                          inside the (shifted) trunk of X.  Contradiction with jtr.\<close>
                      have "j - ?m10 \<le> TrMax X" using False by simp
                      hence "j \<le> TrMax X + ?m10" using jge by simp
                      \<comment> \<open>TrMax argX \<ge> TrMax X + m10 because the diagonal prefix + shifted trunk
                          is a trunk of argX.\<close>
                      have trargX: "TrMax X + ?m10 \<le> TrMax ?argX"
                        by (rule fin_TrMax_argX_ge[OF XT mono pos])
                      hence "j \<le> TrMax ?argX" using \<open>j \<le> TrMax X + ?m10\<close> by simp
                      thus ?thesis using jtr by simp
                    qed
                  qed
                  show ?thesis using ge1 tail by (simp add: cutOK_def)
                qed
                \<comment> \<open>apply the m10>0 IH.\<close>
                have c1p': "?m10 \<noteq> 0" using pos by simp
                have ih: "?argX \<in> T_PS \<longrightarrow>
                            (\<forall>m. cutOK ?argX m \<longrightarrow> Red (bumpAt ?argX m) = Red ?argX)"
                  using IH_m1[OF nz nmu refl refl refl refl nc c1p'] by simp
                have ihapp: "Red (bumpAt ?argX (n + ?m10)) = Red ?argX"
                  using ih argXT cutArg by blast
                have NN: "Red ?argA = Red ?argX"
                  using ihapp bumpFun by simp
                \<comment> \<open>both productive outputs read off N = Red argX resp. N' = Red argA via same map.\<close>
                let ?N  = "Red ?argX"
                let ?N' = "Red ?argA"
                have LN: "Lng ?N = ?m10 + Lng X"
                  using m_6_5_monoT_Red_fact1_Lng[OF XT pos] by simp
                have jN_ge: "?m10 \<le> Lng ?N - 1" using LN LXpos by linarith
                have segN_PT: "seg ?N ?m10 (Lng ?N - 1) \<in> PT_PS"
                  using m_6_5_monoT_Red_m10pos[OF Xpt pos] by simp
                have thenX: "?m10 \<le> Lng ?N - 1 \<and> seg ?N ?m10 (Lng ?N - 1) \<in> PT_PS"
                  using jN_ge segN_PT by simp
                let ?outMap = "\<lambda>P m. map (\<lambda>j. (entry P 0 j - entry P 0 m + entry P 1 m,
                                              entry P 1 j)) [m..<Suc (Lng P - 1)]"
                have rX: "Red X = ?outMap ?N ?m10"
                  using Red.psimps[OF dom] nz nmu nc pos thenX by (simp add: Let_def)
                have thenA: "?m10 \<le> Lng ?N - 1
                              \<and> seg ?N ?m10 (Lng ?N - 1) \<in> PT_PS"
                  using thenX by simp
                \<comment> \<open>rewrite A-side data to X-side via NN (\<open>N' = N\<close>) and Am10 first.\<close>
                have rA: "Red ?A = ?outMap ?N ?m10"
                  using Red.psimps[OF domA] nzA nmuA Anc Apos thenA NN Am10
                  by (simp add: Let_def)
                show ?thesis using rA rX by simp
              qed
            qed
          qed
        qed
        qed
      qed
    qed
  qed
  thus "\<And>n. cutOK X n \<Longrightarrow> X \<in> T_PS \<Longrightarrow> Red (bumpAt X n) = Red X" by blast
qed


subsection \<open>The \<open>(B2)\<close> deliverable and \<open>Red\<close>/\<open>IncrFirst\<close> invariance (\<open>p_6_5_Red_IncrFirst\<close>)\<close>

text \<open>\<open>cutOK\<close> for the top-level @{const coreReduce} cut: the tail past \<open>TrMax\<close> has
  row-0 \<open>\<ge> m\<^sub>1\<^sub>0\<close> (from @{thm [source] cut_bump_coreReduce}'s \<open>tail_low\<close>).\<close>

lemma fin_cutOK_coreReduce:
  assumes T: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "cutOK (coreReduce M) (entry M 1 0)"
proof -
  let ?m = "entry M 1 0"
  have cb: "cut_bump (coreReduce (IncrFirst M)) (coreReduce M) ?m"
    by (rule cut_bump_coreReduce[OF T mono pos])
  have tail: "\<And>j. TrMax (coreReduce M) < j \<Longrightarrow> j < Lng (coreReduce M)
                  \<Longrightarrow> ?m \<le> entry (coreReduce M) 0 j"
    by (rule cut_bump.tail_low[OF cb])
  show ?thesis using pos tail by (simp add: cutOK_def)
qed

text \<open>The top-level cut identity: \<open>coreReduce (IncrFirst M)\<close> is the suffix bump of
  \<open>coreReduce M\<close> at cut \<open>m\<^sub>1\<^sub>0\<close>.  Both are equal-length, share row 1, and row 0 of
  the former is the @{const bumpv} of the latter (the @{locale tail_bump}
  characterisation from @{thm [source] cut_bump_coreReduce}).\<close>

lemma fin_coreReduce_IncrFirst_bumpAt:
  assumes T: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "coreReduce (IncrFirst M) = bumpAt (coreReduce M) (entry M 1 0)"
proof -
  let ?m = "entry M 1 0"
  let ?A = "coreReduce (IncrFirst M)"
  let ?X = "coreReduce M"
  have tb: "tail_bump ?A ?X ?m" by (rule tail_bump_coreReduce[OF T pos])
  show ?thesis
  proof (rule nth_equalityI)
    show "length ?A = length (bumpAt ?X ?m)"
      using tail_bump.len_eq[OF tb] by (simp add: bumpAt_def)
  next
    fix p assume p: "p < length ?A"
    have pX: "p < Lng ?X" using p tail_bump.len_eq[OF tb] by simp
    have e0: "entry ?A 0 p = bumpv ?m (entry ?X 0 p)"
      by (rule tail_bump.row0_bump[OF tb pX])
    have e1: "entry ?A 1 p = entry ?X 1 p"
      by (rule tail_bump.row1_eq[OF tb pX])
    have pb: "p < length (bumpAt ?X ?m)" using p tail_bump.len_eq[OF tb] by (simp add: bumpAt_def)
    have bA: "bumpAt ?X ?m ! p = (bumpv ?m (fst (?X ! p)), snd (?X ! p))"
      unfolding bumpAt_def using pX by (simp add: nth_map)
    have "?A ! p = (entry ?A 0 p, entry ?A 1 p)" using p by (cases "?A ! p") (simp add: entry_def)
    also have "\<dots> = (bumpv ?m (fst (?X ! p)), snd (?X ! p))"
      using e0 e1 by (simp add: entry_def)
    also have "\<dots> = bumpAt ?X ?m ! p" using bA by simp
    finally show "?A ! p = bumpAt ?X ?m ! p" .
  qed
qed

end

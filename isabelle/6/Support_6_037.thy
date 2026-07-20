theory Support_6_037
  imports Frontier_6_054
begin

text \<open>rmt KEYSTONE: \<open>Red\<close> preserves @{const monoT}.  Forward direction of
  \<open>p_6_5_Red_monoT\<close> (\<open>= \<not> multiT (Red M)\<close> for mono \<open>M\<close>, needed by the idempotency
  chain).  Proved by @{const Red}'s well-founded induction; the productive
  branches reuse the value-monotonicity bricks (\<open>m_6_5_Red_leftend_row0_min\<close>,
  the core-nontrunk strict suffix-min, the \<open>m\<^sub>1\<^sub>0>0\<close> brick
  @{thm [source] m_6_5_monoT_Red_m10pos}).\<close>

lemma m_6_5_Red_preserves_monoT:
  assumes M: "M \<in> PT_PS"
  shows "monoT (Red M)"
proof -
  have MT0: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT0])
  have "M \<in> T_PS \<longrightarrow> monoT M \<longrightarrow> monoT (Red M)"
    using domM
  proof (induction M rule: Red.pinduct)
    case (1 M)
    note dom    = 1(1)
    note IH_nc3 = 1(4)  \<comment> \<open>non-core m10=0 shift IH\<close>
    show ?case
    proof (rule impI, rule impI)
      assume MT': "M \<in> T_PS" and mono: "monoT M"
      have MPT: "M \<in> PT_PS" using MT' mono by (simp add: PT_PS_def)
      have Mne: "M \<noteq> []" using MT' by (simp add: T_PS_def)
      have LMpos: "0 < Lng M" using Mne by (cases M) auto
      have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
      have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
      let ?j1  = "Lng M - 1"
      let ?j1' = "TrMax M"
      let ?m00 = "entry M 0 0"
      let ?m10 = "entry M 1 0"
      have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT'])
      have Rne: "Red M \<noteq> []" using LrM LMpos by (cases "Red M") auto
      have RT: "Red M \<in> T_PS" using Rne by (simp add: T_PS_def)
      show "monoT (Red M)"
      proof (cases "?m00 = 0 \<and> ?m10 = 0")
        case core: True
        hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
        show ?thesis
        proof (cases "?j1' = ?j1")
          \<comment> \<open>core-trunk: Red M = diagSeq 0 j1, monoT (diagonal).\<close>
          case True
          have rM: "Red M = diagSeq ?m10 (?m10 + ?j1)"
            using Red.psimps[OF dom] nz nmu c0 c1 True by (simp add: Let_def)
          have rM': "Red M = diagSeq 0 ?j1" using rM c1 by simp
          have le0R: "le0 (Red M) 0 (Lng (Red M) - 1)"
          proof -
            have b0: "(0::nat) < Suc ?j1 - 0" by simp
            have b1: "?j1 < Suc ?j1 - 0" by simp
            have "le0 (diagSeq 0 ?j1) 0 ?j1"
              using le0_diagSeq[OF b0 b1] by simp
            moreover have "Lng (Red M) - 1 = ?j1" using LrM by simp
            ultimately show ?thesis using rM' by simp
          qed
          have nzR: "\<not> zeroT (Red M)"
          proof (cases "Lng (Red M) = 1")
            case True
            have "Lng M = 1" using True LrM by simp
            hence "zeroT M" using c1 by (simp add: zeroT_def)
            thus ?thesis using nz by simp
          next
            case False thus ?thesis by (simp add: zeroT_def)
          qed
          show ?thesis using nzR le0R by (simp add: monoT_def leR_def)
        next
          \<comment> \<open>core-nontrunk: leftend 0 is a strict row-0 suffix-min, reaching the end.\<close>
          case tne: False
          have e0: "entry (Red M) 0 0 = 0"
            by (rule fin_Red_leftend_row0_eq_m10[OF MT' mono, simplified c1])
          have suffmin: "\<forall>j. 0 < j \<longrightarrow> j < Lng (Red M) \<longrightarrow> 0 < entry (Red M) 0 j"
            by (rule rmt_core_nontrunk_strict_suffix_min[OF MPT c0 c1 tne])
          have nzR: "\<not> zeroT (Red M)"
          proof (cases "Lng (Red M) = 1")
            case True
            have "Lng M = 1" using True LrM by simp
            hence "zeroT M" using c1 by (simp add: zeroT_def)
            thus ?thesis using nz by simp
          next
            case False thus ?thesis by (simp add: zeroT_def)
          qed
          have LRpos: "0 < Lng (Red M)" using LrM LMpos by simp
          have le0R: "le0 (Red M) 0 (Lng (Red M) - 1)"
          proof (cases "Lng (Red M) = 1")
            case True thus ?thesis using LRpos by (simp add: le0_def)
          next
            case False
            hence lt: "0 < Lng (Red M) - 1" using LRpos by linarith
            have jNlt: "Lng (Red M) - 1 < Lng (Red M)" using LRpos by linarith
            have strict: "\<And>k. 0 < k \<Longrightarrow> k \<le> Lng (Red M) - 1
                            \<Longrightarrow> entry (Red M) 0 0 < entry (Red M) 0 k"
            proof -
              fix k assume a: "0 < k" and b: "k \<le> Lng (Red M) - 1"
              have klt: "k < Lng (Red M)" using b jNlt by simp
              have "0 < entry (Red M) 0 k" using suffmin a klt by blast
              thus "entry (Red M) 0 0 < entry (Red M) 0 k" using e0 by simp
            qed
            have "leR (Red M) 0 0 (Lng (Red M) - 1)"
              by (rule m_5_1_parent_exists_3[OF RT lt jNlt strict])
            thus ?thesis by (simp add: leR_def)
          qed
          show ?thesis using nzR le0R by (simp add: monoT_def leR_def)
        qed
      next
        case nc: False
        show ?thesis
        proof (cases "?m10 = 0")
          \<comment> \<open>shift branch: Red M = Red (shiftRow0 M); IH on shiftRow0 M.\<close>
          case True
          let ?shift = "map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc ?j1]"
          have rM: "Red M = Red ?shift"
            using Red.psimps[OF dom] nz nmu nc True by (simp add: Let_def)
          have shift_eq: "?shift = shiftRow0 M"
            using LMpos by (simp add: shiftRow0_def)
          have shift_T: "?shift \<in> T_PS" by (simp add: T_PS_def)
          have shift_mono: "monoT ?shift"
            using monoT_shiftRow0[OF MT' mono] shift_eq by simp
          have IH': "monoT (Red ?shift)"
            using IH_nc3[OF nz nmu refl refl refl refl nc True] shift_T shift_mono by blast
          show ?thesis using IH' rM by simp
        next
          \<comment> \<open>m10>0 branch: Red M = productive segment, monoT by m_6_5_monoT_Red_m10pos.\<close>
          case False
          hence c1p: "0 < ?m10" by simp
          let ?arg = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
          have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
            using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
          have arg_T: "?arg \<in> T_PS" using funpow_ne by (simp add: T_PS_def)
          let ?N = "Red ?arg"
          let ?jN = "Lng ?N - 1"
          have rM: "Red M = (let N = ?N; jN = ?jN in
                     if ?m10 \<le> jN \<and> seg N ?m10 jN \<in> PT_PS then
                       map (\<lambda>j. (entry N 0 j - entry N 0 ?m10 + entry N 1 ?m10,
                                 entry N 1 j))
                           [?m10..<Suc jN]
                     else M)"
            using Red.psimps[OF dom] nz nmu nc c1p by (simp add: Let_def)
          have segPT: "seg ?N ?m10 ?jN \<in> PT_PS"
            using m_6_5_monoT_Red_m10pos[OF MPT c1p] by simp
          have LN: "Lng ?N = Lng M + ?m10"
            using m_6_5_monoT_Red_fact1_Lng[OF MT' c1p]
                  coreReduce_m10pos_form[OF c1p] by simp
          have m10le: "?m10 \<le> ?jN" using LN LMpos by linarith
          have then_cond: "?m10 \<le> ?jN \<and> seg ?N ?m10 ?jN \<in> PT_PS"
            using m10le segPT by simp
          have rM': "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                        entry ?N 1 j))
                                 [?m10..<Suc ?jN]"
            using rM then_cond by (simp add: Let_def del: upt_Suc)
          let ?S = "seg ?N ?m10 ?jN"
          let ?d0 = "entry ?N 0 ?m10"
          let ?b1 = "entry ?N 1 ?m10"
          let ?R = "map (\<lambda>p. (fst p - ?d0 + ?b1, snd p)) ?S"
          have segeq: "Red M = ?R"
          proof -
            have "?S = map (\<lambda>j. ?N ! j) [?m10..<Suc ?jN]" by (simp add: seg_def)
            thus ?thesis using rM' by (simp add: entry_def del: upt_Suc cong: map_cong)
          qed
          have seg_mono: "monoT ?S" using segPT by (simp add: PT_PS_def)
          have LSR: "Lng ?R = Lng ?S" by simp
          have eR0: "\<And>j. j < Lng ?S \<Longrightarrow> entry ?R 0 j = entry ?S 0 j - ?d0 + ?b1"
            by (simp add: entry_def)
          have eR1: "\<And>j. j < Lng ?S \<Longrightarrow> entry ?R 1 j = entry ?S 1 j"
            by (simp add: entry_def)
          have Spos: "0 < Lng ?S" using seg_mono by (cases "Lng ?S = 0")
              (simp_all add: monoT_def zeroT_def le0_def leR_def)
          \<comment> \<open>\<open>?d0 = entry ?S 0 0\<close> is the row-0 minimum of the (mono) segment.\<close>
          have seg_T: "?S \<in> T_PS" using segPT by (simp add: PT_PS_def)
          have d0_left: "entry ?S 0 0 = ?d0"
            using entry_seg[where M="?N" and a="?m10" and b="?jN" and i=0 and j=0] Spos
            by (simp only: Lng_seg) simp
          have d0min: "\<And>j. j < Lng ?S \<Longrightarrow> ?d0 \<le> entry ?S 0 j"
          proof -
            fix j assume j: "j < Lng ?S"
            have "entry ?S 0 0 \<le> entry ?S 0 j" by (rule entry0_ge_min[OF seg_T seg_mono j])
            thus "?d0 \<le> entry ?S 0 j" using d0_left by simp
          qed
          have nr0eq: "le0 ?R 0 (Lng ?S - 1) = le0 ?S 0 (Lng ?S - 1)"
          proof -
            have nx: "nextrel0 ?R = nextrel0 ?S"
            proof (intro ext)
              fix a b
              show "nextrel0 ?R a b = nextrel0 ?S a b"
              proof (cases "a < Lng ?S \<and> b < Lng ?S")
                case True
                hence aS: "a < Lng ?S" and bS: "b < Lng ?S" by auto
                have U: "(\<forall>j. a < j \<and> j < b \<longrightarrow> entry ?R 0 b \<le> entry ?R 0 j)
                       = (\<forall>j. a < j \<and> j < b \<longrightarrow> entry ?S 0 b \<le> entry ?S 0 j)"
                proof (rule all_cong1)
                  fix j
                  show "(a < j \<and> j < b \<longrightarrow> entry ?R 0 b \<le> entry ?R 0 j)
                      = (a < j \<and> j < b \<longrightarrow> entry ?S 0 b \<le> entry ?S 0 j)"
                  proof (cases "a < j \<and> j < b")
                    case True
                    hence jS: "j < Lng ?S" using bS by linarith
                    have le_iff: "(entry ?R 0 b \<le> entry ?R 0 j) = (entry ?S 0 b \<le> entry ?S 0 j)"
                      using eR0[OF jS] eR0[OF bS] d0min[OF jS] d0min[OF bS] by linarith
                    show ?thesis using le_iff by blast
                  next
                    case False thus ?thesis by blast
                  qed
                qed
                have lt: "(entry ?R 0 a < entry ?R 0 b) = (entry ?S 0 a < entry ?S 0 b)"
                  using eR0[OF aS] eR0[OF bS] d0min[OF aS] d0min[OF bS] by linarith
                show ?thesis
                  unfolding nextrel0_def using LSR lt U by (simp add: LSR)
              next
                case False thus ?thesis by (auto simp: nextrel0_def LSR)
              qed
            qed
            show ?thesis unfolding le0_def by (simp only: nx LSR)
          qed
          have leRR: "le0 ?R 0 (Lng ?R - 1)"
          proof -
            have "le0 ?S 0 (Lng ?S - 1)" using seg_mono by (simp add: monoT_def leR_def)
            thus ?thesis using nr0eq LSR by simp
          qed
          have nzR: "\<not> zeroT ?R"
          proof (cases "Lng ?S = 1")
            case True
            have e1: "entry ?R 1 0 = entry ?S 1 0" using eR1 Spos by simp
            have "entry ?S 1 0 \<noteq> 0" using seg_mono True by (simp add: monoT_def zeroT_def)
            hence "entry ?R 1 0 \<noteq> 0" using e1 by simp
            thus ?thesis using LSR True by (simp add: zeroT_def)
          next
            case False
            hence "Lng ?R \<noteq> 1" using LSR by simp
            thus ?thesis by (simp add: zeroT_def)
          qed
          have "monoT ?R" using nzR leRR by (simp add: monoT_def leR_def)
          thus ?thesis using segeq by simp
        qed
      qed
    qed
  qed
  thus ?thesis using MT0 M by (simp add: PT_PS_def)
qed

end

theory Frontier_6_042
  imports Support_6_025
begin

subsection \<open>§6.5 TAIL: branch-tail row-0 values of \<open>Red (coreReduce M)\<close> exceed \<open>m\<^sub>1\<^sub>0\<close>\<close>

text \<open>Variable-length concat block access: the \<open>J\<close>-th block of \<open>concat Q\<close>, at local
  offset \<open>loc\<close>, sits at global index \<open>(\<Sum>\<^bsub>K<J\<^esub> Lng Q\<^sub>K) + loc\<close>.\<close>

lemma nth_concat_block:
  assumes JL: "J < length Q" and loc: "loc < length (Q ! J)"
  shows "concat Q ! (sum_list (map length (take J Q)) + loc) = (Q ! J) ! loc"
proof -
  let ?s = "sum_list (map length (take J Q))"
  have blk: "Q ! J = take (length (Q ! J)) (drop ?s (concat Q))"
    by (rule idxsum_concat_block[OF JL])
  \<comment> \<open>\<open>?s + loc < length (concat Q)\<close> since the block lies inside the concat.\<close>
  have lc: "length (concat Q) = sum_list (map length Q)" by (simp add: length_concat)
  have suc: "sum_list (map length (take (Suc J) Q)) = ?s + length (Q ! J)"
    using JL by (simp add: take_Suc_conv_app_nth)
  have mono_take: "sum_list (map length (take (Suc J) Q))
                    \<le> sum_list (map length (take (length Q) Q))"
    using JL by (intro idxsum_sum_take_mono) simp
  have inb: "?s + length (Q ! J) \<le> length (concat Q)"
    using suc lc mono_take by simp
  have locb: "?s + loc < length (concat Q)" using inb loc by linarith
  have "(Q ! J) ! loc = take (length (Q ! J)) (drop ?s (concat Q)) ! loc"
    using blk by simp
  also have "\<dots> = drop ?s (concat Q) ! loc" using loc by simp
  also have "\<dots> = concat Q ! (?s + loc)"
    by (rule nth_drop) (use locb in simp)
  finally show ?thesis by simp
qed

text \<open>Guarded row-1/row-0 leftend bound of \<open>Red\<close>.  When the input already has its
  row-1 left end below (or equal to) its row-0 left end, the \<open>Red\<close> output's row-0
  left end stays at least as large as the input's row-1 left end.  Proved by
  @{const Red}'s well-founded induction; crucially the dead branch \<^bold>\<open>[20]\<close>
  (\<open>Red M = M\<close>) is discharged \<^emph>\<open>directly from the guard\<close> (\<open>entry M 1 0 \<le> entry M 0 0\<close>),
  so this lemma is \<^bold>\<open>not\<close> circular with the dead-branch-unreachability proposition
  \<open>p_6_5_monoT_Red\<close>.  In the productive branches the output left end equals
  \<open>entry M 1 0\<close> (core / shift / m10>0 productive, via @{thm [source] m_6_6_Red_leftend_1}),
  except the core-trunk where it is \<open>m\<^sub>1\<^sub>0 = 0\<close>.  Empirically TRUE 4920/4920.\<close>

lemma Red_leftend_ge_row1:
  assumes MT: "M \<in> T_PS" and guard: "entry M 1 0 \<le> entry M 0 0"
  shows "entry M 1 0 \<le> entry (Red M) 0 0"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have "M \<in> T_PS \<longrightarrow> entry M 1 0 \<le> entry M 0 0 \<longrightarrow> entry M 1 0 \<le> entry (Red M) 0 0"
    using domM
  proof (induction M rule: Red.pinduct)
    case (1 M)
    note dom    = 1(1)
    note IH_mu  = 1(2)
    note IH_nc3 = 1(4)
    show ?case
    proof (rule impI, rule impI)
      assume MT': "M \<in> T_PS" and g: "entry M 1 0 \<le> entry M 0 0"
      have Mne: "M \<noteq> []" using MT' by (simp add: T_PS_def)
      have LMpos: "0 < Lng M" using Mne by (cases M) auto
      show "entry M 1 0 \<le> entry (Red M) 0 0"
      proof (cases "zeroT M")
        case True
        have rM: "Red M = [(0, 0)]" using Red.psimps[OF dom] True by simp
        have "entry M 1 0 = 0" using True by (simp add: zeroT_def)
        thus ?thesis by (simp add: rM entry_def)
      next
        case nz: False
        show ?thesis
        proof (cases "multiT M")
          case True
          have rM: "Red M = concat (map Red (P M))"
            using Red.psimps[OF dom] nz True by simp
          have ne_PM: "P M \<noteq> []" by (rule P_nonempty)
          have PM0_in: "P M ! 0 \<in> set (P M)" using ne_PM by (cases "P M") auto
          have PM0_T: "P M ! 0 \<in> T_PS"
            using P_blocks_nonempty[OF Mne] PM0_in by (auto simp: T_PS_def)
          have PM0_JL: "0 < length (P M)" using ne_PM by (cases "P M") simp_all
          have PM0_len_pos: "0 < Lng (P M ! 0)"
            by (rule idxsum_P_component_nonempty[OF MT' PM0_JL])
          have idx0: "IdxSum (P M) ! 0 = 0" by (simp add: idxsum_nth)
          \<comment> \<open>First block's two leftends agree with \<open>M\<close>'s.\<close>
          have Jle: "(0::nat) \<le> Lng (P M) - 1" using ne_PM by (cases "P M") simp_all
          have PM0_seg: "P M ! 0 = seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1)"
            using m_6_4_P_IdxSum[OF MT' Jle] by simp
          have lp: "0 < Lng (seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1))"
            using PM0_len_pos PM0_seg by simp
          have e1_PM0: "entry (P M ! 0) 1 0 = entry M 1 0"
          proof -
            have "entry (P M ! 0) 1 0
                 = entry (seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1)) 1 0"
              using PM0_seg by simp
            also have "\<dots> = entry M 1 (IdxSum (P M) ! 0 + 0)" by (rule entry_seg[OF lp])
            finally show ?thesis by (simp add: idx0)
          qed
          have e0_PM0: "entry (P M ! 0) 0 0 = entry M 0 0"
          proof -
            have "entry (P M ! 0) 0 0
                 = entry (seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1)) 0 0"
              using PM0_seg by simp
            also have "\<dots> = entry M 0 (IdxSum (P M) ! 0 + 0)" by (rule entry_seg[OF lp])
            finally show ?thesis by (simp add: idx0)
          qed
          have g0: "entry (P M ! 0) 1 0 \<le> entry (P M ! 0) 0 0"
            using g e1_PM0 e0_PM0 by simp
          have IH': "entry (P M ! 0) 1 0 \<le> entry (Red (P M ! 0)) 0 0"
            using IH_mu[OF nz True PM0_in] PM0_T g0 by blast
          \<comment> \<open>The \<open>Red\<close> of the first block is the head block of \<open>concat\<close>.\<close>
          have rPM0_ne: "Red (P M ! 0) \<noteq> []"
          proof -
            have "Lng (Red (P M ! 0)) = Lng (P M ! 0)" by (rule m_6_5_Lng_Red[OF PM0_T])
            thus ?thesis using PM0_len_pos by (cases "Red (P M ! 0)") auto
          qed
          have concat_nth0: "concat (map Red (P M)) ! 0 = Red (P M ! 0) ! 0"
          proof -
            have split: "P M = P M ! 0 # tl (P M)" using ne_PM by (cases "P M") auto
            have "concat (map Red (P M)) = Red (P M ! 0) @ concat (map Red (tl (P M)))"
              by (subst split) simp
            thus ?thesis using rPM0_ne by (simp add: nth_append)
          qed
          have "entry M 1 0 = entry (P M ! 0) 1 0" using e1_PM0 ..
          also have "\<dots> \<le> entry (Red (P M ! 0)) 0 0" by (rule IH')
          also have "\<dots> = entry (concat (map Red (P M))) 0 0"
            by (simp add: entry_def concat_nth0)
          also have "\<dots> = entry (Red M) 0 0" by (simp add: rM)
          finally show ?thesis .
        next
          case nmu: False
          have mono: "monoT M" using nz nmu by (simp add: multiT_def)
          let ?j1  = "Lng M - 1"
          let ?j1' = "TrMax M"
          let ?m00 = "entry M 0 0"
          let ?m10 = "entry M 1 0"
          show ?thesis
          proof (cases "?m00 = 0 \<and> ?m10 = 0")
            case core: True
            hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
            \<comment> \<open>Both core sub-cases give \<open>entry (Red M) 0 0 = 0 \<ge> 0 = m10\<close>.\<close>
            show ?thesis
            proof (cases "?j1' = ?j1")
              case True
              have rM: "Red M = diagSeq ?m10 (?m10 + ?j1)"
                using Red.psimps[OF dom] nz nmu c0 c1 True by (simp add: Let_def)
              have "entry (Red M) 0 0 = ?m10 + 0"
                using rM entry_diagSeq[where a="?m10" and b="?m10 + ?j1" and j=0 and i=0]
                by (simp add: LMpos)
              thus ?thesis using c1 by simp
            next
              case tne: False
              let ?tail = "concat (map (\<lambda>J.
                        (IncrFirst ^^ (Joints M ! J + 1
                            - (if entry (Br M ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
                          (Red ((entry M 0 0 + Joints M ! J + 1,
                                 entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                # tl (Br M ! J))))
                      [0..<Lng (Br M)])"
              have rM: "Red M = diagSeq 0 ?j1' @ ?tail"
                using Red.psimps[OF dom] nz nmu c0 c1 tne by (simp add: Let_def)
              have "entry (Red M) 0 0 = 0"
                using rM by (simp add: entry_diagSeq_append_lo)
              thus ?thesis using c1 by simp
            qed
          next
            case nc: False
            show ?thesis
            proof (cases "?m10 = 0")
              case True
              let ?shift = "map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc ?j1]"
              have rM: "Red M = Red ?shift"
                using Red.psimps[OF dom] nz nmu nc True by (simp add: Let_def)
              have shift_T: "?shift \<in> T_PS" by (simp add: T_PS_def)
              have e0_sh: "entry ?shift 0 0 = 0" using LMpos by (simp add: entry_def)
              have e1_sh: "entry ?shift 1 0 = entry M 1 0" using LMpos by (simp add: entry_def)
              have g_sh: "entry ?shift 1 0 \<le> entry ?shift 0 0"
                using e0_sh e1_sh True by simp
              have IH': "entry ?shift 1 0 \<le> entry (Red ?shift) 0 0"
                using IH_nc3[OF nz nmu refl refl refl refl nc True] shift_T g_sh by blast
              show ?thesis using IH' rM e1_sh by simp
            next
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
              show ?thesis
              proof (cases "?m10 \<le> ?jN \<and> seg ?N ?m10 ?jN \<in> PT_PS")
                case else_nc: False
                \<comment> \<open>Dead branch [20]: \<open>Red M = M\<close>; closed by the guard.\<close>
                have rM_else: "Red M = M"
                proof -
                  have step1: "(let N = ?N; jN = ?jN in
                                 if ?m10 \<le> jN \<and> seg N ?m10 jN \<in> PT_PS
                                 then map (\<lambda>j. (entry N 0 j - entry N 0 ?m10 + entry N 1 ?m10,
                                                entry N 1 j)) [?m10..<Suc jN]
                                 else M) = M"
                    unfolding Let_def by (rule if_not_P[OF else_nc])
                  show ?thesis using rM step1 by simp
                qed
                show ?thesis using g rM_else by simp
              next
                case then_case: True
                have m10_le: "?m10 \<le> ?jN" using then_case by simp
                have rM': "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10
                                              + entry ?N 1 ?m10, entry ?N 1 j))
                                       [?m10..<Suc ?jN]"
                  using rM then_case by (simp add: Let_def del: upt_Suc)
                have len0: "0 < length [?m10..<Suc ?jN]" using m10_le by (simp del: upt_Suc)
                have idx0: "[?m10..<Suc ?jN] ! 0 = ?m10"
                  using m10_le by (simp add: nth_upt del: upt_Suc)
                \<comment> \<open>Output row-0 left end = \<open>entry N 1 m10\<close> = \<open>entry (Red M) 1 0\<close> = \<open>m10\<close>.\<close>
                have e0_rM: "entry (Red M) 0 0 = entry ?N 1 ?m10"
                proof -
                  have "(Red M) ! 0 = (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                            entry ?N 1 j)) ?m10"
                    using rM' len0 idx0 by (simp add: nth_map del: upt_Suc)
                  thus ?thesis unfolding entry_def by simp
                qed
                have e1_rM: "entry (Red M) 1 0 = entry ?N 1 ?m10"
                proof -
                  have "(Red M) ! 0 = (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                            entry ?N 1 j)) ?m10"
                    using rM' len0 idx0 by (simp add: nth_map del: upt_Suc)
                  thus ?thesis unfolding entry_def by simp
                qed
                have linv: "entry (Red M) 1 0 = entry M 1 0" by (rule m_6_6_Red_leftend_1[OF MT'])
                show ?thesis using e0_rM e1_rM linv by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using MT guard by blast
qed

text \<open>Sub-lemma (\<S>6.4 part of the TAIL route).  For \<open>B = coreReduce M\<close> with
  \<open>m\<^sub>1\<^sub>0 = entry M 1 0 > 0\<close>, every joint sits at or above the length-\<open>m\<^sub>1\<^sub>0\<close>
  diagonal prefix: \<open>m\<^sub>1\<^sub>0 \<le> Joints B ! J\<close>.

  Proof.  \<open>B = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ IncrFirst\<^bsup>m\<^sub>1\<^sub>0\<^esup> M\<close> has row-0 value \<open>= p\<close> on every
  prefix index \<open>p < m\<^sub>1\<^sub>0\<close> (@{thm [source] entry_diagSeq_append_lo}), and
  \<open>TrMax B \<ge> m\<^sub>1\<^sub>0\<close> (@{thm [source] TrMax_diagSeq_append_ge}).  The \<open>J\<close>-th first node
  \<open>f = FirstNodes B ! J\<close> sits strictly above the trunk (\<open>f > TrMax B \<ge> m\<^sub>1\<^sub>0\<close>), so
  position \<open>m\<^sub>1\<^sub>0\<close> lies strictly between any putative parent \<open>< m\<^sub>1\<^sub>0\<close> and \<open>f\<close>.  But
  \<open>entry B 0 m\<^sub>1\<^sub>0 = entry M 0 0 + m\<^sub>1\<^sub>0 < entry M 0 (f - m\<^sub>1\<^sub>0) + m\<^sub>1\<^sub>0 = entry B 0 f\<close>
  (strict by @{thm [source] monoT_row0_min}, since \<open>f - m\<^sub>1\<^sub>0 \<ge> 1\<close>), so position
  \<open>m\<^sub>1\<^sub>0\<close> is a strictly-smaller-valued index below \<open>f\<close>; as the row-0 parent is the
  \<^emph>\<open>largest\<close> such (@{thm [source] nextR0_largest_below}), \<open>Joints B ! J \<ge> m\<^sub>1\<^sub>0\<close>.
  Empirically TRUE 1299/1299 (rank4) + 9291/9291 (rank5 exhaustive).\<close>

lemma joints_coreReduce_ge_m10:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and m10pos: "0 < entry M 1 0"
  defines "B \<equiv> diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M"
  assumes JBr: "J < Lng (Br B)"
  shows "entry M 1 0 \<le> Joints B ! J"
proof -
  let ?m = "entry M 1 0"
  let ?rest = "(IncrFirst ^^ ?m) M"
  have L0: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have lenr: "Lng ?rest = Lng M" by simp
  have rest_ne: "?rest \<noteq> []" using L0 lenr by (metis length_greater_0_conv)
  have Bdef: "B = diagSeq 0 (?m - 1) @ ?rest" using B_def by simp
  have BT: "B \<in> T_PS" using rest_ne Bdef by (simp add: T_PS_def)
  \<comment> \<open>\<open>B\<close> is core mono = in \<open>PT_PS\<close>.\<close>
  have BmonoT: "monoT B"
  proof -
    have cr: "coreReduce M = B" using m10pos Bdef by (simp add: coreReduce_def)
    show ?thesis using coreReduce_monoT_m10_pos[OF MT mono m10pos] cr by simp
  qed
  have BPT: "B \<in> PT_PS" using BT BmonoT by (simp add: PT_PS_def)
  \<comment> \<open>row-0 values of \<open>?rest\<close> are \<open>\<ge> ?m\<close>: \<open>entry ?rest 0 0 = entry M 0 0 + ?m\<close>.\<close>
  have er0: "?m - 1 < entry ?rest 0 0"
  proof -
    have "entry ?rest 0 0 = entry M 0 0 + ?m" by (rule entry_funpow_IncrFirst0[OF L0])
    thus ?thesis using m10pos by simp
  qed
  have er1: "?m - 1 < entry ?rest 1 0"
  proof -
    have "entry ?rest 1 0 = entry M 1 0" by (rule entry_funpow_IncrFirst1[OF L0])
    thus ?thesis using m10pos by simp
  qed
  have TrMax_ge: "?m \<le> TrMax B"
    using TrMax_diagSeq_append_ge[OF rest_ne er0 er1] Bdef by simp
  \<comment> \<open>The first node \<open>?f\<close> and its row-0 parent \<open>= Joints B ! J\<close>.\<close>
  let ?f = "FirstNodes B ! J"
  have fnTr: "Joints B ! J \<le> TrMax B \<and> TrMax B < ?f"
    by (rule m_6_4_FirstNodes_TrMax_Joints[OF BPT JBr])
  have ftr: "TrMax B < ?f" using fnTr by simp
  have nxJ: "nextR B 0 (Joints B ! J) ?f" by (rule Joints_parent_nextR[OF BPT JBr])
  \<comment> \<open>\<open>?f > ?m\<close>, so \<open>?f - ?m \<ge> 1\<close>, and \<open>?f < Lng B = ?m + Lng M\<close>.\<close>
  have fm: "?m < ?f" using ftr TrMax_ge by linarith
  have LB: "Lng B = ?m + Lng M" using Bdef m10pos by (simp add: Lng_funpow_IncrFirst)
  have fL: "?f < Lng B" using nxJ by (simp add: nextR_def nextrel0_def)
  have fmlt: "?f - ?m < Lng M" using fL LB fm by linarith
  have fmpos: "0 < ?f - ?m" using fm by linarith
  \<comment> \<open>row-0 of \<open>B\<close> at \<open>?m\<close> and at \<open>?f\<close> (both \<ge> ?m, both via the \<open>?rest\<close> region).\<close>
  have lendiag: "length (diagSeq 0 (?m - 1)) = ?m" using m10pos by (simp add: diagSeq_def)
  \<comment> \<open>row-0 of \<open>B\<close> at any index \<open>?m + d\<close> with \<open>d < Lng M\<close> reads \<open>entry M 0 d + ?m\<close>.\<close>
  have eB_rest: "\<And>d. d < Lng M \<Longrightarrow> entry B 0 (?m + d) = entry M 0 d + ?m"
  proof -
    fix d assume d: "d < Lng M"
    have idx: "?m + d \<ge> length (diagSeq 0 (?m - 1))" using lendiag by simp
    have "B ! (?m + d) = ?rest ! (?m + d - length (diagSeq 0 (?m - 1)))"
      using Bdef idx by (simp add: nth_append)
    hence "entry B 0 (?m + d) = entry ?rest 0 d" using lendiag by (simp add: entry_def)
    also have "\<dots> = entry M 0 d + ?m" using entry_funpow_IncrFirst0[OF d] by simp
    finally show "entry B 0 (?m + d) = entry M 0 d + ?m" .
  qed
  have eBm: "entry B 0 ?m = entry M 0 0 + ?m"
    using eB_rest[OF L0] by simp
  have eBf: "entry B 0 ?f = entry M 0 (?f - ?m) + ?m"
  proof -
    have "?f = ?m + (?f - ?m)" using fm by simp
    hence "entry B 0 ?f = entry B 0 (?m + (?f - ?m))" by simp
    also have "\<dots> = entry M 0 (?f - ?m) + ?m" using eB_rest[OF fmlt] by simp
    finally show ?thesis .
  qed
  \<comment> \<open>Strict: \<open>entry B 0 ?m < entry B 0 ?f\<close> by row-0 strict-min of \<open>M\<close> at \<open>?f - ?m \<ge> 1\<close>.\<close>
  have strict_M: "entry M 0 0 < entry M 0 (?f - ?m)"
    by (rule monoT_row0_min[OF MT mono fmpos fmlt])
  have eBlt: "entry B 0 ?m < entry B 0 ?f" using eBm eBf strict_M by simp
  \<comment> \<open>So position \<open>?m\<close> is a strictly-smaller-valued index below \<open>?f\<close>; parent \<ge> ?m.\<close>
  show ?thesis by (rule nextR0_largest_below[OF nxJ fm eBlt])
qed

text \<open>\<open>npJ M J \<le> Joints M ! J + 1\<close>: the row-1 parent \<open>npJ - 1\<close> of a first node is at
  most its row-0 parent \<open>Joints\<close>.  When \<open>(Br M ! J)\<^bsub>1,0\<^esub> = 0\<close> we have \<open>npJ = 0\<close>.
  Otherwise the first node \<open>f\<close> has a (unique) row-1 parent \<open>p\<^sub>1\<close>: it exists by
  @{thm [source] m_5_1_parent_exists_2} (root 0 has smaller row-1 value and is a
  row-0 ancestor of \<open>f\<close> by monoT), and is unique by @{thm [source] nextR1_unique}.
  Since \<open>nextrel1\<close> requires \<open>le0\<close>, \<open>p\<^sub>1\<close> is a row-0 ancestor of \<open>f\<close>, so
  \<open>entry M 0 p\<^sub>1 < entry M 0 f\<close> and \<open>p\<^sub>1 \<le> Joints M ! J\<close>
  (@{thm [source] nextR0_largest_below}).  Empirically TRUE 1299/1299.\<close>

lemma npJ_le_Joints_Suc:
  assumes M: "M \<in> PT_PS" and core1: "entry M 1 0 = 0" and JBr: "J < Lng (Br M)"
  shows "npJ M J \<le> Joints M ! J + 1"
proof (cases "entry (Br M ! J) 1 0 = 0")
  case True
  thus ?thesis by (simp add: npJ_def)
next
  case nzbr: False
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have monoM: "monoT M" using M by (simp add: PT_PS_def)
  let ?f = "FirstNodes M ! J"
  \<comment> \<open>\<open>?f\<close> is a strict-above-trunk index, hence \<open>0 < ?f < Lng M\<close> and \<open>0 < entry M 1 ?f\<close>.\<close>
  have fnTr: "Joints M ! J \<le> TrMax M \<and> TrMax M < ?f"
    by (rule m_6_4_FirstNodes_TrMax_Joints[OF M JBr])
  have nxJ: "nextR M 0 (Joints M ! J) ?f" by (rule Joints_parent_nextR[OF M JBr])
  have fL: "?f < Lng M" using nxJ by (simp add: nextR_def nextrel0_def)
  have fpos: "0 < ?f" using fnTr by linarith
  have eBf1: "entry M 1 ?f = entry (Br M ! J) 1 0"
    by (rule entry_FirstNodes_eq_component_gen[OF M JBr])
  have f1pos: "0 < entry M 1 ?f" using eBf1 nzbr by simp
  \<comment> \<open>root 0 has row-1 value 0 (core), strictly below \<open>entry M 1 ?f\<close>.\<close>
  have e10_lt: "entry M 1 0 < entry M 1 ?f" using core1 f1pos by simp
  \<comment> \<open>root 0 is a row-0 ancestor of \<open>?f\<close> (monoT).\<close>
  have le00f: "leR M 0 0 ?f"
  proof -
    have root: "leR M 0 0 (Lng M - 1)" using monoM by (simp add: monoT_def)
    have fle: "?f \<le> Lng M - 1" using fL by simp
    show ?thesis by (rule m_5_1_ancestor_tree_1[OF MT root _ fle]) simp
  qed
  \<comment> \<open>Existence and uniqueness of the row-1 parent \<open>p\<^sub>1\<close>.\<close>
  obtain p1 where p1: "0 \<le> p1" "p1 < ?f" "nextR M 1 p1 ?f"
    using m_5_1_parent_exists_2[OF MT fpos fL e10_lt le00f] by blast
  have ex1: "\<exists>!j. nextR M 1 j ?f"
    using p1(3) nextR1_unique by blast
  have the_p1: "(THE j. nextR M 1 j ?f) = p1"
    using p1(3) by (rule the1_equality[OF ex1])
  have np: "npJ M J = Suc p1" using nzbr the_p1 by (simp add: npJ_def)
  \<comment> \<open>\<open>p\<^sub>1\<close> is a row-0 ancestor of \<open>?f\<close> (\<open>nextrel1\<close> requires \<open>le0\<close>), so \<open>p\<^sub>1 \<le> Joints\<close>.\<close>
  have le0p1f: "leR M 0 p1 ?f"
    using p1(3) by (simp add: nextR_def nextrel1_def leR_def)
  have e0_p1f: "entry M 0 p1 < entry M 0 ?f"
    by (rule m_5_1_ancestor_basic_1[OF MT p1(2) order.refl le0p1f])
  have p1_le: "p1 \<le> Joints M ! J"
    by (rule nextR0_largest_below[OF nxJ p1(2) e0_p1f])
  show ?thesis using np p1_le by simp
qed

text \<open>m: \<S>6.5 TAIL main lemma \<open>redB_tail_row0_above_anchor\<close>.

  For \<open>B = coreReduce M\<close> with \<open>m\<^sub>1\<^sub>0 = entry M 1 0 > 0\<close>, every \<^bold>\<open>branch-tail\<close> index
  of \<open>Red B\<close> (every index strictly above the trunk \<open>diagSeq 0 (TrMax B)\<close>) carries a
  row-0 value strictly exceeding \<open>m\<^sub>1\<^sub>0\<close>:
  \[ \forall j.\ \textrm{TrMax}\,B < j < \textrm{Lng}(\textrm{Red}\,B) \;\Longrightarrow\;
       m_{10} < (\textrm{Red}\,B)_{0,j}. \]

  Route (all non-circular green bricks; the dead branch \<^bold>\<open>[20]\<close> is handled by
  @{thm [source] Red_leftend_ge_row1} via the guard, not by the unproven
  dead-branch-unreachability \<open>p_6_5_monoT_Red\<close>):
  \<^item> \<open>B\<close> is core mono, so \<open>Red B = diagSeq 0 (TrMax B) @ concat (branch blocks)\<close>
    (or, in the core-trunk sub-case, \<open>TrMax B = Lng B - 1\<close> and there is no tail
    index — vacuous).
  \<^item> A tail index \<open>j\<close> falls in a block \<open>J\<close> (@{thm [source] idxsum_locate}); the block is
    \<open>IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red (N\<^sub>J B J))\<close> with \<open>e\<^sub>J = Joints B ! J + 1 - npJ B J\<close>, so
    \<open>(Red B)\<^bsub>0,j\<^esub> = (Red (N\<^sub>J B J))\<^bsub>0,loc\<^esub> + e\<^sub>J\<close>
    (@{thm [source] nth_concat_block}, @{thm [source] entry_funpow_IncrFirst0}).
  \<^item> @{thm [source] m_6_5_Red_leftend_row0_min} on \<open>Red (N\<^sub>J B J)\<close> gives
    \<open>(Red N\<^sub>J)\<^bsub>0,loc\<^esub> \<ge> (Red N\<^sub>J)\<^bsub>0,0\<^esub>\<close>, and @{thm [source] Red_leftend_ge_row1} gives
    \<open>(Red N\<^sub>J)\<^bsub>0,0\<^esub> \<ge> (N\<^sub>J)\<^bsub>1,0\<^esub> = npJ B J\<close> (guard \<open>npJ \<le> Joints+1\<close> by
    @{thm [source] npJ_le_Joints_Suc}).  Hence
    \<open>(Red B)\<^bsub>0,j\<^esub> \<ge> e\<^sub>J + npJ \<ge> Joints B ! J + 1 \<ge> m\<^sub>1\<^sub>0 + 1 > m\<^sub>1\<^sub>0\<close>
    (@{thm [source] joints_coreReduce_ge_m10}; the last \<open>\<ge>\<close> is the nat identity
    \<open>(a - b) + b \<ge> a\<close>).
  Empirically TRUE 591/591 + 1557/1557 (rank4) + 12114/12114 (rank5 exhaustive).\<close>

lemma redB_tail_row0_above_anchor:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and m10pos: "0 < entry M 1 0"
  defines "B \<equiv> diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M"
  shows "\<forall>j. TrMax B < j \<longrightarrow> j < Lng (Red B) \<longrightarrow> entry M 1 0 < entry (Red B) 0 j"
proof -
  let ?m = "entry M 1 0"
  let ?rest = "(IncrFirst ^^ ?m) M"
  have L0: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have rest_ne: "?rest \<noteq> []" using L0 by (metis Lng_funpow_IncrFirst length_greater_0_conv)
  have Bdef: "B = diagSeq 0 (?m - 1) @ ?rest" using B_def by simp
  have BT: "B \<in> T_PS" using rest_ne Bdef by (simp add: T_PS_def)
  have Bne: "B \<noteq> []" using BT by (simp add: T_PS_def)
  have cr: "coreReduce M = B" using m10pos Bdef by (simp add: coreReduce_def)
  have BmonoT: "monoT B" using coreReduce_monoT_m10_pos[OF MT mono m10pos] cr by simp
  have BPT: "B \<in> PT_PS" using BT BmonoT by (simp add: PT_PS_def)
  have Bnz: "\<not> zeroT B" using BmonoT by (simp add: monoT_def)
  have Bnmu: "\<not> multiT B" using BmonoT by (simp add: multiT_def)
  have Bc0: "entry B 0 0 = 0" using m10pos by (simp add: Bdef entry_diagSeq_append_lo)
  have Bc1: "entry B 1 0 = 0" using m10pos by (simp add: Bdef entry_diagSeq_append_lo)
  have domB: "Red_dom B" by (rule m_6_5_Red_welldef[OF BT])
  let ?t = "TrMax B"
  show ?thesis
  proof (cases "?t = Lng B - 1")
    \<comment> \<open>Core trunk: \<open>Red B = diagSeq 0 (Lng B - 1)\<close>, length \<open>Lng B\<close>, no tail index.\<close>
    case True
    have LrB: "Lng (Red B) = Lng B" using m_6_5_Lng_Red[OF BT] by simp
    show ?thesis
    proof (intro allI impI)
      fix j assume tj: "?t < j" and jL: "j < Lng (Red B)"
      have "j < Lng B" using jL LrB by simp
      hence False using tj True by simp
      thus "entry M 1 0 < entry (Red B) 0 j" ..
    qed
  next
    case tne: False
    \<comment> \<open>Core non-trunk: \<open>Red B = diagSeq 0 (TrMax B) @ concat Q\<close>.\<close>
    let ?blk = "\<lambda>J. (IncrFirst ^^ (Joints B ! J + 1
                  - (if entry (Br B ! J) 1 0 = 0 then 0
                     else Suc (THE j. nextR B 1 j (FirstNodes B ! J)))))
                (Red ((entry B 0 0 + Joints B ! J + 1,
                       entry B 1 0 + (if entry (Br B ! J) 1 0 = 0 then 0
                              else Suc (THE j. nextR B 1 j (FirstNodes B ! J))))
                      # tl (Br B ! J)))"
    let ?Q = "map ?blk [0..<Lng (Br B)]"
    have rB: "Red B = diagSeq 0 ?t @ concat ?Q"
      using Red.psimps[OF domB] Bnz Bnmu Bc0 Bc1 tne by (simp add: Let_def)
    \<comment> \<open>Block \<open>J\<close> = \<open>IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red (NJ B J))\<close>; its length is \<open>Lng (Br B ! J)\<close>.\<close>
    have blk_eq: "\<And>J. J < Lng (Br B) \<Longrightarrow>
        ?blk J = (IncrFirst ^^ (Joints B ! J + 1 - npJ B J)) (Red (NJ B J))"
    proof -
      fix J assume "J < Lng (Br B)"
      have "(entry B 0 0 + Joints B ! J + 1,
              entry B 1 0 + (if entry (Br B ! J) 1 0 = 0 then 0
                     else Suc (THE j. nextR B 1 j (FirstNodes B ! J)))) # tl (Br B ! J)
            = NJ B J"
        by (simp add: NJ_def npJ_def)
      moreover have "(if entry (Br B ! J) 1 0 = 0 then 0
                       else Suc (THE j. nextR B 1 j (FirstNodes B ! J))) = npJ B J"
        by (simp add: npJ_def)
      ultimately show "?blk J = (IncrFirst ^^ (Joints B ! J + 1 - npJ B J)) (Red (NJ B J))"
        by simp
    qed
    have Lblk: "\<And>J. J < Lng (Br B) \<Longrightarrow> Lng (?blk J) = Lng (Br B ! J)"
    proof -
      fix J assume J: "J < Lng (Br B)"
      have brJne: "Br B ! J \<noteq> []" by (rule Br_component_nonempty[OF BPT J])
      have NJTl: "NJ B J \<in> T_PS" using brJne by (simp add: NJ_def T_PS_def)
      have step1: "Lng (?blk J) = Lng (Red (NJ B J))"
        by (simp only: blk_eq[OF J] Lng_funpow_IncrFirst)
      have step2: "Lng (Red (NJ B J)) = Lng (NJ B J)" by (rule m_6_5_Lng_Red[OF NJTl])
      have step3: "Lng (NJ B J) = Lng (Br B ! J)" using brJne by (rule Lng_NJ)
      show "Lng (?blk J) = Lng (Br B ! J)" using step1 step2 step3 by simp
    qed
    \<comment> \<open>Total tail length and the diagonal prefix length.\<close>
    have LrB: "Lng (Red B) = Lng B" by (rule m_6_5_Lng_Red[OF BT])
    have lendiag: "length (diagSeq 0 ?t) = Suc ?t" by (simp add: diagSeq_def)
    have Ltail: "Lng (concat ?Q) = Lng B - Suc ?t"
    proof -
      have "Lng (Red B) = length (diagSeq 0 ?t) + Lng (concat ?Q)" by (simp add: rB)
      thus ?thesis using LrB lendiag by simp
    qed
    \<comment> \<open>Block-length sum bookkeeping: \<open>IdxSum ?Q ! (length ?Q) = Lng (concat ?Q)\<close>.\<close>
    have lenQ: "length ?Q = Lng (Br B)" by simp
    have idx_total: "IdxSum ?Q ! (length ?Q) = Lng (concat ?Q)"
    proof -
      have "IdxSum ?Q ! (length ?Q) = sum_list (map length (take (length ?Q) ?Q))"
        by (simp add: idxsum_nth)
      also have "\<dots> = sum_list (map length ?Q)" by simp
      also have "\<dots> = length (concat ?Q)" by (simp add: length_concat)
      finally show ?thesis .
    qed
    show ?thesis
    proof (intro allI impI)
      fix j assume tj: "?t < j" and jL: "j < Lng (Red B)"
      \<comment> \<open>Offset into the tail.\<close>
      let ?jp = "j - Suc ?t"
      have jge: "Suc ?t \<le> j" using tj by simp
      have jpL: "?jp < Lng (concat ?Q)"
        using jL LrB Ltail jge by linarith
      \<comment> \<open>\<open>entry (Red B) 0 j = entry (concat ?Q) 0 ?jp\<close>.\<close>
      have e_split: "entry (Red B) 0 j = entry (concat ?Q) 0 ?jp"
      proof -
        have "(Red B) ! j = (diagSeq 0 ?t @ concat ?Q) ! j" by (simp add: rB)
        also have "\<dots> = concat ?Q ! (j - length (diagSeq 0 ?t))"
          using jge lendiag by (simp add: nth_append)
        also have "\<dots> = concat ?Q ! ?jp" using lendiag by simp
        finally show ?thesis by (simp add: entry_def)
      qed
      \<comment> \<open>Locate the block \<open>J\<close> containing \<open>?jp\<close>.\<close>
      have jp_tot: "?jp < IdxSum ?Q ! (length ?Q)" using jpL idx_total by simp
      obtain J where J: "J < length ?Q" "IdxSum ?Q ! J \<le> ?jp"
                       "?jp < IdxSum ?Q ! (J + 1)"
        using idxsum_locate[OF jp_tot] by blast
      have JBr: "J < Lng (Br B)" using J(1) lenQ by simp
      let ?loc = "?jp - IdxSum ?Q ! J"
      have QJ_blk: "?Q ! J = ?blk J"
        using nth_map_upt[where f="?blk" and m=0 and n="Lng (Br B)" and i=J] JBr by simp
      have blkJ_len: "length (?Q ! J) = Lng (Br B ! J)"
        using QJ_blk Lblk[OF JBr] by simp
      have idxdiff: "IdxSum ?Q ! (J + 1) = IdxSum ?Q ! J + length (?Q ! J)"
        using J(1) by (rule idxsum_diff)
      have loc_lt: "?loc < length (?Q ! J)" using J(2,3) idxdiff by linarith
      \<comment> \<open>\<open>entry (concat ?Q) 0 ?jp = entry (?Q ! J) 0 ?loc\<close>.\<close>
      have sJ: "sum_list (map length (take J ?Q)) = IdxSum ?Q ! J"
        using J(1) by (simp add: idxsum_nth less_imp_le_nat)
      have jp_decomp: "?jp = IdxSum ?Q ! J + ?loc" using J(2) by simp
      have e_block: "entry (concat ?Q) 0 ?jp = entry (?Q ! J) 0 ?loc"
      proof -
        have "concat ?Q ! ?jp = concat ?Q ! (sum_list (map length (take J ?Q)) + ?loc)"
          using sJ jp_decomp by simp
        also have "\<dots> = (?Q ! J) ! ?loc"
          by (rule nth_concat_block[OF J(1) loc_lt])
        finally show ?thesis by (simp add: entry_def)
      qed
      \<comment> \<open>Block value = \<open>entry (Red (NJ B J)) 0 ?loc + e\<^sub>J\<close>.\<close>
      let ?eJ = "Joints B ! J + 1 - npJ B J"
      have QJ: "?Q ! J = (IncrFirst ^^ ?eJ) (Red (NJ B J))"
        using QJ_blk blk_eq[OF JBr] by simp
      have brJne: "Br B ! J \<noteq> []" by (rule Br_component_nonempty[OF BPT JBr])
      have NJT: "NJ B J \<in> T_PS" using brJne by (simp add: NJ_def T_PS_def)
      have LredNJ: "Lng (Red (NJ B J)) = Lng (NJ B J)" by (rule m_6_5_Lng_Red[OF NJT])
      have loc_ltN: "?loc < Lng (Red (NJ B J))"
      proof -
        have "?loc < Lng (Br B ! J)" using loc_lt blkJ_len by simp
        also have "\<dots> = Lng (NJ B J)" using brJne by (simp add: Lng_NJ)
        also have "\<dots> = Lng (Red (NJ B J))" using LredNJ by simp
        finally show ?thesis .
      qed
      have e_QJ: "entry (?Q ! J) 0 ?loc = entry (Red (NJ B J)) 0 ?loc + ?eJ"
      proof -
        have "entry (?Q ! J) 0 ?loc = entry ((IncrFirst ^^ ?eJ) (Red (NJ B J))) 0 ?loc"
          using QJ by simp
        also have "\<dots> = entry (Red (NJ B J)) 0 ?loc + ?eJ"
          by (rule entry_funpow_IncrFirst0[OF loc_ltN])
        finally show ?thesis .
      qed
      \<comment> \<open>Leftend lower bound: \<open>entry (Red (NJ B J)) 0 ?loc \<ge> npJ B J\<close>.\<close>
      have NJzm: "zeroT (NJ B J) \<or> monoT (NJ B J)"
        using NJ_nonmulti[OF BPT Bc0 Bc1 JBr] by (simp add: multiT_def)
      have lm_NJ: "entry (Red (NJ B J)) 0 0 \<le> entry (Red (NJ B J)) 0 ?loc"
      proof (cases "zeroT (NJ B J)")
        case True
        \<comment> \<open>\<open>Red (NJ B J) = [(0,0)]\<close>, length 1, \<open>?loc = 0\<close>.\<close>
        have "Lng (Red (NJ B J)) = 1" using LredNJ True by (simp add: zeroT_def)
        hence "?loc = 0" using loc_ltN by simp
        thus ?thesis by simp
      next
        case False
        hence "monoT (NJ B J)" using NJzm by simp
        from m_6_5_Red_leftend_row0_min[OF NJT this] loc_ltN
        show ?thesis by blast
      qed
      \<comment> \<open>\<open>entry (Red (NJ B J)) 0 0 \<ge> entry (NJ B J) 1 0 = npJ B J\<close> (guard via \<open>npJ \<le> Joints+1\<close>).\<close>
      have guardNJ: "entry (NJ B J) 1 0 \<le> entry (NJ B J) 0 0"
      proof -
        have e0: "entry (NJ B J) 0 0 = Joints B ! J + 1"
          using entry_NJ_0_0[of B J] Bc0 by simp
        have e1: "entry (NJ B J) 1 0 = npJ B J"
          using entry_NJ_1_0[of B J] Bc1 by simp
        show ?thesis using e0 e1 npJ_le_Joints_Suc[OF BPT Bc1 JBr] by simp
      qed
      have root_NJ: "entry (NJ B J) 1 0 \<le> entry (Red (NJ B J)) 0 0"
        by (rule Red_leftend_ge_row1[OF NJT guardNJ])
      have npJ_eq: "entry (NJ B J) 1 0 = npJ B J"
        using entry_NJ_1_0[of B J] Bc1 by simp
      have leftend_ge: "npJ B J \<le> entry (Red (NJ B J)) 0 ?loc"
        using root_NJ npJ_eq lm_NJ by simp
      \<comment> \<open>Assemble: \<open>entry (Red B) 0 j \<ge> e\<^sub>J + npJ \<ge> Joints + 1 \<ge> m + 1 > m\<close>.\<close>
      have jt_ge: "?m \<le> Joints B ! J"
      proof -
        have "entry M 1 0 \<le> Joints (diagSeq 0 (entry M 1 0 - 1)
                                  @ (IncrFirst ^^ entry M 1 0) M) ! J"
          using JBr by (intro joints_coreReduce_ge_m10[OF MT mono m10pos]) (simp add: B_def)
        thus ?thesis by (simp add: B_def)
      qed
      have eRBj: "entry (Red B) 0 j = entry (Red (NJ B J)) 0 ?loc + ?eJ"
        using e_split e_block e_QJ by simp
      \<comment> \<open>Nat identity \<open>(a - b) + b \<ge> a\<close> with \<open>a = Joints+1\<close>, \<open>b = npJ\<close>.\<close>
      have nat_id: "Joints B ! J + 1 \<le> ?eJ + npJ B J" by simp
      have "Joints B ! J + 1 \<le> entry (Red (NJ B J)) 0 ?loc + ?eJ"
        using leftend_ge nat_id by linarith
      hence "Joints B ! J + 1 \<le> entry (Red B) 0 j" using eRBj by simp
      thus "entry M 1 0 < entry (Red B) 0 j" using jt_ge by linarith
    qed
  qed
qed


subsection \<open>CASCADE-A: dead-branch[20] unreachability (\<open>p_6_5_monoT_Red\<close>, m10>0)\<close>

text \<open>RESIDUAL (strict row-0 suffix-minimum from the diagonal anchor \<open>m10\<close>):
  for \<open>B = coreReduce M\<close> (\<open>M\<close> monoT, \<open>m10 = M\<^bsub>1,0\<^esub> > 0\<close>), the row-0 value of
  \<open>Red B\<close> at \<open>m10\<close> equals \<open>m10\<close> (it sits on the trunk diagonal), and every later
  index has a STRICTLY larger row-0 value.  Empirically TRUE 3354/0 (Lng\<le>5),
  600/0 (Lng\<le>4).  This is the row-0 forward BC0 fragment; \<open>m_5_1_parent_exists_3\<close>
  turns the strict suffix-min into the \<open>le0\<close> anchor edge \<open>m10 \<rightarrow> jN\<close>.\<close>

text \<open>\<open>m10 \<le> TrMax B\<close>: the diagonal prefix of \<open>B = coreReduce M\<close> has length
  \<open>m10\<close> and \<open>rest = IncrFirst\<^bsup>m10\<^esup> M\<close> starts strictly above the diagonal in both
  rows, so the trunk of \<open>B\<close> reaches at least \<open>m10\<close>.\<close>

lemma coreReduce_m10_le_TrMax:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "entry M 1 0 \<le> TrMax (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M)"
proof -
  let ?m10 = "entry M 1 0"
  let ?rest = "(IncrFirst ^^ ?m10) M"
  let ?k = "?m10 - 1"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LM: "0 < Lng M" using Mne by (cases M) auto
  have ne: "?rest \<noteq> []" using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
  have r0: "?k < entry ?rest 0 0"
  proof -
    have "entry ?rest 0 0 = entry M 0 0 + ?m10" by (rule entry_funpow_IncrFirst0[OF LM])
    thus ?thesis using pos by simp
  qed
  have r1: "?k < entry ?rest 1 0"
  proof -
    have "entry ?rest 1 0 = entry M 1 0" by (rule entry_funpow_IncrFirst1[OF LM])
    thus ?thesis using pos by simp
  qed
  have "Suc ?k \<le> TrMax (diagSeq 0 ?k @ ?rest)"
    by (rule TrMax_diagSeq_append_ge[OF ne r0 r1])
  thus ?thesis using pos by simp
qed

text \<open>The diagonal prefix of \<open>Red B\<close> (core monoT \<open>B = coreReduce M\<close>): for every
  \<open>j \<le> m10\<close>, both rows read \<open>j\<close>.  In particular the row-0/row-1 anchor values at
  \<open>m10\<close> are \<open>m10\<close>.  Proof: \<open>Red B\<close> opens (core-trunk or core-nontrunk) with a
  diagonal \<open>diagSeq 0 t\<close>, \<open>t \<ge> m10\<close>; @{thm [source] entry_diagSeq} /
  @{thm [source] entry_diagSeq_append_lo} read the prefix.\<close>

lemma redB_prefix_diag:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  defines "B \<equiv> diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M"
  shows "\<forall>(i::nat) j. (i = 0 \<or> i = 1) \<and> j \<le> entry M 1 0 \<longrightarrow> entry (Red B) i j = j"
proof -
  let ?m10 = "entry M 1 0"
  let ?B = "B"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
    using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
  have BT: "?B \<in> T_PS" unfolding B_def using funpow_ne by (simp add: T_PS_def)
  have domB: "Red_dom ?B" by (rule m_6_5_Red_welldef[OF BT])
  \<comment> \<open>B is core: entry00 = 0, entry10 = 0.\<close>
  have crB: "entry ?B 0 0 = 0 \<and> entry ?B 1 0 = 0"
  proof -
    have "coreReduce M = ?B" unfolding B_def using pos by (simp add: coreReduce_def)
    thus ?thesis using coreReduce_core[OF MT] by simp
  qed
  have c0: "entry ?B 0 0 = 0" and c1: "entry ?B 1 0 = 0" using crB by simp_all
  \<comment> \<open>B is monoT (coreReduce of mono is mono).\<close>
  have monoB: "monoT ?B"
    using coreReduce_monoT_m10_pos[OF MT mono pos] B_def pos by (simp add: coreReduce_def)
  have nzB: "\<not> zeroT ?B" using monoB by (simp add: monoT_def)
  have nmuB: "\<not> multiT ?B" using monoB by (simp add: multiT_def)
  \<comment> \<open>m10 \<le> TrMax B.\<close>
  have m10leTr: "?m10 \<le> TrMax ?B"
    using coreReduce_m10_le_TrMax[OF MT mono pos] B_def by simp
  let ?j1 = "Lng ?B - 1"
  let ?j1' = "TrMax ?B"
  show "\<forall>(i::nat) j. (i = 0 \<or> i = 1) \<and> j \<le> ?m10 \<longrightarrow> entry (Red ?B) i j = j"
  proof (cases "?j1' = ?j1")
    \<comment> \<open>core-trunk: Red B = diagSeq 0 (Lng B - 1).\<close>
    case True
    have rB: "Red ?B = diagSeq 0 (0 + ?j1)"
      using Red.psimps[OF domB] nzB nmuB c0 c1 True by (simp add: Let_def)
    have m10le1: "?m10 \<le> ?j1" using m10leTr True by simp
    show ?thesis
    proof (intro allI impI)
      fix i j :: nat assume H: "(i = 0 \<or> i = 1) \<and> j \<le> ?m10"
      hence jm: "j \<le> ?m10" by simp
      have jj1: "j \<le> 0 + ?j1" using jm m10le1 by simp
      have jlt: "j < Suc (0 + ?j1) - 0" using jj1 by simp
      have "entry (diagSeq 0 (0 + ?j1)) i j = 0 + j"
        using entry_diagSeq[where a=0 and b="0+?j1" and j=j and i=i] jlt by simp
      thus "entry (Red ?B) i j = j" using rB by simp
    qed
  next
    \<comment> \<open>core-nontrunk: Red B = diagSeq 0 (TrMax B) @ tail.\<close>
    case tne: False
    let ?tail = "concat (map (\<lambda>J.
              (IncrFirst ^^ (Joints ?B ! J + 1
                  - (if entry (Br ?B ! J) 1 0 = 0 then 0
                     else Suc (THE j. nextR ?B 1 j (FirstNodes ?B ! J)))))
                (Red ((entry ?B 0 0 + Joints ?B ! J + 1,
                       entry ?B 1 0 + (if entry (Br ?B ! J) 1 0 = 0 then 0
                              else Suc (THE j. nextR ?B 1 j (FirstNodes ?B ! J))))
                      # tl (Br ?B ! J))))
            [0..<Lng (Br ?B)])"
    have rB: "Red ?B = diagSeq 0 ?j1' @ ?tail"
      using Red.psimps[OF domB] nzB nmuB c0 c1 tne by (simp add: Let_def)
    show ?thesis
    proof (intro allI impI)
      fix i j :: nat assume H: "(i = 0 \<or> i = 1) \<and> j \<le> ?m10"
      hence jm: "j \<le> ?m10" by simp
      have jTr: "j \<le> ?j1'" using jm m10leTr by simp
      have "entry (diagSeq 0 ?j1' @ ?tail) i j = j"
        by (rule entry_diagSeq_append_lo[OF jTr])
      thus "entry (Red ?B) i j = j" using rB by simp
    qed
  qed
qed

text \<open>RESIDUAL (strict row-0 suffix-minimum past the diagonal anchor \<open>m10\<close>):
  for \<open>B = coreReduce M\<close>, every index \<open>j > m10\<close> has row-0 value STRICTLY above
  \<open>m10\<close>.  Empirically TRUE 3354/0 (Lng\<le>5), 600/0 (Lng\<le>4).  This is the genuine
  BC0 core: in the core-nontrunk decomposition \<open>Red B = diagSeq 0 (TrMax B) @
  concat(branch blocks)\<close>, the trunk part (\<open>m10 < j \<le> TrMax B\<close>) gives \<open>j > m10\<close>
  trivially, and the branch part needs \<open>Joints B ! J \<ge> m10\<close> (validated 591/0,
  from @{thm [source] m_6_4_FirstNodes_TrMax_Joints} + the length-\<open>m10\<close> diagonal
  prefix of \<open>B\<close>) plus per-block row-0 minimality (@{thm [source]
  m_6_5_Red_leftend_row0_min}).\<close>

text \<open>The genuinely-hard BC0 residual, restricted to the BRANCH tail.  In the
  core-nontrunk decomposition \<open>Red B = diagSeq 0 (TrMax B) @ tail\<close>, every tail
  index \<open>j > TrMax B\<close> carries a row-0 value \<open>> m10\<close>.  Empirically TRUE 591/0
  (Lng\<le>4); the trunk part (\<open>j \<le> TrMax B\<close>) is discharged below, the core-trunk
  case is vacuous (no tail).  This is what remains of PIECE3/BC0: it needs
  \<open>Joints B ! J \<ge> m10\<close> (validated 591/0) + per-block @{thm [source]
  m_6_5_Red_leftend_row0_min}.\<close>

text \<open>Full strict suffix-min: combine the trunk-diagonal part (\<open>m10 < j \<le>
  TrMax B\<close>, via @{thm [source] redB_prefix_diag}-style diagonal reads) with the
  branch tail (@{thm [source] redB_tail_row0_above_anchor}).\<close>

lemma redB_row0_strict_above_anchor:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  defines "B \<equiv> diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M"
  shows "\<forall>j. entry M 1 0 < j \<and> j < Lng (Red B) \<longrightarrow> entry M 1 0 < entry (Red B) 0 j"
proof (intro allI impI)
  let ?m10 = "entry M 1 0"
  let ?B = "B"
  fix j assume H: "?m10 < j \<and> j < Lng (Red ?B)"
  hence jgt: "?m10 < j" and jlt: "j < Lng (Red ?B)" by simp_all
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
    using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
  have BT: "?B \<in> T_PS" unfolding B_def using funpow_ne by (simp add: T_PS_def)
  have domB: "Red_dom ?B" by (rule m_6_5_Red_welldef[OF BT])
  have crB: "entry ?B 0 0 = 0 \<and> entry ?B 1 0 = 0"
  proof -
    have "coreReduce M = ?B" unfolding B_def using pos by (simp add: coreReduce_def)
    thus ?thesis using coreReduce_core[OF MT] by simp
  qed
  have c0: "entry ?B 0 0 = 0" and c1: "entry ?B 1 0 = 0" using crB by simp_all
  have monoB: "monoT ?B"
    using coreReduce_monoT_m10_pos[OF MT mono pos] B_def pos by (simp add: coreReduce_def)
  have nzB: "\<not> zeroT ?B" using monoB by (simp add: monoT_def)
  have nmuB: "\<not> multiT ?B" using monoB by (simp add: multiT_def)
  have m10leTr: "?m10 \<le> TrMax ?B"
    using coreReduce_m10_le_TrMax[OF MT mono pos] B_def by simp
  let ?j1 = "Lng ?B - 1"
  let ?j1' = "TrMax ?B"
  show "?m10 < entry (Red ?B) 0 j"
  proof (cases "?j1' = ?j1")
    \<comment> \<open>core-trunk: Red B = diagSeq 0 (Lng B-1), row 0 = identity.\<close>
    case True
    have rB: "Red ?B = diagSeq 0 (0 + ?j1)"
      using Red.psimps[OF domB] nzB nmuB c0 c1 True by (simp add: Let_def)
    have LR: "Lng (Red ?B) = Suc ?j1" using rB by simp
    have jj1: "j < Suc ?j1" using jlt LR by simp
    have "entry (diagSeq 0 (0 + ?j1)) 0 j = 0 + j"
      using entry_diagSeq[where a=0 and b="0+?j1" and j=j and i=0] jj1 by simp
    hence "entry (Red ?B) 0 j = j" using rB by simp
    thus ?thesis using jgt by simp
  next
    \<comment> \<open>core-nontrunk: split on trunk (j \<le> TrMax B) vs branch tail (j > TrMax B).\<close>
    case tne: False
    let ?tail = "concat (map (\<lambda>J.
              (IncrFirst ^^ (Joints ?B ! J + 1
                  - (if entry (Br ?B ! J) 1 0 = 0 then 0
                     else Suc (THE j. nextR ?B 1 j (FirstNodes ?B ! J)))))
                (Red ((entry ?B 0 0 + Joints ?B ! J + 1,
                       entry ?B 1 0 + (if entry (Br ?B ! J) 1 0 = 0 then 0
                              else Suc (THE j. nextR ?B 1 j (FirstNodes ?B ! J))))
                      # tl (Br ?B ! J))))
            [0..<Lng (Br ?B)])"
    have rB: "Red ?B = diagSeq 0 ?j1' @ ?tail"
      using Red.psimps[OF domB] nzB nmuB c0 c1 tne by (simp add: Let_def)
    show ?thesis
    proof (cases "j \<le> ?j1'")
      \<comment> \<open>trunk diagonal part: entry = j > m10.\<close>
      case True
      have "entry (diagSeq 0 ?j1' @ ?tail) 0 j = j"
        by (rule entry_diagSeq_append_lo[OF True])
      hence "entry (Red ?B) 0 j = j" using rB by simp
      thus ?thesis using jgt by simp
    next
      \<comment> \<open>branch tail part: the isolated residual.\<close>
      case False
      hence jtr: "?j1' < j" by simp
      show ?thesis
        using redB_tail_row0_above_anchor[OF MT mono pos] jtr jlt
        unfolding B_def by blast
    qed
  qed
qed

lemma redB_row0_strict_suffix_min:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  defines "B \<equiv> diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M"
  shows "entry (Red B) 0 (entry M 1 0) = entry M 1 0
       \<and> (\<forall>j. entry M 1 0 < j \<and> j < Lng (Red B)
              \<longrightarrow> entry M 1 0 < entry (Red B) 0 j)"
proof -
  have anc: "entry (Red B) 0 (entry M 1 0) = entry M 1 0"
    using redB_prefix_diag[OF MT mono pos, rule_format, of 0 "entry M 1 0"]
    unfolding B_def by simp
  show ?thesis using anc redB_row0_strict_above_anchor[OF MT mono pos] unfolding B_def by simp
qed

text \<open>Row-1 diagonal anchor: \<open>m10\<close> sits on the row-1 diagonal of \<open>Red B\<close>, so its
  row-1 value is \<open>m10\<close>.  Used only to rule out \<open>zeroT\<close> in the singleton suffix.
  Empirically TRUE 600/0.\<close>

lemma redB_row1_anchor:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  defines "B \<equiv> diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M"
  shows "entry (Red B) 1 (entry M 1 0) = entry M 1 0"
  using redB_prefix_diag[OF MT mono pos, rule_format, of 1 "entry M 1 0"]
  unfolding B_def by simp

text \<open>BC0 (\<open>le0\<close> anchor edge): from the strict suffix-min, the diagonal anchor
  \<open>m10\<close> is a row-0 ancestor of the right end \<open>jN\<close> of \<open>Red B\<close>.\<close>

lemma redB_le0_anchor_jN:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  defines "B \<equiv> diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M"
  shows "le0 (Red B) (entry M 1 0) (Lng (Red B) - 1)"
proof -
  let ?m10 = "entry M 1 0"
  let ?N = "Red B"
  let ?jN = "Lng ?N - 1"
  \<comment> \<open>geometry: Lng B = Lng M + m10, so m10 < Lng (Red B).\<close>
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LM: "0 < Lng M" using Mne by (cases M) auto
  have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
    using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
  have BT: "B \<in> T_PS" unfolding B_def using funpow_ne by (simp add: T_PS_def)
  have LB: "Lng B = Lng M + ?m10"
  proof -
    have Ldiag: "Lng (diagSeq 0 (?m10 - 1)) = ?m10" using pos by (simp del: upt_Suc)
    show ?thesis unfolding B_def using Ldiag by simp
  qed
  have LN: "Lng ?N = Lng M + ?m10" using m_6_5_Lng_Red[OF BT] LB by simp
  have m10lt: "?m10 < Lng ?N" using LN LM by simp
  have jNlt: "?jN < Lng ?N" using m10lt by simp
  \<comment> \<open>residual: strict suffix-min from the anchor.\<close>
  have res: "entry ?N 0 ?m10 = ?m10
             \<and> (\<forall>j. ?m10 < j \<and> j < Lng ?N \<longrightarrow> ?m10 < entry ?N 0 j)"
    using redB_row0_strict_suffix_min[OF MT mono pos] unfolding B_def by simp
  have anc_val: "entry ?N 0 ?m10 = ?m10" using res by simp
  have strict: "\<And>j. ?m10 < j \<Longrightarrow> j \<le> ?jN \<Longrightarrow> entry ?N 0 ?m10 < entry ?N 0 j"
  proof -
    fix j assume a: "?m10 < j" and b: "j \<le> ?jN"
    have jlt: "j < Lng ?N" using b jNlt by simp
    have "?m10 < entry ?N 0 j" using res a jlt by blast
    thus "entry ?N 0 ?m10 < entry ?N 0 j" using anc_val by simp
  qed
  show ?thesis
  proof (cases "?m10 = ?jN")
    case True
    show ?thesis using True m10lt by (simp add: le0_def)
  next
    case False
    hence lt: "?m10 < ?jN" using m10lt by simp
    have Nne: "?N \<noteq> []" using LN LM by (metis add_is_0 length_0_conv less_numeral_extra(3))
    have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
    have "leR ?N 0 ?m10 ?jN"
      by (rule m_5_1_parent_exists_3[OF NT lt jNlt strict])
    thus ?thesis by (simp add: leR_def)
  qed
qed

end

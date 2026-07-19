theory P_6_6_Red_leftend_1
  imports P_6_7_ST_eq_Union_SkT
begin

text \<open>補題（\<open>Red\<close>と左端の関係） (1): \<open>Red\<close> fixes the row-1 left end.\<close>

text \<open>m: 補題（Redと左端の関係） (1) — discharges @{text p_6_6_Red_leftend_1}.
  Red preserves the row-1 left end: \<open>entry (Red M) 1 0 = entry M 1 0\<close>.

  Proof sketch: by Red.pinduct.  In each branch of the Red recursion:
  (1) zeroT: Red M = [(0,0)], entry M 1 0 = 0.
  (2) multiT: concat first block reduces to P M ! 0 whose leftend = entry M 1 0 (via m_6_4_P_IdxSum).
  (3a) core trunk: diagSeq 0 j1, entry at 0 = 0 = m10.
  (3b) core non-trunk: diagSeq 0 j1' prefix, entry at 0 = 0 = m10.
  (4) m10=0 shift: IH on shiftRow0 M, entry shiftRow0 1 0 = entry M 1 0.
  (5) m10>0 else: Red M = M, trivial.
  (5) m10>0 then: arg = coreReduce M is monoT (coreReduce_monoT_m10_pos), starts at (0,0),
      TrMax arg >= m10 (TrMax_diagSeq_append_ge), so Red arg opens as diagSeq 0 (TrMax arg) prefix
      and entry N 1 m10 = m10 by entry_diagSeq / entry_diagSeq_append_lo.\<close>

lemma m_6_6_Red_leftend_1:
  assumes MT: "M \<in> T_PS"
  shows "entry (Red M) 1 0 = entry M 1 0"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have "M \<in> T_PS \<longrightarrow> entry (Red M) 1 0 = entry M 1 0"
    using domM
  proof (induction M rule: Red.pinduct)
    case (1 M)
    note dom    = 1(1)
    note IH_mu  = 1(2)
    note IH_nc3 = 1(4)
    show ?case
    proof (rule impI)
      assume MT': "M \<in> T_PS"
      have Mne: "M \<noteq> []" using MT' by (simp add: T_PS_def)
      have LMpos: "0 < Lng M" using Mne by (cases M) auto
      show "entry (Red M) 1 0 = entry M 1 0"
      proof (cases "zeroT M")
        \<comment> \<open>Branch 1: zeroT M.  Red M = [(0,0)], entry M 1 0 = 0.\<close>
        case True
        have rM: "Red M = [(0, 0)]"
          using Red.psimps[OF dom] True by simp
        have "entry M 1 0 = 0" using True by (simp add: zeroT_def)
        thus ?thesis by (simp add: rM entry_def)
      next
        case nz: False
        show "entry (Red M) 1 0 = entry M 1 0"
        proof (cases "multiT M")
          \<comment> \<open>Branch 2: multiT M.  Red M = concat (map Red (P M)).\<close>
          case True
          have rM: "Red M = concat (map Red (P M))"
            using Red.psimps[OF dom] nz True by simp
          have L1: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT' True])
          \<comment> \<open>IH for P M ! 0\<close>
          have ne_PM: "P M \<noteq> []" by (rule P_nonempty)
          have PM0_in: "P M ! 0 \<in> set (P M)"
            using ne_PM by (cases "P M") auto
          have PM0_T: "P M ! 0 \<in> T_PS"
            using P_blocks_nonempty[OF Mne] PM0_in by (auto simp: T_PS_def)
          have ih0: "P M ! 0 \<in> T_PS \<longrightarrow>
                       entry (Red (P M ! 0)) 1 0 = entry (P M ! 0) 1 0"
            by (rule IH_mu[OF nz True PM0_in])
          hence IH': "entry (Red (P M ! 0)) 1 0 = entry (P M ! 0) 1 0"
            using PM0_T by blast
          \<comment> \<open>P M ! 0 = seg M 0 ?, so entry (P M ! 0) 1 0 = entry M 1 0\<close>
          have PM0_JL: "0 < length (P M)"
            using ne_PM by (cases "P M") simp_all
          have PM0_len_pos: "0 < Lng (P M ! 0)"
            by (rule idxsum_P_component_nonempty[OF MT' PM0_JL])
          have idx0: "IdxSum (P M) ! 0 = 0"
            by (simp add: idxsum_nth)
          have e_PM0: "entry (P M ! 0) 1 0 = entry M 1 0"
          proof -
            have Jle: "(0::nat) \<le> Lng (P M) - 1"
              using ne_PM by (cases "P M") simp_all
            have PM0_seg: "P M ! 0 = seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1)"
              using m_6_4_P_IdxSum[OF MT' Jle] by simp
            have lp: "0 < Lng (seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1))"
              using PM0_len_pos PM0_seg by simp
            have "entry (P M ! 0) 1 0
                 = entry (seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1)) 1 0"
              using PM0_seg by simp
            also have "\<dots> = entry M 1 (IdxSum (P M) ! 0 + 0)"
              by (rule entry_seg[OF lp])
            also have "\<dots> = entry M 1 0" by (simp add: idx0)
            finally show ?thesis .
          qed
          \<comment> \<open>concat (map Red (P M)) ! 0 = Red (P M ! 0) ! 0\<close>
          have rPM0_ne: "Red (P M ! 0) \<noteq> []"
          proof -
            have "Lng (Red (P M ! 0)) = Lng (P M ! 0)"
              by (rule m_6_5_Lng_Red[OF PM0_T])
            thus ?thesis using PM0_len_pos by (cases "Red (P M ! 0)") auto
          qed
          have concat_nth0: "concat (map Red (P M)) ! 0 = Red (P M ! 0) ! 0"
          proof -
            have split: "P M = P M ! 0 # tl (P M)"
              using ne_PM by (cases "P M") auto
            have "concat (map Red (P M))
                 = Red (P M ! 0) @ concat (map Red (tl (P M)))"
              by (subst split) simp
            thus ?thesis using rPM0_ne by (simp add: nth_append)
          qed
          \<comment> \<open>Chain the equalities\<close>
          have "entry (Red M) 1 0 = entry (concat (map Red (P M))) 1 0"
            by (simp add: rM)
          also have "\<dots> = entry (Red (P M ! 0)) 1 0"
            by (simp add: entry_def concat_nth0)
          also have "\<dots> = entry (P M ! 0) 1 0" by (rule IH')
          also have "\<dots> = entry M 1 0" by (rule e_PM0)
          finally show ?thesis .
        next
          \<comment> \<open>Branches 3-5: mono.\<close>
          case nmu: False
          have mono: "monoT M" using nz nmu by (simp add: multiT_def)
          let ?j1  = "Lng M - 1"
          let ?j1' = "TrMax M"
          let ?m00 = "entry M 0 0"
          let ?m10 = "entry M 1 0"
          show "entry (Red M) 1 0 = entry M 1 0"
          proof (cases "?m00 = 0 \<and> ?m10 = 0")
            \<comment> \<open>Core case: M starts at (0,0).\<close>
            case core: True
            hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
            show ?thesis
            proof (cases "?j1' = ?j1")
              \<comment> \<open>Branch 3a: TrMax = Lng-1; diagonal output diagSeq m10 (m10+j1).\<close>
              case True
              have rM: "Red M = diagSeq ?m10 (?m10 + ?j1)"
                using Red.psimps[OF dom] nz nmu c0 c1 True
                by (simp add: Let_def)
              have e_rM: "entry (Red M) 1 0 = ?m10"
              proof -
                have "entry (diagSeq ?m10 (?m10 + ?j1)) 1 0 = ?m10 + 0"
                  by (rule entry_diagSeq) (simp add: LMpos)
                thus ?thesis using rM by simp
              qed
              show ?thesis using e_rM c1 by simp
            next
              \<comment> \<open>Branch 3b: TrMax /= Lng-1; diagSeq prefix + branches.\<close>
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
                using Red.psimps[OF dom] nz nmu c0 c1 tne
                by (simp add: Let_def)
              have diag_ne: "diagSeq 0 ?j1' \<noteq> []"
                by (simp add: diagSeq_def)
              have "entry (Red M) 1 0 = entry (diagSeq 0 ?j1' @ ?tail) 1 0"
                by (simp add: rM)
              also have "\<dots> = entry (diagSeq 0 ?j1') 1 0"
                using diag_ne by (simp add: entry_def nth_append)
              also have "\<dots> = 0"
                using entry_diagSeq[where a=0 and b="?j1'" and j=0 and i=1]
                by simp
              finally show ?thesis using c1 by simp
            qed
          next
            \<comment> \<open>Non-core case.\<close>
            case nc: False
            show ?thesis
            proof (cases "?m10 = 0")
              \<comment> \<open>Branch 4: m10=0 shift.  Red M = Red (shiftRow0 M).\<close>
              case True
              have c0p: "0 < ?m00" using nc True by simp
              let ?shift = "map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc ?j1]"
              have rM: "Red M = Red ?shift"
                using Red.psimps[OF dom] nz nmu nc True
                by (simp add: Let_def)
              have shift_T: "?shift \<in> T_PS" by (simp add: T_PS_def)
              have IH': "entry (Red ?shift) 1 0 = entry ?shift 1 0"
                using IH_nc3[OF nz nmu refl refl refl refl nc True] shift_T
                by blast
              have e_shift: "entry ?shift 1 0 = entry M 1 0"
                using LMpos by (simp add: entry_def)
              have "entry (Red M) 1 0 = entry (Red ?shift) 1 0"
                by (simp add: rM)
              also have "\<dots> = entry ?shift 1 0" using IH' .
              also have "\<dots> = entry M 1 0" using e_shift .
              finally show ?thesis .
            next
              \<comment> \<open>Branch 5: m10>0.\<close>
              case False
              hence c1p: "0 < ?m10" by simp
              let ?arg = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
              have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
                using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
              have arg_T: "?arg \<in> T_PS"
                using funpow_ne by (simp add: T_PS_def)
              let ?N = "Red ?arg"
              let ?jN = "Lng ?N - 1"
              have rM: "Red M = (let N = ?N; jN = ?jN in
                         if ?m10 \<le> jN \<and> seg N ?m10 jN \<in> PT_PS then
                           map (\<lambda>j. (entry N 0 j - entry N 0 ?m10 + entry N 1 ?m10,
                                     entry N 1 j))
                               [?m10..<Suc jN]
                         else M)"
                using Red.psimps[OF dom] nz nmu nc c1p
                by (simp add: Let_def)
              show ?thesis
              proof (cases "?m10 \<le> ?jN \<and> seg ?N ?m10 ?jN \<in> PT_PS")
                \<comment> \<open>Else branch: Red M = M.  Trivial.\<close>
                case else_nc: False
                have nc: "\<not> (?m10 \<le> ?jN \<and> seg ?N ?m10 ?jN \<in> PT_PS)" using else_nc .
                have rM_else: "Red M = M"
                proof -
                  have step1: "(let N = ?N; jN = ?jN in
                                 if ?m10 \<le> jN \<and> seg N ?m10 jN \<in> PT_PS
                                 then map (\<lambda>j. (entry N 0 j - entry N 0 ?m10 + entry N 1 ?m10,
                                                entry N 1 j)) [?m10..<Suc jN]
                                 else M) = M"
                    unfolding Let_def
                    by (rule if_not_P[OF nc])
                  show ?thesis using rM step1 by simp
                qed
                thus ?thesis by (simp add: rM_else)
              next
                \<comment> \<open>Then branch: entry N 1 m10 = m10 by structure of Red arg.\<close>
                case then_case: True
                have rM': "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10
                                              + entry ?N 1 ?m10,
                                              entry ?N 1 j))
                                       [?m10..<Suc ?jN]"
                  using rM then_case by (simp add: Let_def del: upt_Suc)
                \<comment> \<open>entry (Red M) 1 0 = entry N 1 m10\<close>
                have rM_ne: "0 < length [?m10..<Suc ?jN]"
                  using then_case by simp
                have rM_e10: "entry (Red M) 1 0 = entry ?N 1 ?m10"
                proof -
                  have h1: "[?m10..<Suc ?jN] ! 0 = ?m10"
                    using then_case by (simp add: nth_upt del: upt_Suc)
                  have h2: "(Red M) ! 0 = (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10
                                                  + entry ?N 1 ?m10, entry ?N 1 j)) ?m10"
                    using rM' rM_ne h1 by (simp add: nth_map del: upt_Suc)
                  have h3: "snd ((Red M) ! 0) = entry ?N 1 ?m10"
                    using h2 by simp
                  show ?thesis using h3 unfolding entry_def by simp
                qed
                \<comment> \<open>arg = coreReduce M is monoT\<close>
                have arg_eq_cr: "?arg = coreReduce M"
                  using c1p by (simp add: coreReduce_def)
                have arg_mono: "monoT ?arg"
                  using coreReduce_monoT_m10_pos[OF MT' mono c1p] arg_eq_cr
                  by simp
                \<comment> \<open>arg not zero: Lng arg = m10 + Lng M >= 2\<close>
                have Larg: "Lng ?arg = ?m10 + Lng M"
                  using c1p by (simp add: Lng_funpow_IncrFirst)
                have arg_nz: "\<not> zeroT ?arg"
                proof -
                  have Larg_ge: "Lng ?arg \<ge> 2" using c1p Larg LMpos by linarith
                  thus ?thesis unfolding zeroT_def using Larg_ge by linarith
                qed
                \<comment> \<open>arg not multi\<close>
                have arg_nmu: "\<not> multiT ?arg"
                  using arg_mono by (simp add: multiT_def)
                \<comment> \<open>entry arg 0 0 = 0 and entry arg 1 0 = 0\<close>
                have arg_c0: "entry ?arg 0 0 = 0"
                  using c1p by (simp add: entry_diagSeq_append_lo)
                have arg_c1: "entry ?arg 1 0 = 0"
                  using c1p by (simp add: entry_diagSeq_append_lo)
                \<comment> \<open>Red_dom arg\<close>
                have dom_arg: "Red_dom ?arg"
                  by (rule m_6_5_Red_welldef[OF arg_T])
                \<comment> \<open>TrMax arg >= m10\<close>
                have er0: "?m10 - 1 < entry ((IncrFirst ^^ ?m10) M) 0 0"
                proof -
                  have "entry ((IncrFirst ^^ ?m10) M) 0 0 = entry M 0 0 + ?m10"
                    by (rule entry_funpow_IncrFirst0[OF LMpos])
                  thus ?thesis using c1p by simp
                qed
                have er1: "?m10 - 1 < entry ((IncrFirst ^^ ?m10) M) 1 0"
                proof -
                  have "entry ((IncrFirst ^^ ?m10) M) 1 0 = entry M 1 0"
                    by (rule entry_funpow_IncrFirst1[OF LMpos])
                  thus ?thesis using c1p by simp
                qed
                have TrMax_ge: "?m10 \<le> TrMax ?arg"
                  using TrMax_diagSeq_append_ge[OF funpow_ne er0 er1] by simp
                \<comment> \<open>Red arg unfolds in core (m00=0, m10=0, monoT) case\<close>
                let ?tail_arg = "concat (map (\<lambda>J.
                        (IncrFirst ^^ (Joints ?arg ! J + 1
                            - (if entry (Br ?arg ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR ?arg 1 j (FirstNodes ?arg ! J)))))
                          (Red ((entry ?arg 0 0 + Joints ?arg ! J + 1,
                                 entry ?arg 1 0
                                 + (if entry (Br ?arg ! J) 1 0 = 0 then 0
                                    else Suc (THE j. nextR ?arg 1 j (FirstNodes ?arg ! J))))
                                # tl (Br ?arg ! J))))
                      [0..<Lng (Br ?arg)])"
                show ?thesis
                proof (cases "TrMax ?arg = Lng ?arg - 1")
                  \<comment> \<open>Trunk case: Red arg = diagSeq 0 (Lng arg - 1).\<close>
                  case tr: True
                  have rArg_tr: "Red ?arg = diagSeq 0 (Lng ?arg - 1)"
                    using Red.psimps[OF dom_arg] arg_nz arg_nmu arg_c0 arg_c1 tr
                    by (simp add: Let_def)
                  have NrArg: "?N = diagSeq 0 (Lng ?arg - 1)"
                    using rArg_tr by simp
                  have "entry ?N 1 ?m10
                       = entry (diagSeq 0 (Lng ?arg - 1)) 1 ?m10"
                    using NrArg by simp
                  also have "\<dots> = ?m10"
                    using entry_diagSeq[where a=0 and b="Lng ?arg - 1"
                                        and j="?m10" and i=1]
                    using Larg c1p LMpos by simp
                  finally show ?thesis using rM_e10 by simp
                next
                  \<comment> \<open>Non-trunk case: Red arg = diagSeq 0 (TrMax arg) @ ...\<close>
                  case ntr: False
                  have rArg_ntr: "Red ?arg = diagSeq 0 (TrMax ?arg) @ ?tail_arg"
                    using Red.psimps[OF dom_arg] arg_nz arg_nmu arg_c0 arg_c1 ntr
                    by (simp add: Let_def)
                  have NrArg_ntr: "?N = diagSeq 0 (TrMax ?arg) @ ?tail_arg"
                    using rArg_ntr by simp
                  have "entry ?N 1 ?m10
                       = entry (diagSeq 0 (TrMax ?arg) @ ?tail_arg) 1 ?m10"
                    using NrArg_ntr by simp
                  also have "\<dots> = ?m10"
                    by (rule entry_diagSeq_append_lo) (rule TrMax_ge)
                  finally show ?thesis using rM_e10 by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using MT by blast
qed


lemma p_6_6_Red_leftend_1:
  assumes "M \<in> T_PS"
  shows "entry (Red M) 1 0 = entry M 1 0"
  using assms by (rule m_6_6_Red_leftend_1)

end

theory P_6_5_Red_Pred
  imports Frontier_6_057
begin

text \<open>命題（\<open>Red\<close>と\<open>Pred\<close>の可換性）.\<close>

text \<open>§6.5 命題（\<open>Red\<close>と\<open>Pred\<close>の可換性）\<open>Red (Pred M) = Pred (Red M)\<close> for
  \<open>M \<in> T\<^sub>PS\<close> \<dash> discharges @{text p_6_5_Red_Pred}.  Proved by the same
  @{thm [source] Red.pinduct} as @{thm [source] a3_Red_Pred_cond}; the five
  non-core-nontrunk branches are identical, and the core-nontrunk \<open>Hbr\<close> obligation
  is discharged by @{thm [source] rpred_core_nontrunk_step} using the per-branch
  recursion IH on \<open>N\<^sub>J M J\<close>.  Empirically \<open>Red(Pred M)=Pred(Red M)\<close> holds 7380/7380.\<close>

lemma m_6_5_Red_Pred:
  assumes MT: "M \<in> T_PS"
  shows "Red (Pred M) = Pred (Red M)"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have "M \<in> T_PS \<longrightarrow> Red (Pred M) = Pred (Red M)"
    using domM
  proof (induction M rule: Red.pinduct)
    case (1 M)
    note dom    = 1(1)
    note IH_mu  = 1(2)  \<comment> \<open>multiT IH on \<open>P\<close>-blocks\<close>
    note IH_bz  = 1(3)  \<comment> \<open>core-branch IH (\<open>NJ M J\<close>)\<close>
    note IH_sh  = 1(4)  \<comment> \<open>shift (\<open>m\<^sub>1\<^sub>0=0\<close>) IH\<close>
    note IH_m1  = 1(5)  \<comment> \<open>m10>0 core-reduce-arg IH\<close>
    show ?case
    proof (rule impI)
      assume MT': "M \<in> T_PS"
      have Mne: "M \<noteq> []" using MT' by (simp add: T_PS_def)
      have LMpos: "0 < Lng M" using Mne by (cases M) auto
      show "Red (Pred M) = Pred (Red M)"
      proof (cases "1 < Lng M")
        case False
        \<comment> \<open>\<open>Lng M = 1\<close>: \<open>Pred M = M\<close> and \<open>Lng (Red M) = Lng M = 1\<close>, so
           \<open>Pred (Red M) = Red M\<close>.\<close>
        have L1: "Lng M = 1" using False LMpos by linarith
        have predM: "Pred M = M" using L1 by (simp add: Pred_def)
        have "Lng (Red M) = 1" using m_6_5_Lng_Red[OF MT'] L1 by simp
        hence "Pred (Red M) = Red M" by (simp add: Pred_def)
        thus ?thesis using predM by simp
      next
        case L1: True
        have nz: "\<not> zeroT M" using L1 by (simp add: zeroT_def)
        have predbl: "Pred M = butlast M" using L1 by (simp add: Pred_def)
        show "Red (Pred M) = Pred (Red M)"
        proof (cases "multiT M")
          case mu: True
          \<comment> \<open>Branch 2: multiT.\<close>
          have rM: "Red M = concat (map Red (P M))"
            using Red.psimps[OF dom] nz mu by simp
          let ?L = "map Red (P M)"
          have PMne: "P M \<noteq> []" by (rule P_nonempty)
          have lastPM_in: "last (P M) \<in> set (P M)" using PMne last_in_set by blast
          have lastPM_ne: "last (P M) \<noteq> []"
            using P_blocks_nonempty[OF Mne] lastPM_in by blast
          have lastPM_T: "last (P M) \<in> T_PS" using lastPM_ne by (simp add: T_PS_def)
          have Lne: "?L \<noteq> []" using PMne by simp
          have lastL: "last ?L = Red (last (P M))" using PMne by (simp add: last_map)
          have lastL_ne: "last ?L \<noteq> []"
          proof -
            have "Lng (Red (last (P M))) = Lng (last (P M))"
              by (rule m_6_5_Lng_Red[OF lastPM_T])
            hence "0 < Lng (Red (last (P M)))" using lastPM_ne by (cases "last (P M)") auto
            thus ?thesis using lastL by (cases "last ?L") auto
          qed
          \<comment> \<open>\<open>Pred (Red M)\<close> acts on the last reduced block.\<close>
          have predRM: "Pred (Red M)
                  = concat (map Red (butlast (P M))) @ butlast (Red (last (P M)))"
          proof -
            have LrM: "1 < Lng (Red M)"
            proof -
              have "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT'])
              thus ?thesis using L1 by simp
            qed
            have "Pred (Red M) = butlast (Red M)" using LrM by (simp add: Pred_def)
            also have "\<dots> = butlast (concat ?L)" by (simp add: rM)
            also have "\<dots> = concat (butlast ?L) @ butlast (last ?L)"
              by (rule a3_butlast_concat[OF Lne lastL_ne])
            also have "butlast ?L = map Red (butlast (P M))" by (simp add: a3_map_butlast)
            also have "last ?L = Red (last (P M))" by (rule lastL)
            finally show ?thesis .
          qed
          \<comment> \<open>\<open>Red (Pred M)\<close> via \<open>pred_P_decomp\<close>.\<close>
          have pdec: "P (Pred M) =
                  (if Lng (last (P M)) = 1
                   then butlast (P M)
                   else butlast (P M) @ [Pred (last (P M))])"
            by (rule pred_P_decomp[OF MT' mu])
          have predT: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF MT'])
          have dom_pred: "Red_dom (Pred M)" by (rule m_6_5_Red_welldef[OF predT])
          \<comment> \<open>\<open>Pred M\<close> is still multi (multiT class is stable when last block length \<noteq> 0,
             handled inside the two cases) — unfold \<open>Red (Pred M)\<close> via the recursion.\<close>
          show ?thesis
          proof (cases "Lng (last (P M)) = 1")
            case len1: True
            have PpredM: "P (Pred M) = butlast (P M)" using pdec len1 by simp
            \<comment> \<open>\<open>butlast (Red (last (P M))) = []\<close> since \<open>Lng (last (P M)) = 1\<close>.\<close>
            have empt: "butlast (Red (last (P M))) = []"
              by (rule a3_butlast_Red_len1[OF lastPM_T len1])
            \<comment> \<open>\<open>Red (Pred M) = concat (map Red (P (Pred M)))\<close> — need \<open>Pred M\<close> multi or handle mono.\<close>
            have RpredM: "Red (Pred M) = concat (map Red (butlast (P M)))"
            proof (cases "multiT (Pred M)")
              case True
              have nzP: "\<not> zeroT (Pred M)" using True by (simp add: multiT_def)
              have "Red (Pred M) = concat (map Red (P (Pred M)))"
                using Red.psimps[OF dom_pred] nzP True by simp
              thus ?thesis using PpredM by simp
            next
              case nmuP: False
              \<comment> \<open>\<open>P (Pred M) = butlast (P M)\<close> has length 1: \<open>Pred M\<close> is a single block.\<close>
              have "P (Pred M) = [Pred M]" using nmuP by (subst P.simps) simp
              hence single: "butlast (P M) = [Pred M]" using PpredM by simp
              hence "concat (map Red (butlast (P M))) = Red (Pred M)" by simp
              thus ?thesis by simp
            qed
            show ?thesis using RpredM predRM empt by simp
          next
            case lenN: False
            have lastN_T: "last (P M) \<in> T_PS" by (rule lastPM_T)
            have lastN_L1: "1 < Lng (last (P M))"
              using lenN lastPM_ne by (cases "last (P M)") auto
            have PpredM: "P (Pred M) = butlast (P M) @ [Pred (last (P M))]"
              using pdec lenN by simp
            \<comment> \<open>\<open>Pred M\<close> is multi (its last \<open>P\<close>-block \<open>Pred (last (P M))\<close> is non-trivial here,
               and \<open>butlast (P M)\<close> may be empty or not).\<close>
            have RpredM: "Red (Pred M)
                    = concat (map Red (butlast (P M))) @ Red (Pred (last (P M)))"
            proof (cases "multiT (Pred M)")
              case True
              have nzP: "\<not> zeroT (Pred M)" using True by (simp add: multiT_def)
              have "Red (Pred M) = concat (map Red (P (Pred M)))"
                using Red.psimps[OF dom_pred] nzP True by simp
              thus ?thesis using PpredM by simp
            next
              case nmuP: False
              \<comment> \<open>\<open>P (Pred M)\<close> length 1: then \<open>butlast (P M) = []\<close> and \<open>Pred M = Pred (last (P M))\<close>.\<close>
              have "P (Pred M) = [Pred M]" using nmuP by (subst P.simps) simp
              hence "butlast (P M) @ [Pred (last (P M))] = [Pred M]" using PpredM by simp
              hence bnil: "butlast (P M) = []" and pe: "Pred (last (P M)) = Pred M"
                by auto
              show ?thesis using bnil pe by simp
            qed
            \<comment> \<open>IH on \<open>last (P M)\<close>: \<open>Red (Pred (last (P M))) = Pred (Red (last (P M)))\<close>.\<close>
            have ihL: "Red (Pred (last (P M))) = Pred (Red (last (P M)))"
            proof -
              have ih: "last (P M) \<in> T_PS \<longrightarrow>
                          Red (Pred (last (P M))) = Pred (Red (last (P M)))"
                by (rule IH_mu[OF nz mu lastPM_in])
              thus ?thesis using lastN_T by blast
            qed
            \<comment> \<open>\<open>Pred (Red (last (P M))) = butlast (Red (last (P M)))\<close> since \<open>Lng > 1\<close>.\<close>
            have predRl: "Pred (Red (last (P M))) = butlast (Red (last (P M)))"
            proof -
              have "1 < Lng (Red (last (P M)))"
                using m_6_5_Lng_Red[OF lastN_T] lastN_L1 by simp
              thus ?thesis by (simp add: Pred_def)
            qed
            show ?thesis using RpredM predRM ihL predRl by simp
          qed
        next
          case nmu: False
          have mono: "monoT M" using nz nmu by (simp add: multiT_def)
          have Mpt: "M \<in> PT_PS" using MT' mono by (simp add: PT_PS_def)
          let ?m00 = "entry M 0 0"
          let ?m10 = "entry M 1 0"
          show "Red (Pred M) = Pred (Red M)"
          proof (cases "?m00 = 0 \<and> ?m10 = 0")
            case core: True
            hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
            show ?thesis
            proof (cases "TrMax M = Lng M - 1")
              case trunk: True
              \<comment> \<open>Branch 3a: core diagonal.  \<open>Red M = diagSeq 0 (Lng M - 1)\<close>; \<open>Pred M\<close> is
                 again core-trunk (or a zero term), so \<open>Red (Pred M) = diagSeq 0 (Lng M - 2)\<close>.\<close>
              have rM: "Red M = diagSeq (?m10) (?m10 + (Lng M - 1))"
                using Red.psimps[OF dom] nz nmu c0 c1 trunk by (simp add: Let_def)
              have rM': "Red M = diagSeq 0 (Lng M - 1)" using rM c1 by simp
              have nc4: "1 < Lng M" using L1 .
              have predM_T: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF MT'])
              have predbl: "Pred M = butlast M" using L1 by (simp add: Pred_def)
              have LP: "Lng (Pred M) = Lng M - 1" using L1 by (simp add: predbl)
              have dom_pred: "Red_dom (Pred M)" by (rule m_6_5_Red_welldef[OF predM_T])
              \<comment> \<open>row-0/row-1 head of \<open>Pred M\<close> is core.\<close>
              have c0P: "entry (Pred M) 0 0 = 0" using c0 entry_Pred_0[OF L1] by simp
              have c1P: "entry (Pred M) 1 0 = 0" using c1 entry_Pred_0[OF L1] by simp
              \<comment> \<open>\<open>Red (Pred M) = diagSeq 0 (Lng M - 2)\<close>.\<close>
              have RpredM: "Red (Pred M) = diagSeq 0 (Lng M - 2)"
              proof (cases "zeroT (Pred M)")
                case True
                have L1P: "Lng (Pred M) = 1" using True by (simp add: zeroT_def)
                hence "Lng M - 2 = 0" using LP by simp
                have "Red (Pred M) = [(0,0)]" using Red.psimps[OF dom_pred] True by simp
                also have "\<dots> = diagSeq 0 (Lng M - 2)"
                  using \<open>Lng M - 2 = 0\<close> by (simp add: diagSeq_def)
                finally show ?thesis .
              next
                case False
                have nmuP: "\<not> multiT (Pred M)" by (rule nonmulti_Pred[OF MT' nmu L1])
                have trP: "TrMax (Pred M) = Lng (Pred M) - 1"
                  by (rule a3_TrMax_Pred_trunk[OF MT' trunk L1])
                have "Red (Pred M) = diagSeq (entry (Pred M) 1 0)
                          (entry (Pred M) 1 0 + (Lng (Pred M) - 1))"
                  using Red.psimps[OF dom_pred] False nmuP c0P c1P trP by (simp add: Let_def)
                also have "\<dots> = diagSeq 0 (Lng M - 2)"
                  using c1P LP by (simp add: numeral_2_eq_2)
                finally show ?thesis .
              qed
              \<comment> \<open>\<open>Pred (Red M) = butlast (diagSeq 0 (Lng M - 1)) = diagSeq 0 (Lng M - 2)\<close>.\<close>
              have predRedM: "Pred (Red M) = diagSeq 0 (Lng M - 2)"
              proof -
                have LrM: "1 < Lng (Red M)" using m_6_5_Lng_Red[OF MT'] L1 by simp
                have "Pred (Red M) = butlast (diagSeq 0 (Lng M - 1))"
                  using LrM rM' by (simp add: Pred_def)
                also have "\<dots> = diagSeq 0 ((Lng M - 1) - 1)"
                  using butlast_diagSeq[of 0 "Lng M - 1"] L1 by simp
                also have "(Lng M - 1) - 1 = Lng M - 2" by simp
                finally show ?thesis .
              qed
              show ?thesis using RpredM predRedM by simp
            next
              case tne: False
              \<comment> \<open>Branch 3b: core non-trunk \<dash> discharged via @{thm [source]
                 rpred_core_nontrunk_step} with the per-branch IH on \<open>NJ M J\<close>.\<close>
              have IHbr: "\<And>J. J < Lng (Br M) \<Longrightarrow>
                            Red (Pred (NJ M J)) = Pred (Red (NJ M J))"
              proof -
                fix J assume JBr: "J < Lng (Br M)"
                have M_PT: "M \<in> PT_PS" using MT' mono by (simp add: PT_PS_def)
                have Jmem: "J \<in> set [0..<Lng (Br M)]" using JBr by simp
                have core': "?m00 = 0 \<and> ?m10 = 0" using core by simp
                have npE: "(if entry (Br M ! J) 1 0 = 0 then 0
                            else Suc (THE j. nextR M 1 j (FirstNodes M ! J))) = npJ M J"
                  by (simp add: npJ_def)
                have argE: "((entry M 0 0 + Joints M ! J + 1, entry M 1 0 + npJ M J)
                             # tl (Br M ! J)) = NJ M J"
                  by (simp add: NJ_def)
                have ih: "NJ M J \<in> T_PS \<longrightarrow>
                            Red (Pred (NJ M J)) = Pred (Red (NJ M J))"
                  using IH_bz[OF nz nmu refl refl refl refl core' tne Jmem]
                  by (simp only: npE argE)
                have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
                have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
                show "Red (Pred (NJ M J)) = Pred (Red (NJ M J))" using ih NJT by blast
              qed
              show ?thesis
                by (rule rpred_core_nontrunk_step[OF MT' mono c0 c1 tne IHbr])
            qed
          next
            case nc: False
            show ?thesis
            proof (cases "?m10 = 0")
              case c1z: True
              \<comment> \<open>Branch 4: shift (\<open>m\<^sub>1\<^sub>0 = 0\<close>, \<open>m\<^sub>0\<^sub>0 > 0\<close>).\<close>
              have c0p: "0 < ?m00" using nc c1z by simp
              \<comment> \<open>\<open>Red M = Red (shiftRow0 M)\<close>.\<close>
              have rM_sh: "Red M = Red (shiftRow0 M)"
                by (rule cdn_Red_shiftRow0_m10z[OF MT' mono c1z])
              let ?sh = "shiftRow0 M"
              have shT: "?sh \<in> T_PS" by (simp add: T_PS_def shiftRow0_def Mne)
              \<comment> \<open>IH on the shift argument \<open>?sh\<close>.\<close>
              have SAeq: "map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc (Lng M - 1)] = ?sh"
              proof -
                have "Suc (Lng M - 1) = Lng M" using LMpos by simp
                thus ?thesis by (simp add: shiftRow0_def)
              qed
              have ih_sh: "?sh \<in> T_PS \<longrightarrow> Red (Pred ?sh) = Pred (Red ?sh)"
                using IH_sh[OF nz nmu refl refl refl refl nc c1z] SAeq by simp
              have predRed_sh: "Red (Pred ?sh) = Pred (Red ?sh)" using ih_sh shT by blast
              \<comment> \<open>\<open>Pred (Red M) = Pred (Red ?sh) = Red (Pred ?sh)\<close>.\<close>
              have step1: "Pred (Red M) = Red (Pred ?sh)" using rM_sh predRed_sh by simp
              \<comment> \<open>\<open>shiftRow0\<close> commutes with \<open>Pred = butlast\<close>.\<close>
              have shiftPred: "?sh = ?sh" ..
              have commute: "Pred ?sh = shiftRow0 (Pred M)"
                by (rule a3_shiftRow0_Pred[OF L1])
              \<comment> \<open>\<open>Red (Pred M) = Red (shiftRow0 (Pred M))\<close>.\<close>
              have predM_mono_or: "Red (Pred M) = Red (shiftRow0 (Pred M))"
                by (rule a3_Red_shiftRow0_Pred_m10z[OF MT' mono c1z L1])
              show ?thesis using predM_mono_or commute step1 by simp
            next
              case c1p: False
              \<comment> \<open>Branch 5: \<open>m\<^sub>1\<^sub>0 > 0\<close>.  \<open>Red M = outMap N m10\<close> with \<open>N = Red (argM)\<close>;
                 \<open>Pred M\<close> is again branch 5 with \<open>N' = Red (Pred argM) = Pred N\<close> by the IH
                 on \<open>argM\<close> via @{thm [source] m_6_5_T4_coreArg_Pred}.\<close>
              have pos: "0 < ?m10" using c1p by simp
              let ?argM = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
              have funM_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
                using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
              have argMT: "?argM \<in> T_PS" using funM_ne by (simp add: T_PS_def)
              let ?N = "Red ?argM"
              have LN: "Lng ?N = Lng M + ?m10"
                using m_6_5_monoT_Red_fact1_Lng[OF MT' pos] by simp
              have jN_ge: "?m10 \<le> Lng ?N - 1" using LN LMpos by linarith
              have segN_PT: "seg ?N ?m10 (Lng ?N - 1) \<in> PT_PS"
                using m_6_5_monoT_Red_m10pos[OF Mpt pos] by simp
              have thenM: "?m10 \<le> Lng ?N - 1 \<and> seg ?N ?m10 (Lng ?N - 1) \<in> PT_PS"
                using jN_ge segN_PT by simp
              let ?outMap = "\<lambda>P m. map (\<lambda>j. (entry P 0 j - entry P 0 m + entry P 1 m,
                                            entry P 1 j)) [m..<Suc (Lng P - 1)]"
              have rM: "Red M = ?outMap ?N ?m10"
                using Red.psimps[OF dom] nz nmu nc c1p thenM by (simp add: Let_def)
              \<comment> \<open>\<open>Pred M\<close>: monoT, m10>0, in PT_PS.\<close>
              have predT: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF MT'])
              have e1P: "entry (Pred M) 1 0 = ?m10" by (rule entry_Pred_0[OF L1])
              have posP: "0 < entry (Pred M) 1 0" using e1P pos by simp
              have nzP: "\<not> zeroT (Pred M)" using e1P pos by (simp add: zeroT_def)
              have nmuP: "\<not> multiT (Pred M)" by (rule nonmulti_Pred[OF MT' nmu L1])
              have monoP: "monoT (Pred M)" using nzP nmuP by (simp add: multiT_def)
              have PpredPT: "Pred M \<in> PT_PS" using predT monoP by (simp add: PT_PS_def)
              have ncP: "\<not> (entry (Pred M) 0 0 = 0 \<and> entry (Pred M) 1 0 = 0)"
                using posP by simp
              have domP: "Red_dom (Pred M)" by (rule m_6_5_Red_welldef[OF predT])
              \<comment> \<open>\<open>argM\<close> under \<open>Pred\<close>: \<open>argM(Pred M) = Pred argM\<close>.\<close>
              let ?argP = "diagSeq 0 (entry (Pred M) 1 0 - 1)
                              @ (IncrFirst ^^ (entry (Pred M) 1 0)) (Pred M)"
              have argP_eq: "?argP = Pred ?argM"
                using m_6_5_T4_coreArg_Pred[OF L1 pos] e1P by simp
              \<comment> \<open>IH on \<open>argM\<close>: \<open>Red (Pred argM) = Pred (Red argM)\<close>.\<close>
              have ih: "?argM \<in> T_PS \<longrightarrow> Red (Pred ?argM) = Pred (Red ?argM)"
                using IH_m1[OF nz nmu refl refl refl refl nc c1p] by simp
              have ihM: "Red (Pred ?argM) = Pred ?N" using ih argMT by blast
              have LNgt1: "1 < Lng ?N" using LN L1 pos by simp
              have predN: "Pred ?N = butlast ?N" using LNgt1 by (simp add: Pred_def)
              have NP_eq: "Red ?argP = butlast ?N"
                using argP_eq ihM predN by simp
              have LbutN: "Lng (butlast ?N) = Lng ?N - 1" using LNgt1 by simp
              \<comment> \<open>\<open>Pred M\<close> takes the same productive branch.\<close>
              have LNP: "Lng (Red ?argP) = Lng (Pred M) + entry (Pred M) 1 0"
                using m_6_5_monoT_Red_fact1_Lng[OF predT posP] by simp
              have jNP_ge: "entry (Pred M) 1 0 \<le> Lng (Red ?argP) - 1"
              proof -
                have predM_ne: "Pred M \<noteq> []" using predT by (simp add: T_PS_def)
                hence "0 < Lng (Pred M)" by (cases "Pred M") auto
                thus ?thesis using LNP by linarith
              qed
              have segNP_PT: "seg (Red ?argP) (entry (Pred M) 1 0) (Lng (Red ?argP) - 1) \<in> PT_PS"
                using m_6_5_monoT_Red_m10pos[OF PpredPT posP] by simp
              have thenP: "entry (Pred M) 1 0 \<le> Lng (Red ?argP) - 1
                            \<and> seg (Red ?argP) (entry (Pred M) 1 0) (Lng (Red ?argP) - 1) \<in> PT_PS"
                using jNP_ge segNP_PT by simp
              have rPredM: "Red (Pred M) = ?outMap (Red ?argP) (entry (Pred M) 1 0)"
                using Red.psimps[OF domP] nzP nmuP ncP posP thenP by (simp add: Let_def)
              have rPredM': "Red (Pred M) = ?outMap (butlast ?N) ?m10"
                using rPredM NP_eq e1P by simp
              \<comment> \<open>Now compare \<open>?outMap (butlast ?N) m10\<close> with \<open>Pred (?outMap ?N m10)\<close>.\<close>
              have m10_lt_butN: "?m10 < Lng (butlast ?N)" using LbutN LN LMpos L1 by linarith
              \<comment> \<open>\<open>Pred (Red M) = butlast (?outMap ?N m10) = map f (butlast [m10..<Suc(Lng N -1)])\<close>.\<close>
              have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT'])
              have LrMgt1: "1 < Lng (Red M)" using LrM L1 by simp
              have sucN: "Suc (Lng ?N - 1) = Lng ?N" using LNgt1 by simp
              have rangeN: "[?m10..<Suc (Lng ?N - 1)] = [?m10..<Lng ?N]" by (simp only: sucN)
              have predRedM: "Pred (Red M)
                    = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10, entry ?N 1 j))
                          [?m10..<Lng ?N - 1]"
              proof -
                have "Pred (Red M) = butlast (Red M)" using LrMgt1 by (simp add: Pred_def)
                also have "\<dots> = butlast (map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                                  entry ?N 1 j)) [?m10..<Lng ?N])"
                  using rM rangeN by simp
                also have "\<dots> = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                          entry ?N 1 j)) (butlast [?m10..<Lng ?N])"
                  by (simp add: map_butlast)
                also have "butlast [?m10..<Lng ?N] = [?m10..<Lng ?N - 1]"
                proof -
                  have le: "?m10 \<le> Lng ?N - 1" using jN_ge by simp
                  have suc: "Suc (Lng ?N - 1) = Lng ?N" using LNgt1 by simp
                  have "[?m10..<Lng ?N] = [?m10..<Suc (Lng ?N - 1)]" using suc by simp
                  also have "\<dots> = [?m10..<Lng ?N - 1] @ [Lng ?N - 1]"
                    by (rule upt_Suc_append[OF le])
                  finally show ?thesis by simp
                qed
                finally show ?thesis .
              qed
              \<comment> \<open>\<open>Red (Pred M)\<close> as a map over the same range; entries via \<open>butlast ?N = ?N\<close> below cut.\<close>
              have predRedM2: "Red (Pred M)
                    = map (\<lambda>j. (entry (butlast ?N) 0 j - entry (butlast ?N) 0 ?m10
                                  + entry (butlast ?N) 1 ?m10, entry (butlast ?N) 1 j))
                          [?m10..<Lng ?N - 1]"
              proof -
                have "Suc (Lng (butlast ?N) - 1) = Lng ?N - 1" using LbutN m10_lt_butN by simp
                thus ?thesis using rPredM' by simp
              qed
              \<comment> \<open>entries of \<open>butlast ?N\<close> agree with \<open>?N\<close> on indices \<open>< Lng ?N - 1\<close>.\<close>
              have ebut: "\<And>i j. j < Lng ?N - 1 \<Longrightarrow> entry (butlast ?N) i j = entry ?N i j"
                using LNgt1 by (simp add: entry_def nth_butlast)
              have m10lt': "?m10 < Lng ?N - 1" using m10_lt_butN LbutN by simp
              have ebut_m0: "entry (butlast ?N) 0 ?m10 = entry ?N 0 ?m10"
                by (rule ebut[OF m10lt'])
              have ebut_m1: "entry (butlast ?N) 1 ?m10 = entry ?N 1 ?m10"
                by (rule ebut[OF m10lt'])
              note ebut_m = ebut_m0 ebut_m1
              show ?thesis
              proof (simp only: predRedM predRedM2, rule map_cong[OF refl])
                fix j assume "j \<in> set [?m10..<Lng ?N - 1]"
                hence jlt: "j < Lng ?N - 1" by simp
                have e0j: "entry (butlast ?N) 0 j = entry ?N 0 j" by (rule ebut[OF jlt])
                have e1j: "entry (butlast ?N) 1 j = entry ?N 1 j" by (rule ebut[OF jlt])
                show "(entry (butlast ?N) 0 j - entry (butlast ?N) 0 ?m10
                          + entry (butlast ?N) 1 ?m10, entry (butlast ?N) 1 j)
                      = (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10, entry ?N 1 j)"
                  by (simp only: e0j e1j ebut_m)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using MT by blast
qed



lemma p_6_5_Red_Pred:
  assumes "M \<in> T_PS"
  shows "Red (Pred M) = Pred (Red M)"
  using assms by (rule m_6_5_Red_Pred)

end

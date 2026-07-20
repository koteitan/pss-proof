theory P_6_5_Lng_Red
  imports P_6_5_Red_welldef
begin

text \<open>命題（\<open>Lng\<close>の\<open>Red\<close>不変性）.\<close>

text \<open>m: 命題（Lng の Red 不変性） — discharges p_6_5_Lng_Red.\<close>
lemma m_6_5_Lng_Red:
  assumes MT: "M \<in> T_PS"
  shows "Lng (Red M) = Lng M"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  \<comment> \<open>The property we prove by Red.pinduct induction.\<close>
  have "M \<in> T_PS \<longrightarrow> Lng (Red M) = Lng M"
    using domM
  proof (induction M rule: Red.pinduct)
    case (1 M)
    \<comment> \<open>One single case covering all branches; we case-split manually.\<close>
    note dom    = 1(1)
    note IH_mu  = 1(2)  \<comment> \<open>multiT IH: x∈set(P M) ⟹ Lng(Red x) = Lng x\<close>
    note IH_bz  = 1(3)  \<comment> \<open>core-branch IH (e10=0)\<close>
    note IH_nc3 = 1(4)  \<comment> \<open>non-core m10=0 IH\<close>
    note IH_nc4 = 1(5)  \<comment> \<open>non-core m10>0 IH\<close>
    show ?case
    proof (rule impI)
      assume MT': "M \<in> T_PS"
      have Mne: "M \<noteq> []" using MT' by (simp add: T_PS_def)
      have LMpos: "0 < Lng M" using Mne by (cases M) auto
      show "Lng (Red M) = Lng M"
      proof (cases "zeroT M")
        \<comment> \<open>Branch 1: zeroT M.  Red M = [(0,0)], Lng 1 = Lng M.\<close>
        case True
        have rM: "Red M = [(0, 0)]"
          using Red.psimps[OF dom] True by simp
        thus ?thesis using True by (simp add: rM zeroT_def)
      next
        case nz: False
        show "Lng (Red M) = Lng M"
        proof (cases "multiT M")
          \<comment> \<open>Branch 2: multiT M.  Red M = concat(map Red (P M)).\<close>
          case True
          have rM: "Red M = concat (map Red (P M))"
            using Red.psimps[OF dom] nz True by simp
          have L1: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT' True])
          \<comment> \<open>Bring P M into form the IH_mu was stated with.\<close>
          have pmset: "(if Suc 0 < Lng M
                        then P (take (Pcut M) M) @ [drop (Pcut M) M] else [M])
                      = P M"
            using L1 True by (subst P.simps) simp
          have IH': "\<forall>y \<in> set (P M). Lng (Red y) = Lng y"
          proof
            fix y assume y: "y \<in> set (P M)"
            have yT: "y \<in> T_PS" using P_blocks_nonempty[OF Mne] y by (auto simp: T_PS_def)
            have ih: "y \<in> T_PS \<longrightarrow> Lng (Red y) = Lng y"
              by (rule IH_mu[OF nz True y])
            thus "Lng (Red y) = Lng y" using yT ih by blast
          qed
          have "Lng (Red M) = Lng (concat (map Red (P M)))"
            by (simp add: rM)
          also have "\<dots> = Lng (concat (P M))"
          proof -
            have leneq: "\<And>y. y \<in> set (P M) \<Longrightarrow> Lng (Red y) = Lng y"
              using IH' by blast
            have steps: "map (Lng \<circ> Red) (P M) = map Lng (P M)"
              by (rule map_cong[OF refl]) (simp add: leneq)
            have "Lng (concat (map Red (P M))) = Lng (concat (P M))"
              by (simp only: length_concat map_map steps)
            thus ?thesis by (simp add: rM)
          qed
          also have "\<dots> = Lng M" by (simp add: poper_concat_P)
          finally show ?thesis .
        next
          \<comment> \<open>Branches 3–5: mono (¬ zeroT, ¬ multiT). Use Let_def to expose sub-cases.\<close>
          case nmu: False
          have mono: "monoT M" using nz nmu by (simp add: multiT_def)
          have Mpt: "M \<in> PT_PS" using MT' mono by (simp add: PT_PS_def)
          let ?j1  = "Lng M - 1"
          let ?j1' = "TrMax M"
          let ?m00 = "entry M 0 0"
          let ?m10 = "entry M 1 0"
          show "Lng (Red M) = Lng M"
          proof (cases "?m00 = 0 \<and> ?m10 = 0")
            \<comment> \<open>Core case: M starts at (0,0).\<close>
            case core: True
            hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
            show ?thesis
            proof (cases "?j1' = ?j1")
              \<comment> \<open>Branch 3a: TrMax = Lng-1; diagonal output.\<close>
              case True
              have rM: "Red M = diagSeq ?m10 (?m10 + ?j1)"
                using Red.psimps[OF dom] nz nmu c0 c1 True
                by (simp add: Let_def)
              have "Lng (Red M) = Suc (?m10 + ?j1) - ?m10"
                by (simp add: rM)
              also have "\<dots> = Lng M" using LMpos c1 by simp
              finally show ?thesis .
            next
              \<comment> \<open>Branch 3b: TrMax ≠ Lng-1; diagonal prefix + branches.\<close>
              case tne: False
              have trlt: "?j1' < Lng M - 1"
                using TrMax_bound[OF MT'] tne LMpos by linarith
              \<comment> \<open>IH for each branch index J: Lng(Red(NJ M J)) = Lng(Br M ! J).\<close>
              have IH_NJ: "\<And>J. J < Lng (Br M) \<Longrightarrow>
                    Lng (Red (NJ M J)) = Lng (Br M ! J)"
              proof -
                fix J assume JBr: "J < Lng (Br M)"
                have brJne: "Br M ! J \<noteq> []"
                  by (rule Br_component_nonempty[OF Mpt JBr])
                \<comment> \<open>The IH_bz from pinduct gives us what we need.\<close>
                have J_in: "J \<in> set [0..<Lng (Br M)]"
                  using JBr by simp
                have arg_T: "(entry M 0 0 + Joints M ! J + 1,
                              entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                             else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                             # tl (Br M ! J) \<in> T_PS"
                  by (simp add: T_PS_def)
                let ?arg = "(entry M 0 0 + Joints M ! J + 1,
                              entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                             else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                             # tl (Br M ! J)"
                have NJ_eq: "?arg = NJ M J"
                  by (simp add: NJ_def npJ_def)
                have IH_J: "Lng (Red ?arg) = Lng ?arg"
                  using IH_bz[OF nz nmu refl refl refl refl _ tne J_in] c0 c1 arg_T
                  by (auto simp: c0 c1)
                have Largarg: "Lng ?arg = Lng (Br M ! J)"
                  using brJne by (simp add: NJ_def)
                show "Lng (Red (NJ M J)) = Lng (Br M ! J)"
                  using IH_J NJ_eq Largarg by (simp add: NJ_def)
              qed
              \<comment> \<open>Unfold Red M in this branch.\<close>
              have rM: "Red M = diagSeq 0 ?j1' @
                    concat (map (\<lambda>J.
                        (IncrFirst ^^ (Joints M ! J + 1
                            - (if entry (Br M ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
                          (Red ((entry M 0 0 + Joints M ! J + 1,
                                 entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                # tl (Br M ! J))))
                      [0..<Lng (Br M)])"
                using Red.psimps[OF dom] nz nmu c0 c1 tne
                by (simp add: Let_def)
              \<comment> \<open>Compute Lng step by step.\<close>
              \<comment> \<open>Abbreviate the branch arg.\<close>
              let ?f = "\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1
                            - (if entry (Br M ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
                          (Red ((entry M 0 0 + Joints M ! J + 1,
                                 entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                # tl (Br M ! J)))"
              have "Lng (Red M) = Suc ?j1' + Lng (concat (map ?f [0..<Lng (Br M)]))"
                by (simp add: rM)
              also have "\<dots> = Suc ?j1' + sum_list (map (Lng \<circ> ?f) [0..<Lng (Br M)])"
                by (simp add: length_concat map_map)
              also have "\<dots> = Suc ?j1' + sum_list (map (\<lambda>J. Lng (Br M ! J)) [0..<Lng (Br M)])"
              proof (rule arg_cong[where f="\<lambda>x. Suc ?j1' + x"])
                show "sum_list (map (Lng \<circ> ?f) [0..<Lng (Br M)]) =
                      sum_list (map (\<lambda>J. Lng (Br M ! J)) [0..<Lng (Br M)])"
                proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
                  fix J assume J: "J \<in> set [0..<Lng (Br M)]"
                  hence JBr': "J < Lng (Br M)" by simp
                  have NJ_J_eq: "(entry M 0 0 + Joints M ! J + 1,
                                  entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                                 else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                 # tl (Br M ! J) = NJ M J"
                    by (simp add: NJ_def npJ_def)
                  show "(Lng \<circ> ?f) J = Lng (Br M ! J)"
                  proof -
                    have fJ: "?f J = (IncrFirst ^^ (Joints M ! J + 1
                            - (if entry (Br M ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
                          (Red ((entry M 0 0 + Joints M ! J + 1,
                                 entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                # tl (Br M ! J)))"
                      by simp
                    have "(Lng \<circ> ?f) J = Lng (Red ((entry M 0 0 + Joints M ! J + 1,
                                 entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                # tl (Br M ! J)))"
                      using fJ by (simp add: Lng_funpow_IncrFirst)
                    also have "\<dots> = Lng (Red (NJ M J))"
                      by (simp only: NJ_J_eq)
                    also have "\<dots> = Lng (Br M ! J)"
                      using IH_NJ[OF JBr'] .
                    finally show ?thesis .
                  qed
                qed
              qed
              also have "\<dots> = Suc ?j1' + Lng (concat (Br M))"
              proof -
                have "sum_list (map (\<lambda>J. Lng (Br M ! J)) [0..<Lng (Br M)]) = Lng (concat (Br M))"
                proof -
                  have "map (\<lambda>J. Lng (Br M ! J)) [0..<Lng (Br M)] = map Lng (Br M)"
                    by (rule nth_equalityI) (auto simp: map_nth)
                  thus ?thesis by (simp add: length_concat)
                qed
                thus ?thesis by simp
              qed
              also have "\<dots> = Suc ?j1' + Lng (seg M (?j1' + 1) (Lng M - 1))"
                using trlt by (simp add: Br_def poper_concat_P)
              also have "\<dots> = Suc ?j1' + (Suc (Lng M - 1) - (?j1' + 1))"
                by (simp only: Lng_seg)
              also have "\<dots> = Lng M" using trlt LMpos by simp
              finally show ?thesis .
            qed
          next
            \<comment> \<open>Non-core case: M doesn't start at (0,0).\<close>
            case nc: False
            show ?thesis
            proof (cases "?m10 = 0")
              \<comment> \<open>Branch 4: m10=0 (but m00≠0).  Red M = Red(shift).\<close>
              case True
              have c0p: "0 < ?m00" using nc True by simp
              have rM: "Red M = Red (map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j))
                                        [0..<Suc ?j1])"
                using Red.psimps[OF dom] nz nmu nc True
                by (simp add: Let_def)
              have shift_T: "map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc ?j1] \<in> T_PS"
                by (simp add: T_PS_def)
              have IH': "Lng (Red (map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j))
                                       [0..<Suc ?j1])) =
                         Lng (map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc ?j1])"
                using IH_nc3[OF nz nmu refl refl refl refl nc True] shift_T
                by blast
              have "Lng (Red M) = Lng (map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j))
                                             [0..<Suc ?j1])"
                using rM IH' by simp
              also have "\<dots> = Lng M" using LMpos by simp
              finally show ?thesis .
            next
              \<comment> \<open>Branch 5: m10>0. Red M uses N = Red(diagSeq ++ IncrFirst M).\<close>
              case False
              hence c1p: "0 < ?m10" by simp
              let ?arg = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
              have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
                using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
              have arg_T: "?arg \<in> T_PS"
                using funpow_ne by (simp add: T_PS_def)
              have c1p': "?m10 \<noteq> 0" using c1p by simp
              have IH': "Lng (Red ?arg) = Lng ?arg"
                using IH_nc4[OF nz nmu refl refl refl refl nc c1p'] arg_T
                by blast
              have Larg: "Lng ?arg = ?m10 + Lng M"
                using c1p by (simp add: Lng_funpow_IncrFirst)
              have LN: "Lng (Red ?arg) = ?m10 + Lng M"
                using IH' Larg by simp
              have rM: "Red M = (let N = Red ?arg; jN = Lng N - 1 in
                         if ?m10 \<le> jN \<and> seg N ?m10 jN \<in> PT_PS then
                           map (\<lambda>j. (entry N 0 j - entry N 0 ?m10 + entry N 1 ?m10,
                                     entry N 1 j))
                               [?m10..<Suc jN]
                         else M)"
                using Red.psimps[OF dom] nz nmu nc c1p
                by (simp add: Let_def)
              show ?thesis
              proof (cases "?m10 \<le> Lng (Red ?arg) - 1 \<and>
                            seg (Red ?arg) ?m10 (Lng (Red ?arg) - 1) \<in> PT_PS")
                case True
                have "Red M = map (\<lambda>j. (entry (Red ?arg) 0 j
                                        - entry (Red ?arg) 0 ?m10
                                        + entry (Red ?arg) 1 ?m10,
                                        entry (Red ?arg) 1 j))
                                  [?m10..<Suc (Lng (Red ?arg) - 1)]"
                  using rM True by (simp add: Let_def)
                hence "Lng (Red M) = Suc (Lng (Red ?arg) - 1) - ?m10"
                  by (simp add: length_upt del: upt_Suc)
                also have "\<dots> = Lng M"
                  using LN LMpos by arith
                finally show ?thesis .
              next
                case nc5: False
                \<comment> \<open>cases False: ¬(?m10 ≤ Lng(Red arg)-1 ∧ seg...∈PT_PS)\<close>
                \<comment> \<open>Since LN, LMpos: m10 ≤ Lng(Red arg)-1 is TRUE, so seg...∉PT_PS.\<close>
                have jN_bound: "?m10 \<le> Lng (Red ?arg) - 1"
                  using LN LMpos by arith
                have seg_not_PT: "seg (Red ?arg) ?m10 (Lng (Red ?arg) - 1) \<notin> PT_PS"
                  using nc5 jN_bound by blast
                have "Red M = M"
                  using rM jN_bound seg_not_PT
                  by (simp add: Let_def)
                thus ?thesis by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using MT by blast
qed


lemma p_6_5_Lng_Red:
  assumes "M \<in> T_PS"
  shows "Lng (Red M) = Lng M"
  using assms by (rule m_6_5_Lng_Red)

end

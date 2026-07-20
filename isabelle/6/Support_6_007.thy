theory Support_6_007
  imports P_6_6_Red_leftend_1
begin

text \<open>m: §6.5 注[12] の左端 row-0 最小性（値不変量）.  monoT な入力 \<open>M\<close> に対し、
  その \<open>Red\<close> 出力は左端 \<open>entry (Red M) 0 0\<close> を row-0 の最小値として持つ:
  \<open>\<forall>k < Lng (Red M). entry (Red M) 0 0 \<le> entry (Red M) 0 k\<close>.

  これは PIECE3 の最終 residual（red-le-domain.md §10）。\<open>le0\<close>/\<open>nextrel0\<close> を一切含まない
  純粋な値の単調性なので、BC0/\<open>monoT_Red\<close> の変装ではなく**非循環**である
  （Red 出力が非monoT/zeroT でも成立する）。証明は @{thm [source] m_6_6_Red_leftend_1}
  と同じ Red.pinduct スケルトン。

  各枝:
  \<^item> zeroT / multiT: \<open>monoT M\<close> 仮定と矛盾するので vacuous。
  \<^item> core (m00=0,m10=0): \<open>Red M\<close> は \<open>diagSeq 0 _ @ _\<close> で始まるので
    \<open>entry (Red M) 0 0 = 0\<close>（nat の最小）、自明。trunk/non-trunk 両方を覆う。
  \<^item> non-core m10=0 (shift): \<open>Red M = Red (shiftRow0 M)\<close>、\<open>shiftRow0 M\<close> は core で monoT、
    IH を直接適用。
  \<^item> non-core m10>0 (rebase): \<open>Red M\<close> は \<open>N = Red (coreReduce M)\<close> の suffix \<open>seg N m10 jN\<close>
    を rebase したもの。\<open>then\<close> 枝では \<open>seg N m10 jN \<in> PT_PS\<close>（monoT）なので、その左端
    （= 位置 \<open>m10\<close> の row-0 値）が segment の row-0 最小（@{thm [source] entry0_ge_min}）。
    rebase はオフセットの加減算なので最小性を保つ。else（死枝[20]）では \<open>Red M = M\<close> が
    monoT なので @{thm [source] entry0_ge_min} で直接。\<close>

lemma m_6_5_Red_leftend_row0_min:
  assumes MT: "M \<in> T_PS" and monoM: "monoT M"
  shows "\<forall>k < Lng (Red M). entry (Red M) 0 0 \<le> entry (Red M) 0 k"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have "M \<in> T_PS \<longrightarrow> monoT M \<longrightarrow>
          (\<forall>k < Lng (Red M). entry (Red M) 0 0 \<le> entry (Red M) 0 k)"
    using domM
  proof (induction M rule: Red.pinduct)
    case (1 M)
    note dom    = 1(1)
    note IH_nc3 = 1(4)  \<comment> \<open>non-core m10=0 shift IH\<close>
    show ?case
    proof (rule impI, rule impI)
      assume MT': "M \<in> T_PS" and mono: "monoT M"
      have Mne: "M \<noteq> []" using MT' by (simp add: T_PS_def)
      have LMpos: "0 < Lng M" using Mne by (cases M) auto
      have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
      have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
      let ?j1  = "Lng M - 1"
      let ?j1' = "TrMax M"
      let ?m00 = "entry M 0 0"
      let ?m10 = "entry M 1 0"
      show "\<forall>k < Lng (Red M). entry (Red M) 0 0 \<le> entry (Red M) 0 k"
      proof (cases "?m00 = 0 \<and> ?m10 = 0")
        \<comment> \<open>Core case: \<open>Red M\<close> begins with \<open>diagSeq 0 _\<close>, so leftend row-0 value is 0.\<close>
        case core: True
        hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
        have e0: "entry (Red M) 0 0 = 0"
        proof (cases "?j1' = ?j1")
          \<comment> \<open>core trunk: Red M = diagSeq m10 (m10+j1) = diagSeq 0 j1.\<close>
          case True
          have rM: "Red M = diagSeq ?m10 (?m10 + ?j1)"
            using Red.psimps[OF dom] nz nmu c0 c1 True by (simp add: Let_def)
          have "entry (Red M) 0 0 = ?m10 + 0"
            using rM entry_diagSeq[where a="?m10" and b="?m10 + ?j1" and j=0 and i=0]
            by (simp add: LMpos)
          thus ?thesis using c1 by simp
        next
          \<comment> \<open>core non-trunk: Red M = diagSeq 0 j1' @ tail.\<close>
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
          have "entry (Red M) 0 0 = entry (diagSeq 0 ?j1' @ ?tail) 0 0"
            by (simp add: rM)
          also have "\<dots> = 0"
            by (rule entry_diagSeq_append_lo) simp
          finally show ?thesis .
        qed
        show ?thesis using e0 by simp
      next
        \<comment> \<open>Non-core case.\<close>
        case nc: False
        show ?thesis
        proof (cases "?m10 = 0")
          \<comment> \<open>Branch 4: m10=0 shift.  Red M = Red (shiftRow0 M); IH on shiftRow0 M.\<close>
          case True
          let ?shift = "map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc ?j1]"
          have rM: "Red M = Red ?shift"
            using Red.psimps[OF dom] nz nmu nc True by (simp add: Let_def)
          have shift_eq: "?shift = shiftRow0 M"
            using LMpos by (simp add: shiftRow0_def)
          have shift_T: "?shift \<in> T_PS" by (simp add: T_PS_def)
          have shift_mono: "monoT ?shift"
            using monoT_shiftRow0[OF MT' mono] shift_eq by simp
          have IH': "\<forall>k < Lng (Red ?shift). entry (Red ?shift) 0 0 \<le> entry (Red ?shift) 0 k"
            using IH_nc3[OF nz nmu refl refl refl refl nc True] shift_T shift_mono
            by blast
          show ?thesis using IH' rM by simp
        next
          \<comment> \<open>Branch 5: m10>0.\<close>
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
            \<comment> \<open>Else (dead branch [20]): Red M = M, monoT, use entry0_ge_min.\<close>
            case else_nc: False
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
            show ?thesis
            proof (rule allI, rule impI)
              fix k assume kL: "k < Lng (Red M)"
              have kLM: "k < Lng M" using kL rM_else by simp
              have "entry M 0 0 \<le> entry M 0 k"
                by (rule entry0_ge_min[OF MT' mono kLM])
              thus "entry (Red M) 0 0 \<le> entry (Red M) 0 k" using rM_else by simp
            qed
          next
            \<comment> \<open>Then (productive rebase): leftend = entry N 1 m10; suffix-min from seg PT_PS.\<close>
            case then_case: True
            have m10_le: "?m10 \<le> ?jN" using then_case by simp
            have segPT: "seg ?N ?m10 ?jN \<in> PT_PS" using then_case by simp
            have seg_mono: "monoT (seg ?N ?m10 ?jN)" using segPT by (simp add: PT_PS_def)
            have rM': "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10
                                          + entry ?N 1 ?m10,
                                          entry ?N 1 j))
                                   [?m10..<Suc ?jN]"
              using rM then_case by (simp add: Let_def del: upt_Suc)
            \<comment> \<open>Length of Red M = Suc jN - m10.\<close>
            have LredM: "Lng (Red M) = Suc ?jN - ?m10"
              using rM' by (simp add: length_upt del: upt_Suc)
            \<comment> \<open>The segment seg N m10 jN \<in> T_PS and its leftend (= N at m10) is the row-0 min.\<close>
            have seg_T: "seg ?N ?m10 ?jN \<in> T_PS" using segPT by (simp add: PT_PS_def)
            show ?thesis
            proof (rule allI, rule impI)
              fix k assume kL: "k < Lng (Red M)"
              have kbound: "k < Suc ?jN - ?m10" using kL LredM by simp
              \<comment> \<open>entry (Red M) 0 0 and entry (Red M) 0 k.\<close>
              have idx0: "[?m10..<Suc ?jN] ! 0 = ?m10"
                using m10_le by (simp add: nth_upt del: upt_Suc)
              have idxk: "[?m10..<Suc ?jN] ! k = ?m10 + k"
                using kbound by (simp add: nth_upt del: upt_Suc)
              have len0: "0 < length [?m10..<Suc ?jN]" using m10_le by (simp del: upt_Suc)
              have lenk: "k < length [?m10..<Suc ?jN]"
                using kbound by (simp add: length_upt del: upt_Suc)
              have e_rM0: "entry (Red M) 0 0
                            = entry ?N 0 ?m10 - entry ?N 0 ?m10 + entry ?N 1 ?m10"
              proof -
                have "(Red M) ! 0 = (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                          entry ?N 1 j)) ?m10"
                  using rM' len0 idx0 by (simp add: nth_map del: upt_Suc)
                thus ?thesis unfolding entry_def by simp
              qed
              have e_rMk: "entry (Red M) 0 k
                            = entry ?N 0 (?m10 + k) - entry ?N 0 ?m10 + entry ?N 1 ?m10"
              proof -
                have "(Red M) ! k = (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                          entry ?N 1 j)) (?m10 + k)"
                  using rM' lenk idxk by (simp add: nth_map del: upt_Suc)
                thus ?thesis unfolding entry_def by simp
              qed
              \<comment> \<open>Suffix-min: entry N 0 m10 \<le> entry N 0 (m10+k) via entry0_ge_min on the segment.\<close>
              have segk: "k < Lng (seg ?N ?m10 ?jN)"
                using kbound by (simp only: Lng_seg)
              have seg_min: "entry (seg ?N ?m10 ?jN) 0 0 \<le> entry (seg ?N ?m10 ?jN) 0 k"
                by (rule entry0_ge_min[OF seg_T seg_mono segk])
              have es0: "entry (seg ?N ?m10 ?jN) 0 0 = entry ?N 0 ?m10"
                using entry_seg[where M="?N" and a="?m10" and b="?jN" and i=0 and j=0]
                      m10_le by (simp only: Lng_seg) simp
              have esk: "entry (seg ?N ?m10 ?jN) 0 k = entry ?N 0 (?m10 + k)"
                using entry_seg[where M="?N" and a="?m10" and b="?jN" and i=0 and j=k] segk
                by simp
              have suffmin: "entry ?N 0 ?m10 \<le> entry ?N 0 (?m10 + k)"
                using seg_min es0 esk by simp
              \<comment> \<open>Conclude via monotone rebase (subtract entry N 0 m10, add entry N 1 m10).\<close>
              show "entry (Red M) 0 0 \<le> entry (Red M) 0 k"
                using e_rM0 e_rMk suffmin by linarith
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using MT monoM by blast
qed

end

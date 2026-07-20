theory Support_6_068
  imports Frontier_6_089
begin

lemma m_6_5_Red_rebase:
  "M \<in> T_PS \<Longrightarrow> RedCondA M \<Longrightarrow> \<not> multiT M \<Longrightarrow>
   Red M = map (\<lambda>j. (entry M 0 j - entry M 0 0 + entry M 1 0, entry M 1 j))
               [0..<Lng M]"
proof (induction M rule: measure_induct_rule[where f = Lng])
  case (less M)
  note MT = less.prems(1)
  note condA = less.prems(2)
  note nmu = less.prems(3)
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  show ?case
  proof (cases "zeroT M")
    case z: True
    have rM: "Red M = [(0, 0)]" using Red.psimps[OF dom] z by simp
    have L1: "Lng M = 1" and e10: "entry M 1 0 = 0" using z by (simp_all add: zeroT_def)
    have "map (\<lambda>j. (entry M 0 j - entry M 0 0 + entry M 1 0, entry M 1 j)) [0..<Lng M]
          = [(0, 0)]" using L1 e10 by simp
    thus ?thesis using rM by simp
  next
    case nz: False
    have mono: "monoT M" using nz nmu by (simp add: multiT_def)
    show ?thesis
    proof (cases "entry M 1 0 = 0")
      case m10z: True
      show ?thesis
      proof (cases "entry M 0 0 = 0")
        case c0: True
        have redid: "Red M = M"
          by (rule Red_rebase_core[OF MT condA mono c0 m10z less.IH])
        have maps: "map (\<lambda>j. (entry M 0 j - entry M 0 0 + entry M 1 0, entry M 1 j))
                        [0..<Lng M]
              = map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<Lng M]"
        proof (rule map_cong[OF refl])
          fix x assume "x \<in> set [0..<Lng M]"
          have e1z: "entry M (Suc 0) 0 = 0" using m10z by simp
          show "(entry M 0 x - entry M 0 0 + entry M 1 0, entry M 1 x)
                = (entry M 0 x, entry M 1 x)" using c0 e1z by simp
        qed
        have RHS: "map (\<lambda>j. (entry M 0 j - entry M 0 0 + entry M 1 0, entry M 1 j))
                       [0..<Lng M] = M"
          by (rule trans[OF maps map_entry_id])
        show ?thesis by (simp only: redid RHS)
      next
        case c0n: False
        let ?sh = "map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Suc (Lng M - 1)]"
        have ncore: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" using c0n by simp
        have rM: "Red M = Red ?sh"
          using Red.psimps[OF dom] nz nmu ncore m10z by (simp add: Let_def)
        have sheq: "?sh = shiftRow0 M" using LMpos by (simp add: shiftRow0_def)
        have shne: "shiftRow0 M \<noteq> []" using LMpos by (simp add: shiftRow0_def)
        have shT: "shiftRow0 M \<in> T_PS" using shne by (simp add: T_PS_def)
        have shMono: "monoT (shiftRow0 M)" by (rule monoT_shiftRow0[OF MT mono])
        have shA: "RedCondA (shiftRow0 M)" by (rule RedCondA_shiftRow0[OF MT mono condA])
        have sh00: "entry (shiftRow0 M) 0 0 = 0" using entry_shiftRow0_0[OF LMpos] by simp
        have sh10: "entry (shiftRow0 M) 1 0 = 0"
          using entry_shiftRow0_1[OF LMpos] m10z by simp
        have IH': "\<And>X. Lng X < Lng (shiftRow0 M) \<Longrightarrow> X \<in> T_PS \<Longrightarrow> RedCondA X
                    \<Longrightarrow> \<not> multiT X
                    \<Longrightarrow> Red X = map (\<lambda>j. (entry X 0 j - entry X 0 0 + entry X 1 0,
                                           entry X 1 j)) [0..<Lng X]"
          using less.IH by simp
        have redsh: "Red (shiftRow0 M) = shiftRow0 M"
          by (rule Red_rebase_core[OF shT shA shMono sh00 sh10 IH'])
        have "Red M = shiftRow0 M" using rM sheq redsh by simp
        moreover have
          "map (\<lambda>j. (entry M 0 j - entry M 0 0 + entry M 1 0, entry M 1 j)) [0..<Lng M]
           = shiftRow0 M" using m10z by (simp add: shiftRow0_def)
        ultimately show ?thesis by simp
      qed
    next
      case m10p: False
      have pos: "0 < entry M 1 0" using m10p by simp
      let ?m = "entry M 1 0"  let ?c0 = "entry M 0 0"
      let ?A = "diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
      let ?f = "\<lambda>p. (fst p - ?c0 + ?m, snd p)"
      let ?N = "Red ?A"
      let ?jN = "Lng ?N - 1"
      have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
      have LA: "Lng ?A = ?m + Lng M" using Ld by simp
      have LApos: "0 < Lng ?A" using LA LMpos by simp
      have Ane: "?A \<noteq> []" using LApos length_greater_0_conv by blast
      have AT: "?A \<in> T_PS" using Ane by (simp add: T_PS_def)
      have ncore: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" using m10p by simp
      have rM: "Red M = (let N = ?N; jN = ?jN in
                 if ?m \<le> jN \<and> seg N ?m jN \<in> PT_PS then
                   map (\<lambda>j. (entry N 0 j - entry N 0 ?m + entry N 1 ?m,
                             entry N 1 j))
                       [?m..<Suc jN]
                 else M)"
        using Red.psimps[OF dom] nz nmu ncore m10p by (simp add: Let_def)
      have Nval: "?N = diagSeq 0 (?m + TrMax M)
                    @ concat (map (\<lambda>J. map ?f (Br M ! J)) [0..<Lng (Br M)])"
        by (rule Red_coreReduce_eq[OF MT condA mono pos less.IH])
      have LN: "Lng ?N = ?m + Lng M" using m_6_5_Lng_Red[OF AT] LA by simp
      have jNval: "?jN = ?m + Lng M - 1" using LN by simp
      have mjN: "?m \<le> ?jN" using jNval LMpos by linarith
      have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
      \<comment> \<open>the M-image inside N: seg N m jN = map f M\<close>
      have mapfM: "map ?f M = diagSeq ?m (?m + TrMax M)
                     @ concat (map (\<lambda>J. map ?f (Br M ! J)) [0..<Lng (Br M)])"
      proof -
        have tk: "map ?f (take (TrMax M + 1) M) = diagSeq ?m (?m + TrMax M)"
        proof (rule nth_equalityI)
          have tkL: "TrMax M + 1 \<le> Lng M" using tb LMpos by linarith
          show "length (map ?f (take (TrMax M + 1) M))
                = length (diagSeq ?m (?m + TrMax M))"
            using tkL by (simp add: diagSeq_def)
        next
          fix k assume "k < length (map ?f (take (TrMax M + 1) M))"
          hence kTr: "k \<le> TrMax M" by simp
          have kM: "k < Lng M" using kTr tb LMpos by linarith
          have ent: "entry M 0 k = ?c0 + k \<and> entry M 1 k = ?m + k"
            by (rule trunk_entries_offset[OF MT condA kTr])
          have Mk: "M ! k = (?c0 + k, ?m + k)"
            using ent by (simp add: entry_def prod_eq_iff)
          have lhs: "map ?f (take (TrMax M + 1) M) ! k = (?m + k, ?m + k)"
            using kTr kM Mk by simp
          have rhs: "diagSeq ?m (?m + TrMax M) ! k = (?m + k, ?m + k)"
            using kTr by (simp add: diagSeq_def del: upt_Suc)
          show "map ?f (take (TrMax M + 1) M) ! k = diagSeq ?m (?m + TrMax M) ! k"
            using lhs rhs by simp
        qed
        have dr: "map ?f (drop (TrMax M + 1) M)
                  = concat (map (\<lambda>J. map ?f (Br M ! J)) [0..<Lng (Br M)])"
        proof (cases "TrMax M = Lng M - 1")
          case True
          have "drop (TrMax M + 1) M = []" using True LMpos by simp
          moreover have "Br M = []" using True by (simp add: Br_def)
          ultimately show ?thesis by simp
        next
          case False
          let ?S = "seg M (TrMax M + 1) (Lng M - 1)"
          have brQ: "Br M = P ?S" using False by (simp add: Br_def)
          have segdrop: "?S = drop (TrMax M + 1) M"
            by (rule seg_to_last_eq_drop[OF LMpos])
          have ccS: "concat (Br M) = ?S" using brQ idxsum_concat_P[of ?S] by simp
          have "map ?f (drop (TrMax M + 1) M) = map ?f (concat (Br M))"
            using segdrop ccS by simp
          also have "\<dots> = concat (map (map ?f) (Br M))" by (simp add: map_concat)
          also have "\<dots> = concat (map (\<lambda>J. map ?f (Br M ! J)) [0..<Lng (Br M)])"
          proof -
            have "map (map ?f) (map (nth (Br M)) [0..<length (Br M)])
                  = map (\<lambda>J. map ?f (Br M ! J)) [0..<length (Br M)]"
              by (simp add: o_def)
            hence "map (map ?f) (Br M) = map (\<lambda>J. map ?f (Br M ! J)) [0..<length (Br M)]"
              by (simp add: map_nth)
            thus ?thesis by simp
          qed
          finally show ?thesis .
        qed
        have "map ?f M = map ?f (take (TrMax M + 1) M) @ map ?f (drop (TrMax M + 1) M)"
          by (metis append_take_drop_id map_append)
        thus ?thesis using tk dr by simp
      qed
      have segN: "seg ?N ?m ?jN = map ?f M"
      proof -
        have segdropN: "seg ?N ?m ?jN = drop ?m ?N"
        proof -
          have "0 < Lng ?N" using LN LMpos by simp
          thus ?thesis using seg_to_last_eq_drop[of ?N ?m] by simp
        qed
        have Ldd: "Lng (diagSeq 0 (?m + TrMax M)) = ?m + TrMax M + 1"
          by (simp del: upt_Suc)
        have mle: "?m \<le> ?m + TrMax M" by simp
        have "drop ?m ?N = drop ?m (diagSeq 0 (?m + TrMax M))
                @ concat (map (\<lambda>J. map ?f (Br M ! J)) [0..<Lng (Br M)])"
          using Nval Ldd by simp
        also have "\<dots> = diagSeq ?m (?m + TrMax M)
                @ concat (map (\<lambda>J. map ?f (Br M ! J)) [0..<Lng (Br M)])"
          using drop_diagSeq[OF mle] by simp
        finally show ?thesis using segdropN mapfM by simp
      qed
      \<comment> \<open>the slice is a productive mono tail\<close>
      have fcomp: "map ?f M = (IncrFirst ^^ ?m) (shiftRow0 M)"
      proof -
        have sh: "shiftRow0 M = map (\<lambda>p. (fst p - ?c0, snd p)) M"
          using rebase_as_pair_map[of M ?c0 0] by (simp add: shiftRow0_def)
        have "(IncrFirst ^^ ?m) (shiftRow0 M)
              = map (\<lambda>p. (fst p + ?m, snd p)) (map (\<lambda>p. (fst p - ?c0, snd p)) M)"
          using sh funpow_IncrFirst_as_map by simp
        also have "\<dots> = map ?f M" by simp
        finally show ?thesis by simp
      qed
      have monoF: "monoT (map ?f M)"
      proof -
        have m1: "monoT (shiftRow0 M)" by (rule monoT_shiftRow0[OF MT mono])
        have "monoT ((IncrFirst ^^ ?m) (shiftRow0 M))"
          by (induction ?m) (use m1 in \<open>simp_all add: IncrFirst_monoT_eq\<close>)
        thus ?thesis using fcomp by simp
      qed
      have fne: "map ?f M \<noteq> []" using Mne by simp
      have fT: "map ?f M \<in> T_PS" using fne by (simp add: T_PS_def)
      have segPT: "seg ?N ?m ?jN \<in> PT_PS" using segN fT monoF by (simp add: PT_PS_def)
      have rM': "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m + entry ?N 1 ?m,
                                   entry ?N 1 j)) [?m..<Suc ?jN]"
        using rM mjN segPT by (simp add: Let_def del: upt_Suc)
      \<comment> \<open>the anchor entries: position m sits in the diagonal prefix of N\<close>
      have eNm: "entry ?N 0 ?m = ?m \<and> entry ?N 1 ?m = ?m"
      proof -
        have mlt: "?m < ?m + TrMax M + 1" by simp
        have "?N ! ?m = diagSeq 0 (?m + TrMax M) ! ?m"
          using Nval mlt by (simp add: nth_append del: upt_Suc)
        also have "\<dots> = (?m, ?m)" using mlt by (simp add: diagSeq_def del: upt_Suc)
        finally show ?thesis by (simp add: entry_def)
      qed
      \<comment> \<open>row-0 values in the window are at least m, so the rebase is the identity\<close>
      have geW: "\<And>j. ?m \<le> j \<Longrightarrow> j \<le> ?jN \<Longrightarrow> ?m \<le> entry ?N 0 j"
      proof -
        fix j assume mj: "?m \<le> j" and jj: "j \<le> ?jN"
        define k where "k = j - ?m"
        have jk: "j = ?m + k" using mj k_def by simp
        have kM: "k < Lng M" using jj jNval jk LMpos by linarith
        have "entry ?N 0 j = fst ((map ?f M) ! k)"
        proof -
          have "?N ! j = (seg ?N ?m ?jN) ! k"
          proof -
            have "seg ?N ?m ?jN ! k = ?N ! (?m + k)"
              unfolding seg_def using jj jk by (simp add: nth_map del: upt_Suc)
            thus ?thesis using jk by simp
          qed
          thus ?thesis using segN by (simp add: entry_def)
        qed
        moreover have "fst ((map ?f M) ! k) = entry M 0 k - ?c0 + ?m"
          using kM by (simp add: entry_def)
        ultimately show "?m \<le> entry ?N 0 j" by simp
      qed
      have rM'': "Red M = map (\<lambda>j. ?N ! j) [?m..<Suc ?jN]"
      proof -
        have "map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m + entry ?N 1 ?m, entry ?N 1 j))
                  [?m..<Suc ?jN]
              = map (\<lambda>j. ?N ! j) [?m..<Suc ?jN]"
        proof (rule map_cong[OF refl])
          fix j assume "j \<in> set [?m..<Suc ?jN]"
          hence mj: "?m \<le> j" and jj: "j \<le> ?jN" by auto
          have jL: "j < Lng ?N" using jj LN LMpos by linarith
          have "entry ?N 0 j - entry ?N 0 ?m + entry ?N 1 ?m = entry ?N 0 j"
            using eNm geW[OF mj jj] by simp
          thus "(entry ?N 0 j - entry ?N 0 ?m + entry ?N 1 ?m, entry ?N 1 j) = ?N ! j"
            by (simp add: entry_def prod_eq_iff)
        qed
        thus ?thesis using rM' by simp
      qed
      have "Red M = seg ?N ?m ?jN" using rM'' by (simp add: seg_def)
      hence redval: "Red M = map ?f M" using segN by simp
      have "map (\<lambda>j. (entry M 0 j - entry M 0 0 + entry M 1 0, entry M 1 j)) [0..<Lng M]
            = map ?f M" by (rule rebase_as_pair_map)
      thus ?thesis using redval by simp
    qed
  qed
qed

end

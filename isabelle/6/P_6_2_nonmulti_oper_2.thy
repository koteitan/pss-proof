theory P_6_2_nonmulti_oper_2
  imports P_6_2_nonmulti_oper_1
begin

text \<open>m: 命題（非複項性と基本列の関係）(2) — singleton \<open>[M[n]]\<close>.\<close>

lemma m_6_2_nonmulti_oper_2:
  assumes M: "M \<in> T_PS" and n: "n \<ge> 1" and nm: "\<not> multiT M"
    and H: "\<not> nextR M 0 0 (Lng M - 1) \<or> entry M 1 (Lng M - 1) > 0"
  shows "P ((M::pairseq)[n]) = [(M[n])]"
proof -
  let ?j1 = "Lng M - 1"
  have "\<not> (multiT (M[n]) \<and> 1 < Lng (M[n]))"
  proof (cases "Lng M = 1")
    case True
    hence "?j1 = 0" by simp
    hence "M[n] = M" by (simp add: oper_def Let_def)
    thus ?thesis using nm by simp
  next
    case False
    have L: "1 < Lng M" using M False by (cases M) (auto simp: T_PS_def)
    have nz: "?j1 \<noteq> 0" using L by simp
    \<comment> \<open>mono: row-0 strictly increases away from 0\<close>
    have mono: "\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j"
      using m_6_2_multi_crit_12[OF M] nm by simp
    have j1L: "?j1 < Lng M" using L by simp
    have e0j1: "entry M 0 ?j1 > 0"
    proof -
      have "entry M 0 0 < entry M 0 ?j1" using mono[rule_format, of ?j1] nz j1L by simp
      thus ?thesis by simp
    qed
    have notzero: "\<not> (entry M 0 ?j1 = 0 \<and> entry M 1 ?j1 = 0)" using e0j1 by simp
    show ?thesis
    proof (cases "hasParent M (idx1 M ?j1) ?j1")
      case noparent: False
      \<comment> \<open>degenerate: \<open>M[n] = Pred M\<close>, non-multi\<close>
      have "M[n] = Pred M"
        using notzero noparent nz by (auto simp: oper_def Let_def)
      moreover have "\<not> multiT (Pred M)" by (rule nonmulti_Pred[OF M nm L])
      ultimately show ?thesis by simp
    next
      case haspar: True
      let ?i1 = "idx1 M ?j1"
      let ?j0 = "parent M ?i1 ?j1"
      let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
      let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
      have parR: "nextR M ?i1 ?j0 ?j1"
        using haspar unfolding hasParent_def parent_def by (rule theI')
      have j0lt: "?j0 < ?j1" using parR by (cases "?i1 = 0")
          (auto simp: nextR_def nextrel0_def nextrel1_def)
      have op: "M[n] = take ?j0 M @
          concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1))
                                [?j0..<?j1]) [0..<n])"
        using poper_oper_expand[OF L notzero haspar, of n] by (simp add: Let_def)
      \<comment> \<open>the saving fact: when the parent is index 0, the row-0 increment is positive\<close>
      have j0d0: "?j0 = 0 \<Longrightarrow> 0 < ?d0"
      proof -
        assume j00: "?j0 = 0"
        have "?i1 \<noteq> 0"
        proof
          assume "?i1 = 0"
          hence "nextR M 0 0 ?j1" using parR j00 by simp
          \<comment> \<open>then \<open>i1 = 0\<close> means \<open>entry M 1 ?j1 = 0\<close>, contradicting \<open>H\<close>\<close>
          moreover have "entry M 1 ?j1 = 0"
            using \<open>?i1 = 0\<close> by (simp add: idx1_def split: if_split_asm)
          ultimately show False using H by simp
        qed
        hence i11: "0 < ?i1" by simp
        have "entry M 0 ?j0 < entry M 0 ?j1"
          using mono[rule_format, of ?j1] j00 nz L by simp
        thus "0 < ?d0" using i11 by simp
      qed
      \<comment> \<open>show \<open>M[n]\<close> is non-multi via the row-0 strict-minimum criterion\<close>
      let ?N = "M[n]"
      have NT: "?N \<in> T_PS" using poper_oper_nth0[OF M L n] by (simp add: T_PS_def)
      \<comment> \<open>row-0 head equals \<open>entry M 0 0\<close>\<close>
      have hd0: "entry ?N 0 0 = entry M 0 0"
        using poper_oper_nth0[OF M L n] by (simp add: entry_def)
      \<comment> \<open>express the row-0 value list of \<open>?N\<close>\<close>
      let ?A = "map (entry M 0) [0..<?j0]"
      let ?B = "concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [0..<n])"
      have j0L: "?j0 \<le> Lng M" using j0lt nz L by linarith
      have fstN: "map fst ?N = ?A @ ?B"
      proof -
        have "map fst (take ?j0 M) = ?A"
        proof (rule nth_equalityI)
          show "length (map fst (take ?j0 M)) = length ?A" using j0L by simp
        next
          fix i assume ilen: "i < length (map fst (take ?j0 M))"
          hence ilt: "i < ?j0" using j0L by simp
          have itk: "i < length (take ?j0 M)" using ilen by simp
          have "map fst (take ?j0 M) ! i = fst (take ?j0 M ! i)"
            using itk by (simp add: nth_map)
          also have "\<dots> = fst (M ! i)" using ilt by (simp add: nth_take)
          also have "\<dots> = entry M 0 i" by (simp add: entry_def)
          also have "\<dots> = ?A ! i" using ilt by simp
          finally show "map fst (take ?j0 M) ! i = ?A ! i" .
        qed
        moreover have "map fst (concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0,
                            entry M 1 j + k * ?d1)) [?j0..<?j1]) [0..<n])) = ?B"
          by (simp add: map_concat o_def)
        ultimately show ?thesis using op by simp
      qed
      \<comment> \<open>row-0 value list of \<open>?N\<close> is \<open>(entry M 0 0) # tail\<close> with all tail values larger\<close>
      have headM: "map fst ?N \<noteq> []"
        using poper_oper_nth0[OF M L n] by (cases ?N) auto
      \<comment> \<open>the key: every element of the tail strictly exceeds \<open>entry M 0 0\<close>\<close>
      have tailgt: "\<forall>x \<in> set (tl (map fst ?N)). entry M 0 0 < x"
      proof (cases "0 < ?j0")
        case j0pos: True
        \<comment> \<open>prefix non-empty: tail \<open>= tl ?A @ ?B\<close>\<close>
        have Ane: "?A \<noteq> []" using j0pos by simp
        have tleq: "tl (map fst ?N) = tl ?A @ ?B" using fstN Ane by simp
        show ?thesis
        proof
          fix x assume "x \<in> set (tl (map fst ?N))"
          hence "x \<in> set (tl ?A) \<or> x \<in> set ?B" using tleq by auto
          thus "entry M 0 0 < x"
          proof
            assume "x \<in> set (tl ?A)"
            then obtain p where p: "p \<in> set [Suc 0..<?j0]" and xeq: "x = entry M 0 p"
              using j0pos by (cases ?j0) (auto simp: map_tl[symmetric] upt_conv_Cons)
            have prng: "0 < p \<and> p < ?j0" using p by auto
            hence "p < Lng M" using j0lt nz L by linarith
            hence "entry M 0 0 < entry M 0 p" using mono[rule_format, of p] prng by simp
            thus ?thesis using xeq by simp
          next
            assume "x \<in> set ?B"
            then obtain kk where kk: "kk \<in> set [0..<n]"
              and xin: "x \<in> set (map (\<lambda>j. entry M 0 j + kk * ?d0) [?j0..<?j1])"
              by (auto simp: set_concat)
            from xin obtain j where jrng: "j \<in> set [?j0..<?j1]"
              and xeq: "x = entry M 0 j + kk * ?d0" by auto
            from jrng have jrng': "?j0 \<le> j \<and> j < ?j1" by auto
            have jpos: "0 < j" using jrng' j0pos by simp
            have jL: "j < Lng M" using jrng' j0lt nz L by linarith
            hence "entry M 0 0 < entry M 0 j" using mono[rule_format, of j] jpos by simp
            thus ?thesis using xeq by simp
          qed
        qed
      next
        case j00: False
        hence j0z: "?j0 = 0" by simp
        hence d0pos: "0 < ?d0" by (rule j0d0)
        have Ane: "?A = []" using j0z by simp
        \<comment> \<open>split \<open>?B\<close> into block 0 and the rest\<close>
        have nlist: "[0..<n] = 0 # [Suc 0..<n]" using n by (simp add: upt_conv_Cons)
        have blk0: "map (\<lambda>j. entry M 0 j + 0 * ?d0) [?j0..<?j1] = map (entry M 0) [0..<?j1]"
          using j0z by simp
        have Beq: "?B = map (entry M 0) [0..<?j1] @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
        proof -
          have "?B = concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) (0 # [Suc 0..<n]))"
            by (simp only: nlist)
          also have "\<dots> = map (\<lambda>j. entry M 0 j + 0 * ?d0) [?j0..<?j1] @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
            by simp
          also have "\<dots> = map (entry M 0) [0..<?j1] @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
            by (simp only: blk0)
          finally show ?thesis .
        qed
        have j1ne: "[0..<?j1] \<noteq> []" using nz by simp
        have tlblk0: "tl (map (entry M 0) [0..<?j1]) = map (entry M 0) [Suc 0..<?j1]"
          using nz by (cases ?j1) (auto simp: upt_conv_Cons)
        have tleq: "tl (map fst ?N) = map (entry M 0) [Suc 0..<?j1] @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
        proof -
          have "map fst ?N = map (entry M 0) [0..<?j1] @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
            using fstN Ane Beq by simp
          hence "tl (map fst ?N) = tl (map (entry M 0) [0..<?j1]) @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
            using j1ne by (simp add: tl_append2)
          thus ?thesis by (simp only: tlblk0)
        qed
        show ?thesis
        proof
          fix x assume "x \<in> set (tl (map fst ?N))"
          hence "x \<in> set (map (entry M 0) [Suc 0..<?j1]) \<or>
                 x \<in> set (concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n]))"
            using tleq by auto
          thus "entry M 0 0 < x"
          proof
            assume "x \<in> set (map (entry M 0) [Suc 0..<?j1])"
            then obtain p where p: "p \<in> set [Suc 0..<?j1]" and xeq: "x = entry M 0 p" by auto
            have prng: "0 < p \<and> p < ?j1" using p by auto
            hence "p < Lng M" using nz L by linarith
            hence "entry M 0 0 < entry M 0 p" using mono[rule_format, of p] prng by simp
            thus ?thesis using xeq by simp
          next
            assume "x \<in> set (concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n]))"
            then obtain kk where kk: "kk \<in> set [Suc 0..<n]"
              and xin: "x \<in> set (map (\<lambda>j. entry M 0 j + kk * ?d0) [?j0..<?j1])"
              by (auto simp: set_concat)
            from xin obtain j where jrng: "j \<in> set [?j0..<?j1]"
              and xeq: "x = entry M 0 j + kk * ?d0" by auto
            from jrng have jrng': "?j0 \<le> j \<and> j < ?j1" by auto
            have kkpos: "0 < kk" using kk by auto
            have jL: "j < Lng M" using jrng' j0lt nz L by linarith
            show "entry M 0 0 < x"
            proof (cases "0 < j")
              case True
              hence "entry M 0 0 < entry M 0 j" using mono[rule_format, of j] jL by simp
              thus ?thesis using xeq by simp
            next
              case False
              hence "j = 0" by simp
              hence "x = entry M 0 0 + kk * ?d0" using xeq by simp
              moreover have "0 < kk * ?d0" using kkpos d0pos by simp
              ultimately show ?thesis by simp
            qed
          qed
        qed
      qed
      have strict: "\<forall>k. 0 < k \<and> k < Lng ?N \<longrightarrow> entry M 0 0 < entry ?N 0 k"
      proof (intro allI impI)
        fix k assume k: "0 < k \<and> k < Lng ?N"
        have klen: "length (tl (map fst ?N)) = Lng ?N - 1" by (simp add: length_map)
        have kml: "k - 1 < length (tl (map fst ?N))" using k klen by linarith
        have ksuc: "Suc (k - 1) = k" using k by simp
        have "entry ?N 0 k = (map fst ?N) ! k" using k by (simp add: entry_def)
        also have "\<dots> = (map fst ?N) ! Suc (k - 1)" using ksuc by simp
        also have "\<dots> = (tl (map fst ?N)) ! (k - 1)" using kml by (simp add: nth_tl)
        also have "\<dots> \<in> set (tl (map fst ?N))" using kml by (rule nth_mem)
        finally show "entry M 0 0 < entry ?N 0 k" using tailgt by blast
      qed
      have "\<forall>j. 0 < j \<and> j < Lng ?N \<longrightarrow> entry ?N 0 0 < entry ?N 0 j"
        using strict hd0 by simp
      hence "\<not> multiT ?N" using m_6_2_multi_crit_12[OF NT] by simp
      thus ?thesis by simp
    qed
  qed
  thus ?thesis by (rule poper_P_nonmulti)
qed


lemma p_6_2_nonmulti_oper_2:
  assumes "M \<in> T_PS" "n \<ge> 1" "\<not> multiT M"
    "\<not> nextR M 0 0 (Lng M - 1) \<or> entry M 1 (Lng M - 1) > 0"
  shows "P ((M::pairseq)[n]) = [(M[n])]"
  using assms by (rule m_6_2_nonmulti_oper_2)

end

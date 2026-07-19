theory Support_6_073
  imports P_6_6_reduced_oper
begin

section \<open>§6.5 命題（\<open>Red\<close>と基本列の可換性） — A4 final form\<close>

text \<open>Route (INVERTS the article's order, no n-induction): with
  \<open>Y = Red M = rebaseRow0 c m M\<close> (closed form, \<open>c = M\<^bsub>0,0\<^esub>\<close>, \<open>m = M\<^bsub>1,0\<^esub>\<close>),
  \<^item> \<open>Y[n] = rebaseRow0 c m (M[n])\<close> — \<open>oper\<close> commutes with the uniform row-0
    rebase (the discriminator entries/parents agree via the floor congruence,
    and \<open>d\<^sub>0\<close> is a row-0 difference, hence rebase-invariant);
  \<^item> \<open>Red (M[n]) = Red (rebaseRow0 c m (M[n]))\<close> — @{thm [source] cdn_red_cong},
    since all row-0 entries of \<open>M[n]\<close> stay \<open>\<ge> c\<close>;
  \<^item> \<open>Red (Y[n]) = Y[n]\<close> — \<open>Y \<in> RT\<^sub>PS\<close> by idempotency and
    今日の @{thm [source] m_6_6_reduced_oper} (reducedness preserved by oper
    on ALL of \<open>RT\<^sub>PS\<close>).
  Chaining: \<open>Red (M[n]) = Red (Y[n]) = Y[n] = (Red M)[n]\<close>.\<close>

text \<open>Floor congruence: a uniform row-0 rebase above a global floor is a
  \<open>congR\<close>-congruence (via @{thm [source] nextrel0_rebaseRow0_eq}).\<close>

lemma congR_rebaseRow0:
  assumes lb: "\<And>j. j < Lng M \<Longrightarrow> c \<le> entry M 0 j"
  shows "congR M (rebaseRow0 c d M)"
  unfolding congR_def
proof (intro conjI allI impI)
  show "Lng M = Lng (rebaseRow0 c d M)" by simp
next
  show "nextrel0 M = nextrel0 (rebaseRow0 c d M)"
    by (rule ext, rule ext) (simp add: nextrel0_rebaseRow0_eq[OF lb])
next
  fix j assume "j < Lng (rebaseRow0 c d M)"
  hence "j < Lng M" by simp
  thus "entry M 1 j = entry (rebaseRow0 c d M) 1 j"
    by (simp add: rebaseRow0_def entry_def)
qed

text \<open>All pairs of \<open>M[n]\<close> keep row 0 above the mono floor \<open>c = M\<^bsub>0,0\<^esub>\<close>:
  the prefix and \<open>Pred\<close>/identity cases are pairs of \<open>M\<close>; tiling blocks shift
  row 0 upward by \<open>k\<cdot>d\<^sub>0\<close>.\<close>

lemma oper_row0_floor:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and p: "p \<in> set ((M::pairseq)[n])"
  shows "entry M 0 0 \<le> fst p"
proof -
  let ?c = "entry M 0 0"
  have inM: "\<And>q. q \<in> set M \<Longrightarrow> ?c \<le> fst q"
  proof -
    fix q assume "q \<in> set M"
    then obtain j where jL: "j < Lng M" and qj: "q = M ! j"
      by (auto simp: in_set_conv_nth)
    have "?c \<le> entry M 0 j" by (rule entry0_ge_min[OF MT mono jL])
    thus "?c \<le> fst q" using qj by (simp add: entry_def)
  qed
  show ?thesis
  proof (cases "Lng M - 1 = 0
                \<or> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
                \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)")
    case True
    have "(M::pairseq)[n] = M \<or> (M::pairseq)[n] = Pred M"
      using True by (auto simp: oper_def Let_def)
    moreover have "set (Pred M) \<subseteq> set M"
      by (auto simp: Pred_def dest: in_set_butlastD)
    ultimately have "p \<in> set M" using p by auto
    thus ?thesis by (rule inM)
  next
    case False
    hence ndeg: "Lng M - 1 \<noteq> 0"
      and nz: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
      and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)" by auto
    have L: "1 < Lng M" using ndeg by linarith
    let ?j1 = "Lng M - 1"
    define i1 where "i1 = idx1 M ?j1"
    define j0 where "j0 = parent M i1 ?j1"
    define d0 where "d0 = (if 0 < i1 then entry M 0 ?j1 - entry M 0 j0 else 0)"
    define d1 where "d1 = (if 1 < i1 then entry M 1 ?j1 - entry M 1 j0 else 0)"
    have exp: "M[n] = take j0 M
        @ concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j + k * d1))
                               [j0..<?j1]) [0..<n])"
      using poper_oper_expand[OF L nz hp, of n]
      unfolding Let_def i1_def[symmetric] j0_def[symmetric]
                d0_def[symmetric] d1_def[symmetric] .
    have "p \<in> set (take j0 M)
          \<or> p \<in> set (concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0,
                                                 entry M 1 j + k * d1))
                                        [j0..<?j1]) [0..<n]))"
      using p[unfolded exp] by (simp only: set_append) blast
    thus ?thesis
    proof
      assume "p \<in> set (take j0 M)"
      hence "p \<in> set M" by (rule in_set_takeD)
      thus ?thesis by (rule inM)
    next
      assume "p \<in> set (concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0,
                                                    entry M 1 j + k * d1))
                                           [j0..<?j1]) [0..<n]))"
      then obtain k where pk: "p \<in> set (map (\<lambda>j. (entry M 0 j + k * d0,
                                                    entry M 1 j + k * d1))
                                            [j0..<?j1])"
        by auto
      from pk obtain j where jset: "j \<in> set [j0..<?j1]"
          and pv: "p = (entry M 0 j + k * d0, entry M 1 j + k * d1)"
        by auto
      have jL: "j < Lng M" using jset by auto
      have "?c \<le> entry M 0 j" by (rule entry0_ge_min[OF MT mono jL])
      thus ?thesis using pv by simp
    qed
  qed
qed

text \<open>\<open>oper\<close> commutes with the row-0 rebase above the mono floor.\<close>

lemma oper_rebase_commute:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
  shows "(rebaseRow0 (entry M 0 0) m M)[n]
         = rebaseRow0 (entry M 0 0) m ((M::pairseq)[n])"
proof -
  let ?c = "entry M 0 0"
  let ?f = "\<lambda>p. (fst p - ?c + m, snd p)"
  let ?Y = "rebaseRow0 ?c m M"
  have Yf: "?Y = map ?f M" by (simp add: rebaseRow0_def)
  have lb: "\<And>j. j < Lng M \<Longrightarrow> ?c \<le> entry M 0 j"
    by (rule entry0_ge_min[OF MT mono])
  have cong: "congR M ?Y" by (rule congR_rebaseRow0[OF lb])
  have LY: "Lng ?Y = Lng M" by simp
  have nR: "nextR M = nextR ?Y" by (rule congR_nextR[OF cong])
  have row0Y: "\<And>j. j < Lng M \<Longrightarrow> entry ?Y 0 j = entry M 0 j - ?c + m"
    by (rule entry_rebaseRow0_0)
  have row1Y: "\<And>j. j < Lng M \<Longrightarrow> entry ?Y 1 j = entry M 1 j"
    by (rule entry_rebaseRow0_1)
  show ?thesis
  proof (cases "Lng M = 1")
    case True
    have "M[n] = M" by (rule roper_oper_Lng1[OF True])
    moreover have "?Y[n] = ?Y" using LY True by (intro roper_oper_Lng1) simp
    ultimately show ?thesis by simp
  next
    case False
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have L: "1 < Lng M" using False Mne by (cases M) auto
    let ?j1 = "Lng M - 1"
    have j1pos: "0 < ?j1" using L by simp
    have j1lt: "?j1 < Lng M" using L by simp
    have leM: "leR M 0 0 ?j1" using mono by (simp add: monoT_def)
    have e0j1: "?c < entry M 0 ?j1"
      by (rule m_5_1_ancestor_basic_1[OF MT j1pos order.refl leM])
    have nzM: "\<not> (entry M 0 ?j1 = 0 \<and> entry M 1 ?j1 = 0)" using e0j1 by auto
    have e0Yj1: "entry ?Y 0 ?j1 = entry M 0 ?j1 - ?c + m" using row0Y j1lt by simp
    have nzY: "\<not> (entry ?Y 0 ?j1 = 0 \<and> entry ?Y 1 ?j1 = 0)"
      using e0Yj1 e0j1 by auto
    have i1Y: "idx1 ?Y ?j1 = idx1 M ?j1" using row1Y j1lt by (simp add: idx1_def)
    have hpY: "\<And>i j. hasParent ?Y i j = hasParent M i j"
      using nR by (simp add: hasParent_def)
    have parY: "\<And>i j. parent ?Y i j = parent M i j"
      using nR by (simp add: parent_def)
    show ?thesis
    proof (cases "hasParent M (idx1 M ?j1) ?j1")
      case False
      have opM: "M[n] = Pred M"
        by (rule oper_degenerate_eq_Pred[OF L disjI2[OF False]])
      have FY: "\<not> hasParent ?Y (idx1 ?Y (Lng ?Y - 1)) (Lng ?Y - 1)"
        using False i1Y hpY LY by simp
      have opY: "?Y[n] = Pred ?Y"
        using oper_degenerate_eq_Pred[OF _ disjI2[OF FY]] LY L by simp
      have "Pred ?Y = rebaseRow0 ?c m (Pred M)"
        using LY L by (simp add: Pred_def rebaseRow0_def map_butlast)
      thus ?thesis using opM opY by simp
    next
      case hp: True
      define i1 where "i1 = idx1 M ?j1"
      define j0 where "j0 = parent M i1 ?j1"
      define d0 where "d0 = (if 0 < i1 then entry M 0 ?j1 - entry M 0 j0 else 0)"
      define d1 where "d1 = (if 1 < i1 then entry M 1 ?j1 - entry M 1 j0 else 0)"
      have hp': "hasParent M i1 ?j1" using hp i1_def by simp
      have parR: "nextR M i1 j0 ?j1"
        using hp' unfolding hasParent_def parent_def j0_def i1_def by (rule theI')
      have j0lt: "j0 < ?j1" and le0j01: "leR M 0 j0 ?j1"
        using poper_nextR_imp_le0[OF parR] by simp_all
      have j0L: "j0 < Lng M" using j0lt j1lt by linarith
      have e0j0lt: "entry M 0 j0 < entry M 0 ?j1"
        by (rule m_5_1_ancestor_basic_1[OF MT j0lt order.refl le0j01])
      have hpYj: "hasParent ?Y (idx1 ?Y (Lng ?Y - 1)) (Lng ?Y - 1)"
        using hp LY i1Y hpY by simp
      have nzY': "\<not> (entry ?Y 0 (Lng ?Y - 1) = 0 \<and> entry ?Y 1 (Lng ?Y - 1) = 0)"
        using nzY LY by simp
      have LYg: "1 < Lng ?Y" using LY L by simp
      \<comment> \<open>the two expansions\<close>
      have expM: "M[n] = take j0 M
          @ concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j + k * d1))
                                 [j0..<?j1]) [0..<n])"
        using poper_oper_expand[OF L nzM hp, of n]
        unfolding Let_def i1_def[symmetric] j0_def[symmetric]
                  d0_def[symmetric] d1_def[symmetric] .
      have d0Y: "(if 0 < i1 then entry ?Y 0 ?j1 - entry ?Y 0 j0 else 0) = d0"
      proof (cases "0 < i1")
        case True
        have "entry ?Y 0 ?j1 - entry ?Y 0 j0
              = (entry M 0 ?j1 - ?c + m) - (entry M 0 j0 - ?c + m)"
          using row0Y j1lt j0L by simp
        also have "\<dots> = entry M 0 ?j1 - entry M 0 j0"
          using lb[OF j0L] lb[OF j1lt] e0j0lt by linarith
        finally show ?thesis using True by (simp add: d0_def)
      next
        case False thus ?thesis by (simp add: d0_def)
      qed
      have d1Y: "(if 1 < i1 then entry ?Y 1 ?j1 - entry ?Y 1 j0 else 0) = d1"
        using row1Y j1lt j0L by (simp add: d1_def)
      have expY: "?Y[n] = take j0 ?Y
          @ concat (map (\<lambda>k. map (\<lambda>j. (entry ?Y 0 j + k * d0, entry ?Y 1 j + k * d1))
                                 [j0..<?j1]) [0..<n])"
        using poper_oper_expand[OF LYg nzY' hpYj, of n]
        unfolding Let_def LY i1Y i1_def[symmetric] parY j0_def[symmetric]
                  d0Y d1Y .
      \<comment> \<open>blockwise: the \<open>Y\<close>-block is the \<open>?f\<close>-image of the \<open>M\<close>-block\<close>
      have blocks: "\<And>k. map (\<lambda>j. (entry ?Y 0 j + k * d0, entry ?Y 1 j + k * d1))
                          [j0..<?j1]
                  = map ?f (map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j + k * d1))
                                [j0..<?j1])"
      proof -
        fix k
        show "map (\<lambda>j. (entry ?Y 0 j + k * d0, entry ?Y 1 j + k * d1)) [j0..<?j1]
              = map ?f (map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j + k * d1))
                            [j0..<?j1])"
          unfolding map_map
        proof (rule map_cong[OF refl])
          fix j assume "j \<in> set [j0..<?j1]"
          hence jL: "j < Lng M" using j1lt by auto
          have "entry ?Y 0 j + k * d0 = (entry M 0 j + k * d0) - ?c + m"
            using row0Y[OF jL] lb[OF jL] by linarith
          thus "(entry ?Y 0 j + k * d0, entry ?Y 1 j + k * d1)
                = (?f \<circ> (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j + k * d1))) j"
            using row1Y[OF jL] by simp
        qed
      qed
      have takeY: "take j0 ?Y = map ?f (take j0 M)"
        by (simp add: rebaseRow0_def take_map)
      have maps: "map (\<lambda>k. map (\<lambda>j. (entry ?Y 0 j + k * d0, entry ?Y 1 j + k * d1))
                              [j0..<?j1]) [0..<n]
                = map (map ?f)
                      (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0,
                                           entry M 1 j + k * d1))
                                    [j0..<?j1]) [0..<n])"
        unfolding map_map
        by (rule map_cong[OF refl]) (simp only: o_apply blocks)
      have "?Y[n] = map ?f (take j0 M)
          @ concat (map (map ?f)
                        (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0,
                                             entry M 1 j + k * d1))
                                      [j0..<?j1]) [0..<n]))"
        unfolding expY takeY maps ..
      also have "\<dots> = map ?f (take j0 M)
          @ map ?f (concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0,
                                               entry M 1 j + k * d1))
                                        [j0..<?j1]) [0..<n]))"
        by (simp add: map_concat)
      also have "\<dots> = map ?f (M[n])" using expM by simp
      finally show ?thesis by (simp add: rebaseRow0_def)
    qed
  qed
qed

end

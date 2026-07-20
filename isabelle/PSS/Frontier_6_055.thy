theory Frontier_6_055
  imports Support_6_037
begin

(* ===== final-layer block (if2): idempotency re-decomposition + B1 + finish ===== *)

subsection \<open>§6.6 final layer (if2): \<open>Red\<close>-output re-decomposition and idempotency\<close>

text \<open>if2: re-decomposition of \<open>P (concat Qs)\<close> for a list of NON-MULTI blocks whose
  row-0 heads are descending left-minima.  Concretely: each block \<open>Qs!J\<close> is
  non-empty and \<open>\<not> multiT\<close>, and the head \<open>entry (Qs!J) 0 0\<close> is \<open>\<le>\<close> every row-0
  value of \<open>concat Qs\<close> at an index strictly inside an earlier-or-equal block.  Then
  \<open>P (concat Qs) = Qs\<close>.  Proof by induction peeling the FIRST block via
  @{thm [source] m_6_2_P_additive} at the boundary \<open>Lng (Qs!0)\<close> (a row-0 left-min
  because the head of block 1 \<le> all of block 0).  Empirically TRUE (the
  \<open>Red\<close>-output branch blocks satisfy this, 900/900 core-nontrunk at rank\<le>4).\<close>

lemma if2_P_concat_blocks:
  "\<And>i. Qs \<noteq> []
       \<Longrightarrow> (\<forall>J < length Qs. Qs!J \<noteq> [] \<and> \<not> multiT (Qs!J))
       \<Longrightarrow> (\<forall>J < length Qs. \<forall>I \<le> J. \<forall>k < Lng (Qs!I).
              entry (Qs!J) 0 0 \<le> entry (Qs!I) 0 k)
       \<Longrightarrow> P (concat Qs) = Qs"
proof (induction Qs rule: length_induct)
  case (1 Qs)
  note IH = 1(1)
  note Qsne = 1(2)
  note nm = 1(3)
  note hmin = 1(4)
  show ?case
  proof (cases Qs)
    case Nil
    thus ?thesis using Qsne by simp
  next
    case (Cons Q0 rest)
    have Q0ne: "Q0 \<noteq> []" and Q0nm: "\<not> multiT Q0"
      using nm Cons by fastforce+
    show ?thesis
    proof (cases "rest = []")
      case True
      \<comment> \<open>single non-multi block.\<close>
      have "P (concat Qs) = P Q0" using Cons True by simp
      also have "\<dots> = [Q0]" by (rule poper_P_nonmulti) (use Q0nm in simp)
      finally show ?thesis using Cons True by simp
    next
      case restne0: False
      \<comment> \<open>at least two blocks: peel block 0 at the boundary \<open>Lng Q0\<close>.\<close>
      let ?S = "concat Qs"
      have Sval: "?S = Q0 @ concat rest" using Cons by simp
      have restne: "concat rest \<noteq> []"
      proof -
        obtain a list where rl: "rest = a # list" using restne0 by (cases rest) auto
        have "a \<noteq> []" using nm Cons restne0 rl by fastforce
        thus ?thesis using rl by simp
      qed
      have ST: "?S \<in> T_PS"
      proof -
        have "?S \<noteq> []" using Sval Q0ne by simp
        thus ?thesis by (simp add: T_PS_def)
      qed
      let ?c = "Lng Q0"
      have cpos: "0 < ?c" using Q0ne by (cases Q0) auto
      have LS: "Lng ?S = Lng Q0 + Lng (concat rest)" using Sval by simp
      have cle: "?c \<le> Lng ?S - 1" using LS restne by (cases "concat rest") auto
      \<comment> \<open>row-0 of \<open>?S\<close> below \<open>?c\<close> reads \<open>Q0\<close>; at \<open>?c\<close> reads \<open>head (concat rest)\<close>.\<close>
      have eS_lo: "\<And>j. j < ?c \<Longrightarrow> entry ?S 0 j = entry Q0 0 j"
        using Sval cpos by (simp add: entry_def nth_append)
      have eS_c: "entry ?S 0 ?c = entry (concat rest) 0 0"
        using Sval by (simp add: entry_def nth_append)
      \<comment> \<open>head of block 1 (= head of \<open>concat rest\<close>) is \<open>\<le>\<close> all of block 0.\<close>
      have lmin: "\<And>j. j < ?c \<Longrightarrow> entry ?S 0 ?c \<le> entry ?S 0 j"
      proof -
        fix j assume j: "j < ?c"
        have len1: "1 < length Qs" using Cons restne0 by (cases rest) auto
        have jc: "j < Lng (Qs!0)" using j Cons by simp
        have h1: "entry (Qs!1) 0 0 \<le> entry (Qs!0) 0 j"
          using hmin[rule_format, of 1 0 j] len1 jc by simp
        have q0: "Qs!0 = Q0" using Cons by simp
        have q1: "Qs!1 = rest!0" using Cons by simp
        have r0ne: "rest!0 \<noteq> []" using nm Cons restne0 by fastforce
        have head_rest: "entry (concat rest) 0 0 = entry (rest!0) 0 0"
        proof -
          obtain a list where rl: "rest = a # list" using restne0 by (cases rest) auto
          have ane: "a \<noteq> []" using r0ne rl by simp
          have "concat rest = a @ concat list" using rl by simp
          thus ?thesis using ane rl by (simp add: entry_def nth_append)
        qed
        show "entry ?S 0 ?c \<le> entry ?S 0 j"
          using h1 j eS_lo eS_c head_rest q0 q1 by simp
      qed
      \<comment> \<open>additive split of \<open>P\<close> at the boundary \<open>?c\<close>.\<close>
      have split: "P ?S = P (seg ?S 0 (?c - 1)) @ P (seg ?S ?c (Lng ?S - 1))"
        by (rule m_6_2_P_additive[OF ST cpos cle lmin])
      \<comment> \<open>left part is \<open>Q0\<close>.\<close>
      have segL: "seg ?S 0 (?c - 1) = Q0"
      proof -
        have suc_c: "Suc (?c - 1) = ?c" using cpos by simp
        have cleS: "Suc (?c - 1) \<le> Lng ?S" using suc_c cle LS restne by simp
        have "seg ?S 0 (?c - 1) = take (Suc (?c - 1)) ?S"
          by (rule seg_0_eq_take[OF cleS])
        also have "\<dots> = take ?c ?S" using suc_c by simp
        also have "\<dots> = Q0" using Sval by simp
        finally show ?thesis .
      qed
      have PL: "P (seg ?S 0 (?c - 1)) = [Q0]"
      proof -
        have "\<not> (multiT Q0 \<and> 1 < Lng Q0)" using Q0nm by simp
        thus ?thesis using segL by (simp add: poper_P_nonmulti)
      qed
      \<comment> \<open>right part is \<open>concat rest\<close>.\<close>
      have segR: "seg ?S ?c (Lng ?S - 1) = concat rest"
      proof -
        have LSpos: "0 < Lng ?S" using LS cpos by linarith
        have "seg ?S ?c (Lng ?S - 1) = drop ?c ?S"
          by (rule seg_to_last_eq_drop[OF LSpos])
        also have "\<dots> = concat rest" using Sval by simp
        finally show ?thesis .
      qed
      \<comment> \<open>IH on \<open>rest\<close>.\<close>
      have nm_rest: "\<forall>J < length rest. rest!J \<noteq> [] \<and> \<not> multiT (rest!J)"
      proof (intro allI impI)
        fix J assume J: "J < length rest"
        have "Suc J < length Qs" using J Cons by simp
        moreover have "Qs!(Suc J) = rest!J" using Cons by simp
        ultimately show "rest!J \<noteq> [] \<and> \<not> multiT (rest!J)" using nm by metis
      qed
      have hmin_rest: "\<forall>J < length rest. \<forall>I \<le> J. \<forall>k < Lng (rest!I).
              entry (rest!J) 0 0 \<le> entry (rest!I) 0 k"
      proof (intro allI impI)
        fix J I k assume J: "J < length rest" and IJ: "I \<le> J" and k: "k < Lng (rest!I)"
        have sJ: "Suc J < length Qs" using J Cons by simp
        have sIJ: "Suc I \<le> Suc J" using IJ by simp
        have kQ: "k < Lng (Qs!(Suc I))" using k Cons by simp
        have "entry (Qs!(Suc J)) 0 0 \<le> entry (Qs!(Suc I)) 0 k"
          using hmin sJ sIJ kQ by blast
        moreover have "Qs!(Suc J) = rest!J" using Cons by simp
        moreover have "Qs!(Suc I) = rest!I" using Cons by simp
        ultimately show "entry (rest!J) 0 0 \<le> entry (rest!I) 0 k" by simp
      qed
      have shorter: "length rest < length Qs" using Cons by simp
      have PR: "P (concat rest) = rest"
        using IH shorter restne0 nm_rest hmin_rest by blast
      have "P ?S = [Q0] @ rest" using split PL segR PR by simp
      thus ?thesis using Cons by simp
    qed
  qed
qed

text \<open>if2: \<open>(IncrFirst^^k)\<close> preserves \<open>\<not> multiT\<close> (per @{thm [source] IncrFirst_multiT_eq}).\<close>

lemma if2_multiT_funpow_IncrFirst: "multiT ((IncrFirst ^^ k) M) = multiT M"
  by (induction k) (simp_all add: IncrFirst_multiT_eq)

text \<open>if2: the branch block \<open>B\<^sub>J = (IncrFirst^^e\<^sub>J)(Red (NJ M J))\<close> of a core-nontrunk
  \<open>M\<close> is non-empty and non-multi.  \<open>NJ M J\<close> is non-multi (@{thm [source] NJ_nonmulti});
  if mono it is in \<open>PT\<^sub>PS\<close> so \<open>Red (NJ M J)\<close> is mono (@{thm [source]
  m_6_5_Red_preserves_monoT}, the now-green keystone); if zero \<open>Red (NJ M J) = [(0,0)]\<close>
  is zero.  Either way \<open>\<not> multiT\<close>, preserved by \<open>(IncrFirst^^e\<^sub>J)\<close>.\<close>

lemma if2_block_props:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
  shows "(IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) \<noteq> []
       \<and> \<not> multiT ((IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))"
proof -
  let ?e = "Joints M ! J + 1 - npJ M J"
  let ?B = "(IncrFirst ^^ ?e) (Red (NJ M J))"
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
  have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
  have nm: "\<not> multiT (NJ M J)" by (rule NJ_nonmulti[OF M c0 c1 JBr])
  have L0: "0 < Lng (Red (NJ M J))"
  proof -
    have "Lng (Red (NJ M J)) = Lng (NJ M J)" by (rule m_6_5_Lng_Red[OF NJT])
    moreover have "0 < Lng (NJ M J)" by (simp add: NJ_def)
    ultimately show ?thesis by simp
  qed
  have LB: "Lng ?B = Lng (Red (NJ M J))" by (simp only: Lng_funpow_IncrFirst)
  have Bpos: "0 < Lng ?B" using L0 LB by simp
  have Bne: "?B \<noteq> []" using Bpos length_greater_0_conv by blast
  have nmRed: "\<not> multiT (Red (NJ M J))"
  proof (cases "zeroT (NJ M J)")
    case True
    have domNJ: "Red_dom (NJ M J)" by (rule m_6_5_Red_welldef[OF NJT])
    have "Red (NJ M J) = [(0,0)]" using Red.psimps[OF domNJ] True by simp
    thus ?thesis by (simp add: multiT_def zeroT_def entry_def)
  next
    case False
    have mono: "monoT (NJ M J)" using nm False by (simp add: multiT_def)
    have NJPT: "NJ M J \<in> PT_PS" using NJT mono by (simp add: PT_PS_def)
    have "monoT (Red (NJ M J))" by (rule m_6_5_Red_preserves_monoT[OF NJPT])
    thus ?thesis by (simp add: multiT_def)
  qed
  have nmB: "\<not> multiT ?B" using nmRed by (simp add: if2_multiT_funpow_IncrFirst)
  show ?thesis using Bne nmB by simp
qed

text \<open>if2: the branch block row-0 head \<open>Joints M ! J + 1\<close> is the row-0 MINIMUM of the
  block \<open>B\<^sub>J\<close>.  Inner \<open>Red (NJ M J)\<close> has its head as row-0 min (@{thm [source]
  m_6_5_Red_leftend_row0_min}, or trivially for the zero singleton);
  \<open>(IncrFirst^^e\<^sub>J)\<close> shifts row 0 uniformly, preserving the min.\<close>

lemma if2_block_row0_min:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
    and k: "k < Lng ((IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))"
  shows "Joints M ! J + 1
         \<le> entry ((IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))) 0 k"
proof -
  let ?e = "Joints M ! J + 1 - npJ M J"
  let ?R = "Red (NJ M J)"
  let ?B = "(IncrFirst ^^ ?e) ?R"
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
  have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
  have nm: "\<not> multiT (NJ M J)" by (rule NJ_nonmulti[OF M c0 c1 JBr])
  have LR: "Lng ?R = Lng (NJ M J)" by (rule m_6_5_Lng_Red[OF NJT])
  have LRpos: "0 < Lng ?R" using LR by (simp add: NJ_def)
  have kR: "k < Lng ?R" using k by simp
  \<comment> \<open>row-0 head of \<open>?R\<close> is its row-0 min.\<close>
  have headmin: "entry ?R 0 0 \<le> entry ?R 0 k"
  proof (cases "zeroT (NJ M J)")
    case True
    have domNJ: "Red_dom (NJ M J)" by (rule m_6_5_Red_welldef[OF NJT])
    have R1: "?R = [(0,0)]" using Red.psimps[OF domNJ] True by simp
    have "k = 0" using kR R1 by simp
    thus ?thesis by simp
  next
    case False
    have mono: "monoT (NJ M J)" using nm False by (simp add: multiT_def)
    show ?thesis using m_6_5_Red_leftend_row0_min[OF NJT mono] kR by blast
  qed
  \<comment> \<open>head value of \<open>?R\<close> is \<open>npJ M J\<close>.\<close>
  have head_val: "entry ?R 0 0 = npJ M J" by (rule fin_Red_NJ_leftend[OF M c0 c1 JBr])
  have nple: "npJ M J \<le> Joints M ! J + 1" by (rule npJ_le_Joints_Suc[OF M c1 JBr])
  \<comment> \<open>\<open>(IncrFirst^^e)\<close> shifts row 0 by \<open>e\<close>.\<close>
  have eB: "entry ?B 0 k = entry ?R 0 k + ?e"
    by (rule entry_funpow_IncrFirst0[OF kR])
  have "Joints M ! J + 1 = npJ M J + ?e" using nple by simp
  also have "\<dots> = entry ?R 0 0 + ?e" using head_val by simp
  also have "\<dots> \<le> entry ?R 0 k + ?e" using headmin by simp
  also have "\<dots> = entry ?B 0 k" using eB by simp
  finally show ?thesis .
qed

text \<open>if2: STRUCTURE — \<open>Br (Red M) = map B [0..<Lng (Br M)]\<close> for a core-nontrunk
  \<open>M\<close>.  By @{thm [source] fl_s_TrMax_Red} \<open>TrMax (Red M) = TrMax M \<noteq> Lng (Red M) - 1\<close>,
  so \<open>Br (Red M) = P (seg (Red M) (TrMax M + 1) (Lng (Red M) - 1))\<close>; that segment is
  exactly the \<open>concat (branch blocks)\<close> tail of @{thm [source]
  d_Red_core_nontrunk_unfold} (dropping the \<open>diagSeq 0 (TrMax M)\<close> prefix); and
  @{thm [source] if2_P_concat_blocks} re-decomposes it back to the blocks
  (non-multi by @{thm [source] if2_block_props}; descending heads by
  @{thm [source] if2_block_row0_min} + @{thm [source] fin_block_head} +
  Joints non-increasing @{thm [source] m_6_4_FirstNodes_Joints_mono}).\<close>

lemma if2_Br_Red:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  shows "Br (Red M)
       = map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))
             [0..<Lng (Br M)]"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have mono: "monoT M" using M by (simp add: PT_PS_def)
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  let ?t = "TrMax M"
  let ?blk = "\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))"
  let ?Qs = "map ?blk [0..<Lng (Br M)]"
  have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  \<comment> \<open>\<open>TrMax\<close> and the unfold of \<open>Red M\<close>.\<close>
  have trR: "TrMax (Red M) = ?t" by (rule fl_s_TrMax_Red[OF MT mono c0 c1 tne])
  have rM: "Red M = diagSeq 0 ?t @ concat ?Qs"
    by (rule d_Red_core_nontrunk_unfold[OF MT nz nmu c0 c1 tne])
  \<comment> \<open>there is a branch.\<close>
  have brne: "Br M \<noteq> []"
  proof -
    have "Br M = P (seg M (?t + 1) (Lng M - 1))" using tne by (simp add: Br_def)
    thus ?thesis using P_nonempty by simp
  qed
  have JBr: "0 < Lng (Br M)" using brne by (cases "Br M") auto
  \<comment> \<open>\<open>TrMax (Red M) \<noteq> Lng (Red M) - 1\<close>.\<close>
  have tb: "?t \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  with tne have trlt: "?t < Lng M - 1" by linarith
  have trRne: "TrMax (Red M) \<noteq> Lng (Red M) - 1" using trR trlt LrM by simp
  \<comment> \<open>length of the diagonal prefix.\<close>
  have lenD: "Lng (diagSeq 0 ?t) = Suc ?t" by (simp del: upt_Suc)
  \<comment> \<open>\<open>Br (Red M)\<close> as the \<open>P\<close> of the segment past the trunk.\<close>
  have brRed: "Br (Red M) = P (seg (Red M) (?t + 1) (Lng (Red M) - 1))"
    using trRne trR by (simp add: Br_def)
  \<comment> \<open>that segment is \<open>concat ?Qs\<close>.\<close>
  have RMne: "Red M \<noteq> []"
  proof -
    have "0 < Lng (Red M)" using rM lenD by simp
    thus ?thesis by (cases "Red M") auto
  qed
  have LRM_ge: "?t + 1 \<le> Lng (Red M) - 1"
  proof -
    have "Lng (Red M) - 1 = Lng M - 1" using LrM by simp
    thus ?thesis using trlt by linarith
  qed
  have seg_eq: "seg (Red M) (?t + 1) (Lng (Red M) - 1) = concat ?Qs"
  proof -
    have LRMpos: "0 < Lng (Red M)" using RMne by (cases "Red M") auto
    have "seg (Red M) (?t + 1) (Lng (Red M) - 1) = drop (?t + 1) (Red M)"
      by (rule seg_to_last_eq_drop[OF LRMpos])
    also have "\<dots> = drop (Suc ?t) (diagSeq 0 ?t @ concat ?Qs)" using rM by simp
    also have "\<dots> = concat ?Qs" using lenD by simp
    finally show ?thesis .
  qed
  \<comment> \<open>re-decompose \<open>P (concat ?Qs) = ?Qs\<close>.\<close>
  have Qsne: "?Qs \<noteq> []" using JBr by simp
  have lenQs: "length ?Qs = Lng (Br M)" by simp
  have nm: "\<forall>J < length ?Qs. ?Qs!J \<noteq> [] \<and> \<not> multiT (?Qs!J)"
  proof (intro allI impI)
    fix J assume J: "J < length ?Qs"
    hence JB: "J < Lng (Br M)" using lenQs by simp
    have nthQ: "?Qs!J = ?blk J" using JB by simp
    show "?Qs!J \<noteq> [] \<and> \<not> multiT (?Qs!J)"
      using if2_block_props[OF M c0 c1 JB] nthQ by simp
  qed
  have hmin: "\<forall>J < length ?Qs. \<forall>I \<le> J. \<forall>k < Lng (?Qs!I).
                entry (?Qs!J) 0 0 \<le> entry (?Qs!I) 0 k"
  proof (intro allI impI)
    fix J I k
    assume J: "J < length ?Qs" and IJ: "I \<le> J" and k: "k < Lng (?Qs!I)"
    have JB: "J < Lng (Br M)" using J lenQs by simp
    have IB: "I < Lng (Br M)" using IJ JB by linarith
    have nthJ: "?Qs!J = ?blk J" using JB by simp
    have nthI: "?Qs!I = ?blk I" using IB by simp
    \<comment> \<open>head of block J equals \<open>Joints M ! J + 1\<close>.\<close>
    have hJ: "entry (?Qs!J) 0 0 = Joints M ! J + 1"
      using fin_block_head[OF M c0 c1 JB] nthJ by simp
    \<comment> \<open>row-0 of block I is \<open>\<ge> Joints M ! I + 1\<close>.\<close>
    have kI: "k < Lng (?blk I)" using k nthI by simp
    have geI: "Joints M ! I + 1 \<le> entry (?Qs!I) 0 k"
      using if2_block_row0_min[OF M c0 c1 IB kI] nthI by simp
    \<comment> \<open>Joints non-increasing: \<open>Joints M ! J \<le> Joints M ! I\<close>.\<close>
    have jJI: "Joints M ! J \<le> Joints M ! I"
    proof (cases "I = J")
      case True thus ?thesis by simp
    next
      case False
      hence IltJ: "I < J" using IJ by simp
      show ?thesis using m_6_4_FirstNodes_Joints_mono[OF M IltJ JB] by simp
    qed
    show "entry (?Qs!J) 0 0 \<le> entry (?Qs!I) 0 k"
      using hJ geI jJI by simp
  qed
  have "P (concat ?Qs) = ?Qs"
    by (rule if2_P_concat_blocks[OF Qsne nm hmin])
  thus ?thesis using brRed seg_eq by simp
qed


subsection \<open>§6.5/§6.6 idempotency closing chain (a1)\<close>

text \<open>a1: the trunk row-0 of \<open>Red M\<close> (core-nontrunk) is the diagonal:
  \<open>j \<le> TrMax M \<Longrightarrow> entry (Red M) 0 j = j\<close>.  Direct from
  @{thm [source] d_Red_core_nontrunk_unfold}: \<open>Red M = diagSeq 0 (TrMax M) @ \<dots>\<close>,
  and \<open>j \<le> TrMax M\<close> lands in the diagonal prefix.\<close>

lemma a1_Red_trunk_row0:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and j: "j \<le> TrMax M"
  shows "entry (Red M) 0 j = j"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have mono: "monoT M" using M by (simp add: PT_PS_def)
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  let ?t = "TrMax M"
  let ?tail = "concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                  (Red (NJ M J)))
                     [0..<Lng (Br M)])"
  have rM: "Red M = diagSeq 0 ?t @ ?tail"
    by (rule d_Red_core_nontrunk_unfold[OF MT nz nmu c0 c1 tne])
  have lenD: "Lng (diagSeq 0 ?t) = Suc ?t" by (simp del: upt_Suc)
  have jlt: "j < length (diagSeq 0 ?t)" using j lenD by simp
  have "(Red M) ! j = (diagSeq 0 ?t) ! j"
    using rM jlt by (simp add: nth_append)
  hence step: "entry (Red M) 0 j = entry (diagSeq 0 ?t) 0 j" by (simp add: entry_def)
  have "entry (diagSeq 0 ?t) 0 j = 0 + j"
    by (rule entry_diagSeq) (use j in simp)
  thus ?thesis using step by simp
qed

text \<open>a1: the \<open>J\<close>-th first node of a core-nontrunk \<open>M\<close> has a unique row-0 parent
  and lies inside \<open>M\<close>.  Both follow from @{thm [source] m_6_4_mono_slice_next}
  (the parent existence) and the \<open>nextrel0\<close> index bound.\<close>

lemma a1_FN_hasParent:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "hasParent M 0 (FirstNodes M ! J)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with JBr show False by simp
  qed
  with tb have trlt: "TrMax M < Lng M - 1" by linarith
  let ?j0 = "TrMax M + 1"
  have brQ: "Br M = P (seg M ?j0 (Lng M - 1))" using trne by (simp add: Br_def)
  have lenQ: "Lng (P (seg M ?j0 (Lng M - 1))) = Lng (Br M)" using brQ by simp
  have Jle: "J \<le> Lng (P (seg M ?j0 (Lng M - 1))) - 1" using JBr lenQ by linarith
  have hp: "hasParent M 0 (?j0 + IdxSum (P (seg M ?j0 (Lng M - 1))) ! J)"
    using m_6_4_mono_slice_next[OF M _ _ Jle] trlt by auto
  have JIdx: "J < length (IdxSum (Br M))" using JBr by (simp add: IdxSum_def)
  have fnJ: "FirstNodes M ! J = ?j0 + IdxSum (Br M) ! J"
    using JIdx by (simp add: FirstNodes_def)
  show ?thesis using hp fnJ brQ by simp
qed

lemma a1_FN_lt:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "FirstNodes M ! J < Lng M"
proof -
  have "nextR M 0 (Joints M ! J) (FirstNodes M ! J)"
    by (rule Joints_parent_nextR[OF M JBr])
  thus ?thesis by (simp add: nextR_def nextrel0_def)
qed

text \<open>a1: locate a position in a concat by block.  Standard list decomposition:
  any \<open>p < length (concat Q)\<close> lies in a unique block \<open>I\<close> at offset \<open>q\<close>.\<close>

lemma a1_concat_locate_raw:
  "p < length (concat Q) \<Longrightarrow>
     \<exists>I q. I < length Q \<and> q < length (Q ! I)
           \<and> p = sum_list (map length (take I Q)) + q"
proof (induction Q arbitrary: p)
  case Nil thus ?case by simp
next
  case (Cons a Q)
  show ?case
  proof (cases "p < length a")
    case True
    show ?thesis
      by (rule exI[of _ 0], rule exI[of _ p]) (simp add: True)
  next
    case False
    hence ge: "length a \<le> p" by simp
    have plt: "p - length a < length (concat Q)"
      using Cons.prems ge by simp
    from Cons.IH[OF plt] obtain I q where IL: "I < length Q"
        and qL: "q < length (Q ! I)"
        and pe: "p - length a = sum_list (map length (take I Q)) + q" by blast
    show ?thesis
      apply (rule exI[of _ "Suc I"], rule exI[of _ q])
      using IL qL pe ge by simp
  qed
qed

lemma a1_concat_locate:
  assumes p: "p < length (concat Q)"
  shows "\<exists>I q. I < length Q \<and> q < length (Q ! I)
              \<and> entry (concat Q) 0 p = entry (Q ! I) 0 q
              \<and> p = sum_list (map length (take I Q)) + q"
proof -
  from a1_concat_locate_raw[OF p] obtain I q where IL: "I < length Q"
      and qL: "q < length (Q ! I)"
      and pe: "p = sum_list (map length (take I Q)) + q" by blast
  have "concat Q ! p = (Q ! I) ! q"
    using nth_concat_block[OF IL qL] pe by simp
  hence "entry (concat Q) 0 p = entry (Q ! I) 0 q" by (simp add: entry_def)
  thus ?thesis using IL qL pe by blast
qed

lemma a1_sumlen_take_mono:
  assumes "J0 \<le> J1"
  shows "sum_list (map length (take J0 Q)) \<le> sum_list (map length (take J1 Q))"
  using assms by (rule idxsum_sum_take_mono)

text \<open>a1: (A) the joints of \<open>Red M\<close> coincide with those of \<open>M\<close> for a core-nontrunk
  \<open>M\<close>: \<open>Joints (Red M) ! J = Joints M ! J\<close>.  The \<open>J\<close>-th first node of \<open>Red M\<close> has
  row-0 head \<open>Joints M ! J + 1\<close> (@{thm [source] fin_block_head} via
  @{thm [source] entry_FirstNodes_eq_component} on the block decomposition), and
  its unique row-0 parent in \<open>Red M\<close> is the diagonal index \<open>Joints M ! J\<close>
  (trunk value \<open>Joints M ! J\<close>; the between-condition is the block-min
  @{thm [source] if2_block_row0_min} + trunk monotonicity + \<open>Joints\<close>
  non-increasing).\<close>

lemma a1_if_Joints_Red:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and JBr: "J < Lng (Br M)"
  shows "Joints (Red M) ! J = Joints M ! J"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have mono: "monoT M" using M by (simp add: PT_PS_def)
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  let ?t = "TrMax M"
  let ?blk = "\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))"
  let ?Qs = "map ?blk [0..<Lng (Br M)]"
  \<comment> \<open>structural facts about \<open>Red M\<close>.\<close>
  have RMmono: "monoT (Red M)" by (rule m_6_5_Red_preserves_monoT[OF M])
  have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  have RMne: "Red M \<noteq> []" using LrM MT by (cases "Red M") (auto simp: T_PS_def)
  have RMT: "Red M \<in> T_PS" using RMne by (simp add: T_PS_def)
  have RM_PT: "Red M \<in> PT_PS" using RMT RMmono by (simp add: PT_PS_def)
  have brR: "Br (Red M) = ?Qs" by (rule if2_Br_Red[OF M c0 c1 tne])
  have lenBrR: "Lng (Br (Red M)) = Lng (Br M)" using brR by simp
  have JBrR: "J < Lng (Br (Red M))" using JBr lenBrR by simp
  have trR: "TrMax (Red M) = ?t" by (rule fl_s_TrMax_Red[OF MT mono c0 c1 tne])
  have rM: "Red M = diagSeq 0 ?t @ concat ?Qs"
    by (rule d_Red_core_nontrunk_unfold[OF MT nz nmu c0 c1 tne])
  \<comment> \<open>the first node of \<open>Red M\<close>.\<close>
  let ?FN = "FirstNodes (Red M) ! J"
  have FNlt: "?FN < Lng (Red M)" by (rule a1_FN_lt[OF RM_PT JBrR])
  \<comment> \<open>row-0 head of the first node = Joints M ! J + 1.\<close>
  have blkJ: "Br (Red M) ! J = ?blk J" using brR JBr by simp
  have FNrow0: "entry (Red M) 0 ?FN = Joints M ! J + 1"
  proof -
    have "entry (Red M) 0 ?FN = entry (Br (Red M) ! J) 0 0"
      by (rule entry_FirstNodes_eq_component[OF RM_PT JBrR])
    also have "\<dots> = entry (?blk J) 0 0" using blkJ by simp
    also have "\<dots> = Joints M ! J + 1" by (rule fin_block_head[OF M c0 c1 JBr])
    finally show ?thesis .
  qed
  \<comment> \<open>the diagonal index \<open>Joints M ! J\<close> is below the trunk top.\<close>
  have aJTr: "Joints M ! J \<le> ?t"
    using m_6_4_FirstNodes_TrMax_Joints[OF M JBr] by simp
  have aJrow0: "entry (Red M) 0 (Joints M ! J) = Joints M ! J"
    by (rule a1_Red_trunk_row0[OF M c0 c1 tne aJTr])
  \<comment> \<open>\<open>Joints M ! J < ?FN\<close>: the first node is past the whole trunk.\<close>
  have FNgt: "?t < ?FN"
  proof -
    have "?FN = TrMax (Red M) + 1 + IdxSum (Br (Red M)) ! J"
      by (rule FirstNodes_nth[OF JBrR])
    thus ?thesis using trR by simp
  qed
  have aJltFN: "Joints M ! J < ?FN" using aJTr FNgt by linarith
  \<comment> \<open>the between-condition for \<open>nextrel0 (Red M) (Joints M ! J) ?FN\<close>.\<close>
  have between: "\<And>j. Joints M ! J < j \<Longrightarrow> j < ?FN
                   \<Longrightarrow> entry (Red M) 0 ?FN \<le> entry (Red M) 0 j"
  proof -
    fix j assume jlo: "Joints M ! J < j" and jhi: "j < ?FN"
    show "entry (Red M) 0 ?FN \<le> entry (Red M) 0 j"
    proof (cases "j \<le> ?t")
      case True
      have "entry (Red M) 0 j = j" by (rule a1_Red_trunk_row0[OF M c0 c1 tne True])
      moreover have "Joints M ! J + 1 \<le> j" using jlo by simp
      ultimately show ?thesis using FNrow0 by simp
    next
      case False
      hence jgt: "?t < j" by simp
      \<comment> \<open>\<open>j\<close> is inside the branch region; locate its block.\<close>
      have jlt: "j < Lng (Red M)" using jhi FNlt by linarith
      \<comment> \<open>row-0 of any branch index is \<open>\<ge> Joints M ! I + 1\<close> for its block \<open>I \<le> J\<close>.\<close>
      \<comment> \<open>We use the descending-head property: the segment past the trunk has all
        row-0 entries \<open>\<ge> Joints M ! J + 1\<close> up to (but not including) the J-th head.\<close>
      have seg_eq: "seg (Red M) (?t + 1) (Lng (Red M) - 1) = concat ?Qs"
      proof -
        have LRMpos: "0 < Lng (Red M)" using RMne by (cases "Red M") auto
        have lenD: "Lng (diagSeq 0 ?t) = Suc ?t" by (simp del: upt_Suc)
        have "seg (Red M) (?t + 1) (Lng (Red M) - 1) = drop (?t + 1) (Red M)"
          by (rule seg_to_last_eq_drop[OF LRMpos])
        also have "\<dots> = drop (Suc ?t) (diagSeq 0 ?t @ concat ?Qs)" using rM by simp
        also have "\<dots> = concat ?Qs" using lenD by simp
        finally show ?thesis .
      qed
      \<comment> \<open>index \<open>j\<close> maps to index \<open>j - (?t+1)\<close> in \<open>concat ?Qs\<close>; locate its block \<open>I\<close>.\<close>
      define p where "p = j - (?t + 1)"
      have jp: "j = (?t + 1) + p" using jgt p_def by simp
      have lenD2: "Lng (diagSeq 0 ?t) = Suc ?t" by (simp del: upt_Suc)
      have lenconcat: "Lng (concat ?Qs) = Lng (Red M) - (?t + 1)"
      proof -
        have "Lng (Red M) = Lng (diagSeq 0 ?t) + Lng (concat ?Qs)"
          using rM by simp
        thus ?thesis using lenD2 by simp
      qed
      have plt: "p < Lng (concat ?Qs)"
        using lenconcat jlt jp by linarith
      have ej_seg: "entry (Red M) 0 j = entry (concat ?Qs) 0 p"
      proof -
        have lp: "p < Lng (seg (Red M) (?t + 1) (Lng (Red M) - 1))"
          using seg_eq plt by simp
        have "entry (seg (Red M) (?t + 1) (Lng (Red M) - 1)) 0 p
            = entry (Red M) 0 ((?t + 1) + p)" by (rule entry_seg[OF lp])
        thus ?thesis using seg_eq jp by simp
      qed
      \<comment> \<open>locate the block \<open>I\<close> of position \<open>p\<close> in \<open>concat ?Qs\<close>.\<close>
      have lenQ: "length ?Qs = Lng (Br M)" by simp
      obtain I q where Idef: "I < length ?Qs" "q < Lng (?Qs ! I)"
          and pIq: "entry (concat ?Qs) 0 p = entry (?Qs ! I) 0 q"
          and Iidx: "p = sum_list (map length (take I ?Qs)) + q"
        using a1_concat_locate[OF plt] by blast
      have IB: "I < Lng (Br M)" using Idef(1) lenQ by simp
      have nthI: "?Qs ! I = ?blk I" using IB by simp
      have qB: "q < Lng (?blk I)" using Idef(2) nthI by simp
      have geI: "Joints M ! I + 1 \<le> entry (?blk I) 0 q"
        by (rule if2_block_row0_min[OF M c0 c1 IB qB])
      \<comment> \<open>\<open>I \<le> J\<close> because position \<open>p\<close> precedes the head of block \<open>J\<close>.\<close>
      have IleJ: "I \<le> J"
      proof (rule ccontr)
        assume "\<not> I \<le> J"
        hence JltI: "J < I" by simp
        \<comment> \<open>head of block J is at \<open>?t + 1 + IdxSum ?Qs ! J\<close> = \<open>?FN\<close>, and \<open>p \<ge>\<close> start of block I > head of J.\<close>
        have idxJ: "IdxSum (Br (Red M)) ! J = sum_list (map length (take J ?Qs))"
          using brR JBrR by (simp add: idxsum_nth lenBrR)
        have idxI_ge: "sum_list (map length (take J ?Qs))
                       \<le> sum_list (map length (take I ?Qs))"
          using JltI by (simp add: a1_sumlen_take_mono)
        have pstart: "sum_list (map length (take I ?Qs)) \<le> p" using Iidx by simp
        have "?FN = (?t + 1) + sum_list (map length (take J ?Qs))"
          using FirstNodes_nth[OF JBrR] trR idxJ by simp
        hence "?FN \<le> (?t + 1) + p" using idxI_ge pstart by linarith
        thus False using jhi jp by linarith
      qed
      have jJI: "Joints M ! J \<le> Joints M ! I"
      proof (cases "I = J")
        case True thus ?thesis by simp
      next
        case False
        hence IltJ: "I < J" using IleJ by simp
        show ?thesis using m_6_4_FirstNodes_Joints_mono[OF M IltJ JBr] by simp
      qed
      have "entry (Red M) 0 ?FN = Joints M ! J + 1" by (rule FNrow0)
      also have "\<dots> \<le> Joints M ! I + 1" using jJI by simp
      also have "\<dots> \<le> entry (?blk I) 0 q" using geI by simp
      also have "\<dots> = entry (concat ?Qs) 0 p" using pIq nthI by simp
      also have "\<dots> = entry (Red M) 0 j" using ej_seg by simp
      finally show ?thesis .
    qed
  qed
  \<comment> \<open>assemble \<open>nextrel0 (Red M) (Joints M ! J) ?FN\<close>.\<close>
  have nr0: "nextrel0 (Red M) (Joints M ! J) ?FN"
    unfolding nextrel0_def
  proof (intro conjI allI impI)
    show "Joints M ! J < Lng (Red M)" using aJltFN FNlt by linarith
    show "?FN < Lng (Red M)" by (rule FNlt)
    show "Joints M ! J < ?FN" by (rule aJltFN)
    show "entry (Red M) 0 (Joints M ! J) < entry (Red M) 0 ?FN"
      using aJrow0 FNrow0 by simp
    fix j assume "Joints M ! J < j \<and> j < ?FN"
    thus "entry (Red M) 0 ?FN \<le> entry (Red M) 0 j" using between by blast
  qed
  have nx: "nextR (Red M) 0 (Joints M ! J) ?FN" by (simp add: nextR_def nr0)
  \<comment> \<open>uniqueness of the parent, from @{thm [source] Joints_parent_nextR}.\<close>
  have hp: "nextR (Red M) 0 (Joints (Red M) ! J) ?FN"
    by (rule Joints_parent_nextR[OF RM_PT JBrR])
  have exu: "\<exists>!j0. nextR (Red M) 0 j0 ?FN"
  proof -
    have "hasParent (Red M) 0 ?FN"
      by (rule a1_FN_hasParent[OF RM_PT JBrR])
    thus ?thesis by (simp add: hasParent_def)
  qed
  have "Joints (Red M) ! J = (THE j0. nextR (Red M) 0 j0 ?FN)"
    using hp exu by (simp add: the1_equality)
  also have "\<dots> = Joints M ! J" using nx exu by (simp add: the1_equality)
  finally show ?thesis .
qed

text \<open>a1: the row-1 head of the \<open>J\<close>-th branch block of \<open>Red M\<close> equals \<open>npJ M J\<close>.
  Indeed \<open>Br (Red M) ! J = IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red (N\<^sub>J M J))\<close> (@{thm [source] if2_Br_Red})
  and @{const IncrFirst} leaves row 1 unchanged (@{thm [source] entry_funpow_IncrFirst1});
  the inner row-1 left end is preserved by @{const Red}
  (@{thm [source] m_6_6_Red_leftend_1}) and equals \<open>entry M 1 0 + npJ M J = npJ M J\<close>
  (@{thm [source] entry_NJ_1_0}, core).\<close>

lemma a1_BrRed_row1_head:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and JBr: "J < Lng (Br M)"
  shows "entry (Br (Red M) ! J) 1 0 = npJ M J"
proof -
  let ?e = "Joints M ! J + 1 - npJ M J"
  let ?R = "Red (NJ M J)"
  have brR: "Br (Red M) ! J
           = (IncrFirst ^^ ?e) ?R"
  proof -
    have "Br (Red M)
        = map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))
              [0..<Lng (Br M)]"
      by (rule if2_Br_Red[OF M c0 c1 tne])
    thus ?thesis using JBr by simp
  qed
  have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
  have LR: "Lng ?R = Lng (NJ M J)" by (rule m_6_5_Lng_Red[OF NJT])
  have Rne: "?R \<noteq> []" using LR NJne by (cases ?R) (auto simp: NJ_def)
  have L0: "0 < Lng ?R" using Rne by (cases ?R) auto
  \<comment> \<open>\<open>IncrFirst\<close> preserves row 1.\<close>
  have e1: "entry ((IncrFirst ^^ ?e) ?R) 1 0 = entry ?R 1 0"
    by (rule entry_funpow_IncrFirst1[OF L0])
  \<comment> \<open>\<open>Red\<close> preserves the row-1 left end.\<close>
  have e2: "entry ?R 1 0 = entry (NJ M J) 1 0" by (rule m_6_6_Red_leftend_1[OF NJT])
  have e3: "entry (NJ M J) 1 0 = npJ M J" using entry_NJ_1_0[of M J] c1 by simp
  show ?thesis using brR e1 e2 e3 by simp
qed

text \<open>a1: (B), the \<open>npJ = 0\<close> sub-case.  If \<open>npJ M J = 0\<close> then \<open>npJ (Red M) J = 0\<close>:
  the discriminant \<open>entry (Br (Red M) ! J) 1 0\<close> is \<open>npJ M J\<close>
  (@{thm [source] a1_BrRed_row1_head}), so it is \<open>0\<close>, hence \<open>npJ (Red M) J = 0\<close>
  by @{thm [source] npJ_def}.\<close>

lemma a1_if_npJ_Red_zero:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and JBr: "J < Lng (Br M)"
    and np0: "npJ M J = 0"
  shows "npJ (Red M) J = 0"
proof -
  have "entry (Br (Red M) ! J) 1 0 = npJ M J"
    by (rule a1_BrRed_row1_head[OF M c0 c1 tne JBr])
  hence "entry (Br (Red M) ! J) 1 0 = 0" using np0 by simp
  thus ?thesis by (simp add: npJ_def)
qed

text \<open>a1: the trunk row-1 of \<open>Red M\<close> (core-nontrunk) is the diagonal:
  \<open>j \<le> TrMax M \<Longrightarrow> entry (Red M) 1 j = j\<close>.  Same proof as
  @{thm [source] a1_Red_trunk_row0} but row 1.\<close>

lemma a1_Red_trunk_row1:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and j: "j \<le> TrMax M"
  shows "entry (Red M) 1 j = j"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have mono: "monoT M" using M by (simp add: PT_PS_def)
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  let ?t = "TrMax M"
  let ?tail = "concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                  (Red (NJ M J)))
                     [0..<Lng (Br M)])"
  have rM: "Red M = diagSeq 0 ?t @ ?tail"
    by (rule d_Red_core_nontrunk_unfold[OF MT nz nmu c0 c1 tne])
  have lenD: "Lng (diagSeq 0 ?t) = Suc ?t" by (simp del: upt_Suc)
  have jlt: "j < length (diagSeq 0 ?t)" using j lenD by simp
  have "(Red M) ! j = (diagSeq 0 ?t) ! j"
    using rM jlt by (simp add: nth_append)
  hence step: "entry (Red M) 1 j = entry (diagSeq 0 ?t) 1 j" by (simp add: entry_def)
  have "entry (diagSeq 0 ?t) 1 j = 0 + j"
    by (rule entry_diagSeq) (use j in simp)
  thus ?thesis using step by simp
qed

text \<open>a1: the trunk of \<open>Red M\<close> is \<open>le0\<close>-linear: \<open>a \<le> b \<le> TrMax M \<Longrightarrow>
  le0 (Red M) a b\<close>.  The diagonal trunk entries are \<open>0,1,\<dots>,TrMax M\<close>
  (@{thm [source] a1_Red_trunk_row0}), giving consecutive \<open>nextrel0\<close> steps.\<close>

lemma a1_Red_trunk_nextrel0_step:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and j: "j < TrMax M"
  shows "nextrel0 (Red M) j (Suc j)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have jL: "j < Lng (Red M)" using j tb LrM LMpos by linarith
  have sjL: "Suc j < Lng (Red M)" using j tb LrM LMpos by linarith
  have ej: "entry (Red M) 0 j = j"
    by (rule a1_Red_trunk_row0[OF M c0 c1 tne]) (use j in simp)
  have esj: "entry (Red M) 0 (Suc j) = Suc j"
    by (rule a1_Red_trunk_row0[OF M c0 c1 tne]) (use j in simp)
  show ?thesis unfolding nextrel0_def
    using jL sjL ej esj by simp
qed

lemma a1_Red_trunk_le0:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and ab: "a \<le> b" and bTr: "b \<le> TrMax M"
  shows "le0 (Red M) a b"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have bL: "b < Lng (Red M)" using bTr tb LrM LMpos by linarith
  have rt: "(nextrel0 (Red M))\<^sup>*\<^sup>* a b" using ab bTr
  proof (induction b)
    case 0
    thus ?case by simp
  next
    case (Suc b)
    show ?case
    proof (cases "a = Suc b")
      case True thus ?thesis by simp
    next
      case False
      hence aleb: "a \<le> b" using Suc.prems(1) by simp
      have bTr: "b \<le> TrMax M" using Suc.prems(2) by simp
      have step: "nextrel0 (Red M) b (Suc b)"
        by (rule a1_Red_trunk_nextrel0_step[OF M c0 c1 tne]) (use Suc.prems(2) in simp)
      have "(nextrel0 (Red M))\<^sup>*\<^sup>* a b" by (rule Suc.IH[OF aleb bTr])
      thus ?thesis using step by (rule rtranclp.rtrancl_into_rtrancl)
    qed
  qed
  have aL: "a < Lng (Red M)" using ab bL by linarith
  show ?thesis using rt aL bL by (simp add: le0_def)
qed

text \<open>a1: a proper \<open>le0\<close>-ancestor lies at-or-below the immediate row-0 parent.
  If \<open>le0 M x k\<close>, \<open>x \<noteq> k\<close>, and \<open>k\<close> has a row-0 parent \<open>p\<close>, then \<open>x \<le> p\<close>.
  The \<open>rtrancl\<close> chain decomposes as \<open>(nextrel0)\<^sup>* x y\<close>, \<open>nextrel0 y k\<close>; then \<open>x \<le> y\<close>
  (@{thm [source] nextrel0_rtrancl_mono}) and \<open>y \<le> p\<close>
  (@{thm [source] nextR0_largest_below}).\<close>

lemma a1_le0_ancestor_le_parent:
  assumes le0: "le0 M x k" and ne: "x \<noteq> k"
    and px: "nextR M 0 p k"
  shows "x \<le> p"
proof -
  have r: "(nextrel0 M)\<^sup>*\<^sup>* x k" using le0 by (simp add: le0_def)
  from r ne obtain y where xy: "(nextrel0 M)\<^sup>*\<^sup>* x y" and yk: "nextrel0 M y k"
    by (metis rtranclp.cases)
  have xley: "x \<le> y" using xy by (rule nextrel0_rtrancl_mono)
  have ylt: "y < k" using yk by (simp add: nextrel0_def)
  have yval: "entry M 0 y < entry M 0 k" using yk by (simp add: nextrel0_def)
  have ylep: "y \<le> p" by (rule nextR0_largest_below[OF px ylt yval])
  show ?thesis using xley ylep by simp
qed

text \<open>a1: (B), the \<open>npJ > 0\<close> sub-case.  \<open>npJ (Red M) J = npJ M J\<close>.  The \<open>J\<close>-th first
  node of \<open>Red M\<close> has row-1 value \<open>npJ M J\<close> (@{thm [source] a1_BrRed_row1_head}, via
  @{thm [source] entry_FirstNodes_eq_component} on row 1), and its unique row-1
  parent is the diagonal index \<open>npJ M J - 1\<close>: the trunk row-1 there is
  \<open>npJ M J - 1 < npJ M J\<close>, \<open>le0\<close> holds through the row-0 parent \<open>Joints M ! J\<close>
  (@{thm [source] a1_if_Joints_Red}), and the between-condition follows because
  every \<open>le0\<close>-ancestor of the first node is the node itself or \<open>\<le> Joints M ! J\<close>
  (@{thm [source] a1_le0_ancestor_le_parent}), where the trunk row-1 values are
  \<open>\<ge> npJ M J\<close>.\<close>

lemma a1_if_npJ_Red_pos:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and JBr: "J < Lng (Br M)"
    and nppos: "0 < npJ M J"
  shows "npJ (Red M) J = npJ M J"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have mono: "monoT M" using M by (simp add: PT_PS_def)
  let ?t = "TrMax M"
  let ?n = "npJ M J"
  \<comment> \<open>structural facts about \<open>Red M\<close> (mirroring @{thm [source] a1_if_Joints_Red}).\<close>
  have RMmono: "monoT (Red M)" by (rule m_6_5_Red_preserves_monoT[OF M])
  have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  have RMne: "Red M \<noteq> []" using LrM MT by (cases "Red M") (auto simp: T_PS_def)
  have RMT: "Red M \<in> T_PS" using RMne by (simp add: T_PS_def)
  have RM_PT: "Red M \<in> PT_PS" using RMT RMmono by (simp add: PT_PS_def)
  have brR: "Br (Red M)
           = map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))
                 [0..<Lng (Br M)]" by (rule if2_Br_Red[OF M c0 c1 tne])
  have lenBrR: "Lng (Br (Red M)) = Lng (Br M)" using brR by simp
  have JBrR: "J < Lng (Br (Red M))" using JBr lenBrR by simp
  have trR: "TrMax (Red M) = ?t" by (rule fl_s_TrMax_Red[OF MT mono c0 c1 tne])
  \<comment> \<open>the first node \<open>?FN\<close>.\<close>
  let ?FN = "FirstNodes (Red M) ! J"
  have FNlt: "?FN < Lng (Red M)" by (rule a1_FN_lt[OF RM_PT JBrR])
  \<comment> \<open>row-1 value at \<open>?FN\<close> is \<open>?n\<close>.\<close>
  have FNrow1: "entry (Red M) 1 ?FN = ?n"
  proof -
    have "entry (Red M) 1 ?FN = entry (Br (Red M) ! J) 1 0"
      by (rule entry_FirstNodes_eq_component_gen[OF RM_PT JBrR])
    also have "\<dots> = ?n" by (rule a1_BrRed_row1_head[OF M c0 c1 tne JBr])
    finally show ?thesis .
  qed
  \<comment> \<open>row-0 parent of \<open>?FN\<close> is the diagonal index \<open>Joints M ! J\<close>.\<close>
  have aJTr: "Joints M ! J \<le> ?t"
    using m_6_4_FirstNodes_TrMax_Joints[OF M JBr] by simp
  have nxt0: "nextR (Red M) 0 (Joints M ! J) ?FN"
  proof -
    have e1: "Joints (Red M) ! J = Joints M ! J" by (rule a1_if_Joints_Red[OF M c0 c1 tne JBr])
    have "nextR (Red M) 0 (Joints (Red M) ! J) ?FN"
      by (rule Joints_parent_nextR[OF RM_PT JBrR])
    thus ?thesis using e1 by simp
  qed
  \<comment> \<open>diagonal index \<open>?n - 1\<close> is in the trunk.\<close>
  have nle: "?n \<le> ?t + 1"
  proof -
    have "?n \<le> Joints M ! J + 1" by (rule npJ_le_Joints_Suc[OF M c1 JBr])
    thus ?thesis using aJTr by simp
  qed
  have nm1Tr: "?n - 1 \<le> ?t" using nle nppos by linarith
  have row1_nm1: "entry (Red M) 1 (?n - 1) = ?n - 1"
    by (rule a1_Red_trunk_row1[OF M c0 c1 tne nm1Tr])
  \<comment> \<open>\<open>le0 (Red M) (?n - 1) ?FN\<close>: through the row-0 parent and the diagonal chain.\<close>
  have FNgt: "?t < ?FN"
  proof -
    have "?FN = TrMax (Red M) + 1 + IdxSum (Br (Red M)) ! J"
      by (rule FirstNodes_nth[OF JBrR])
    thus ?thesis using trR by simp
  qed
  have aJltFN: "Joints M ! J < ?FN" using aJTr FNgt by linarith
  \<comment> \<open>diagonal segment is le0-linear: \<open>?n - 1 \<le> Joints M ! J\<close>, both diagonal, le0.\<close>
  have nm1leJ: "?n - 1 \<le> Joints M ! J"
  proof -
    have "?n \<le> Joints M ! J + 1" by (rule npJ_le_Joints_Suc[OF M c1 JBr])
    thus ?thesis using nppos by linarith
  qed
  have le0_diag: "le0 (Red M) (?n - 1) (Joints M ! J)"
    by (rule a1_Red_trunk_le0[OF M c0 c1 tne _ aJTr]) (rule nm1leJ)
  have le0_parentFN: "le0 (Red M) (Joints M ! J) ?FN"
  proof -
    have nr: "nextrel0 (Red M) (Joints M ! J) ?FN" using nxt0 by (simp add: nextR_def)
    have jL: "Joints M ! J < Lng (Red M)" using nr by (simp add: nextrel0_def)
    have "(nextrel0 (Red M))\<^sup>*\<^sup>* (Joints M ! J) ?FN"
      using nr by (rule r_into_rtranclp)
    thus ?thesis using jL FNlt by (simp add: le0_def)
  qed
  have le0FN: "le0 (Red M) (?n - 1) ?FN" by (rule le0_trans[OF le0_diag le0_parentFN])
  \<comment> \<open>the between-condition for \<open>nextrel1 (Red M) (?n - 1) ?FN\<close>.\<close>
  have between1: "\<And>x. ?n - 1 < x \<Longrightarrow> le0 (Red M) x ?FN
                    \<Longrightarrow> ?n \<le> entry (Red M) 1 x"
  proof -
    fix x assume xlo: "?n - 1 < x" and xle: "le0 (Red M) x ?FN"
    show "?n \<le> entry (Red M) 1 x"
    proof (cases "x = ?FN")
      case True thus ?thesis using FNrow1 by simp
    next
      case False
      have xleJ: "x \<le> Joints M ! J"
        by (rule a1_le0_ancestor_le_parent[OF xle False nxt0])
      hence xTr: "x \<le> ?t" using aJTr by simp
      have "entry (Red M) 1 x = x" by (rule a1_Red_trunk_row1[OF M c0 c1 tne xTr])
      moreover have "?n \<le> x" using xlo nppos by linarith
      ultimately show ?thesis by simp
    qed
  qed
  \<comment> \<open>assemble \<open>nextrel1 (Red M) (?n - 1) ?FN\<close>.\<close>
  have nr1: "nextrel1 (Red M) (?n - 1) ?FN"
    unfolding nextrel1_def
  proof (intro conjI allI impI)
    show "?n - 1 < Lng (Red M)" using nm1Tr aJTr FNlt FNgt by linarith
    show "?FN < Lng (Red M)" by (rule FNlt)
    show "?n - 1 < ?FN" using nm1leJ aJltFN by linarith
    show "entry (Red M) 1 (?n - 1) < entry (Red M) 1 ?FN"
      using row1_nm1 FNrow1 nppos by simp
    show "le0 (Red M) (?n - 1) ?FN" by (rule le0FN)
    fix x assume hx: "?n - 1 < x \<and> le0 (Red M) x ?FN"
    have "?n \<le> entry (Red M) 1 x" using hx between1 by blast
    thus "entry (Red M) 1 ?FN \<le> entry (Red M) 1 x" using FNrow1 by simp
  qed
  have nx1: "nextR (Red M) 1 (?n - 1) ?FN" unfolding nextR_def using nr1 by simp
  \<comment> \<open>uniqueness via @{thm [source] nextR1_unique}.\<close>
  have theval: "(THE j. nextR (Red M) 1 j ?FN) = ?n - 1"
  proof (rule the_equality)
    show "nextR (Red M) 1 (?n - 1) ?FN" by (rule nx1)
  next
    fix j assume "nextR (Red M) 1 j ?FN"
    thus "j = ?n - 1" using nx1 by (rule nextR1_unique)
  qed
  \<comment> \<open>discriminant is non-zero so the \<open>else\<close> branch of \<open>npJ\<close> fires.\<close>
  have disc: "entry (Br (Red M) ! J) 1 0 = ?n"
    by (rule a1_BrRed_row1_head[OF M c0 c1 tne JBr])
  have discpos: "entry (Br (Red M) ! J) 1 0 \<noteq> 0" using disc nppos by simp
  have "npJ (Red M) J = Suc (THE j. nextR (Red M) 1 j ?FN)"
    using discpos by (simp add: npJ_def)
  also have "\<dots> = Suc (?n - 1)" using theval by simp
  also have "\<dots> = ?n" using nppos by simp
  finally show ?thesis .
qed

text \<open>a1: (B) the row-1 junction counts of \<open>Red M\<close> coincide with those of \<open>M\<close>:
  \<open>npJ (Red M) J = npJ M J\<close>.  Cases on \<open>npJ M J = 0\<close>
  (@{thm [source] a1_if_npJ_Red_zero}) vs \<open>> 0\<close>
  (@{thm [source] a1_if_npJ_Red_pos}).\<close>

lemma a1_if_npJ_Red:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and JBr: "J < Lng (Br M)"
  shows "npJ (Red M) J = npJ M J"
proof (cases "npJ M J = 0")
  case True
  thus ?thesis using a1_if_npJ_Red_zero[OF M c0 c1 tne JBr True] by simp
next
  case False
  hence "0 < npJ M J" by simp
  thus ?thesis using a1_if_npJ_Red_pos[OF M c0 c1 tne JBr] by simp
qed

text \<open>a1: iterating @{thm [source] m_6_5_Red_IncrFirst}: \<open>Red ((IncrFirst ^^ k) X)
  = Red X\<close> for \<open>X \<in> T\<^sub>PS\<close>.\<close>

lemma a1_Red_funpow_IncrFirst:
  assumes XT: "X \<in> T_PS"
  shows "Red ((IncrFirst ^^ k) X) = Red X"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  have Xne: "X \<noteq> []" using XT by (simp add: T_PS_def)
  have IXne: "(IncrFirst ^^ k) X \<noteq> []"
    using Xne by (metis Lng_funpow_IncrFirst length_0_conv)
  have IXT: "(IncrFirst ^^ k) X \<in> T_PS" using IXne by (simp add: T_PS_def)
  have "Red ((IncrFirst ^^ Suc k) X) = Red (IncrFirst ((IncrFirst ^^ k) X))"
    by (simp add: funpow_swap1)
  also have "\<dots> = Red ((IncrFirst ^^ k) X)" by (rule m_6_5_Red_IncrFirst[OF IXT])
  also have "\<dots> = Red X" by (rule Suc.IH)
  finally show ?case .
qed

text \<open>a1: the \<open>J\<close>-th \<open>N\<^sub>J\<close> of \<open>Red M\<close> equals \<open>IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red (N\<^sub>J M J))\<close>, i.e.
  exactly the \<open>J\<close>-th branch block of \<open>Red M\<close>.  Indeed by (A) and (B) the new head
  of \<open>NJ (Red M) J\<close> is \<open>(Joints M ! J + 1, npJ M J)\<close>, which is already the head of
  the block \<open>IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red (N\<^sub>J M J))\<close> (row 0 \<open>= npJ M J + e\<^sub>J = Joints M ! J + 1\<close>
  by @{thm [source] fin_block_head}; row 1 \<open>= npJ M J\<close> by
  @{thm [source] a1_BrRed_row1_head}), so the head-replacement in \<open>NJ\<close> is the
  identity.\<close>

lemma a1_NJ_Red_eq:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and JBr: "J < Lng (Br M)"
  shows "NJ (Red M) J
       = (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))"
proof -
  let ?e = "Joints M ! J + 1 - npJ M J"
  let ?blk = "(IncrFirst ^^ ?e) (Red (NJ M J))"
  \<comment> \<open>structural facts about \<open>Red M\<close>.\<close>
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have mono: "monoT M" using M by (simp add: PT_PS_def)
  have RMmono: "monoT (Red M)" by (rule m_6_5_Red_preserves_monoT[OF M])
  have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  have RMne: "Red M \<noteq> []" using LrM MT by (cases "Red M") (auto simp: T_PS_def)
  have RMT: "Red M \<in> T_PS" using RMne by (simp add: T_PS_def)
  have RM_PT: "Red M \<in> PT_PS" using RMT RMmono by (simp add: PT_PS_def)
  have brR: "Br (Red M)
           = map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))
                 [0..<Lng (Br M)]" by (rule if2_Br_Red[OF M c0 c1 tne])
  have lenBrR: "Lng (Br (Red M)) = Lng (Br M)" using brR by simp
  have JBrR: "J < Lng (Br (Red M))" using JBr lenBrR by simp
  have blkJ: "Br (Red M) ! J = ?blk" using brR JBr by simp
  \<comment> \<open>head of the block.\<close>
  have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
  have Rne: "Red (NJ M J) \<noteq> []"
    using m_6_5_Lng_Red[OF NJT] NJne by (cases "Red (NJ M J)") (auto simp: NJ_def)
  have blkne: "?blk \<noteq> []" using Rne by (metis Lng_funpow_IncrFirst length_0_conv)
  \<comment> \<open>\<open>NJ (Red M) J\<close> uses Joints/npJ of \<open>Red M\<close>, which equal those of \<open>M\<close> (A,B).\<close>
  have jE: "Joints (Red M) ! J = Joints M ! J" by (rule a1_if_Joints_Red[OF M c0 c1 tne JBr])
  have npE: "npJ (Red M) J = npJ M J" by (rule a1_if_npJ_Red[OF M c0 c1 tne JBr])
  have c0R: "entry (Red M) 0 0 = 0"
    by (rule a1_Red_trunk_row0[OF M c0 c1 tne]) simp
  have c1R: "entry (Red M) 1 0 = entry M 1 0" by (rule m_6_6_Red_leftend_1[OF MT])
  \<comment> \<open>head of \<open>NJ (Red M) J\<close>.\<close>
  have hd_eq: "(entry (Red M) 0 0 + Joints (Red M) ! J + 1,
                entry (Red M) 1 0 + npJ (Red M) J)
             = (Joints M ! J + 1, npJ M J)"
    using c0R c1R c1 jE npE by simp
  have NJR: "NJ (Red M) J = (Joints M ! J + 1, npJ M J) # tl (Br (Red M) ! J)"
    using hd_eq by (simp add: NJ_def)
  \<comment> \<open>head of the block \<open>?blk\<close> equals \<open>(Joints M ! J + 1, npJ M J)\<close>.\<close>
  have blk_hd0: "entry ?blk 0 0 = Joints M ! J + 1"
    by (rule fin_block_head[OF M c0 c1 JBr])
  have blk_hd1: "entry ?blk 1 0 = npJ M J"
    using a1_BrRed_row1_head[OF M c0 c1 tne JBr] blkJ by simp
  have "?blk ! 0 = (Joints M ! J + 1, npJ M J)"
    using blk_hd0 blk_hd1 blkne by (cases ?blk) (auto simp: entry_def)
  hence "?blk = (Joints M ! J + 1, npJ M J) # tl ?blk"
    using blkne by (cases ?blk) auto
  hence "(Joints M ! J + 1, npJ M J) # tl (Br (Red M) ! J) = ?blk"
    using blkJ by simp
  thus ?thesis using NJR by simp
qed

text \<open>a1: (B1) the core-nontrunk idempotency residual:
  \<open>Red (NJ (Red M) J) = Red (NJ M J)\<close>, given the per-branch idempotency IH.
  By @{thm [source] a1_NJ_Red_eq} the left input is \<open>IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red (N\<^sub>J M J))\<close>;
  @{thm [source] a1_Red_funpow_IncrFirst} strips the \<open>IncrFirst\<close> and the inner
  \<open>Red\<close>, leaving \<open>Red (Red (N\<^sub>J M J))\<close>, which the IH collapses to \<open>Red (N\<^sub>J M J)\<close>.\<close>

lemma a1_Red_NJ_Red_residual:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and JBr: "J < Lng (Br M)"
    and IH: "Red (Red (NJ M J)) = Red (NJ M J)"
  shows "Red (NJ (Red M) J) = Red (NJ M J)"
proof -
  let ?e = "Joints M ! J + 1 - npJ M J"
  have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
  have RNJne: "Red (NJ M J) \<noteq> []"
    using m_6_5_Lng_Red[OF NJT] NJne by (cases "Red (NJ M J)") (auto simp: NJ_def)
  have RNJT: "Red (NJ M J) \<in> T_PS" using RNJne by (simp add: T_PS_def)
  have "Red (NJ (Red M) J) = Red ((IncrFirst ^^ ?e) (Red (NJ M J)))"
    using a1_NJ_Red_eq[OF M c0 c1 tne JBr] by simp
  also have "\<dots> = Red (Red (NJ M J))" by (rule a1_Red_funpow_IncrFirst[OF RNJT])
  also have "\<dots> = Red (NJ M J)" by (rule IH)
  finally show ?thesis .
qed

text \<open>a1: (B1) the core-nontrunk branch of idempotency.  Unfold both \<open>Red M\<close> and
  \<open>Red (Red M)\<close> by @{thm [source] d_Red_core_nontrunk_unfold} and align the
  diagonal prefix (\<open>TrMax (Red M) = TrMax M\<close>), the per-branch exponents
  (\<open>Joints\<close>/\<open>npJ\<close> via (A)/(B)) and the residual blocks
  (@{thm [source] a1_Red_NJ_Red_residual}).\<close>

lemma a1_idem_core_nontrunk:
  assumes MT: "M \<in> T_PS" and nz: "\<not> zeroT M" and nmu: "\<not> multiT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and IH: "\<And>J. J < Lng (Br M) \<Longrightarrow> Red (Red (NJ M J)) = Red (NJ M J)"
  shows "Red (Red M) = Red M"
proof -
  have mono: "monoT M" using nz nmu by (simp add: monoT_def multiT_def)
  have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  let ?t = "TrMax M"
  \<comment> \<open>\<open>Red M\<close> is itself core-nontrunk.\<close>
  have RMmono: "monoT (Red M)" by (rule m_6_5_Red_preserves_monoT[OF M_PT])
  have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  have RMne: "Red M \<noteq> []" using LrM MT by (cases "Red M") (auto simp: T_PS_def)
  have RMT: "Red M \<in> T_PS" using RMne by (simp add: T_PS_def)
  have RM_PT: "Red M \<in> PT_PS" using RMT RMmono by (simp add: PT_PS_def)
  have RMnz: "\<not> zeroT (Red M)" using RMmono by (simp add: monoT_def)
  have RMnmu: "\<not> multiT (Red M)" using RMmono by (simp add: multiT_def)
  have c0R: "entry (Red M) 0 0 = 0"
    by (rule a1_Red_trunk_row0[OF M_PT c0 c1 tne]) simp
  have c1R: "entry (Red M) 1 0 = 0"
    using m_6_6_Red_leftend_1[OF MT] c1 by simp
  have trR: "TrMax (Red M) = ?t" by (rule fl_s_TrMax_Red[OF MT mono c0 c1 tne])
  have brR: "Br (Red M)
           = map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))
                 [0..<Lng (Br M)]" by (rule if2_Br_Red[OF M_PT c0 c1 tne])
  have lenBrR: "Lng (Br (Red M)) = Lng (Br M)" using brR by simp
  have tb: "?t \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  with tne have trlt: "?t < Lng M - 1" by linarith
  have tneR: "TrMax (Red M) \<noteq> Lng (Red M) - 1" using trR trlt LrM by simp
  \<comment> \<open>unfold \<open>Red (Red M)\<close>.\<close>
  have unfoldRR: "Red (Red M)
       = diagSeq 0 (TrMax (Red M))
           @ concat (map (\<lambda>J. (IncrFirst ^^ (Joints (Red M) ! J + 1 - npJ (Red M) J))
                                  (Red (NJ (Red M) J)))
                     [0..<Lng (Br (Red M))])"
    by (rule d_Red_core_nontrunk_unfold[OF RMT RMnz RMnmu c0R c1R tneR])
  \<comment> \<open>unfold \<open>Red M\<close>.\<close>
  have unfoldR: "Red M
       = diagSeq 0 ?t
           @ concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                  (Red (NJ M J)))
                     [0..<Lng (Br M)])"
    by (rule d_Red_core_nontrunk_unfold[OF MT nz nmu c0 c1 tne])
  \<comment> \<open>the two block maps agree over the range \<open>[0..<Lng (Br M)]\<close>.\<close>
  have blocks_eq:
    "map (\<lambda>J. (IncrFirst ^^ (Joints (Red M) ! J + 1 - npJ (Red M) J)) (Red (NJ (Red M) J)))
         [0..<Lng (Br (Red M))]
       = map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))
         [0..<Lng (Br M)]"
  proof -
    have "map (\<lambda>J. (IncrFirst ^^ (Joints (Red M) ! J + 1 - npJ (Red M) J)) (Red (NJ (Red M) J)))
              [0..<Lng (Br M)]
        = map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))
              [0..<Lng (Br M)]"
    proof (rule map_cong[OF refl])
      fix J assume "J \<in> set [0..<Lng (Br M)]"
      hence True: "J < Lng (Br M)" by simp
      have jE: "Joints (Red M) ! J = Joints M ! J"
        by (rule a1_if_Joints_Red[OF M_PT c0 c1 tne True])
      have npE: "npJ (Red M) J = npJ M J"
        by (rule a1_if_npJ_Red[OF M_PT c0 c1 tne True])
      have resid: "Red (NJ (Red M) J) = Red (NJ M J)"
        by (rule a1_Red_NJ_Red_residual[OF M_PT c0 c1 tne True IH[OF True]])
      show "(IncrFirst ^^ (Joints (Red M) ! J + 1 - npJ (Red M) J)) (Red (NJ (Red M) J))
          = (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))"
        using jE npE resid by simp
    qed
    thus ?thesis using lenBrR by simp
  qed
  \<comment> \<open>assemble.\<close>
  have "Red (Red M)
      = diagSeq 0 ?t
          @ concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                 (Red (NJ M J)))
                    [0..<Lng (Br M)])"
    using unfoldRR trR blocks_eq by simp
  also have "\<dots> = Red M" using unfoldR by simp
  finally show ?thesis .
qed

text \<open>a1: (D, \<open>m10>0\<close> branch) full \<open>m10>0\<close> idempotency.  Both \<open>Red M\<close> and
  \<open>Red (Red M)\<close> take the \<open>m10>0\<close> productive branch (\<open>Red M\<close> is \<open>monoT\<close> with the
  same row-1 left end \<open>m10 > 0\<close>), reading off \<open>?outMap _ m10\<close> applied to the inner
  \<open>Red (coreReduce _)\<close>.  The two inner values coincide by
  @{thm [source] b2_idem_m10pos} (\<open>Red (coreReduce (Red M)) = Red (coreReduce M)\<close>),
  so the outputs are equal.\<close>

lemma a1_idem_m10pos:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
    and IH: "Red (Red (coreReduce M)) = Red (coreReduce M)"
  shows "Red (Red M) = Red M"
proof -
  let ?m = "entry M 1 0"
  have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have nc: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" using pos by simp
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  let ?outMap = "\<lambda>P m. map (\<lambda>j. (entry P 0 j - entry P 0 m + entry P 1 m,
                                  entry P 1 j)) [m..<Suc (Lng P - 1)]"
  \<comment> \<open>the recursion argument equals \<open>coreReduce M\<close>.\<close>
  let ?arg = "diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
  have creq: "coreReduce M = ?arg" by (rule coreReduce_m10pos_form[OF pos])
  let ?N = "Red ?arg"
  have Ncr: "?N = Red (coreReduce M)" using creq by simp
  \<comment> \<open>\<open>Red M\<close> takes the productive \<open>m10>0\<close> branch.\<close>
  have LN: "Lng ?N = Lng M + ?m" by (rule m_6_5_monoT_Red_fact1_Lng[OF MT pos])
  have jN_ge: "?m \<le> Lng ?N - 1" using LN LMpos by linarith
  have segN_PT: "seg ?N ?m (Lng ?N - 1) \<in> PT_PS"
    by (rule m_6_5_monoT_Red_m10pos[OF M_PT pos])
  have thenM: "?m \<le> Lng ?N - 1 \<and> seg ?N ?m (Lng ?N - 1) \<in> PT_PS"
    using jN_ge segN_PT by simp
  have rM: "Red M = ?outMap ?N ?m"
    using Red.psimps[OF dom] nz nmu nc pos thenM by (simp add: Let_def)
  \<comment> \<open>\<open>Red M\<close> is \<open>monoT\<close> with row-1 left end \<open>?m > 0\<close>.\<close>
  have RMmono: "monoT (Red M)" by (rule m_6_5_Red_preserves_monoT[OF M_PT])
  have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  have RMne: "Red M \<noteq> []" using LrM LMpos by (cases "Red M") auto
  have RMT: "Red M \<in> T_PS" using RMne by (simp add: T_PS_def)
  have RM_PT: "Red M \<in> PT_PS" using RMT RMmono by (simp add: PT_PS_def)
  have RMm10: "entry (Red M) 1 0 = ?m" by (rule m_6_6_Red_leftend_1[OF MT])
  have RMpos: "0 < entry (Red M) 1 0" using RMm10 pos by simp
  have RMnz: "\<not> zeroT (Red M)" using RMmono by (simp add: monoT_def)
  have RMnmu: "\<not> multiT (Red M)" using RMmono by (simp add: multiT_def)
  have RMnc: "\<not> (entry (Red M) 0 0 = 0 \<and> entry (Red M) 1 0 = 0)" using RMpos by simp
  have domRM: "Red_dom (Red M)" by (rule m_6_5_Red_welldef[OF RMT])
  \<comment> \<open>the inner \<open>Red (coreReduce (Red M))\<close> equals \<open>?N\<close> (b2 + leftend).\<close>
  let ?argRM = "diagSeq 0 (entry (Red M) 1 0 - 1) @ (IncrFirst ^^ (entry (Red M) 1 0)) (Red M)"
  have crRMeq: "coreReduce (Red M) = ?argRM" by (rule coreReduce_m10pos_form[OF RMpos])
  have b2: "Red (coreReduce (Red M)) = Red (coreReduce M)"
    by (rule b2_idem_m10pos[OF MT mono pos IH])
  have innerN: "Red ?argRM = ?N"
    using b2 crRMeq Ncr by simp
  \<comment> \<open>\<open>Red (Red M)\<close> takes the productive \<open>m10>0\<close> branch on the SAME inner value.\<close>
  have LNrm: "Lng (Red ?argRM) = Lng (Red M) + entry (Red M) 1 0"
    by (rule m_6_5_monoT_Red_fact1_Lng[OF RMT RMpos])
  have LRMpos: "0 < Lng (Red M)" using RMne by (cases "Red M") auto
  have jNrm_ge: "entry (Red M) 1 0 \<le> Lng (Red ?argRM) - 1" using LNrm LRMpos by linarith
  have segNrm_PT: "seg (Red ?argRM) (entry (Red M) 1 0) (Lng (Red ?argRM) - 1) \<in> PT_PS"
    by (rule m_6_5_monoT_Red_m10pos[OF RM_PT RMpos])
  have thenRM: "entry (Red M) 1 0 \<le> Lng (Red ?argRM) - 1
                \<and> seg (Red ?argRM) (entry (Red M) 1 0) (Lng (Red ?argRM) - 1) \<in> PT_PS"
    using jNrm_ge segNrm_PT by simp
  have rRM: "Red (Red M) = ?outMap (Red ?argRM) (entry (Red M) 1 0)"
    using Red.psimps[OF domRM] RMnz RMnmu RMnc RMpos thenRM by (simp add: Let_def)
  \<comment> \<open>conclude: same map, same \<open>m\<close>, same inner \<open>?N\<close>.\<close>
  have "Red (Red M) = ?outMap ?N ?m" using rRM innerN RMm10 by simp
  also have "\<dots> = Red M" using rM by simp
  finally show ?thesis .
qed

text \<open>a1: (D) non-multi idempotency: \<open>M \<in> T\<^sub>PS \<Longrightarrow> \<not> multiT M \<Longrightarrow>
  Red (Red M) = Red M\<close>.  By @{thm [source] Red.pinduct}: the \<open>zeroT\<close>,
  core-trunk, shift and \<open>m10>0\<close> branches are the existing bricks
  (@{thm [source] idem2_zeroT}, @{thm [source] idem2_core_trunk},
  @{thm [source] idem2_shift_reduce}, @{thm [source] b2_idem_m10pos}); the
  core-nontrunk branch is @{thm [source] a1_idem_core_nontrunk}, whose per-branch
  IH \<open>Red (Red (N\<^sub>J M J)) = Red (N\<^sub>J M J)\<close> is the core-nontrunk pinduct IH
  (\<open>N\<^sub>J M J\<close> is non-multi by @{thm [source] NJ_nonmulti}, so the \<open>\<not> multiT\<close>
  premise holds).\<close>

lemma idem_nonmulti:
  assumes MT0: "M \<in> T_PS" and nmu0: "\<not> multiT M"
  shows "Red (Red M) = Red M"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT0])
  have "M \<in> T_PS \<longrightarrow> \<not> multiT M \<longrightarrow> Red (Red M) = Red M"
    using domM
  proof (induction M rule: Red.pinduct)
    case (1 M)
    note dom    = 1(1)
    note IH_bz  = 1(3)  \<comment> \<open>core-nontrunk IH (recursion on \<open>N\<^sub>J M J\<close>)\<close>
    note IH_sh  = 1(4)  \<comment> \<open>shift IH (recursion on \<open>coreReduce M\<close>)\<close>
    show ?case
    proof (rule impI, rule impI)
      assume MT: "M \<in> T_PS" and nmu: "\<not> multiT M"
      show "Red (Red M) = Red M"
      proof (cases "zeroT M")
        case True
        thus ?thesis by (rule idem2_zeroT[OF MT])
      next
        case nz: False
        have mono: "monoT M" using nz nmu by (simp add: monoT_def multiT_def)
        let ?m00 = "entry M 0 0"
        let ?m10 = "entry M 1 0"
        show ?thesis
        proof (cases "?m00 = 0 \<and> ?m10 = 0")
          case core: True
          hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
          show ?thesis
          proof (cases "TrMax M = Lng M - 1")
            case True
            thus ?thesis by (rule idem2_core_trunk[OF MT nz nmu c0 c1])
          next
            case tne: False
            \<comment> \<open>the core-nontrunk branch: discharge via the per-branch IH.\<close>
            have IHbr: "\<And>J. J < Lng (Br M) \<Longrightarrow> Red (Red (NJ M J)) = Red (NJ M J)"
            proof -
              fix J assume JBr: "J < Lng (Br M)"
              have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
              have Jmem: "J \<in> set [0..<Lng (Br M)]" using JBr by simp
              have core': "?m00 = 0 \<and> ?m10 = 0" using core by simp
              \<comment> \<open>the raw recursive argument equals \<open>NJ M J\<close> (cf. @{thm [source] d_Red_core_nontrunk_unfold}).\<close>
              have npE: "(if entry (Br M ! J) 1 0 = 0 then 0
                          else Suc (THE j. nextR M 1 j (FirstNodes M ! J))) = npJ M J"
                by (simp add: npJ_def)
              have argE: "((entry M 0 0 + Joints M ! J + 1, entry M 1 0 + npJ M J)
                           # tl (Br M ! J)) = NJ M J"
                by (simp add: NJ_def)
              \<comment> \<open>the raw IH for the recursive argument, rewritten to \<open>NJ M J\<close>.\<close>
              have ih: "NJ M J \<in> T_PS \<longrightarrow> \<not> multiT (NJ M J)
                          \<longrightarrow> Red (Red (NJ M J)) = Red (NJ M J)"
                using IH_bz[OF nz nmu refl refl refl refl core' tne Jmem]
                by (simp only: npE argE)
              have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
              have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
              have NJnm: "\<not> multiT (NJ M J)" by (rule NJ_nonmulti[OF M_PT c0 c1 JBr])
              show "Red (Red (NJ M J)) = Red (NJ M J)" using ih NJT NJnm by blast
            qed
            show ?thesis by (rule a1_idem_core_nontrunk[OF MT nz nmu c0 c1 tne IHbr])
          qed
        next
          case nc: False
          have ncc: "\<not> (?m00 = 0 \<and> ?m10 = 0)" using nc by simp
          have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
          show ?thesis
          proof (cases "?m10 = 0")
            case True
            \<comment> \<open>shift branch: \<open>coreReduce M\<close> is the shift map; its idempotency is the IH.\<close>
            let ?sh = "map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc (Lng M - 1)]"
            have sheq: "?sh = coreReduce M"
              using True LMpos by (simp add: coreReduce_def del: upt_Suc)
            have shne: "?sh \<noteq> []" using LMpos by simp
            have crne: "coreReduce M \<noteq> []" using sheq shne by simp
            have crT: "coreReduce M \<in> T_PS" using crne by (simp add: T_PS_def)
            have IHsh: "Red (Red (coreReduce M)) = Red (coreReduce M)"
            proof -
              have raw: "?sh \<in> T_PS \<longrightarrow> \<not> multiT ?sh \<longrightarrow> Red (Red ?sh) = Red ?sh"
                by (rule IH_sh[OF nz nmu refl refl refl refl ncc True])
              have shnm: "\<not> multiT (coreReduce M)" by (rule coreReduce_nonmulti[OF MT mono])
              show ?thesis using raw sheq crT shnm by simp
            qed
            show ?thesis by (rule idem2_shift_reduce[OF MT mono ncc True IHsh])
          next
            case False
            hence pos: "0 < ?m10" by simp
            \<comment> \<open>\<open>m10>0\<close> branch: the recursion argument equals \<open>coreReduce M\<close>
              (@{thm [source] coreReduce_m10pos_form}), so the \<open>m10>0\<close> pinduct IH
              gives \<open>Red (Red (coreReduce M)) = Red (coreReduce M)\<close>, which
              @{thm [source] b2_idem_m10pos} consumes.\<close>
            note IH_m1 = 1(5)
            let ?arg = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
            have creq: "coreReduce M = ?arg" by (rule coreReduce_m10pos_form[OF pos])
            have Mne2: "M \<noteq> []" using MT by (simp add: T_PS_def)
            have funne: "(IncrFirst ^^ ?m10) M \<noteq> []"
              using Mne2 by (metis Lng_funpow_IncrFirst length_0_conv)
            have argne: "?arg \<noteq> []" using funne by simp
            have argT: "?arg \<in> T_PS" using argne by (simp add: T_PS_def)
            have IHcr: "Red (Red (coreReduce M)) = Red (coreReduce M)"
            proof -
              have raw: "?arg \<in> T_PS \<longrightarrow> \<not> multiT ?arg \<longrightarrow> Red (Red ?arg) = Red ?arg"
                by (rule IH_m1[OF nz nmu refl refl refl refl ncc False])
              have argnm: "\<not> multiT (coreReduce M)" by (rule coreReduce_nonmulti[OF MT mono])
              hence "\<not> multiT ?arg" using creq by simp
              thus ?thesis using raw argT creq by simp
            qed
            show ?thesis by (rule a1_idem_m10pos[OF MT mono pos IHcr])
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using MT0 nmu0 by blast
qed

end

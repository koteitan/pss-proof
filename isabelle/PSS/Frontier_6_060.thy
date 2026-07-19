theory Frontier_6_060
  imports P_6_6_reduced_slice
begin

subsection \<open>§6.6 keystone (e)-CRUX: prepending a diagonal segment\<close>

text \<open>
  Structural facts about \<open>A = diagSeq 0 k @ M\<close> when \<open>M\<close> is monotone and the
  junction values dominate the diagonal (\<open>k < M\<^bsub>0,0\<^esub>\<close>, \<open>k < M\<^bsub>1,0\<^esub>\<close>).  These are
  the foundation of the §6.6 keystone (e)-lemma.  Empirically TRUE (re-verified
  23655/0 over \<open>monoT M\<close>, \<open>Lng M \<le> 4\<close>, values \<open>\<le> 4\<close>, \<open>0 \<le> k < M\<^bsub>0,0\<^esub>\<close>,
  \<open>k < M\<^bsub>1,0\<^esub>\<close>).  Side conditions are the weakest correct form: \<open>k < M\<^bsub>0,0\<^esub>\<close> and
  \<open>k < M\<^bsub>1,0\<^esub>\<close> (NOT \<open>\<le>\<close>; the junction step \<open>(k,k) <\<^sup>Next (M\<^bsub>0,0\<^esub>,M\<^bsub>1,0\<^esub>)\<close> needs
  strict increase in both rows).  No \<open>Red\<close> is involved \<open>-\<close> pure trunk-combinatorics,
  built on @{thm [source] nextR1_diagSeq_append}, @{thm [source] le_TrMax_intro},
  @{thm [source] TrMax_in_S}, @{thm [source] TrMax_stop} and the drop-shift transfer
  @{thm [source] poper_nextrel1_drop}.
\<close>

text \<open>The diagonal prefix \<open>diagSeq 0 k\<close> has length \<open>Suc k\<close>, so the tail past it is
  exactly \<open>M\<close>: \<open>drop (Suc k) (diagSeq 0 k @ M) = M\<close>.\<close>

lemma ecrux_drop_tail: "drop (Suc k) (diagSeq 0 k @ M) = M"
proof -
  have "Lng (diagSeq 0 k) = Suc k" by simp
  thus ?thesis by simp
qed

lemma ecrux_Lng: "Lng (diagSeq 0 k @ M) = Suc k + Lng M"
  by simp

text \<open>m (§6.6 keystone (e)-CRUX, part 1): prepending a length-\<open>Suc k\<close> diagonal to a
  monotone \<open>M\<close> whose first pair dominates the diagonal raises \<open>TrMax\<close> by exactly
  \<open>Suc k\<close>.  The whole diagonal (and its junction to \<open>M\<close>) is one trunk run, and past
  the junction the trunk of \<open>A\<close> mirrors that of \<open>M\<close> (drop-shift transfer).\<close>

lemma ecrux_TrMax_diag_prefix:
  assumes mono: "monoT M" and r0: "k < entry M 0 0" and r1: "k < entry M 1 0"
  shows "TrMax (diagSeq 0 k @ M) = Suc k + TrMax M"
proof -
  let ?c = "Suc k"
  let ?A = "diagSeq 0 k @ M"
  have "0 < Lng M" using mono by (simp add: monoT_def leR_def le0_def)
  hence Mne: "M \<noteq> []" by auto
  have MT: "M \<in> T_PS" using Mne by (simp add: T_PS_def)
  have LM: "0 < Lng M" using Mne by (cases M) auto
  have LA: "Lng ?A = ?c + Lng M" using Lng_diagSeq[of 0 k] by simp
  have LApos: "0 < Lng ?A" using LA by linarith
  have "?A \<noteq> []" using LApos by (cases ?A) auto
  hence AT: "?A \<in> T_PS" by (simp add: T_PS_def)
  have dropeq: "drop ?c ?A = M" by (rule ecrux_drop_tail)
  \<comment> \<open>lower bound: every step below \<open>?c + TrMax M\<close> is a trunk step of \<open>?A\<close>.\<close>
  have lower: "?c + TrMax M \<le> TrMax ?A"
  proof -
    have allstep: "\<forall>j'<?c + TrMax M. nextR ?A 1 j' (j' + 1)"
    proof (intro allI impI)
      fix j' assume j'lt: "j' < ?c + TrMax M"
      show "nextR ?A 1 j' (j' + 1)"
      proof (cases "j' < ?c")
        case True
        hence jk: "j' \<le> k" by simp
        have "nextR (diagSeq 0 k @ M) 1 j' (Suc j')"
          by (rule nextR1_diagSeq_append[OF Mne r0 r1 jk])
        thus ?thesis by simp
      next
        case False
        hence jge: "?c \<le> j'" by simp
        let ?a = "j' - ?c"
        have aTr: "?a < TrMax M" using j'lt jge by simp
        have aL: "?a < Lng M - ?c + ?c" using aTr TrMax_bound[OF MT] LM by linarith
        have aLA: "?a < Lng ?A - ?c" using aTr TrMax_bound[OF MT] LA by linarith
        have a1LA: "?a + 1 < Lng ?A - ?c" using aTr TrMax_bound[OF MT] LA by linarith
        have stepM: "nextR M 1 ?a (?a + 1)" using TrMax_in_S[OF MT] aTr by simp
        have rel: "nextrel1 (drop ?c ?A) ?a (?a + 1)
                    \<longleftrightarrow> nextrel1 ?A (?c + ?a) (?c + (?a + 1))"
          by (rule poper_nextrel1_drop[OF aLA a1LA])
        have lhs: "nextrel1 M ?a (?a + 1)" using stepM by (simp add: nextR_def)
        have "nextrel1 ?A (?c + ?a) (?c + (?a + 1))" using rel lhs dropeq by simp
        hence "nextrel1 ?A j' (j' + 1)" using jge by simp
        thus ?thesis by (simp add: nextR_def)
      qed
    qed
    show ?thesis by (rule le_TrMax_intro[OF AT allstep])
  qed
  \<comment> \<open>upper bound: case on whether \<open>M\<close> is all-trunk.\<close>
  have upper: "TrMax ?A \<le> ?c + TrMax M"
  proof (cases "TrMax M = Lng M - 1")
    case True
    \<comment> \<open>\<open>?c + TrMax M = Lng ?A - 1\<close>, which bounds \<open>TrMax\<close>.\<close>
    have "TrMax ?A \<le> Lng ?A - 1" by (rule TrMax_bound[OF AT])
    also have "\<dots> = ?c + (Lng M - 1)" using LA LM by simp
    also have "\<dots> = ?c + TrMax M" using True by simp
    finally show ?thesis .
  next
    case False
    have trlt: "TrMax M < Lng M - 1" using False TrMax_bound[OF MT] by simp
    show ?thesis
    proof (rule ccontr)
      assume "\<not> TrMax ?A \<le> ?c + TrMax M"
      hence gt: "?c + TrMax M < TrMax ?A" by simp
      \<comment> \<open>the step at \<open>?c + TrMax M\<close> is then a trunk step of \<open>?A\<close>.\<close>
      have stepA: "nextR ?A 1 (?c + TrMax M) ((?c + TrMax M) + 1)"
        using TrMax_in_S[OF AT] gt by simp
      \<comment> \<open>transfer it back to a step of \<open>M\<close> at \<open>TrMax M\<close>.\<close>
      have b0: "TrMax M < Lng ?A - ?c" using trlt LA LM by linarith
      have b1: "TrMax M + 1 < Lng ?A - ?c" using trlt LA LM by linarith
      have rel: "nextrel1 (drop ?c ?A) (TrMax M) (TrMax M + 1)
                  \<longleftrightarrow> nextrel1 ?A (?c + TrMax M) (?c + (TrMax M + 1))"
        by (rule poper_nextrel1_drop[OF b0 b1])
      have "nextrel1 ?A (?c + TrMax M) (?c + (TrMax M + 1))"
        using stepA by (simp add: nextR_def)
      hence "nextrel1 (drop ?c ?A) (TrMax M) (TrMax M + 1)" using rel by simp
      hence "nextR M 1 (TrMax M) (TrMax M + 1)" using dropeq by (simp add: nextR_def)
      thus False using TrMax_stop[OF MT trlt] by simp
    qed
  qed
  show ?thesis using lower upper by simp
qed

subsection \<open>§6.6 keystone (e)-CRUX: \<open>Red (diagSeq 0 (m\<^sub>1\<^sub>0-1) @ M) = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ Red M\<close>\<close>

text \<open>wf5-ecrux helper: for a mono \<open>Y\<close> whose row-0 dominates the diagonal
  (\<open>Suc k \<le> entry Y 0 0\<close>, hence \<open>\<le> entry Y 0 j\<close> at every column by
  @{thm [source] entry0_ge_min}), bumping \<open>diagSeq 0 k @ Y\<close> at the cut \<open>Suc k\<close>
  is exactly one @{const IncrFirst} on the tail \<open>Y\<close>: the diagonal values
  \<open>0..k\<close> are all \<open>< Suc k\<close> (fixed), and every tail row-0 value is \<open>\<ge> Suc k\<close>
  (incremented).\<close>

lemma ecrux_bumpAt_diag_IncrFirst:
  assumes YT: "Y \<in> T_PS" and mono: "monoT Y" and dom0: "Suc k \<le> entry Y 0 0"
  shows "bumpAt (diagSeq 0 k @ Y) (Suc k) = diagSeq 0 k @ IncrFirst Y"
proof (rule nth_equalityI)
  let ?A = "diagSeq 0 k @ Y"
  have LY: "0 < Lng Y" using YT by (cases Y) (auto simp: T_PS_def)
  have LA: "Lng ?A = Suc k + Lng Y" by simp
  show "length (bumpAt ?A (Suc k)) = length (diagSeq 0 k @ IncrFirst Y)"
    by simp
  fix p assume p: "p < length (bumpAt ?A (Suc k))"
  have pA: "p < Lng ?A" using p by simp
  have pLA: "p < Suc k + Lng Y" using pA LA by simp
  show "bumpAt ?A (Suc k) ! p = (diagSeq 0 k @ IncrFirst Y) ! p"
  proof (cases "p \<le> k")
    case True
    \<comment> \<open>diagonal prefix: row-0 value \<open>p \<le> k < Suc k\<close>, untouched by the bump.\<close>
    have e0A: "entry ?A 0 p = p" by (rule entry_diagSeq_append_lo[OF True])
    have e1A: "entry ?A 1 p = p" by (rule entry_diagSeq_append_lo[OF True])
    have b0: "entry (bumpAt ?A (Suc k)) 0 p = bumpv (Suc k) (entry ?A 0 p)"
      by (rule entry_bumpAt0[OF pA])
    have b0v: "bumpv (Suc k) (entry ?A 0 p) = p" using e0A True by (simp add: bumpv_def)
    have b1: "entry (bumpAt ?A (Suc k)) 1 p = entry ?A 1 p" by (rule entry_bumpAt1[OF pA])
    have pAb: "p < Lng (bumpAt ?A (Suc k))" using pA by simp
    have fst0: "fst (bumpAt ?A (Suc k) ! p) = p" using b0 b0v by (simp add: entry_def)
    have snd0: "snd (bumpAt ?A (Suc k) ! p) = p" using b1 e1A by (simp add: entry_def)
    have lhs: "bumpAt ?A (Suc k) ! p = (p, p)"
      using fst0 snd0 by (metis prod.collapse)
    \<comment> \<open>RHS diagonal prefix at \<open>p \<le> k\<close> is also \<open>(p,p)\<close>.\<close>
    have pld: "p < length (diagSeq 0 k)" using True by simp
    have "(diagSeq 0 k @ IncrFirst Y) ! p = diagSeq 0 k ! p"
      using pld by (simp add: nth_append)
    also have "\<dots> = (p, p)" using diagSeq_nth[of p k 0] True by simp
    finally have rhs: "(diagSeq 0 k @ IncrFirst Y) ! p = (p, p)" .
    show ?thesis using lhs rhs by simp
  next
    case False
    \<comment> \<open>tail: \<open>p = Suc k + a\<close> with \<open>a < Lng Y\<close>; row-0 value \<open>\<ge> Suc k\<close>, bumped.\<close>
    hence pk: "Suc k \<le> p" by simp
    let ?a = "p - Suc k"
    have pe: "p = Suc k + ?a" using pk by simp
    have aLY: "?a < Lng Y" using pLA pk by simp
    have e0A: "entry ?A 0 p = entry Y 0 ?a"
      using entry_diagSeq_append_hi[OF aLY, where p=0 and k=k] pe by simp
    have e1A: "entry ?A 1 p = entry Y 1 ?a"
      using entry_diagSeq_append_hi[OF aLY, where p=1 and k=k] pe by simp
    have dom_a: "entry Y 0 0 \<le> entry Y 0 ?a" by (rule entry0_ge_min[OF YT mono aLY])
    have geA: "Suc k \<le> entry ?A 0 p" using e0A dom0 dom_a by simp
    have b0: "entry (bumpAt ?A (Suc k)) 0 p = bumpv (Suc k) (entry ?A 0 p)"
      by (rule entry_bumpAt0[OF pA])
    have b0v: "bumpv (Suc k) (entry ?A 0 p) = Suc (entry Y 0 ?a)"
      using geA e0A by (simp add: bumpv_def)
    have b1: "entry (bumpAt ?A (Suc k)) 1 p = entry Y 1 ?a"
      using entry_bumpAt1[OF pA] e1A by simp
    have fst0: "fst (bumpAt ?A (Suc k) ! p) = Suc (entry Y 0 ?a)"
      using b0 b0v by (simp add: entry_def)
    have snd0: "snd (bumpAt ?A (Suc k) ! p) = entry Y 1 ?a"
      using b1 by (simp add: entry_def)
    have lhs: "bumpAt ?A (Suc k) ! p = (Suc (entry Y 0 ?a), entry Y 1 ?a)"
      using fst0 snd0 by (metis prod.collapse)
    \<comment> \<open>RHS: tail of \<open>diagSeq 0 k @ IncrFirst Y\<close> at \<open>p = Suc k + a\<close>.\<close>
    have aLI: "?a < Lng (IncrFirst Y)" using aLY by simp
    have "(diagSeq 0 k @ IncrFirst Y) ! p = IncrFirst Y ! ?a"
      using pe by (simp add: nth_append)
    also have "\<dots> = (entry (IncrFirst Y) 0 ?a, entry (IncrFirst Y) 1 ?a)"
      using aLI by (simp add: entry_def)
    also have "\<dots> = (Suc (entry Y 0 ?a), entry Y 1 ?a)"
      using entry_IncrFirst[OF aLY, of 0] entry_IncrFirst[OF aLY, of 1] by simp
    finally have rhs: "(diagSeq 0 k @ IncrFirst Y) ! p = (Suc (entry Y 0 ?a), entry Y 1 ?a)" .
    show ?thesis using lhs rhs by simp
  qed
qed

text \<open>wf5-ecrux helper: the cut condition for \<open>diagSeq 0 k @ Y\<close> at \<open>Suc k\<close>.
  The trunk runs through the whole diagonal (\<open>TrMax \<ge> Suc k\<close> by
  @{thm [source] TrMax_diagSeq_append_ge}), so every post-trunk index lands in
  the tail \<open>Y\<close>, where row-0 \<open>\<ge> Suc k\<close> (dominance).\<close>

lemma ecrux_cutOK_diag:
  assumes YT: "Y \<in> T_PS" and mono: "monoT Y"
    and r0: "k < entry Y 0 0" and r1: "k < entry Y 1 0"
  shows "cutOK (diagSeq 0 k @ Y) (Suc k)"
proof -
  let ?A = "diagSeq 0 k @ Y"
  have Yne: "Y \<noteq> []" using YT by (simp add: T_PS_def)
  have trge: "Suc k \<le> TrMax ?A" by (rule TrMax_diagSeq_append_ge[OF Yne r0 r1])
  have LA: "Lng ?A = Suc k + Lng Y" by simp
  have "\<forall>j. TrMax ?A < j \<longrightarrow> j < Lng ?A \<longrightarrow> Suc k \<le> entry ?A 0 j"
  proof (intro allI impI)
    fix j assume jt: "TrMax ?A < j" and jl: "j < Lng ?A"
    have jge: "Suc k \<le> j" using jt trge by simp
    let ?a = "j - Suc k"
    have je: "j = Suc k + ?a" using jge by simp
    have aLY: "?a < Lng Y" using jl LA jge by simp
    have e0: "entry ?A 0 j = entry Y 0 ?a"
      using entry_diagSeq_append_hi[OF aLY, where p=0 and k=k] je by simp
    have dom_a: "entry Y 0 0 \<le> entry Y 0 ?a" by (rule entry0_ge_min[OF YT mono aLY])
    show "Suc k \<le> entry ?A 0 j" using e0 r0 dom_a by simp
  qed
  thus ?thesis by (simp add: cutOK_def)
qed

text \<open>wf5-ecrux helper (one step): \<open>Red\<close> is unchanged by one @{const IncrFirst} on
  the tail of a dominating diagonal prefix.  This is the cut-bump engine
  (@{thm [source] fin_cut_bump_Red}) instance with the bump identity
  (@{thm [source] ecrux_bumpAt_diag_IncrFirst}) and the cut
  (@{thm [source] ecrux_cutOK_diag}).\<close>

lemma ecrux_Red_diag_IncrFirst_step:
  assumes YT: "Y \<in> T_PS" and mono: "monoT Y"
    and r0: "k < entry Y 0 0" and r1: "k < entry Y 1 0"
  shows "Red (diagSeq 0 k @ IncrFirst Y) = Red (diagSeq 0 k @ Y)"
proof -
  let ?A = "diagSeq 0 k @ Y"
  have AT: "?A \<in> T_PS" using YT by (simp add: T_PS_def)
  have cut: "cutOK ?A (Suc k)" by (rule ecrux_cutOK_diag[OF YT mono r0 r1])
  have dom0: "Suc k \<le> entry Y 0 0" using r0 by simp
  have bumpId: "bumpAt ?A (Suc k) = diagSeq 0 k @ IncrFirst Y"
    by (rule ecrux_bumpAt_diag_IncrFirst[OF YT mono dom0])
  have "Red (bumpAt ?A (Suc k)) = Red ?A" by (rule fin_cut_bump_Red[OF cut AT])
  thus ?thesis using bumpId by simp
qed

text \<open>wf5-ecrux helper (iterate): \<open>Red\<close> is unchanged by \<open>i\<close>-fold @{const IncrFirst}
  on the tail.  Each step preserves the hypotheses: \<open>IncrFirst\<close> keeps \<open>monoT\<close>
  and \<open>T\<^sub>PS\<close>, raises row-0 (so \<open>k <\<close> persists), and fixes row-1.\<close>

lemma ecrux_Red_diag_IncrFirst_pow:
  assumes YT: "Y \<in> T_PS" and mono: "monoT Y"
    and r0: "k < entry Y 0 0" and r1: "k < entry Y 1 0"
  shows "Red (diagSeq 0 k @ (IncrFirst ^^ i) Y) = Red (diagSeq 0 k @ Y)"
  using YT mono r0 r1
proof (induction i arbitrary: Y)
  case 0
  show ?case by simp
next
  case (Suc i)
  let ?Y' = "IncrFirst Y"
  have LY: "0 < Lng Y" using Suc.prems(1) by (cases Y) (auto simp: T_PS_def)
  have Y'T: "?Y' \<in> T_PS" using Suc.prems(1) by (simp add: T_PS_def IncrFirst_def)
  have Y'mono: "monoT ?Y'" using Suc.prems(2) by (simp add: IncrFirst_monoT_eq)
  have e0: "entry ?Y' 0 0 = Suc (entry Y 0 0)" using entry_IncrFirst[OF LY, of 0] by simp
  have e1: "entry ?Y' 1 0 = entry Y 1 0" using entry_IncrFirst[OF LY, of 1] by simp
  have r0': "k < entry ?Y' 0 0" using Suc.prems(3) e0 by simp
  have r1': "k < entry ?Y' 1 0" using Suc.prems(4) e1 by simp
  \<comment> \<open>peel one \<open>IncrFirst\<close> off the iterate, push it through via the IH on \<open>Y'\<close>.\<close>
  have shift: "(IncrFirst ^^ Suc i) Y = (IncrFirst ^^ i) ?Y'"
    by (simp add: funpow_Suc_right del: funpow.simps)
  have "Red (diagSeq 0 k @ (IncrFirst ^^ Suc i) Y)
          = Red (diagSeq 0 k @ (IncrFirst ^^ i) ?Y')"
    using shift by simp
  also have "\<dots> = Red (diagSeq 0 k @ ?Y')"
    by (rule Suc.IH[OF Y'T Y'mono r0' r1'])
  also have "\<dots> = Red (diagSeq 0 k @ Y)"
    by (rule ecrux_Red_diag_IncrFirst_step[OF Suc.prems(1,2,3,4)])
  finally show ?case .
qed

text \<open>wf5-ecrux: \<open>Red (diagSeq 0 k @ M) = Red (coreReduce M)\<close> for \<open>k = m\<^sub>1\<^sub>0 - 1\<close>.
  Since \<open>coreReduce M = diagSeq 0 k @ IncrFirst\<^bsup>m\<^sub>1\<^sub>0\<^esup> M\<close>
  (@{thm [source] coreReduce_m10pos_form}), the two differ only by \<open>m\<^sub>1\<^sub>0\<close>
  tail-@{const IncrFirst}s, collapsed by @{thm [source] ecrux_Red_diag_IncrFirst_pow}.\<close>

lemma ecrux_Red_diag_eq_Red_coreReduce:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and r0: "entry M 1 0 - 1 < entry M 0 0" and pos: "0 < entry M 1 0"
  shows "Red (diagSeq 0 (entry M 1 0 - 1) @ M) = Red (coreReduce M)"
proof -
  let ?k = "entry M 1 0 - 1"
  have r1: "?k < entry M 1 0" using pos by simp
  have crM: "coreReduce M = diagSeq 0 ?k @ (IncrFirst ^^ (entry M 1 0)) M"
    by (rule coreReduce_m10pos_form[OF pos])
  have "Red (coreReduce M) = Red (diagSeq 0 ?k @ (IncrFirst ^^ (entry M 1 0)) M)"
    using crM by simp
  also have "\<dots> = Red (diagSeq 0 ?k @ M)"
    by (rule ecrux_Red_diag_IncrFirst_pow[OF MT mono r0 r1])
  finally show ?thesis by simp
qed

end

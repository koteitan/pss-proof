theory Frontier_6_043
  imports P_6_5_monoT_Red
begin

subsection \<open>§6.4 NJ-alignment: tail-\<open>IncrFirst\<close> equivariance of trunk/branches\<close>

text \<open>
  This section proves a purely §6.4 structural fact (NO @{const Red}): the
  trunk/branch decomposition (@{const TrMax}, @{const Br}, @{const FirstNodes},
  @{const Joints}, @{const npJ}, and the block exponent \<open>e\<^sub>J = Joints!J+1-npJ\<close>)
  is invariant when row 0 of a
  tail suffix is bumped by \<open>+1\<close>, provided the tail sits strictly row-0-above
  the prefix (the \<open>cut\<close> condition).  The motivating instance is
  \<open>coreReduce M\<close> vs. \<open>coreReduce (IncrFirst M)\<close> for a mono \<open>M\<close> with
  \<open>m\<^sub>1\<^sub>0 > 0\<close>: both share the length-\<open>m\<^sub>1\<^sub>0\<close> diagonal prefix and differ only by one
  extra @{const IncrFirst} on the tail.

  The key reduction is that the whole decomposition depends only on the ORDER
  of row-0 entries (via @{const nextrel0}/@{const nextrel1}) plus the row-1
  values, and the bump \<open>v \<mapsto> (if v < n then v else Suc v)\<close> is an order
  isomorphism on values: it fixes the prefix values (all \<open>< n\<close>) and shifts the
  tail values (all \<open>\<ge> n\<close>) by 1, preserving every strict comparison.
  Empirically 19296/19296 (abstract cut-invariant, len\<le>4 val\<le>2) and the
  concrete coreReduce instance 744/744 (len\<le>3 val\<le>3).
\<close>

text \<open>The value-bump \<open>bumpv n\<close> is strictly monotone, hence an order iso.\<close>

definition bumpv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bumpv n v = (if v < n then v else Suc v)"

lemma bumpv_strict_mono: "(bumpv n a < bumpv n b) = (a < b)"
  by (auto simp: bumpv_def)

lemma bumpv_le: "(bumpv n a \<le> bumpv n b) = (a \<le> b)"
  by (auto simp: bumpv_def)


text \<open>Abstract hypotheses linking \<open>A\<close> and \<open>X\<close> on a cut at \<open>n\<close>:
  equal length; row 0 of \<open>A\<close> is the bump of row 0 of \<open>X\<close>; row 1 shared.\<close>

locale tail_bump =
  fixes A X :: pairseq and n :: nat
  assumes len_eq: "Lng A = Lng X"
    and row0_bump: "\<And>j. j < Lng X \<Longrightarrow> entry A 0 j = bumpv n (entry X 0 j)"
    and row1_eq:   "\<And>j. j < Lng X \<Longrightarrow> entry A 1 j = entry X 1 j"
begin

lemma row0_lt: "\<lbrakk>a < Lng X; b < Lng X\<rbrakk> \<Longrightarrow> (entry A 0 a < entry A 0 b) = (entry X 0 a < entry X 0 b)"
  by (simp add: row0_bump bumpv_strict_mono)

lemma row0_ge: "\<lbrakk>a < Lng X; b < Lng X\<rbrakk> \<Longrightarrow> (entry A 0 b \<le> entry A 0 a) = (entry X 0 b \<le> entry X 0 a)"
  by (simp add: row0_bump bumpv_le)

lemma nextrel0_eq: "nextrel0 A = nextrel0 X"
proof (intro ext)
  fix a b
  show "nextrel0 A a b = nextrel0 X a b"
  proof (cases "a < Lng X \<and> b < Lng X")
    case True
    hence aX: "a < Lng X" and bX: "b < Lng X" by auto
    have U: "(\<forall>j. a < j \<and> j < b \<longrightarrow> entry A 0 b \<le> entry A 0 j)
        = (\<forall>j. a < j \<and> j < b \<longrightarrow> entry X 0 b \<le> entry X 0 j)"
    proof
      assume H: "\<forall>j. a < j \<and> j < b \<longrightarrow> entry A 0 b \<le> entry A 0 j"
      show "\<forall>j. a < j \<and> j < b \<longrightarrow> entry X 0 b \<le> entry X 0 j"
      proof (intro allI impI)
        fix j assume aj: "a < j \<and> j < b"
        hence jX: "j < Lng X" using bX by linarith
        from H aj have "entry A 0 b \<le> entry A 0 j" by blast
        thus "entry X 0 b \<le> entry X 0 j" using row0_ge[OF jX bX] by simp
      qed
    next
      assume H: "\<forall>j. a < j \<and> j < b \<longrightarrow> entry X 0 b \<le> entry X 0 j"
      show "\<forall>j. a < j \<and> j < b \<longrightarrow> entry A 0 b \<le> entry A 0 j"
      proof (intro allI impI)
        fix j assume aj: "a < j \<and> j < b"
        hence jX: "j < Lng X" using bX by linarith
        from H aj have "entry X 0 b \<le> entry X 0 j" by blast
        thus "entry A 0 b \<le> entry A 0 j" using row0_ge[OF jX bX] by simp
      qed
    qed
    thus ?thesis using row0_lt[OF aX bX]
      by (auto simp: nextrel0_def len_eq)
  next
    case False
    thus ?thesis by (auto simp: nextrel0_def len_eq)
  qed
qed

lemma le0_eq: "le0 A = le0 X"
  by (intro ext) (simp add: le0_def nextrel0_eq len_eq)

lemma nextrel1_eq: "nextrel1 A = nextrel1 X"
proof (intro ext)
  fix a b
  show "nextrel1 A a b = nextrel1 X a b"
  proof (cases "a < Lng X \<and> b < Lng X")
    case True
    hence aX: "a < Lng X" and bX: "b < Lng X" by auto
    have e1a: "entry A 1 a = entry X 1 a" by (rule row1_eq[OF aX])
    have e1b: "entry A 1 b = entry X 1 b" by (rule row1_eq[OF bX])
    have U: "(\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry A 1 b \<le> entry A 1 j)
              = (\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry X 1 b \<le> entry X 1 j)"
    proof (rule all_cong1)
      fix j
      show "(a < j \<and> le0 X j b \<longrightarrow> entry A 1 b \<le> entry A 1 j)
          = (a < j \<and> le0 X j b \<longrightarrow> entry X 1 b \<le> entry X 1 j)"
      proof (cases "a < j \<and> le0 X j b")
        case True
        hence jX: "j < Lng X" by (simp add: le0_def)
        show ?thesis using e1b row1_eq[OF jX] by simp
      next
        case False
        thus ?thesis by blast
      qed
    qed
    have "nextrel1 A a b =
       (a < Lng X \<and> b < Lng X \<and> a < b \<and>
        entry A 1 a < entry A 1 b \<and> le0 X a b \<and>
        (\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry A 1 b \<le> entry A 1 j))"
      unfolding nextrel1_def by (simp add: len_eq le0_eq)
    also have "\<dots> =
       (a < Lng X \<and> b < Lng X \<and> a < b \<and>
        entry X 1 a < entry X 1 b \<and> le0 X a b \<and>
        (\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry X 1 b \<le> entry X 1 j))"
      using e1a e1b U by simp
    also have "\<dots> = nextrel1 X a b"
      unfolding nextrel1_def by (simp add: len_eq le0_eq)
    finally show ?thesis .
  next
    case False
    thus ?thesis by (auto simp: nextrel1_def len_eq)
  qed
qed

lemma le1_eq: "le1 A = le1 X"
  by (intro ext) (simp add: le1_def nextrel1_eq len_eq)

lemma nextR_eq: "nextR A = nextR X"
  by (intro ext) (simp add: nextR_def nextrel0_eq nextrel1_eq)

lemma leR_eq: "leR A = leR X"
  by (intro ext) (simp add: leR_def le0_eq le1_eq)

lemma TrMax_eq: "TrMax A = TrMax X"
  by (simp add: TrMax_def nextR_eq)

lemma zeroT_eq: "zeroT A = zeroT X"
  using row1_eq[of 0]
  by (cases "Lng X = 0") (auto simp: zeroT_def len_eq)

lemma monoT_eq: "monoT A = monoT X"
  by (simp add: monoT_def zeroT_eq leR_eq len_eq)

lemma multiT_eq: "multiT A = multiT X"
  by (simp add: multiT_def zeroT_eq monoT_eq)

lemma Pcut_eq: "Pcut A = Pcut X"
  by (simp add: Pcut_def leR_eq len_eq)

end


text \<open>The concrete tail-bump instance arising from \<open>coreReduce\<close>: with
  \<open>X = diagSeq 0 (n-1) @ R\<close> and \<open>A = diagSeq 0 (n-1) @ IncrFirst R\<close>
  (\<open>n \<ge> 1\<close>, \<open>entry R 0 j \<ge> 0\<close> always so tail values \<open>\<ge> n\<close>), the pair
  \<open>(A,X)\<close> satisfies the @{locale tail_bump} hypotheses with cut \<open>n\<close>.\<close>

lemma diag_tail_bump:
  assumes n1: "1 \<le> n"
    and rge: "\<And>j'. j' < Lng R \<Longrightarrow> n \<le> entry R 0 j'"
  shows "tail_bump (diagSeq 0 (n-1) @ IncrFirst R) (diagSeq 0 (n-1) @ R) n"
proof
  let ?X = "diagSeq 0 (n-1) @ R"
  let ?A = "diagSeq 0 (n-1) @ IncrFirst R"
  show "Lng ?A = Lng ?X" by simp
next
  let ?X = "diagSeq 0 (n-1) @ R"
  let ?A = "diagSeq 0 (n-1) @ IncrFirst R"
  fix j assume j: "j < Lng ?X"
  show "entry ?A 0 j = bumpv n (entry ?X 0 j)"
  proof (cases "j < n")
    case True
    \<comment> \<open>prefix: both diagonal, value \<open>= j < n\<close>, bump is identity\<close>
    have jd: "j < Suc (n-1) - 0" using True n1 by simp
    have eX: "entry ?X 0 j = j"
      using jd by (simp add: nth_append entry_def diagSeq_nth)
    have eA: "entry ?A 0 j = j"
      using jd by (simp add: nth_append entry_def diagSeq_nth)
    show ?thesis using eX eA True by (simp add: bumpv_def)
  next
    case False
    \<comment> \<open>tail position \<open>j = n-1+1+j' = n+j'\<close>; value \<open>\<ge> n\<close>, bump is \<open>+1\<close>\<close>
    have nle: "n \<le> j" using False by simp
    have lenpre: "length (diagSeq 0 (n-1)) = n" using n1 by simp
    have jR: "j - n < Lng R" using j nle lenpre by simp
    have eX: "entry ?X 0 j = entry R 0 (j - n)"
      using nle lenpre jR by (simp add: nth_append entry_def)
    have eA0: "entry ?A 0 j = entry (IncrFirst R) 0 (j - n)"
      using nle lenpre jR by (simp add: nth_append entry_def)
    have eA: "entry ?A 0 j = Suc (entry R 0 (j - n))"
      using eA0 jR by (simp add: entry_IncrFirst)
    have ge: "n \<le> entry R 0 (j - n)" using rge[OF jR] .
    show ?thesis using eX eA ge by (simp add: bumpv_def)
  qed
next
  let ?X = "diagSeq 0 (n-1) @ R"
  let ?A = "diagSeq 0 (n-1) @ IncrFirst R"
  fix j assume j: "j < Lng ?X"
  show "entry ?A 1 j = entry ?X 1 j"
  proof (cases "j < n")
    case True
    have jd: "j < Suc (n-1) - 0" using True n1 by simp
    have eX: "entry ?X 1 j = j"
      using jd by (simp add: nth_append entry_def diagSeq_nth)
    have eA: "entry ?A 1 j = j"
      using jd by (simp add: nth_append entry_def diagSeq_nth)
    show ?thesis using eX eA by simp
  next
    case False
    have nle: "n \<le> j" using False by simp
    have lenpre: "length (diagSeq 0 (n-1)) = n" using n1 by simp
    have jR: "j - n < Lng R" using j nle lenpre by simp
    have eX: "entry ?X 1 j = entry R 1 (j - n)"
      using nle lenpre jR by (simp add: nth_append entry_def)
    have eA0: "entry ?A 1 j = entry (IncrFirst R) 1 (j - n)"
      using nle lenpre jR by (simp add: nth_append entry_def)
    have eA: "entry ?A 1 j = entry R 1 (j - n)"
      using eA0 jR by (simp add: entry_IncrFirst)
    show ?thesis using eX eA by simp
  qed
qed


text \<open>For a mono \<open>M\<close> with \<open>m\<^sub>1\<^sub>0 > 0\<close>, \<open>coreReduce M\<close> and
  \<open>coreReduce (IncrFirst M)\<close> share the length-\<open>m\<^sub>1\<^sub>0\<close> diagonal prefix and differ
  by one extra @{const IncrFirst} on the tail: with \<open>R = IncrFirst\<^bsup>m\<^sub>1\<^sub>0\<^esup> M\<close>,
  \<open>coreReduce M = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ R\<close> and
  \<open>coreReduce (IncrFirst M) = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ IncrFirst R\<close>.\<close>

lemma coreReduce_m10pos_form:
  assumes pos: "0 < entry M 1 0"
  shows "coreReduce M = diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M"
  using pos by (simp add: coreReduce_def)

lemma coreReduce_IncrFirst_m10pos_form:
  assumes pos: "0 < entry M 1 0" and L: "0 < Lng M"
  shows "coreReduce (IncrFirst M)
       = diagSeq 0 (entry M 1 0 - 1) @ IncrFirst ((IncrFirst ^^ (entry M 1 0)) M)"
proof -
  let ?m = "entry M 1 0"
  have m1: "entry (IncrFirst M) 1 0 = ?m" using L by (simp add: entry_IncrFirst)
  have pos': "0 < entry (IncrFirst M) 1 0" using pos m1 by simp
  have "coreReduce (IncrFirst M)
      = diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) (IncrFirst M)"
    using pos' m1 by (simp add: coreReduce_def)
  also have "(IncrFirst ^^ ?m) (IncrFirst M) = IncrFirst ((IncrFirst ^^ ?m) M)"
    by (simp add: funpow_swap1)
  finally show ?thesis .
qed

text \<open>The @{locale tail_bump} interpretation for the \<open>coreReduce\<close> pair.\<close>

lemma tail_bump_coreReduce:
  assumes T: "M \<in> T_PS" and pos: "0 < entry M 1 0"
  shows "tail_bump (coreReduce (IncrFirst M)) (coreReduce M) (entry M 1 0)"
proof -
  let ?m = "entry M 1 0"
  let ?R = "(IncrFirst ^^ ?m) M"
  have crX: "coreReduce M = diagSeq 0 (?m - 1) @ ?R" by (rule coreReduce_m10pos_form[OF pos])
  have L: "0 < Lng M" using T by (cases M) (auto simp: T_PS_def)
  have crA: "coreReduce (IncrFirst M) = diagSeq 0 (?m - 1) @ IncrFirst ?R"
    by (rule coreReduce_IncrFirst_m10pos_form[OF pos L])
  have m1: "1 \<le> ?m" using pos by simp
  have rge: "\<And>j'. j' < Lng ?R \<Longrightarrow> ?m \<le> entry ?R 0 j'"
  proof -
    fix j' assume "j' < Lng ?R"
    hence jM: "j' < Lng M" by simp
    have "entry ?R 0 j' = entry M 0 j' + ?m" by (rule entry_funpow_IncrFirst0[OF jM])
    thus "?m \<le> entry ?R 0 j'" by simp
  qed
  have "tail_bump (diagSeq 0 (?m-1) @ IncrFirst ?R) (diagSeq 0 (?m-1) @ ?R) ?m"
    by (rule diag_tail_bump[OF m1 rge])
  thus ?thesis using crX crA by simp
qed


subsubsection \<open>Trunk/branch equalities for the \<open>coreReduce\<close> pair\<close>

text \<open>Throughout: \<open>M \<in> T_PS\<close>, \<open>monoT M\<close>, \<open>m\<^sub>1\<^sub>0 = entry M 1 0 > 0\<close>;
  \<open>A = coreReduce (IncrFirst M)\<close>, \<open>crM = coreReduce M\<close>.\<close>

text \<open>(1) Trunk right-end is shared.\<close>

lemma njA_TrMax_eq:
  assumes T: "M \<in> T_PS" and pos: "0 < entry M 1 0"
  shows "TrMax (coreReduce (IncrFirst M)) = TrMax (coreReduce M)"
  by (rule tail_bump.TrMax_eq[OF tail_bump_coreReduce[OF T pos]])

text \<open>The branch segment of \<open>coreReduce M\<close> starts strictly past the diagonal
  prefix (its left end \<open>TrMax + 1\<close> exceeds \<open>m\<^sub>1\<^sub>0\<close>), so on that segment the bump
  is a uniform @{const IncrFirst}.  We use this to transfer @{const Br}.\<close>

lemma njA_TrMax_ge_m10:
  assumes T: "M \<in> T_PS" and pos: "0 < entry M 1 0"
  shows "entry M 1 0 \<le> TrMax (coreReduce M)"
proof -
  let ?m = "entry M 1 0"
  let ?R = "(IncrFirst ^^ ?m) M"
  have cr: "coreReduce M = diagSeq 0 (?m - 1) @ ?R" by (rule coreReduce_m10pos_form[OF pos])
  have L0: "0 < Lng M" using T by (cases M) (auto simp: T_PS_def)
  have lenr: "Lng ?R = Lng M" by simp
  have ne: "?R \<noteq> []" using L0 lenr by (metis length_greater_0_conv)
  have er0: "entry ?R 0 0 = entry M 0 0 + ?m" by (rule entry_funpow_IncrFirst0[OF L0])
  have er1: "entry ?R 1 0 = entry M 1 0" by (rule entry_funpow_IncrFirst1[OF L0])
  have r0: "?m - 1 < entry ?R 0 0" using pos er0 by simp
  have r1: "?m - 1 < entry ?R 1 0" using pos er1 by simp
  have "Suc (?m - 1) \<le> TrMax (coreReduce M)"
    using cr TrMax_diagSeq_append_ge[OF ne r0 r1] by simp
  thus ?thesis using pos by simp
qed

text \<open>On the branch segment (indices \<open>\<ge> m\<^sub>1\<^sub>0\<close>) the tail bump is a uniform
  @{const IncrFirst}: \<open>seg A a b = IncrFirst (seg crM a b)\<close> for \<open>m\<^sub>1\<^sub>0 \<le> a\<close>.\<close>

lemma njA_seg_IncrFirst:
  assumes T: "M \<in> T_PS" and pos: "0 < entry M 1 0" and a: "entry M 1 0 \<le> a"
    and b: "b < Lng (coreReduce M)"
  shows "seg (coreReduce (IncrFirst M)) a b = IncrFirst (seg (coreReduce M) a b)"
proof -
  let ?m = "entry M 1 0"
  let ?R = "(IncrFirst ^^ ?m) M"
  let ?D = "diagSeq 0 (?m - 1)"
  have lenD: "length ?D = ?m" using pos by simp
  have crX: "coreReduce M = ?D @ ?R" by (rule coreReduce_m10pos_form[OF pos])
  have L: "0 < Lng M" using T by (cases M) (auto simp: T_PS_def)
  have crA: "coreReduce (IncrFirst M) = ?D @ IncrFirst ?R"
    by (rule coreReduce_IncrFirst_m10pos_form[OF pos L])
  show ?thesis
  proof (rule nth_equalityI)
    show "length (seg (coreReduce (IncrFirst M)) a b)
        = length (IncrFirst (seg (coreReduce M) a b))"
      by (simp add: seg_def IncrFirst_def)
  next
    fix p assume p: "p < length (seg (coreReduce (IncrFirst M)) a b)"
    have pb: "p < Suc b - a" using p by (simp add: seg_def del: upt_Suc)
    let ?j = "a + p"
    have idx: "[a..<Suc b] ! p = ?j" using pb by (simp add: nth_upt del: upt_Suc)
    have jge: "?m \<le> ?j" using a by simp
    have jb: "?j \<le> b" using pb by simp
    have jlt: "?j < Lng (coreReduce M)" using jb b by simp
    have kR: "?j - ?m < Lng ?R"
    proof -
      have "Lng (coreReduce M) = ?m + Lng ?R" using crX lenD by simp
      thus ?thesis using jlt jge by linarith
    qed
    \<comment> \<open>both sequences index into the tail at \<open>?j - ?m\<close>\<close>
    have lhs: "seg (coreReduce (IncrFirst M)) a b ! p = (?D @ IncrFirst ?R) ! ?j"
      using pb crA idx by (simp add: seg_def del: upt_Suc)
    have rhs0: "seg (coreReduce M) a b ! p = (?D @ ?R) ! ?j"
      using pb crX idx by (simp add: seg_def del: upt_Suc)
    have tailL: "(?D @ IncrFirst ?R) ! ?j = IncrFirst ?R ! (?j - ?m)"
      using jge lenD by (simp add: nth_append)
    have tailX: "(?D @ ?R) ! ?j = ?R ! (?j - ?m)"
      using jge lenD by (simp add: nth_append)
    have inc: "IncrFirst ?R ! (?j - ?m) = (Suc (fst (?R ! (?j - ?m))), snd (?R ! (?j - ?m)))"
      using kR by (simp add: IncrFirst_def)
    have segm: "IncrFirst (seg (coreReduce M) a b) ! p
                 = (Suc (fst (seg (coreReduce M) a b ! p)), snd (seg (coreReduce M) a b ! p))"
      using p by (simp add: IncrFirst_def)
    show "seg (coreReduce (IncrFirst M)) a b ! p
                   = IncrFirst (seg (coreReduce M) a b) ! p"
      using lhs rhs0 tailL tailX inc segm by simp
  qed
qed

end

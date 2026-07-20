theory Frontier_6_054
  imports Support_6_036
begin

text \<open>\<open>shiftRow0\<close> preserves \<open>congR\<close> for mono \<open>A\<close>, \<open>X\<close> (row-1 untouched, and
  \<open>nextrel0 (shiftRow0 _) = nextrel0 _\<close> by @{thm [source] nextrel0_shiftRow0_eq}).\<close>

lemma congR_shiftRow0:
  assumes R: "congR A X" and AT: "A \<in> T_PS" and XT: "X \<in> T_PS"
    and monoA: "monoT A" and monoX: "monoT X"
  shows "congR (shiftRow0 A) (shiftRow0 X)"
proof -
  have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
  have n0: "nextrel0 A = nextrel0 X" using R by (simp add: congR_def)
  show ?thesis unfolding congR_def
  proof (intro conjI allI impI)
    show "Lng (shiftRow0 A) = Lng (shiftRow0 X)" using LAX by simp
    show "nextrel0 (shiftRow0 A) = nextrel0 (shiftRow0 X)"
    proof (intro ext)
      fix p q
      have "nextrel0 (shiftRow0 A) p q = nextrel0 A p q"
        by (rule nextrel0_shiftRow0_eq[OF AT monoA])
      also have "\<dots> = nextrel0 X p q" using n0 by simp
      also have "\<dots> = nextrel0 (shiftRow0 X) p q"
        by (rule nextrel0_shiftRow0_eq[OF XT monoX, symmetric])
      finally show "nextrel0 (shiftRow0 A) p q = nextrel0 (shiftRow0 X) p q" .
    qed
    fix j assume j: "j < Lng (shiftRow0 X)"
    hence jX: "j < Lng X" by simp
    have jA: "j < Lng A" using jX LAX by simp
    have "entry (shiftRow0 A) 1 j = entry A 1 j" using entry_shiftRow0_1[OF jA] .
    also have "\<dots> = entry X 1 j" using R jX by (simp add: congR_def)
    also have "\<dots> = entry (shiftRow0 X) 1 j" using entry_shiftRow0_1[OF jX] by simp
    finally show "entry (shiftRow0 A) 1 j = entry (shiftRow0 X) 1 j" .
  qed
qed

text \<open>The branch \<^emph>\<open>segment\<close> \<open>seg _ (TrMax+1) (Lng-1)\<close> inherits \<open>congR\<close> (shared
  \<open>TrMax\<close>), hence \<open>Br A\<close> and \<open>Br X\<close> have the same length and each component pair
  \<open>Br A ! J\<close> / \<open>Br X ! J\<close> is \<open>congR\<close>-related (P-block of a \<open>congR\<close> segment).\<close>

lemma congR_brseg:
  assumes R: "congR A X" and ne: "TrMax X \<noteq> Lng X - 1" and L0: "0 < Lng X"
  shows "congR (seg A (TrMax X + 1) (Lng X - 1)) (seg X (TrMax X + 1) (Lng X - 1))"
proof -
  have sb: "Lng X - 1 < Lng X" using L0 by simp
  show ?thesis by (rule congR_seg[OF R sb])
qed

lemma congR_Br_length:
  assumes R: "congR A X" and AT: "A \<in> T_PS" and XT: "X \<in> T_PS"
  shows "length (Br A) = length (Br X)"
proof -
  have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
  have trAX: "TrMax A = TrMax X" by (rule congR_TrMax[OF R])
  show ?thesis
  proof (cases "TrMax X = Lng X - 1")
    case True
    hence "Br A = []" "Br X = []" using trAX LAX by (simp_all add: Br_def)
    thus ?thesis by simp
  next
    case False
    have L0: "0 < Lng X" using XT by (cases X) (auto simp: T_PS_def)
    let ?sa = "seg A (TrMax X + 1) (Lng X - 1)" let ?sx = "seg X (TrMax X + 1) (Lng X - 1)"
    have Rseg: "congR ?sa ?sx" by (rule congR_brseg[OF R False L0])
    have BrA: "Br A = P ?sa" using False trAX LAX by (simp add: Br_def)
    have BrX: "Br X = P ?sx" using False by (simp add: Br_def)
    have "length (P ?sa) = length (P ?sx)" by (rule congR_P_length[OF Rseg])
    thus ?thesis using BrA BrX by simp
  qed
qed

lemma congR_Br_block:
  assumes R: "congR A X" and AT: "A \<in> T_PS" and XT: "X \<in> T_PS"
    and J: "J < length (Br X)"
  shows "congR (Br A ! J) (Br X ! J)"
proof -
  have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
  have trAX: "TrMax A = TrMax X" by (rule congR_TrMax[OF R])
  have ne: "TrMax X \<noteq> Lng X - 1"
  proof
    assume "TrMax X = Lng X - 1"
    hence "Br X = []" by (simp add: Br_def)
    thus False using J by simp
  qed
  have L0: "0 < Lng X" using XT by (cases X) (auto simp: T_PS_def)
  let ?sa = "seg A (TrMax X + 1) (Lng X - 1)" let ?sx = "seg X (TrMax X + 1) (Lng X - 1)"
  have Rseg: "congR ?sa ?sx" by (rule congR_brseg[OF R ne L0])
  have trlt: "TrMax X < Lng X - 1" using TrMax_bound[OF XT] ne by linarith
  have sxlen: "0 < Lng ?sx" using trlt L0 by (simp only: Lng_seg)
  have salen: "0 < Lng ?sa" using sxlen Rseg by (simp add: congR_def)
  have sane: "?sa \<noteq> []" using salen length_greater_0_conv by blast
  have sxne: "?sx \<noteq> []" using sxlen length_greater_0_conv by blast
  have saT: "?sa \<in> T_PS" using sane by (simp add: T_PS_def)
  have sxT: "?sx \<in> T_PS" using sxne by (simp add: T_PS_def)
  have BrA: "Br A = P ?sa" using ne trAX LAX by (simp add: Br_def)
  have BrX: "Br X = P ?sx" using ne by (simp add: Br_def)
  have JX: "J < length (P ?sx)" using J BrX by simp
  have "congR (P ?sa ! J) (P ?sx ! J)" by (rule congR_P_block[OF Rseg saT sxT JX])
  thus ?thesis using BrA BrX by simp
qed

text \<open>\<^bold>\<open>REMAINING OBLIGATION for the full \<open>cong_red_cong\<close>\<close> (\<open>congR A X \<Longrightarrow> Red A =
  Red X\<close>, empirically 0-fail).  The structural sharing above closes the \<open>zeroT\<close>,
  \<open>multiT\<close> (via @{thm [source] congR_P_block}), core-trunk, and \<open>monoT\<close>-shift (via
  @{thm [source] congR_shiftRow0}) recursion alignments.  Two obstructions remain,
  newly pinned here:

  \<^enum> \<^bold>\<open>Cross-branch interleave\<close> (decisive, empirically confirmed
    \<open>python/cong_step0.py\<close>): \<open>congR\<close> does \<^emph>\<open>not\<close> preserve the \<open>m\<^sub>0\<^sub>0 = 0\<close> split.  With
    \<open>X\<close> core mono (\<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close>) one may have \<open>entry A 0 0 > 0\<close> (48/90 cases),
    so \<open>A\<close> takes the \<^emph>\<open>shift\<close> branch while \<open>X\<close> takes \<^emph>\<open>core-trunk/nontrunk\<close>.  Hence a
    plain @{thm [source] Red.pinduct} on \<open>X\<close> (or \<open>A\<close>) does \<^emph>\<open>not\<close> line the two sides'
    branches up the way @{thm [source] fin_cut_bump_Red} does (there \<open>bumpAt\<close>
    preserves \<open>m\<^sub>0\<^sub>0\<close>/\<open>m\<^sub>1\<^sub>0\<close>, so both took the same branch).  The fix is to route the
    shift side through \<open>Red A = Red (shiftRow0 A)\<close> and use \<open>congR (shiftRow0 A)
    (shiftRow0 X)\<close> (= @{thm [source] congR_shiftRow0}) — but the matching Red-call
    is \<^emph>\<open>not\<close> a sub-call of \<open>X\<close> in \<open>X\<close>'s recursion tree, so the bare \<open>pinduct\<close> IH
    does not reach it.  A custom well-founded induction (e.g. on
    \<open>Lng + entry _ 0 0\<close>, which strictly decreases under shift and stays under the
    core/branch descents) or a prior \<open>Red\<close>-normalisation \<open>Red M = Red (shiftRow0
    M)\<close> (collapsing \<open>m\<^sub>0\<^sub>0\<close> before the structural induction) is required.

  \<^enum> \<^bold>\<open>Two missing value-helpers\<close> for the still-aligned branches once (1) is handled:
    \<^item> \<open>congR_NJ\<close>: \<open>congR (NJ A J) (NJ X J)\<close> in the core-nontrunk branch — the
      \<open>NJ\<close> head row-0 is \<open>entry _ 0 0 + Joints!J + 1\<close>, so its \<open>nextrel0\<close>-alignment
      vs. \<open>tl (Br _ ! J)\<close> needs the core assumption; reduce via
      @{thm [source] congR_Br_block} + the shared \<open>Joints\<close>/@{const npJ}.
    \<^item> \<open>congR_diag_funpow\<close>: \<open>congR (diagSeq 0 (m\<^sub>1\<^sub>0-1) @ (IncrFirst^^m\<^sub>1\<^sub>0) A)
      (diagSeq 0 (m\<^sub>1\<^sub>0-1) @ (IncrFirst^^m\<^sub>1\<^sub>0) X)\<close> for the \<open>m\<^sub>1\<^sub>0>0\<close> branch — row-1 and
      the diagonal prefix are identical, the suffixes are @{thm [source]
      congR_funpow_IncrFirst}-related, and every suffix row-0 value \<open>\<ge> m\<^sub>1\<^sub>0\<close>
      exceeds every prefix value (\<open>< m\<^sub>1\<^sub>0\<close>), so the cross-boundary \<open>nextrel0\<close> is
      constant; provable from @{thm [source] nextrel0_diagSeq_append_step} +
      @{thm [source] entry_funpow_IncrFirst0} but tedious (all index-pair cases).

  The locale + the eight green \<open>congR_*\<close> inheritance lemmas are the reusable
  engine; obstruction (1) is the genuine mathematical content still to design.

  \<^bold>\<open>RESOLVED below\<close> (\<open>cdn_red_cong\<close>): obstruction (1) is closed by \<open>Red.pinduct\<close>
  on \<open>A\<close> with the cross-branch (\<open>A\<close> core, \<open>X\<close> shift) normalised through
  \<open>cdn_Red_shiftRow0_m10z\<close> (\<open>m\<^sub>1\<^sub>0 = 0\<close> there); the two value-helpers are
  \<open>congR_NJ\<close> and \<open>congR_diag_funpow\<close>.\<close>


subsection \<open>Master-key: \<open>congR\<close> nextrel-congruence of \<open>Red\<close> (\<open>cdn_red_cong\<close>)\<close>

text \<open>Structural list-data of \<open>Br\<close>: a \<open>congR\<close>-related pair shares the per-block
  lengths, hence \<open>IdxSum (Br _)\<close>, \<open>FirstNodes\<close>, and \<open>Joints\<close>.\<close>

lemma congR_Br_maplen:
  assumes R: "congR A X" and AT: "A \<in> T_PS" and XT: "X \<in> T_PS"
  shows "map length (Br A) = map length (Br X)"
proof (rule nth_equalityI)
  have lenE: "length (Br A) = length (Br X)" by (rule congR_Br_length[OF R AT XT])
  thus "length (map length (Br A)) = length (map length (Br X))" by simp
  fix J assume "J < length (map length (Br A))"
  hence J: "J < length (Br A)" by simp
  hence JX: "J < length (Br X)" using lenE by simp
  have "congR (Br A ! J) (Br X ! J)" by (rule congR_Br_block[OF R AT XT JX])
  hence "Lng (Br A ! J) = Lng (Br X ! J)" by (rule congR_Lng)
  thus "map length (Br A) ! J = map length (Br X) ! J" using J JX by simp
qed

lemma congR_IdxSum_Br:
  assumes R: "congR A X" and AT: "A \<in> T_PS" and XT: "X \<in> T_PS"
  shows "IdxSum (Br A) = IdxSum (Br X)"
proof -
  have ml: "map length (Br A) = map length (Br X)" by (rule congR_Br_maplen[OF R AT XT])
  have ll: "length (Br A) = length (Br X)" by (metis ml length_map)
  have "\<And>x. sum_list (map length (take x (Br A))) = sum_list (map length (take x (Br X)))"
    using ml by (metis take_map)
  thus ?thesis using ll by (simp add: IdxSum_def)
qed

lemma congR_FirstNodes:
  assumes R: "congR A X" and AT: "A \<in> T_PS" and XT: "X \<in> T_PS"
  shows "FirstNodes A = FirstNodes X"
proof -
  have "IdxSum (Br A) = IdxSum (Br X)" by (rule congR_IdxSum_Br[OF R AT XT])
  thus ?thesis by (simp add: FirstNodes_def congR_TrMax[OF R])
qed

lemma congR_Joints:
  assumes R: "congR A X" and AT: "A \<in> T_PS" and XT: "X \<in> T_PS"
  shows "Joints A = Joints X"
  by (simp add: Joints_def congR_nextR[OF R] congR_FirstNodes[OF R AT XT]
                congR_Br_length[OF R AT XT])

lemma congR_npJ:
  assumes R: "congR A X" and AT: "A \<in> T_PS" and XT: "X \<in> T_PS"
    and J: "J < length (Br X)"
  shows "npJ A J = npJ X J"
proof -
  have JA: "J < length (Br A)" using J congR_Br_length[OF R AT XT] by simp
  have RbrJ: "congR (Br A ! J) (Br X ! J)" by (rule congR_Br_block[OF R AT XT J])
  have LbrJ: "Lng (Br A ! J) = Lng (Br X ! J)" by (rule congR_Lng[OF RbrJ])
  have e1: "entry (Br A ! J) 1 0 = entry (Br X ! J) 1 0"
  proof (cases "0 < Lng (Br X ! J)")
    case True thus ?thesis using RbrJ by (simp add: congR_def)
  next
    case False
    hence "Lng (Br X ! J) = 0" by simp
    hence "Br X ! J = []" "Br A ! J = []" using LbrJ by auto
    thus ?thesis by (simp add: entry_def)
  qed
  have theEq: "(THE j. nextR A 1 j (FirstNodes A ! J))
             = (THE j. nextR X 1 j (FirstNodes X ! J))"
    by (simp add: congR_nextR[OF R] congR_FirstNodes[OF R AT XT])
  show ?thesis unfolding npJ_def by (simp only: e1 theEq)
qed

text \<open>\<open>congR_NJ\<close>: in the core branch (\<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close> on both sides) the branch
  recursion arg \<open>N\<^sub>J\<close> is \<open>congR\<close>-related.  Both heads are
  \<open>(Joints!J + 1, npJ J)\<close> (shared), and the tails are the shared branch block
  beyond index 0; the only delicate point (\<open>nextrel0\<close>) is inherited from
  @{thm [source] congR_Br_block} because \<open>NJ\<close> only changes the index-0 row-0 head,
  which is below the rest (core).\<close>

lemma cdn_nextrel0_suc_cong:
  assumes L: "Lng M = Lng N"
    and row: "\<And>j::nat. 0 < j \<Longrightarrow> j < Lng M \<Longrightarrow> entry M 0 j = entry N 0 j"
  shows "nextrel0 M (Suc p) (Suc q) = nextrel0 N (Suc p) (Suc q)"
proof -
  have ebetw: "\<And>j. Suc p < j \<Longrightarrow> j < Suc q \<Longrightarrow> j < Lng M \<Longrightarrow> entry M 0 j = entry N 0 j"
    by (rule row) auto
  show ?thesis
  proof (cases "Suc p < Lng M \<and> Suc q < Lng M")
    case True
    hence pL: "Suc p < Lng M" and qL: "Suc q < Lng M" by simp_all
    have eqp: "entry M 0 (Suc p) = entry N 0 (Suc p)" using row[of "Suc p"] pL by simp
    have eqq: "entry M 0 (Suc q) = entry N 0 (Suc q)" using row[of "Suc q"] qL by simp
    have betw: "(\<forall>j. Suc p < j \<and> j < Suc q \<longrightarrow> entry M 0 j \<ge> entry M 0 (Suc q))
              = (\<forall>j. Suc p < j \<and> j < Suc q \<longrightarrow> entry N 0 j \<ge> entry N 0 (Suc q))"
    proof -
      have "\<And>j. Suc p < j \<Longrightarrow> j < Suc q \<Longrightarrow> entry M 0 j = entry N 0 j"
      proof -
        fix j assume a: "Suc p < j" and b: "j < Suc q"
        have "j < Lng M" using b qL by simp
        thus "entry M 0 j = entry N 0 j" using ebetw[OF a b] by simp
      qed
      thus ?thesis using eqq by metis
    qed
    show ?thesis unfolding nextrel0_def using L eqp eqq betw by simp
  next
    case False
    thus ?thesis unfolding nextrel0_def using L by auto
  qed
qed

lemma cdn_minhead_runmin_char:
  assumes minU: "\<And>j. 0 < j \<Longrightarrow> j < Lng U \<Longrightarrow> entry U 0 0 < entry U 0 j"
    and qpos: "0 < q" and qU: "q < Lng U"
  shows "nextrel0 U 0 q \<longleftrightarrow> (\<forall>l. 0 < l \<and> l < q \<longrightarrow> \<not> nextrel0 U l q)"
proof
  assume nr: "nextrel0 U 0 q"
  show "\<forall>l. 0 < l \<and> l < q \<longrightarrow> \<not> nextrel0 U l q"
  proof (intro allI impI)
    fix l assume l: "0 < l \<and> l < q"
    hence "entry U 0 l \<ge> entry U 0 q" using nr by (auto simp: nextrel0_def)
    thus "\<not> nextrel0 U l q" by (auto simp: nextrel0_def)
  qed
next
  assume H: "\<forall>l. 0 < l \<and> l < q \<longrightarrow> \<not> nextrel0 U l q"
  have all_ge: "\<forall>l. 0 < l \<and> l < q \<longrightarrow> entry U 0 l \<ge> entry U 0 q"
  proof (intro allI impI)
    fix l assume l: "0 < l \<and> l < q"
    show "entry U 0 l \<ge> entry U 0 q"
    proof (rule ccontr)
      assume "\<not> entry U 0 l \<ge> entry U 0 q"
      hence lt: "entry U 0 l < entry U 0 q" by simp
      let ?S = "{l'. 0 < l' \<and> l' < q \<and> entry U 0 l' < entry U 0 q}"
      have lin: "l \<in> ?S" using l lt by simp
      have fin: "finite ?S" by simp
      have ne: "?S \<noteq> {}" using lin by blast
      let ?m = "Max ?S"
      have mS: "?m \<in> ?S" using Max_in[OF fin ne] .
      hence mpos: "0 < ?m" and mq: "?m < q" and mlt: "entry U 0 ?m < entry U 0 q" by auto
      have between: "\<forall>j. ?m < j \<and> j < q \<longrightarrow> entry U 0 j \<ge> entry U 0 q"
      proof (intro allI impI)
        fix j assume j: "?m < j \<and> j < q"
        hence jpos: "0 < j" using mpos by simp
        show "entry U 0 j \<ge> entry U 0 q"
        proof (rule ccontr)
          assume "\<not> entry U 0 j \<ge> entry U 0 q"
          hence "j \<in> ?S" using j jpos by simp
          hence "j \<le> ?m" using Max_ge[OF fin] by simp
          thus False using j by simp
        qed
      qed
      have "nextrel0 U ?m q"
        using mpos mq mlt qU between by (simp add: nextrel0_def)
      thus False using H mpos mq by blast
    qed
  qed
  have "entry U 0 0 < entry U 0 q" by (rule minU[OF qpos qU])
  thus "nextrel0 U 0 q" using qpos qU all_ge by (auto simp: nextrel0_def)
qed

lemma cdn_nextrel0_minhead_cong:
  assumes L: "Lng U = Lng V"
    and minU: "\<And>j. 0 < j \<Longrightarrow> j < Lng U \<Longrightarrow> entry U 0 0 < entry U 0 j"
    and minV: "\<And>j. 0 < j \<Longrightarrow> j < Lng V \<Longrightarrow> entry V 0 0 < entry V 0 j"
    and tail: "\<And>p q. nextrel0 U (Suc p) (Suc q) = nextrel0 V (Suc p) (Suc q)"
  shows "nextrel0 U = nextrel0 V"
proof (intro ext)
  fix p q
  show "nextrel0 U p q = nextrel0 V p q"
  proof (cases p)
    case (Suc p')
    show ?thesis
    proof (cases q)
      case 0 thus ?thesis using Suc by (simp add: nextrel0_def)
    next
      case (Suc q') thus ?thesis using \<open>p = Suc p'\<close> tail by simp
    qed
  next
    case 0
    show ?thesis
    proof (cases q)
      case 0 thus ?thesis using \<open>p = 0\<close> by (simp add: nextrel0_def)
    next
      case (Suc q')
      have qpos: "0 < q" using Suc by simp
      show ?thesis
      proof (cases "q < Lng U")
        case False
        hence "\<not> q < Lng U" "\<not> q < Lng V" using L by auto
        thus ?thesis using \<open>p = 0\<close> by (simp add: nextrel0_def)
      next
        case True
        have qU: "q < Lng U" by (rule True)
        have qV: "q < Lng V" using qU L by simp
        have tailEq: "\<And>l. 0 < l \<Longrightarrow> l < q \<Longrightarrow> nextrel0 U l q = nextrel0 V l q"
        proof -
          fix l assume lp: "0 < l" and lq: "l < q"
          obtain l' where l': "l = Suc l'" using lp by (cases l) auto
          obtain q' where q'': "q = Suc q'" using qpos by (cases q) auto
          show "nextrel0 U l q = nextrel0 V l q" using tail[of l' q'] l' q'' by simp
        qed
        have cU: "nextrel0 U 0 q \<longleftrightarrow> (\<forall>l. 0 < l \<and> l < q \<longrightarrow> \<not> nextrel0 U l q)"
          by (rule cdn_minhead_runmin_char[OF minU qpos qU])
        have cV: "nextrel0 V 0 q \<longleftrightarrow> (\<forall>l. 0 < l \<and> l < q \<longrightarrow> \<not> nextrel0 V l q)"
          by (rule cdn_minhead_runmin_char[OF minV qpos qV])
        have "(\<forall>l. 0 < l \<and> l < q \<longrightarrow> \<not> nextrel0 U l q)
            = (\<forall>l. 0 < l \<and> l < q \<longrightarrow> \<not> nextrel0 V l q)"
          using tailEq by metis
        thus ?thesis using cU cV \<open>p = 0\<close> by simp
      qed
    qed
  qed
qed

text \<open>\<open>congR_NJ\<close>: in the core branch (\<open>m\<^sub>0\<^sub>0 = 0\<close> on both sides) the branch
  recursion arg \<open>N\<^sub>J\<close> is \<open>congR\<close>-related.  The head pair \<open>(Joints!J+1, npJ J)\<close> is
  shared, the tails are the shared branch block beyond index 0, and the head
  row-0 is the strict minimum (joints below branch first + monoT), so
  @{thm [source] cdn_nextrel0_minhead_cong} closes \<open>nextrel0\<close>.\<close>

lemma congR_NJ:
  assumes R: "congR A X" and AX: "A \<in> PT_PS" and XX: "X \<in> PT_PS"
    and c0A: "entry A 0 0 = 0" and c0X: "entry X 0 0 = 0"
    and J: "J < length (Br X)"
  shows "congR (NJ A J) (NJ X J)"
proof -
  have AT: "A \<in> T_PS" and monoA: "monoT A" using AX by (simp_all add: PT_PS_def)
  have XT: "X \<in> T_PS" and monoX: "monoT X" using XX by (simp_all add: PT_PS_def)
  have JBrX: "J < Lng (Br X)" using J by simp
  have JBrA: "J < Lng (Br A)" using J congR_Br_length[OF R AT XT] by simp
  have RbrJ: "congR (Br A ! J) (Br X ! J)" by (rule congR_Br_block[OF R AT XT J])
  have LbrJ: "Lng (Br A ! J) = Lng (Br X ! J)" by (rule congR_Lng[OF RbrJ])
  have brAne: "Br A ! J \<noteq> []" by (rule Br_component_nonempty[OF AX JBrA])
  have brXne: "Br X ! J \<noteq> []" by (rule Br_component_nonempty[OF XX JBrX])
  have jtE: "Joints A ! J = Joints X ! J" using congR_Joints[OF R AT XT] by simp
  have npE: "npJ A J = npJ X J" by (rule congR_npJ[OF R AT XT J])
  have L0X: "0 < Lng X" using XT by (cases X) (auto simp: T_PS_def)
  have e10: "entry A 1 0 = entry X 1 0" using R L0X by (simp add: congR_def)
  let ?cA = "Joints A ! J + 1" let ?cX = "Joints X ! J + 1"
  have cEq: "?cA = ?cX" using jtE by simp
  \<comment> \<open>row-0 head of NJ.\<close>
  have hA0: "entry (NJ A J) 0 0 = ?cA" using c0A by (simp add: entry_NJ_0_0)
  have hX0: "entry (NJ X J) 0 0 = ?cX" using c0X by (simp add: entry_NJ_0_0)
  have LNJA: "Lng (NJ A J) = Lng (Br A ! J)" using brAne by (rule Lng_NJ)
  have LNJX: "Lng (NJ X J) = Lng (Br X ! J)" using brXne by (rule Lng_NJ)
  have LNJ: "Lng (NJ A J) = Lng (NJ X J)" using LNJA LNJX LbrJ by simp
  \<comment> \<open>strict head min on A.\<close>
  have minA: "\<And>j. 0 < j \<Longrightarrow> j < Lng (NJ A J) \<Longrightarrow> entry (NJ A J) 0 0 < entry (NJ A J) 0 j"
  proof -
    fix j assume jp: "0 < j" and jl: "j < Lng (NJ A J)"
    have jbr: "j < Lng (Br A ! J)" using jl LNJA by simp
    have eq: "entry (NJ A J) 0 j = entry (Br A ! J) 0 j" by (rule entry_NJ_hi[OF jp jbr])
    have brmono: "monoT (Br A ! J)"
    proof -
      have "zeroT (Br A ! J) \<or> monoT (Br A ! J)" by (rule Br_component_nonmulti[OF AX JBrA])
      moreover have "\<not> zeroT (Br A ! J)" using jp jbr by (auto simp: zeroT_def)
      ultimately show ?thesis by blast
    qed
    have brT: "Br A ! J \<in> T_PS" using brAne by (simp add: T_PS_def)
    have hd: "entry A 0 0 + ?cA \<le> entry (Br A ! J) 0 0"
      using joints_lt_branch_first[OF AX JBrA] by simp
    have hd': "?cA \<le> entry (Br A ! J) 0 0" using hd c0A by simp
    have brstr: "entry (Br A ! J) 0 0 < entry (Br A ! J) 0 j"
      by (rule monoT_row0_min[OF brT brmono jp jbr])
    show "entry (NJ A J) 0 0 < entry (NJ A J) 0 j" using hA0 eq hd' brstr by simp
  qed
  have minX: "\<And>j. 0 < j \<Longrightarrow> j < Lng (NJ X J) \<Longrightarrow> entry (NJ X J) 0 0 < entry (NJ X J) 0 j"
  proof -
    fix j assume jp: "0 < j" and jl: "j < Lng (NJ X J)"
    have jbr: "j < Lng (Br X ! J)" using jl LNJX by simp
    have eq: "entry (NJ X J) 0 j = entry (Br X ! J) 0 j" by (rule entry_NJ_hi[OF jp jbr])
    have brmono: "monoT (Br X ! J)"
    proof -
      have "zeroT (Br X ! J) \<or> monoT (Br X ! J)" by (rule Br_component_nonmulti[OF XX JBrX])
      moreover have "\<not> zeroT (Br X ! J)" using jp jbr by (auto simp: zeroT_def)
      ultimately show ?thesis by blast
    qed
    have brT: "Br X ! J \<in> T_PS" using brXne by (simp add: T_PS_def)
    have hd: "entry X 0 0 + ?cX \<le> entry (Br X ! J) 0 0"
      using joints_lt_branch_first[OF XX JBrX] by simp
    have hd': "?cX \<le> entry (Br X ! J) 0 0" using hd c0X by simp
    have brstr: "entry (Br X ! J) 0 0 < entry (Br X ! J) 0 j"
      by (rule monoT_row0_min[OF brT brmono jp jbr])
    show "entry (NJ X J) 0 0 < entry (NJ X J) 0 j" using hX0 eq hd' brstr by simp
  qed
  \<comment> \<open>tail nextrel0 sharing (indices \<ge> 1 are the shared branch block).\<close>
  have tailrel: "\<And>p q. nextrel0 (NJ A J) (Suc p) (Suc q) = nextrel0 (NJ X J) (Suc p) (Suc q)"
  proof -
    fix p q
    have nbr: "nextrel0 (Br A ! J) = nextrel0 (Br X ! J)" using RbrJ by (simp add: congR_def)
    have rowA: "\<And>j::nat. 0 < j \<Longrightarrow> j < Lng (NJ A J) \<Longrightarrow> entry (NJ A J) 0 j = entry (Br A ! J) 0 j"
    proof -
      fix j::nat assume jp: "0 < j" and jl: "j < Lng (NJ A J)"
      have "j < Lng (Br A ! J)" using jl LNJA by simp
      thus "entry (NJ A J) 0 j = entry (Br A ! J) 0 j" using entry_NJ_hi[OF jp] by simp
    qed
    have rowX: "\<And>j::nat. 0 < j \<Longrightarrow> j < Lng (NJ X J) \<Longrightarrow> entry (NJ X J) 0 j = entry (Br X ! J) 0 j"
    proof -
      fix j::nat assume jp: "0 < j" and jl: "j < Lng (NJ X J)"
      have "j < Lng (Br X ! J)" using jl LNJX by simp
      thus "entry (NJ X J) 0 j = entry (Br X ! J) 0 j" using entry_NJ_hi[OF jp] by simp
    qed
    have stepA: "nextrel0 (NJ A J) (Suc p) (Suc q) = nextrel0 (Br A ! J) (Suc p) (Suc q)"
      by (rule cdn_nextrel0_suc_cong[OF LNJA rowA])
    have stepX: "nextrel0 (NJ X J) (Suc p) (Suc q) = nextrel0 (Br X ! J) (Suc p) (Suc q)"
      by (rule cdn_nextrel0_suc_cong[OF LNJX rowX])
    show "nextrel0 (NJ A J) (Suc p) (Suc q) = nextrel0 (NJ X J) (Suc p) (Suc q)"
      using stepA stepX nbr by simp
  qed
  have nr0Eq: "nextrel0 (NJ A J) = nextrel0 (NJ X J)"
    by (rule cdn_nextrel0_minhead_cong[OF LNJ minA minX tailrel])
  \<comment> \<open>row-1 agreement.\<close>
  have row1: "\<And>j. j < Lng (NJ X J) \<Longrightarrow> entry (NJ A J) 1 j = entry (NJ X J) 1 j"
  proof -
    fix j assume jX: "j < Lng (NJ X J)"
    have jA: "j < Lng (NJ A J)" using jX LNJ by simp
    show "entry (NJ A J) 1 j = entry (NJ X J) 1 j"
    proof (cases "j = 0")
      case True
      have "entry (NJ A J) 1 0 = entry A 1 0 + npJ A J" by (rule entry_NJ_1_0)
      moreover have "entry (NJ X J) 1 0 = entry X 1 0 + npJ X J" by (rule entry_NJ_1_0)
      ultimately show ?thesis using True e10 npE by simp
    next
      case False
      hence jp: "0 < j" by simp
      have jbrX: "j < Lng (Br X ! J)" using jX LNJX by simp
      have jbrA: "j < Lng (Br A ! J)" using jbrX LbrJ by simp
      have nA: "NJ A J ! j = Br A ! J ! j"
        unfolding NJ_def using jp jbrA by (cases "Br A ! J") (auto simp: nth_Cons')
      have nX: "NJ X J ! j = Br X ! J ! j"
        unfolding NJ_def using jp jbrX by (cases "Br X ! J") (auto simp: nth_Cons')
      have a1: "entry (NJ A J) 1 j = entry (Br A ! J) 1 j" using nA by (simp add: entry_def)
      have x1: "entry (NJ X J) 1 j = entry (Br X ! J) 1 j" using nX by (simp add: entry_def)
      show ?thesis using a1 x1 RbrJ jbrX by (simp add: congR_def)
    qed
  qed
  show ?thesis unfolding congR_def using LNJ nr0Eq row1 by simp
qed


text \<open>Closed form of row-0 of the \<open>coreReduce\<close> recursion arg \<open>diagSeq 0 (m-1) @
  (IncrFirst^m) M\<close>: the diagonal prefix \<open>< m\<close>, the suffix \<open>\<ge> m\<close>.\<close>

lemma cdn_entry0_diagfun:
  assumes mpos: "0 < m" and ib: "i < m + Lng M"
  shows "entry (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) M) 0 i
         = (if i < m then i else entry M 0 (i - m) + m)"
proof (cases "i < m")
  case True
  hence "i \<le> m - 1" using mpos by simp
  thus ?thesis using True by (simp add: entry_diagSeq_append_lo)
next
  case False
  hence im: "m \<le> i" by simp
  let ?R = "(IncrFirst ^^ m) M"
  have iLM: "i - m < Lng M" using ib im by simp
  have e: "entry (diagSeq 0 (m - 1) @ ?R) 0 i = entry ?R 0 (i - m)"
  proof -
    have "i = Suc (m - 1) + (i - m)" using im mpos by simp
    thus ?thesis using entry_diagSeq_append_hi[of "i - m" ?R "m - 1" 0] iLM by simp
  qed
  have eR: "entry ?R 0 (i - m) = entry M 0 (i - m) + m"
    by (rule entry_funpow_IncrFirst0[OF iLM])
  show ?thesis using False e eR by simp
qed

lemma cdn_Lng_diagfun:
  assumes mpos: "0 < m"
  shows "Lng (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) M) = m + Lng M"
proof -
  have "Lng (diagSeq 0 (m - 1)) = m" using mpos by (simp del: upt_Suc)
  thus ?thesis by simp
qed

text \<open>The running-min predicate \<open>\<forall>r<q. entry M 0 r \<ge> entry M 0 q\<close> is characterised
  by \<open>nextrel0\<close>: no \<open>nextrel0\<close> edge enters \<open>q\<close> from a smaller index.\<close>

lemma cdn_runmin_char:
  assumes qM: "q < Lng M"
  shows "(\<forall>r. r < q \<longrightarrow> entry M 0 r \<ge> entry M 0 q)
       = (\<forall>r. r < q \<longrightarrow> \<not> nextrel0 M r q)"
proof
  assume H: "\<forall>r. r < q \<longrightarrow> entry M 0 r \<ge> entry M 0 q"
  show "\<forall>r. r < q \<longrightarrow> \<not> nextrel0 M r q" using H by (auto simp: nextrel0_def)
next
  assume H: "\<forall>r. r < q \<longrightarrow> \<not> nextrel0 M r q"
  show "\<forall>r. r < q \<longrightarrow> entry M 0 r \<ge> entry M 0 q"
  proof (intro allI impI)
    fix r assume r: "r < q"
    show "entry M 0 r \<ge> entry M 0 q"
    proof (rule ccontr)
      assume "\<not> entry M 0 r \<ge> entry M 0 q"
      hence lt: "entry M 0 r < entry M 0 q" by simp
      let ?S = "{r'. r' < q \<and> entry M 0 r' < entry M 0 q}"
      have lin: "r \<in> ?S" using r lt by simp
      have fin: "finite ?S" by simp
      have ne: "?S \<noteq> {}" using lin by blast
      let ?mx = "Max ?S"
      have mS: "?mx \<in> ?S" using Max_in[OF fin ne] .
      hence mq: "?mx < q" and mlt: "entry M 0 ?mx < entry M 0 q" by auto
      have between: "\<forall>j. ?mx < j \<and> j < q \<longrightarrow> entry M 0 j \<ge> entry M 0 q"
      proof (intro allI impI)
        fix j assume j: "?mx < j \<and> j < q"
        show "entry M 0 j \<ge> entry M 0 q"
        proof (rule ccontr)
          assume "\<not> entry M 0 j \<ge> entry M 0 q"
          hence "j \<in> ?S" using j by simp
          hence "j \<le> ?mx" using Max_ge[OF fin] by simp
          thus False using j by simp
        qed
      qed
      have "nextrel0 M ?mx q" unfolding nextrel0_def using mq qM mlt between by simp
      thus False using H mq by blast
    qed
  qed
qed

text \<open>\<open>nextrel0\<close>-congruence of the \<open>coreReduce\<close> arg: from \<open>congR A X\<close> (\<open>nextrel0\<close>
  + \<open>Lng\<close> shared) and \<open>m>0\<close>, the \<open>diagSeq\<close>-prefixed funpow shift preserves
  \<open>nextrel0\<close>.  The diagonal prefix is shared (constant); the suffix \<open>nextrel0\<close> is
  \<open>nextrel0 A = nextrel0 X\<close> (\<open>IncrFirst\<close>-invariant); and the single prefix\<rightarrow>suffix
  boundary edge from index \<open>m-1\<close> is a running-min predicate determined by
  \<open>nextrel0\<close>.\<close>

lemma cdn_nextrel0_diagfun_cong:
  assumes R: "congR A X" and mpos: "0 < m"
  shows "nextrel0 (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) A)
       = nextrel0 (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) X)"
proof (intro ext)
  let ?aA = "diagSeq 0 (m - 1) @ (IncrFirst ^^ m) A"
  let ?aX = "diagSeq 0 (m - 1) @ (IncrFirst ^^ m) X"
  have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
  have nAX: "nextrel0 A = nextrel0 X" using R by (simp add: congR_def)
  have La: "Lng ?aA = m + Lng A" by (rule cdn_Lng_diagfun[OF mpos])
  have Lx: "Lng ?aX = m + Lng X" by (rule cdn_Lng_diagfun[OF mpos])
  have LaLx: "Lng ?aA = Lng ?aX" using La Lx LAX by simp
  have eA: "\<And>i. i < m + Lng A \<Longrightarrow> entry ?aA 0 i = (if i < m then i else entry A 0 (i - m) + m)"
    by (rule cdn_entry0_diagfun[OF mpos])
  have eX: "\<And>i. i < m + Lng X \<Longrightarrow> entry ?aX 0 i = (if i < m then i else entry X 0 (i - m) + m)"
    by (rule cdn_entry0_diagfun[OF mpos])
  fix p q
  show "nextrel0 ?aA p q = nextrel0 ?aX p q"
  proof (cases "p < q \<and> q < Lng ?aA")
    case False
    thus ?thesis unfolding nextrel0_def using LaLx by auto
  next
    case True
    hence pq: "p < q" and qa: "q < Lng ?aA" by simp_all
    have qx: "q < Lng ?aX" using qa LaLx by simp
    have qaB: "q < m + Lng A" using qa La by simp
    have qxB: "q < m + Lng X" using qx Lx by simp
    have eA: "\<And>i. i \<le> q \<Longrightarrow> entry ?aA 0 i = (if i < m then i else entry A 0 (i - m) + m)"
      using eA qaB by (metis le_imp_less_Suc less_Suc_eq_le order_le_less_trans)
    have eX: "\<And>i. i \<le> q \<Longrightarrow> entry ?aX 0 i = (if i < m then i else entry X 0 (i - m) + m)"
      using eX qxB by (metis le_imp_less_Suc less_Suc_eq_le order_le_less_trans)
    show ?thesis
    proof (cases "q < m")
      case qlt: True
      \<comment> \<open>both indices in the diagonal prefix: nextrel0 is the consecutive relation.\<close>
      have plt: "p < m" using pq qlt by simp
      have valA: "\<And>j. j \<le> q \<Longrightarrow> entry ?aA 0 j = j"
        using eA qlt by simp
      have valX: "\<And>j. j \<le> q \<Longrightarrow> entry ?aX 0 j = j"
        using eX qlt by simp
      have diagchar: "\<And>aa::pairseq. q < Lng aa \<Longrightarrow> (\<And>j. j \<le> q \<Longrightarrow> entry aa 0 j = j)
                       \<Longrightarrow> nextrel0 aa p q \<longleftrightarrow> q = Suc p"
      proof -
        fix aa::pairseq
        assume qaa: "q < Lng aa" and val: "\<And>j. j \<le> q \<Longrightarrow> entry aa 0 j = j"
        show "nextrel0 aa p q \<longleftrightarrow> q = Suc p"
        proof
          assume "nextrel0 aa p q"
          hence betw: "\<forall>j. p < j \<and> j < q \<longrightarrow> entry aa 0 j \<ge> entry aa 0 q"
            by (simp add: nextrel0_def)
          show "q = Suc p"
          proof (rule ccontr)
            assume "q \<noteq> Suc p"
            hence "Suc p < q" using pq by simp
            hence "entry aa 0 (Suc p) \<ge> entry aa 0 q" using betw by simp
            moreover have "entry aa 0 (Suc p) = Suc p" using val \<open>Suc p < q\<close> by simp
            moreover have "entry aa 0 q = q" using val by simp
            ultimately show False using \<open>Suc p < q\<close> by simp
          qed
        next
          assume qsp: "q = Suc p"
          have ep: "entry aa 0 p = p" using val pq by simp
          have eq: "entry aa 0 q = q" using val by simp
          have "\<forall>j. p < j \<and> j < q \<longrightarrow> entry aa 0 j \<ge> entry aa 0 q" using qsp by simp
          thus "nextrel0 aa p q" unfolding nextrel0_def using pq qaa ep eq qsp by simp
        qed
      qed
      have lhs: "nextrel0 ?aA p q \<longleftrightarrow> q = Suc p" by (rule diagchar[OF qa valA])
      have rhs: "nextrel0 ?aX p q \<longleftrightarrow> q = Suc p" by (rule diagchar[OF qx valX])
      show ?thesis using lhs rhs by simp
    next
      case qge: False
      hence qm: "m \<le> q" by simp
      then obtain qq where qeq: "q = m + qq" using le_Suc_ex by blast
      have qqA: "qq < Lng A" using qa La qeq by simp
      have eq_q: "entry ?aA 0 q = entry A 0 qq + m" "entry ?aX 0 q = entry X 0 qq + m"
        using eA[of q] eX[of q] qge qeq by simp_all
      show ?thesis
      proof (cases "p < m")
        case psm: True
        \<comment> \<open>prefix\<rightarrow>suffix boundary edge; only \<open>p = m-1\<close> can succeed.\<close>
        show ?thesis
        proof (cases "p = m - 1")
          case pm: True
          \<comment> \<open>edge \<open>m-1 \<rightarrow> q\<close>: holds iff running-min predicate \<open>PA(qq)\<close>, shared.\<close>
          have lhs: "nextrel0 ?aA p q
                = (\<forall>r. r < qq \<longrightarrow> entry A 0 r \<ge> entry A 0 qq)"
          proof
            assume nr: "nextrel0 ?aA p q"
            show "\<forall>r. r < qq \<longrightarrow> entry A 0 r \<ge> entry A 0 qq"
            proof (intro allI impI)
              fix r assume r: "r < qq"
              have idx: "p < m + r \<and> m + r < q" using pm mpos r qeq by simp
              have "entry ?aA 0 (m + r) \<ge> entry ?aA 0 q" using nr idx by (simp add: nextrel0_def)
              moreover have "entry ?aA 0 (m + r) = entry A 0 r + m"
                using eA[of "m + r"] idx by simp
              ultimately show "entry A 0 r \<ge> entry A 0 qq" using eq_q by simp
            qed
          next
            assume H: "\<forall>r. r < qq \<longrightarrow> entry A 0 r \<ge> entry A 0 qq"
            have ep: "entry ?aA 0 p = m - 1" using eA[of p] psm pm pq by simp
            have lt: "entry ?aA 0 p < entry ?aA 0 q" using ep eq_q mpos by simp
            have betw: "\<forall>j. p < j \<and> j < q \<longrightarrow> entry ?aA 0 j \<ge> entry ?aA 0 q"
            proof (intro allI impI)
              fix j assume j: "p < j \<and> j < q"
              have jm: "m \<le> j" using j pm mpos by linarith
              then obtain jj where jj: "j = m + jj" using le_Suc_ex by blast
              have jjlt: "jj < qq" using j jj qeq by simp
              have "entry ?aA 0 j = entry A 0 jj + m" using eA[of j] jm jj j by simp
              thus "entry ?aA 0 j \<ge> entry ?aA 0 q" using H jjlt eq_q by simp
            qed
            show "nextrel0 ?aA p q" unfolding nextrel0_def using pq qa lt betw by simp
          qed
          have rhs: "nextrel0 ?aX p q
                = (\<forall>r. r < qq \<longrightarrow> entry X 0 r \<ge> entry X 0 qq)"
          proof
            assume nr: "nextrel0 ?aX p q"
            show "\<forall>r. r < qq \<longrightarrow> entry X 0 r \<ge> entry X 0 qq"
            proof (intro allI impI)
              fix r assume r: "r < qq"
              have idx: "p < m + r \<and> m + r < q" using pm mpos r qeq by simp
              have "entry ?aX 0 (m + r) \<ge> entry ?aX 0 q" using nr idx by (simp add: nextrel0_def)
              moreover have "entry ?aX 0 (m + r) = entry X 0 r + m" using eX[of "m + r"] idx by simp
              ultimately show "entry X 0 r \<ge> entry X 0 qq" using eq_q by simp
            qed
          next
            assume H: "\<forall>r. r < qq \<longrightarrow> entry X 0 r \<ge> entry X 0 qq"
            have ep: "entry ?aX 0 p = m - 1" using eX[of p] psm pm pq by simp
            have lt: "entry ?aX 0 p < entry ?aX 0 q" using ep eq_q mpos by simp
            have betw: "\<forall>j. p < j \<and> j < q \<longrightarrow> entry ?aX 0 j \<ge> entry ?aX 0 q"
            proof (intro allI impI)
              fix j assume j: "p < j \<and> j < q"
              have jm: "m \<le> j" using j pm mpos by linarith
              then obtain jj where jj: "j = m + jj" using le_Suc_ex by blast
              have jjlt: "jj < qq" using j jj qeq by simp
              have "entry ?aX 0 j = entry X 0 jj + m" using eX[of j] jm jj j by simp
              thus "entry ?aX 0 j \<ge> entry ?aX 0 q" using H jjlt eq_q by simp
            qed
            show "nextrel0 ?aX p q" unfolding nextrel0_def using pq qx lt betw by simp
          qed
          \<comment> \<open>the running-min predicates agree by @{const nextrel0} sharing.\<close>
          have PAeq: "(\<forall>r. r < qq \<longrightarrow> entry A 0 r \<ge> entry A 0 qq)
                    = (\<forall>r. r < qq \<longrightarrow> entry X 0 r \<ge> entry X 0 qq)"
          proof -
            have cA: "(\<forall>r. r < qq \<longrightarrow> entry A 0 r \<ge> entry A 0 qq)
                    = (\<forall>r. r < qq \<longrightarrow> \<not> nextrel0 A r qq)"
              by (rule cdn_runmin_char[OF qqA])
            have qqX: "qq < Lng X" using qqA LAX by simp
            have cX: "(\<forall>r. r < qq \<longrightarrow> entry X 0 r \<ge> entry X 0 qq)
                    = (\<forall>r. r < qq \<longrightarrow> \<not> nextrel0 X r qq)"
              by (rule cdn_runmin_char[OF qqX])
            show ?thesis using cA cX nAX by simp
          qed
          show ?thesis using lhs rhs PAeq by simp
        next
          case pne: False
          hence plt2: "p < m - 1" using psm by simp
          \<comment> \<open>a prefix index \<open>m-1\<close> lies strictly between \<open>p\<close> and \<open>q\<close> with value \<open>m-1 < entry q\<close>,
              so the \<open>between\<close>-test fails on BOTH sides; \<open>nextrel0\<close> is false.\<close>
          have idxm: "p < m - 1 \<and> m - 1 < q" using plt2 qm mpos by simp
          have lhs: "\<not> nextrel0 ?aA p q"
          proof
            assume nr: "nextrel0 ?aA p q"
            have "entry ?aA 0 (m - 1) \<ge> entry ?aA 0 q" using nr idxm by (simp add: nextrel0_def)
            moreover have "entry ?aA 0 (m - 1) = m - 1" using eA[of "m - 1"] mpos qm by simp
            ultimately show False using eq_q mpos by simp
          qed
          have rhs: "\<not> nextrel0 ?aX p q"
          proof
            assume nr: "nextrel0 ?aX p q"
            have "entry ?aX 0 (m - 1) \<ge> entry ?aX 0 q" using nr idxm by (simp add: nextrel0_def)
            moreover have "entry ?aX 0 (m - 1) = m - 1" using eX[of "m - 1"] mpos qm by simp
            ultimately show False using eq_q mpos by simp
          qed
          show ?thesis using lhs rhs by simp
        qed
      next
        case pge: False
        hence pm: "m \<le> p" by simp
        then obtain pp where peq: "p = m + pp" using le_Suc_ex by blast
        \<comment> \<open>suffix\<rightarrow>suffix edge: reduces to \<open>nextrel0 A pp qq = nextrel0 X pp qq\<close>.\<close>
        have ppqq: "pp < qq" using pq peq qeq by simp
        have lhs: "nextrel0 ?aA p q = nextrel0 A pp qq"
        proof
          assume nr: "nextrel0 ?aA p q"
          have lt: "entry A 0 pp < entry A 0 qq"
            using nr eA[of p] eA[of q] pm peq qge qeq pq by (simp add: nextrel0_def)
          have betw: "\<forall>j. pp < j \<and> j < qq \<longrightarrow> entry A 0 j \<ge> entry A 0 qq"
          proof (intro allI impI)
            fix j assume j: "pp < j \<and> j < qq"
            have idx: "p < m + j \<and> m + j < q" using j peq qeq by simp
            have "entry ?aA 0 (m + j) \<ge> entry ?aA 0 q" using nr idx by (simp add: nextrel0_def)
            thus "entry A 0 j \<ge> entry A 0 qq" using eA[of "m + j"] idx eq_q by simp
          qed
          show "nextrel0 A pp qq" unfolding nextrel0_def using ppqq qqA lt betw by simp
        next
          assume nr: "nextrel0 A pp qq"
          have ppA: "pp < Lng A" using ppqq qqA by simp
          have lt: "entry ?aA 0 p < entry ?aA 0 q"
            using nr eA[of p] eA[of q] pm peq qge qeq pq by (simp add: nextrel0_def)
          have betw: "\<forall>j. p < j \<and> j < q \<longrightarrow> entry ?aA 0 j \<ge> entry ?aA 0 q"
          proof (intro allI impI)
            fix j assume j: "p < j \<and> j < q"
            have jm: "m \<le> j" using j peq by simp
            then obtain jj where jj: "j = m + jj" using le_Suc_ex by blast
            have jjr: "pp < jj \<and> jj < qq" using j jj peq qeq by simp
            have "entry A 0 jj \<ge> entry A 0 qq" using nr jjr by (simp add: nextrel0_def)
            thus "entry ?aA 0 j \<ge> entry ?aA 0 q" using eA[of j] jm jj j eq_q by simp
          qed
          show "nextrel0 ?aA p q" unfolding nextrel0_def using pq qa lt betw by simp
        qed
        have rhs: "nextrel0 ?aX p q = nextrel0 X pp qq"
        proof
          assume nr: "nextrel0 ?aX p q"
          have qqX: "qq < Lng X" using qqA LAX by simp
          have lt: "entry X 0 pp < entry X 0 qq"
            using nr eX[of p] eX[of q] pm peq qge qeq pq by (simp add: nextrel0_def)
          have betw: "\<forall>j. pp < j \<and> j < qq \<longrightarrow> entry X 0 j \<ge> entry X 0 qq"
          proof (intro allI impI)
            fix j assume j: "pp < j \<and> j < qq"
            have idx: "p < m + j \<and> m + j < q" using j peq qeq by simp
            have "entry ?aX 0 (m + j) \<ge> entry ?aX 0 q" using nr idx by (simp add: nextrel0_def)
            thus "entry X 0 j \<ge> entry X 0 qq" using eX[of "m + j"] idx eq_q by simp
          qed
          show "nextrel0 X pp qq" unfolding nextrel0_def using ppqq qqX lt betw by simp
        next
          assume nr: "nextrel0 X pp qq"
          have qqX: "qq < Lng X" using qqA LAX by simp
          have lt: "entry ?aX 0 p < entry ?aX 0 q"
            using nr eX[of p] eX[of q] pm peq qge qeq pq by (simp add: nextrel0_def)
          have betw: "\<forall>j. p < j \<and> j < q \<longrightarrow> entry ?aX 0 j \<ge> entry ?aX 0 q"
          proof (intro allI impI)
            fix j assume j: "p < j \<and> j < q"
            have jm: "m \<le> j" using j peq by simp
            then obtain jj where jj: "j = m + jj" using le_Suc_ex by blast
            have jjr: "pp < jj \<and> jj < qq" using j jj peq qeq by simp
            have "entry X 0 jj \<ge> entry X 0 qq" using nr jjr by (simp add: nextrel0_def)
            thus "entry ?aX 0 j \<ge> entry ?aX 0 q" using eX[of j] jm jj j eq_q by simp
          qed
          show "nextrel0 ?aX p q" unfolding nextrel0_def using pq qx lt betw by simp
        qed
        show ?thesis using lhs rhs nAX by simp
      qed
    qed
  qed
qed

text \<open>\<open>congR_diag_funpow\<close>: the \<open>m\<^sub>1\<^sub>0 > 0\<close> recursion arg inherits \<open>congR\<close>.\<close>

lemma congR_diag_funpow:
  assumes R: "congR A X" and mpos: "0 < m"
  shows "congR (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) A)
              (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) X)"
proof -
  let ?aA = "diagSeq 0 (m - 1) @ (IncrFirst ^^ m) A"
  let ?aX = "diagSeq 0 (m - 1) @ (IncrFirst ^^ m) X"
  have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
  show ?thesis unfolding congR_def
  proof (intro conjI allI impI)
    show "Lng ?aA = Lng ?aX" using cdn_Lng_diagfun[OF mpos] LAX by simp
  next
    show "nextrel0 ?aA = nextrel0 ?aX" by (rule cdn_nextrel0_diagfun_cong[OF R mpos])
  next
    fix j assume jX: "j < Lng ?aX"
    have Lx: "Lng ?aX = m + Lng X" by (rule cdn_Lng_diagfun[OF mpos])
    have La: "Lng ?aA = m + Lng A" by (rule cdn_Lng_diagfun[OF mpos])
    show "entry ?aA 1 j = entry ?aX 1 j"
    proof (cases "j < m")
      case True
      hence "j \<le> m - 1" using mpos by simp
      thus ?thesis by (simp add: entry_diagSeq_append_lo)
    next
      case False
      hence jm: "m \<le> j" by simp
      then obtain jj where jj: "j = m + jj" using le_Suc_ex by blast
      have jjX: "jj < Lng X" using jX Lx jj by simp
      have jjA: "jj < Lng A" using jjX LAX by simp
      have eA1: "entry ?aA 1 j = entry A 1 jj"
      proof -
        have je: "j = Suc (m - 1) + jj" using jm mpos jj by simp
        have "entry ?aA 1 j = entry ((IncrFirst ^^ m) A) 1 jj"
          using je entry_diagSeq_append_hi[of jj "(IncrFirst ^^ m) A" "m - 1" 1] jjA by simp
        thus ?thesis using entry_funpow_IncrFirst1[OF jjA] by simp
      qed
      have eX1: "entry ?aX 1 j = entry X 1 jj"
      proof -
        have je: "j = Suc (m - 1) + jj" using jm mpos jj by simp
        have "entry ?aX 1 j = entry ((IncrFirst ^^ m) X) 1 jj"
          using je entry_diagSeq_append_hi[of jj "(IncrFirst ^^ m) X" "m - 1" 1] jjX by simp
        thus ?thesis using entry_funpow_IncrFirst1[OF jjX] by simp
      qed
      have "entry A 1 jj = entry X 1 jj" using R jjX by (simp add: congR_def)
      thus ?thesis using eA1 eX1 by simp
    qed
  qed
qed

text \<open>\<open>shiftRow0\<close> is the identity on a row-0-anchored (\<open>m\<^sub>0\<^sub>0 = 0\<close>) sequence.\<close>

lemma cdn_shiftRow0_id:
  assumes c0: "entry M 0 0 = 0"
  shows "shiftRow0 M = M"
proof (rule nth_equalityI)
  show "length (shiftRow0 M) = length M" by simp
next
  fix p assume p: "p < length (shiftRow0 M)"
  hence pL: "p < Lng M" by simp
  have "shiftRow0 M ! p = (entry M 0 p - entry M 0 0, entry M 1 p)"
    using pL by (simp add: shiftRow0_def)
  also have "\<dots> = (entry M 0 p, entry M 1 p)" using c0 by simp
  also have "\<dots> = M ! p" by (rule entry_pair)
  finally show "shiftRow0 M ! p = M ! p" .
qed

text \<open>\<open>Red M = Red (shiftRow0 M)\<close> for a mono \<open>M\<close> with \<open>m\<^sub>1\<^sub>0 = 0\<close>: if \<open>m\<^sub>0\<^sub>0 = 0\<close>
  the shift is the identity; if \<open>m\<^sub>0\<^sub>0 > 0\<close> the shift branch of @{const Red} is
  exactly \<open>Red (shiftRow0 M)\<close>.  This is the easy half needed for the cross-branch
  alignment (the \<open>m\<^sub>1\<^sub>0 > 0\<close> case never arises against a shift-branch partner).\<close>

lemma cdn_Red_shiftRow0_m10z:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and c1: "entry M 1 0 = 0"
  shows "Red M = Red (shiftRow0 M)"
proof (cases "entry M 0 0 = 0")
  case True
  thus ?thesis using cdn_shiftRow0_id[OF True] by simp
next
  case False
  hence c0p: "0 < entry M 0 0" by simp
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have nz: "\<not> zeroT M" using mono by (simp add: multiT_def monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  let ?j1 = "Lng M - 1"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have nc: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" using False by simp
  have rM: "Red M = Red (map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Suc ?j1])"
    using Red.psimps[OF domM] nz nmu nc c1 by (simp add: Let_def)
  have SX: "map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Suc ?j1] = shiftRow0 M"
  proof -
    have "Suc ?j1 = Lng M" using LMpos by simp
    thus ?thesis by (simp add: shiftRow0_def)
  qed
  show ?thesis using rM SX by simp
qed

text \<open>\<open>shiftRow0\<close> relates a mono \<open>M\<close> to itself by \<open>congR\<close> (row 1 untouched,
  \<open>nextrel0\<close> shift-invariant).\<close>

lemma congR_self_shiftRow0:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
  shows "congR M (shiftRow0 M)"
  unfolding congR_def
proof (intro conjI allI impI)
  show "Lng M = Lng (shiftRow0 M)" by simp
next
  show "nextrel0 M = nextrel0 (shiftRow0 M)"
  proof (intro ext)
    fix p q show "nextrel0 M p q = nextrel0 (shiftRow0 M) p q"
      by (rule nextrel0_shiftRow0_eq[OF MT mono, symmetric])
  qed
next
  fix j assume "j < Lng (shiftRow0 M)"
  hence jM: "j < Lng M" by simp
  thus "entry M 1 j = entry (shiftRow0 M) 1 j" using entry_shiftRow0_1[OF jM] by simp
qed

text \<open>\<^bold>\<open>The master key\<close>: \<open>Red\<close> is a \<open>congR\<close> (nextrel-structure) congruence.  Proved by
  @{thm [source] Red.pinduct} on \<open>A\<close>; the cross-branch case (\<open>A\<close> core, \<open>X\<close> shift)
  is closed by normalising \<open>X\<close> via @{thm [source] cdn_Red_shiftRow0_m10z}
  (\<open>m\<^sub>1\<^sub>0 = 0\<close> there), reducing it to the aligned core-core case.\<close>

lemma cdn_red_cong:
  "\<And>X. congR A X \<Longrightarrow> A \<in> T_PS \<Longrightarrow> Red A = Red X"
proof -
  have "A \<in> T_PS \<longrightarrow> (\<forall>X. congR A X \<longrightarrow> Red A = Red X)"
  proof (cases "A \<in> T_PS")
    case False thus ?thesis by simp
  next
    case AT0: True
    have domA: "Red_dom A" by (rule m_6_5_Red_welldef[OF AT0])
    show ?thesis
      using domA
    proof (induction A rule: Red.pinduct)
      case (1 A)
      note dom = 1(1)
      note IH_mu = 1(2)
      note IH_bz = 1(3)
      note IH_sh = 1(4)
      note IH_m1 = 1(5)
      show ?case
      proof (rule impI, rule allI, rule impI)
        assume AT: "A \<in> T_PS"
        fix X assume R: "congR A X"
        have Ane: "A \<noteq> []" using AT by (simp add: T_PS_def)
        have LApos: "0 < Lng A" using Ane by (cases A) auto
        have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
        have Xne: "X \<noteq> []" using LAX LApos by (cases X) auto
        have XT: "X \<in> T_PS" using Xne by (simp add: T_PS_def)
        have zE: "zeroT A = zeroT X" by (rule congR_zeroT[OF R])
        have muE: "multiT A = multiT X" by (rule congR_multiT[OF R])
        have trE: "TrMax A = TrMax X" by (rule congR_TrMax[OF R])
        have domX: "Red_dom X" by (rule m_6_5_Red_welldef[OF XT])
        show "Red A = Red X"
        proof (cases "zeroT A")
          case True
          have "Red A = [(0,0)]" using Red.psimps[OF dom] True by simp
          moreover have "Red X = [(0,0)]" using Red.psimps[OF domX] zE True by simp
          ultimately show ?thesis by simp
        next
          case nz: False
          have nzX: "\<not> zeroT X" using zE nz by simp
          show ?thesis
          proof (cases "multiT A")
            case mu: True
            have muX: "multiT X" using muE mu by simp
            have rA: "Red A = concat (map Red (P A))"
              using Red.psimps[OF dom] nz mu by simp
            have rX: "Red X = concat (map Red (P X))"
              using Red.psimps[OF domX] nzX muX by simp
            have lenP: "length (P A) = length (P X)" by (rule congR_P_length[OF R])
            have blocks: "\<And>J. J < length (P X) \<Longrightarrow> Red (P A ! J) = Red (P X ! J)"
            proof -
              fix J assume JX: "J < length (P X)"
              have JA: "J < length (P A)" using JX lenP by simp
              have RP: "congR (P A ! J) (P X ! J)" by (rule congR_P_block[OF R AT XT JX])
              have PAJ_T: "P A ! J \<in> T_PS"
                using P_blocks_nonempty[OF Ane] JA nth_mem by (metis T_PS_def mem_Collect_eq)
              have ih: "P A ! J \<in> T_PS \<longrightarrow> (\<forall>Y. congR (P A ! J) Y \<longrightarrow> Red (P A ! J) = Red Y)"
                by (rule IH_mu[OF nz mu]) (rule nth_mem[OF JA])
              thus "Red (P A ! J) = Red (P X ! J)" using PAJ_T RP by blast
            qed
            have "map Red (P A) = map Red (P X)"
              by (rule nth_equalityI) (simp_all add: lenP blocks)
            thus ?thesis using rA rX by simp
          next
            case nmu: False
            have nmuX: "\<not> multiT X" using muE nmu by simp
            have monoA: "monoT A" using nz nmu by (simp add: multiT_def)
            have monoX: "monoT X" using nzX nmuX by (simp add: multiT_def)
            have Apt: "A \<in> PT_PS" using AT monoA by (simp add: PT_PS_def)
            have Xpt: "X \<in> PT_PS" using XT monoX by (simp add: PT_PS_def)
            \<comment> \<open>row-1 head shared: m10 equal on both sides.\<close>
            have m10E: "entry A 1 0 = entry X 1 0" using R LApos by (simp add: congR_def)
            show ?thesis
            proof (cases "entry A 1 0 = 0")
              case c1z: True
              have c1zX: "entry X 1 0 = 0" using m10E c1z by simp
              show ?thesis
              proof (cases "entry A 0 0 = 0")
                case c0z: True
                \<comment> \<open>A is core.  Normalise X to its row-0 anchor X' (= X if core, else shiftRow0 X).\<close>
                let ?X' = "shiftRow0 X"
                have RedX: "Red X = Red ?X'" by (rule cdn_Red_shiftRow0_m10z[OF XT monoX c1zX])
                have RXX': "congR X ?X'" by (rule congR_self_shiftRow0[OF XT monoX])
                have RAX': "congR A ?X'" by (rule congR_trans[OF R RXX'])
                have X'T: "?X' \<in> T_PS" by (simp add: T_PS_def shiftRow0_def Xne)
                have monoX': "monoT ?X'" by (rule monoT_shiftRow0[OF XT monoX])
                have c0X': "entry ?X' 0 0 = 0"
                  using entry_shiftRow0_0[OF LApos[unfolded LAX]] by simp
                have c1X': "entry ?X' 1 0 = 0"
                  using entry_shiftRow0_1[OF LApos[unfolded LAX]] c1zX by simp
                have LX': "Lng ?X' = Lng A" using LAX by simp
                have nzX': "\<not> zeroT ?X'" using monoX' by (simp add: monoT_def multiT_def)
                have nmuX': "\<not> multiT ?X'" using monoX' by (simp add: multiT_def)
                have X'pt: "?X' \<in> PT_PS" using X'T monoX' by (simp add: PT_PS_def)
                have nc0X': "\<not> (entry ?X' 0 0 = 0 \<and> entry ?X' 1 0 = 0) \<Longrightarrow> False"
                  using c0X' c1X' by simp
                \<comment> \<open>both A and X' are core: align the core formula.\<close>
                have RAA': "Red A = Red ?X'"
                proof (cases "TrMax A = Lng A - 1")
                  case trunk: True
                  have rA: "Red A = diagSeq (entry A 1 0) (entry A 1 0 + (Lng A - 1))"
                    using Red.psimps[OF dom] nz nmu c0z c1z trunk by (simp add: Let_def)
                  have trX': "TrMax ?X' = Lng ?X' - 1"
                    using congR_TrMax[OF RAX'] trunk LX' by simp
                  have rX': "Red ?X' = diagSeq (entry ?X' 1 0) (entry ?X' 1 0 + (Lng ?X' - 1))"
                    using Red.psimps[OF m_6_5_Red_welldef[OF X'T]] nzX' nmuX' c0X' c1X' trX'
                    by (simp add: Let_def)
                  show ?thesis using rA rX' c1z c1X' LX' by simp
                next
                  case tne: False
                  have trX'ne: "TrMax ?X' \<noteq> Lng ?X' - 1"
                    using congR_TrMax[OF RAX'] tne LX' by simp
                  let ?bl = "\<lambda>M J. (IncrFirst ^^ (Joints M ! J + 1
                        - (if entry (Br M ! J) 1 0 = 0 then 0
                           else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
                      (Red ((entry M 0 0 + Joints M ! J + 1,
                             entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                    else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                            # tl (Br M ! J)))"
                  have rA: "Red A = diagSeq 0 (TrMax A) @ concat (map (?bl A) [0..<Lng (Br A)])"
                    using Red.psimps[OF dom] nz nmu c0z c1z tne by (simp add: Let_def)
                  have rX': "Red ?X' = diagSeq 0 (TrMax ?X') @ concat (map (?bl ?X') [0..<Lng (Br ?X')])"
                    using Red.psimps[OF m_6_5_Red_welldef[OF X'T]] nzX' nmuX' c0X' c1X' trX'ne
                    by (simp add: Let_def)
                  have LbrE: "Lng (Br A) = Lng (Br ?X')" by (rule congR_Br_length[OF RAX' AT X'T])
                  have concatEq: "concat (map (?bl A) [0..<Lng (Br A)])
                                = concat (map (?bl ?X') [0..<Lng (Br ?X')])"
                  proof (rule arg_cong[where f=concat], simp only: LbrE, rule map_cong[OF refl])
                    fix J assume "J \<in> set [0..<Lng (Br ?X')]"
                    hence JBr: "J < Lng (Br ?X')" by simp
                    hence JBr': "J < length (Br ?X')" by simp
                    have jtE: "Joints A ! J = Joints ?X' ! J" using congR_Joints[OF RAX' AT X'T] by simp
                    have npAeq: "(if entry (Br A ! J) 1 0 = 0 then 0
                                  else Suc (THE j. nextR A 1 j (FirstNodes A ! J))) = npJ A J"
                      unfolding npJ_def by (rule refl)
                    have npX'eq: "(if entry (Br ?X' ! J) 1 0 = 0 then 0
                                  else Suc (THE j. nextR ?X' 1 j (FirstNodes ?X' ! J))) = npJ ?X' J"
                      unfolding npJ_def by (rule refl)
                    have npE: "npJ A J = npJ ?X' J" by (rule congR_npJ[OF RAX' AT X'T JBr'])
                    have argAeq: "(entry A 0 0 + Joints A ! J + 1, entry A 1 0 + npJ A J)
                                  # tl (Br A ! J) = NJ A J" unfolding NJ_def by (rule refl)
                    have argX'eq: "(entry ?X' 0 0 + Joints ?X' ! J + 1, entry ?X' 1 0 + npJ ?X' J)
                                  # tl (Br ?X' ! J) = NJ ?X' J" unfolding NJ_def by (rule refl)
                    have RNJ: "congR (NJ A J) (NJ ?X' J)"
                      by (rule congR_NJ[OF RAX' Apt X'pt c0z c0X' JBr'])
                    have NJAne: "NJ A J \<noteq> []" by (simp add: NJ_def)
                    have NJAT: "NJ A J \<in> T_PS" using NJAne by (simp add: T_PS_def)
                    have JBrA: "J < Lng (Br A)" using JBr LbrE by simp
                    have Jmem: "J \<in> set [0..<Lng (Br A)]" using JBrA by simp
                    have core': "entry A 0 0 = 0 \<and> entry A 1 0 = 0" using c0z c1z by simp
                    have ih: "NJ A J \<in> T_PS \<longrightarrow> (\<forall>Y. congR (NJ A J) Y \<longrightarrow> Red (NJ A J) = Red Y)"
                      using IH_bz[OF nz nmu refl refl refl refl core' tne Jmem] c0z c1z
                      by (simp add: c0z c1z NJ_def npJ_def)
                    have RedNJ: "Red (NJ A J) = Red (NJ ?X' J)" using ih NJAT RNJ by blast
                    have expE: "Joints A ! J + 1 - npJ A J = Joints ?X' ! J + 1 - npJ ?X' J"
                      using jtE npE by simp
                    show "?bl A J = ?bl ?X' J"
                      by (simp only: npAeq npX'eq argAeq argX'eq expE RedNJ)
                  qed
                  have prefE: "diagSeq 0 (TrMax A) = diagSeq 0 (TrMax ?X')"
                    using congR_TrMax[OF RAX'] by simp
                  show ?thesis using rA rX' prefE concatEq by simp
                qed
                show ?thesis using RAA' RedX by simp
              next
                case c0p: False
                \<comment> \<open>A is shift (m00>0, m10=0): \<open>Red A = Red (shiftRow0 A)\<close>; align via IH_sh.\<close>
                have ncA: "\<not> (entry A 0 0 = 0 \<and> entry A 1 0 = 0)" using c0p by simp
                let ?SA = "map (\<lambda>j. (entry A 0 j - entry A 0 0, entry A 1 j)) [0..<Suc (Lng A - 1)]"
                have rA: "Red A = Red ?SA"
                  using Red.psimps[OF dom] nz nmu ncA c1z by (simp add: Let_def)
                have SAeq: "?SA = shiftRow0 A"
                proof -
                  have "Suc (Lng A - 1) = Lng A" using LApos by simp
                  thus ?thesis by (simp add: shiftRow0_def)
                qed
                have RedX: "Red X = Red (shiftRow0 X)"
                  by (rule cdn_Red_shiftRow0_m10z[OF XT monoX c1zX])
                have RshiftR: "congR (shiftRow0 A) (shiftRow0 X)"
                  by (rule congR_shiftRow0[OF R AT XT monoA monoX])
                have SAT: "shiftRow0 A \<in> T_PS" by (simp add: T_PS_def shiftRow0_def Ane)
                have ih: "shiftRow0 A \<in> T_PS \<longrightarrow>
                            (\<forall>Y. congR (shiftRow0 A) Y \<longrightarrow> Red (shiftRow0 A) = Red Y)"
                  using IH_sh[OF nz nmu refl refl refl refl ncA c1z] SAeq by simp
                have "Red (shiftRow0 A) = Red (shiftRow0 X)" using ih SAT RshiftR by blast
                thus ?thesis using rA SAeq RedX by simp
              qed
            next
              case c1p: False
              \<comment> \<open>m10>0 on both sides: aligned m10>0 branch, args congR by congR_diag_funpow.\<close>
              have pos: "0 < entry A 1 0" using c1p by simp
              have posX: "0 < entry X 1 0" using m10E pos by simp
              have ncA: "\<not> (entry A 0 0 = 0 \<and> entry A 1 0 = 0)" using pos by simp
              have ncX: "\<not> (entry X 0 0 = 0 \<and> entry X 1 0 = 0)" using posX by simp
              let ?m10 = "entry A 1 0"
              have m10eq: "entry X 1 0 = ?m10" using m10E by simp
              let ?argA = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) A"
              let ?argX = "diagSeq 0 (entry X 1 0 - 1) @ (IncrFirst ^^ (entry X 1 0)) X"
              have argXrw: "?argX = diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) X" using m10eq by simp
              have Rarg: "congR ?argA (diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) X)"
                by (rule congR_diag_funpow[OF R pos])
              have funA_ne: "(IncrFirst ^^ ?m10) A \<noteq> []"
                using Ane by (metis Lng_funpow_IncrFirst length_0_conv)
              have argAT: "?argA \<in> T_PS" using funA_ne by (simp add: T_PS_def)
              have ih: "?argA \<in> T_PS \<longrightarrow> (\<forall>Y. congR ?argA Y \<longrightarrow> Red ?argA = Red Y)"
                using IH_m1[OF nz nmu refl refl refl refl ncA c1p] by simp
              have NN: "Red ?argA = Red ?argX"
                using ih argAT Rarg argXrw by simp
              \<comment> \<open>productive outputs read off the shared \<open>N = Red argA = Red argX\<close>.\<close>
              let ?N = "Red ?argA"
              have LN: "Lng ?N = ?m10 + Lng A"
                using m_6_5_monoT_Red_fact1_Lng[OF AT pos] by simp
              have jN_ge: "?m10 \<le> Lng ?N - 1" using LN LApos by linarith
              have segN_PT: "seg ?N ?m10 (Lng ?N - 1) \<in> PT_PS"
                using m_6_5_monoT_Red_m10pos[OF Apt pos] by simp
              have thenA: "?m10 \<le> Lng ?N - 1 \<and> seg ?N ?m10 (Lng ?N - 1) \<in> PT_PS"
                using jN_ge segN_PT by simp
              let ?outMap = "\<lambda>P m. map (\<lambda>j. (entry P 0 j - entry P 0 m + entry P 1 m,
                                            entry P 1 j)) [m..<Suc (Lng P - 1)]"
              have rA: "Red A = ?outMap ?N ?m10"
                using Red.psimps[OF dom] nz nmu ncA pos thenA by (simp add: Let_def)
              have thenX: "?m10 \<le> Lng (Red ?argX) - 1
                            \<and> seg (Red ?argX) ?m10 (Lng (Red ?argX) - 1) \<in> PT_PS"
                using thenA NN by simp
              have rX: "Red X = ?outMap (Red ?argX) (entry X 1 0)"
                using Red.psimps[OF domX] nzX nmuX ncX posX thenX m10eq by (simp add: Let_def)
              show ?thesis using rA rX NN m10eq by simp
            qed
          qed
        qed
      qed
    qed
  qed
  thus "\<And>X. congR A X \<Longrightarrow> A \<in> T_PS \<Longrightarrow> Red A = Red X" by blast
qed




subsection \<open>§6.5/§6.6 idempotency keystone residual (B2): \<open>Red (coreReduce (Red M)) = Red (coreReduce M)\<close>\<close>

text \<open>m: row-0 of the unbumped diagonal-prefixed sequence \<open>diagSeq 0 (m-1) @ B\<close>.\<close>

lemma b2_entry0_diag_app:
  assumes mpos: "0 < m" and ib: "i < m + Lng B"
  shows "entry (diagSeq 0 (m - 1) @ B) 0 i
         = (if i < m then i else entry B 0 (i - m))"
proof (cases "i < m")
  case True
  hence "i \<le> m - 1" using mpos by simp
  thus ?thesis using True by (simp add: entry_diagSeq_append_lo)
next
  case False
  hence im: "m \<le> i" by simp
  have iLB: "i - m < Lng B" using ib im by simp
  have "i = Suc (m - 1) + (i - m)" using im mpos by simp
  thus ?thesis using entry_diagSeq_append_hi[of "i - m" B "m - 1" 0] iLB False by simp
qed

lemma b2_Lng_diag_app:
  assumes mpos: "0 < m"
  shows "Lng (diagSeq 0 (m - 1) @ B) = m + Lng B"
proof -
  have "Lng (diagSeq 0 (m - 1)) = m" using mpos by (simp del: upt_Suc)
  thus ?thesis by simp
qed

text \<open>m: the genuine new \<open>nextrel0\<close> congruence for the multi-\<open>IncrFirst\<close> tail bump.
  \<open>diagSeq 0 (m-1) @ (IncrFirst^^m) B\<close> bumps the tail of \<open>diagSeq 0 (m-1) @ B\<close>
  by \<open>+m\<close> past the cut at \<open>m\<close>.  When every tail row-0 value is \<open>\<ge> m\<close> (the cut
  condition), this preserves \<open>nextrel0\<close>: the diagonal prefix is shared, the
  prefix\<rightarrow>suffix boundary edge \<open>m-1 \<rightarrow> q\<close> reduces to the same running-min
  predicate on \<open>B\<close>, and suffix\<rightarrow>suffix edges are a uniform shift.\<close>

lemma b2_nextrel0_tailbump:
  assumes mpos: "0 < m" and cut: "\<And>j. j < Lng B \<Longrightarrow> m \<le> entry B 0 j"
  shows "nextrel0 (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) B)
       = nextrel0 (diagSeq 0 (m - 1) @ B)"
proof (intro ext)
  let ?aA = "diagSeq 0 (m - 1) @ (IncrFirst ^^ m) B"
  let ?aX = "diagSeq 0 (m - 1) @ B"
  have La: "Lng ?aA = m + Lng B" by (rule cdn_Lng_diagfun[OF mpos])
  have Lx: "Lng ?aX = m + Lng B" by (rule b2_Lng_diag_app[OF mpos])
  have LaLx: "Lng ?aA = Lng ?aX" using La Lx by simp
  have eA0: "\<And>i. i < m + Lng B \<Longrightarrow> entry ?aA 0 i = (if i < m then i else entry B 0 (i - m) + m)"
    by (rule cdn_entry0_diagfun[OF mpos])
  have eX0: "\<And>i. i < m + Lng B \<Longrightarrow> entry ?aX 0 i = (if i < m then i else entry B 0 (i - m))"
    by (rule b2_entry0_diag_app[OF mpos])
  fix p q
  show "nextrel0 ?aA p q = nextrel0 ?aX p q"
  proof (cases "p < q \<and> q < Lng ?aA")
    case False
    thus ?thesis unfolding nextrel0_def using LaLx by auto
  next
    case True
    hence pq: "p < q" and qa: "q < Lng ?aA" by simp_all
    have qx: "q < Lng ?aX" using qa LaLx by simp
    have qaB: "q < m + Lng B" using qa La by simp
    have eA: "\<And>i. i \<le> q \<Longrightarrow> entry ?aA 0 i = (if i < m then i else entry B 0 (i - m) + m)"
      using eA0 qaB by (metis le_imp_less_Suc less_Suc_eq_le order_le_less_trans)
    have eX: "\<And>i. i \<le> q \<Longrightarrow> entry ?aX 0 i = (if i < m then i else entry B 0 (i - m))"
      using eX0 qaB by (metis le_imp_less_Suc less_Suc_eq_le order_le_less_trans)
    show ?thesis
    proof (cases "q < m")
      case qlt: True
      have plt: "p < m" using pq qlt by simp
      have valA: "\<And>j. j \<le> q \<Longrightarrow> entry ?aA 0 j = j" using eA qlt by simp
      have valX: "\<And>j. j \<le> q \<Longrightarrow> entry ?aX 0 j = j" using eX qlt by simp
      have diagchar: "\<And>aa::pairseq. q < Lng aa \<Longrightarrow> (\<And>j. j \<le> q \<Longrightarrow> entry aa 0 j = j)
                       \<Longrightarrow> nextrel0 aa p q \<longleftrightarrow> q = Suc p"
      proof -
        fix aa::pairseq
        assume qaa: "q < Lng aa" and val: "\<And>j. j \<le> q \<Longrightarrow> entry aa 0 j = j"
        show "nextrel0 aa p q \<longleftrightarrow> q = Suc p"
        proof
          assume "nextrel0 aa p q"
          hence betw: "\<forall>j. p < j \<and> j < q \<longrightarrow> entry aa 0 j \<ge> entry aa 0 q"
            by (simp add: nextrel0_def)
          show "q = Suc p"
          proof (rule ccontr)
            assume "q \<noteq> Suc p"
            hence "Suc p < q" using pq by simp
            hence "entry aa 0 (Suc p) \<ge> entry aa 0 q" using betw by simp
            moreover have "entry aa 0 (Suc p) = Suc p" using val \<open>Suc p < q\<close> by simp
            moreover have "entry aa 0 q = q" using val by simp
            ultimately show False using \<open>Suc p < q\<close> by simp
          qed
        next
          assume qsp: "q = Suc p"
          have ep: "entry aa 0 p = p" using val pq by simp
          have eq: "entry aa 0 q = q" using val by simp
          have "\<forall>j. p < j \<and> j < q \<longrightarrow> entry aa 0 j \<ge> entry aa 0 q" using qsp by simp
          thus "nextrel0 aa p q" unfolding nextrel0_def using pq qaa ep eq qsp by simp
        qed
      qed
      have lhs: "nextrel0 ?aA p q \<longleftrightarrow> q = Suc p" by (rule diagchar[OF qa valA])
      have rhs: "nextrel0 ?aX p q \<longleftrightarrow> q = Suc p" by (rule diagchar[OF qx valX])
      show ?thesis using lhs rhs by simp
    next
      case qge: False
      hence qm: "m \<le> q" by simp
      then obtain qq where qeq: "q = m + qq" using le_Suc_ex by blast
      have qqB: "qq < Lng B" using qa La qeq by simp
      have eq_qA: "entry ?aA 0 q = entry B 0 qq + m" using eA[of q] qge qeq by simp
      have eq_qX: "entry ?aX 0 q = entry B 0 qq" using eX[of q] qge qeq by simp
      have cutqq: "m \<le> entry B 0 qq" by (rule cut[OF qqB])
      show ?thesis
      proof (cases "p < m")
        case psm: True
        show ?thesis
        proof (cases "p = m - 1")
          case pm: True
          have lhs: "nextrel0 ?aA p q = (\<forall>r. r < qq \<longrightarrow> entry B 0 r \<ge> entry B 0 qq)"
          proof
            assume nr: "nextrel0 ?aA p q"
            show "\<forall>r. r < qq \<longrightarrow> entry B 0 r \<ge> entry B 0 qq"
            proof (intro allI impI)
              fix r assume r: "r < qq"
              have idx: "p < m + r \<and> m + r < q" using pm mpos r qeq by simp
              have "entry ?aA 0 (m + r) \<ge> entry ?aA 0 q" using nr idx by (simp add: nextrel0_def)
              moreover have "entry ?aA 0 (m + r) = entry B 0 r + m" using eA[of "m + r"] idx by simp
              ultimately show "entry B 0 r \<ge> entry B 0 qq" using eq_qA by simp
            qed
          next
            assume H: "\<forall>r. r < qq \<longrightarrow> entry B 0 r \<ge> entry B 0 qq"
            have ep: "entry ?aA 0 p = m - 1" using eA[of p] psm pm pq by simp
            have lt: "entry ?aA 0 p < entry ?aA 0 q" using ep eq_qA mpos by simp
            have betw: "\<forall>j. p < j \<and> j < q \<longrightarrow> entry ?aA 0 j \<ge> entry ?aA 0 q"
            proof (intro allI impI)
              fix j assume j: "p < j \<and> j < q"
              have jm: "m \<le> j" using j pm mpos by linarith
              then obtain jj where jj: "j = m + jj" using le_Suc_ex by blast
              have jjlt: "jj < qq" using j jj qeq by simp
              have "entry ?aA 0 j = entry B 0 jj + m" using eA[of j] jm jj j by simp
              thus "entry ?aA 0 j \<ge> entry ?aA 0 q" using H jjlt eq_qA by simp
            qed
            show "nextrel0 ?aA p q" unfolding nextrel0_def using pq qa lt betw by simp
          qed
          have rhs: "nextrel0 ?aX p q = (\<forall>r. r < qq \<longrightarrow> entry B 0 r \<ge> entry B 0 qq)"
          proof
            assume nr: "nextrel0 ?aX p q"
            show "\<forall>r. r < qq \<longrightarrow> entry B 0 r \<ge> entry B 0 qq"
            proof (intro allI impI)
              fix r assume r: "r < qq"
              have idx: "p < m + r \<and> m + r < q" using pm mpos r qeq by simp
              have "entry ?aX 0 (m + r) \<ge> entry ?aX 0 q" using nr idx by (simp add: nextrel0_def)
              moreover have "entry ?aX 0 (m + r) = entry B 0 r" using eX[of "m + r"] idx by simp
              ultimately show "entry B 0 r \<ge> entry B 0 qq" using eq_qX by simp
            qed
          next
            assume H: "\<forall>r. r < qq \<longrightarrow> entry B 0 r \<ge> entry B 0 qq"
            have ep: "entry ?aX 0 p = m - 1" using eX[of p] psm pm pq by simp
            have lt: "entry ?aX 0 p < entry ?aX 0 q" using ep eq_qX cutqq mpos by simp
            have betw: "\<forall>j. p < j \<and> j < q \<longrightarrow> entry ?aX 0 j \<ge> entry ?aX 0 q"
            proof (intro allI impI)
              fix j assume j: "p < j \<and> j < q"
              have jm: "m \<le> j" using j pm mpos by linarith
              then obtain jj where jj: "j = m + jj" using le_Suc_ex by blast
              have jjlt: "jj < qq" using j jj qeq by simp
              have "entry ?aX 0 j = entry B 0 jj" using eX[of j] jm jj j by simp
              thus "entry ?aX 0 j \<ge> entry ?aX 0 q" using H jjlt eq_qX by simp
            qed
            show "nextrel0 ?aX p q" unfolding nextrel0_def using pq qx lt betw by simp
          qed
          show ?thesis using lhs rhs by simp
        next
          case pne: False
          hence plt2: "p < m - 1" using psm by simp
          have idxm: "p < m - 1 \<and> m - 1 < q" using plt2 qm mpos by simp
          have lhs: "\<not> nextrel0 ?aA p q"
          proof
            assume nr: "nextrel0 ?aA p q"
            have "entry ?aA 0 (m - 1) \<ge> entry ?aA 0 q" using nr idxm by (simp add: nextrel0_def)
            moreover have "entry ?aA 0 (m - 1) = m - 1" using eA[of "m - 1"] mpos qm by simp
            ultimately show False using eq_qA mpos by simp
          qed
          have rhs: "\<not> nextrel0 ?aX p q"
          proof
            assume nr: "nextrel0 ?aX p q"
            have "entry ?aX 0 (m - 1) \<ge> entry ?aX 0 q" using nr idxm by (simp add: nextrel0_def)
            moreover have "entry ?aX 0 (m - 1) = m - 1" using eX[of "m - 1"] mpos qm by simp
            ultimately show False using eq_qX cutqq mpos by simp
          qed
          show ?thesis using lhs rhs by simp
        qed
      next
        case pge: False
        hence pm: "m \<le> p" by simp
        then obtain pp where peq: "p = m + pp" using le_Suc_ex by blast
        have ppqq: "pp < qq" using pq peq qeq by simp
        have lhs: "nextrel0 ?aA p q = nextrel0 B pp qq"
        proof
          assume nr: "nextrel0 ?aA p q"
          have lt: "entry B 0 pp < entry B 0 qq"
            using nr eA[of p] eA[of q] pm peq qge qeq pq by (simp add: nextrel0_def)
          have betw: "\<forall>j. pp < j \<and> j < qq \<longrightarrow> entry B 0 j \<ge> entry B 0 qq"
          proof (intro allI impI)
            fix j assume j: "pp < j \<and> j < qq"
            have idx: "p < m + j \<and> m + j < q" using j peq qeq by simp
            have "entry ?aA 0 (m + j) \<ge> entry ?aA 0 q" using nr idx by (simp add: nextrel0_def)
            thus "entry B 0 j \<ge> entry B 0 qq" using eA[of "m + j"] idx eq_qA by simp
          qed
          show "nextrel0 B pp qq" unfolding nextrel0_def using ppqq qqB lt betw by simp
        next
          assume nr: "nextrel0 B pp qq"
          have lt: "entry ?aA 0 p < entry ?aA 0 q"
            using nr eA[of p] eA[of q] pm peq qge qeq pq by (simp add: nextrel0_def)
          have betw: "\<forall>j. p < j \<and> j < q \<longrightarrow> entry ?aA 0 j \<ge> entry ?aA 0 q"
          proof (intro allI impI)
            fix j assume j: "p < j \<and> j < q"
            have jm: "m \<le> j" using j peq by simp
            then obtain jj where jj: "j = m + jj" using le_Suc_ex by blast
            have jjr: "pp < jj \<and> jj < qq" using j jj peq qeq by simp
            have "entry B 0 jj \<ge> entry B 0 qq" using nr jjr by (simp add: nextrel0_def)
            thus "entry ?aA 0 j \<ge> entry ?aA 0 q" using eA[of j] jm jj j eq_qA by simp
          qed
          show "nextrel0 ?aA p q" unfolding nextrel0_def using pq qa lt betw by simp
        qed
        have rhs: "nextrel0 ?aX p q = nextrel0 B pp qq"
        proof
          assume nr: "nextrel0 ?aX p q"
          have lt: "entry B 0 pp < entry B 0 qq"
            using nr eX[of p] eX[of q] pm peq qge qeq pq by (simp add: nextrel0_def)
          have betw: "\<forall>j. pp < j \<and> j < qq \<longrightarrow> entry B 0 j \<ge> entry B 0 qq"
          proof (intro allI impI)
            fix j assume j: "pp < j \<and> j < qq"
            have idx: "p < m + j \<and> m + j < q" using j peq qeq by simp
            have "entry ?aX 0 (m + j) \<ge> entry ?aX 0 q" using nr idx by (simp add: nextrel0_def)
            thus "entry B 0 j \<ge> entry B 0 qq" using eX[of "m + j"] idx eq_qX by simp
          qed
          show "nextrel0 B pp qq" unfolding nextrel0_def using ppqq qqB lt betw by simp
        next
          assume nr: "nextrel0 B pp qq"
          have lt: "entry ?aX 0 p < entry ?aX 0 q"
            using nr eX[of p] eX[of q] pm peq qge qeq pq by (simp add: nextrel0_def)
          have betw: "\<forall>j. p < j \<and> j < q \<longrightarrow> entry ?aX 0 j \<ge> entry ?aX 0 q"
          proof (intro allI impI)
            fix j assume j: "p < j \<and> j < q"
            have jm: "m \<le> j" using j peq by simp
            then obtain jj where jj: "j = m + jj" using le_Suc_ex by blast
            have jjr: "pp < jj \<and> jj < qq" using j jj peq qeq by simp
            have "entry B 0 jj \<ge> entry B 0 qq" using nr jjr by (simp add: nextrel0_def)
            thus "entry ?aX 0 j \<ge> entry ?aX 0 q" using eX[of j] jm jj j eq_qX by simp
          qed
          show "nextrel0 ?aX p q" unfolding nextrel0_def using pq qx lt betw by simp
        qed
        show ?thesis using lhs rhs by simp
      qed
    qed
  qed
qed

text \<open>m: \<open>congR\<close> for the multi-\<open>IncrFirst\<close> tail bump (row 1 untouched, \<open>nextrel0\<close>
  preserved by @{thm [source] b2_nextrel0_tailbump}).\<close>

lemma b2_congR_tailbump:
  assumes mpos: "0 < m" and cut: "\<And>j. j < Lng B \<Longrightarrow> m \<le> entry B 0 j"
  shows "congR (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) B) (diagSeq 0 (m - 1) @ B)"
  unfolding congR_def
proof (intro conjI allI impI)
  show "Lng (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) B) = Lng (diagSeq 0 (m - 1) @ B)"
    using cdn_Lng_diagfun[OF mpos] b2_Lng_diag_app[OF mpos] by simp
next
  show "nextrel0 (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) B) = nextrel0 (diagSeq 0 (m - 1) @ B)"
    by (rule b2_nextrel0_tailbump[OF mpos cut])
next
  fix j assume jX: "j < Lng (diagSeq 0 (m - 1) @ B)"
  have Lx: "Lng (diagSeq 0 (m - 1) @ B) = m + Lng B" by (rule b2_Lng_diag_app[OF mpos])
  show "entry (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) B) 1 j = entry (diagSeq 0 (m - 1) @ B) 1 j"
  proof (cases "j < m")
    case True
    hence "j \<le> m - 1" using mpos by simp
    thus ?thesis by (simp add: entry_diagSeq_append_lo)
  next
    case False
    hence jm: "m \<le> j" by simp
    then obtain jj where jj: "j = m + jj" using le_Suc_ex by blast
    have jjB: "jj < Lng B" using jX Lx jj by simp
    have je: "j = Suc (m - 1) + jj" using jm mpos jj by simp
    have lhs: "entry (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) B) 1 j = entry B 1 jj"
    proof -
      have "entry (diagSeq 0 (m - 1) @ (IncrFirst ^^ m) B) 1 j = entry ((IncrFirst ^^ m) B) 1 jj"
        using je entry_diagSeq_append_hi[of jj "(IncrFirst ^^ m) B" "m - 1" 1] jjB by simp
      thus ?thesis using entry_funpow_IncrFirst1[OF jjB] by simp
    qed
    have rhs: "entry (diagSeq 0 (m - 1) @ B) 1 j = entry B 1 jj"
      using je entry_diagSeq_append_hi[of jj B "m - 1" 1] jjB by simp
    show ?thesis using lhs rhs by simp
  qed
qed

text \<open>m: in the \<open>m\<^sub>1\<^sub>0 > 0\<close> productive branch, \<open>Red M\<close> is exactly the right slice
  of \<open>N = Red (coreReduce M)\<close> from the diagonal anchor \<open>m\<^sub>1\<^sub>0\<close> (the rebase is the
  identity because \<open>N\<^bsub>0,m\<^sub>1\<^sub>0\<^esub> = N\<^bsub>1,m\<^sub>1\<^sub>0\<^esub> = m\<^sub>1\<^sub>0\<close> and the slice row 0 is \<open>\<ge> m\<^sub>1\<^sub>0\<close>).\<close>

lemma b2_RedM_eq_segN:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "Red M = seg (Red (coreReduce M)) (entry M 1 0) (Lng (Red (coreReduce M)) - 1)"
proof -
  let ?m = "entry M 1 0"
  let ?B = "diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
  let ?N = "Red ?B"
  let ?jN = "Lng ?N - 1"
  have crM: "coreReduce M = ?B" by (rule coreReduce_m10pos_form[OF pos])
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have nc: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" using pos by simp
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have MPT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  \<comment> \<open>geometry.\<close>
  have LN: "Lng ?N = Lng M + ?m" by (rule m_6_5_monoT_Red_fact1_Lng[OF MT pos])
  have m10le: "?m \<le> ?jN" using LN LMpos by linarith
  have segPT: "seg ?N ?m ?jN \<in> PT_PS" using m_6_5_monoT_Red_m10pos[OF MPT pos] by simp
  have thenC: "?m \<le> ?jN \<and> seg ?N ?m ?jN \<in> PT_PS" using m10le segPT by simp
  \<comment> \<open>productive form.\<close>
  have rM: "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m + entry ?N 1 ?m, entry ?N 1 j))
                       [?m..<Suc ?jN]"
    using Red.psimps[OF domM] nz nmu nc pos thenC by (simp add: Let_def)
  \<comment> \<open>anchor values: entry N 0 m = m, entry N 1 m = m, so the rebase shift cancels.\<close>
  have anc0: "entry ?N 0 ?m = ?m" using redB_prefix_diag[OF MT mono pos, rule_format, of 0 ?m] by simp
  have anc1: "entry ?N 1 ?m = ?m" using redB_prefix_diag[OF MT mono pos, rule_format, of 1 ?m] by simp
  \<comment> \<open>strict above anchor: entry N 0 j \<ge> m for m \<le> j \<le> jN.\<close>
  have above: "\<And>j. ?m < j \<Longrightarrow> j \<le> ?jN \<Longrightarrow> ?m < entry ?N 0 j"
  proof -
    fix j assume a: "?m < j" and b: "j \<le> ?jN"
    have jlt: "j < Lng ?N" using b LN LMpos by linarith
    show "?m < entry ?N 0 j"
      using redB_row0_strict_above_anchor[OF MT mono pos, rule_format, of j] a jlt by simp
  qed
  \<comment> \<open>the map equals seg N m jN.\<close>
  have seqeq: "Red M = seg ?N ?m ?jN"
  proof (rule nth_equalityI)
    have Lmap: "Lng (Red M) = Suc ?jN - ?m" using rM by (simp add: length_upt del: upt_Suc)
    have Lseg: "Lng (seg ?N ?m ?jN) = Suc ?jN - ?m" by (simp only: Lng_seg)
    show "length (Red M) = length (seg ?N ?m ?jN)" using Lmap Lseg by simp
    fix p assume p: "p < length (Red M)"
    have plen: "p < Suc ?jN - ?m" using p rM by (simp add: length_upt del: upt_Suc)
    have idx: "[?m..<Suc ?jN] ! p = ?m + p" using plen by (simp add: nth_upt del: upt_Suc)
    have pmlt: "?m + p < Suc ?jN" using plen by simp
    have pmle: "?m + p \<le> ?jN" using pmlt by simp
    have plenmap: "p < length [?m..<Suc ?jN]" using plen by (simp add: length_upt del: upt_Suc)
    have row0ge: "?m \<le> entry ?N 0 (?m + p)"
    proof (cases "p = 0")
      case True thus ?thesis using anc0 by simp
    next
      case False
      hence "?m < ?m + p" by simp
      thus ?thesis using above[of "?m + p"] pmle by simp
    qed
    have step_nth: "Red M ! p
        = (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m + entry ?N 1 ?m, entry ?N 1 j)) ([?m..<Suc ?jN] ! p)"
      by (subst rM) (rule nth_map[OF plenmap])
    have "Red M ! p = (entry ?N 0 (?m + p) - entry ?N 0 ?m + entry ?N 1 ?m, entry ?N 1 (?m + p))"
      using step_nth idx by simp
    also have "\<dots> = (entry ?N 0 (?m + p), entry ?N 1 (?m + p))"
      using anc0 anc1 row0ge by simp
    also have "\<dots> = seg ?N ?m ?jN ! p"
    proof -
      have pseg: "p < Lng (seg ?N ?m ?jN)" using plen by (simp only: Lng_seg)
      have e0: "fst (seg ?N ?m ?jN ! p) = entry ?N 0 (?m + p)"
        using entry_seg[OF pseg, of 0] by (simp add: entry_def)
      have e1: "snd (seg ?N ?m ?jN ! p) = entry ?N 1 (?m + p)"
        using entry_seg[OF pseg, of 1] by (simp add: entry_def)
      show ?thesis using e0 e1 by (simp add: prod_eq_iff)
    qed
    finally show "Red M ! p = seg ?N ?m ?jN ! p" .
  qed
  show ?thesis using seqeq crM by simp
qed

text \<open>m: \<open>N = Red (coreReduce M)\<close> splits as its diagonal prefix \<open>diagSeq 0 (m\<^sub>1\<^sub>0-1)\<close>
  followed by \<open>Red M\<close> (its tail slice).  Uses @{thm [source] redB_prefix_diag}
  (prefix is the diagonal) and @{thm [source] b2_RedM_eq_segN} (tail is \<open>Red M\<close>).\<close>

lemma b2_N_eq_diag_RedM:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "Red (coreReduce M) = diagSeq 0 (entry M 1 0 - 1) @ Red M"
proof -
  let ?m = "entry M 1 0"
  let ?N = "Red (coreReduce M)"
  let ?jN = "Lng ?N - 1"
  have crM: "coreReduce M = diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
    by (rule coreReduce_m10pos_form[OF pos])
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have LN: "Lng ?N = Lng M + ?m"
    using m_6_5_monoT_Red_fact1_Lng[OF MT pos] crM by simp
  have mlt: "?m < Lng ?N" using LN LMpos by linarith
  have RMeq: "Red M = seg ?N ?m ?jN" by (rule b2_RedM_eq_segN[OF MT mono pos])
  \<comment> \<open>prefix: take m N = diagSeq 0 (m-1).\<close>
  have prefdiag: "\<And>i j. (i = 0 \<or> i = 1) \<and> j \<le> ?m \<Longrightarrow> entry ?N i j = j"
    using redB_prefix_diag[OF MT mono pos, rule_format] crM by simp
  have takeeq: "take ?m ?N = diagSeq 0 (?m - 1)"
  proof (rule nth_equalityI)
    have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
    show "length (take ?m ?N) = length (diagSeq 0 (?m - 1))"
      using mlt Ld by simp
    fix p assume p: "p < length (take ?m ?N)"
    have pm: "p < ?m" using p mlt by simp
    have ple: "p \<le> ?m" using pm by simp
    have pN: "p < Lng ?N" using pm mlt by simp
    have "take ?m ?N ! p = ?N ! p" using pm by simp
    also have "\<dots> = (entry ?N 0 p, entry ?N 1 p)" by (simp add: entry_def)
    also have "\<dots> = (p, p)" using prefdiag[of 0 p] prefdiag[of 1 p] ple by simp
    also have "\<dots> = diagSeq 0 (?m - 1) ! p"
    proof -
      have pb: "p < Suc (?m - 1) - 0" using pm pos by simp
      have "diagSeq 0 (?m - 1) ! p = (0 + p, 0 + p)" by (rule diagSeq_nth[OF pb])
      thus ?thesis by simp
    qed
    finally show "take ?m ?N ! p = diagSeq 0 (?m - 1) ! p" .
  qed
  \<comment> \<open>tail: drop m N = seg N m jN = Red M.\<close>
  have LNpos: "0 < Lng ?N" using mlt by linarith
  have dropeq: "drop ?m ?N = seg ?N ?m ?jN"
    by (rule seg_to_last_eq_drop[OF LNpos, symmetric])
  have "?N = take ?m ?N @ drop ?m ?N" by simp
  also have "\<dots> = diagSeq 0 (?m - 1) @ seg ?N ?m ?jN" using takeeq dropeq by simp
  also have "\<dots> = diagSeq 0 (?m - 1) @ Red M" using RMeq by simp
  finally show ?thesis .
qed

text \<open>m (B2 keystone, \<open>m\<^sub>1\<^sub>0 > 0\<close>): the idempotency \<open>Red.pinduct\<close> residual.
  \<open>coreReduce (Red M)\<close> is the \<open>+m\<^sub>1\<^sub>0\<close> tail-bump of \<open>N = Red (coreReduce M)\<close>
  (= \<open>diagSeq 0 (m\<^sub>1\<^sub>0-1) @ Red M\<close>), hence \<open>congR\<close> to \<open>N\<close> (@{thm [source]
  b2_congR_tailbump}); so by the master-key @{thm [source] cdn_red_cong},
  \<open>Red (coreReduce (Red M)) = Red N\<close>, which the supplied idempotency IH on
  \<open>coreReduce M\<close> collapses to \<open>N = Red (coreReduce M)\<close>.\<close>

lemma b2_idem_m10pos:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
    and IH: "Red (Red (coreReduce M)) = Red (coreReduce M)"
  shows "Red (coreReduce (Red M)) = Red (coreReduce M)"
proof -
  let ?m = "entry M 1 0"
  let ?N = "Red (coreReduce M)"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  \<comment> \<open>Red M is in T_PS and has the same row-1 left end m10 > 0.\<close>
  have LRM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  have RMne: "Red M \<noteq> []" using LRM LMpos by (cases "Red M") auto
  have RMT: "Red M \<in> T_PS" using RMne by (simp add: T_PS_def)
  have RMm10: "entry (Red M) 1 0 = ?m" by (rule m_6_6_Red_leftend_1[OF MT])
  have RMpos: "0 < entry (Red M) 1 0" using RMm10 pos by simp
  \<comment> \<open>coreReduce (Red M) in m10>0 form.\<close>
  have crRM: "coreReduce (Red M) = diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) (Red M)"
    using coreReduce_m10pos_form[OF RMpos] RMm10 by simp
  \<comment> \<open>N = diagSeq prefix @ Red M.\<close>
  have Neq: "?N = diagSeq 0 (?m - 1) @ Red M" by (rule b2_N_eq_diag_RedM[OF MT mono pos])
  \<comment> \<open>cut condition: row 0 of Red M is \<ge> m10.\<close>
  have RMrow0: "Red M = seg ?N ?m (Lng ?N - 1)" by (rule b2_RedM_eq_segN[OF MT mono pos])
  have anc0: "entry ?N 0 ?m = ?m"
    using redB_prefix_diag[OF MT mono pos, rule_format, of 0 ?m]
          coreReduce_m10pos_form[OF pos] by simp
  have LN: "Lng ?N = Lng M + ?m"
    using m_6_5_monoT_Red_fact1_Lng[OF MT pos] coreReduce_m10pos_form[OF pos] by simp
  have mlt: "?m < Lng ?N" using LN LMpos by linarith
  have cut: "\<And>j. j < Lng (Red M) \<Longrightarrow> ?m \<le> entry (Red M) 0 j"
  proof -
    fix j assume j: "j < Lng (Red M)"
    have jseg: "j < Lng (seg ?N ?m (Lng ?N - 1))" using j RMrow0 by simp
    have "j < Suc (Lng ?N - 1) - ?m" using jseg by (simp only: Lng_seg)
    hence jN: "?m + j < Lng ?N" using mlt by simp
    have ej: "entry (Red M) 0 j = entry ?N 0 (?m + j)" using RMrow0 entry_seg[OF jseg] by simp
    show "?m \<le> entry (Red M) 0 j"
    proof (cases "j = 0")
      case True thus ?thesis using ej anc0 by simp
    next
      case False
      hence mj: "?m < ?m + j" by simp
      have "?m < entry (Red (diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M)) 0 (?m + j)"
        using redB_row0_strict_above_anchor[OF MT mono pos, rule_format, of "?m + j"]
              mj jN coreReduce_m10pos_form[OF pos] by simp
      hence "?m < entry ?N 0 (?m + j)" using coreReduce_m10pos_form[OF pos] by simp
      thus ?thesis using ej by simp
    qed
  qed
  \<comment> \<open>congR: coreReduce (Red M) ~ N.\<close>
  have RcongN: "congR (coreReduce (Red M)) ?N"
    using b2_congR_tailbump[OF pos cut] crRM Neq by simp
  have funpow_ne: "(IncrFirst ^^ ?m) (Red M) \<noteq> []"
    using RMne by (metis Lng_funpow_IncrFirst length_0_conv)
  have crRMT: "coreReduce (Red M) \<in> T_PS"
    using funpow_ne by (simp add: T_PS_def crRM)
  \<comment> \<open>master-key congruence + the idempotency IH.\<close>
  have "Red (coreReduce (Red M)) = Red ?N" by (rule cdn_red_cong[OF RcongN crRMT])
  also have "\<dots> = ?N" using IH by simp
  finally show ?thesis .
qed


(* ===== final-layer block from workflow fl-s ===== *)

subsection \<open>§6.6 final layer (S): \<open>Red\<close>-output structure on the core-nontrunk branch\<close>

text \<open>m: For a core-nontrunk \<open>M\<close> (\<open>monoT\<close>, \<open>M\<^bsub>0,0\<^esub> = M\<^bsub>1,0\<^esub> = 0\<close>, \<open>TrMax M \<noteq> Lng M - 1\<close>),
  the row-1 parent \<open>npJ M 0 - 1\<close> of the first node \<open>FirstNodes M ! 0 = TrMax M + 1\<close>
  lies strictly below \<open>TrMax M\<close>, so \<open>npJ M 0 \<le> TrMax M\<close>.

  The clean argument: \<open>FirstNodes M ! 0 = TrMax M + 1\<close> (since \<open>IdxSum (Br M) ! 0 = 0\<close>);
  if the branch head row-1 is \<open>0\<close> then \<open>npJ M 0 = 0 \<le> TrMax M\<close>; otherwise the unique
  row-1 parent \<open>p\<^sub>1\<close> of \<open>TrMax M + 1\<close> satisfies \<open>p\<^sub>1 < TrMax M + 1\<close>, and \<open>p\<^sub>1 = TrMax M\<close>
  would give \<open>nextR M 1 (TrMax M) (TrMax M + 1)\<close>, contradicting @{thm [source] TrMax_stop}.
  Hence \<open>p\<^sub>1 < TrMax M\<close> and \<open>npJ M 0 = Suc p\<^sub>1 \<le> TrMax M\<close>.
  Empirically TRUE 1865/1865 (rank\<le>4, core-nontrunk), \<open>npJ M 0 = TrMax M + 1\<close> never.\<close>

lemma s_FirstNode0_eq_TrMax_Suc:
  assumes M: "M \<in> PT_PS" and brne: "Br M \<noteq> []"
  shows "FirstNodes M ! 0 = TrMax M + 1"
proof -
  have JBr: "0 < length (Br M)" using brne by (cases "Br M") auto
  have "IdxSum (Br M) ! 0 = 0" by (simp add: idxsum_nth[where J=0])
  thus ?thesis using FirstNodes_nth[OF JBr] by simp
qed

lemma s_npJ0_le_TrMax:
  assumes M: "M \<in> PT_PS" and core1: "entry M 1 0 = 0" and brne: "Br M \<noteq> []"
  shows "npJ M 0 \<le> TrMax M"
proof (cases "entry (Br M ! 0) 1 0 = 0")
  case True
  thus ?thesis by (simp add: npJ_def)
next
  case nzbr: False
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have monoM: "monoT M" using M by (simp add: PT_PS_def)
  have JBr: "0 < Lng (Br M)" using brne by (cases "Br M") auto
  let ?f = "FirstNodes M ! 0"
  have fnEq: "?f = TrMax M + 1" by (rule s_FirstNode0_eq_TrMax_Suc[OF M brne])
  \<comment> \<open>\<open>TrMax M \<noteq> Lng M - 1\<close> because there is a branch.\<close>
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with brne show False by simp
  qed
  with tb have trlt: "TrMax M < Lng M - 1" by linarith
  \<comment> \<open>structure of the first node, mirroring @{thm [source] npJ_le_Joints_Suc}.\<close>
  have fnTr: "Joints M ! 0 \<le> TrMax M \<and> TrMax M < ?f"
    by (rule m_6_4_FirstNodes_TrMax_Joints[OF M JBr])
  have nxJ: "nextR M 0 (Joints M ! 0) ?f" by (rule Joints_parent_nextR[OF M JBr])
  have fL: "?f < Lng M" using nxJ by (simp add: nextR_def nextrel0_def)
  have fpos: "0 < ?f" using fnTr by linarith
  have eBf1: "entry M 1 ?f = entry (Br M ! 0) 1 0"
    by (rule entry_FirstNodes_eq_component_gen[OF M JBr])
  have f1pos: "0 < entry M 1 ?f" using eBf1 nzbr by simp
  have e10_lt: "entry M 1 0 < entry M 1 ?f" using core1 f1pos by simp
  have le00f: "leR M 0 0 ?f"
  proof -
    have root: "leR M 0 0 (Lng M - 1)" using monoM by (simp add: monoT_def)
    have fle: "?f \<le> Lng M - 1" using fL by simp
    show ?thesis by (rule m_5_1_ancestor_tree_1[OF MT root _ fle]) simp
  qed
  obtain p1 where p1: "0 \<le> p1" "p1 < ?f" "nextR M 1 p1 ?f"
    using m_5_1_parent_exists_2[OF MT fpos fL e10_lt le00f] by blast
  have ex1: "\<exists>!j. nextR M 1 j ?f"
    using p1(3) nextR1_unique by blast
  have the_p1: "(THE j. nextR M 1 j ?f) = p1"
    using p1(3) by (rule the1_equality[OF ex1])
  have np: "npJ M 0 = Suc p1" using nzbr the_p1 by (simp add: npJ_def)
  \<comment> \<open>\<open>p\<^sub>1 \<le> TrMax M\<close> from \<open>p\<^sub>1 < ?f = TrMax M + 1\<close>; and \<open>p\<^sub>1 \<noteq> TrMax M\<close> by \<open>TrMax_stop\<close>.\<close>
  have p1_le: "p1 \<le> TrMax M" using p1(2) fnEq by simp
  have p1_ne: "p1 \<noteq> TrMax M"
  proof
    assume eq: "p1 = TrMax M"
    have "nextR M 1 (TrMax M) (TrMax M + 1)" using p1(3) eq fnEq by simp
    moreover have "\<not> nextR M 1 (TrMax M) (TrMax M + 1)" by (rule TrMax_stop[OF MT trlt])
    ultimately show False by simp
  qed
  have "p1 < TrMax M" using p1_le p1_ne by linarith
  thus ?thesis using np by simp
qed

text \<open>m: \<S>6.6 final layer (S) — keystone \<open>TrMax (Red M) = TrMax M\<close> on core-nontrunk.

  \<open>Red M = diagSeq 0 (TrMax M) @ rest\<close> with \<open>rest = concat (branch blocks)\<close>.  The
  trunk of the output coincides with that of \<open>M\<close> by @{thm [source] TrMax_eqI}:
  \<^item> \<^bold>\<open>below\<close>: for \<open>j' < TrMax M\<close> both \<open>j'\<close>, \<open>j'+1\<close> sit on the diagonal prefix, so
    the consecutive step is a \<open>nextR _ 1\<close> edge (@{thm [source] nextR1_consecutive}).
  \<^item> \<^bold>\<open>stop\<close>: at the junction \<open>entry (Red M) 1 (TrMax M) = TrMax M\<close> but
    \<open>entry (Red M) 1 (TrMax M + 1) = npJ M 0 \<le> TrMax M\<close> (@{thm [source] s_npJ0_le_TrMax}
    via row-1 leftend invariance of the bumped \<open>Red (N\<^sub>0)\<close>), so the row-1 value does
    not strictly increase and the trunk stops.
  Empirically TRUE 22601/22601 (rank\<le>5 core-nontrunk).\<close>

lemma fl_s_TrMax_Red:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  shows "TrMax (Red M) = TrMax M"
proof -
  have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  let ?t = "TrMax M"
  \<comment> \<open>there is a branch.\<close>
  have tb: "?t \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  with tne have trlt: "?t < Lng M - 1" by linarith
  have brne: "Br M \<noteq> []"
  proof -
    have "Br M = P (seg M (?t + 1) (Lng M - 1))" using tne by (simp add: Br_def)
    thus ?thesis using P_nonempty by simp
  qed
  have JBr: "0 < Lng (Br M)" using brne by (cases "Br M") auto
  \<comment> \<open>unfold \<open>Red M\<close> in the core-nontrunk branch.\<close>
  define f where "f = (\<lambda>J.
        (IncrFirst ^^ (Joints M ! J + 1
            - (if entry (Br M ! J) 1 0 = 0 then 0
               else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
          (Red ((entry M 0 0 + Joints M ! J + 1,
                 entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                        else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                # tl (Br M ! J))))"
  have rM: "Red M = diagSeq 0 ?t @ concat (map f [0..<Lng (Br M)])"
    using Red.psimps[OF dom] nz nmu c0 c1 tne unfolding f_def by (simp add: Let_def)
  \<comment> \<open>the first block, identified with \<open>(IncrFirst ^^ e\<^sub>0) (Red (NJ M 0))\<close>.\<close>
  have f0: "f 0 = (IncrFirst ^^ (Joints M ! 0 + 1 - npJ M 0)) (Red (NJ M 0))"
    unfolding f_def NJ_def npJ_def using c0 c1 by simp
  have blk0_ne: "Red (NJ M 0) \<noteq> []"
  proof -
    have brJne: "Br M ! 0 \<noteq> []" by (rule Br_component_nonempty[OF M_PT JBr])
    have "NJ M 0 \<noteq> []" by (simp add: NJ_def)
    hence "NJ M 0 \<in> T_PS" by (simp add: T_PS_def)
    hence "Lng (Red (NJ M 0)) = Lng (NJ M 0)" by (rule m_6_5_Lng_Red)
    moreover have "0 < Lng (NJ M 0)" by (simp add: NJ_def)
    ultimately show ?thesis by (cases "Red (NJ M 0)") auto
  qed
  \<comment> \<open>\<open>rest = concat blocks\<close>; split off block 0 so its head is exposed.\<close>
  let ?rest = "concat (map f [0..<Lng (Br M)])"
  have blk0f_ne: "f 0 \<noteq> []"
  proof -
    have "Lng (f 0) = Lng (Red (NJ M 0))" using f0 by simp
    thus ?thesis using blk0_ne by (cases "f 0") auto
  qed
  have rest_split: "?rest = f 0 @ concat (map f [1..<Lng (Br M)])"
  proof -
    have "[0..<Lng (Br M)] = 0 # [1..<Lng (Br M)]"
      using JBr by (simp add: upt_rec)
    thus ?thesis by simp
  qed
  have rest_ne: "?rest \<noteq> []" using rest_split blk0f_ne by simp
  \<comment> \<open>length of the diagonal prefix is \<open>Suc ?t\<close>.\<close>
  have lenD: "Lng (diagSeq 0 ?t) = Suc ?t" by (simp del: upt_Suc)
  \<comment> \<open>the junction row-1 value of \<open>Red M\<close> is \<open>npJ M 0\<close>, which is \<open>\<le> ?t\<close>.\<close>
  have e_junc1: "entry (Red M) 1 (?t + 1) = npJ M 0"
  proof -
    have "entry (Red M) 1 (?t + 1) = entry ?rest 1 0"
      using rM by (simp add: entry_diagSeq_append_junction)
    also have "\<dots> = entry (f 0) 1 0"
      using rest_split blk0f_ne by (simp add: entry_def nth_append)
    also have "\<dots> = entry (Red (NJ M 0)) 1 0"
    proof -
      have L0: "0 < Lng (Red (NJ M 0))" using blk0_ne by (cases "Red (NJ M 0)") auto
      show ?thesis using f0 entry_funpow_IncrFirst1[OF L0] by simp
    qed
    also have "\<dots> = entry (NJ M 0) 1 0"
      by (rule m_6_6_Red_leftend_1) (simp add: NJ_def T_PS_def)
    also have "\<dots> = entry M 1 0 + npJ M 0" by (rule entry_NJ_1_0)
    also have "\<dots> = npJ M 0" using c1 by simp
    finally show ?thesis .
  qed
  have np_le: "npJ M 0 \<le> ?t" by (rule s_npJ0_le_TrMax[OF M_PT c1 brne])
  \<comment> \<open>now pin \<open>TrMax\<close> by @{thm [source] TrMax_eqI}.\<close>
  have RMne: "Red M \<noteq> []"
  proof -
    have "Lng (Red M) = Suc ?t + Lng (concat (map f [0..<Lng (Br M)]))"
      using rM lenD by simp
    thus ?thesis by (cases "Red M") auto
  qed
  have RMT: "Red M \<in> T_PS" using RMne by (simp add: T_PS_def)
  show ?thesis
  proof (rule TrMax_eqI[OF RMT])
    fix j' assume j': "j' < ?t"
    \<comment> \<open>below: diagonal-prefix consecutive step.\<close>
    have jj: "Suc j' \<le> ?t" using j' by simp
    have L: "Suc j' < Lng (Red M)"
    proof -
      have "Suc ?t \<le> Lng (Red M)" using rM lenD by simp
      thus ?thesis using jj by linarith
    qed
    have jle: "j' \<le> ?t" using j' by simp
    have e0j:  "entry (Red M) 0 j' = j'"
      using rM entry_diagSeq_append_lo[OF jle] by simp
    have e0sj: "entry (Red M) 0 (Suc j') = Suc j'"
      using rM entry_diagSeq_append_lo[OF jj] by simp
    have e1j:  "entry (Red M) 1 j' = j'"
      using rM entry_diagSeq_append_lo[OF jle] by simp
    have e1sj: "entry (Red M) 1 (Suc j') = Suc j'"
      using rM entry_diagSeq_append_lo[OF jj] by simp
    show "nextR (Red M) 1 j' (j' + 1)"
      using nextR1_consecutive[OF L] e0j e0sj e1j e1sj by simp
  next
    \<comment> \<open>stop: row-1 does not strictly increase at the junction.\<close>
    show "\<not> nextR (Red M) 1 ?t (?t + 1)"
    proof
      assume step: "nextR (Red M) 1 ?t (?t + 1)"
      have "entry (Red M) 1 ?t < entry (Red M) 1 (?t + 1)"
        using step by (simp add: nextR_def nextrel1_def)
      moreover have "entry (Red M) 1 ?t = ?t"
      proof -
        have "entry (diagSeq 0 ?t @ concat (map f [0..<Lng (Br M)])) 1 ?t = ?t"
          by (rule entry_diagSeq_append_lo[OF order.refl])
        thus ?thesis using rM by simp
      qed
      ultimately have "?t < npJ M 0" using e_junc1 by simp
      thus False using np_le by linarith
    qed
  qed
qed


(* ===== final-layer block from workflow fl-d ===== *)
subsection \<open>D (idempotency domain): reusable core-nontrunk \<open>Red\<close> unfold (\<open>NJ\<close> form)\<close>

text \<open>m (final layer, B1 prep): the core-nontrunk \<open>Red\<close> equation written in the
  abstracted \<open>NJ\<close>/\<open>npJ\<close> form.  This is the same equation reproduced inline at
  many use-sites (e.g. \<open>m_6_5_Lng_Red\<close>'s non-trunk case, line ~6694); banking it
  once makes the B1 (core-nontrunk idempotency) re-decomposition a short rewrite.
  Empirically the recursive arguments \<open>NJ M J\<close> are exactly the \<open>tl (Br M ! J)\<close>
  branch heads rebased by \<open>(Joints M ! J + 1, npJ M J)\<close>, and they are
  \<^emph>\<open>non-multi\<close> (@{thm [source] NJ_nonmulti}) so the idempotency \<open>Red.pinduct\<close>
  IH on the \<open>\<not> multiT\<close> domain D applies to each of them.\<close>

lemma d_Red_core_nontrunk_unfold:
  assumes MT: "M \<in> T_PS" and nz: "\<not> zeroT M" and nmu: "\<not> multiT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  shows "Red M = diagSeq 0 (TrMax M)
           @ concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                  (Red (NJ M J)))
                     [0..<Lng (Br M)])"
proof -
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have rM: "Red M = diagSeq 0 (TrMax M) @
        concat (map (\<lambda>J.
            (IncrFirst ^^ (Joints M ! J + 1
                - (if entry (Br M ! J) 1 0 = 0 then 0
                   else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
              (Red ((entry M 0 0 + Joints M ! J + 1,
                     entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                            else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                    # tl (Br M ! J))))
          [0..<Lng (Br M)])"
    using Red.psimps[OF dom] nz nmu c0 c1 tne by (simp add: Let_def)
  have blk_eq: "(\<lambda>J.
            (IncrFirst ^^ (Joints M ! J + 1
                - (if entry (Br M ! J) 1 0 = 0 then 0
                   else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
              (Red ((entry M 0 0 + Joints M ! J + 1,
                     entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                            else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                    # tl (Br M ! J))))
        = (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))"
  proof (rule ext)
    fix J
    have npE: "(if entry (Br M ! J) 1 0 = 0 then 0
                else Suc (THE j. nextR M 1 j (FirstNodes M ! J))) = npJ M J"
      by (simp add: npJ_def)
    have argE: "((entry M 0 0 + Joints M ! J + 1, entry M 1 0 + npJ M J)
                 # tl (Br M ! J)) = NJ M J"
      by (simp add: NJ_def)
    show "(IncrFirst ^^ (Joints M ! J + 1
              - (if entry (Br M ! J) 1 0 = 0 then 0
                 else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
            (Red ((entry M 0 0 + Joints M ! J + 1,
                   entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                          else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                  # tl (Br M ! J)))
        = (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))"
      by (simp only: npE argE)
  qed
  show ?thesis using rM by (simp only: blk_eq)
qed


(* ===== final-layer block: idempotency re-decomposition (fin) ===== *)

text \<open>fin: the row-0 left end of \<open>Red M\<close> equals \<open>M\<^bsub>1,0\<^esub>\<close> for \<open>monoT M\<close>.  Branch-by-branch
  on the @{const Red} recursion: core (trunk/non-trunk) gives \<open>0 = m\<^sub>1\<^sub>0\<close>; the
  \<open>m\<^sub>1\<^sub>0 = 0\<close> shift recurses onto \<open>shiftRow0 M\<close> (core); the \<open>m\<^sub>1\<^sub>0 > 0\<close> branch is the
  productive rebase whose left end is \<open>entry N 1 m\<^sub>1\<^sub>0 = m\<^sub>1\<^sub>0\<close> (@{thm [source]
  redB_row1_anchor}, the \<open>then_case\<close> is forced by @{thm [source] m_6_5_monoT_Red_m10pos}).
  Empirically TRUE 10220/10220 (monoT, rank\<le>4).\<close>

lemma fin_Red_leftend_row0_eq_m10:
  assumes MT: "M \<in> T_PS" and monoM: "monoT M"
  shows "entry (Red M) 0 0 = entry M 1 0"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have "M \<in> T_PS \<longrightarrow> monoT M \<longrightarrow> entry (Red M) 0 0 = entry M 1 0"
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
      show "entry (Red M) 0 0 = entry M 1 0"
      proof (cases "?m00 = 0 \<and> ?m10 = 0")
        case core: True
        hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
        have e0: "entry (Red M) 0 0 = 0"
        proof (cases "?j1' = ?j1")
          case True
          have rM: "Red M = diagSeq ?m10 (?m10 + ?j1)"
            using Red.psimps[OF dom] nz nmu c0 c1 True by (simp add: Let_def)
          have "entry (Red M) 0 0 = ?m10 + 0"
            using rM entry_diagSeq[where a="?m10" and b="?m10 + ?j1" and j=0 and i=0]
            by (simp add: LMpos)
          thus ?thesis using c1 by simp
        next
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
          also have "\<dots> = 0" by (rule entry_diagSeq_append_lo) simp
          finally show ?thesis .
        qed
        show ?thesis using e0 c1 by simp
      next
        case nc: False
        show ?thesis
        proof (cases "?m10 = 0")
          case True
          let ?shift = "map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc ?j1]"
          have rM: "Red M = Red ?shift"
            using Red.psimps[OF dom] nz nmu nc True by (simp add: Let_def)
          have shift_eq: "?shift = shiftRow0 M"
            using LMpos by (simp add: shiftRow0_def)
          have shift_T: "?shift \<in> T_PS" by (simp add: T_PS_def)
          have shift_mono: "monoT ?shift"
            using monoT_shiftRow0[OF MT' mono] shift_eq by simp
          have IH': "entry (Red ?shift) 0 0 = entry ?shift 1 0"
            using IH_nc3[OF nz nmu refl refl refl refl nc True] shift_T shift_mono by blast
          have e1sh: "entry ?shift 1 0 = ?m10" using LMpos by (simp add: entry_def)
          show ?thesis using IH' rM e1sh by simp
        next
          case False
          hence c1p: "0 < ?m10" by simp
          have Mpt: "M \<in> PT_PS" using MT' mono by (simp add: PT_PS_def)
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
          \<comment> \<open>the productive branch is forced for monoT M (segment is PT_PS).\<close>
          have segPT: "seg ?N ?m10 ?jN \<in> PT_PS"
            using m_6_5_monoT_Red_m10pos[OF Mpt c1p] by simp
          have LN: "Lng ?N = Lng M + ?m10"
            using m_6_5_monoT_Red_fact1_Lng[OF MT' c1p]
                  coreReduce_m10pos_form[OF c1p] by simp
          have m10le: "?m10 \<le> ?jN" using LN LMpos by linarith
          have then_cond: "?m10 \<le> ?jN \<and> seg ?N ?m10 ?jN \<in> PT_PS"
            using m10le segPT by simp
          have rM': "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                        entry ?N 1 j))
                                 [?m10..<Suc ?jN]"
            using rM then_cond by (simp add: Let_def del: upt_Suc)
          have idx0: "[?m10..<Suc ?jN] ! 0 = ?m10"
            using m10le by (simp add: nth_upt del: upt_Suc)
          have len0: "0 < length [?m10..<Suc ?jN]" using m10le by (simp del: upt_Suc)
          have e_rM0: "entry (Red M) 0 0
                        = entry ?N 0 ?m10 - entry ?N 0 ?m10 + entry ?N 1 ?m10"
          proof -
            have "(Red M) ! 0 = (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                      entry ?N 1 j)) ?m10"
              using rM' len0 idx0 by (simp add: nth_map del: upt_Suc)
            thus ?thesis unfolding entry_def by simp
          qed
          \<comment> \<open>row-1 anchor value: entry N 1 m10 = m10.\<close>
          have e1val: "entry ?N 1 ?m10 = ?m10"
            using redB_row1_anchor[OF MT' mono c1p]
                  coreReduce_m10pos_form[OF c1p] by simp
          show ?thesis using e_rM0 e1val by simp
        qed
      qed
    qed
  qed
  thus ?thesis using MT monoM by blast
qed

text \<open>fin: the row-0 left end of \<open>Red (NJ M J)\<close> equals \<open>npJ M J\<close>, for a core-nontrunk
  \<open>M\<close>.  Since \<open>NJ M J\<close> is non-multi (@{thm [source] NJ_nonmulti}); if it is monoT
  apply @{thm [source] fin_Red_leftend_row0_eq_m10} (its \<open>m\<^sub>1\<^sub>0 = npJ M J\<close> by
  @{thm [source] entry_NJ_1_0}); if it is zeroT (singleton with \<open>npJ = 0\<close>) then
  \<open>Red (NJ M J) = [(0,0)]\<close>, leftend \<open>0 = npJ\<close>.\<close>

lemma fin_Red_NJ_leftend:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
  shows "entry (Red (NJ M J)) 0 0 = npJ M J"
proof -
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
  have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
  have nm: "\<not> multiT (NJ M J)" by (rule NJ_nonmulti[OF M c0 c1 JBr])
  have e1: "entry (NJ M J) 1 0 = npJ M J" using entry_NJ_1_0[of M J] c1 by simp
  show ?thesis
  proof (cases "zeroT (NJ M J)")
    case True
    have domNJ: "Red_dom (NJ M J)" by (rule m_6_5_Red_welldef[OF NJT])
    have "Red (NJ M J) = [(0,0)]" using Red.psimps[OF domNJ] True by simp
    moreover have "npJ M J = 0" using True e1 by (simp add: zeroT_def)
    ultimately show ?thesis by (simp add: entry_def)
  next
    case False
    have mono: "monoT (NJ M J)" using nm False by (simp add: multiT_def)
    have "entry (Red (NJ M J)) 0 0 = entry (NJ M J) 1 0"
      by (rule fin_Red_leftend_row0_eq_m10[OF NJT mono])
    thus ?thesis using e1 by simp
  qed
qed

text \<open>fin: the row-0 head of the core-nontrunk branch block
  \<open>B\<^sub>J = IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red (N\<^sub>J M J))\<close> (\<open>e\<^sub>J = Joints M ! J + 1 - npJ M J\<close>) equals
  \<open>Joints M ! J + 1\<close>.  Indeed \<open>IncrFirst\<close> bumps row 0 by \<open>e\<^sub>J\<close> and the inner left end
  is \<open>npJ M J\<close> (@{thm [source] fin_Red_NJ_leftend}); with \<open>npJ \<le> Joints+1\<close>
  (@{thm [source] npJ_le_Joints_Suc}) the sum \<open>npJ + e\<^sub>J = Joints M ! J + 1\<close>.\<close>

lemma fin_block_head:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
  shows "entry ((IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))) 0 0
         = Joints M ! J + 1"
proof -
  have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
  have L0: "0 < Lng (Red (NJ M J))"
  proof -
    have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
    have "Lng (Red (NJ M J)) = Lng (NJ M J)" by (rule m_6_5_Lng_Red[OF NJT])
    moreover have "0 < Lng (NJ M J)" by (simp add: NJ_def)
    ultimately show ?thesis by simp
  qed
  have e0: "entry ((IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))) 0 0
            = entry (Red (NJ M J)) 0 0 + (Joints M ! J + 1 - npJ M J)"
    by (rule entry_funpow_IncrFirst0[OF L0])
  have inner: "entry (Red (NJ M J)) 0 0 = npJ M J"
    by (rule fin_Red_NJ_leftend[OF M c0 c1 JBr])
  have le: "npJ M J \<le> Joints M ! J + 1" by (rule npJ_le_Joints_Suc[OF M c1 JBr])
  show ?thesis using e0 inner le by simp
qed

(* ===== keystone: Red preserves monoT (forward direction of p_6_5_Red_monoT) ===== *)

text \<open>rmt: tail row-0 positivity for a mono core-nontrunk \<open>M\<close>.  Every branch-tail
  index \<open>j > TrMax M\<close> of \<open>Red M = diagSeq 0 (TrMax M) @ concat (branch blocks)\<close>
  reads a row-0 value \<open>\<ge> Joints M ! J + 1 \<ge> 1 > 0\<close>.  Adapts the non-trunk arm of
  @{thm [source] redB_tail_row0_above_anchor}, anchoring at the row-0 left end
  \<open>0\<close> (instead of \<open>m\<^sub>1\<^sub>0\<close>).\<close>

lemma rmt_core_nontrunk_tail_pos:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  shows "\<forall>j. TrMax M < j \<longrightarrow> j < Lng (Red M) \<longrightarrow> 0 < entry (Red M) 0 j"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have mono: "monoT M" using M by (simp add: PT_PS_def)
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  let ?t = "TrMax M"
  let ?blk = "\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))"
  let ?Q = "map ?blk [0..<Lng (Br M)]"
  have rB: "Red M = diagSeq 0 ?t @ concat ?Q"
    by (rule d_Red_core_nontrunk_unfold[OF MT nz nmu c0 c1 tne])
  have Lblk: "\<And>J. J < Lng (Br M) \<Longrightarrow> Lng (?blk J) = Lng (Br M ! J)"
  proof -
    fix J assume J: "J < Lng (Br M)"
    have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M J])
    have NJTl: "NJ M J \<in> T_PS" using brJne by (simp add: NJ_def T_PS_def)
    have step1: "Lng (?blk J) = Lng (Red (NJ M J))" by (simp only: Lng_funpow_IncrFirst)
    have step2: "Lng (Red (NJ M J)) = Lng (NJ M J)" by (rule m_6_5_Lng_Red[OF NJTl])
    have step3: "Lng (NJ M J) = Lng (Br M ! J)" using brJne by (rule Lng_NJ)
    show "Lng (?blk J) = Lng (Br M ! J)" using step1 step2 step3 by simp
  qed
  have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  have lendiag: "length (diagSeq 0 ?t) = Suc ?t" by (simp add: diagSeq_def)
  have Ltail: "Lng (concat ?Q) = Lng M - Suc ?t"
  proof -
    have "Lng (Red M) = length (diagSeq 0 ?t) + Lng (concat ?Q)" by (simp add: rB)
    thus ?thesis using LrM lendiag by simp
  qed
  have lenQ: "length ?Q = Lng (Br M)" by simp
  have idx_total: "IdxSum ?Q ! (length ?Q) = Lng (concat ?Q)"
  proof -
    have "IdxSum ?Q ! (length ?Q) = sum_list (map length (take (length ?Q) ?Q))"
      by (simp add: idxsum_nth)
    also have "\<dots> = sum_list (map length ?Q)" by simp
    also have "\<dots> = length (concat ?Q)" by (simp add: length_concat)
    finally show ?thesis .
  qed
  show ?thesis
  proof (intro allI impI)
    fix j assume tj: "?t < j" and jL: "j < Lng (Red M)"
    let ?jp = "j - Suc ?t"
    have jge: "Suc ?t \<le> j" using tj by simp
    have jpL: "?jp < Lng (concat ?Q)" using jL LrM Ltail jge by linarith
    have e_split: "entry (Red M) 0 j = entry (concat ?Q) 0 ?jp"
    proof -
      have "(Red M) ! j = (diagSeq 0 ?t @ concat ?Q) ! j" by (simp add: rB)
      also have "\<dots> = concat ?Q ! (j - length (diagSeq 0 ?t))"
        using jge lendiag by (simp add: nth_append)
      also have "\<dots> = concat ?Q ! ?jp" using lendiag by simp
      finally show ?thesis by (simp add: entry_def)
    qed
    have jp_tot: "?jp < IdxSum ?Q ! (length ?Q)" using jpL idx_total by simp
    obtain J where J: "J < length ?Q" "IdxSum ?Q ! J \<le> ?jp"
                     "?jp < IdxSum ?Q ! (J + 1)"
      using idxsum_locate[OF jp_tot] by blast
    have JBr: "J < Lng (Br M)" using J(1) lenQ by simp
    let ?loc = "?jp - IdxSum ?Q ! J"
    have QJ_blk: "?Q ! J = ?blk J"
      using nth_map_upt[where f="?blk" and m=0 and n="Lng (Br M)" and i=J] JBr by simp
    have blkJ_len: "length (?Q ! J) = Lng (Br M ! J)"
      using QJ_blk Lblk[OF JBr] by simp
    have idxdiff: "IdxSum ?Q ! (J + 1) = IdxSum ?Q ! J + length (?Q ! J)"
      using J(1) by (rule idxsum_diff)
    have loc_lt: "?loc < length (?Q ! J)" using J(2,3) idxdiff by linarith
    have sJ: "sum_list (map length (take J ?Q)) = IdxSum ?Q ! J"
      using J(1) by (simp add: idxsum_nth less_imp_le_nat)
    have jp_decomp: "?jp = IdxSum ?Q ! J + ?loc" using J(2) by simp
    have e_block: "entry (concat ?Q) 0 ?jp = entry (?Q ! J) 0 ?loc"
    proof -
      have "concat ?Q ! ?jp = concat ?Q ! (sum_list (map length (take J ?Q)) + ?loc)"
        using sJ jp_decomp by simp
      also have "\<dots> = (?Q ! J) ! ?loc"
        by (rule nth_concat_block[OF J(1) loc_lt])
      finally show ?thesis by (simp add: entry_def)
    qed
    let ?eJ = "Joints M ! J + 1 - npJ M J"
    have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
    have NJT: "NJ M J \<in> T_PS" using brJne by (simp add: NJ_def T_PS_def)
    have LredNJ: "Lng (Red (NJ M J)) = Lng (NJ M J)" by (rule m_6_5_Lng_Red[OF NJT])
    have loc_ltN: "?loc < Lng (Red (NJ M J))"
    proof -
      have "?loc < Lng (Br M ! J)" using loc_lt blkJ_len by simp
      also have "\<dots> = Lng (NJ M J)" using brJne by (simp add: Lng_NJ)
      also have "\<dots> = Lng (Red (NJ M J))" using LredNJ by simp
      finally show ?thesis .
    qed
    have e_QJ: "entry (?Q ! J) 0 ?loc = entry (Red (NJ M J)) 0 ?loc + ?eJ"
    proof -
      have "entry (?Q ! J) 0 ?loc = entry ((IncrFirst ^^ ?eJ) (Red (NJ M J))) 0 ?loc"
        using QJ_blk by simp
      also have "\<dots> = entry (Red (NJ M J)) 0 ?loc + ?eJ"
        by (rule entry_funpow_IncrFirst0[OF loc_ltN])
      finally show ?thesis .
    qed
    \<comment> \<open>Leftend lower bound: \<open>entry (Red (NJ M J)) 0 ?loc \<ge> npJ M J\<close>.\<close>
    have NJzm: "zeroT (NJ M J) \<or> monoT (NJ M J)"
      using NJ_nonmulti[OF M c0 c1 JBr] by (simp add: multiT_def)
    have lm_NJ: "entry (Red (NJ M J)) 0 0 \<le> entry (Red (NJ M J)) 0 ?loc"
    proof (cases "zeroT (NJ M J)")
      case True
      have "Lng (Red (NJ M J)) = 1" using LredNJ True by (simp add: zeroT_def)
      hence "?loc = 0" using loc_ltN by simp
      thus ?thesis by simp
    next
      case False
      hence "monoT (NJ M J)" using NJzm by simp
      from m_6_5_Red_leftend_row0_min[OF NJT this] loc_ltN show ?thesis by blast
    qed
    have inner: "entry (Red (NJ M J)) 0 0 = npJ M J"
      by (rule fin_Red_NJ_leftend[OF M c0 c1 JBr])
    have leftend_ge: "npJ M J \<le> entry (Red (NJ M J)) 0 ?loc" using inner lm_NJ by simp
    have eRBj: "entry (Red M) 0 j = entry (Red (NJ M J)) 0 ?loc + ?eJ"
      using e_split e_block e_QJ by simp
    have nat_id: "Joints M ! J + 1 \<le> ?eJ + npJ M J" by simp
    have "Joints M ! J + 1 \<le> entry (Red (NJ M J)) 0 ?loc + ?eJ"
      using leftend_ge nat_id by linarith
    hence "Joints M ! J + 1 \<le> entry (Red M) 0 j" using eRBj by simp
    thus "0 < entry (Red M) 0 j" by linarith
  qed
qed

text \<open>rmt: strict row-0 suffix-minimum for a mono core-nontrunk \<open>M\<close>: the row-0
  left end is \<open>0\<close> and every later index reads a strictly larger row-0 value
  (trunk diagonal reads \<open>j > 0\<close>; branch tail \<open>\<ge> Joints+1 > 0\<close> via
  @{thm [source] rmt_core_nontrunk_tail_pos}).\<close>

lemma rmt_core_nontrunk_strict_suffix_min:
  assumes M: "M \<in> PT_PS" and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  shows "\<forall>j. 0 < j \<longrightarrow> j < Lng (Red M) \<longrightarrow> 0 < entry (Red M) 0 j"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have mono: "monoT M" using M by (simp add: PT_PS_def)
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  let ?t = "TrMax M"
  let ?blk = "\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))"
  let ?Q = "map ?blk [0..<Lng (Br M)]"
  have rB: "Red M = diagSeq 0 ?t @ concat ?Q"
    by (rule d_Red_core_nontrunk_unfold[OF MT nz nmu c0 c1 tne])
  have tail_pos: "\<forall>j. ?t < j \<longrightarrow> j < Lng (Red M) \<longrightarrow> 0 < entry (Red M) 0 j"
    by (rule rmt_core_nontrunk_tail_pos[OF M c0 c1 tne])
  show ?thesis
  proof (intro allI impI)
    fix j assume jpos: "0 < j" and jL: "j < Lng (Red M)"
    show "0 < entry (Red M) 0 j"
    proof (cases "j \<le> ?t")
      case True
      have "entry (diagSeq 0 ?t @ concat ?Q) 0 j = j"
        by (rule entry_diagSeq_append_lo[OF True])
      hence "entry (Red M) 0 j = j" using rB by simp
      thus ?thesis using jpos by simp
    next
      case False
      hence "?t < j" by simp
      thus ?thesis using tail_pos jL by blast
    qed
  qed
qed

end

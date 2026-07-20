theory Frontier_6_066
  imports Support_6_045
begin

text \<open>The \<open>IncrFirst\<close> relation between the slice and its rebase (content.md 1244):
  \<open>seg M j'\<^sub>0 j'\<^sub>1 = IncrFirst\<^bsup>M\<^bsub>0,j'\<^sub>0\<^esub>-M\<^bsub>1,j'\<^sub>0\<^esub>\<^esup>(N')\<close>.  Holds whenever, on the
  slice, \<open>M\<^bsub>1,j'\<^sub>0\<^esub> \<le> M\<^bsub>0,j'\<^sub>0\<^esub> \<le> M\<^bsub>0,j'\<^sub>0+k\<^esub>\<close> (condAB_coeff (2) + slice row-0
  monotonicity).  This is the bridge that makes \<open>N'\<close>'s reduced/nextrel structure
  inherit from the slice via \<open>Red\<close>'s \<open>IncrFirst\<close>-invariance.  Pure entrywise.\<close>

lemma seg_eq_IncrFirst_rebaseNp:
  assumes jord: "j0' \<le> j1'"
    and c2: "entry M 1 j0' \<le> entry M 0 j0'"
    and mono: "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
  shows "seg M j0' j1' = (IncrFirst ^^ (entry M 0 j0' - entry M 1 j0')) (rebaseNp M j0' j1')"
proof (rule nth_equalityI)
  let ?d = "entry M 0 j0' - entry M 1 j0'"
  let ?R = "(IncrFirst ^^ ?d) (rebaseNp M j0' j1')"
  show Llen: "length (seg M j0' j1') = length ?R"
    using Lng_seg[of M j0' j1'] Lng_rebaseNp[of M j0' j1'] jord by simp
next
  let ?d = "entry M 0 j0' - entry M 1 j0'"
  let ?R = "(IncrFirst ^^ (entry M 0 j0' - entry M 1 j0')) (rebaseNp M j0' j1')"
  fix k assume "k < length (seg M j0' j1')"
  hence kL: "k < Suc (j1' - j0')" using Lng_seg[of M j0' j1'] jord by simp
  have kLseg: "k < Lng (seg M j0' j1')" using kL jord by simp
  have kLR: "k < Lng (rebaseNp M j0' j1')" using kL by simp
  \<comment> \<open>Row 0.\<close>
  have s0: "entry (seg M j0' j1') 0 k = entry M 0 (j0' + k)"
    by (rule entry_seg[OF kLseg])
  have r0: "entry ?R 0 k = entry (rebaseNp M j0' j1') 0 k + ?d"
    using kLR by (rule entry_funpow_IncrFirst0)
  have rb0: "entry (rebaseNp M j0' j1') 0 k
               = entry M 0 (j0' + k) - entry M 0 j0' + entry M 1 j0'"
    by (rule entry_rebaseNp(1)[OF kL])
  have monk: "entry M 0 j0' \<le> entry M 0 (j0' + k)" using mono kL by simp
  have R0: "entry ?R 0 k = entry M 0 (j0' + k)"
    using r0 rb0 c2 monk by simp
  \<comment> \<open>Row 1.\<close>
  have s1: "entry (seg M j0' j1') 1 k = entry M 1 (j0' + k)"
    by (rule entry_seg[OF kLseg])
  have r1: "entry ?R 1 k = entry (rebaseNp M j0' j1') 1 k"
    using kLR by (rule entry_funpow_IncrFirst1)
  have rb1: "entry (rebaseNp M j0' j1') 1 k = entry M 1 (j0' + k)"
    by (rule entry_rebaseNp(2)[OF kL])
  have R1: "entry ?R 1 k = entry M 1 (j0' + k)" using r1 rb1 by simp
  \<comment> \<open>Combine into pair equality.\<close>
  have "seg M j0' j1' ! k = (entry (seg M j0' j1') 0 k, entry (seg M j0' j1') 1 k)"
    by (simp add: entry_def)
  also have "\<dots> = (entry M 0 (j0' + k), entry M 1 (j0' + k))" using s0 s1 by simp
  also have "\<dots> = (entry ?R 0 k, entry ?R 1 k)" using R0 R1 by simp
  also have "\<dots> = ?R ! k" by (simp add: entry_def)
  finally show "seg M j0' j1' ! k = ?R ! k" .
qed


text \<open>\<S>6.6 condA_m10pos JUNCTION bricks (Front A, tag pss-cAm10).

  Goal: \<open>condA_m10pos\<close> — \<open>RedCondA M\<close> for a reduced \<open>monoT M\<close> with \<open>m\<^sub>1\<^sub>0 > 0\<close>.
  Route (NON-circular, cites only GREEN facts): set \<open>N = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ M\<close>;
  \<open>N\<close> is reduced \<open>monoT\<close> with core \<open>(0,0)\<close> (@{thm [source] m_6_6_reduced_leftend} at \<open>u=0\<close>),
  so \<open>RedCondA N\<close> (@{thm [source] kst_reduced_imp_condAB_monoT_core}).  Each genuine
  row-\<open>i\<close> parent of \<open>M\<close> at column \<open>j\<^sub>1 \<ge> 1\<close> transfers to the column \<open>m\<^sub>1\<^sub>0+j\<^sub>1\<close> of
  \<open>N\<close> shifted by \<open>m\<^sub>1\<^sub>0\<close>, with entries unshifted; \<open>RedCondA N\<close> there gives \<open>RedCondA M\<close>.

  Here the prefix length is \<open>m\<^sub>1\<^sub>0 = Suc (m\<^sub>1\<^sub>0 - 1)\<close>, so the GREEN \<open>diagSeq 0 k @ rest\<close>
  bricks apply with \<open>k = m\<^sub>1\<^sub>0 - 1\<close>.  Empirically TRUE: 44 reduced \<open>monoT m\<^sub>1\<^sub>0>0\<close>
  sequences (vals \<le> 3, len \<le> 3), 0 condA failures, 0 transfer/parent-structure
  failures (python/, this worktree).\<close>

text \<open>Brick A (entry transfer): \<open>entry N i (m\<^sub>1\<^sub>0 + j) = entry M i j\<close> for \<open>j < Lng M\<close>.
  The \<open>M\<close>-region of \<open>N\<close> is read literally (values UNSHIFTED) by
  @{thm [source] entry_diagSeq_append_hi} with \<open>k = m\<^sub>1\<^sub>0 - 1\<close> (\<open>Suc k = m\<^sub>1\<^sub>0\<close>).\<close>

lemma cAm10_entry_transfer:
  assumes m10pos: "0 < m10" and jL: "j < Lng M"
  shows "entry (diagSeq 0 (m10 - 1) @ M) i (m10 + j) = entry M i j"
proof -
  have suc: "Suc (m10 - 1) = m10" using m10pos by simp
  have "entry (diagSeq 0 (m10 - 1) @ M) i (Suc (m10 - 1) + j) = entry M i j"
    by (rule entry_diagSeq_append_hi[OF jL])
  thus ?thesis using suc by simp
qed

lemma cAm10_entry_junction:
  assumes m10pos: "0 < m10"
  shows "entry (diagSeq 0 (m10 - 1) @ M) i m10 = entry M i 0"
proof -
  have suc: "Suc (m10 - 1) = m10" using m10pos by simp
  have "entry (diagSeq 0 (m10 - 1) @ M) i (Suc (m10 - 1)) = entry M i 0"
    using entry_diagSeq_append_junction[of "m10 - 1" M i] by simp
  thus ?thesis using suc by simp
qed

text \<open>Brick B (row-0 \<open>nextrel0\<close> shift): for \<open>j0,j1 < Lng M\<close>, the row-0 \<open>nextR\<close> edge
  in the \<open>M\<close>-region of \<open>N\<close> is exactly the \<open>M\<close>-edge.  The open interval
  \<open>(m\<^sub>1\<^sub>0+j0, m\<^sub>1\<^sub>0+j1)\<close> lies entirely in the \<open>M\<close>-region (\<open>> m\<^sub>1\<^sub>0\<close>), so the
  "no-smaller-intermediate" guard restricts to \<open>M\<close>.\<close>

lemma cAm10_nextrel0_shift:
  assumes m10pos: "0 < m10" and j0L: "j0 < Lng M" and j1L: "j1 < Lng M"
  shows "nextrel0 (diagSeq 0 (m10 - 1) @ M) (m10 + j0) (m10 + j1)
           \<longleftrightarrow> nextrel0 M j0 j1"
proof -
  let ?N = "diagSeq 0 (m10 - 1) @ M"
  have suc: "Suc (m10 - 1) = m10" using m10pos by simp
  have LN: "Lng ?N = m10 + Lng M" using suc by simp
  have e0: "\<And>j. j < Lng M \<Longrightarrow> entry ?N 0 (m10 + j) = entry M 0 j"
    using m10pos by (rule cAm10_entry_transfer)
  show ?thesis
  proof
    assume H: "nextrel0 ?N (m10 + j0) (m10 + j1)"
    have lt: "m10 + j0 < m10 + j1" using H by (simp add: nextrel0_def)
    have j0j1: "j0 < j1" using lt by simp
    have eval: "entry M 0 j0 < entry M 0 j1"
      using H e0[OF j0L] e0[OF j1L] by (simp add: nextrel0_def)
    have noint: "\<forall>j. j0 < j \<and> j < j1 \<longrightarrow> entry M 0 j \<ge> entry M 0 j1"
    proof (intro allI impI)
      fix j assume a: "j0 < j \<and> j < j1"
      have jL: "j < Lng M" using a j1L by simp
      have rng: "m10 + j0 < m10 + j \<and> m10 + j < m10 + j1" using a by simp
      have "entry ?N 0 (m10 + j) \<ge> entry ?N 0 (m10 + j1)"
        using H rng by (simp add: nextrel0_def)
      thus "entry M 0 j \<ge> entry M 0 j1" using e0[OF jL] e0[OF j1L] by simp
    qed
    show "nextrel0 M j0 j1"
      unfolding nextrel0_def using j0L j1L j0j1 eval noint by simp
  next
    assume H: "nextrel0 M j0 j1"
    have j0j1: "j0 < j1" using H by (simp add: nextrel0_def)
    have ltN: "m10 + j0 < m10 + j1" using j0j1 by simp
    have bN1: "m10 + j1 < Lng ?N" using j1L LN by simp
    have bN0: "m10 + j0 < Lng ?N" using ltN bN1 by simp
    have eval: "entry ?N 0 (m10 + j0) < entry ?N 0 (m10 + j1)"
      using H e0[OF j0L] e0[OF j1L] by (simp add: nextrel0_def)
    have noint: "\<forall>j. m10 + j0 < j \<and> j < m10 + j1 \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 (m10 + j1)"
    proof (intro allI impI)
      fix j assume a: "m10 + j0 < j \<and> j < m10 + j1"
      have jge: "m10 \<le> j" using a by simp
      obtain j' where jeq: "j = m10 + j'" using jge le_Suc_ex by blast
      have aj': "j0 < j' \<and> j' < j1" using a jeq by simp
      have j'L: "j' < Lng M" using aj' j1L by simp
      have "entry M 0 j' \<ge> entry M 0 j1" using H aj' by (simp add: nextrel0_def)
      thus "entry ?N 0 j \<ge> entry ?N 0 (m10 + j1)"
        using jeq e0[OF j'L] e0[OF j1L] by simp
    qed
    show "nextrel0 ?N (m10 + j0) (m10 + j1)"
      unfolding nextrel0_def using ltN bN0 bN1 eval noint by simp
  qed
qed

text \<open>Brick C (le0 shift, \<open>M \<rightarrow> N\<close>): a row-0 \<open>M\<close>-chain lifts to the \<open>M\<close>-region
  of \<open>N\<close> (shifted by \<open>m\<^sub>1\<^sub>0\<close>); each \<open>M\<close>-edge lifts by @{thm [source] cAm10_nextrel0_shift}.\<close>

lemma cAm10_nextrel0_rtrancl_M_to_N:
  assumes m10pos: "0 < m10" and ch: "(nextrel0 M)\<^sup>*\<^sup>* a b" and bL: "b < Lng M"
  shows "(nextrel0 (diagSeq 0 (m10 - 1) @ M))\<^sup>*\<^sup>* (m10 + a) (m10 + b)"
  using ch bL
proof (induction rule: rtranclp_induct)
  case base show ?case by simp
next
  case (step y z)
  have yz: "y < z" using step.hyps(2) by (simp add: nextrel0_def)
  have zL: "z < Lng M" using step.hyps(2) by (simp add: nextrel0_def)
  have yL: "y < Lng M" using yz zL by simp
  have IHy: "(nextrel0 (diagSeq 0 (m10 - 1) @ M))\<^sup>*\<^sup>* (m10 + a) (m10 + y)"
    using step.IH yL by simp
  have "nextrel0 (diagSeq 0 (m10 - 1) @ M) (m10 + y) (m10 + z)"
    using cAm10_nextrel0_shift[OF m10pos yL zL] step.hyps(2) by simp
  with IHy show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

text \<open>Brick C' (le0 shift, \<open>N \<rightarrow> M\<close>): a row-0 chain in the \<open>M\<close>-region of \<open>N\<close>
  starting at \<open>m\<^sub>1\<^sub>0 + a\<close> stays \<open>\<ge> m\<^sub>1\<^sub>0\<close> (@{thm [source] nextrel0_rtrancl_mono}), so each
  edge descends to an \<open>M\<close>-edge.\<close>

lemma cAm10_nextrel0_rtrancl_N_to_M:
  assumes m10pos: "0 < m10"
    and ch: "(nextrel0 (diagSeq 0 (m10 - 1) @ M))\<^sup>*\<^sup>* (m10 + a) c"
  shows "\<exists>b. c = m10 + b \<and> (nextrel0 M)\<^sup>*\<^sup>* a b"
  using ch
proof (induction rule: rtranclp_induct)
  case base show ?case by (rule exI[of _ a]) simp
next
  case (step y z)
  obtain b where yb: "y = m10 + b" and chMb: "(nextrel0 M)\<^sup>*\<^sup>* a b"
    using step.IH by blast
  let ?N = "diagSeq 0 (m10 - 1) @ M"
  have suc: "Suc (m10 - 1) = m10" using m10pos by simp
  have LN: "Lng ?N = m10 + Lng M" using suc by simp
  have yz: "y < z" using step.hyps(2) by (simp add: nextrel0_def)
  have zLN: "z < Lng ?N" using step.hyps(2) by (simp add: nextrel0_def)
  have zge: "m10 \<le> z" using yb yz by simp
  obtain c' where zc: "z = m10 + c'" using zge le_Suc_ex by blast
  have bL: "b < Lng M" using yb zLN LN yz zc by simp
  have c'L: "c' < Lng M" using zc zLN LN by simp
  have "nextrel0 M b c'"
    using cAm10_nextrel0_shift[OF m10pos bL c'L] step.hyps(2) yb zc by simp
  with chMb have "(nextrel0 M)\<^sup>*\<^sup>* a c'" by (rule rtranclp.rtrancl_into_rtrancl)
  thus ?case using zc by blast
qed

text \<open>Brick C'' (le0 shift, both directions): \<open>le0 N (m\<^sub>1\<^sub>0+j0) (m\<^sub>1\<^sub>0+j1) \<longleftrightarrow> le0 M j0 j1\<close>
  for \<open>j0,j1 < Lng M\<close>.\<close>

lemma cAm10_le0_shift:
  assumes m10pos: "0 < m10" and j0L: "j0 < Lng M" and j1L: "j1 < Lng M"
  shows "le0 (diagSeq 0 (m10 - 1) @ M) (m10 + j0) (m10 + j1) \<longleftrightarrow> le0 M j0 j1"
proof -
  let ?N = "diagSeq 0 (m10 - 1) @ M"
  have suc: "Suc (m10 - 1) = m10" using m10pos by simp
  have LN: "Lng ?N = m10 + Lng M" using suc by simp
  have bN0: "m10 + j0 < Lng ?N" using j0L LN by simp
  have bN1: "m10 + j1 < Lng ?N" using j1L LN by simp
  show ?thesis
  proof
    assume "le0 ?N (m10 + j0) (m10 + j1)"
    hence ch: "(nextrel0 ?N)\<^sup>*\<^sup>* (m10 + j0) (m10 + j1)" by (simp add: le0_def)
    obtain b where beq: "m10 + j1 = m10 + b" and chM: "(nextrel0 M)\<^sup>*\<^sup>* j0 b"
      using cAm10_nextrel0_rtrancl_N_to_M[OF m10pos ch] by blast
    have "b = j1" using beq by simp
    hence "(nextrel0 M)\<^sup>*\<^sup>* j0 j1" using chM by simp
    thus "le0 M j0 j1" using j0L j1L by (simp add: le0_def)
  next
    assume "le0 M j0 j1"
    hence ch: "(nextrel0 M)\<^sup>*\<^sup>* j0 j1" by (simp add: le0_def)
    have "(nextrel0 ?N)\<^sup>*\<^sup>* (m10 + j0) (m10 + j1)"
      by (rule cAm10_nextrel0_rtrancl_M_to_N[OF m10pos ch j1L])
    thus "le0 ?N (m10 + j0) (m10 + j1)" using bN0 bN1 by (simp add: le0_def)
  qed
qed

text \<open>Brick D (row-1 \<open>nextrel1\<close> shift): for \<open>j0,j1 < Lng M\<close>, the row-1 \<open>nextR\<close> edge
  in the \<open>M\<close>-region of \<open>N\<close> is exactly the \<open>M\<close>-edge.  Since \<open>m\<^sub>1\<^sub>0 + j0 \<ge> m\<^sub>1\<^sub>0\<close>, the
  \<open>le0\<close>-reachability universal \<open>m\<^sub>1\<^sub>0+j0 < j \<and> le0 N j (m\<^sub>1\<^sub>0+j1)\<close> only ranges over the
  \<open>M\<close>-region (\<open>j > m\<^sub>1\<^sub>0\<close>), where @{thm [source] cAm10_le0_shift} and
  @{thm [source] cAm10_entry_transfer} reduce it to \<open>M\<close>'s universal.\<close>

lemma cAm10_nextrel1_shift:
  assumes m10pos: "0 < m10" and j0L: "j0 < Lng M" and j1L: "j1 < Lng M"
  shows "nextrel1 (diagSeq 0 (m10 - 1) @ M) (m10 + j0) (m10 + j1)
           \<longleftrightarrow> nextrel1 M j0 j1"
proof -
  let ?N = "diagSeq 0 (m10 - 1) @ M"
  have suc: "Suc (m10 - 1) = m10" using m10pos by simp
  have LN: "Lng ?N = m10 + Lng M" using suc by simp
  have e1: "\<And>j. j < Lng M \<Longrightarrow> entry ?N 1 (m10 + j) = entry M 1 j"
    using m10pos by (rule cAm10_entry_transfer)
  have le0sh: "\<And>x y. x < Lng M \<Longrightarrow> y < Lng M
        \<Longrightarrow> le0 ?N (m10 + x) (m10 + y) = le0 M x y"
    using m10pos by (rule cAm10_le0_shift)
  show ?thesis
  proof
    assume H: "nextrel1 ?N (m10 + j0) (m10 + j1)"
    have lt: "m10 + j0 < m10 + j1" using H by (simp add: nextrel1_def)
    have j0j1: "j0 < j1" using lt by simp
    have eval: "entry M 1 j0 < entry M 1 j1"
      using H e1[OF j0L] e1[OF j1L] by (simp add: nextrel1_def)
    have le0M: "le0 M j0 j1"
      using H le0sh[OF j0L j1L] by (simp add: nextrel1_def)
    have univ: "\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j \<ge> entry M 1 j1"
    proof (intro allI impI)
      fix j assume a: "j0 < j \<and> le0 M j j1"
      have jL: "j < Lng M" using a unfolding le0_def by simp
      have rng: "m10 + j0 < m10 + j" using a by simp
      have leN: "le0 ?N (m10 + j) (m10 + j1)" using a le0sh[OF jL j1L] by simp
      have "entry ?N 1 (m10 + j) \<ge> entry ?N 1 (m10 + j1)"
        using H rng leN by (simp add: nextrel1_def)
      thus "entry M 1 j \<ge> entry M 1 j1" using e1[OF jL] e1[OF j1L] by simp
    qed
    show "nextrel1 M j0 j1"
      unfolding nextrel1_def using j0L j1L j0j1 eval le0M univ by simp
  next
    assume H: "nextrel1 M j0 j1"
    have j0j1: "j0 < j1" using H by (simp add: nextrel1_def)
    have ltN: "m10 + j0 < m10 + j1" using j0j1 by simp
    have bN1: "m10 + j1 < Lng ?N" using j1L LN by simp
    have bN0: "m10 + j0 < Lng ?N" using ltN bN1 by simp
    have eval: "entry ?N 1 (m10 + j0) < entry ?N 1 (m10 + j1)"
      using H e1[OF j0L] e1[OF j1L] by (simp add: nextrel1_def)
    have le0M: "le0 M j0 j1" using H by (simp add: nextrel1_def)
    have le0N: "le0 ?N (m10 + j0) (m10 + j1)" using le0M le0sh[OF j0L j1L] by simp
    have univ: "\<forall>j. m10 + j0 < j \<and> le0 ?N j (m10 + j1) \<longrightarrow> entry ?N 1 j \<ge> entry ?N 1 (m10 + j1)"
    proof (intro allI impI)
      fix j assume a: "m10 + j0 < j \<and> le0 ?N j (m10 + j1)"
      have jge: "m10 \<le> j" using a by simp
      obtain j' where jeq: "j = m10 + j'" using jge le_Suc_ex by blast
      have j'lt: "j0 < j'" using a jeq by simp
      have jLN: "j < Lng ?N" using a unfolding le0_def by simp
      have j'L: "j' < Lng M" using jLN LN jeq by simp
      have leM: "le0 M j' j1" using a jeq le0sh[OF j'L j1L] by simp
      have "entry M 1 j' \<ge> entry M 1 j1" using H j'lt leM by (simp add: nextrel1_def)
      thus "entry ?N 1 j \<ge> entry ?N 1 (m10 + j1)"
        using jeq e1[OF j'L] e1[OF j1L] by simp
    qed
    show "nextrel1 ?N (m10 + j0) (m10 + j1)"
      unfolding nextrel1_def using ltN bN0 bN1 eval le0N univ by simp
  qed
qed

text \<open>Brick E (unified \<open>nextR\<close> shift): \<open>nextR N i (m\<^sub>1\<^sub>0+j0) (m\<^sub>1\<^sub>0+j1) \<longleftrightarrow> nextR M i j0 j1\<close>
  for \<open>i \<le> 1\<close>, \<open>j0,j1 < Lng M\<close>.\<close>

lemma cAm10_nextR_shift:
  assumes m10pos: "0 < m10" and i: "i \<le> 1" and j0L: "j0 < Lng M" and j1L: "j1 < Lng M"
  shows "nextR (diagSeq 0 (m10 - 1) @ M) i (m10 + j0) (m10 + j1)
           \<longleftrightarrow> nextR M i j0 j1"
proof (cases "i = 0")
  case True
  thus ?thesis unfolding nextR_def
    using cAm10_nextrel0_shift[OF m10pos j0L j1L] by simp
next
  case False
  hence "i = 1" using i by simp
  thus ?thesis unfolding nextR_def
    using cAm10_nextrel1_shift[OF m10pos j0L j1L] by simp
qed

text \<open>Brick F (row-0 strict ascent in a \<open>monoT M\<close>): \<open>entry M 0 0 < entry M 0 j1\<close> for
  \<open>0 < j1 < Lng M\<close>.  Convexity (@{thm [source] m_5_1_ancestor_tree_1}) lifts
  \<open>leR M 0 0 (Lng M-1)\<close> to \<open>leR M 0 0 j1\<close>; then @{thm [source] m_5_1_ancestor_basic_1}.
  (Same argument as @{thm [source] kfwd_monoT_hasParent_col}.)\<close>

lemma cAm10_monoT_row0_strict:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and j1pos: "0 < j1" and j1L: "j1 < Lng M"
  shows "entry M 0 0 < entry M 0 j1"
proof -
  have le0top: "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
  have j1le: "j1 \<le> Lng M - 1" using j1L by linarith
  have le0j1: "leR M 0 0 j1"
    by (rule m_5_1_ancestor_tree_1[OF MT le0top zero_le j1le])
  show ?thesis
    by (rule m_5_1_ancestor_basic_1[OF MT j1pos order.refl le0j1])
qed

text \<open>Brick G (JUNCTION parent transfer): for reduced \<open>monoT M\<close> with \<open>m\<^sub>1\<^sub>0 > 0\<close>,
  every genuine row-\<open>i\<close> parent of \<open>M\<close> at an interior column \<open>j\<^sub>1 \<ge> 1\<close> transfers to a
  parent of \<open>N = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ M\<close> shifted by \<open>m\<^sub>1\<^sub>0\<close>:
    \<open>hasParent M i j\<^sub>1 \<Longrightarrow> hasParent N i (m\<^sub>1\<^sub>0+j\<^sub>1) \<and> parent N i (m\<^sub>1\<^sub>0+j\<^sub>1) = m\<^sub>1\<^sub>0 + parent M i j\<^sub>1\<close>.
  Existence: lift the unique \<open>M\<close>-edge (@{thm [source] cAm10_nextR_shift}).  Uniqueness:
  an \<open>N\<close>-parent \<open>q\<close> is either in the \<open>M\<close>-region (\<open>q \<ge> m\<^sub>1\<^sub>0\<close>, descends to \<open>M\<close>'s
  unique parent) or in the diagonal prefix (\<open>q < m\<^sub>1\<^sub>0\<close>), the latter ruled out: for
  row 0 the junction column \<open>m\<^sub>1\<^sub>0\<close> (value \<open>m\<^sub>0\<^sub>0 < entry M 0 j\<^sub>1\<close>) lies strictly
  between, breaking the \<open>nextrel0\<close> guard; for row 1 the genuine shifted parent
  \<open>m\<^sub>1\<^sub>0 + parent M 1 j\<^sub>1\<close> is \<open>le0\<close>-reachable with strictly smaller row-1 value, breaking
  the \<open>nextrel1\<close> reachability-minimality guard.\<close>

lemma cAm10_junction_parent:
  assumes M: "M \<in> RT_PS" and mono: "monoT M" and m10pos: "0 < entry M 1 0"
    and i: "i \<le> 1" and j1pos: "0 < j1" and hp: "hasParent M i j1"
  defines "m10 \<equiv> entry M 1 0"
  defines "N \<equiv> diagSeq 0 (m10 - 1) @ M"
  shows "hasParent N i (m10 + j1) \<and> parent N i (m10 + j1) = m10 + parent M i j1"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have m10p: "0 < m10" using m10pos unfolding m10_def .
  have suc: "Suc (m10 - 1) = m10" using m10p by simp
  have LN: "Lng N = m10 + Lng M" using suc unfolding N_def by simp
  \<comment> \<open>the unique M-parent \<open>p0\<close>.\<close>
  obtain p0 where p0: "nextR M i p0 j1" and uq: "\<And>r. nextR M i r j1 \<Longrightarrow> r = p0"
    using hp unfolding hasParent_def by blast
  have parMeq: "parent M i j1 = p0"
    unfolding parent_def using p0 uq by (blast intro: the1_equality)
  have j1L: "j1 < Lng M" using p0 unfolding nextR_def nextrel0_def nextrel1_def
    by (auto split: if_splits)
  have p0lt: "p0 < j1" using p0 unfolding nextR_def nextrel0_def nextrel1_def
    by (auto split: if_splits)
  have p0L: "p0 < Lng M" using p0lt j1L by simp
  \<comment> \<open>existence in N: lift the M-edge.\<close>
  have edgeN: "nextR N i (m10 + p0) (m10 + j1)"
    unfolding N_def using cAm10_nextR_shift[OF m10p i p0L j1L] p0 by simp
  \<comment> \<open>uniqueness in N.\<close>
  have uniqN: "\<And>q. nextR N i q (m10 + j1) \<Longrightarrow> q = m10 + p0"
  proof -
    fix q assume qe: "nextR N i q (m10 + j1)"
    have qlt: "q < m10 + j1" using qe unfolding nextR_def nextrel0_def nextrel1_def
      by (auto split: if_splits)
    show "q = m10 + p0"
    proof (cases "m10 \<le> q")
      case True
      obtain q' where qeq: "q = m10 + q'" using True le_Suc_ex by blast
      have q'lt: "q' < j1" using qlt qeq by simp
      have q'L: "q' < Lng M" using q'lt j1L by simp
      have "nextR M i q' j1"
        using cAm10_nextR_shift[OF m10p i q'L j1L] qe qeq unfolding N_def by simp
      hence "q' = p0" by (rule uq)
      thus ?thesis using qeq by simp
    next
      case False
      hence qpre: "q < m10" by simp
      \<comment> \<open>prefix index: rule out per row.\<close>
      show ?thesis
      proof (cases "i = 0")
        case True
        \<comment> \<open>row 0: junction column \<open>m10\<close> breaks the guard.\<close>
        have qrel: "nextrel0 N q (m10 + j1)" using qe True unfolding nextR_def by simp
        have qmid: "q < m10" using qpre .
        have midhi: "m10 < m10 + j1" using j1pos by simp
        have qall: "\<forall>j. q < j \<and> j < m10 + j1 \<longrightarrow> entry N 0 j \<ge> entry N 0 (m10 + j1)"
          using qrel unfolding nextrel0_def by blast
        have guard: "entry N 0 m10 \<ge> entry N 0 (m10 + j1)"
          using qall qmid midhi by blast
        have ej: "entry N 0 m10 = entry M 0 0"
          unfolding N_def using m10p by (rule cAm10_entry_junction)
        have ebj: "entry N 0 (m10 + j1) = entry M 0 j1"
          unfolding N_def using m10p j1L by (rule cAm10_entry_transfer)
        have strict: "entry M 0 0 < entry M 0 j1"
          by (rule cAm10_monoT_row0_strict[OF MT mono j1pos j1L])
        show ?thesis using guard ej ebj strict by simp
      next
        case False
        hence i1: "i = 1" using i by simp
        \<comment> \<open>row 1: the genuine shifted parent is le0-reachable with smaller row-1.\<close>
        have qrel: "nextrel1 N q (m10 + j1)" using qe i1 unfolding nextR_def by simp
        have le0Mp: "le0 M p0 j1" using p0 i1 unfolding nextR_def by (simp add: nextrel1_def)
        have le0Np: "le0 N (m10 + p0) (m10 + j1)"
          unfolding N_def using cAm10_le0_shift[OF m10p p0L j1L] le0Mp by simp
        have qlow: "q < m10 + p0" using qpre by simp
        have qall: "\<forall>j. q < j \<and> le0 N j (m10 + j1) \<longrightarrow> entry N 1 j \<ge> entry N 1 (m10 + j1)"
          using qrel unfolding nextrel1_def by blast
        have guard: "entry N 1 (m10 + p0) \<ge> entry N 1 (m10 + j1)"
          using qall qlow le0Np by blast
        have ep0: "entry N 1 (m10 + p0) = entry M 1 p0"
          unfolding N_def using m10p p0L by (rule cAm10_entry_transfer)
        have ebj: "entry N 1 (m10 + j1) = entry M 1 j1"
          unfolding N_def using m10p j1L by (rule cAm10_entry_transfer)
        have strict: "entry M 1 p0 < entry M 1 j1"
          using p0 i1 unfolding nextR_def by (simp add: nextrel1_def)
        show ?thesis using guard ep0 ebj strict by simp
      qed
    qed
  qed
  have hpN: "hasParent N i (m10 + j1)"
    unfolding hasParent_def using edgeN uniqN by blast
  have parNeq: "parent N i (m10 + j1) = m10 + p0"
    unfolding parent_def using edgeN uniqN by (blast intro: the1_equality)
  show ?thesis using hpN parNeq parMeq by simp
qed

text \<open>Brick H (column 0 has no parent): \<open>\<not> hasParent M i 0\<close> — \<open>nextR\<close> needs
  \<open>j0 < j1\<close>, impossible for \<open>j1 = 0\<close>.  So RedCondA's obligation at column 0 is vacuous.\<close>

lemma cAm10_no_parent_col0: "\<not> hasParent M i 0"
proof
  assume "hasParent M i 0"
  then obtain j0 where "nextR M i j0 0" unfolding hasParent_def by blast
  thus False unfolding nextR_def nextrel0_def nextrel1_def by (auto split: if_splits)
qed

text \<open>\<S>6.6 condA_m10pos — KEYSTONE FORWARD residual DISCHARGED.

  \<open>RedCondA M\<close> for a reduced \<open>monoT M\<close> with \<open>m\<^sub>1\<^sub>0 = entry M 1 0 > 0\<close>.  Build
  \<open>N = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ M\<close>; \<open>N\<close> is reduced \<open>monoT\<close> with core \<open>(0,0)\<close>
  (@{thm [source] m_6_6_reduced_leftend}, \<open>u = 0\<close>), so \<open>RedCondA N\<close>
  (@{thm [source] kst_reduced_imp_condAB_monoT_core}).  At each interior column
  \<open>j\<^sub>1 \<ge> 1\<close> with \<open>hasParent M i j\<^sub>1\<close>, the parent transfers (@{thm [source]
  cAm10_junction_parent}) and \<open>RedCondA N\<close> at \<open>m\<^sub>1\<^sub>0 + j\<^sub>1\<close> reads back through the
  unshifted entry transfer (@{thm [source] cAm10_entry_transfer}) to \<open>M\<close>; column 0
  is vacuous (@{thm [source] cAm10_no_parent_col0}).  Cites only GREEN facts — no
  \<open>p_*\<close> stub, no \<open>Red_le\<close>, no self-reference.\<close>

lemma condA_m10pos:
  assumes M: "M \<in> RT_PS" and mono: "monoT M" and m10pos: "0 < entry M 1 0"
  shows "RedCondA M"
  unfolding RedCondA_def
proof (intro allI impI)
  fix i j1 assume i: "i \<le> 1" and hp: "hasParent M i j1"
  let ?m10 = "entry M 1 0"
  let ?N = "diagSeq 0 (?m10 - 1) @ M"
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have MPT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have m10p: "0 < ?m10" using m10pos .
  \<comment> \<open>column 0 is vacuous; interior columns transfer.\<close>
  have j1pos: "0 < j1"
  proof (rule ccontr)
    assume "\<not> 0 < j1" hence "j1 = 0" by simp
    thus False using hp cAm10_no_parent_col0 by simp
  qed
  have j1L: "j1 < Lng M" using hp unfolding hasParent_def nextR_def nextrel0_def nextrel1_def
    by (auto split: if_splits)
  \<comment> \<open>N reduced monoT with core, via the GREEN left-end brick at \<open>u = 0\<close>.\<close>
  have ule: "(0::nat) \<le> ?m10" by simp
  have Nguard: "?N = (if (0::nat) < ?m10 then diagSeq 0 (?m10 - 1) else []) @ M"
    using m10p by simp
  have Nred_mono: "Red ?N = ?N \<and> monoT ?N"
    using m_6_6_reduced_leftend[OF M MPT ule] Nguard by simp
  have Nne: "?N \<noteq> []"
  proof -
    have "M \<noteq> []" using MT by (simp add: T_PS_def)
    thus ?thesis by simp
  qed
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have NRT: "?N \<in> RT_PS" using NT Nred_mono by (simp add: RT_PS_def)
  have NmonoT: "monoT ?N" using Nred_mono by simp
  have eN00: "entry ?N 0 0 = 0" using m10p by (simp add: entry_diagSeq_append_lo)
  have eN10: "entry ?N 1 0 = 0" using m10p by (simp add: entry_diagSeq_append_lo)
  \<comment> \<open>RedCondA N via the GREEN keystone core.\<close>
  have condAN: "RedCondA ?N"
    using kst_reduced_imp_condAB_monoT_core[OF NRT NmonoT eN00 eN10] by simp
  \<comment> \<open>parent transfer at the interior column.\<close>
  have tr: "hasParent ?N i (?m10 + j1) \<and> parent ?N i (?m10 + j1) = ?m10 + parent M i j1"
    using cAm10_junction_parent[OF M mono m10pos i j1pos hp] by simp
  have hpN: "hasParent ?N i (?m10 + j1)" using tr by simp
  have parN: "parent ?N i (?m10 + j1) = ?m10 + parent M i j1" using tr by simp
  \<comment> \<open>RedCondA N at \<open>m10+j1\<close>, read back through the unshifted entry transfer.\<close>
  have parMlt: "parent M i j1 < j1"
  proof -
    obtain p0 where p0: "nextR M i p0 j1" and uq: "\<And>r. nextR M i r j1 \<Longrightarrow> r = p0"
      using hp unfolding hasParent_def by blast
    have "parent M i j1 = p0" unfolding parent_def using p0 uq by (blast intro: the1_equality)
    moreover have "p0 < j1" using p0 unfolding nextR_def nextrel0_def nextrel1_def
      by (auto split: if_splits)
    ultimately show ?thesis by simp
  qed
  have parML: "parent M i j1 < Lng M" using parMlt j1L by simp
  have condAN_at: "entry ?N i (parent ?N i (?m10 + j1)) + 1 = entry ?N i (?m10 + j1)"
    using condAN i hpN unfolding RedCondA_def by blast
  have lhs: "entry ?N i (?m10 + parent M i j1) = entry M i (parent M i j1)"
    using m10p parML by (rule cAm10_entry_transfer)
  have rhs: "entry ?N i (?m10 + j1) = entry M i j1"
    using m10p j1L by (rule cAm10_entry_transfer)
  show "entry M i (parent M i j1) + 1 = entry M i j1"
    using condAN_at parN lhs rhs by simp
qed

text \<open>\<S>6.6 KEYSTONE FORWARD (GENERAL M) — now UNCONDITIONAL.  The residual
  hypothesis \<open>condA_m10pos\<close> of @{thm [source] kst_reduced_imp_condAB_cond} is
  discharged by the GREEN @{thm [source] condA_m10pos} above, so for ANY reduced
  \<open>M\<close> we get \<open>RedCondA M \<and> RedCondB M\<close>.  Cites only GREEN facts (no \<open>p_*\<close> stub, no
  \<open>Red_le\<close>, no self-reference).\<close>

lemma kst_reduced_imp_condAB_uncond:
  assumes M: "M \<in> RT_PS"
  shows "RedCondA M \<and> RedCondB M"
  by (rule kst_reduced_imp_condAB_cond[OF condA_m10pos M])



text \<open>\<S>6.6 KEYSTONE BACKWARD (monoT core) — central bricks (tag pss-wf24-bwd).
  The aux (*) of content.md 1224-1244: for a next-tie PT_PS slice \<open>seg M j'\<^sub>0 j'\<^sub>1\<close>,
  the backward column \<open>N = bwdN M j'\<^sub>0 j'\<^sub>1\<close> is reduced.  Here we bank the two
  central structural pieces: \<open>RedCondB (bwdN ..)\<close> and \<open>RedCondA (bwdN ..)\<close>.\<close>

text \<open>The rebase has left-end row 0 value \<open>M\<^bsub>1,j'\<^sub>0\<^esub>\<close> (the shift cancels at \<open>j=0\<close>).\<close>

lemma entry_rebaseNp00:
  shows "entry (rebaseNp M j0' j1') 0 0 = entry M 1 j0'"
proof -
  have lt: "(0::nat) < Suc (j1' - j0')" by simp
  have "entry (rebaseNp M j0' j1') 0 0
          = entry M 0 (j0' + 0) - entry M 0 j0' + entry M 1 j0'"
    by (rule entry_rebaseNp(1)[OF lt])
  thus ?thesis by simp
qed

text \<open>\<open>bwdN \<in> T_PS\<close> (non-empty): \<open>T_PS = {M. M \<noteq> []}\<close> and \<open>Lng (bwdN ..) \<ge> 1\<close>.\<close>

lemma bwdN_in_T_PS: "bwdN M j0' j1' \<in> T_PS"
proof -
  have "0 < Lng (bwdN M j0' j1')" by (simp add: Lng_bwdN)
  hence "bwdN M j0' j1' \<noteq> []" by auto
  thus ?thesis by (simp add: T_PS_def)
qed

lemma rebaseNp_in_T_PS: "rebaseNp M j0' j1' \<in> T_PS"
  by (simp add: T_PS_def rebaseNp_def)

text \<open>The rebase \<open>N'\<close> is mono whenever the slice is: \<open>seg M j'\<^sub>0 j'\<^sub>1 = IncrFirst\<^bsup>d\<^esup>(N')\<close>
  (@{thm [source] seg_eq_IncrFirst_rebaseNp}) and \<open>monoT\<close> is \<open>IncrFirst\<close>-invariant
  (@{thm [source] monoT_funpow_IncrFirst}).\<close>

lemma monoT_rebaseNp:
  assumes jord: "j0' \<le> j1'"
    and c2: "entry M 1 j0' \<le> entry M 0 j0'"
    and rmono: "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
    and segmono: "monoT (seg M j0' j1')"
  shows "monoT (rebaseNp M j0' j1')"
proof -
  have "seg M j0' j1' = (IncrFirst ^^ (entry M 0 j0' - entry M 1 j0')) (rebaseNp M j0' j1')"
    by (rule seg_eq_IncrFirst_rebaseNp[OF jord c2 rmono])
  hence "monoT ((IncrFirst ^^ (entry M 0 j0' - entry M 1 j0')) (rebaseNp M j0' j1'))"
    using segmono by simp
  thus ?thesis by (simp add: monoT_funpow_IncrFirst)
qed

text \<open>\<open>bwdN\<close> is mono: in the \<open>M\<^bsub>1,j'\<^sub>0\<^esub>=0\<close> case it equals the mono rebase; otherwise the
  diagonal prefix sits strictly below the rebase's row-0 left end \<open>M\<^bsub>1,j'\<^sub>0\<^esub>\<close>, so
  @{thm [source] monoT_diagSeq_append} applies (\<open>diagPre m = diagSeq 0 (m-1)\<close> for \<open>m>0\<close>).\<close>

lemma diagPre_eq_diagSeq:
  assumes "0 < m"
  shows "diagPre m = diagSeq 0 (m - 1)"
  using assms by (simp add: diagPre_def diagSeq_def)

lemma monoT_bwdN:
  assumes jord: "j0' \<le> j1'"
    and c2: "entry M 1 j0' \<le> entry M 0 j0'"
    and rmono: "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
    and segmono: "monoT (seg M j0' j1')"
  shows "monoT (bwdN M j0' j1')"
proof (cases "entry M 1 j0' = 0")
  case True
  have "bwdN M j0' j1' = rebaseNp M j0' j1'" by (rule Lng_bwdN_zero[OF True])
  thus ?thesis using monoT_rebaseNp[OF jord c2 rmono segmono] by simp
next
  case False
  hence pos: "0 < entry M 1 j0'" by simp
  let ?R = "rebaseNp M j0' j1'"
  have Rmono: "monoT ?R" by (rule monoT_rebaseNp[OF jord c2 rmono segmono])
  have Rne: "?R \<noteq> []" by (simp add: rebaseNp_def)
  have RT: "?R \<in> T_PS" by (rule rebaseNp_in_T_PS)
  have R00: "entry ?R 0 0 = entry M 1 j0'" by (rule entry_rebaseNp00)
  have lt: "entry M 1 j0' - 1 < entry ?R 0 0" using pos R00 by simp
  have "monoT (diagSeq 0 (entry M 1 j0' - 1) @ ?R)"
    by (rule monoT_diagSeq_append[OF Rne Rmono RT lt])
  moreover have "diagPre (entry M 1 j0') = diagSeq 0 (entry M 1 j0' - 1)"
    by (rule diagPre_eq_diagSeq[OF pos])
  ultimately show ?thesis by (simp add: bwdN_def)
qed

text \<open>\<open>RedCondB (bwdN ..)\<close>: \<open>bwdN\<close> is a \<open>monoT\<close> sequence with left end \<open>(0,0)\<close>
  (@{thm [source] bwdN_left_end}), so \<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close> and
  @{thm [source] m_6_6_monoT_RedCondB} applies.  Piece (2) of the aux (*).\<close>

lemma RedCondB_bwdN:
  assumes jord: "j0' \<le> j1'"
    and c2: "entry M 1 j0' \<le> entry M 0 j0'"
    and rmono: "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
    and segmono: "monoT (seg M j0' j1')"
  shows "RedCondB (bwdN M j0' j1')"
proof -
  let ?N = "bwdN M j0' j1'"
  have NT: "?N \<in> T_PS" by (rule bwdN_in_T_PS)
  have Nmono: "monoT ?N" by (rule monoT_bwdN[OF jord c2 rmono segmono])
  have le: "entry ?N 0 0 = 0 \<and> entry ?N 1 0 = 0" by (rule bwdN_left_end)
  hence e00: "entry ?N 0 0 = 0" and eq0: "entry ?N 0 0 = entry ?N 1 0" by simp_all
  show ?thesis by (rule m_6_6_monoT_RedCondB[OF NT Nmono e00 eq0])
qed


text \<open>Entry of \<open>bwdN\<close> on the whole diagonal region \<open>k \<le> M\<^bsub>1,j'\<^sub>0\<^esub>\<close>: it is the
  identity \<open>N\<^bsub>i,k\<^esub> = k\<close>.  For \<open>k < m\<close> this is @{thm [source] entry_bwdN_diag}; at the
  junction \<open>k = m\<close> the rebase left end is \<open>(m, m)\<close> too (content.md 1230), so the
  diagonal extends continuously to \<open>k = m\<close>.\<close>

lemma entry_bwdN_diag_le:
  assumes "k \<le> entry M 1 j0'" and i: "i \<le> 1"
  shows "entry (bwdN M j0' j1') i k = k"
proof (cases "k < entry M 1 j0'")
  case True
  thus ?thesis by (rule entry_bwdN_diag)
next
  case False
  hence keq: "k = entry M 1 j0'" using assms by simp
  have ge: "entry M 1 j0' \<le> k" using keq by simp
  have "entry (bwdN M j0' j1') i k = entry (rebaseNp M j0' j1') i (k - entry M 1 j0')"
    by (rule entry_bwdN_rebase[OF ge])
  also have "k - entry M 1 j0' = 0" using keq by simp
  finally have eq: "entry (bwdN M j0' j1') i k = entry (rebaseNp M j0' j1') i 0" by simp
  show ?thesis
  proof (cases "i = 0")
    case True
    have "entry (rebaseNp M j0' j1') 0 0 = entry M 1 j0'" by (rule entry_rebaseNp00)
    thus ?thesis using eq True keq by simp
  next
    case False
    hence i1: "i = 1" using i by simp
    have lt: "(0::nat) < Suc (j1' - j0')" by simp
    have "entry (rebaseNp M j0' j1') 1 0 = entry M 1 (j0' + 0)"
      by (rule entry_rebaseNp(2)[OF lt])
    hence "entry (rebaseNp M j0' j1') 1 0 = entry M 1 j0'" by simp
    thus ?thesis using eq i1 keq by simp
  qed
qed

text \<open>\<open>nextR\<close> in the strict diagonal region of \<open>bwdN\<close> is consecutive: if both
  endpoints satisfy \<open>k\<^sub>1 \<le> M\<^bsub>1,j'\<^sub>0\<^esub>\<close> then \<open>N\<^bsub>k\<^esub> = (k,k)\<close>, so the only
  \<open>nextR\<close>-edges land at \<open>k\<^sub>0 = k\<^sub>1 - 1\<close> (content.md case \<open>k\<^sub>1 \<le> M\<^bsub>1,j'\<^sub>0\<^esub>\<close>).\<close>

lemma RedCondA_bwdN_diag_case:
  assumes nx: "nextR (bwdN M j0' j1') i k0 k1" and i: "i \<le> 1"
    and k1le: "k1 \<le> entry M 1 j0'"
  shows "entry (bwdN M j0' j1') i k0 + 1 = entry (bwdN M j0' j1') i k1"
proof -
  let ?N = "bwdN M j0' j1'"
  have k0lt: "k0 < k1" using nx
    by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
  have k0le: "k0 \<le> entry M 1 j0'" using k0lt k1le by simp
  \<comment> \<open>Both endpoints are on the diagonal: \<open>N\<^bsub>i,k\<^esub> = k\<close>.\<close>
  have ek0: "entry ?N i k0 = k0" by (rule entry_bwdN_diag_le[OF k0le i])
  have ek1: "entry ?N i k1 = k1" by (rule entry_bwdN_diag_le[OF k1le i])
  \<comment> \<open>The \<open>nextR\<close> minimality forces \<open>k0 = k1 - 1\<close>.\<close>
  have "k1 = Suc k0"
  proof (rule ccontr)
    assume "k1 \<noteq> Suc k0"
    hence sk: "Suc k0 < k1" using k0lt by simp
    have mid_le: "Suc k0 \<le> entry M 1 j0'" using sk k1le by simp
    have emid: "entry ?N i (Suc k0) = Suc k0" by (rule entry_bwdN_diag_le[OF mid_le i])
    show False
    proof (cases "i = 0")
      case True
      \<comment> \<open>Row-0 \<open>nextrel0\<close>: the intermediate \<open>Suc k0\<close> has \<open>entry \<ge> entry k1\<close>, i.e. \<open>Suc k0 \<ge> k1\<close>.\<close>
      have "\<forall>j. k0 < j \<and> j < k1 \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 k1"
        using nx True by (simp add: nextR_def nextrel0_def)
      hence "entry ?N 0 (Suc k0) \<ge> entry ?N 0 k1" using sk by simp
      thus False using emid ek1 True sk by simp
    next
      case False
      hence i1: "i = 1" using i by simp
      \<comment> \<open>Row-1 \<open>nextrel1\<close>: need \<open>le0 ?N (Suc k0) k1\<close> to invoke minimality.  On the
         diagonal both \<open>le0\<close> steps are consecutive (@{thm [source] entry_bwdN_diag_le}).\<close>
      have le0junc: "le0 ?N (Suc k0) k1"
      proof -
        have pos: "0 < entry M 1 j0'" using sk k1le by simp
        have eq: "diagPre (entry M 1 j0') = diagSeq 0 (entry M 1 j0' - 1)"
          by (rule diagPre_eq_diagSeq[OF pos])
        have skk1: "Suc k0 \<le> k1" using sk by simp
        have k1k: "k1 \<le> entry M 1 j0' - 1 \<or> k1 = entry M 1 j0'" using k1le by linarith
        thus ?thesis
        proof
          assume "k1 \<le> entry M 1 j0' - 1"
          hence "le0 (diagSeq 0 (entry M 1 j0' - 1) @ rebaseNp M j0' j1') (Suc k0) k1"
            by (rule le0_diagSeq_append_prefix[OF skk1])
          thus ?thesis using eq by (simp add: bwdN_def)
        next
          assume k1m: "k1 = entry M 1 j0'"
          \<comment> \<open>reach \<open>m-1\<close> through the prefix then one junction step to \<open>m\<close>.\<close>
          have skm1: "Suc k0 \<le> entry M 1 j0' - 1" using sk k1m by simp
          have r1: "le0 ?N (Suc k0) (entry M 1 j0' - 1)"
          proof -
            have "le0 (diagSeq 0 (entry M 1 j0' - 1) @ rebaseNp M j0' j1') (Suc k0) (entry M 1 j0' - 1)"
              by (rule le0_diagSeq_append_prefix[OF skm1 order_refl])
            thus ?thesis using eq by (simp add: bwdN_def)
          qed
          \<comment> \<open>junction step \<open>(m-1) \<rightarrow> m\<close>: \<open>nextrel0 ?N (m-1) m\<close> since both diagonal.\<close>
          have step: "nextrel0 ?N (entry M 1 j0' - 1) (entry M 1 j0')"
          proof -
            have Lm1: "entry M 1 j0' - 1 < entry M 1 j0'" using pos by simp
            have e1: "entry ?N 0 (entry M 1 j0' - 1) = entry M 1 j0' - 1"
              by (rule entry_bwdN_diag_le[where i=0]) simp_all
            have e2: "entry ?N 0 (entry M 1 j0') = entry M 1 j0'"
              by (rule entry_bwdN_diag_le[OF order_refl]) simp
            have lt2: "entry M 1 j0' < Lng ?N" using Lng_bwdN by simp
            have lt1: "entry M 1 j0' - 1 < Lng ?N" using lt2 by simp
            have noint: "\<forall>j. entry M 1 j0' - 1 < j \<and> j < entry M 1 j0'
                            \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 (entry M 1 j0')" by auto
            show ?thesis unfolding nextrel0_def
              using Lm1 e1 e2 lt1 lt2 noint pos by simp
          qed
          have rt1: "(nextrel0 ?N)\<^sup>*\<^sup>* (Suc k0) (entry M 1 j0' - 1)"
            using r1 by (simp add: le0_def)
          have rtm: "(nextrel0 ?N)\<^sup>*\<^sup>* (Suc k0) (entry M 1 j0')"
            using rt1 step by (rule rtranclp.rtrancl_into_rtrancl)
          have b0: "Suc k0 < Lng ?N" using sk k1m by (simp add: Lng_bwdN)
          have b1: "entry M 1 j0' < Lng ?N" by (simp add: Lng_bwdN)
          have "le0 ?N (Suc k0) (entry M 1 j0')"
            using rtm b0 b1 by (simp add: le0_def)
          thus ?thesis using k1m by simp
        qed
      qed
      have minrule: "\<forall>j. k0 < j \<and> le0 ?N j k1 \<longrightarrow> entry ?N 1 j \<ge> entry ?N 1 k1"
        using nx i1 by (simp add: nextR_def nextrel1_def)
      have "entry ?N 1 (Suc k0) \<ge> entry ?N 1 k1" using minrule sk le0junc by simp
      thus False using emid ek1 i1 sk by simp
    qed
  qed
  thus ?thesis using ek0 ek1 by simp
qed


text \<open>Entry of \<open>bwdN\<close> on the rebase region \<open>k = m + t\<close> (\<open>m = M\<^bsub>1,j'\<^sub>0\<^esub>\<close>) in terms of \<open>M\<close>:
  row 0 is \<open>M\<^bsub>0,j'\<^sub>0+t\<^esub> - M\<^bsub>0,j'\<^sub>0\<^esub> + m\<close>, row 1 is \<open>M\<^bsub>1,j'\<^sub>0+t\<^esub>\<close>.\<close>

lemma entry_bwdN_rebase_M:
  assumes "t < Suc (j1' - j0')"
  shows "entry (bwdN M j0' j1') 0 (entry M 1 j0' + t)
           = entry M 0 (j0' + t) - entry M 0 j0' + entry M 1 j0'"
    and "entry (bwdN M j0' j1') 1 (entry M 1 j0' + t) = entry M 1 (j0' + t)"
proof -
  let ?m = "entry M 1 j0'"
  have ge: "?m \<le> ?m + t" by simp
  have r0: "entry (bwdN M j0' j1') 0 (?m + t) = entry (rebaseNp M j0' j1') 0 ((?m + t) - ?m)"
    by (rule entry_bwdN_rebase[OF ge])
  have r1: "entry (bwdN M j0' j1') 1 (?m + t) = entry (rebaseNp M j0' j1') 1 ((?m + t) - ?m)"
    by (rule entry_bwdN_rebase[OF ge])
  have tm: "(?m + t) - ?m = t" by simp
  show "entry (bwdN M j0' j1') 0 (?m + t) = entry M 0 (j0' + t) - entry M 0 j0' + ?m"
    using r0 tm entry_rebaseNp(1)[OF assms] by simp
  show "entry (bwdN M j0' j1') 1 (?m + t) = entry M 1 (j0' + t)"
    using r1 tm entry_rebaseNp(2)[OF assms] by simp
qed

text \<open>\<S>6.6 KEYSTONE BACKWARD aux (*): \<open>RedCondA (bwdN ..)\<close>, the case-1 transfer.
  For a \<open>nextR\<close>-edge \<open>(i,k\<^sub>0) <\<^bsub>N\<^esub>\<^sup>Next (i,k\<^sub>1)\<close> with both endpoints in the rebase
  region (\<open>m \<le> k\<^sub>0\<close>), the edge corresponds to an \<open>M\<close>-edge on the slice
  \<open>(i,j'\<^sub>0+a) <\<^bsub>M\<^esub>\<^sup>Next (i,j'\<^sub>0+b)\<close> (\<open>a = k\<^sub>0-m\<close>, \<open>b = k\<^sub>1-m\<close>), and \<open>RedCondA M\<close>
  closes it (content.md 1238, \<open>M\<^bsub>1,j'\<^sub>0\<^esub> \<le> k\<^sub>0\<close> case).

  Row 0 transfer is a strictly-monotone shift of \<open>M\<close>'s row 0 on the slice (the
  intermediate \<open>nextrel0\<close> range stays \<open>> k\<^sub>0 \<ge> m\<close>, hence in the rebase).  Row 1
  transfer uses that any \<open>le0 N\<close> path from a rebase node \<open>\<ge> m\<close> stays \<open>\<ge> m\<close>
  (@{thm [source] nextrel0_rtrancl_mono}: \<open>nextrel0\<close> indices increase), so the
  row-1 minimality of \<open>N\<close> (over a superset of witnesses) implies that of \<open>M\<close>.\<close>

text \<open>Row-0 case-1 transfer: \<open>nextrel0 (bwdN ..) (m+a) (m+b) \<Longrightarrow> nextrel0 M (j'\<^sub>0+a) (j'\<^sub>0+b)\<close>.\<close>

lemma nextrel0_bwdN_rebase_to_M:
  assumes jord: "j0' \<le> j1'" and j1LM: "j1' < Lng M"
    and rmono: "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
    and aL: "a < Suc (j1' - j0')" and bL: "b < Suc (j1' - j0')"
    and nx: "nextrel0 (bwdN M j0' j1') (entry M 1 j0' + a) (entry M 1 j0' + b)"
  shows "nextrel0 M (j0' + a) (j0' + b)"
proof -
  let ?N = "bwdN M j0' j1'" let ?m = "entry M 1 j0'"
  let ?c = "entry M 0 j0'"
  have abm: "?m + a < ?m + b" using nx unfolding nextrel0_def by blast
  have ab: "a < b" using abm by simp
  \<comment> \<open>entries on the rebase region\<close>
  have eNa: "entry ?N 0 (?m + a) = entry M 0 (j0' + a) - ?c + ?m"
    by (rule entry_bwdN_rebase_M(1)[OF aL])
  have eNb: "entry ?N 0 (?m + b) = entry M 0 (j0' + b) - ?c + ?m"
    by (rule entry_bwdN_rebase_M(1)[OF bL])
  have aLle: "a \<le> j1' - j0'" using aL by simp
  have bLle: "b \<le> j1' - j0'" using bL by simp
  have monb: "?c \<le> entry M 0 (j0' + b)" by (rule rmono[rule_format, OF bLle])
  have mona: "?c \<le> entry M 0 (j0' + a)" by (rule rmono[rule_format, OF aLle])
  \<comment> \<open>strict order transfers\<close>
  have strict: "entry M 0 (j0' + a) < entry M 0 (j0' + b)"
  proof -
    have "entry ?N 0 (?m + a) < entry ?N 0 (?m + b)"
      using nx unfolding nextrel0_def by blast
    thus ?thesis using eNa eNb mona monb by linarith
  qed
  \<comment> \<open>bounds\<close>
  have aLM: "j0' + a < Lng M" using aL j1LM jord by simp
  have bLM: "j0' + b < Lng M" using bL j1LM jord by simp
  \<comment> \<open>intermediate plateau: any \<open>j0'+a < j' < j0'+b\<close> maps to rebase index \<open>?m+(j'-j0')\<close>.\<close>
  have mid: "\<forall>j'. j0' + a < j' \<and> j' < j0' + b \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j0' + b)"
  proof (intro allI impI)
    fix j' assume a': "j0' + a < j' \<and> j' < j0' + b"
    let ?t = "j' - j0'"
    have j'ge: "j0' \<le> j'" using a' by simp
    have jeq: "j0' + ?t = j'" using j'ge by simp
    have tL: "?t < Suc (j1' - j0')" using a' bL j'ge by linarith
    have at: "a < ?t" using a' j'ge by linarith
    have tb: "?t < b" using a' j'ge by linarith
    have tLle: "?t \<le> j1' - j0'" using tL by simp
    have monj'0: "?c \<le> entry M 0 (j0' + ?t)" by (rule rmono[rule_format, OF tLle])
    have monj': "?c \<le> entry M 0 j'" using monj'0 jeq by simp
    have eNt0: "entry ?N 0 (?m + ?t) = entry M 0 (j0' + ?t) - ?c + ?m"
      by (rule entry_bwdN_rebase_M(1)[OF tL])
    have eNt: "entry ?N 0 (?m + ?t) = entry M 0 j' - ?c + ?m" using eNt0 jeq by simp
    \<comment> \<open>rebase index \<open>?m+?t\<close> is strictly between \<open>?m+a\<close> and \<open>?m+b\<close>.\<close>
    have lo: "?m + a < ?m + ?t" using at by simp
    have hi: "?m + ?t < ?m + b" using tb by simp
    have geN: "entry ?N 0 (?m + ?t) \<ge> entry ?N 0 (?m + b)"
      using nx lo hi unfolding nextrel0_def by blast
    have "entry M 0 j' - ?c + ?m \<ge> entry M 0 (j0' + b) - ?c + ?m"
      using geN eNt eNb by simp
    thus "entry M 0 j' \<ge> entry M 0 (j0' + b)" using monj' monb by linarith
  qed
  have abM: "j0' + a < j0' + b" using ab by simp
  show ?thesis unfolding nextrel0_def
    using aLM bLM abM strict mid by blast
qed



text \<open>Row-0 single-step transfer, M-to-N direction (witness mapping for row-1 minimality).
  \<open>nextrel0 M (j'\<^sub>0+a) (j'\<^sub>0+b) \<Longrightarrow> nextrel0 (bwdN ..) (m+a) (m+b)\<close> on the slice.\<close>

lemma nextrel0_M_to_bwdN_rebase:
  assumes jord: "j0' \<le> j1'" and j1LM: "j1' < Lng M"
    and rmono: "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
    and aL: "a \<le> j1' - j0'" and bL: "b \<le> j1' - j0'"
    and nx: "nextrel0 M (j0' + a) (j0' + b)"
  shows "nextrel0 (bwdN M j0' j1') (entry M 1 j0' + a) (entry M 1 j0' + b)"
proof -
  let ?N = "bwdN M j0' j1'" let ?m = "entry M 1 j0'" let ?c = "entry M 0 j0'"
  have aL': "a < Suc (j1' - j0')" using aL by simp
  have bL': "b < Suc (j1' - j0')" using bL by simp
  have ab: "a < b" using nx by (simp add: nextrel0_def)
  have eNa: "entry ?N 0 (?m + a) = entry M 0 (j0' + a) - ?c + ?m"
    by (rule entry_bwdN_rebase_M(1)[OF aL'])
  have eNb: "entry ?N 0 (?m + b) = entry M 0 (j0' + b) - ?c + ?m"
    by (rule entry_bwdN_rebase_M(1)[OF bL'])
  have monb: "?c \<le> entry M 0 (j0' + b)" by (rule rmono[rule_format, OF bL])
  have mona: "?c \<le> entry M 0 (j0' + a)" by (rule rmono[rule_format, OF aL])
  have strictM: "entry M 0 (j0' + a) < entry M 0 (j0' + b)" using nx by (simp add: nextrel0_def)
  have strict: "entry ?N 0 (?m + a) < entry ?N 0 (?m + b)"
    using eNa eNb mona monb strictM by linarith
  have aLN: "?m + a < Lng ?N" using aL' by (simp add: Lng_bwdN)
  have bLN: "?m + b < Lng ?N" using bL' by (simp add: Lng_bwdN)
  have mid: "\<forall>j. ?m + a < j \<and> j < ?m + b \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 (?m + b)"
  proof (intro allI impI)
    fix j assume aj: "?m + a < j \<and> j < ?m + b"
    let ?t = "j - ?m"
    have jge: "?m \<le> j" using aj by simp
    have jeq: "?m + ?t = j" using jge by simp
    have tlo: "a < ?t" using aj jge by linarith
    have thi: "?t < b" using aj jge by linarith
    have tL: "?t < Suc (j1' - j0')" using thi bL' by simp
    have tLle: "?t \<le> j1' - j0'" using tL by simp
    have eNt0: "entry ?N 0 (?m + ?t) = entry M 0 (j0' + ?t) - ?c + ?m"
      by (rule entry_bwdN_rebase_M(1)[OF tL])
    have eNt: "entry ?N 0 j = entry M 0 (j0' + ?t) - ?c + ?m" using eNt0 unfolding jeq .
    have mont: "?c \<le> entry M 0 (j0' + ?t)" by (rule rmono[rule_format, OF tLle])
    have midM: "entry M 0 (j0' + ?t) \<ge> entry M 0 (j0' + b)"
    proof -
      have "j0' + a < j0' + ?t" using tlo by simp
      moreover have "j0' + ?t < j0' + b" using thi by simp
      ultimately show ?thesis using nx unfolding nextrel0_def by blast
    qed
    have "entry M 0 (j0' + ?t) - ?c + ?m \<ge> entry M 0 (j0' + b) - ?c + ?m"
      using midM mont monb by simp
    thus "entry ?N 0 j \<ge> entry ?N 0 (?m + b)" using eNt eNb by simp
  qed
  have abN: "?m + a < ?m + b" using ab by simp
  show ?thesis unfolding nextrel0_def
    using aLN bLN abN strict mid by blast
qed

text \<open>le0 transfer, N rebase to M (rtrancl induction; \<open>nextrel0\<close> indices stay \<open>\<ge> m\<close>).\<close>

lemma le0_bwdN_rebase_to_M:
  assumes jord: "j0' \<le> j1'" and j1LM: "j1' < Lng M"
    and rmono: "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
    and bL: "b \<le> j1' - j0'"
    and le: "le0 (bwdN M j0' j1') (entry M 1 j0' + a) (entry M 1 j0' + b)"
  shows "le0 M (j0' + a) (j0' + b)"
proof -
  let ?N = "bwdN M j0' j1'" let ?m = "entry M 1 j0'"
  have ch: "(nextrel0 ?N)\<^sup>*\<^sup>* (?m + a) (?m + b)" using le by (simp add: le0_def)
  \<comment> \<open>Generalize: any rtrancl path from \<open>?m+a\<close> to \<open>z\<close> (with \<open>z \<le> ?m + b\<close>) maps to M.\<close>
  have main: "\<And>z. (nextrel0 ?N)\<^sup>*\<^sup>* (?m + a) z \<Longrightarrow> z \<le> ?m + b
                  \<Longrightarrow> ?m + a \<le> z \<and> (nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + (z - ?m))"
  proof -
    fix z assume "(nextrel0 ?N)\<^sup>*\<^sup>* (?m + a) z" and "z \<le> ?m + b"
    thus "?m + a \<le> z \<and> (nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + (z - ?m))"
    proof (induction rule: rtranclp_induct)
      case base show ?case by simp
    next
      case (step y w)
      have yw: "y < w" using step.hyps(2) by (simp add: nextrel0_def)
      have wle: "w \<le> ?m + b" using step.prems by simp
      have yle: "y \<le> ?m + b" using yw wle by simp
      have ywle: "?m + a \<le> y \<and> (nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + (y - ?m))"
        by (rule step.IH[OF yle])
      have ge: "?m + a \<le> y" using ywle by simp
      have yge: "?m \<le> y" using ge by simp
      have wge: "?m \<le> w" using yw yge by simp
      let ?ya = "y - ?m" let ?wa = "w - ?m"
      have yaeq: "?m + ?ya = y" using yge by simp
      have waeq: "?m + ?wa = w" using wge by simp
      have wL: "?wa \<le> j1' - j0'" using wle bL wge by linarith
      have yaL: "?ya \<le> j1' - j0'" using yw wL wge yge by linarith
      have nxN: "nextrel0 ?N (?m + ?ya) (?m + ?wa)" using step.hyps(2) yaeq waeq by simp
      have nxM: "nextrel0 M (j0' + ?ya) (j0' + ?wa)"
        by (rule nextrel0_bwdN_rebase_to_M[OF jord j1LM rmono _ _ nxN]) (use yaL wL in simp)+
      have "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + ?ya)" using conjunct2[OF ywle] .
      hence rtw: "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + ?wa)" using nxM by (rule rtranclp.rtrancl_into_rtrancl)
      have aw: "?m + a \<le> w" using ge yw by simp
      show ?case by (rule conjI[OF aw rtw])
    qed
  qed
  have main_z: "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + (( ?m + b) - ?m))"
    using main[OF ch] by simp
  have abeq: "(?m + b) - ?m = b" by simp
  have rt: "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + b)" using main_z abeq by simp
  have ale: "?m + a < Lng ?N" using le by (simp add: le0_def)
  have aL: "a \<le> j1' - j0'" using ale by (simp add: Lng_bwdN)
  have aLM: "j0' + a < Lng M" using aL j1LM jord by simp
  have bLM: "j0' + b < Lng M" using bL j1LM jord by simp
  show ?thesis using rt aLM bLM by (simp add: le0_def)
qed

text \<open>le0 transfer, M to N rebase (for mapping a row-1 minimality witness into N).\<close>

lemma le0_M_to_bwdN_rebase:
  assumes jord: "j0' \<le> j1'" and j1LM: "j1' < Lng M"
    and rmono: "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
    and aL: "a \<le> j1' - j0'" and bL: "b \<le> j1' - j0'"
    and le: "le0 M (j0' + a) (j0' + b)"
  shows "le0 (bwdN M j0' j1') (entry M 1 j0' + a) (entry M 1 j0' + b)"
proof -
  let ?N = "bwdN M j0' j1'" let ?m = "entry M 1 j0'"
  have ch: "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + b)" using le by (simp add: le0_def)
  have main: "\<And>z. (nextrel0 M)\<^sup>*\<^sup>* (j0' + a) z \<Longrightarrow> z \<le> j0' + b
                  \<Longrightarrow> j0' + a \<le> z \<and> (nextrel0 ?N)\<^sup>*\<^sup>* (?m + a) (?m + (z - j0'))"
  proof -
    fix z assume "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) z" and "z \<le> j0' + b"
    thus "j0' + a \<le> z \<and> (nextrel0 ?N)\<^sup>*\<^sup>* (?m + a) (?m + (z - j0'))"
    proof (induction rule: rtranclp_induct)
      case base show ?case by simp
    next
      case (step y w)
      have yw: "y < w" using step.hyps(2) by (simp add: nextrel0_def)
      have wle: "w \<le> j0' + b" using step.prems by simp
      have yle: "y \<le> j0' + b" using yw wle by simp
      have ywN: "j0' + a \<le> y \<and> (nextrel0 ?N)\<^sup>*\<^sup>* (?m + a) (?m + (y - j0'))"
        by (rule step.IH[OF yle])
      have ge: "j0' + a \<le> y" using ywN by simp
      have yge: "j0' \<le> y" using ge by simp
      have wge: "j0' \<le> w" using yw yge by simp
      let ?ya = "y - j0'" let ?wa = "w - j0'"
      have yaeq: "j0' + ?ya = y" using yge by simp
      have waeq: "j0' + ?wa = w" using wge by simp
      have wL: "?wa \<le> j1' - j0'" using wle bL wge by linarith
      have yaL: "?ya \<le> j1' - j0'" using yw wL wge yge by linarith
      have nxM: "nextrel0 M (j0' + ?ya) (j0' + ?wa)" using step.hyps(2) yaeq waeq by simp
      have nxN: "nextrel0 ?N (?m + ?ya) (?m + ?wa)"
        by (rule nextrel0_M_to_bwdN_rebase[OF jord j1LM rmono yaL wL nxM])
      have "(nextrel0 ?N)\<^sup>*\<^sup>* (?m + a) (?m + ?ya)" using conjunct2[OF ywN] .
      hence rtw: "(nextrel0 ?N)\<^sup>*\<^sup>* (?m + a) (?m + ?wa)" using nxN by (rule rtranclp.rtrancl_into_rtrancl)
      have aw: "j0' + a \<le> w" using ge yw by simp
      show ?case by (rule conjI[OF aw rtw])
    qed
  qed
  have main_z: "(nextrel0 ?N)\<^sup>*\<^sup>* (?m + a) (?m + ((j0' + b) - j0'))"
    using main[OF ch] by simp
  have rt: "(nextrel0 ?N)\<^sup>*\<^sup>* (?m + a) (?m + b)" using main_z by simp
  have aLN: "?m + a < Lng ?N" using aL by (simp add: Lng_bwdN)
  have bLN: "?m + b < Lng ?N" using bL by (simp add: Lng_bwdN)
  show ?thesis using rt aLN bLN by (simp add: le0_def)
qed

text \<open>Row-1 case-1 transfer: \<open>nextrel1 (bwdN ..) (m+a) (m+b) \<Longrightarrow> nextrel1 M (j'\<^sub>0+a) (j'\<^sub>0+b)\<close>.
  The row-1 minimality of \<open>N\<close> ranges over a superset of \<open>M\<close>'s witnesses (every \<open>M\<close>
  witness on the slice maps to an \<open>N\<close> rebase witness via @{thm [source] le0_M_to_bwdN_rebase}),
  so it implies \<open>M\<close>'s; the diagonal-prefix witnesses below \<open>m\<close> are simply extra.\<close>

lemma nextrel1_bwdN_rebase_to_M:
  assumes jord: "j0' \<le> j1'" and j1LM: "j1' < Lng M"
    and rmono: "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
    and aL: "a \<le> j1' - j0'" and bL: "b \<le> j1' - j0'"
    and nx: "nextrel1 (bwdN M j0' j1') (entry M 1 j0' + a) (entry M 1 j0' + b)"
  shows "nextrel1 M (j0' + a) (j0' + b)"
proof -
  let ?N = "bwdN M j0' j1'" let ?m = "entry M 1 j0'"
  have aL': "a < Suc (j1' - j0')" using aL by simp
  have bL': "b < Suc (j1' - j0')" using bL by simp
  have abN: "?m + a < ?m + b" using nx by (simp add: nextrel1_def)
  have ab: "a < b" using abN by simp
  have aLM: "j0' + a < Lng M" using aL j1LM jord by simp
  have bLM: "j0' + b < Lng M" using bL j1LM jord by simp
  \<comment> \<open>row-1 entries\<close>
  have e1a: "entry ?N 1 (?m + a) = entry M 1 (j0' + a)" by (rule entry_bwdN_rebase_M(2)[OF aL'])
  have e1b: "entry ?N 1 (?m + b) = entry M 1 (j0' + b)" by (rule entry_bwdN_rebase_M(2)[OF bL'])
  have strict1: "entry M 1 (j0' + a) < entry M 1 (j0' + b)"
    using nx e1a e1b by (simp add: nextrel1_def)
  \<comment> \<open>le0 transfer\<close>
  have le0N: "le0 ?N (?m + a) (?m + b)" using nx by (simp add: nextrel1_def)
  have le0M: "le0 M (j0' + a) (j0' + b)"
    by (rule le0_bwdN_rebase_to_M[OF jord j1LM rmono bL le0N])
  \<comment> \<open>minimality\<close>
  have minN: "\<forall>j. ?m + a < j \<and> le0 ?N j (?m + b) \<longrightarrow> entry ?N 1 j \<ge> entry ?N 1 (?m + b)"
    using nx by (simp add: nextrel1_def)
  have minM: "\<forall>j'. j0' + a < j' \<and> le0 M j' (j0' + b) \<longrightarrow> entry M 1 j' \<ge> entry M 1 (j0' + b)"
  proof (intro allI impI)
    fix j' assume H: "j0' + a < j' \<and> le0 M j' (j0' + b)"
    hence aj': "j0' + a < j'" and le0j': "le0 M j' (j0' + b)" by simp_all
    have j'le: "j' \<le> j0' + b"
    proof -
      have "(nextrel0 M)\<^sup>*\<^sup>* j' (j0' + b)" using le0j' by (simp add: le0_def)
      thus ?thesis by (rule nextrel0_rtrancl_mono)
    qed
    have j'ge: "j0' \<le> j'" using aj' by simp
    let ?t = "j' - j0'"
    have teq: "j0' + ?t = j'" using j'ge by simp
    have tlo: "a < ?t" using aj' j'ge by linarith
    have tle: "?t \<le> b" using j'le j'ge by linarith
    have tL: "?t \<le> j1' - j0'" using tle bL by simp
    \<comment> \<open>map the M-witness into the N rebase region\<close>
    have le0jt: "le0 M (j0' + ?t) (j0' + b)" using le0j' teq by simp
    have le0Nt: "le0 ?N (?m + ?t) (?m + b)"
      by (rule le0_M_to_bwdN_rebase[OF jord j1LM rmono tL bL le0jt])
    have aj'N: "?m + a < ?m + ?t" using tlo by simp
    have "entry ?N 1 (?m + ?t) \<ge> entry ?N 1 (?m + b)" using minN aj'N le0Nt by blast
    moreover have "entry ?N 1 (?m + ?t) = entry M 1 (j0' + ?t)"
      by (rule entry_bwdN_rebase_M(2)) (use tL in simp)
    ultimately have "entry M 1 (j0' + ?t) \<ge> entry M 1 (j0' + b)" using e1b by simp
    thus "entry M 1 j' \<ge> entry M 1 (j0' + b)" using teq by simp
  qed
  have abM: "j0' + a < j0' + b" using ab by simp
  show ?thesis unfolding nextrel1_def
    using aLM bLM abM strict1 le0M minM by blast
qed

text \<open>\<S>6.6 KEYSTONE BACKWARD aux (*): \<open>RedCondA (bwdN ..)\<close>.  Three cases on a
  \<open>nextR\<close>-edge \<open>(i,k\<^sub>0) <\<^bsub>N\<^esub>\<^sup>Next (i,k\<^sub>1)\<close> (content.md 1238-1242):
  \<^item> \<open>m \<le> k\<^sub>0\<close>: transfer the edge to \<open>M\<close> and use \<open>RedCondA M\<close>;
  \<^item> \<open>k\<^sub>1 \<le> m\<close>: pure diagonal, \<open>k\<^sub>0 = k\<^sub>1 - 1\<close> (@{thm [source] RedCondA_bwdN_diag_case});
  \<^item> \<open>k\<^sub>0 < m < k\<^sub>1\<close>: the cross-boundary case — left for the assembly (blocker note).\<close>

lemma RedCondA_bwdN_case1_and_diag:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M"
    and jord: "j0' \<le> j1'" and j1LM: "j1' < Lng M"
    and rmono: "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
    and nx: "nextR (bwdN M j0' j1') i k0 k1" and i: "i \<le> 1"
    and notcross: "entry M 1 j0' \<le> k0 \<or> k1 \<le> entry M 1 j0'"
  shows "entry (bwdN M j0' j1') i (parent (bwdN M j0' j1') i k1) + 1
            = entry (bwdN M j0' j1') i k1
         \<and> nextR (bwdN M j0' j1') i k0 k1"
proof -
  let ?N = "bwdN M j0' j1'" let ?m = "entry M 1 j0'"
  have k0lt: "k0 < k1" using nx
    by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
  have k1LN: "k1 < Lng ?N" using nx
    by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
  \<comment> \<open>parent of \<open>k1\<close> is \<open>k0\<close> (uniqueness from \<open>nextR\<close>).\<close>
  have pk: "parent ?N i k1 = k0"
  proof -
    have "\<exists>!j0. nextR ?N i j0 k1"
    proof
      show "nextR ?N i k0 k1" by (rule nx)
      fix j0 assume "nextR ?N i j0 k1"
      thus "j0 = k0" using wf17_nextR_unique[OF i _ nx] by simp
    qed
    thus ?thesis unfolding parent_def using the1_equality nx by fastforce
  qed
  have main: "entry ?N i k0 + 1 = entry ?N i k1"
  proof (cases "k1 \<le> ?m")
    case True
    show ?thesis by (rule RedCondA_bwdN_diag_case[OF nx i True])
  next
    case False
    hence mk1: "?m < k1" by simp
    have mk0: "?m \<le> k0" using notcross mk1 by linarith
    \<comment> \<open>both endpoints in rebase region; transfer to M.\<close>
    let ?a = "k0 - ?m" let ?b = "k1 - ?m"
    have aeq: "?m + ?a = k0" using mk0 by simp
    have beq: "?m + ?b = k1" using mk1 by simp
    have bLN: "k1 < Lng ?N" by (rule k1LN)
    have bL: "?b \<le> j1' - j0'" using bLN beq by (simp add: Lng_bwdN)
    have aL: "?a \<le> j1' - j0'" using k0lt bL aeq beq by linarith
    have aL': "?a < Suc (j1' - j0')" using aL by simp
    have bL': "?b < Suc (j1' - j0')" using bL by simp
    have nxM: "nextR M i (j0' + ?a) (j0' + ?b)"
    proof (cases "i = 0")
      case True
      have "nextrel0 ?N (?m + ?a) (?m + ?b)" using nx True aeq beq by (simp add: nextR_def)
      hence "nextrel0 M (j0' + ?a) (j0' + ?b)"
        by (rule nextrel0_bwdN_rebase_to_M[OF jord j1LM rmono aL' bL'])
      thus ?thesis using True by (simp add: nextR_def)
    next
      case False hence i1: "i = 1" using i by simp
      have "nextrel1 ?N (?m + ?a) (?m + ?b)" using nx i1 aeq beq by (simp add: nextR_def)
      hence "nextrel1 M (j0' + ?a) (j0' + ?b)"
        by (rule nextrel1_bwdN_rebase_to_M[OF jord j1LM rmono aL bL])
      thus ?thesis using i1 by (simp add: nextR_def)
    qed
    \<comment> \<open>hasParent M i (j0'+?b) with parent j0'+?a, RedCondA gives +1.\<close>
    have hpM: "hasParent M i (j0' + ?b)"
    proof -
      have "\<exists>!j0. nextR M i j0 (j0' + ?b)"
      proof
        show "nextR M i (j0' + ?a) (j0' + ?b)" by (rule nxM)
        fix j0 assume nj0: "nextR M i j0 (j0' + ?b)"
        show "j0 = j0' + ?a" using wf17_nextR_unique[OF i nj0 nxM] by simp
      qed
      thus ?thesis by (simp add: hasParent_def)
    qed
    have parM: "parent M i (j0' + ?b) = j0' + ?a"
      unfolding parent_def using nxM hpM the1_equality
      by (metis (mono_tags, lifting) hasParent_def)
    have iLM': "i \<le> 1" by (rule i)
    have condA_eq: "entry M i (parent M i (j0' + ?b)) + 1 = entry M i (j0' + ?b)"
      using condA hpM iLM' unfolding RedCondA_def by blast
    have eMa: "entry M i (j0' + ?a) + 1 = entry M i (j0' + ?b)"
      using condA_eq parM by simp
    \<comment> \<open>transfer back: entry ?N i k = entry M i (j0'+(k-m)) shifted.\<close>
    show ?thesis
    proof (cases "i = 0")
      case True
      have eNa0: "entry ?N 0 (?m + ?a) = entry M 0 (j0' + ?a) - entry M 0 j0' + ?m"
        by (rule entry_bwdN_rebase_M(1)[OF aL'])
      have eNa: "entry ?N 0 k0 = entry M 0 (j0' + ?a) - entry M 0 j0' + ?m"
        using eNa0 unfolding aeq .
      have eNb0: "entry ?N 0 (?m + ?b) = entry M 0 (j0' + ?b) - entry M 0 j0' + ?m"
        by (rule entry_bwdN_rebase_M(1)[OF bL'])
      have eNb: "entry ?N 0 k1 = entry M 0 (j0' + ?b) - entry M 0 j0' + ?m"
        using eNb0 unfolding beq .
      have mona: "entry M 0 j0' \<le> entry M 0 (j0' + ?a)" by (rule rmono[rule_format, OF aL])
      have monb: "entry M 0 j0' \<le> entry M 0 (j0' + ?b)" by (rule rmono[rule_format, OF bL])
      have eMa0: "entry M 0 (j0' + ?a) + 1 = entry M 0 (j0' + ?b)" using eMa True by simp
      have "entry ?N 0 k0 + 1 = entry ?N 0 k1" using eNa eNb eMa0 mona monb by linarith
      thus ?thesis using True by simp
    next
      case False hence i1: "i = 1" using i by simp
      have eNa0: "entry ?N 1 (?m + ?a) = entry M 1 (j0' + ?a)"
        by (rule entry_bwdN_rebase_M(2)[OF aL'])
      have eNa: "entry ?N 1 k0 = entry M 1 (j0' + ?a)" using eNa0 unfolding aeq .
      have eNb0: "entry ?N 1 (?m + ?b) = entry M 1 (j0' + ?b)"
        by (rule entry_bwdN_rebase_M(2)[OF bL'])
      have eNb: "entry ?N 1 k1 = entry M 1 (j0' + ?b)" using eNb0 unfolding beq .
      have eMa1: "entry M 1 (j0' + ?a) + 1 = entry M 1 (j0' + ?b)" using eMa i1 by simp
      have "entry ?N 1 k0 + 1 = entry ?N 1 k1" using eNa eNb eMa1 by simp
      thus ?thesis using i1 by simp
    qed
  qed
  have "entry ?N i (parent ?N i k1) + 1 = entry ?N i k1" using pk main by simp
  thus ?thesis using nx by simp
qed



text \<open>Slice strictness: a PT_PS (monoT) slice has strictly increasing row 0 from its
  left end, \<open>M\<^bsub>0,j'\<^sub>0\<^esub> < M\<^bsub>0,j'\<^sub>0+s\<^esub>\<close> for \<open>1 \<le> s \<le> j'\<^sub>1-j'\<^sub>0\<close>
  (@{thm [source] m_6_2_multi_crit_23} on the slice).\<close>

lemma seg_row0_strict:
  assumes jord: "j0' \<le> j1'" and j1LM: "j1' < Lng M"
    and segmono: "monoT (seg M j0' j1')"
    and s: "0 < s" and sL: "s \<le> j1' - j0'"
  shows "entry M 0 j0' < entry M 0 (j0' + s)"
proof -
  let ?S = "seg M j0' j1'"
  have ST: "?S \<in> T_PS" using jord by (simp add: T_PS_def seg_def del: upt_Suc)
  have LS: "Lng ?S = Suc (j1' - j0')" using jord by simp
  have leS: "leR ?S 0 0 (Lng ?S - 1)" using segmono by (simp add: monoT_def)
  have strict: "\<forall>j. 0 < j \<and> j < Lng ?S \<longrightarrow> entry ?S 0 0 < entry ?S 0 j"
    using m_6_2_multi_crit_23[OF ST] leS by blast
  have sLS: "s < Lng ?S" using sL LS by simp
  have "entry ?S 0 0 < entry ?S 0 s" using strict s sLS by blast
  moreover have "entry ?S 0 0 = entry M 0 j0'"
    using entry_seg[where j=0] LS by simp
  moreover have "entry ?S 0 s = entry M 0 (j0' + s)"
    using entry_seg[where j=s] sLS by simp
  ultimately show ?thesis by simp
qed

text \<open>Trunk reachability \<open>le0 N m k\<^sub>1\<close> in the rebase region: from the junction \<open>m\<close>
  (where \<open>N\<^bsub>0,m\<^esub> = m\<close>) every rebase node \<open>m < j \<le> k\<^sub>1\<close> has \<open>N\<^bsub>0,j\<^esub> > m\<close> (slice
  strictness), so @{thm [source] le0_build} pins the trunk.\<close>

lemma le0_bwdN_junction_to_rebase:
  assumes jord: "j0' \<le> j1'" and j1LM: "j1' < Lng M"
    and segmono: "monoT (seg M j0' j1')"
    and k1L: "k1 \<le> j1' - j0'" and pos: "0 < k1"
  shows "le0 (bwdN M j0' j1') (entry M 1 j0') (entry M 1 j0' + k1)"
proof -
  let ?N = "bwdN M j0' j1'" let ?m = "entry M 1 j0'"
  have NT: "?N \<in> T_PS" by (rule bwdN_in_T_PS)
  have em: "entry ?N 0 ?m = ?m" by (rule entry_bwdN_diag_le[OF order_refl]) simp
  have k1LN: "?m + k1 < Lng ?N" using k1L by (simp add: Lng_bwdN)
  have mlt: "?m < ?m + k1" using pos by simp
  have strict: "\<forall>j. ?m < j \<and> j \<le> ?m + k1 \<longrightarrow> entry ?N 0 ?m < entry ?N 0 j"
  proof (intro allI impI)
    fix j assume hj: "?m < j \<and> j \<le> ?m + k1"
    let ?s = "j - ?m"
    have jge: "?m \<le> j" using hj by simp
    have jeq: "?m + ?s = j" using jge by simp
    have spos: "0 < ?s" using hj jge by linarith
    have sL: "?s \<le> j1' - j0'" using hj jge k1L by linarith
    have sL': "?s < Suc (j1' - j0')" using sL by simp
    have eNj0: "entry ?N 0 (?m + ?s) = entry M 0 (j0' + ?s) - entry M 0 j0' + ?m"
      by (rule entry_bwdN_rebase_M(1)[OF sL'])
    have eNj: "entry ?N 0 j = entry M 0 (j0' + ?s) - entry M 0 j0' + ?m"
      using eNj0 unfolding jeq .
    have strictM: "entry M 0 j0' < entry M 0 (j0' + ?s)"
      by (rule seg_row0_strict[OF jord j1LM segmono spos sL])
    have "?m < entry M 0 (j0' + ?s) - entry M 0 j0' + ?m" using strictM by simp
    thus "entry ?N 0 ?m < entry ?N 0 j" using eNj em by simp
  qed
  have "(nextrel0 ?N)\<^sup>*\<^sup>* ?m (?m + k1)"
    by (rule le0_build[OF NT k1LN mlt strict])
  moreover have "?m < Lng ?N" using k1LN by simp
  ultimately show ?thesis using k1LN by (simp add: le0_def)
qed

text \<open>\<S>6.6 KEYSTONE BACKWARD aux (*): \<open>RedCondA (bwdN ..)\<close> case 2 (\<open>k\<^sub>0 < m < k\<^sub>1\<close>).
  Then \<open>k\<^sub>0 + 1 \<le> m < k\<^sub>1\<close> (no integer strictly between consecutive), the witness
  \<open>k\<^sub>0+1\<close> is on the diagonal/junction (\<open>N\<^bsub>i,k\<^sub>0+1\<^esub> = k\<^sub>0+1\<close>) and reaches \<open>k\<^sub>1\<close>
  (@{thm [source] le0_bwdN_junction_to_rebase} via the junction), so the \<open>nextR\<close>
  minimality pins \<open>N\<^bsub>i,k\<^sub>1\<^esub> = k\<^sub>0 + 1\<close>, i.e. \<open>k\<^sub>0 = N\<^bsub>i,k\<^sub>1\<^esub> - 1\<close>.\<close>

lemma RedCondA_bwdN_cross_case:
  assumes jord: "j0' \<le> j1'" and j1LM: "j1' < Lng M"
    and segmono: "monoT (seg M j0' j1')"
    and nx: "nextR (bwdN M j0' j1') i k0 k1" and i: "i \<le> 1"
    and cross: "k0 < entry M 1 j0' \<and> entry M 1 j0' < k1"
  shows "entry (bwdN M j0' j1') i k0 + 1 = entry (bwdN M j0' j1') i k1"
proof -
  let ?N = "bwdN M j0' j1'" let ?m = "entry M 1 j0'"
  have k0m: "k0 < ?m" and mk1: "?m < k1" using cross by simp_all
  have k0lt: "k0 < k1" using k0m mk1 by simp
  have k1LN: "k1 < Lng ?N" using nx
    by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
  \<comment> \<open>\<open>k\<^sub>0+1 \<le> m\<close> (no integer strictly between \<open>k\<^sub>0\<close> and \<open>k\<^sub>0+1\<close> can be \<open>m\<close>... actually \<open>k\<^sub>0<m\<close>).\<close>
  have sk0m: "Suc k0 \<le> ?m" using k0m by simp
  have sk0k1: "Suc k0 < k1" using sk0m mk1 by simp
  \<comment> \<open>entries at \<open>k\<^sub>0\<close> and \<open>k\<^sub>0+1\<close> are diagonal.\<close>
  have ek0: "entry ?N i k0 = k0" by (rule entry_bwdN_diag_le[OF less_imp_le[OF k0m] i])
  have esk0: "entry ?N i (Suc k0) = Suc k0" by (rule entry_bwdN_diag_le[OF sk0m i])
  \<comment> \<open>witness \<open>k\<^sub>0+1\<close> reaches \<open>k\<^sub>1\<close> via the junction trunk.\<close>
  have le0wit: "le0 ?N (Suc k0) k1"
  proof -
    have sk0Lm: "Suc k0 \<le> ?m" by (rule sk0m)
    \<comment> \<open>first \<open>k\<^sub>0+1 \<rightarrow> m\<close> (diagonal prefix + junction), then \<open>m \<rightarrow> k\<^sub>1\<close>.\<close>
    have part1: "le0 ?N (Suc k0) ?m"
    proof (cases "Suc k0 = ?m")
      case True
      have "?m < Lng ?N" using k1LN mk1 by simp
      thus ?thesis using True by (simp add: le0_def)
    next
      case False
      hence skm: "Suc k0 < ?m" using sk0m by simp
      have pos: "0 < ?m" using skm by simp
      have eq: "diagPre ?m = diagSeq 0 (?m - 1)" by (rule diagPre_eq_diagSeq[OF pos])
      have skm1: "Suc k0 \<le> ?m - 1" using skm by simp
      have r1: "le0 ?N (Suc k0) (?m - 1)"
      proof -
        have "le0 (diagSeq 0 (?m - 1) @ rebaseNp M j0' j1') (Suc k0) (?m - 1)"
          by (rule le0_diagSeq_append_prefix[OF skm1 order_refl])
        thus ?thesis using eq by (simp add: bwdN_def)
      qed
      have step: "nextrel0 ?N (?m - 1) ?m"
      proof -
        have Lm1: "?m - 1 < ?m" using pos by simp
        have e1: "entry ?N 0 (?m - 1) = ?m - 1" by (rule entry_bwdN_diag_le[where i=0]) simp_all
        have e2: "entry ?N 0 ?m = ?m" by (rule entry_bwdN_diag_le[OF order_refl]) simp
        have lt2: "?m < Lng ?N" by (simp add: Lng_bwdN)
        have lt1: "?m - 1 < Lng ?N" using lt2 by simp
        have noint: "\<forall>j. ?m - 1 < j \<and> j < ?m \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 ?m" by auto
        show ?thesis unfolding nextrel0_def using Lm1 e1 e2 lt1 lt2 noint pos by simp
      qed
      have rt1: "(nextrel0 ?N)\<^sup>*\<^sup>* (Suc k0) (?m - 1)" using r1 by (simp add: le0_def)
      have rtm: "(nextrel0 ?N)\<^sup>*\<^sup>* (Suc k0) ?m"
        using rt1 step by (rule rtranclp.rtrancl_into_rtrancl)
      have b1: "?m < Lng ?N" by (simp add: Lng_bwdN)
      have b0: "Suc k0 < Lng ?N" using skm b1 by simp
      show ?thesis using rtm b0 b1 by (simp add: le0_def)
    qed
    \<comment> \<open>then \<open>m \<rightarrow> k\<^sub>1\<close>.\<close>
    let ?t1 = "k1 - ?m"
    have t1eq: "?m + ?t1 = k1" using mk1 by simp
    have t1pos: "0 < ?t1" using mk1 by simp
    have t1L: "?t1 \<le> j1' - j0'" using k1LN t1eq by (simp add: Lng_bwdN)
    have part2: "le0 ?N ?m k1"
      using le0_bwdN_junction_to_rebase[OF jord j1LM segmono t1L t1pos] t1eq by simp
    show ?thesis using part1 part2 le0_trans by blast
  qed
  \<comment> \<open>now pin \<open>entry N i k1 = k0+1\<close>.\<close>
  have eik1_gt: "k0 < entry ?N i k1"
  proof (cases "i = 0")
    case True
    have "entry ?N 0 k0 < entry ?N 0 k1" using nx True by (simp add: nextR_def nextrel0_def)
    thus ?thesis using ek0 True by simp
  next
    case False hence i1: "i = 1" using i by simp
    have "entry ?N 1 k0 < entry ?N 1 k1" using nx i1 by (simp add: nextR_def nextrel1_def)
    thus ?thesis using ek0 i1 by simp
  qed
  have eik1_le: "entry ?N i k1 \<le> Suc k0"
  proof (cases "i = 0")
    case True
    have "entry ?N 0 (Suc k0) \<ge> entry ?N 0 k1"
      using nx True sk0k1 by (simp add: nextR_def nextrel0_def)
    thus ?thesis using esk0 True by simp
  next
    case False hence i1: "i = 1" using i by simp
    have "entry ?N 1 (Suc k0) \<ge> entry ?N 1 k1"
      using nx i1 sk0k1 le0wit by (simp add: nextR_def nextrel1_def)
    thus ?thesis using esk0 i1 by simp
  qed
  have "entry ?N i k1 = Suc k0" using eik1_gt eik1_le by simp
  thus ?thesis using ek0 by simp
qed

text \<open>\<open>rmono\<close> (slice row-0 weakly increasing from \<open>j'\<^sub>0\<close>) from a monoT slice:
  immediate from @{thm [source] seg_row0_strict} (strict \<Rightarrow> weak, with the \<open>s=0\<close> case).\<close>

lemma seg_rmono_of_monoT:
  assumes jord: "j0' \<le> j1'" and j1LM: "j1' < Lng M"
    and segmono: "monoT (seg M j0' j1')"
  shows "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
proof (intro allI impI)
  fix k assume kL: "k \<le> j1' - j0'"
  show "entry M 0 j0' \<le> entry M 0 (j0' + k)"
  proof (cases "k = 0")
    case True thus ?thesis by simp
  next
    case False hence "0 < k" by simp
    thus ?thesis using seg_row0_strict[OF jord j1LM segmono _ kL] by simp
  qed
qed

text \<open>\<S>6.6 KEYSTONE BACKWARD aux (*): \<open>RedCondA (bwdN ..)\<close> — piece (1) ASSEMBLED.
  Every \<open>nextR\<close>-edge of the backward column \<open>N = bwdN M j'\<^sub>0 j'\<^sub>1\<close> falls into the
  case-1/diagonal regime (@{thm [source] RedCondA_bwdN_case1_and_diag}) or the
  cross-boundary regime (@{thm [source] RedCondA_bwdN_cross_case}); both give the
  \<open>RedCondA\<close> consecutive-coefficient conclusion.  Needs \<open>RedCondA M\<close> and the slice
  being a \<open>monoT\<close> (PT_PS) slice.  Content.md 1238-1242.\<close>

lemma RedCondA_bwdN:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M"
    and jord: "j0' \<le> j1'" and j1LM: "j1' < Lng M"
    and segmono: "monoT (seg M j0' j1')"
  shows "RedCondA (bwdN M j0' j1')"
  unfolding RedCondA_def
proof (intro allI impI)
  fix i c :: nat
  assume i: "i \<le> 1" and hp: "hasParent (bwdN M j0' j1') i c"
  let ?N = "bwdN M j0' j1'" let ?m = "entry M 1 j0'"
  let ?k0 = "parent ?N i c"
  have rmono: "\<forall>k \<le> j1' - j0'. entry M 0 j0' \<le> entry M 0 (j0' + k)"
    by (rule seg_rmono_of_monoT[OF jord j1LM segmono])
  have nx: "nextR ?N i ?k0 c"
    using hp unfolding hasParent_def parent_def by (rule theI')
  show "entry ?N i ?k0 + 1 = entry ?N i c"
  proof (cases "?m \<le> ?k0 \<or> c \<le> ?m")
    case True
    have "entry ?N i ?k0 + 1 = entry ?N i c \<and> nextR ?N i ?k0 c"
      by (rule RedCondA_bwdN_case1_and_diag[OF MT condA jord j1LM rmono nx i True])
    thus ?thesis by simp
  next
    case False
    hence cross: "?k0 < ?m \<and> ?m < c" by simp
    show ?thesis by (rule RedCondA_bwdN_cross_case[OF jord j1LM segmono nx i cross])
  qed
qed


text \<open>\<S>6.6 KEYSTONE BACKWARD (GENERAL M) — Front A assembly (wf24-bwd).

  Mirror of the GREEN forward lift @{thm [source] kst_reduced_imp_condAB_cond}.
  Goal: \<open>kst_condAB_imp_reduced: M \<in> T_PS \<Longrightarrow> RedCondA M \<Longrightarrow> RedCondB M \<Longrightarrow> Red M = M\<close>
  for any \<open>M\<close> satisfying conditions (A) and (B), i.e. the backward half of the
  \<S>6.6 keystone \<open>reduced \<longleftrightarrow> A\<and>B\<close>.

  WLOG over the \<open>T_PS\<close> trichotomy, by strong induction on \<open>Lng M\<close>:
  \<^item> \<open>zeroT M\<close>: backward half of @{thm [source] kst_reduced_iff_cond_zeroT}.
  \<^item> \<open>multiT M\<close>: each \<open>P\<close>-block \<open>P M ! J\<close> inherits \<open>A\<and>B\<close>
    (@{thm [source] m_6_6_RedCond_P_block}, the concat-lift direction) and is
    strictly shorter (@{thm [source] kfwd_P_block_shorter}); the IH reduces every
    block, and @{thm [source] m_6_6_P_reduced} reassembles \<open>Red M = M\<close>.
  \<^item> \<open>monoT M\<close>, \<open>m\<^sub>1\<^sub>0 = 0\<close>: \<open>m\<^sub>0\<^sub>0 = 0\<close> by @{thm [source] m_6_6_bwd_e00_from_e10}, so the
    keystone CORE applies (residual hypothesis \<open>core\<close>).
  \<^item> \<open>monoT M\<close>, \<open>m\<^sub>1\<^sub>0 > 0\<close>: residual hypothesis \<open>monoT_m10pos\<close> (the diagonal-prefix
    \<open>N = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ M\<close> reduction, content.md 1260-1290).

  The two residual hypotheses are exactly the monoT half of the backward
  keystone; every OTHER case (zeroT / multiT recursion / monoT m10=0 collapse)
  is discharged GREEN here.  Cites only GREEN facts (no \<open>p_*\<close> stub, no \<open>Red_le\<close>,
  no goal self-reference).\<close>

lemma kst_condAB_imp_reduced_cond:
  assumes core:
    "\<And>N. N \<in> T_PS \<Longrightarrow> monoT N \<Longrightarrow> entry N 0 0 = 0 \<Longrightarrow> entry N 1 0 = 0
       \<Longrightarrow> RedCondA N \<Longrightarrow> RedCondB N \<Longrightarrow> Red N = N"
  assumes monoT_m10pos:
    "\<And>N. N \<in> T_PS \<Longrightarrow> monoT N \<Longrightarrow> 0 < entry N 1 0
       \<Longrightarrow> RedCondA N \<Longrightarrow> RedCondB N \<Longrightarrow> Red N = N"
  assumes M0: "M \<in> T_PS" and condA0: "RedCondA M" and condB0: "RedCondB M"
  shows "Red M = M"
  using M0 condA0 condB0
proof (induction M rule: measure_induct_rule[where f = Lng])
  case (less M)
  have MT: "M \<in> T_PS" by (rule less.prems(1))
  have condA: "RedCondA M" by (rule less.prems(2))
  have condB: "RedCondB M" by (rule less.prems(3))
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  show ?case
  proof (cases "zeroT M")
    case True
    \<comment> \<open>zeroT: backward half of the GREEN zeroT iff.\<close>
    have "M \<in> RT_PS"
      using kst_reduced_iff_cond_zeroT[OF MT True] condA condB by blast
    thus ?thesis by (simp add: RT_PS_def)
  next
    case nz: False
    show ?thesis
    proof (cases "multiT M")
      case True
      \<comment> \<open>multiT: each block inherits \<open>A\<and>B\<close>, is shorter, reduced by IH; reassemble.\<close>
      have blocksRT: "\<forall>J < Lng (P M). P M ! J \<in> RT_PS"
      proof (intro allI impI)
        fix J assume J: "J < Lng (P M)"
        hence JL: "J < length (P M)" by simp
        have memB: "P M ! J \<in> set (P M)" using JL by simp
        have BT: "P M ! J \<in> T_PS"
          using P_blocks_nonempty[OF Mne] memB by (auto simp: T_PS_def)
        have BAB: "RedCondA (P M ! J) \<and> RedCondB (P M ! J)"
          by (rule m_6_6_RedCond_P_block[OF MT True condA condB JL])
        have shorter: "Lng (P M ! J) < Lng M"
          by (rule kfwd_P_block_shorter[OF MT True JL])
        have "Red (P M ! J) = P M ! J"
          by (rule less.IH[OF shorter BT conjunct1[OF BAB] conjunct2[OF BAB]])
        thus "P M ! J \<in> RT_PS" using BT by (simp add: RT_PS_def)
      qed
      have "M \<in> RT_PS" using m_6_6_P_reduced[OF MT] blocksRT by blast
      thus ?thesis by (simp add: RT_PS_def)
    next
      case nmu: False
      have mono: "monoT M" using nz nmu by (simp add: monoT_def multiT_def)
      show ?thesis
      proof (cases "0 < entry M 1 0")
        case True
        \<comment> \<open>monoT, m10>0: residual hypothesis.\<close>
        show ?thesis by (rule monoT_m10pos[OF MT mono True condA condB])
      next
        case False
        hence e10: "entry M 1 0 = 0" by simp
        have e00: "entry M 0 0 = 0" by (rule m_6_6_bwd_e00_from_e10[OF MT condB e10])
        \<comment> \<open>monoT, m10=0 \<Longrightarrow> m00=0: the keystone core.\<close>
        show ?thesis by (rule core[OF MT mono e00 e10 condA condB])
      qed
    qed
  qed
qed

end

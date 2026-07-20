theory Frontier_6_023
  imports Support_6_006
begin

text \<open>m (H3): branch-5 re-basing map preserves \<open>leR\<close> on the suffix.

  In \<open>Red\<close> branch 5 (\<open>M\<^sub>0 \<noteq> (0,0)\<close>, \<open>M\<^bsub>1,0\<^esub> > 0\<close>), with \<open>N\<close> a term and
  \<open>m\<^sub>1\<^sub>0 \<le> j\<^sub>N = Lng N - 1\<close>, the productive form [18] is
  \<open>Red M = map (\<lambda>p. (fst p - N\<^bsub>0,m\<^sub>1\<^sub>0\<^esub> + N\<^bsub>1,m\<^sub>1\<^sub>0\<^esub>, snd p)) (seg N m\<^sub>1\<^sub>0 (Lng N - 1))\<close>.
  This is a composition of (i) the seg-extraction transfer
  @{thm [source] adm_le0_seg}/@{thm [source] adm_le1_seg} and (ii) a uniform
  row-0 affine shift (subtract \<open>N\<^bsub>0,m\<^sub>1\<^sub>0\<^esub>\<close>, add \<open>N\<^bsub>1,m\<^sub>1\<^sub>0\<^esub>\<close>) of the slice.

  The map is the generic affine row-0 shift \<open>rebaseRow0 c d\<close>; on a slice whose
  row-0 minimum is its left end (the [18] \<open>PT\<^sub>PS\<close>-anchoring guarantees this via
  @{thm [source] monoT_row0_min}) the subtraction does not truncate, so the order
  on row 0 — and hence \<open>nextrel0\<close>/\<open>le0\<close>, and then \<open>nextrel1\<close>/\<open>le1\<close> which keep row 1
  and reuse \<open>le0\<close> — is preserved.\<close>

definition rebaseRow0 :: "nat \<Rightarrow> nat \<Rightarrow> pairseq \<Rightarrow> pairseq" where
  "rebaseRow0 c d M = map (\<lambda>p. (fst p - c + d, snd p)) M"

lemma Lng_rebaseRow0[simp]: "Lng (rebaseRow0 c d M) = Lng M"
  by (simp add: rebaseRow0_def)

lemma entry_rebaseRow0_0:
  "j < Lng M \<Longrightarrow> entry (rebaseRow0 c d M) 0 j = entry M 0 j - c + d"
  by (simp add: rebaseRow0_def entry_def)

lemma entry_rebaseRow0_1:
  "j < Lng M \<Longrightarrow> entry (rebaseRow0 c d M) 1 j = entry M 1 j"
  by (simp add: rebaseRow0_def entry_def)

text \<open>Generic affine row-0 shift preserves \<open>nextrel0\<close> when \<open>c\<close> is a row-0 lower
  bound (so no nat-truncation).\<close>

lemma nextrel0_rebaseRow0_eq:
  assumes lb: "\<And>j. j < Lng M \<Longrightarrow> c \<le> entry M 0 j"
  shows "nextrel0 (rebaseRow0 c d M) j0 j1 = nextrel0 M j0 j1"
proof (cases "j0 < Lng M \<and> j1 < Lng M")
  case True
  hence j0L: "j0 < Lng M" and j1L: "j1 < Lng M" by simp_all
  have e0: "entry (rebaseRow0 c d M) 0 j0 = entry M 0 j0 - c + d"
    using j0L by (rule entry_rebaseRow0_0)
  have e1: "entry (rebaseRow0 c d M) 0 j1 = entry M 0 j1 - c + d"
    using j1L by (rule entry_rebaseRow0_0)
  have gj0: "c \<le> entry M 0 j0" using lb[OF j0L] .
  have gj1: "c \<le> entry M 0 j1" using lb[OF j1L] .
  have lt_iff: "(entry M 0 j0 - c + d < entry M 0 j1 - c + d) = (entry M 0 j0 < entry M 0 j1)"
    using gj0 gj1 by linarith
  have ge_iff: "\<forall>j. j0 < j \<and> j < j1 \<longrightarrow>
                  (entry (rebaseRow0 c d M) 0 j \<ge> entry (rebaseRow0 c d M) 0 j1)
                  = (entry M 0 j \<ge> entry M 0 j1)"
  proof (intro allI impI)
    fix j assume jb: "j0 < j \<and> j < j1"
    hence jL: "j < Lng M" using j1L by simp
    have ej: "entry (rebaseRow0 c d M) 0 j = entry M 0 j - c + d"
      using jL by (rule entry_rebaseRow0_0)
    have gj: "c \<le> entry M 0 j" using lb[OF jL] .
    show "(entry (rebaseRow0 c d M) 0 j \<ge> entry (rebaseRow0 c d M) 0 j1)
            = (entry M 0 j \<ge> entry M 0 j1)"
      using ej e1 gj gj1 by linarith
  qed
  show ?thesis
    unfolding nextrel0_def
    using e0 e1 lt_iff ge_iff by (simp cong: conj_cong)
next
  case False
  thus ?thesis by (auto simp: nextrel0_def)
qed

lemma le0_rebaseRow0_eq:
  assumes lb: "\<And>j. j < Lng M \<Longrightarrow> c \<le> entry M 0 j"
  shows "le0 (rebaseRow0 c d M) j0 j1 = le0 M j0 j1"
proof -
  have "nextrel0 (rebaseRow0 c d M) = nextrel0 M"
    by (intro ext) (rule nextrel0_rebaseRow0_eq[OF lb])
  thus ?thesis by (simp add: le0_def)
qed

text \<open>\<open>nextrel1\<close> only adds row-1 comparisons (row 1 is kept) and a \<open>le0\<close>-quantified
  condition, so it transfers along the \<open>le0\<close> correspondence above.\<close>

lemma nextrel1_rebaseRow0_eq:
  assumes lb: "\<And>j. j < Lng M \<Longrightarrow> c \<le> entry M 0 j"
  shows "nextrel1 (rebaseRow0 c d M) j0 j1 = nextrel1 M j0 j1"
proof (cases "j0 < Lng M \<and> j1 < Lng M")
  case True
  hence j0L: "j0 < Lng M" and j1L: "j1 < Lng M" by simp_all
  have e1j0: "entry (rebaseRow0 c d M) 1 j0 = entry M 1 j0" using j0L by (rule entry_rebaseRow0_1)
  have e1j1: "entry (rebaseRow0 c d M) 1 j1 = entry M 1 j1" using j1L by (rule entry_rebaseRow0_1)
  have le0eq: "le0 (rebaseRow0 c d M) = le0 M"
    by (intro ext) (rule le0_rebaseRow0_eq[OF lb])
  have univ: "(\<forall>j. j0 < j \<and> le0 (rebaseRow0 c d M) j j1
                 \<longrightarrow> entry (rebaseRow0 c d M) 1 j \<ge> entry (rebaseRow0 c d M) 1 j1)
            = (\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j \<ge> entry M 1 j1)"
  proof (intro iffI allI impI)
    fix j assume A: "\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j \<ge> entry M 1 j1"
      and B: "j0 < j \<and> le0 (rebaseRow0 c d M) j j1"
    from B have jL: "(j::nat) < Lng M" by (simp add: le0_def)
    have ej: "entry (rebaseRow0 c d M) 1 j = entry M 1 j" using jL by (rule entry_rebaseRow0_1)
    from B A have "entry M 1 j1 \<le> entry M 1 j" using le0eq by simp
    thus "entry (rebaseRow0 c d M) 1 j1 \<le> entry (rebaseRow0 c d M) 1 j"
      using ej e1j1 by simp
  next
    fix j assume A: "\<forall>j. j0 < j \<and> le0 (rebaseRow0 c d M) j j1
                       \<longrightarrow> entry (rebaseRow0 c d M) 1 j \<ge> entry (rebaseRow0 c d M) 1 j1"
      and B: "j0 < j \<and> le0 M j j1"
    from B have jL: "(j::nat) < Lng M" by (simp add: le0_def)
    have ej: "entry (rebaseRow0 c d M) 1 j = entry M 1 j" using jL by (rule entry_rebaseRow0_1)
    from B A have "entry (rebaseRow0 c d M) 1 j1 \<le> entry (rebaseRow0 c d M) 1 j"
      using le0eq by simp
    thus "entry M 1 j1 \<le> entry M 1 j" using ej e1j1 by simp
  qed
  have le0eq2: "\<And>a b. le0 (rebaseRow0 c d M) a b = le0 M a b" using le0eq by simp
  show ?thesis
    unfolding nextrel1_def
    using e1j0 e1j1 le0eq univ by (simp cong: conj_cong)
next
  case False
  thus ?thesis by (auto simp: nextrel1_def)
qed

subsection \<open>§6.5 補正定義域 \<open>anchored_slice\<close> の基本性質 (correction A4)\<close>

text \<open>An ancestor-anchored slice is non-empty, hence in \<open>T\<^sub>PS\<close> (so \<open>Red\<close> is
  defined on it via @{thm [source] m_6_5_Red_welldef}).\<close>

lemma anchored_slice_imp_T_PS:
  assumes "M \<in> anchored_slice"
  shows "M \<in> T_PS"
proof -
  from assms obtain S a b where ab: "a \<le> b" and M: "M = seg S a b"
    unfolding anchored_slice_def by blast
  have "length M = Suc b - a" using M by simp
  with ab have "0 < length M" by simp
  thus ?thesis by (simp add: T_PS_def)
qed


text \<open>m: 命題（zeroT の Red 不変性） — discharges p_6_5_Red_zeroT.\<close>
\<comment> \<open>Auxiliary: when Lng M = 1, ¬ zeroT M, M ∈ T_PS, then entry (Red M) 1 0 ≠ 0.\<close>
lemma rz_Red_entry1_nz:
  assumes MT: "M \<in> T_PS" and L1: "Lng M = 1" and nz: "\<not> zeroT M"
  shows "entry (Red M) 1 0 \<noteq> 0"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  \<comment> \<open>Lng M = 1 and ¬ zeroT M implies monoT and ¬ multiT.\<close>
  have mono: "monoT M" using L1 nz by (simp add: monoT_def leR_def le0_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  let ?m10 = "entry M 1 0"
  have m10pos: "0 < ?m10" using nz L1 by (simp add: zeroT_def)
  \<comment> \<open>¬ core: m10 > 0 implies ¬ (m00 = 0 \<and> m10 = 0).\<close>
  have nc: "\<not> (entry M 0 0 = 0 \<and> ?m10 = 0)" using m10pos by simp
  \<comment> \<open>Red M unfolds to the m10>0 non-core branch.\<close>
  let ?arg = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
  have rM: "Red M = (let N = Red ?arg; jN = Lng N - 1 in
             if ?m10 \<le> jN \<and> seg N ?m10 jN \<in> PT_PS then
               map (\<lambda>j. (entry N 0 j - entry N 0 ?m10 + entry N 1 ?m10,
                         entry N 1 j))
                   [?m10..<Suc jN]
             else M)"
    using Red.psimps[OF domM] nz nmu nc m10pos
    by (simp add: Let_def)
  \<comment> \<open>arg is in T_PS (non-empty).\<close>
  have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
    using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
  have arg_T: "?arg \<in> T_PS" using funpow_ne by (simp add: T_PS_def)
  \<comment> \<open>Lng (Red arg) = Lng arg = m10 + 1.\<close>
  have Larg1: "Lng ?arg = ?m10 + 1"
    using m10pos L1 by (simp add: Lng_funpow_IncrFirst)
  have LN: "Lng (Red ?arg) = ?m10 + 1"
    using m_6_5_Lng_Red[OF arg_T] Larg1 by simp
  \<comment> \<open>jN = m10, so m10 \<le> jN holds.\<close>
  have jN_eq: "Lng (Red ?arg) - 1 = ?m10" using LN m10pos by simp
  have m10_le: "?m10 \<le> Lng (Red ?arg) - 1" using jN_eq by simp
  \<comment> \<open>Case split on whether seg (Red arg) m10 m10 \<in> PT_PS.\<close>
  show "entry (Red M) 1 0 \<noteq> 0"
  proof (cases "seg (Red ?arg) ?m10 (Lng (Red ?arg) - 1) \<in> PT_PS")
    case ptps: True
    \<comment> \<open>Red M = [(entry N 1 m10, entry N 1 m10)].\<close>
    have rM': "Red M = map (\<lambda>j. (entry (Red ?arg) 0 j - entry (Red ?arg) 0 ?m10
                                  + entry (Red ?arg) 1 ?m10,
                                  entry (Red ?arg) 1 j))
                            [?m10..<Suc (Lng (Red ?arg) - 1)]"
      using rM ptps m10_le by (simp add: Let_def)
    have rM'': "Red M = [(entry (Red ?arg) 1 ?m10, entry (Red ?arg) 1 ?m10)]"
      using rM' jN_eq by simp
    \<comment> \<open>seg N m10 m10 \<in> PT_PS \<Longrightarrow> monoT \<Longrightarrow> \<not> zeroT \<Longrightarrow> entry N 1 m10 \<noteq> 0.\<close>
    have seg_len1: "Lng (seg (Red ?arg) ?m10 ?m10) = 1"
      using LN m10pos by simp
    have seg_mono: "monoT (seg (Red ?arg) ?m10 ?m10)"
      using ptps jN_eq by (simp add: PT_PS_def)
    have seg_nz: "\<not> zeroT (seg (Red ?arg) ?m10 ?m10)"
      using seg_mono by (simp add: monoT_def)
    have eseg: "entry (seg (Red ?arg) ?m10 ?m10) 1 0 = entry (Red ?arg) 1 ?m10"
      using entry_seg[where M="Red ?arg" and a="?m10" and b="?m10" and i=1 and j=0]
            seg_len1 by simp
    have ne10: "entry (Red ?arg) 1 ?m10 \<noteq> 0"
    proof -
      have "entry (seg (Red ?arg) ?m10 ?m10) 1 0 \<noteq> 0"
        using seg_nz seg_len1 by (simp add: zeroT_def)
      thus ?thesis using eseg by simp
    qed
    have "entry (Red M) 1 0 = entry (Red ?arg) 1 ?m10"
      by (simp add: rM'' entry_def)
    thus "entry (Red M) 1 0 \<noteq> 0" using ne10 by simp
  next
    case False
    \<comment> \<open>Red M = M, and entry M 1 0 = m10 > 0.\<close>
    have "Red M = M" using rM m10_le False by (simp add: Let_def)
    thus ?thesis using m10pos by simp
  qed
qed

end

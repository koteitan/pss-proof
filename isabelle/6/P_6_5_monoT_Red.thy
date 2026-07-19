theory P_6_5_monoT_Red
  imports Frontier_6_042
begin

text \<open>命題（単項性と\<open>Red\<close>の関係） — the suffix \<open>(N\<^sub>j)\<^bsub>j=M\<^bsub>1,0\<^esub>\<^esub>\<^bsup>Lng N-1\<^esup>\<close> of
  \<open>N = Red (((j,j))\<^bsub>j=0\<^esub>\<^bsup>M\<^bsub>1,0\<^esub>-1\<^esup> \<oplus> IncrFirst\<^bsup>M\<^bsub>1,0\<^esub>\<^esup>(M))\<close> is mono;
  this is exactly the branch condition that makes the \<open>Red M := M\<close> fall-throughs
  \<^bold>\<open>[19]\<close>/\<^bold>\<open>[20]\<close> in the §6.5 definition dead.\<close>

text \<open>Encoding note: the article's diagonal \<open>((j,j))\<^bsub>j=0\<^esub>\<^bsup>M\<^bsub>1,0\<^esub>-1\<^esup>\<close> is the
  \<^emph>\<open>empty\<close> sequence when \<open>M\<^bsub>1,0\<^esub> = 0\<close>, but \<open>diagSeq 0 (entry M 1 0 - 1)\<close> is a
  spurious singleton \<open>[(0,0)]\<close> there (nat subtraction \<open>0-1=0\<close>), making the literal
  statement false at \<open>M\<^bsub>1,0\<^esub>=0\<close>.  Red invokes this construction only in its
  \<open>m\<^sub>1\<^sub>0>0\<close> branch [17], so the premise \<open>0 < entry M 1 0\<close> is added (faithful to
  the use-site); discharged by \<open>m_6_5_monoT_Red_m10pos\<close> in the corresponding §6 proposition theory.\<close>

text \<open>STEP-monoT_Red (α, m10>0): the suffix \<open>(N\<^bsub>j\<^esub>)\<^bsub>j=m10\<^esub>\<^bsup>jN\<^esup>\<close> is monoT, i.e.
  \<open>seg N m10 jN \<in> PT_PS\<close>.  This is the dead-branch[20] guard.  By
  @{thm [source] adm_le0_seg}, \<open>monoT(seg N m10 jN)\<close> reduces to the BC0 anchor
  edge @{thm [source] redB_le0_anchor_jN}.  Discharges \<open>p_6_5_monoT_Red\<close>
  for the \<open>m10>0\<close> case (the only case reachable in the \<open>Red\<close> recursion).\<close>

lemma m_6_5_monoT_Red_m10pos:
  assumes M: "M \<in> PT_PS" and pos: "0 < entry M 1 0"
  defines "N \<equiv> Red (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M)"
  shows "seg N (entry M 1 0) (Lng N - 1) \<in> PT_PS"
proof -
  let ?m10 = "entry M 1 0"
  let ?B = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
  let ?jN = "Lng N - 1"
  have MT: "M \<in> T_PS" and mono: "monoT M" using M by (simp_all add: PT_PS_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LM: "0 < Lng M" using Mne by (cases M) auto
  \<comment> \<open>geometry of N.\<close>
  have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
    using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
  have BT: "?B \<in> T_PS" using funpow_ne by (simp add: T_PS_def)
  have LB: "Lng ?B = Lng M + ?m10"
  proof -
    have Ldiag: "Lng (diagSeq 0 (?m10 - 1)) = ?m10" using pos by (simp del: upt_Suc)
    show ?thesis using Ldiag by simp
  qed
  have NB: "N = Red ?B" unfolding N_def by simp
  have LN: "Lng N = Lng M + ?m10" using m_6_5_Lng_Red[OF BT] LB NB by simp
  have m10lt: "?m10 < Lng N" using LN LM by simp
  have m10le: "?m10 \<le> ?jN" using m10lt by simp
  \<comment> \<open>the segment is non-empty, hence in T_PS.\<close>
  let ?S = "seg N ?m10 ?jN"
  have LS: "Lng ?S = Suc ?jN - ?m10" by (simp only: Lng_seg)
  have LSpos: "0 < Lng ?S" using LS m10le m10lt by simp
  have Sne: "?S \<noteq> []" using LSpos by force
  have ST: "?S \<in> T_PS" using Sne by (simp add: T_PS_def)
  \<comment> \<open>BC0 anchor edge: le0 N m10 jN.\<close>
  have bc0: "le0 N ?m10 ?jN"
    using redB_le0_anchor_jN[OF MT mono pos] NB by simp
  \<comment> \<open>transfer the le0 anchor edge onto the segment via @{thm [source] adm_le0_seg}.\<close>
  have jNlt: "?jN < Lng N" using m10lt by simp
  have inr0: "(0::nat) \<le> ?jN - ?m10" by simp
  have inrJ: "?jN - ?m10 \<le> ?jN - ?m10" by simp
  have transfer: "le0 ?S 0 (?jN - ?m10) = le0 N (?m10 + 0) (?m10 + (?jN - ?m10))"
    by (rule adm_le0_seg[OF jNlt inr0 inrJ m10le])
  have segend: "?m10 + (?jN - ?m10) = ?jN" using m10le by simp
  have le0S: "le0 ?S 0 (?jN - ?m10)"
    using transfer bc0 segend by simp
  \<comment> \<open>turn into monoT: leR S 0 0 (Lng S - 1) and non-zero.\<close>
  have LSm1: "Lng ?S - 1 = ?jN - ?m10" using LS m10le by simp
  have leRS: "leR ?S 0 0 (Lng ?S - 1)" using le0S LSm1 by (simp add: leR_def)
  have nzS: "\<not> zeroT ?S"
  proof (cases "Lng ?S = 1")
    case True
    \<comment> \<open>singleton: then m10 = jN, le0 S 0 0 trivially, and entry S 1 0 = entry N 1 m10 \<noteq> 0.\<close>
    have e1: "entry ?S 1 0 = entry N 1 ?m10"
      using entry_seg[where M=N and a="?m10" and b="?jN" and i=1 and j=0] LSpos
      by (simp only: LS) simp
    \<comment> \<open>entry N 1 m10 = m10 > 0 (row-1 diagonal value at the anchor).\<close>
    have e1val: "entry N 1 ?m10 = ?m10"
      using redB_row1_anchor[OF MT mono pos] NB by simp
    have "entry ?S 1 0 \<noteq> 0" using e1 e1val pos by simp
    thus ?thesis by (simp add: zeroT_def)
  next
    case False
    thus ?thesis by (simp add: zeroT_def)
  qed
  have monoS: "monoT ?S" using leRS nzS by (simp add: monoT_def)
  show ?thesis using ST monoS by (simp add: PT_PS_def)
qed


lemma p_6_5_monoT_Red:
  assumes "M \<in> PT_PS" "0 < entry M 1 0"  \<comment> \<open>m10>0: the empty-diagonal regime Red uses\<close>
  defines "N \<equiv> Red (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M)"
  shows "seg N (entry M 1 0) (Lng N - 1) \<in> PT_PS"
  unfolding N_def
  by (rule m_6_5_monoT_Red_m10pos[OF assms(1) assms(2)])

end

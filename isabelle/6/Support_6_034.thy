theory Support_6_034
  imports Frontier_6_051
begin

text \<open>m: \<open>(B2)\<close> — \<open>Red (coreReduce (IncrFirst M)) = Red (coreReduce M)\<close>.  By the
  cut identity above, \<open>coreReduce (IncrFirst M) = bumpAt (coreReduce M) m\<^sub>1\<^sub>0\<close>, and
  @{thm [source] fin_cut_bump_Red} (the engine) collapses the suffix bump under
  @{thm [source] fin_cutOK_coreReduce}.\<close>

lemma m_6_5_Red_IncrFirst_B2:
  assumes T: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "Red (coreReduce (IncrFirst M)) = Red (coreReduce M)"
proof -
  let ?m = "entry M 1 0"
  let ?X = "coreReduce M"
  have Mne: "M \<noteq> []" using T by (simp add: T_PS_def)
  have funpow_ne: "(IncrFirst ^^ ?m) M \<noteq> []"
    using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
  have crX: "?X = diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
    by (rule coreReduce_m10pos_form[OF pos])
  have XT: "?X \<in> T_PS" using funpow_ne crX by (simp add: T_PS_def)
  have cut: "cutOK ?X ?m" by (rule fin_cutOK_coreReduce[OF T mono pos])
  have ideq: "coreReduce (IncrFirst M) = bumpAt ?X ?m"
    by (rule fin_coreReduce_IncrFirst_bumpAt[OF T mono pos])
  have "Red (bumpAt ?X ?m) = Red ?X" by (rule fin_cut_bump_Red[OF cut XT])
  thus ?thesis using ideq by simp
qed

end

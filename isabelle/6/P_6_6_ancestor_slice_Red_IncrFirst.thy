theory P_6_6_ancestor_slice_Red_IncrFirst
  imports Support_6_072
begin

text \<open>系（直系先祖による切片と\<open>Red\<close>と\<open>IncrFirst\<close>の関係）.  原文の指数の添字 \<open>m\<close> は
  \<open>j\<^sub>0'\<close> の誤記（corrections.md A2）。\<close>

section \<open>§6.6 系（直系先祖による切片と\<open>Red\<close>と\<open>IncrFirst\<close>の関係） (correction A2)\<close>

text \<open>For reduced \<open>M\<close> and an ancestor-anchored window \<open>j0' < j1'\<close>, the slice
  reads back from its reduction by \<open>IncrFirst\<^bsup>M\<^bsub>0,j0'\<^esub>-M\<^bsub>1,j0'\<^esub>\<^esup>\<close>.  Route
  (simpler than the article's (A)/(B) verification for \<open>M'\<close>): the closed form
  @{thm [source] m_6_5_Red_rebase} evaluates \<open>N = Red S\<close> to the rebase of \<open>S\<close>
  directly; the readback \<open>S = IncrFirst\<^sup>k N\<close> is then nat arithmetic from the
  anchor row-0 minimality (@{thm [source] m_5_1_ancestor_basic_1}) and
  簡約性と係数の基本性質 (@{thm [source] m_6_6_reduced_coeff}); and
  \<open>Red N = Red (IncrFirst\<^sup>k N) = Red S = N\<close> by
  @{thm [source] cdn_red_cong} + @{thm [source] congR_self_funpow_IncrFirst}.\<close>

lemma m_6_6_ancestor_slice_Red_IncrFirst:
  assumes M: "M \<in> RT_PS" and j01: "j0' < j1'" and j1L: "j1' \<le> Lng M - 1"
    and anc: "leR M 0 j0' j1'"
  defines "N \<equiv> Red (seg M j0' j1')"
  shows "Red N = N \<and> monoT N
       \<and> seg M j0' j1' = (IncrFirst ^^ (entry M 0 j0' - entry M 1 j0')) N"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Lpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have j1lt: "j1' < Lng M" using j1L Lpos by linarith
  let ?S = "seg M j0' j1'"
  let ?e0 = "entry M 0 j0'"  let ?e1 = "entry M 1 j0'"
  let ?k = "?e0 - ?e1"
  have monoS: "monoT ?S" by (rule m_6_2_mono_ancestor_slice[OF MT j01 anc])
  have LS: "Lng ?S = Suc j1' - j0'" by simp
  have LSpos: "0 < Lng ?S" using j01 by simp
  have Sne: "?S \<noteq> []" using LSpos length_greater_0_conv by blast
  have ST: "?S \<in> T_PS" using Sne by (simp add: T_PS_def)
  have condAM: "RedCondA M" using m_6_6_reduced_iff_cond[OF MT] M by simp
  have condAS: "RedCondA ?S" by (rule RedCondA_seg[OF j1lt condAM])
  have nmuS: "\<not> multiT ?S" using monoS by (simp add: multiT_def)
  have rb: "Red ?S = map (\<lambda>j. (entry ?S 0 j - entry ?S 0 0 + entry ?S 1 0,
                                entry ?S 1 j)) [0..<Lng ?S]"
    by (rule m_6_5_Red_rebase[OF ST condAS nmuS])
  have e00S: "entry ?S 0 0 = ?e0" using LSpos by (simp add: entry_seg)
  have e10S: "entry ?S 1 0 = ?e1" using LSpos by (simp add: entry_seg)
  have j0lt: "j0' < Lng M" using j01 j1lt by linarith
  have cf: "?e1 \<le> ?e0" by (rule m_6_6_reduced_coeff[OF M j0lt])
  have minS: "\<And>j. j < Lng ?S \<Longrightarrow> ?e0 \<le> entry ?S 0 j"
  proof -
    fix j assume jS: "j < Lng ?S"
    show "?e0 \<le> entry ?S 0 j"
    proof (cases "j = 0")
      case True thus ?thesis using e00S by simp
    next
      case False
      have ej: "entry ?S 0 j = entry M 0 (j0' + j)" using jS by (simp add: entry_seg)
      have jj: "j0' < j0' + j" using False by simp
      have jb: "j0' + j \<le> j1'" using jS LS by linarith
      have "entry M 0 j0' < entry M 0 (j0' + j)"
        by (rule m_5_1_ancestor_basic_1[OF MT jj jb anc])
      thus ?thesis using ej by simp
    qed
  qed
  have NL: "Lng N = Lng ?S" unfolding N_def using rb by simp
  have NT: "N \<in> T_PS"
  proof -
    have "0 < Lng N" using NL LSpos by simp
    hence "N \<noteq> []" using length_greater_0_conv by blast
    thus ?thesis by (simp add: T_PS_def)
  qed
  have Nnth: "\<And>j. j < Lng ?S \<Longrightarrow>
                N ! j = (entry ?S 0 j - ?e0 + ?e1, entry ?S 1 j)"
    unfolding N_def using rb e00S e10S by simp
  have main: "?S = (IncrFirst ^^ ?k) N"
  proof (rule nth_equalityI)
    show "Lng ?S = Lng ((IncrFirst ^^ ?k) N)"
      using NL funpow_IncrFirst_as_map by simp
  next
    fix j assume jS: "j < Lng ?S"
    have jN: "j < Lng N" using jS NL by simp
    have lhs: "?S ! j = (entry ?S 0 j, entry ?S 1 j)"
      by (simp add: entry_def)
    have rhs: "(IncrFirst ^^ ?k) N ! j = (fst (N ! j) + ?k, snd (N ! j))"
      using funpow_IncrFirst_as_map jN by simp
    have fstv: "fst (N ! j) + ?k = entry ?S 0 j"
    proof -
      have "fst (N ! j) = entry ?S 0 j - ?e0 + ?e1" using Nnth[OF jS] by simp
      moreover have "entry ?S 0 j - ?e0 + ?e1 + (?e0 - ?e1) = entry ?S 0 j"
        using minS[OF jS] cf by linarith
      ultimately show ?thesis by simp
    qed
    have sndv: "snd (N ! j) = entry ?S 1 j" using Nnth[OF jS] by simp
    show "?S ! j = (IncrFirst ^^ ?k) N ! j"
      using lhs rhs fstv sndv by simp
  qed
  have SPT: "?S \<in> PT_PS" using ST monoS by (simp add: PT_PS_def)
  have monoN: "monoT N" unfolding N_def by (rule m_6_5_Red_preserves_monoT[OF SPT])
  have redN: "Red N = N"
  proof -
    have "Red N = Red ((IncrFirst ^^ ?k) N)"
      by (rule cdn_red_cong[OF congR_self_funpow_IncrFirst NT])
    also have "\<dots> = Red ?S" using main by simp
    also have "\<dots> = N" unfolding N_def ..
    finally show ?thesis .
  qed
  show ?thesis using redN monoN main by simp
qed

lemma p_6_6_ancestor_slice_Red_IncrFirst:
  assumes "M \<in> RT_PS" "j0' < j1'" "j1' \<le> Lng M - 1" "leR M 0 j0' j1'"
  defines "N \<equiv> Red (seg M j0' j1')"
  shows "Red N = N \<and> monoT N
       \<and> seg M j0' j1' = (IncrFirst ^^ (entry M 0 j0' - entry M 1 j0')) N"
  unfolding N_def
  by (rule m_6_6_ancestor_slice_Red_IncrFirst[OF assms(1) assms(2) assms(3) assms(4)])

end

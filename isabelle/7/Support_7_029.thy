theory Support_7_029
  imports Frontier_7_034
begin

lemma Mark_slice_eq_Red:
  assumes "M \<in> RT_PS" and "j0' < j1'" and "j1' \<le> Lng M - 1" and "leR M 0 j0' j1'"
  shows "Mark (seg M j0' j1') m = Mark (Red (seg M j0' j1')) m"
proof -
  let ?S = "seg M j0' j1'"  let ?N = "Red ?S"
  let ?k = "entry M 0 j0' - entry M 1 j0'"
  have segeq: "?S = (IncrFirst ^^ ?k) ?N"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF assms] by simp
  have NR: "?N \<in> RT_PS" using slice_Red_in_RT_PS[OF assms] by simp
  have NT: "?N \<in> T_PS" using NR by (simp add: RT_PS_def)
  have RN: "Red ?N \<in> RT_PS" using NR by (simp add: RT_PS_def)
  have "Mark ?S m = Mark ((IncrFirst ^^ ?k) ?N) m" using segeq by simp
  also have "\<dots> = Mark ?N m" by (rule Mark_funpow_IncrFirst[OF NT RN])
  finally show ?thesis .
qed


text \<open>§8.1 補題 part(1), the conjuncts NOT involving the A20-guarded slice
  equality (content.md 2949–2955): \<open>Trans (Pred M) \<noteq> 0\<close>, \<open>condI \<or> condIII\<close>,
  \<open>c\<^sub>1 \<in> T_B\<close> and \<open>c\<^sub>1\<close> principal.  Standalone green.  The guarded conjunct
  \<open>j\<^sub>0 < j\<^sub>1 - 1 \<longrightarrow> Trans (seg M j\<^sub>0 (j\<^sub>1 - 1)) = c\<^sub>1\<close> requires the §7.4 Mark–Trans
  representation \<open>Mark M m = Trans (seg M m (Lng M - 1))\<close> (content.md 2490),
  currently unproven, and is NOT discharged here.\<close>

text \<open>§7.4 「\<open>Mark\<close> の \<open>Trans\<close> による表示」 (content.md 2490) の橋渡し補題:
  後方スライス \<open>S = seg M m (Lng M - 1)\<close> について \<open>Mark S 0 = Trans S\<close> が
  既存補題のみから無条件に従う。\<open>S\<close> は一般には \<open>RT\<^bsub>PS\<^esub>\<close> に属さない(reduced で
  ない)ので、\<open>Red S\<close> を経由する: @{thm [source] m_6_6_ancestor_slice_Red_IncrFirst}
  により \<open>Red S\<close> は monoT かつ \<open>RT\<^bsub>PS\<^esub>\<close> に属し、ゆえに \<open>(Red S, 0) \<in> Marked\<close>。
  @{thm [source] ra_Mark0_eq_Trans} で \<open>Mark (Red S) 0 = Trans (Red S)\<close>、これを
  @{thm [source] Mark_slice_eq_Red} / @{thm [source] Trans_slice_eq_Red} で
  \<open>S\<close> へ持ち上げる。これにより、表示 \<open>Mark M m = Trans S\<close> は
  \<open>Mark M m = Mark S 0\<close> (parent の言う fact2)と同値になる。\<close>

lemma m_7_4_Mark0_slice_eq_Trans:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mlt: "m < Lng M - 1"
  shows "Mark (seg M m (Lng M - 1)) 0 = Trans (seg M m (Lng M - 1))"
proof -
  let ?j1 = "Lng M - 1"
  let ?S = "seg M m ?j1"
  let ?N = "Red ?S"
  \<comment> \<open>slice hypotheses, read off the \<open>Marked\<close> membership of \<open>m\<close>\<close>
  have leM: "leR M 0 m (Lng M - 1)" using mM by (simp add: Marked_def)
  have mj1: "m < ?j1" using mlt .
  have j1le: "?j1 \<le> Lng M - 1" by simp
  \<comment> \<open>\<open>Red ?S\<close> is monoT and reduced; the slice equals \<open>(IncrFirst^k) (Red ?S)\<close>\<close>
  have anc: "Red ?N = ?N \<and> monoT ?N
           \<and> ?S = (IncrFirst ^^ (entry M 0 m - entry M 1 m)) ?N"
    by (rule m_6_6_ancestor_slice_Red_IncrFirst[OF MR mj1 j1le leM])
  have monoN: "monoT ?N" using anc by simp
  have NR: "?N \<in> RT_PS" using slice_Red_in_RT_PS[OF MR mj1 j1le leM] by simp
  have NT: "?N \<in> T_PS" using NR by (simp add: RT_PS_def)
  \<comment> \<open>\<open>(Red ?S, 0) \<in> Marked\<close>: \<open>adm N 0\<close> always, \<open>le0 N 0 (Lng N - 1)\<close> from monoT\<close>
  have le0N: "leR ?N 0 0 (Lng ?N - 1)" using monoN by (simp add: monoT_def)
  have admN0: "adm ?N 0" by (rule adm_index0)
  have N0M: "(?N, 0) \<in> Marked" using NT admN0 le0N by (simp add: Marked_def)
  \<comment> \<open>\<open>Mark (Red ?S) 0 = Trans (Red ?S)\<close> by the index-0 representation\<close>
  have key: "Mark ?N 0 = Trans ?N" using ra_Mark0_eq_Trans N0M NR by simp
  \<comment> \<open>lift through \<open>Red\<close> to the slice itself\<close>
  have mk: "Mark ?S 0 = Mark ?N 0"
    by (rule Mark_slice_eq_Red[OF MR mj1 j1le leM])
  have tr: "Trans ?S = Trans ?N"
    by (rule Trans_slice_eq_Red[OF MR mj1 j1le leM])
  show ?thesis using mk tr key by simp
qed


text \<open>§7.4 keystone「\<open>Mark\<close> の \<open>Trans\<close> による表示」(content.md 2490) の multiT
  分岐の還元ステップ。\<open>multiT M\<close> のとき、許容的内部添字 \<open>m\<close> の \<open>Mark M m\<close> は
  最後の \<open>P\<close>-成分 \<open>PJ = drop (Pcut M) M\<close> 上の \<open>Mark PJ (m - Pcut M)\<close> に等しく
  (@{thm [source] multi_Marked_last_component}, Mark の (C) 分岐)、後方スライス
  \<open>seg M m (Lng M - 1)\<close> もまた \<open>PJ\<close> の対応スライス
  \<open>seg PJ (m - Pcut M) (Lng PJ - 1)\<close> に一致する(@{thm [source] seg_of_seg})。
  さらに \<open>PJ \<in> RT_PS\<close>、\<open>(PJ, m - Pcut M) \<in> Marked\<close>、\<open>Lng PJ < Lng M\<close>、
  \<open>m - Pcut M < Lng PJ - 1\<close> が成り立つので、表示 \<open>Mark M m = Trans (seg M m \<dots>)\<close>
  は、より短い \<open>PJ\<close> 上の同じ表示へ完全に還元される(強帰納法の multiT ステップ)。
  経験的検証: maxlen \<le> 4, maxe \<le> 3 の reduced multi で内部許容 \<open>m\<close> 違反 0 件。
  ここで \<open>PJ \<noteq> [(0,0)]\<close>(内部 \<open>m\<close> なら \<open>Lng PJ \<ge> 2\<close>)。\<close>

lemma m_7_4_repr_multiT_step:
  assumes MR: "M \<in> RT_PS" and mu: "multiT M"
    and mM: "(M, m) \<in> Marked" and mlt: "m < Lng M - 1"
  defines "PJ \<equiv> drop (Pcut M) M"
  shows "Mark M m = Mark PJ (m - Pcut M)
       \<and> seg M m (Lng M - 1) = seg PJ (m - Pcut M) (Lng PJ - 1)
       \<and> PJ \<in> RT_PS \<and> (PJ, m - Pcut M) \<in> Marked
       \<and> Lng PJ < Lng M \<and> m - Pcut M < Lng PJ - 1"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
  have cle: "Pcut M \<le> m" by (rule multi_Marked_last_component(1)[OF MT mu mM])
  \<comment> \<open>length of the last component and \<open>m\<close> in range\<close>
  let ?j1 = "Lng M - 1"
  have LPJ: "Lng PJ = Lng M - Pcut M" using PJ_def by simp
  have mltL: "m < Lng M" using mlt by linarith
  \<comment> \<open>(1) Mark reduction via the (C) branch (non-\<open>[(0,0)]\<close> since interior \<open>m\<close>)\<close>
  have PJne00: "PJ \<noteq> [(0,0)]"
  proof
    assume z: "PJ = [(0,0)]"
    have "Lng PJ = 1" using z by simp
    hence "Pcut M = Lng M - 1" using LPJ cut L by linarith
    thus False using cle mlt by linarith
  qed
  have PJeq: "P M ! (Lng (P M) - 1) = PJ"
    using trans_multiT_last_component(1)[OF MT mu] PJ_def by simp
  have j0eq: "Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 = Pcut M"
    by (rule trans_multiT_last_component(2)[OF MT mu])
  have domK: "\<And>m'. Trans_Mark_dom (Inr (M, m'))" by (rule m_7_3_Mark_welldef[OF MR])
  have nmono: "\<not> monoT M" using mu by (simp add: multiT_def)
  have c1: "(M \<notin> RT_PS) = False" using MR by simp
  have c2: "(Lng M - 1 = 0) = False" using L by simp
  have c3: "monoT M = False" using nmono by simp
  have meqj0: "m - (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1) = m - Pcut M"
    using j0eq by simp
  have PJne00': "P M ! (Lng (P M) - 1) \<noteq> [(0, 0)]" using PJne00 PJeq by simp
  have markM: "Mark M m = Mark PJ (m - Pcut M)"
  proof -
    have raw: "Mark M m =
        (if P M ! (Lng (P M) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
         else Mark (P M ! (Lng (P M) - 1))
                (m - (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1)))"
      by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
    have "Mark M m = Mark (P M ! (Lng (P M) - 1))
                       (m - (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1))"
      using raw PJne00' by (simp only: if_False)
    also have "\<dots> = Mark PJ (m - Pcut M)" using PJeq meqj0 by simp
    finally show ?thesis .
  qed
  \<comment> \<open>(2) slice composition: \<open>seg M m ?j1 = seg PJ (m - Pcut M) (Lng PJ - 1)\<close>\<close>
  have segPJ: "PJ = seg M (Pcut M) ?j1"
  proof -
    have "0 < Lng M" using L by linarith
    hence "seg M (Pcut M) (Lng M - 1) = drop (Pcut M) M"
      by (rule seg_to_last_eq_drop)
    thus ?thesis using PJ_def by simp
  qed
  have segcomp: "seg M m ?j1 = seg PJ (m - Pcut M) (Lng PJ - 1)"
  proof -
    have a_le_b: "Pcut M \<le> ?j1" using cut by simp
    have d_le: "Lng PJ - 1 \<le> ?j1 - Pcut M" using LPJ cut by linarith
    have step: "seg (seg M (Pcut M) ?j1) (m - Pcut M) (Lng PJ - 1)
        = seg M (Pcut M + (m - Pcut M)) (Pcut M + (Lng PJ - 1))"
      by (rule seg_of_seg[OF a_le_b d_le])
    have e1: "Pcut M + (m - Pcut M) = m" using cle by simp
    have e2: "Pcut M + (Lng PJ - 1) = ?j1" using LPJ cut by linarith
    have "seg PJ (m - Pcut M) (Lng PJ - 1) = seg M m ?j1"
      using step segPJ e1 e2 by simp
    thus ?thesis by simp
  qed
  \<comment> \<open>(3) \<open>PJ \<in> RT_PS\<close>, \<open>(PJ, m - Pcut M) \<in> Marked\<close>, length / index bounds\<close>
  have Pne: "P M \<noteq> []" by (rule P_nonempty)
  have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
  have PJRT: "PJ \<in> RT_PS"
    using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
  have mPJ: "(PJ, m - Pcut M) \<in> Marked"
    using multi_Marked_last_component(2)[OF MT mu mM] PJ_def by simp
  have LngPJlt: "Lng PJ < Lng M" using LPJ cut by linarith
  have mPJlt: "m - Pcut M < Lng PJ - 1" using LPJ cut cle mlt by linarith
  show ?thesis
    using markM segcomp PJRT mPJ LngPJlt mPJlt by blast
qed


text \<open>§7.4 keystone「\<open>Mark\<close> の \<open>Trans\<close> による表示」(content.md 2490)。
  \<open>(M,m) \<in> Marked\<close>, \<open>M \<in> RT_PS\<close>, \<open>m < Lng M - 1\<close> のとき
  \<open>Mark M m = Trans (seg M m (Lng M - 1))\<close>。
  橋渡し補題 @{thm [source] m_7_4_Mark0_slice_eq_Trans} により目標は
  \<open>Mark M m = Mark (seg M m (Lng M - 1)) 0\<close> (fact2) と同値である。
  ここでは \<open>m = 0\<close> の場合と、\<open>multiT M\<close> から最後の \<open>P\<close>-成分への還元
  (@{thm [source] m_7_4_repr_multiT_step}) を用いて、\<open>Lng M\<close> に関する強帰納法で
  「\<open>m = 0\<close> または、その還元を有限回適用して到達する成分が \<open>m' = 0\<close> で評価される」
  範囲を扱う。すなわち追加仮定 \<open>m = 0\<close> を置いた完全証明(\<open>monoT\<close> の内部
  \<open>m > 0\<close> ステージは未了 — 報告参照)。\<close>

lemma m_7_4_Mark_Trans_repr_m0:
  assumes mM: "(M, 0) \<in> Marked" and MR: "M \<in> RT_PS" and mlt: "0 < Lng M - 1"
  shows "Mark M 0 = Trans (seg M 0 (Lng M - 1))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L: "1 < Lng M" using mlt by linarith
  have L0: "0 < Lng M" using L by linarith
  \<comment> \<open>\<open>seg M 0 (Lng M - 1) = M\<close>\<close>
  have segM: "seg M 0 (Lng M - 1) = M"
  proof -
    have "seg M 0 (Lng M - 1) = take (Suc (Lng M - 1)) M"
      by (rule seg_0_eq_take) (use L in linarith)
    also have "Suc (Lng M - 1) = Lng M" using L by simp
    finally show ?thesis by simp
  qed
  \<comment> \<open>\<open>Mark M 0 = Trans M\<close> by the index-0 representation\<close>
  have key: "Mark M 0 = Trans M" using ra_Mark0_eq_Trans mM MR by simp
  show ?thesis using key segM by simp
qed


text \<open>§7.4 keystone, the boundary \<open>m = j\<^sub>1 - 1\<close> sub-case of the \<open>monoT\<close> stage
  (content.md 2495–2540): the backward slice \<open>seg M m (Lng M - 1)\<close> then has
  length 2, so its reduction \<open>N = Red (seg M m (Lng M - 1))\<close> is a reduced
  two-column \<open>monoT\<close> sequence, and \<open>Trans (seg M m (Lng M - 1))\<close> evaluates to the
  explicit closed form \<open>D\<^bsub>M\<^bsub>1,m\<^esub>\<^esub> D\<^bsub>M\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0\<close> via the two-column lemma
  (@{thm [source] m_7_3_twoColumn_Trans}) lifted through \<open>Red\<close>
  (@{thm [source] Trans_slice_eq_Red}).  Row 1 is preserved by \<open>Red\<close>
  (\<open>seg = (IncrFirst ^^ k) N\<close>, @{thm [source] entry_funpow_IncrFirst1}).\<close>

lemma m_7_4_Trans_slice_2col:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS"
    and mj1: "m = Lng M - 2" and L: "1 < Lng M - 1"
  shows "Trans (seg M m (Lng M - 1))
       = Dpt (enat (entry M 1 m)) (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
proof -
  let ?j1 = "Lng M - 1"
  let ?S = "seg M m ?j1"
  let ?N = "Red ?S"
  let ?k = "entry M 0 m - entry M 1 m"
  \<comment> \<open>slice hypotheses from \<open>Marked\<close> membership\<close>
  have leM: "leR M 0 m ?j1" using mM by (simp add: Marked_def)
  have mlt: "m < ?j1" using mj1 L by linarith
  have j1le: "?j1 \<le> Lng M - 1" by simp
  \<comment> \<open>\<open>N\<close> reduced, monoT, \<open>seg = (IncrFirst ^^ k) N\<close>\<close>
  have anc: "Red ?N = ?N \<and> monoT ?N \<and> ?S = (IncrFirst ^^ ?k) ?N"
    by (rule m_6_6_ancestor_slice_Red_IncrFirst[OF MR mlt j1le leM])
  have monoN: "monoT ?N" using anc by simp
  have segIF: "?S = (IncrFirst ^^ ?k) ?N" using anc by simp
  have NR: "?N \<in> RT_PS" using slice_Red_in_RT_PS[OF MR mlt j1le leM] by simp
  \<comment> \<open>length of slice and of \<open>N\<close> is 2\<close>
  have LS: "Lng ?S = 2" using mj1 L by simp
  have LN: "Lng ?N = 2"
  proof -
    have "Lng ?S = Lng ((IncrFirst ^^ ?k) ?N)" using segIF by simp
    also have "\<dots> = Lng ?N" by (rule Lng_funpow_IncrFirst)
    finally show ?thesis using LS by simp
  qed
  \<comment> \<open>two-column \<open>Trans\<close> value of \<open>N\<close>\<close>
  have transN: "Trans ?N
      = Dpt (enat (entry ?N 1 0)) (Dpt (enat (entry ?N 1 1)) 0\<^sub>B)"
    by (rule m_7_3_twoColumn_Trans[OF NR monoN LN])
  \<comment> \<open>row-1 of \<open>N\<close> equals row-1 of the slice (\<open>IncrFirst\<close> preserves row 1)\<close>
  have e1N0: "entry ?N 1 0 = entry M 1 m"
  proof -
    have "entry ?S 1 0 = entry ((IncrFirst ^^ ?k) ?N) 1 0" using segIF by simp
    also have "\<dots> = entry ?N 1 0"
      by (rule entry_funpow_IncrFirst1) (use LN in linarith)
    finally have a: "entry ?S 1 0 = entry ?N 1 0" .
    have b: "entry ?S 1 0 = entry M 1 m"
      using entry_seg[of 0 M m ?j1 1] LS by simp
    show ?thesis using a b by simp
  qed
  have e1N1: "entry ?N 1 1 = entry M 1 ?j1"
  proof -
    have "entry ?S 1 1 = entry ((IncrFirst ^^ ?k) ?N) 1 1" using segIF by simp
    also have "\<dots> = entry ?N 1 1"
      by (rule entry_funpow_IncrFirst1) (use LN in linarith)
    finally have a: "entry ?S 1 1 = entry ?N 1 1" .
    have idx: "m + 1 = ?j1" using mj1 L by linarith
    have b: "entry ?S 1 1 = entry M 1 ?j1"
      using entry_seg[of 1 M m ?j1 1] LS idx by simp
    show ?thesis using a b by simp
  qed
  \<comment> \<open>lift \<open>Trans\<close> through \<open>Red\<close> to the slice\<close>
  have tr: "Trans ?S = Trans ?N"
    by (rule Trans_slice_eq_Red[OF MR mlt j1le leM])
  show ?thesis using tr transN e1N0 e1N1 by simp
qed


text \<open>§7.4 keystone, the \<open>c\<^sub>0\<close> value at the boundary \<open>m = j\<^sub>1 - 1\<close> of the
  \<open>monoT\<close> stage: there \<open>m\<close> is the rightmost index of \<open>Pred M\<close>
  (\<open>m = Lng (Pred M) - 1\<close>), so the replaced surgery component
  \<open>c\<^sub>0 = Mark (Pred M) m\<close> collapses to the single principal term
  \<open>D\<^bsub>M\<^bsub>1,m\<^esub>\<^esub> 0\<close> by the rightmost-basepoint characterization
  (@{thm [source] m_7_3_Mark_rightmost1}).\<close>

lemma m_7_4_Mark_Pred_boundary:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS"
    and mj1: "m = Lng M - 2" and L: "1 < Lng M - 1"
  shows "Mark (Pred M) m = Dpt (enat (entry M 1 m)) 0\<^sub>B"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L1: "1 < Lng M" using L by linarith
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have pb: "Pred M = butlast M" using L1 by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using pb by simp
  have mlt: "m < Lng M - 1" using mj1 L by linarith
  \<comment> \<open>\<open>(Pred M, m) \<in> Marked\<close> and \<open>m\<close> is the rightmost index of \<open>Pred M\<close>\<close>
  have mP: "(Pred M, m) \<in> Marked" by (rule Marked_Pred[OF MT L1 mM mlt])
  have mlast: "m = Lng (Pred M) - 1" using LP mj1 L by linarith
  \<comment> \<open>\<open>Pred M\<close> is non-zero (\<open>Lng \<ge> 2\<close>)\<close>
  have nzP: "\<not> zeroT (Pred M)"
  proof -
    have "1 < Lng (Pred M)" using LP L by linarith
    thus ?thesis by (auto simp: zeroT_def)
  qed
  \<comment> \<open>rightmost-basepoint form of \<open>Mark (Pred M) m\<close>\<close>
  have rm: "Mark (Pred M) m = Dpt (enat (entry (Pred M) 1 m)) 0\<^sub>B"
    using m_7_3_Mark_rightmost1[OF mP predRT nzP] mlast by simp
  \<comment> \<open>row-1 entry survives \<open>butlast\<close> (\<open>m < Lng (Pred M)\<close>)\<close>
  have e1: "entry (Pred M) 1 m = entry M 1 m"
  proof -
    have "m < length (butlast M)" using LP mlast L by simp
    thus ?thesis using pb by (simp add: entry_def nth_butlast)
  qed
  show ?thesis using rm e1 by simp
qed


text \<open>§7.4 keystone, the \<open>monoT\<close> boundary case \<open>m = j\<^sub>1 - 1\<close> fully assembled.
  At the boundary the marked index \<open>m\<close> is itself the second basepoint
  \<open>transJm1 M\<close>: the row-0 parent of \<open>j\<^sub>1\<close> is \<open>m\<close> (adjacent, marked), and \<open>m\<close> is
  admissible (from \<open>Marked\<close>), so \<open>Adm M (parent M 0 j\<^sub>1) = m\<close>.  Hence
  @{thm [source] m_7_3_Mark_rightmost2} evaluates \<open>Mark M m = transC2 M\<close>, the
  two-column slice value @{thm [source] m_7_4_Trans_slice_2col} computes
  \<open>Trans (seg M m (Lng M - 1)) = D\<^bsub>M\<^bsub>1,m\<^esub>\<^esub> D\<^bsub>M\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0\<close>, and the two coincide
  because at the boundary \<open>c\<^sub>2 = transC2 M\<close> collapses to that same closed form
  (its \<open>c\<^sub>1 = Mark (Pred M) m = D\<^bsub>M\<^bsub>1,m\<^esub>\<^esub> 0\<close> by @{thm [source] m_7_4_Mark_Pred_boundary},
  so \<open>v = M\<^bsub>1,m\<^esub>\<close>, \<open>t\<^sub>2 = 0\<close>).\<close>

lemma m_7_4_Mark_Trans_repr_monoT_boundary:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mono: "monoT M"
    and mj1: "m = Lng M - 2" and L: "1 < Lng M - 1"
  shows "Mark M m = Trans (seg M m (Lng M - 1))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have MP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have L1: "1 < Lng M" using L by linarith
  let ?j1 = "Lng M - 1"
  \<comment> \<open>\<open>m = j\<^sub>1 - 1\<close>, adjacent to \<open>j\<^sub>1\<close>\<close>
  have mlt: "m < ?j1" using mj1 L by linarith
  have adj: "?j1 = Suc m" using mj1 L by linarith
  \<comment> \<open>\<open>(M, m) \<in> Marked\<close> gives \<open>adm M m\<close> and \<open>le0 M m j\<^sub>1\<close>\<close>
  have admM: "adm M m" using mM by (simp add: Marked_def)
  have leM: "leR M 0 m ?j1" using mM by (simp add: Marked_def)
  have le0m: "le0 M m ?j1" using leM by (simp add: leR_def)
  \<comment> \<open>row-0 parent of \<open>j\<^sub>1\<close> is \<open>m\<close>: adjacency gives \<open>nextrel0 M m j\<^sub>1\<close>, uniqueness from \<open>hasParent\<close>\<close>
  have nr0: "nextrel0 M m ?j1"
    using le0_adjacent_step[of M m] le0m adj by simp
  have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L1])
  have parj0: "parent M 0 ?j1 = m"
  proof -
    have ex1: "\<exists>!j. nextR M 0 j ?j1"
      using hp by (simp add: hasParent_def)
    have wit: "nextR M 0 m ?j1" using nr0 by (simp add: nextR_def)
    show ?thesis unfolding parent_def
      using the1_equality[OF ex1 wit] .
  qed
  \<comment> \<open>\<open>m\<close> is admissible, so \<open>Adm M (parent M 0 j\<^sub>1) = m\<close>, i.e. \<open>transJm1 M = m\<close>\<close>
  have transJm1eq: "transJm1 M = m"
    using admM parj0 by (simp add: transJm1_def transJ0_def transJ1_def Adm_def)
  \<comment> \<open>\<open>transJ1 M > 0\<close> and \<open>transT1 M \<noteq> 0\<close> (\<open>Pred M\<close> is non-zero since \<open>Lng \<ge> 3\<close>)\<close>
  have J1pos: "transJ1 M > 0" using L by (simp add: transJ1_def)
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have nzPred: "\<not> zeroT (Pred M)"
  proof -
    have "Lng (Pred M) = Lng M - 1" using L1 by (simp add: Pred_def)
    hence "1 < Lng (Pred M)" using L by linarith
    thus ?thesis by (auto simp: zeroT_def)
  qed
  have T1: "transT1 M \<noteq> 0\<^sub>B"
    using m_7_3_Trans_zeroT[OF predRT] nzPred by (simp add: transT1_def)
  \<comment> \<open>\<open>Mark M m = transC2 M\<close> via the second-basepoint evaluation\<close>
  have markC2: "Mark M m = transC2 M"
    using m_7_3_Mark_rightmost2[OF MR MP J1pos T1] transJm1eq by simp
  \<comment> \<open>\<open>transC2 M\<close> collapses to the closed two-column form\<close>
  have c0val: "Mark (Pred M) m = Dpt (enat (entry M 1 m)) 0\<^sub>B"
    by (rule m_7_4_Mark_Pred_boundary[OF mM MR mj1 L])
  have c1val: "transC1 M = Dpt (enat (entry M 1 m)) 0\<^sub>B"
    using c0val transJm1eq by (simp add: transC1_def)
  have vval: "transV M = enat (entry M 1 m)"
    using c1val by (simp add: transV_def)
  have t2val: "transT2 M = 0\<^sub>B"
    using c1val by (simp add: transT2_def)
  \<comment> \<open>\<open>j\<^sub>0 = m\<close> is admissible, so condition (I) or (III) fires (\<open>transCondV\<close>/(VI) too land here)\<close>
  have admj0: "adm M (transJ0 M)"
    using admM parj0 by (simp add: transJ0_def transJ1_def)
  have c2val: "transC2 M
      = Dpt (enat (entry M 1 m)) (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
  proof (cases "transCondI M \<or> transCondIII M \<or> transCondV M")
    case True
    have "transC2 M = Dpt (transV M) (transT2 M +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
      unfolding transC2_def Let_def transJ1_def using True by simp
    thus ?thesis using vval t2val by simp
  next
    case notIIIV: False
    show ?thesis
    proof (cases "transCondVI M")
      case True
      have "transC2 M = Dpt (transV M) (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
        unfolding transC2_def Let_def transJ1_def using notIIIV True by simp
      thus ?thesis using vval by simp
    next
      case notVI: False
      \<comment> \<open>this branch is impossible: at the boundary (I)/(III)/(VI) always fires\<close>
      have condA: "RedCondA M" using m_6_6_reduced_iff_cond[OF MT] MR by auto
      \<comment> \<open>\<open>\<not> (I)\<close> with \<open>adm\<close> forces \<open>b > 0\<close>; \<open>\<not> (III)\<close> forces \<open>v\<^sub>p < b\<close>\<close>
      have bpos: "entry M 1 ?j1 > 0"
      proof (rule ccontr)
        assume "\<not> entry M 1 ?j1 > 0"
        hence "entry M 1 ?j1 = 0" by simp
        hence "transCondI M" using admj0 by (simp add: transCondI_def transJ0_def transJ1_def)
        thus False using notIIIV by blast
      qed
      have vplt: "entry M 1 m < entry M 1 ?j1"
      proof (rule ccontr)
        assume "\<not> entry M 1 m < entry M 1 ?j1"
        hence ge: "entry M 1 (parent M 0 ?j1) \<ge> entry M 1 ?j1" using parj0 by simp
        hence "transCondIII M" using bpos admj0
          by (simp add: transCondIII_def transJ0_def transJ1_def)
        thus False using notIIIV by blast
      qed
      \<comment> \<open>row-1 next-relation \<open>m \<rightarrow> j\<^sub>1\<close> (valley trivial: no index strictly between)\<close>
      have mltL: "m < Lng M" using mlt L1 by linarith
      have j1ltL: "?j1 < Lng M" using L1 by linarith
      have valley: "\<forall>j. m < j \<and> le0 M j ?j1 \<longrightarrow> entry M 1 j \<ge> entry M 1 ?j1"
      proof (intro allI impI)
        fix j assume h: "m < j \<and> le0 M j ?j1"
        have "(nextrel0 M)\<^sup>*\<^sup>* j ?j1" using h by (simp add: le0_def)
        hence "j \<le> ?j1" by (rule nextrel0_rtrancl_mono)
        moreover have "m < j" using h by simp
        ultimately have "j = ?j1" using adj by linarith
        thus "entry M 1 j \<ge> entry M 1 ?j1" by simp
      qed
      have nr1: "nextrel1 M m ?j1"
        unfolding nextrel1_def
        using mltL j1ltL mlt vplt le0m valley by blast
      have wit1: "nextR M 1 m ?j1" using nr1 by (simp add: nextR_def)
      have uniq: "\<And>j. nextR M 1 j ?j1 \<Longrightarrow> j = m"
      proof -
        fix j assume "nextR M 1 j ?j1"
        hence nj: "nextrel1 M j ?j1" by (simp add: nextR_def)
        show "j = m"
        proof (rule ccontr)
          assume jne: "j \<noteq> m"
          have jlt: "j < ?j1" using nj by (simp add: nextrel1_def)
          have "j < m \<or> m < j" using jne by linarith
          thus False
          proof
            assume "m < j" thus False using jlt adj by linarith
          next
            assume jm: "j < m"
            \<comment> \<open>then \<open>m\<close> lies strictly between \<open>j\<close> and \<open>j\<^sub>1\<close> with \<open>le0 M m j\<^sub>1\<close>,\<close>
            \<comment> \<open>so the \<open>nextrel1\<close> valley at \<open>j\<close> forces \<open>entry M 1 m \<ge> entry M 1 j\<^sub>1\<close>\<close>
            have "j < m \<and> le0 M m ?j1" using jm le0m by simp
            hence "entry M 1 m \<ge> entry M 1 ?j1"
              using nj by (simp add: nextrel1_def)
            thus False using vplt by simp
          qed
        qed
      qed
      have ex1: "\<exists>!j. nextR M 1 j ?j1"
      proof (rule ex1I)
        show "nextR M 1 m ?j1" by (rule wit1)
      next
        fix j assume "nextR M 1 j ?j1" thus "j = m" by (rule uniq)
      qed
      have hp1: "hasParent M 1 ?j1"
        unfolding hasParent_def by (rule ex1)
      have par1: "parent M 1 ?j1 = m"
        unfolding parent_def by (rule the1_equality[OF ex1 wit1])
      \<comment> \<open>RedCondA at the row-1 parent: \<open>entry M 1 m + 1 = entry M 1 j\<^sub>1\<close>\<close>
      have step: "entry M 1 (parent M 1 ?j1) + 1 = entry M 1 ?j1"
        using condA[unfolded RedCondA_def, rule_format, of 1 ?j1] hp1 by simp
      have vp1: "entry M 1 m + 1 = entry M 1 ?j1" using step par1 by simp
      have "transCondVI M"
        unfolding transCondVI_def transJ0_def transJ1_def
        using bpos vp1 parj0 adj by simp
      thus ?thesis using notVI by blast
    qed
  qed
  \<comment> \<open>the slice's \<open>Trans\<close> is the same closed form\<close>
  have rhs: "Trans (seg M m ?j1)
      = Dpt (enat (entry M 1 m)) (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
    by (rule m_7_4_Trans_slice_2col[OF mM MR mj1 L])
  show ?thesis using markC2 c2val rhs by simp
qed


text \<open>§7.4 keystone, \<open>monoT\<close> interior helper (1): the predecessor of the
  reduced slice \<open>N = Red (seg M m j\<^sub>1)\<close> is the reduction of the shorter slice
  \<open>seg M m (j\<^sub>1 - 1)\<close>.  Combines \<open>Pred (seg M m j\<^sub>1) = seg M m (j\<^sub>1 - 1)\<close> (a
  \<open>butlast\<close>/\<open>seg\<close> computation, valid for \<open>m < j\<^sub>1\<close>) with the \<open>Red\<close>/\<open>Pred\<close>
  commutativity @{thm [source] m_6_5_Red_Pred}.\<close>

lemma m_7_4_Pred_Red_slice:
  assumes mj1: "m < j1"
  shows "Pred (Red (seg M m j1)) = Red (seg M m (j1 - 1))"
proof -
  let ?S = "seg M m j1"
  have LS: "Lng ?S = Suc j1 - m" by simp
  have LSgt1: "1 < Lng ?S" using mj1 by simp
  have segne: "?S \<noteq> []" using LSgt1 by (cases ?S) auto
  have ST: "?S \<in> T_PS" using segne by (simp add: T_PS_def)
  \<comment> \<open>\<open>Pred (seg M m j\<^sub>1) = butlast (seg M m j\<^sub>1) = seg M m (j\<^sub>1 - 1)\<close>\<close>
  have predseg: "Pred ?S = seg M m (j1 - 1)"
  proof -
    have pb: "Pred ?S = butlast ?S" using LSgt1 by (simp add: Pred_def)
    have Lbut: "Lng (butlast (seg M m j1)) = Suc (j1 - 1) - m" using mj1 by simp
    have "butlast (seg M m j1) = seg M m (j1 - 1)"
    proof (rule nth_equalityI)
      show "length (butlast (seg M m j1)) = length (seg M m (j1 - 1))"
        using mj1 by simp
    next
      fix i assume "i < length (butlast (seg M m j1))"
      hence ilt: "i < j1 - m" using mj1 by simp
      have lhs: "butlast (seg M m j1) ! i = seg M m j1 ! i"
        using ilt by (simp add: nth_butlast)
      have a: "seg M m j1 ! i = M ! (m + i)"
        using ilt unfolding seg_def by (simp del: upt_Suc)
      have b: "seg M m (j1 - 1) ! i = M ! (m + i)"
        using ilt mj1 unfolding seg_def by (simp del: upt_Suc)
      show "butlast (seg M m j1) ! i = seg M m (j1 - 1) ! i"
        using lhs a b by simp
    qed
    thus ?thesis using pb by simp
  qed
  have "Pred (Red ?S) = Red (Pred ?S)" by (rule m_6_5_Red_Pred[OF ST, symmetric])
  also have "\<dots> = Red (seg M m (j1 - 1))" using predseg by simp
  finally show ?thesis .
qed


text \<open>§7.4 keystone, \<open>monoT\<close> interior helper (2): the \<open>Trans\<close> of the predecessor
  of the reduced slice \<open>N = Red (seg M m j\<^sub>1)\<close> equals the \<open>Trans\<close> of the shorter
  slice \<open>seg M m (j\<^sub>1 - 1) = seg M m (Lng M - 2)\<close> (= \<open>transT1 N\<close> readback).
  Uses helper (1) and @{thm [source] Trans_slice_eq_Red} on the \<open>[m, j\<^sub>1-1]\<close> slice.
  IH-free.\<close>

lemma m_7_4_Trans_PredN:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
  shows "Trans (Pred (Red (seg M m (Lng M - 1)))) = Trans (seg M m (Lng M - 2))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  let ?j1 = "Lng M - 1"
  have L: "2 < Lng M" using mint by linarith
  have mj1: "m < ?j1" using mint by linarith
  \<comment> \<open>helper (1): \<open>Pred N = Red (seg M m (j\<^sub>1 - 1))\<close>\<close>
  have predN: "Pred (Red (seg M m ?j1)) = Red (seg M m (?j1 - 1))"
    by (rule m_7_4_Pred_Red_slice[OF mj1])
  have j1m1: "?j1 - 1 = Lng M - 2" by simp
  \<comment> \<open>\<open>leR M 0 m (j\<^sub>1 - 1)\<close> by descending the endpoint of \<open>leR M 0 m j\<^sub>1\<close>\<close>
  have leM: "leR M 0 m ?j1" using mM by (simp add: Marked_def)
  have leM': "leR M 0 m (?j1 - 1)"
    by (rule m_5_1_ancestor_tree_1[OF MT leM]) (use mint in linarith)+
  have mlt': "m < ?j1 - 1" using mint by linarith
  have j1le': "?j1 - 1 \<le> Lng M - 1" by simp
  \<comment> \<open>\<open>Trans (Red (seg M m (j\<^sub>1-1))) = Trans (seg M m (j\<^sub>1-1))\<close>\<close>
  have tr: "Trans (seg M m (?j1 - 1)) = Trans (Red (seg M m (?j1 - 1)))"
    by (rule Trans_slice_eq_Red[OF MR mlt' j1le' leM'])
  have "Trans (Pred (Red (seg M m ?j1))) = Trans (Red (seg M m (?j1 - 1)))"
    using predN by simp
  also have "\<dots> = Trans (seg M m (?j1 - 1))" using tr by simp
  also have "\<dots> = Trans (seg M m (Lng M - 2))" using j1m1 by simp
  finally show ?thesis .
qed


text \<open>§7.4 keystone, \<open>monoT\<close> interior helper (3): a backward slice of \<open>Pred M\<close>
  that ends strictly before the last column of \<open>M\<close> coincides with the same
  slice of \<open>M\<close> (the dropped last entry is past the slice).  \<open>a \<le> b < Lng M - 1\<close>.\<close>

lemma m_7_4_seg_Pred_eq:
  assumes L: "1 < Lng M" and ab: "a \<le> b" and blt: "b < Lng M - 1"
  shows "seg (Pred M) a b = seg M a b"
proof (rule nth_equalityI)
  have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using pb by simp
  show "length (seg (Pred M) a b) = length (seg M a b)" by simp
next
  have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
  fix i assume "i < length (seg (Pred M) a b)"
  hence ilt: "i < Suc b - a" by simp
  have ai: "a + i \<le> b" using ilt ab by linarith
  have abound: "a + i < Lng M - 1" using ai blt by linarith
  have lhs: "seg (Pred M) a b ! i = Pred M ! (a + i)"
    using ilt unfolding seg_def by (simp del: upt_Suc)
  also have "\<dots> = M ! (a + i)"
    using pb abound by (simp add: nth_butlast)
  also have "\<dots> = seg M a b ! i"
    using ilt unfolding seg_def by (simp del: upt_Suc)
  finally show "seg (Pred M) a b ! i = seg M a b ! i" .
qed


text \<open>§7.4 keystone, \<open>monoT\<close> interior identity (1): \<open>c\<^sub>0\<^bsup>M\<^esup> = transT1 N\<close>,
  i.e. \<open>Mark (Pred M) m = Trans (Pred N)\<close> where \<open>N = Red (seg M m (Lng M-1))\<close>.
  Takes the keystone instantiated at \<open>Pred M\<close> (the strong-induction hypothesis,
  passed verbatim) and chains it through helpers (2),(3):
  \<open>Mark (Pred M) m = Trans (seg (Pred M) m (Lng (Pred M)-1))
       = Trans (seg M m (Lng M-2)) = Trans (Pred N)\<close>.  Empirically exact
  (repr3/repr4: 0 violations on monoT interior \<open>0<m<j\<^sub>1-1\<close>).\<close>

lemma m_7_4_interior_id1:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and ihPred: "Mark (Pred M) m = Trans (seg (Pred M) m (Lng (Pred M) - 1))"
  shows "Mark (Pred M) m = Trans (Pred (Red (seg M m (Lng M - 1))))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  let ?j1 = "Lng M - 1"
  have L: "2 < Lng M" using mint by linarith
  have L1: "1 < Lng M" using L by linarith
  have pb: "Pred M = butlast M" using L1 by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using pb by simp
  have LPm1: "Lng (Pred M) - 1 = Lng M - 2" using LP by simp
  \<comment> \<open>the slice of \<open>Pred M\<close> equals the slice of \<open>M\<close> (helper (3))\<close>
  have mle: "m \<le> Lng M - 2" using mint by linarith
  have blt: "(Lng M - 2) < Lng M - 1" using L by linarith
  have segP: "seg (Pred M) m (Lng (Pred M) - 1) = seg M m (Lng M - 2)"
    using m_7_4_seg_Pred_eq[OF L1 mle blt] LPm1 by simp
  \<comment> \<open>chain: IH on \<open>Pred M\<close> \<open>\<leadsto>\<close> slice \<open>\<leadsto>\<close> helper (2)\<close>
  have a: "Mark (Pred M) m = Trans (seg M m (Lng M - 2))"
    using ihPred segP by simp
  have b: "Trans (Pred (Red (seg M m ?j1))) = Trans (seg M m (Lng M - 2))"
    by (rule m_7_4_Trans_PredN[OF mM MR mint])
  show ?thesis using a b by simp
qed

end

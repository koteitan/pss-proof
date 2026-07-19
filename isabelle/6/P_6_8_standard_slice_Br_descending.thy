theory P_6_8_standard_slice_Br_descending
  imports Support_6_024
begin

subsection \<open>§6.8 降順性\<close>

text \<open>命題（標準形の切片と\<open>Br\<close>の降順性の関係）.\<close>

text \<open>m: 命題（標準形の切片と \<open>Br\<close> の降順性の関係） — the article's WLOG-monoT reduction
  (content.md 1434).  For a general standard \<open>M\<close> the slice \<open>(M\<^sub>j)\<^bsub>j=j'\<^sub>0\<^esub>\<^bsup>j'\<^sub>1\<^esup>\<close> with
  \<open>(0,j'\<^sub>0) \<le>\<^sub>M (0,j'\<^sub>1)\<close> is reduced to the monoT case @{thm [source]
  m_6_8_slice_Br_descending_monoT}.  By the article: \<open>M\<close> may be taken non-multi, i.e.
  monoT (the \<open>j'\<^sub>0 < j'\<^sub>1\<close> hypothesis rules out zeroT).  Mechanically: pick \<open>k\<close> with
  \<open>M \<in> S\<^sub>kT_PS\<close>; if \<open>M\<close> is monoT apply the core directly; if \<open>M\<close> is multi, the row-0
  ancestry \<open>(0,j'\<^sub>0) \<le>\<^sub>M (0,j'\<^sub>1)\<close> CONFINES the slice to the single \<open>P\<close>-component \<open>K\<close>
  containing \<open>j'\<^sub>1\<close> (the component's left end \<open>a\<close> is a row-0 local minimum, so
  \<open>j'\<^sub>0 < a\<close> would force \<open>entry M 0 j'\<^sub>0 \<ge> entry M 0 a\<close> while ancestry forces
  \<open>entry M 0 j'\<^sub>0 < entry M 0 a\<close>; hence \<open>a \<le> j'\<^sub>0\<close>).  That component is monoT and
  standard (\<open>P\<close>-components of a standard form are non-multi and standard,
  @{thm [source] m_6_2_P_components_1}, @{thm [source] m_6_7_standard_P_components}),
  the slice equals a slice of it (@{thm [source] seg_of_seg}) with \<open>le0\<close> transferred
  (@{thm [source] adm_le0_seg}), and the core applies to it.  Discharges
  @{text p_6_8_standard_slice_Br_descending}.\<close>

lemma m_6_8_standard_slice_Br_descending:
  assumes M: "M \<in> ST_PS" and lt: "j0' < j1'" and j1: "j1' \<le> Lng M - 1"
    and leR: "leR M 0 j0' j1'"
  shows "monoT (seg M j0' j1') \<and> descending (Br (seg M j0' j1'))"
proof
  have MT: "M \<in> T_PS" by (rule ST_PS_T_PS[OF M])
  show "monoT (seg M j0' j1')" by (rule m_6_2_mono_ancestor_slice[OF MT lt leR])
next
  \<comment> \<open>obtain the rank \<open>k\<close> with \<open>M \<in> S\<^sub>kT_PS\<close> from \<open>ST_PS = \<Union>\<^sub>k S\<^sub>kT_PS\<close>\<close>
  have MT: "M \<in> T_PS" by (rule ST_PS_T_PS[OF M])
  obtain k where MS: "M \<in> SkT_PS k"
    using M m_6_7_ST_eq_Union_SkT by blast
  have jM: "j1' < Lng M" using j1 lt by linarith
  have le0M: "le0 M j0' j1'" using leR by (simp add: leR_def)
  show "descending (Br (seg M j0' j1'))"
  proof (cases "monoT M")
    case True
    \<comment> \<open>\<open>M\<close> non-multi: apply the monoT core directly\<close>
    show ?thesis by (rule m_6_8_slice_Br_descending_monoT[OF MS True lt j1 leR])
  next
    case notmono: False
    \<comment> \<open>then \<open>M\<close> is multi (\<open>zeroT M\<close> would give \<open>Lng M = 1\<close>, contradicting \<open>j'\<^sub>0 < j'\<^sub>1\<close>)\<close>
    have notzero: "\<not> zeroT M"
    proof
      assume "zeroT M"
      hence "Lng M = 1" by (simp add: zeroT_def)
      thus False using lt j1 by linarith
    qed
    \<comment> \<open>locate the \<open>P\<close>-component \<open>K\<close> containing \<open>j'\<^sub>1\<close>\<close>
    have total: "IdxSum (P M) ! (length (P M)) = Lng M"
    proof -
      have "IdxSum (P M) ! (length (P M)) = sum_list (map length (P M))"
        by (simp add: idxsum_nth)
      also have "\<dots> = length (concat (P M))" by (simp add: length_concat)
      also have "concat (P M) = M" by (rule idxsum_concat_P)
      finally show ?thesis by simp
    qed
    have jlt: "j1' < IdxSum (P M) ! (length (P M))" using jM total by simp
    obtain K where K1: "K < length (P M)"
      and K2: "IdxSum (P M) ! K \<le> j1'"
      and K3: "j1' < IdxSum (P M) ! (K + 1)"
      using idxsum_locate[OF jlt] by blast
    let ?a = "IdxSum (P M) ! K"
    let ?b = "IdxSum (P M) ! (K + 1) - 1"
    have almin: "\<forall>j' < ?a. entry M 0 j' \<ge> entry M 0 ?a"
      using idxsum_leftend_lmin[OF MT K1] by blast
    \<comment> \<open>CONFINEMENT: the left end \<open>?a\<close> of \<open>j'\<^sub>1\<close>'s component is \<open>\<le> j'\<^sub>0\<close>\<close>
    have aj0: "?a \<le> j0'"
    proof (rule ccontr)
      assume "\<not> ?a \<le> j0'"
      hence j0a: "j0' < ?a" by simp
      have aj1: "?a \<le> j1'" using K2 by simp
      have "entry M 0 j0' < entry M 0 ?a"
        by (rule m_5_1_ancestor_basic_1[OF MT j0a aj1 leR])
      moreover have "entry M 0 ?a \<le> entry M 0 j0'" using almin j0a by blast
      ultimately show False by simp
    qed
    \<comment> \<open>the component \<open>C = P M ! K = seg M ?a ?b\<close>: standard, monoT, and contains the slice\<close>
    have Kle: "K \<le> Lng (P M) - 1" using K1 by (cases "P M") auto
    have comp: "P M ! K = seg M ?a ?b" by (rule m_6_4_P_IdxSum[OF MT Kle])
    have lenpos: "0 < length (P M ! K)" by (rule idxsum_P_component_nonempty[OF MT K1])
    have diff: "IdxSum (P M) ! (K + 1) = ?a + length (P M ! K)" by (rule idxsum_diff[OF K1])
    have bge: "j1' \<le> ?b" using K3 diff lenpos by linarith
    have bL: "?b < Lng M"
    proof -
      have "IdxSum (P M) ! (K + 1) \<le> IdxSum (P M) ! (length (P M))"
        by (rule idxsum_mono[OF _ order.refl]) (use K1 in simp)
      hence "IdxSum (P M) ! (K + 1) \<le> Lng M" using total by simp
      thus ?thesis using lenpos diff by linarith
    qed
    \<comment> \<open>the component is in \<open>S\<^sub>kT_PS\<close>, hence standard, and monoT (length \<open>> 1\<close>)\<close>
    have CS: "P M ! K \<in> SkT_PS k"
      using m_6_7_standard_P_components[OF MS] K1 by (metis P_nonempty length_greater_0_conv
        Suc_le_lessD Suc_pred' Suc_le_eq Kle)
    have CT: "P M ! K \<in> T_PS" using CS SkT_PS_subset_ST_PS ST_PS_T_PS by blast
    have CinP: "P M ! K \<in> set (P M)" using K1 by (rule nth_mem)
    have Czm: "zeroT (P M ! K) \<or> monoT (P M ! K)"
      using m_6_2_P_components_1[OF MT] CinP by blast
    have ab: "?a \<le> ?b" using aj0 lt bge by linarith
    have a_lt_b: "?a < ?b" using aj0 lt bge by linarith
    have CL: "Lng (P M ! K) = Suc ?b - ?a" using comp by simp
    have Cgt1: "Lng (P M ! K) > 1" using a_lt_b CL by linarith
    have Cmono: "monoT (P M ! K)" using Czm Cgt1 by (auto simp: zeroT_def)
    \<comment> \<open>the slice equals a slice of the component\<close>
    have segeq: "seg M j0' j1' = seg (P M ! K) (j0' - ?a) (j1' - ?a)"
    proof -
      have dle: "j1' - ?a \<le> ?b - ?a" using bge by linarith
      have "seg (seg M ?a ?b) (j0' - ?a) (j1' - ?a) = seg M (?a + (j0' - ?a)) (?a + (j1' - ?a))"
        by (rule seg_of_seg[OF ab dle])
      hence "seg (P M ! K) (j0' - ?a) (j1' - ?a) = seg M (?a + (j0' - ?a)) (?a + (j1' - ?a))"
        using comp by simp
      also have "?a + (j0' - ?a) = j0'" using aj0 by simp
      also have "?a + (j1' - ?a) = j1'" using aj0 lt by simp
      finally show ?thesis by simp
    qed
    \<comment> \<open>transfer \<open>le0\<close> from \<open>M\<close> to the component (@{thm [source] adm_le0_seg})\<close>
    have aj1: "?a \<le> j1'" using K2 by simp
    have leneq0: "j0' - ?a \<le> ?b - ?a" using aj0 lt bge by linarith
    have leneq1: "j1' - ?a \<le> ?b - ?a" using bge by linarith
    have step: "le0 (seg M ?a ?b) (j0' - ?a) (j1' - ?a) = le0 M (?a + (j0' - ?a)) (?a + (j1' - ?a))"
      by (rule adm_le0_seg[OF bL leneq0 leneq1 ab])
    have e0: "?a + (j0' - ?a) = j0'" using aj0 by simp
    have e1: "?a + (j1' - ?a) = j1'" using aj0 lt by simp
    have "le0 (seg M ?a ?b) (j0' - ?a) (j1' - ?a)" using step le0M e0 e1 by simp
    hence le0C: "le0 (P M ! K) (j0' - ?a) (j1' - ?a)" using comp by simp
    hence leRC: "leR (P M ! K) 0 (j0' - ?a) (j1' - ?a)" by (simp add: leR_def)
    have ltC: "j0' - ?a < j1' - ?a" using aj0 lt by linarith
    have j1C: "j1' - ?a \<le> Lng (P M ! K) - 1" using bge CL aj0 lt by linarith
    have "descending (Br (seg (P M ! K) (j0' - ?a) (j1' - ?a)))"
      by (rule m_6_8_slice_Br_descending_monoT[OF CS Cmono ltC j1C leRC])
    thus ?thesis using segeq by simp
  qed
qed


lemma p_6_8_standard_slice_Br_descending:
  assumes "M \<in> ST_PS" "j0' < j1'" "j1' \<le> Lng M - 1" "leR M 0 j0' j1'"
  shows "monoT (seg M j0' j1') \<and> descending (Br (seg M j0' j1'))"
  using assms by (rule m_6_8_standard_slice_Br_descending)

end

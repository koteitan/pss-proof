theory Frontier_6_064
  imports Support_6_043
begin

section \<open>Front A (wf19) — GLUE: \<open>Lng N < Lng M\<close>, in-block transfer, and \<open>condA_top_all\<close>\<close>

text \<open>WF19 GLUE 1 (\<open>Lng N < Lng M\<close>).  For the in-block (\<open>J\<^sub>1>0\<close>) regime, the article
  applies the IH to the diagonal-prefixed
  \<open>N := (if 0 < R\<^sup>*\<^bsub>1,0\<^esub> then diagSeq 0 (R\<^sup>*\<^bsub>1,0\<^esub>-1) else []) @ R\<^sup>*\<close> of
  @{thm [source] wf15_inblock_N_core} (\<open>R\<^sup>* = Red (NJ M J\<^sup>*)\<close>).  We have
  \<open>Lng N = R\<^sup>*\<^bsub>1,0\<^esub> + Lng R\<^sup>*\<close> and \<open>Lng M = off + Lng R\<^sup>*\<close> (last-block start
  @{thm [source] wf16_inblock_parent_corr}), so \<open>Lng N < Lng M \<longleftrightarrow> R\<^sup>*\<^bsub>1,0\<^esub> < off\<close>.
  Now \<open>R\<^sup>*\<^bsub>1,0\<^esub> = npJ M J\<^sup>*\<close> (@{thm [source] m_6_6_Red_leftend_1},
  @{thm [source] entry_NJ_1_0}) and \<open>off = FirstNodes M ! J\<^sup>* = TrMax M + 1 + IdxSum (Br M) ! J\<^sup>*\<close>
  (@{thm [source] wf17_off_eq_firstnode}, @{thm [source] FirstNodes_nth}).  Two cases:
  \<^item> \<open>J\<^sup>* = 0\<close>: \<open>IdxSum (Br M) ! 0 = 0\<close>, \<open>off = TrMax M + 1\<close>, and \<open>npJ M 0 \<le> TrMax M\<close>
    (@{thm [source] s_npJ0_le_TrMax}), so \<open>npJ M 0 \<le> TrMax M < off\<close>.
  \<^item> \<open>J\<^sup>* > 0\<close>: \<open>IdxSum (Br M) ! J\<^sup>* \<ge> 1\<close> (the earlier branch \<open>Br M ! 0\<close> is nonempty),
    and \<open>npJ M J\<^sup>* \<le> Joints M ! J\<^sup>* + 1 \<le> TrMax M + 1\<close>
    (@{thm [source] npJ_le_Joints_Suc}, @{thm [source] m_6_4_FirstNodes_TrMax_Joints}),
    so \<open>npJ M J\<^sup>* \<le> TrMax M + 1 \<le> TrMax M + IdxSum (Br M) ! J\<^sup>* < off\<close>.
  EMPIRICALLY \<open>0/423\<close> reduced \<open>monoT\<close> cores (val \<le>3, len \<le>5; \<open>python/_wf19_probe.py\<close>).
  SOUND — cites only GREEN facts; never a \<open>p_*\<close> stub.\<close>

lemma wf19_IdxSum_pos:
  assumes M: "M \<in> PT_PS" and J: "J < Lng (Br M)" and Jpos: "0 < J"
  shows "0 < IdxSum (Br M) ! J"
proof -
  have Jle: "J \<le> length (Br M)" using J by simp
  have idx: "IdxSum (Br M) ! J = sum_list (map length (take J (Br M)))"
    by (rule idxsum_nth[OF Jle])
  have br0ne: "Br M ! 0 \<noteq> []" by (rule Br_component_nonempty[OF M]) (use J Jpos in linarith)
  \<comment> \<open>\<open>Br M ! 0\<close> is a member of \<open>take J (Br M)\<close> (its head, as \<open>0 < J\<close>).\<close>
  have br0in: "Br M ! 0 \<in> set (take J (Br M))"
  proof -
    have "Br M ! 0 = take J (Br M) ! 0" using Jpos J by simp
    moreover have "0 < length (take J (Br M))" using Jpos J by simp
    ultimately show ?thesis using nth_mem by metis
  qed
  have lenin: "length (Br M ! 0) \<in> set (map length (take J (Br M)))"
    using br0in by simp
  have le1: "length (Br M ! 0) \<le> sum_list (map length (take J (Br M)))"
    by (rule member_le_sum_list[OF lenin]) simp
  have pos1: "0 < length (Br M ! 0)" using br0ne by simp
  have "0 < sum_list (map length (take J (Br M)))" using le1 pos1 by linarith
  thus ?thesis using idx by simp
qed

lemma wf19_Lng_N_lt:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and nzNJ: "\<not> zeroT (NJ M (Lng (Br M) - 1))"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  defines "Rs \<equiv> Red (NJ M Jstar)"
  defines "N \<equiv> (if 0 < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs"
  shows "Lng N < Lng M"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  have JBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  have NJne: "NJ M Jstar \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M Jstar \<in> T_PS" using NJne by (simp add: T_PS_def)
  \<comment> \<open>\<open>Lng Rs = Lng (NJ M Jstar)\<close> and \<open>Lng M = off + Lng Rs\<close>.\<close>
  have lRs: "Lng Rs = Lng (NJ M Jstar)"
    unfolding Rs_def by (rule m_6_5_Lng_Red[OF NJT])
  define off where "off \<equiv> Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J))) [0..<Jstar]))"
  note B16 = wf16_inblock_parent_corr[OF M mono e00 e10 tne]
  have Leq: "Lng M - 1 = off + (Lng (NJ M Jstar) - 1)"
    using conjunct1[OF B16] unfolding off_def Jstar_def by simp
  have NJpos: "0 < Lng (NJ M Jstar)" using NJne by (cases "NJ M Jstar") auto
  have LM: "Lng M = off + Lng (NJ M Jstar)"
    using Leq NJpos MT by (cases M) (auto simp: T_PS_def)
  \<comment> \<open>\<open>off = FirstNodes M ! Jstar = TrMax M + 1 + IdxSum (Br M) ! Jstar\<close>.\<close>
  have offFN: "off = FirstNodes M ! Jstar"
    unfolding off_def Jstar_def by (rule wf17_off_eq_firstnode[OF M mono e00 e10 tne])
  have offTr: "off = TrMax M + 1 + IdxSum (Br M) ! Jstar"
    using offFN FirstNodes_nth[OF JBr] by simp
  \<comment> \<open>\<open>entry Rs 1 0 = npJ M Jstar\<close>.\<close>
  have e1Rs: "entry Rs 1 0 = npJ M Jstar"
    unfolding Rs_def using m_6_6_Red_leftend_1[OF NJT] entry_NJ_1_0[of M Jstar] e10 by simp
  \<comment> \<open>\<open>npJ M Jstar < off\<close>.\<close>
  have npoff: "npJ M Jstar < off"
  proof (cases "Jstar = 0")
    case True
    have np0: "npJ M 0 \<le> TrMax M" by (rule s_npJ0_le_TrMax[OF Mpt e10 brne])
    have "IdxSum (Br M) ! 0 = sum_list (map length (take 0 (Br M)))"
      by (rule idxsum_nth) simp
    hence idx0: "IdxSum (Br M) ! Jstar = 0" using True by simp
    show ?thesis using np0 offTr idx0 True by simp
  next
    case False
    hence Jpos: "0 < Jstar" by simp
    have idxpos: "0 < IdxSum (Br M) ! Jstar"
      by (rule wf19_IdxSum_pos[OF Mpt JBr Jpos])
    have nple: "npJ M Jstar \<le> Joints M ! Jstar + 1"
      by (rule npJ_le_Joints_Suc[OF Mpt e10 JBr])
    have jle: "Joints M ! Jstar \<le> TrMax M"
      using m_6_4_FirstNodes_TrMax_Joints[OF Mpt JBr] by simp
    show ?thesis using nple jle idxpos offTr by linarith
  qed
  \<comment> \<open>\<open>Lng N = entry Rs 1 0 + Lng Rs\<close>.\<close>
  have LN: "Lng N = entry Rs 1 0 + Lng Rs"
  proof (cases "0 < entry Rs 1 0")
    case True
    have "N = diagSeq 0 (entry Rs 1 0 - 1) @ Rs" unfolding N_def using True by simp
    hence "Lng N = Lng (diagSeq 0 (entry Rs 1 0 - 1)) + Lng Rs" by simp
    also have "\<dots> = (Suc (entry Rs 1 0 - 1) - 0) + Lng Rs" by simp
    also have "\<dots> = entry Rs 1 0 + Lng Rs" using True by simp
    finally show ?thesis .
  next
    case False
    hence "N = Rs" unfolding N_def by simp
    thus ?thesis using False by simp
  qed
  \<comment> \<open>Combine: \<open>Lng N = npJ + Lng Rs < off + Lng Rs = Lng M\<close>.\<close>
  show ?thesis using LN e1Rs npoff lRs LM by linarith
qed


text \<open>WF19 GLUE 2 (in-block entry transfer at an arbitrary in-block column).  From
  @{thm [source] wf16_inblock_parent_corr}'s \<open>drop off M = (IncrFirst ^^ ee) Rs\<close>,
  every in-block column \<open>off + c\<close> (\<open>c < Lng Rs\<close>) reads the block value:
  \<open>entry M 0 (off+c) = entry Rs 0 c + ee\<close>, \<open>entry M 1 (off+c) = entry Rs 1 c\<close>
  (@{thm [source] incf_pow_entry0}, @{thm [source] incf_pow_entry1}).  SOUND.\<close>

lemma wf19_inblock_entry:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  defines "ee \<equiv> Joints M ! Jstar + 1 - npJ M Jstar"
  defines "off \<equiv> Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J))) [0..<Jstar]))"
  defines "Rs \<equiv> Red (NJ M Jstar)"
  assumes cLng: "c < Lng Rs"
  shows "entry M 0 (off + c) = entry Rs 0 c + ee
       \<and> entry M 1 (off + c) = entry Rs 1 c"
proof -
  note B16 = wf16_inblock_parent_corr[OF M mono e00 e10 tne]
  have dropoff: "drop off M = (IncrFirst ^^ ee) Rs"
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF B16]]]]
    unfolding off_def Jstar_def ee_def Rs_def by simp
  have LM: "Lng M - 1 = off + (Lng (NJ M Jstar) - 1)"
    using conjunct1[OF B16] unfolding off_def Jstar_def by simp
  have lRs: "Lng Rs = Lng (NJ M Jstar)"
  proof -
    have NJne: "NJ M Jstar \<noteq> []" by (simp add: NJ_def)
    hence "NJ M Jstar \<in> T_PS" by (simp add: T_PS_def)
    thus ?thesis unfolding Rs_def by (rule m_6_5_Lng_Red)
  qed
  have NJpos: "0 < Lng (NJ M Jstar)"
  proof -
    have "NJ M Jstar \<noteq> []" by (simp add: NJ_def)
    thus ?thesis by (cases "NJ M Jstar") auto
  qed
  have LMpos: "0 < Lng M"
  proof -
    have "M \<in> T_PS" using M by (simp add: RT_PS_def)
    thus ?thesis by (cases M) (auto simp: T_PS_def)
  qed
  have offc_lt: "off + c < Lng M"
    using cLng lRs LM NJpos LMpos by linarith
  \<comment> \<open>read \<open>M ! (off+c)\<close> from the dropped block.\<close>
  have Moffc: "M ! (off + c) = ((IncrFirst ^^ ee) Rs) ! c"
  proof -
    have "M ! (off + c) = drop off M ! c"
      using offc_lt by (simp add: add.commute)
    thus ?thesis using dropoff by simp
  qed
  have e0: "entry M 0 (off + c) = entry ((IncrFirst ^^ ee) Rs) 0 c"
    using Moffc by (simp add: entry_def)
  have e1: "entry M 1 (off + c) = entry ((IncrFirst ^^ ee) Rs) 1 c"
    using Moffc by (simp add: entry_def)
  have b0: "entry ((IncrFirst ^^ ee) Rs) 0 c = entry Rs 0 c + ee"
    by (rule incf_pow_entry0[OF cLng])
  have b1: "entry ((IncrFirst ^^ ee) Rs) 1 c = entry Rs 1 c"
    by (rule incf_pow_entry1[OF cLng])
  show ?thesis using e0 e1 b0 b1 by simp
qed


text \<open>WF19 GLUE 3 (in-block last-column \<open>condA\<close> closer).  For an in-block parent
  \<open>off \<le> p\<close> of the last column, GIVEN \<open>RedCondA Rs\<close> (supplied by the IH on the
  diagonal-prefixed \<open>N\<close> via @{thm [source] wf17_RedCondA_diag_tail}), the
  \<open>condA\<close> relation at the last column follows: @{thm [source] wf16_inblock_parent_corr}
  maps the M-parent edge to a \<open>Rs\<close>-parent edge at \<open>kk\<close>, \<open>RedCondA Rs\<close> gives the
  block-local relation \<open>entry Rs i (p-off) + 1 = entry Rs i kk\<close>, and the entry
  transfers (last column from @{thm [source] wf16_inblock_parent_corr}, parent
  column from @{thm [source] wf19_inblock_entry}) pull it back to \<open>M\<close> — the row-0
  \<open>+ee\<close> shift cancels.  SOUND.\<close>

lemma wf19_inblock_condA:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and rcaRs: "RedCondA (Red (NJ M (Lng (Br M) - 1)))"
    and i: "i \<le> 1"
    and hp: "hasParent M i (Lng M - 1)"
    and pge: "Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J)))
                              [0..<Lng (Br M) - 1]))
              \<le> parent M i (Lng M - 1)"
  shows "entry M i (parent M i (Lng M - 1)) + 1 = entry M i (Lng M - 1)"
proof -
  define Jstar where "Jstar \<equiv> Lng (Br M) - 1"
  define ee where "ee \<equiv> Joints M ! Jstar + 1 - npJ M Jstar"
  define off where "off \<equiv> Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J))) [0..<Jstar]))"
  define Rs where "Rs \<equiv> Red (NJ M Jstar)"
  define kk where "kk \<equiv> Lng (NJ M Jstar) - 1"
  define p where "p \<equiv> parent M i (Lng M - 1)"
  have pgeoff: "off \<le> p" using pge unfolding off_def p_def Jstar_def by simp
  have rcaRs': "RedCondA Rs" using rcaRs unfolding Rs_def Jstar_def .
  note B16 = wf16_inblock_parent_corr[OF M mono e00 e10 tne]
  \<comment> \<open>length identity and \<open>kk < Lng Rs\<close>.\<close>
  have Leq: "Lng M - 1 = off + kk"
    using conjunct1[OF B16] unfolding off_def Jstar_def kk_def by simp
  have kkLT: "kk < Lng Rs"
    using conjunct1[OF conjunct2[OF B16]] unfolding Rs_def Jstar_def kk_def by simp
  \<comment> \<open>parent \<open>p\<close> maps in-block to \<open>p - off = parent Rs i kk\<close>, with \<open>hasParent Rs i kk\<close>.\<close>
  have parcorr: "hasParent Rs i kk \<and> parent Rs i kk = p - off"
  proof -
    have hpM: "hasParent M i (Lng M - 1)" by (rule hp)
    have parM: "parent M i (Lng M - 1) = p" unfolding p_def ..
    have C5: "\<forall>i\<le>1. \<forall>p. off \<le> p \<longrightarrow> hasParent M i (Lng M - 1) \<longrightarrow> parent M i (Lng M - 1) = p
              \<longrightarrow> hasParent Rs i kk \<and> parent Rs i kk = p - off"
      using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF B16]]]]]]
      unfolding off_def Jstar_def Rs_def kk_def by simp
    show ?thesis using C5 i pgeoff hpM parM by blast
  qed
  have hpRs: "hasParent Rs i kk" using parcorr by simp
  have parRs: "parent Rs i kk = p - off" using parcorr by simp
  have c_lt: "p - off < Lng Rs"
  proof -
    obtain q where q: "nextR Rs i q kk" and uq: "\<And>r. nextR Rs i r kk \<Longrightarrow> r = q"
      using hpRs unfolding hasParent_def by blast
    have parq: "parent Rs i kk = q"
      unfolding parent_def using q uq by (rule the_equality)
    have qlt: "q < kk" using q unfolding nextR_def nextrel0_def nextrel1_def
      by (auto split: if_splits)
    have "p - off = q" using parRs parq by simp
    thus ?thesis using qlt kkLT by linarith
  qed
  \<comment> \<open>block-local \<open>condA\<close> relation at \<open>kk\<close> (from \<open>RedCondA Rs\<close>).\<close>
  have relRs: "entry Rs i (parent Rs i kk) + 1 = entry Rs i kk"
    using rcaRs' hpRs i unfolding RedCondA_def by blast
  hence relRs': "entry Rs i (p - off) + 1 = entry Rs i kk" using parRs by simp
  \<comment> \<open>entry transfers (both rows at the in-block parent column \<open>p = off + (p-off)\<close>).\<close>
  have poff: "off + (p - off) = p" using pgeoff by simp
  have c_lt': "p - off < Lng (Red (NJ M (Lng (Br M) - 1)))"
    using c_lt unfolding Rs_def Jstar_def .
  have T: "entry M 0 (off + (p - off)) = entry Rs 0 (p - off) + ee
         \<and> entry M 1 (off + (p - off)) = entry Rs 1 (p - off)"
    using wf19_inblock_entry[OF M mono e00 e10 tne c_lt']
    unfolding off_def Jstar_def ee_def Rs_def by simp
  have ep0: "entry M 0 p = entry Rs 0 (p - off) + ee"
    using conjunct1[OF T] poff by simp
  have ep1: "entry M 1 p = entry Rs 1 (p - off)"
    using conjunct2[OF T] poff by simp
  show ?thesis
  proof (cases "i = 0")
    case True
    have ej1: "entry M 0 (Lng M - 1) = entry Rs 0 kk + ee"
      using conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF
              conjunct2[OF conjunct2[OF conjunct2[OF B16]]]]]]]
      unfolding ee_def Jstar_def Rs_def kk_def by simp
    have "entry M 0 p + 1 = entry Rs 0 (p - off) + ee + 1" using ep0 by simp
    also have "\<dots> = (entry Rs 0 (p - off) + 1) + ee" by simp
    also have "\<dots> = entry Rs 0 kk + ee" using relRs' True by simp
    also have "\<dots> = entry M 0 (Lng M - 1)" using ej1 by simp
    finally show ?thesis unfolding p_def using True by simp
  next
    case False
    hence i1: "i = 1" using i by simp
    have ej1: "entry M 1 (Lng M - 1) = entry Rs 1 kk"
      using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF
              conjunct2[OF conjunct2[OF B16]]]]]]]
      unfolding Jstar_def Rs_def kk_def by simp
    have "entry M 1 p + 1 = entry Rs 1 (p - off) + 1" using ep1 by simp
    also have "\<dots> = entry Rs 1 kk" using relRs' i1 by simp
    also have "\<dots> = entry M 1 (Lng M - 1)" using ej1 by simp
    finally show ?thesis unfolding p_def using i1 by simp
  qed
qed


text \<open>WF19 GLUE 4 (row-0, \<open>kk>0\<close> ROUTING: the row-0 last-column parent is in-block).
  When \<open>kk = Lng (NJ M J\<^sup>*)-1 > 0\<close>, \<open>Lng Rs > 1\<close>, so the reduced \<open>monoT\<close> branch
  reduction \<open>Rs = Red (NJ M J\<^sup>*)\<close> has a row-0 parent of its own last column \<open>kk\<close>
  (@{thm [source] kfwd_monoT_hasParent_top}).  By the @{thm [source] wf16_inblock_parent_corr}
  \<open>nextR\<close>-correspondence (the \<open>\<longleftrightarrow>\<close> direction), that edge lifts to an in-block
  M-edge \<open>nextR M 0 (off + q) (Lng M-1)\<close>, so the unique row-0 M-parent of the last
  column is \<open>off + q \<ge> off\<close> — i.e. in-block.  This routes the row-0 \<open>kk>0\<close> case to
  @{thm [source] wf19_inblock_condA}.  EMPIRICALLY \<open>206/206\<close> in-block
  (\<open>python/_wf19_probe2.py\<close>).  SOUND.\<close>

lemma wf19_r0_kkpos_inblock:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and kkpos: "0 < Lng (NJ M (Lng (Br M) - 1)) - 1"
    and hp0: "hasParent M 0 (Lng M - 1)"
  shows "Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J)))
                              [0..<Lng (Br M) - 1]))
         \<le> parent M 0 (Lng M - 1)"
proof -
  define Jstar where "Jstar \<equiv> Lng (Br M) - 1"
  define off where "off \<equiv> Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J))) [0..<Jstar]))"
  define Rs where "Rs \<equiv> Red (NJ M Jstar)"
  define kk where "kk \<equiv> Lng (NJ M Jstar) - 1"
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  have JBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  have NJne: "NJ M Jstar \<noteq> []" by (simp add: NJ_def)
  have nm: "\<not> multiT (NJ M Jstar)" by (rule NJ_nonmulti[OF Mpt e00 e10 JBr])
  have kkp: "0 < kk" using kkpos unfolding kk_def Jstar_def by simp
  have nzNJ: "\<not> zeroT (NJ M Jstar)"
  proof -
    have "Lng (NJ M Jstar) \<noteq> 1" using kkp unfolding kk_def by linarith
    thus ?thesis by (simp add: zeroT_def)
  qed
  have monoNJ: "monoT (NJ M Jstar)" using nm nzNJ by (simp add: multiT_def)
  have NJT: "NJ M Jstar \<in> T_PS" using NJne by (simp add: T_PS_def)
  have NJPT: "NJ M Jstar \<in> PT_PS" using NJT monoNJ by (simp add: PT_PS_def)
  have monoRs: "monoT Rs" unfolding Rs_def by (rule m_6_5_Red_preserves_monoT[OF NJPT])
  have lRs: "Lng Rs = Lng (NJ M Jstar)" unfolding Rs_def by (rule m_6_5_Lng_Red[OF NJT])
  have NJpos: "0 < Lng (NJ M Jstar)" using NJne by (cases "NJ M Jstar") auto
  have RsT: "Rs \<in> T_PS"
  proof -
    have "0 < Lng Rs" using lRs NJpos by simp
    hence "Rs \<noteq> []" by (cases Rs) auto
    thus ?thesis by (simp add: T_PS_def)
  qed
  have LRs1: "1 < Lng Rs" using kkp lRs unfolding kk_def by linarith
  \<comment> \<open>\<open>kk = Lng Rs - 1\<close> is the last column of \<open>Rs\<close>; it has a row-0 parent.\<close>
  have kkeq: "kk = Lng Rs - 1" using lRs unfolding kk_def by simp
  have hpRs: "hasParent Rs 0 kk"
    using kfwd_monoT_hasParent_top[OF RsT monoRs LRs1] kkeq by simp
  obtain q where q: "nextR Rs 0 q kk" using hpRs unfolding hasParent_def by blast
  \<comment> \<open>lift the \<open>Rs\<close>-edge at \<open>kk\<close> to an in-block M-edge via wf16 conjunct (5).\<close>
  note B16 = wf16_inblock_parent_corr[OF M mono e00 e10 tne]
  have corr: "\<forall>i\<le>1. \<forall>p. off \<le> p \<longrightarrow>
                (nextR M i p (Lng M - 1) \<longleftrightarrow> nextR Rs i (p - off) kk)"
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF B16]]]]]
    unfolding off_def Jstar_def Rs_def kk_def by simp
  have iff0: "nextR M 0 (off + q) (Lng M - 1) \<longleftrightarrow> nextR Rs 0 ((off + q) - off) kk"
    using corr by simp
  have nM: "nextR M 0 (off + q) (Lng M - 1)"
    using iff0 q by simp
  \<comment> \<open>uniqueness of the row-0 M-parent of the last column.\<close>
  have uniqM: "\<And>r. nextR M 0 r (Lng M - 1) \<Longrightarrow> r = off + q"
    using nM by (blast intro: idxsum_parent0_unique)
  have exu: "\<exists>!r. nextR M 0 r (Lng M - 1)" using nM uniqM by blast
  have parM: "parent M 0 (Lng M - 1) = off + q"
    unfolding parent_def using nM by (rule the1_equality[OF exu])
  show ?thesis using parM unfolding off_def Jstar_def by simp
qed


text \<open>WF19 GLUE 5 (row-1, \<open>kk=0\<close> ROUTING: the branch row-1 head is nonzero).
  When \<open>kk = 0\<close> (singleton last block) and the last column has a ROW-1 parent, the
  last-column row-1 value \<open>entry M 1 (Lng M-1) = entry Rs 1 0 = npJ M J\<^sup>*\<close>
  (@{thm [source] wf16_inblock_parent_corr} row-1 conjunct, @{thm [source] m_6_6_Red_leftend_1},
  @{thm [source] entry_NJ_1_0}) is \<open>> 0\<close> (a row-1 parent strictly lowers the value),
  so \<open>npJ M J\<^sup>* \<noteq> 0\<close>, equivalently \<open>entry (Br M ! J\<^sup>*) 1 0 \<noteq> 0\<close> (\<^const>\<open>npJ\<close> def).
  This supplies the \<open>brnz\<close> side-condition of @{thm [source] wf17_crossblock_row1}.
  EMPIRICALLY \<open>0/123\<close> (\<open>brnz\<close> always holds when row-1 has a parent and \<open>kk=0\<close>).
  SOUND.\<close>

lemma wf19_brnz_of_r1_kk0:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and kk0: "Lng (NJ M (Lng (Br M) - 1)) = 1"
    and hp1: "hasParent M 1 (Lng M - 1)"
  shows "entry (Br M ! (Lng (Br M) - 1)) 1 0 \<noteq> 0"
proof -
  define Jstar where "Jstar \<equiv> Lng (Br M) - 1"
  define Rs where "Rs \<equiv> Red (NJ M Jstar)"
  define kk where "kk \<equiv> Lng (NJ M Jstar) - 1"
  have NJne: "NJ M Jstar \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M Jstar \<in> T_PS" using NJne by (simp add: T_PS_def)
  have kk0': "kk = 0" using kk0 unfolding kk_def Jstar_def by simp
  \<comment> \<open>last-column row-1 value reads the block left end.\<close>
  note B16 = wf16_inblock_parent_corr[OF M mono e00 e10 tne]
  have e1: "entry M 1 (Lng M - 1) = entry Rs 1 kk"
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF
            conjunct2[OF conjunct2[OF B16]]]]]]]
    unfolding Rs_def Jstar_def kk_def by simp
  have eRs0: "entry Rs 1 0 = npJ M Jstar"
    unfolding Rs_def using m_6_6_Red_leftend_1[OF NJT] entry_NJ_1_0[of M Jstar] e10 by simp
  have eval: "entry M 1 (Lng M - 1) = npJ M Jstar"
    using e1 eRs0 kk0' by simp
  \<comment> \<open>a row-1 parent strictly lowers the value, so the last-column value is \<open>> 0\<close>.\<close>
  obtain pp where pp: "nextR M 1 pp (Lng M - 1)"
    using hp1 unfolding hasParent_def by blast
  have "entry M 1 pp < entry M 1 (Lng M - 1)"
    using pp unfolding nextR_def nextrel1_def by simp
  hence vpos: "0 < entry M 1 (Lng M - 1)" by linarith
  have nppos: "0 < npJ M Jstar" using vpos eval by simp
  \<comment> \<open>\<open>npJ \<noteq> 0\<close> forces the \<^const>\<open>npJ\<close> else-branch, i.e. \<open>entry (Br M ! J\<^sup>*) 1 0 \<noteq> 0\<close>.\<close>
  show ?thesis
  proof (rule ccontr)
    assume "\<not> entry (Br M ! (Lng (Br M) - 1)) 1 0 \<noteq> 0"
    hence "entry (Br M ! Jstar) 1 0 = 0" unfolding Jstar_def by simp
    hence "npJ M Jstar = 0" by (simp add: npJ_def)
    thus False using nppos by simp
  qed
qed


text \<open>WF19 GLUE 6 (transfer \<open>RedCondA\<close> from the diagonal-prefixed \<open>N\<close> to \<open>Rs\<close>).
  The article \<open>N = (if 0 < R\<^sup>*\<^bsub>1,0\<^esub> then diagSeq 0 (R\<^sup>*\<^bsub>1,0\<^esub>-1) else []) @ R\<^sup>*\<close>
  (@{thm [source] wf15_inblock_N_core}); given \<open>RedCondA N\<close> (from the IH applied to
  the strictly-shorter \<open>N\<close>, @{thm [source] wf19_Lng_N_lt}), strip the diagonal
  prefix (@{thm [source] wf17_RedCondA_diag_tail}) to obtain \<open>RedCondA R\<^sup>*\<close>.  SOUND.\<close>

lemma wf19_RedCondA_Rs:
  assumes rcaN: "RedCondA ((if 0 < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs)"
  shows "RedCondA Rs"
proof (cases "0 < entry Rs 1 0")
  case True
  have "RedCondA (diagSeq 0 (entry Rs 1 0 - 1) @ Rs)" using rcaN True by simp
  thus ?thesis by (rule wf17_RedCondA_diag_tail)
next
  case False
  thus ?thesis using rcaN by simp
qed


text \<open>WF19 ASSEMBLY — the \<S>6.6 keystone forward (monoT core), reduced to the SINGLE
  residual row-1 cross-block \<open>kk>0\<close> relation \<open>r1cross\<close> (the value pin that Front B's
  \<open>wf19_valpin\<close> supplies; @{thm [source] wf18_crossblock_row1_kkpos} derives it from
  \<open>pTr + valpin\<close>).  All other last-column cases are CLOSED by the bricks:
  \<^item> \<open>j\<^sub>1' < Lng M - 1\<close>: \<open>Pred M\<close>-lift + IH (as in @{thm [source] kst_reduced_imp_condAB_monoT_core_cond});
  \<^item> \<open>kk = 0\<close> (cross): row-0 @{thm [source] wf17_crossblock_row0}, row-1
    @{thm [source] wf17_crossblock_row1} (its \<open>brnz\<close> from @{thm [source] wf19_brnz_of_r1_kk0});
  \<^item> \<open>kk > 0\<close> in-block: @{thm [source] wf19_inblock_condA} with \<open>RedCondA R\<^sup>*\<close> from the IH on
    the diagonal-prefixed \<open>N\<close> (@{thm [source] wf15_inblock_N_core}, @{thm [source] wf19_Lng_N_lt},
    @{thm [source] wf19_RedCondA_Rs}); row-0 \<open>kk>0\<close> is always in-block
    (@{thm [source] wf19_r0_kkpos_inblock}).
  \<^item> \<open>RedCondB\<close>: identical to the cond lemma (last column vacuous, below-last by Pred+IH).
  SOUND — cites only GREEN bricks and the explicit \<open>r1cross\<close> residual; no \<open>p_*\<close> stub,
  no goal self-citation.\<close>

lemma condAB_all_cond:
  assumes r1cross:
    "\<And>N. N \<in> RT_PS \<Longrightarrow> monoT N \<Longrightarrow> entry N 0 0 = 0 \<Longrightarrow> entry N 1 0 = 0
       \<Longrightarrow> TrMax N \<noteq> Lng N - 1
       \<Longrightarrow> 0 < Lng (NJ N (Lng (Br N) - 1)) - 1
       \<Longrightarrow> hasParent N 1 (Lng N - 1)
       \<Longrightarrow> parent N 1 (Lng N - 1) < FirstNodes N ! (Lng (Br N) - 1)
       \<Longrightarrow> entry N 1 (parent N 1 (Lng N - 1)) + 1 = entry N 1 (Lng N - 1)"
  assumes M0: "M \<in> RT_PS" and mono0: "monoT M"
    and e000: "entry M 0 0 = 0" and e100: "entry M 1 0 = 0"
  shows "RedCondA M \<and> RedCondB M"
  using M0 mono0 e000 e100
proof (induction M rule: measure_induct_rule[where f = Lng])
  case (less M)
  have M: "M \<in> RT_PS" by (rule less.prems(1))
  have mono: "monoT M" by (rule less.prems(2))
  have e00: "entry M 0 0 = 0" by (rule less.prems(3))
  have e10: "entry M 1 0 = 0" by (rule less.prems(4))
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  let ?j1 = "Lng M - 1"
  show ?case
  proof (cases "TrMax M = Lng M - 1")
    case True
    show ?thesis by (rule kfwd_reduced_core_trunk_condAB[OF M mono e00 e10 True])
  next
    case tne: False
    have trlt: "TrMax M < Lng M - 1" using TrMax_bound[OF MT] tne by linarith
    have L2: "1 < Lng M" using trlt LMpos by linarith
    define off where "off \<equiv> Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J))) [0..<Lng (Br M) - 1]))"
    define kkM where "kkM \<equiv> Lng (NJ M (Lng (Br M) - 1)) - 1"
    \<comment> \<open>--- RedCondA M ---\<close>
    have condA: "RedCondA M"
      unfolding RedCondA_def
    proof (intro allI impI)
      fix i j1' assume i: "i \<le> 1" and hp: "hasParent M i j1'"
      have j1L: "j1' < Lng M"
        using hp unfolding hasParent_def nextR_def nextrel0_def nextrel1_def
        by (auto split: if_splits)
      have par_lt: "parent M i j1' < j1'"
      proof -
        obtain q where q: "nextR M i q j1'"
          and uq: "\<And>r. nextR M i r j1' \<Longrightarrow> r = q"
          using hp unfolding hasParent_def by blast
        have "parent M i j1' = q"
          unfolding parent_def using q uq by (blast intro: the1_equality)
        moreover have "q < j1'" using q
          unfolding nextR_def nextrel0_def nextrel1_def by (auto split: if_splits)
        ultimately show ?thesis by simp
      qed
      show "entry M i (parent M i j1') + 1 = entry M i j1'"
      proof (cases "j1' = ?j1")
        case top: True
        have hpT: "hasParent M i ?j1" using hp top by simp
        \<comment> \<open>route on \<open>kk = 0\<close> vs \<open>kk > 0\<close>, then row / in-block / cross.\<close>
        show ?thesis
        proof (cases "kkM = 0")
          case kk0: True
          have kk0': "Lng (NJ M (Lng (Br M) - 1)) = 1"
          proof -
            have "NJ M (Lng (Br M) - 1) \<noteq> []" by (simp add: NJ_def)
            hence "0 < Lng (NJ M (Lng (Br M) - 1))" by (cases "NJ M (Lng (Br M) - 1)") auto
            thus ?thesis using kk0 unfolding kkM_def by linarith
          qed
          show ?thesis
          proof (cases "i = 0")
            case True
            have hp0: "hasParent M 0 ?j1" using hpT True by simp
            note R = wf17_crossblock_row0[OF M mono e00 e10 tne kk0' hp0]
            have parJ: "parent M 0 ?j1 = Joints M ! (Lng (Br M) - 1)"
              using conjunct1[OF R] by simp
            have eR: "entry M 0 ?j1 = entry M 0 (Joints M ! (Lng (Br M) - 1)) + 1"
              using conjunct2[OF R] by simp
            have "entry M 0 (parent M 0 ?j1) + 1 = entry M 0 (Joints M ! (Lng (Br M) - 1)) + 1"
              using parJ by simp
            also have "\<dots> = entry M 0 ?j1" using eR by simp
            finally show ?thesis using top True by simp
          next
            case False
            hence i1: "i = 1" using i by simp
            have hp1: "hasParent M 1 ?j1" using hpT i1 by simp
            have brnz: "entry (Br M ! (Lng (Br M) - 1)) 1 0 \<noteq> 0"
              by (rule wf19_brnz_of_r1_kk0[OF M mono e00 e10 tne kk0' hp1])
            note R = wf17_crossblock_row1[OF M mono e00 e10 tne kk0' brnz hp1]
            have npeq: "npJ M (Lng (Br M) - 1) = parent M 1 ?j1 + 1"
              using conjunct1[OF conjunct2[OF R]] by simp
            have epar: "entry M 1 (parent M 1 ?j1) = parent M 1 ?j1"
              using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF R]]]] by simp
            have ej1: "entry M 1 ?j1 = npJ M (Lng (Br M) - 1)"
              using conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF R]]]] by simp
            have "entry M 1 (parent M 1 ?j1) + 1 = parent M 1 ?j1 + 1" using epar by simp
            also have "\<dots> = npJ M (Lng (Br M) - 1)" using npeq by simp
            also have "\<dots> = entry M 1 ?j1" using ej1 by simp
            finally show ?thesis using top i1 by simp
          qed
        next
          case kkne: False
          have kkpos: "0 < Lng (NJ M (Lng (Br M) - 1)) - 1"
            using kkne unfolding kkM_def by simp
          \<comment> \<open>get \<open>RedCondA R\<^sup>*\<close> from the IH on the strictly-shorter diagonal-prefixed \<open>N\<close>.\<close>
          have nzNJ: "\<not> zeroT (NJ M (Lng (Br M) - 1))"
          proof -
            have "Lng (NJ M (Lng (Br M) - 1)) \<noteq> 1" using kkpos by linarith
            thus ?thesis by (simp add: zeroT_def)
          qed
          define Rs where "Rs \<equiv> Red (NJ M (Lng (Br M) - 1))"
          define N where "N \<equiv> (if 0 < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs"
          have Ncore: "Red N = N \<and> monoT N \<and> entry N 0 0 = 0 \<and> entry N 1 0 = 0
                     \<and> N = (if 0 < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs"
            using wf15_inblock_N_core[OF M mono e00 e10 tne nzNJ]
            unfolding Rs_def N_def by simp
          have NT: "N \<in> T_PS"
          proof -
            have "Rs \<noteq> []"
            proof -
              have "NJ M (Lng (Br M) - 1) \<noteq> []" by (simp add: NJ_def)
              hence "NJ M (Lng (Br M) - 1) \<in> T_PS" by (simp add: T_PS_def)
              hence "Lng Rs = Lng (NJ M (Lng (Br M) - 1))"
                unfolding Rs_def by (rule m_6_5_Lng_Red)
              moreover have "0 < Lng (NJ M (Lng (Br M) - 1))"
                by (simp add: NJ_def)
              ultimately show ?thesis by (cases Rs) auto
            qed
            hence "N \<noteq> []" unfolding N_def by simp
            thus ?thesis by (simp add: T_PS_def)
          qed
          have redN: "Red N = N" by (rule conjunct1[OF Ncore])
          have monoN: "monoT N" by (rule conjunct1[OF conjunct2[OF Ncore]])
          have eN00: "entry N 0 0 = 0" by (rule conjunct1[OF conjunct2[OF conjunct2[OF Ncore]]])
          have eN10: "entry N 1 0 = 0"
            by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF Ncore]]]])
          have NRT: "N \<in> RT_PS" using NT redN by (simp add: RT_PS_def)
          have NLlt: "Lng N < Lng M"
            using wf19_Lng_N_lt[OF M mono e00 e10 tne nzNJ] unfolding N_def Rs_def by simp
          have IHN: "RedCondA N \<and> RedCondB N"
            by (rule less.IH[OF NLlt NRT monoN eN00 eN10])
          have Neq: "N = (if 0 < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs"
            unfolding N_def ..
          have rcaN: "RedCondA ((if 0 < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs)"
            using IHN Neq by simp
          have rcaRs: "RedCondA Rs" by (rule wf19_RedCondA_Rs[OF rcaN])
          have rcaRs': "RedCondA (Red (NJ M (Lng (Br M) - 1)))" using rcaRs unfolding Rs_def .
          \<comment> \<open>in-block vs cross.\<close>
          show ?thesis
          proof (cases "off \<le> parent M i ?j1")
            case inb: True
            have rel: "entry M i (parent M i ?j1) + 1 = entry M i ?j1"
              by (rule wf19_inblock_condA[OF M mono e00 e10 tne rcaRs' i hpT])
                 (use inb in \<open>simp add: off_def\<close>)
            thus ?thesis using top by simp
          next
            case cross: False
            have pcross: "parent M i ?j1 < off" using cross by simp
            show ?thesis
            proof (cases "i = 0")
              case True
              \<comment> \<open>row-0 \<open>kk>0\<close> is ALWAYS in-block — contradiction with \<open>cross\<close>.\<close>
              have hp0: "hasParent M 0 ?j1" using hpT True by simp
              have "off \<le> parent M 0 ?j1"
                using wf19_r0_kkpos_inblock[OF M mono e00 e10 tne kkpos hp0]
                unfolding off_def by simp
              hence False using pcross True by simp
              thus ?thesis ..
            next
              case False
              hence i1: "i = 1" using i by simp
              have hp1: "hasParent M 1 ?j1" using hpT i1 by simp
              have pcr: "parent M 1 ?j1 < FirstNodes M ! (Lng (Br M) - 1)"
                using pcross i1 wf17_off_eq_firstnode[OF M mono e00 e10 tne]
                unfolding off_def by simp
              have "entry M 1 (parent M 1 ?j1) + 1 = entry M 1 ?j1"
                by (rule r1cross[OF M mono e00 e10 tne kkpos hp1 pcr])
              thus ?thesis using top i1 by simp
            qed
          qed
        qed
      next
        case below: False
        have jpos: "0 < j1'" using par_lt by linarith
        have jle: "j1' \<le> Lng M - 2" using j1L below by linarith
        have L3: "2 < Lng M" using jpos jle by linarith
        have predRT: "Pred M \<in> RT_PS" and predmono: "monoT (Pred M)"
          and pred00: "entry (Pred M) 0 0 = 0" and pred10: "entry (Pred M) 1 0 = 0"
          and predLlt: "Lng (Pred M) < Lng M"
          using ncons_Pred_core[OF M mono e00 e10 tne L3] by blast+
        have condA_pred: "RedCondA (Pred M)"
          using less.IH[OF predLlt predRT predmono pred00 pred10] by simp
        have hpP: "hasParent (Pred M) i j1'"
          using kfwd_hasParent_Pred_iff[OF MT L2 i jle] hp by simp
        have parP: "parent (Pred M) i j1' = parent M i j1'"
          by (rule kfwd_parent_Pred_eq[OF MT L2 i jle hp])
        have parle: "parent M i j1' \<le> Lng M - 2" using par_lt jle by linarith
        have relP: "entry (Pred M) i (parent (Pred M) i j1') + 1
                     = entry (Pred M) i j1'"
          using condA_pred hpP i unfolding RedCondA_def by blast
        have e_par: "entry (Pred M) i (parent M i j1') = entry M i (parent M i j1')"
          by (rule kfwd_entry_Pred_eq[OF L2 parle])
        have e_j1: "entry (Pred M) i j1' = entry M i j1'"
          by (rule kfwd_entry_Pred_eq[OF L2 jle])
        show ?thesis using relP parP e_par e_j1 by simp
      qed
    qed
    \<comment> \<open>--- RedCondB M (identical to the cond lemma) ---\<close>
    have condB: "RedCondB M"
      unfolding RedCondB_def
    proof (intro allI impI)
      fix j1' assume H: "\<not> hasParent M 0 j1' \<and> j1' \<le> Lng M - 1"
      hence noP: "\<not> hasParent M 0 j1'" and hle: "j1' \<le> Lng M - 1" by simp_all
      show "entry M 0 j1' = entry M 1 j1'"
      proof (cases "j1' = ?j1")
        case top: True
        have "hasParent M 0 ?j1" by (rule kfwd_monoT_hasParent_top[OF MT mono L2])
        thus ?thesis using noP top by simp
      next
        case below: False
        have jle: "j1' \<le> Lng M - 2" using hle below by linarith
        show ?thesis
        proof (cases "j1' = 0")
          case True
          show ?thesis using True e00 e10 by simp
        next
          case False
          have jpos: "0 < j1'" using False by simp
          have L3: "2 < Lng M" using jpos jle by linarith
          have predRT: "Pred M \<in> RT_PS" and predmono: "monoT (Pred M)"
            and pred00: "entry (Pred M) 0 0 = 0" and pred10: "entry (Pred M) 1 0 = 0"
            and predLlt: "Lng (Pred M) < Lng M"
            using ncons_Pred_core[OF M mono e00 e10 tne L3] by blast+
          have LP: "Lng (Pred M) = Lng M - 1" using L2 by (simp add: Pred_def length_butlast)
          have IHpred: "RedCondA (Pred M) \<and> RedCondB (Pred M)"
            by (rule less.IH[OF predLlt predRT predmono pred00 pred10])
          have noPP: "\<not> hasParent (Pred M) 0 j1'"
            using kfwd_hasParent_Pred_iff[OF MT L2 _ jle] noP by simp
          have hleP: "j1' \<le> Lng (Pred M) - 1" using jle LP by linarith
          have relB: "entry (Pred M) 0 j1' = entry (Pred M) 1 j1'"
            using IHpred noPP hleP unfolding RedCondB_def by blast
          have e0: "entry (Pred M) 0 j1' = entry M 0 j1'"
            by (rule kfwd_entry_Pred_eq[OF L2 jle])
          have e1: "entry (Pred M) 1 j1' = entry M 1 j1'"
            by (rule kfwd_entry_Pred_eq[OF L2 jle])
          show ?thesis using relB e0 e1 by simp
        qed
      qed
    qed
    show ?thesis using condA condB by blast
  qed
qed


text \<open>\<open>wf21_Br_eq_seg\<close>: the last branch block \<open>Br M ! Jstar\<close> is exactly the
  \<open>M\<close>-suffix \<open>seg M m (Lng M - 1)\<close> with \<open>m = FirstNodes M ! Jstar\<close>.  Hence
  \<open>entry (Br M ! Jstar) i t = entry M i (m + t)\<close> — the bridge for the entry
  transfers and the witness-edge preservation.  Truth-checked (red_model.py):
  46 reduced mono nontrunk cores (mono last branch), all satisfy
  \<open>Br M ! Jstar = seg M (FirstNodes M ! Jstar) (Lng M - 1)\<close>.\<close>

lemma wf21_Br_eq_seg:
  assumes M: "M \<in> PT_PS" and brne: "Br M \<noteq> []"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  shows "Br M ! Jstar = seg M (FirstNodes M ! Jstar) (Lng M - 1)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with brne show False by simp
  qed
  with TrMax_bound[OF MT] have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have NLpos: "0 < Lng ?N" using trlt by simp
  have Nne: "?N \<noteq> []" using NLpos length_greater_0_conv by blast
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  \<comment> \<open>\<open>Jstar\<close> is the last index of \<open>Br M = P ?N\<close>.\<close>
  have nBpos: "0 < Lng (Br M)" using brne by (cases "Br M") auto
  have JN: "Jstar < length (P ?N)" unfolding Jstar_def using nBpos brQ by simp
  have Jle: "Jstar \<le> Lng (P ?N) - 1" using JN by (cases "P ?N") auto
  have Jsuc: "Jstar + 1 = length (P ?N)"
    unfolding Jstar_def using nBpos brQ by simp
  \<comment> \<open>block = slice of \<open>?N\<close>.\<close>
  have comp: "(P ?N) ! Jstar
            = seg ?N (IdxSum (P ?N) ! Jstar) (IdxSum (P ?N) ! (Jstar + 1) - 1)"
    by (rule m_6_4_P_IdxSum[OF NT Jle])
  \<comment> \<open>right endpoint reaches the full length (cumulative sum at the end).\<close>
  have total: "IdxSum (P ?N) ! (length (P ?N)) = Lng ?N"
  proof -
    have "IdxSum (P ?N) ! (length (P ?N)) = sum_list (map length (take (length (P ?N)) (P ?N)))"
      by (simp add: idxsum_nth)
    also have "\<dots> = sum_list (map length (P ?N))" by simp
    also have "\<dots> = length (concat (P ?N))" by (simp add: length_concat)
    also have "concat (P ?N) = ?N" by (rule idxsum_concat_P)
    finally show ?thesis by simp
  qed
  have rb: "IdxSum (P ?N) ! (Jstar + 1) = Lng ?N" using total Jsuc by simp
  let ?a = "IdxSum (P ?N) ! Jstar"
  have blk: "Br M ! Jstar = seg ?N ?a (Lng ?N - 1)"
    using comp rb brQ by simp
  \<comment> \<open>compose the two suffix-segments via \<open>drop\<close>.\<close>
  have seg1: "?N = drop (TrMax M + 1) M"
    by (rule seg_to_last_eq_drop[OF LMpos])
  have seg2: "seg ?N ?a (Lng ?N - 1) = drop ?a ?N"
    by (rule seg_to_last_eq_drop[OF NLpos])
  have dd: "drop ?a ?N = drop (TrMax M + 1 + ?a) M"
    using seg1 by (simp add: drop_drop add.commute)
  have segM: "drop (TrMax M + 1 + ?a) M = seg M (TrMax M + 1 + ?a) (Lng M - 1)"
    by (rule seg_to_last_eq_drop[OF LMpos, symmetric])
  have fn: "FirstNodes M ! Jstar = TrMax M + 1 + ?a"
    using FirstNodes_nth[OF JN[unfolded brQ[symmetric]]] brQ by simp
  show ?thesis
    using blk seg2 dd segM fn by simp
qed

section \<open>Front A (wf22) — non-circular \<open>r1cross\<close> via M's TRUNK structure\<close>

text \<open>WF22 BRICK A (\<open>wf22_le0_off_last\<close>): the last branch block's left end \<open>off =
  FirstNodes M ! Jstar\<close> row-0-reaches the last column \<open>j\<^sub>1 = Lng M - 1\<close>.  The last
  block \<open>Br M ! Jstar = seg M off j\<^sub>1\<close> (@{thm [source] wf21_Br_eq_seg}) is \<open>monoT\<close>
  (its length \<open>= Lng (NJ M Jstar) > 1\<close> for \<open>kk > 0\<close>, @{thm [source] Br_component_nonmulti}),
  so its left end \<open>off\<close> is a row-0 ancestor of every later in-block index
  (@{thm [source] le0_monoT_seg_into_list}).  SOUND — GREEN cites only.\<close>

lemma wf22_le0_off_last:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and kkpos: "0 < Lng (NJ M (Lng (Br M) - 1)) - 1"
  shows "le0 M (FirstNodes M ! (Lng (Br M) - 1)) (Lng M - 1)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  define Jstar where "Jstar \<equiv> Lng (Br M) - 1"
  have JstarBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  define off where "off \<equiv> FirstNodes M ! Jstar"
  \<comment> \<open>last block is the suffix segment \<open>seg M off j\<^sub>1\<close>.\<close>
  have blkeq: "Br M ! Jstar = seg M off (Lng M - 1)"
    using wf21_Br_eq_seg[OF Mpt brne] unfolding Jstar_def off_def by simp
  \<comment> \<open>last block monoT (length \<open>> 1\<close> from \<open>kk > 0\<close>).\<close>
  have Llast: "Lng (NJ M Jstar) = Lng (Br M ! Jstar)"
    using conjunct1[OF conjunct2[OF conjunct2[OF kfwd_lastblock_locate[OF M mono e00 e10 tne]]]]
    unfolding Jstar_def by simp
  have kk': "1 < Lng (NJ M Jstar)" using kkpos unfolding Jstar_def by linarith
  have lastgt1: "1 < Lng (Br M ! Jstar)" using kk' Llast by simp
  have notz: "\<not> zeroT (Br M ! Jstar)" using lastgt1 by (simp add: zeroT_def)
  have lastmono: "monoT (Br M ! Jstar)"
    using Br_component_nonmulti[OF Mpt JstarBr] notz unfolding Jstar_def by blast
  have segmono: "monoT (seg M off (Lng M - 1))" using lastmono blkeq by simp
  \<comment> \<open>\<open>off \<le> Lng M - 1\<close> (block left end \<le> last column).\<close>
  have offlt: "off < Lng M"
  proof -
    have tb: "TrMax M < FirstNodes M ! Jstar"
      using m_6_4_FirstNodes_TrMax_Joints[OF Mpt JstarBr] by simp
    have lastL: "Lng (Br M ! Jstar) = Suc (Lng M - 1) - off"
      using blkeq by (simp only: Lng_seg)
    show ?thesis using lastgt1 lastL LMpos by linarith
  qed
  have offle: "off \<le> Lng M - 1" using offlt by linarith
  have beL: "Lng M - 1 < Lng M" using LMpos by linarith
  \<comment> \<open>left end row-0-reaches the last index of the monoT block.\<close>
  have "le0 M off (Lng M - 1)"
    by (rule le0_monoT_seg_into_list[OF MT segmono offle order.refl beL])
  thus ?thesis unfolding off_def Jstar_def .
qed

text \<open>WF22 BRICK B (\<open>wf22_off_row1val\<close>): the last block's left end row-1 value is
  the branch coefficient \<open>npJ M Jstar\<close>, which is \<open>\<le> Joints M ! Jstar + 1\<close>.  This is
  the head value of the last \<open>Red\<close>-block \<open>= IncrFirst\<^bsup>ee\<^esup>(Red (NJ M Jstar))\<close>; row 1 is
  \<open>IncrFirst\<close>-invariant, the head is \<open>entry (Red (NJ M Jstar)) 1 0 = entry (NJ M Jstar) 1 0
  = npJ M Jstar\<close>.  Replicates the (\<open>kk\<close>-free) head machinery of
  @{thm [source] wf17_crossblock_row1}.  SOUND — GREEN cites only.\<close>

lemma wf22_off_row1val:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  shows "entry M 1 (FirstNodes M ! (Lng (Br M) - 1)) = npJ M (Lng (Br M) - 1)
       \<and> npJ M (Lng (Br M) - 1) \<le> Joints M ! (Lng (Br M) - 1) + 1"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  define Jstar where "Jstar \<equiv> Lng (Br M) - 1"
  have JstarBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  define ee where "ee \<equiv> Joints M ! Jstar + 1 - npJ M Jstar"
  define off where "off \<equiv> Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J))) [0..<Jstar]))"
  have offFN: "off = FirstNodes M ! Jstar"
    unfolding off_def Jstar_def
    by (rule wf17_off_eq_firstnode[OF M mono e00 e10 tne])
  \<comment> \<open>\<open>M ! off\<close> is the head of the last \<open>Red\<close>-block \<open>(IncrFirst ^^ ee) (Red (NJ M Jstar))\<close>.\<close>
  have dropoff: "drop off M = (IncrFirst ^^ ee) (Red (NJ M Jstar))"
  proof -
    have "drop off M = (IncrFirst ^^ (Joints M ! Jstar + 1 - npJ M Jstar)) (Red (NJ M Jstar))"
      using conjunct1[OF kfwd_lastblock_locate[OF M mono e00 e10 tne]] redM
      unfolding off_def Jstar_def by simp
    thus ?thesis unfolding ee_def by simp
  qed
  have offlt: "off < Lng M"
  proof -
    have NJne: "NJ M Jstar \<noteq> []" by (simp add: NJ_def)
    have NJpos: "0 < Lng (NJ M Jstar)" using NJne by (cases "NJ M Jstar") auto
    have Llast: "Lng (NJ M Jstar) = Lng (Br M ! Jstar)"
      using conjunct1[OF conjunct2[OF conjunct2[OF kfwd_lastblock_locate[OF M mono e00 e10 tne]]]]
      unfolding Jstar_def by simp
    have blkeq: "Br M ! Jstar = seg M (FirstNodes M ! Jstar) (Lng M - 1)"
      using wf21_Br_eq_seg[OF Mpt brne] unfolding Jstar_def by simp
    have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
    have lastL: "Lng (Br M ! Jstar) = Suc (Lng M - 1) - FirstNodes M ! Jstar"
      using blkeq by (simp only: Lng_seg)
    show ?thesis using NJpos Llast lastL LMpos offFN by linarith
  qed
  have Moff: "M ! off = ((IncrFirst ^^ ee) (Red (NJ M Jstar))) ! 0"
  proof -
    have "M ! off = drop off M ! 0" using offlt by simp
    thus ?thesis using dropoff by simp
  qed
  have NJne: "NJ M Jstar \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M Jstar \<in> T_PS" using NJne by (simp add: T_PS_def)
  have RNJne: "Red (NJ M Jstar) \<noteq> []"
  proof -
    have "Lng (Red (NJ M Jstar)) = Lng (NJ M Jstar)" by (rule m_6_5_Lng_Red[OF NJT])
    thus ?thesis using NJne by (cases "NJ M Jstar") auto
  qed
  hence RNJpos: "0 < Lng (Red (NJ M Jstar))" by (cases "Red (NJ M Jstar)") auto
  have blk1: "entry ((IncrFirst ^^ ee) (Red (NJ M Jstar))) 1 0
              = entry (Red (NJ M Jstar)) 1 0"
    by (rule entry_funpow_IncrFirst1[OF RNJpos])
  have RNJ1: "entry (Red (NJ M Jstar)) 1 0 = npJ M Jstar"
    using m_6_6_Red_leftend_1[OF NJT] entry_NJ_1_0[of M Jstar] e10 by simp
  have eoff1: "entry M 1 off = npJ M Jstar"
    using Moff blk1 RNJ1 by (simp add: entry_def)
  have np_le: "npJ M Jstar \<le> Joints M ! Jstar + 1"
    by (rule npJ_le_Joints_Suc[OF Mpt e10 JstarBr])
  show ?thesis using eoff1 np_le offFN unfolding Jstar_def by simp
qed

text \<open>WF22 KEYSTONE (\<open>wf22_r1cross_factA\<close>): the row-1 cross-block \<open>kk > 0\<close> last-column
  relation \<open>entry M 1 p + 1 = entry M 1 j\<^sub>1\<close>, derived NON-CIRCULARLY from M's trunk
  structure (NOT N/IH), MODULO the single structural fact FACT A
  (\<open>fa : parent M 1 j\<^sub>1 \<le> Joints M ! Jstar\<close>, Front B's \<open>wf22_row1parent_le_joint\<close>;
  empirically 0-fail, 423/423 at maxlen 5).  Argument:
   \<^item> \<open>p = parent M 1 j\<^sub>1 \<le> joint \<le> TrMax M\<close>, so \<open>entry M 1 p = p\<close>
     (@{thm [source] ncons_diag_prefix_entry}) and \<open>nextrel1 M p j\<^sub>1\<close> gives
     \<open>p = entry M 1 p < entry M 1 j\<^sub>1\<close> + minimality
     (\<open>\<forall>q. p<q \<and> le0 M q j\<^sub>1 \<longrightarrow> entry M 1 q \<ge> entry M 1 j\<^sub>1\<close>).
   \<^item> If \<open>p < joint\<close>: witness \<open>q = p+1 \<le> joint\<close>, \<open>le0 M (p+1) j\<^sub>1\<close>
     (@{thm [source] slice_le0_to_index}), \<open>entry M 1 (p+1) = p+1\<close> (trunk).  Minimality:
     \<open>entry M 1 j\<^sub>1 \<le> p+1\<close>.
   \<^item> If \<open>p = joint\<close>: witness \<open>q = off = FirstNodes M ! Jstar > p\<close> (cross-block),
     \<open>le0 M off j\<^sub>1\<close> (@{thm [source] wf22_le0_off_last}),
     \<open>entry M 1 off = npJ M Jstar \<le> joint+1 = p+1\<close> (@{thm [source] wf22_off_row1val}).
     Minimality: \<open>entry M 1 j\<^sub>1 \<le> p+1\<close>.
   \<^item> Either way \<open>p < entry M 1 j\<^sub>1 \<le> p+1\<close>, so \<open>entry M 1 j\<^sub>1 = p+1 = entry M 1 p + 1\<close>.
  SOUND — cites only GREEN bricks and the explicit FACT A hypothesis; no \<open>p_*\<close> stub,
  no goal self-citation, no N/IH (non-circular per docs \<S>17).\<close>

lemma wf22_r1cross_factA:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and kkpos: "0 < Lng (NJ M (Lng (Br M) - 1)) - 1"
    and hp1: "hasParent M 1 (Lng M - 1)"
    and pcross: "parent M 1 (Lng M - 1) < FirstNodes M ! (Lng (Br M) - 1)"
    \<comment> \<open>FACT A (Front B \<open>wf22_row1parent_le_joint\<close>): the row-1 parent is \<le> the joint.\<close>
    and fa: "parent M 1 (Lng M - 1) \<le> Joints M ! (Lng (Br M) - 1)"
  shows "entry M 1 (parent M 1 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  define Jstar where "Jstar \<equiv> Lng (Br M) - 1"
  have JstarBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  define j1 where "j1 \<equiv> Lng M - 1"
  define p where "p \<equiv> parent M 1 j1"
  define off where "off \<equiv> FirstNodes M ! Jstar"
  define joint where "joint \<equiv> Joints M ! Jstar"
  have pj: "p \<le> joint" using fa unfolding p_def j1_def joint_def Jstar_def .
  have pcr: "p < off" using pcross unfolding p_def j1_def off_def Jstar_def .
  \<comment> \<open>joint \<le> TrMax M (last joint sits in the diagonal trunk).\<close>
  have jointTr: "joint \<le> TrMax M"
    using m_6_4_FirstNodes_TrMax_Joints[OF Mpt JstarBr] unfolding joint_def by simp
  have pTr: "p \<le> TrMax M" using pj jointTr by simp
  \<comment> \<open>(1) trunk value of \<open>p\<close>.\<close>
  have epp: "entry M 1 p = p"
    unfolding p_def j1_def
    by (rule ncons_diag_prefix_entry[OF M mono e00 e10 tne]) (use pTr in \<open>simp add: p_def j1_def\<close>)
  \<comment> \<open>(2) \<open>nextrel1 M p j\<^sub>1\<close> from the parent.\<close>
  have nr1: "nextrel1 M p j1"
  proof -
    obtain q where q: "nextR M 1 q j1" and uq: "\<And>r. nextR M 1 r j1 \<Longrightarrow> r = q"
      using hp1 unfolding hasParent_def j1_def by blast
    have "parent M 1 j1 = q" unfolding parent_def using q uq
      by (blast intro: the1_equality)
    hence "nextR M 1 p j1" using q unfolding p_def by simp
    thus ?thesis by (simp add: nextR_def)
  qed
  have pltj1: "entry M 1 p < entry M 1 j1" using nr1 by (simp add: nextrel1_def)
  have pj1gt: "p < entry M 1 j1" using pltj1 epp by simp
  have minim: "\<And>q. p < q \<Longrightarrow> le0 M q j1 \<Longrightarrow> entry M 1 j1 \<le> entry M 1 q"
    using nr1 unfolding nextrel1_def by blast
  \<comment> \<open>(3) the witness, by the two sub-cases.\<close>
  have ej1_le: "entry M 1 j1 \<le> p + 1"
  proof (cases "p < joint")
    case True
    \<comment> \<open>witness \<open>q = p+1 \<le> joint\<close>: trunk value and \<open>le0\<close> from the slice.\<close>
    have qle: "p + 1 \<le> joint" using True by simp
    have qTr: "p + 1 \<le> TrMax M" using qle jointTr by simp
    have eq1: "entry M 1 (p + 1) = p + 1"
      by (rule ncons_diag_prefix_entry[OF M mono e00 e10 tne]) (use qTr in simp)
    have j1le: "j1 \<le> Lng M - 1" unfolding j1_def by simp
    have trlt: "TrMax M < Lng M - 1" using TrMax_bound[OF MT] tne by linarith
    have qlt: "p + 1 < j1" using qTr trlt unfolding j1_def by linarith
    have leq: "le0 M (p + 1) j1"
      using slice_le0_to_index[OF Mpt brne _ qlt j1le]
            qle unfolding joint_def Jstar_def j1_def by (simp add: leR_def)
    have "entry M 1 j1 \<le> entry M 1 (p + 1)" by (rule minim) (use leq in auto)
    thus ?thesis using eq1 by simp
  next
    case False
    have peq: "p = joint" using pj False by simp
    \<comment> \<open>witness \<open>q = off > p\<close>: \<open>le0\<close> from the last block, value \<open>npJ \<le> joint+1 = p+1\<close>.\<close>
    have leoff: "le0 M off j1"
      using wf22_le0_off_last[OF M mono e00 e10 tne kkpos]
      unfolding off_def Jstar_def j1_def by simp
    have eoff_le: "entry M 1 off \<le> p + 1"
    proof -
      have "entry M 1 off = npJ M Jstar \<and> npJ M Jstar \<le> joint + 1"
        using wf22_off_row1val[OF M mono e00 e10 tne]
        unfolding off_def Jstar_def joint_def by simp
      thus ?thesis using peq by linarith
    qed
    have "entry M 1 j1 \<le> entry M 1 off" by (rule minim) (use pcr leoff in auto)
    thus ?thesis using eoff_le by simp
  qed
  \<comment> \<open>(4) combine: \<open>p < entry M 1 j\<^sub>1 \<le> p+1\<close>.\<close>
  have "entry M 1 j1 = p + 1" using pj1gt ej1_le by linarith
  thus ?thesis using epp unfolding p_def j1_def by simp
qed

text \<open>WF22 FACT A (\<open>wf22_row1parent_le_joint\<close>): the row-1 cross-block parent of the
  last column lies at or below the joint, \<open>p = parent M 1 j\<^sub>1 \<le> Joints M ! Jstar\<close>.
  This is the structural fact the trunk-reachability route needs (empirically
  0-fail, 423/423 at maxlen 5).  PROOF (non-circular, GREEN): \<open>p\<close> row-0-reaches
  \<open>j\<^sub>1\<close> (from \<open>nextrel1 M p j\<^sub>1\<close>); truncate that path at the last-block start \<open>off =
  FirstNodes M ! Jstar\<close> (@{thm [source] m_5_1_ancestor_tree_1}, since \<open>p < off \<le> j\<^sub>1\<close>)
  to get \<open>le0 M p off\<close>; \<open>off\<close> has a UNIQUE row-0 parent \<open>= Joints M ! Jstar\<close>
  (@{thm [source] m_6_4_mono_slice_next}, @{thm [source] Joints_nth}); so by parent
  maximality (@{thm [source] parent_max}) \<open>p \<le> Joints M ! Jstar\<close>.  SOUND — GREEN cites.\<close>

lemma wf22_row1parent_le_joint:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and hp1: "hasParent M 1 (Lng M - 1)"
    and pcross: "parent M 1 (Lng M - 1) < FirstNodes M ! (Lng (Br M) - 1)"
  shows "parent M 1 (Lng M - 1) \<le> Joints M ! (Lng (Br M) - 1)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have trlt: "TrMax M < Lng M - 1" using TrMax_bound[OF MT] tne by linarith
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  define Jstar where "Jstar \<equiv> Lng (Br M) - 1"
  have JstarBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  define j1 where "j1 \<equiv> Lng M - 1"
  define p where "p \<equiv> parent M 1 j1"
  define off where "off \<equiv> FirstNodes M ! Jstar"
  have pcr: "p < off" using pcross unfolding p_def j1_def off_def Jstar_def .
  \<comment> \<open>\<open>off \<le> j\<^sub>1\<close> and \<open>p < j\<^sub>1\<close>.\<close>
  have offTr: "TrMax M < off"
    using m_6_4_FirstNodes_TrMax_Joints[OF Mpt JstarBr] unfolding off_def by simp
  \<comment> \<open>last block start \<open>off \<le> Lng M - 1 = j\<^sub>1\<close> (it is the entry of the last block).\<close>
  have blkeq: "Br M ! Jstar = seg M off (Lng M - 1)"
    using wf21_Br_eq_seg[OF Mpt brne] unfolding Jstar_def off_def by simp
  have lastpos: "0 < Lng (Br M ! Jstar)"
    using Br_component_nonempty[OF Mpt JstarBr] by (cases "Br M ! Jstar") auto
  have offle: "off \<le> j1"
  proof -
    have "Lng (Br M ! Jstar) = Suc (Lng M - 1) - off" using blkeq by (simp only: Lng_seg)
    thus ?thesis using lastpos LMpos unfolding j1_def by linarith
  qed
  \<comment> \<open>\<open>p\<close> row-0-reaches \<open>j\<^sub>1\<close> (from the row-1 parent edge).\<close>
  have nr1: "nextrel1 M p j1"
  proof -
    obtain q where q: "nextR M 1 q j1" and uq: "\<And>r. nextR M 1 r j1 \<Longrightarrow> r = q"
      using hp1 unfolding hasParent_def j1_def by blast
    have "parent M 1 j1 = q" unfolding parent_def using q uq
      by (blast intro: the1_equality)
    hence "nextR M 1 p j1" using q unfolding p_def by simp
    thus ?thesis by (simp add: nextR_def)
  qed
  have le0pj1: "leR M 0 p j1" using nr1 by (simp add: nextrel1_def leR_def)
  \<comment> \<open>truncate the row-0 path at \<open>off\<close>: \<open>le0 M p off\<close>.\<close>
  have le0poff: "leR M 0 p off"
    by (rule m_5_1_ancestor_tree_1[OF MT le0pj1 less_imp_le_nat[OF pcr] offle])
  \<comment> \<open>\<open>off\<close> has unique row-0 parent \<open>= Joints M ! Jstar\<close>.\<close>
  have offexpand: "off = (TrMax M + 1) + IdxSum (P (seg M (TrMax M + 1) (Lng M - 1))) ! Jstar"
  proof -
    have brQ: "Br M = P (seg M (TrMax M + 1) (Lng M - 1))" using tne by (simp add: Br_def)
    have "off = TrMax M + 1 + IdxSum (Br M) ! Jstar"
      using FirstNodes_nth[OF JstarBr] unfolding off_def by simp
    thus ?thesis using brQ by simp
  qed
  have JleP: "Jstar \<le> Lng (P (seg M (TrMax M + 1) (Lng M - 1))) - 1"
  proof -
    have brQ: "Br M = P (seg M (TrMax M + 1) (Lng M - 1))" using tne by (simp add: Br_def)
    show ?thesis using JstarBr brQ by simp
  qed
  have j0pos: "0 < TrMax M + 1" by simp
  have j0le: "TrMax M + 1 \<le> Lng M - 1" using trlt by simp
  have hpoff: "hasParent M 0 off"
    using m_6_4_mono_slice_next[OF Mpt j0pos j0le JleP] offexpand by simp
  have jointoff: "Joints M ! Jstar = parent M 0 off"
    using Joints_nth[OF JstarBr] unfolding off_def by simp
  have nxoff: "nextR M 0 (Joints M ! Jstar) off"
  proof -
    have "\<exists>!j0. nextR M 0 j0 off" using hpoff by (simp add: hasParent_def)
    hence "nextR M 0 (THE j0. nextR M 0 j0 off) off" by (rule theI')
    thus ?thesis using jointoff by (simp add: parent_def)
  qed
  \<comment> \<open>parent maximality: \<open>p \<le> Joints M ! Jstar\<close>.\<close>
  have "p \<le> Joints M ! Jstar"
    by (rule parent_max[OF hpoff nxoff le0poff pcr])
  thus ?thesis unfolding p_def j1_def Jstar_def .
qed

text \<open>WF22 \<open>r1cross\<close> (UNCONDITIONAL): the row-1 cross-block \<open>kk > 0\<close> last-column
  relation, with FACT A (@{thm [source] wf22_row1parent_le_joint}) discharged.
  This is exactly the residual hypothesis of @{thm [source] condAB_all_cond}.\<close>

lemma wf22_r1cross:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and kkpos: "0 < Lng (NJ M (Lng (Br M) - 1)) - 1"
    and hp1: "hasParent M 1 (Lng M - 1)"
    and pcross: "parent M 1 (Lng M - 1) < FirstNodes M ! (Lng (Br M) - 1)"
  shows "entry M 1 (parent M 1 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1)"
  by (rule wf22_r1cross_factA[OF M mono e00 e10 tne kkpos hp1 pcross
        wf22_row1parent_le_joint[OF M mono e00 e10 tne hp1 pcross]])

text \<open>\<S>6.6 KEYSTONE FORWARD (monoT core), UNCONDITIONAL.  The conditional skeleton
  @{thm [source] condAB_all_cond} reduces every \<open>RedCondA\<close>/\<open>RedCondB\<close> obligation to
  the single residual \<open>r1cross\<close> (row-1 cross-block \<open>kk>0\<close> last-column relation),
  now discharged by @{thm [source] wf22_r1cross} via M's trunk-reachability
  structure (non-circular, docs \<S>17).  This unblocks \<S>6.5 \<open>Red_le\<close> via the
  \<open>reduced \<Longrightarrow> RedCondA \<Longrightarrow> red_le\<close> lead.  SOUND — GREEN cites only.\<close>

lemma kst_reduced_imp_condAB_monoT_core:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
  shows "RedCondA M \<and> RedCondB M"
  by (rule condAB_all_cond[OF wf22_r1cross M mono e00 e10])


text \<open>\<S>6.6 KEYSTONE FORWARD (GENERAL M) — Front A assembly (wf23-fwd).

  Goal: \<open>kst_reduced_imp_condAB: M \<in> RT_PS \<Longrightarrow> RedCondA M \<and> RedCondB M\<close> for any
  reduced \<open>M\<close> (the forward half of the \<S>6.6 keystone \<open>reduced \<longleftrightarrow> A\<and>B\<close>).

  WLOG reduction over the \<open>T_PS\<close> trichotomy (\<open>zeroT\<close>/\<open>monoT\<close>/\<open>multiT\<close>), by strong
  induction on \<open>Lng M\<close>:
  \<^item> \<open>zeroT M\<close>: forward half of @{thm [source] kst_reduced_iff_cond_zeroT}.
  \<^item> \<open>multiT M\<close>: each \<open>P\<close>-block \<open>P M ! J \<in> RT_PS\<close> (@{thm [source] m_6_6_P_reduced})
    and is strictly shorter (\<open>kfwd_P_block_shorter\<close> below); IH gives
    blockwise \<open>A\<and>B\<close>, lifted by @{thm [source] m_6_6_RedCond_concat_lift}.
  \<^item> \<open>monoT M\<close>, \<open>m\<^sub>1\<^sub>0 = 0\<close>: if \<open>m\<^sub>0\<^sub>0 = 0\<close>, the keystone core
    @{thm [source] kst_reduced_imp_condAB_monoT_core}; if \<open>m\<^sub>0\<^sub>0 \<noteq> 0\<close>, vacuous
    (@{thm [source] kfwd_reduced_monoT_shift_vacuous}).
  \<^item> \<open>monoT M\<close>, \<open>m\<^sub>1\<^sub>0 > 0\<close>: \<open>RedCondB\<close> is GREEN here
    (\<open>kfwd_reduced_monoT_condB\<close> below); \<open>RedCondA\<close> is the SOLE residual.

  The residual is supplied as a hypothesis \<open>condA_m10pos\<close> in
  \<open>kst_reduced_imp_condAB_cond\<close>; the unconditional target
  \<open>kst_reduced_imp_condAB\<close> cites it, see the residual note below.\<close>

text \<open>Helper: every \<open>P\<close>-block of a \<open>multiT M\<close> is strictly shorter than \<open>M\<close>.
  \<open>multiT M \<Longrightarrow> length (P M) > 1\<close> (@{thm [source] m_6_2_P_components_2}) and every block
  is nonempty (@{thm [source] P_blocks_nonempty}); since \<open>concat (P M) = M\<close>
  (@{thm [source] idxsum_concat_P}) the lengths sum to \<open>Lng M\<close> with \<open>\<ge> 2\<close> positive
  summands, so each is \<open>< Lng M\<close>.\<close>

lemma kfwd_P_block_shorter:
  assumes M: "M \<in> T_PS" and multi: "multiT M" and J: "J < length (P M)"
  shows "Lng (P M ! J) < Lng M"
proof -
  have Mne: "M \<noteq> []" using M by (simp add: T_PS_def)
  let ?Q = "P M"
  have len2: "1 < length ?Q" using multi m_6_2_P_components_2[OF M] by simp
  have allne: "\<forall>B \<in> set ?Q. B \<noteq> []" by (rule P_blocks_nonempty[OF Mne])
  have allpos: "\<forall>B \<in> set ?Q. 0 < length B"
    using allne by auto
  have sumQ: "sum_list (map length ?Q) = Lng M"
    using idxsum_concat_P[of M] by (metis length_concat)
  \<comment> \<open>Block \<open>J\<close> is one summand; the others (at least one, since \<open>length ?Q \<ge> 2\<close>)
     are positive, so block \<open>J\<close> is strictly below the total.\<close>
  have JinB: "?Q ! J \<in> set ?Q" using J by simp
  \<comment> \<open>pick another block \<open>K \<noteq> J\<close>.\<close>
  define K :: nat where "K \<equiv> (if J = 0 then 1 else 0)"
  have K: "K < length ?Q" using len2 J unfolding K_def by (cases "J = 0") auto
  have KneJ: "K \<noteq> J" unfolding K_def by (cases "J = 0") auto
  have KinB: "?Q ! K \<in> set ?Q" using K by simp
  have Kpos: "0 < length (?Q ! K)" using allpos KinB by blast
  \<comment> \<open>\<open>length(?Q!J) + length(?Q!K) \<le> total\<close>: the two distinct summands are bounded by
     the sum over \<open>{J,K}\<close>, itself \<le> the full sum over \<open>{..<length ?Q}\<close>.\<close>
  have eq0: "sum_list (map length ?Q) = (\<Sum>i<length ?Q. length (?Q ! i))"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  have JK: "{J, K} \<subseteq> {..<length ?Q}" using J K by auto
  have JneK: "J \<noteq> K" using KneJ by simp
  have two_le: "length (?Q ! J) + length (?Q ! K) \<le> (\<Sum>i<length ?Q. length (?Q ! i))"
  proof -
    have "(\<Sum>i\<in>{J,K}. length (?Q ! i)) \<le> (\<Sum>i<length ?Q. length (?Q ! i))"
      by (rule sum_mono2[OF finite_lessThan JK]) simp
    moreover have "(\<Sum>i\<in>{J,K}. length (?Q ! i)) = length (?Q ! J) + length (?Q ! K)"
      using JneK by simp
    ultimately show ?thesis by simp
  qed
  have "Lng (?Q ! J) < length (?Q ! J) + length (?Q ! K)"
    using Kpos by simp
  also have "\<dots> \<le> (\<Sum>i<length ?Q. length (?Q ! i))" using two_le by simp
  also have "\<dots> = sum_list (map length ?Q)" using eq0 by simp
  also have "\<dots> = Lng M" by (rule sumQ)
  finally show ?thesis .
qed

text \<open>Helper: a reduced \<open>monoT M\<close> has equal first column, \<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0\<close>.
  This is the equality strengthening of @{thm [source] kst_reduced_row1_le_row0}:
  in the \<open>m\<^sub>1\<^sub>0 > 0\<close> productive branch the rebase forces
  \<open>entry (Red M) 0 0 = entry N 1 m\<^sub>1\<^sub>0 = entry (Red M) 1 0\<close>; with \<open>Red M = M\<close> the two
  first-column entries coincide.  In the \<open>m\<^sub>1\<^sub>0 = 0\<close> branch either \<open>m\<^sub>0\<^sub>0 = 0\<close> (so
  \<open>0 = 0\<close>) or \<open>m\<^sub>0\<^sub>0 \<noteq> 0\<close> is impossible (@{thm [source] kfwd_reduced_monoT_shift_vacuous}).\<close>

lemma kfwd_reduced_monoT_diag00:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
  shows "entry M 0 0 = entry M 1 0"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  let ?j1  = "Lng M - 1"
  let ?m00 = "entry M 0 0"
  let ?m10 = "entry M 1 0"
  show "?m00 = ?m10"
  proof (cases "?m10 = 0")
    case True
    \<comment> \<open>\<open>m\<^sub>1\<^sub>0 = 0\<close>: either \<open>m\<^sub>0\<^sub>0 = 0\<close> or the shift-vacuous contradiction.\<close>
    show ?thesis
    proof (cases "?m00 = 0")
      case True thus ?thesis using \<open>?m10 = 0\<close> by simp
    next
      case False
      from kfwd_reduced_monoT_shift_vacuous[OF M mono True False] show ?thesis by simp
    qed
  next
    case False
    hence c1p: "0 < ?m10" by simp
    have nc: "\<not> (?m00 = 0 \<and> ?m10 = 0)" using c1p by simp
    have MPT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
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
    have segPT: "seg ?N ?m10 ?jN \<in> PT_PS"
      using m_6_5_monoT_Red_m10pos[OF MPT c1p] by simp
    have segne: "seg ?N ?m10 ?jN \<noteq> []"
      using segPT by (simp add: PT_PS_def T_PS_def)
    have m10_le: "?m10 \<le> ?jN"
    proof -
      have "0 < Lng (seg ?N ?m10 ?jN)"
        using segne by (cases "seg ?N ?m10 ?jN") auto
      hence "0 < Suc ?jN - ?m10" by (simp only: Lng_seg)
      thus ?thesis by simp
    qed
    have then_case: "?m10 \<le> ?jN \<and> seg ?N ?m10 ?jN \<in> PT_PS"
      using m10_le segPT by simp
    have rM': "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10
                                  + entry ?N 1 ?m10, entry ?N 1 j))
                           [?m10..<Suc ?jN]"
      using rM then_case by (simp add: Let_def del: upt_Suc)
    have len0: "0 < length [?m10..<Suc ?jN]" using m10_le by (simp del: upt_Suc)
    have idx0: "[?m10..<Suc ?jN] ! 0 = ?m10"
      using m10_le by (simp add: nth_upt del: upt_Suc)
    have nth0: "(Red M) ! 0 = (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10
                                      + entry ?N 1 ?m10, entry ?N 1 j)) ?m10"
      using rM' len0 idx0 by (simp add: nth_map del: upt_Suc)
    have e_rM0: "entry (Red M) 0 0 = entry ?N 1 ?m10"
      using nth0 unfolding entry_def by simp
    have e_rM1: "entry (Red M) 1 0 = entry ?N 1 ?m10"
      using nth0 unfolding entry_def by simp
    have "?m00 = entry (Red M) 0 0" using redM by simp
    also have "\<dots> = entry ?N 1 ?m10" using e_rM0 .
    also have "\<dots> = entry (Red M) 1 0" using e_rM1 by simp
    also have "\<dots> = ?m10" using redM by simp
    finally show ?thesis .
  qed
qed

text \<open>Helper: a \<open>monoT M\<close> has a row-0 parent at every interior column.  Convexity
  (@{thm [source] m_5_1_ancestor_tree_1}) lifts \<open>leR M 0 0 (Lng M-1)\<close> to
  \<open>leR M 0 0 j1\<close>, then @{thm [source] m_5_1_ancestor_basic_1} +
  @{thm [source] m_5_1_parent_exists_1} produce the row-0 parent.\<close>

lemma kfwd_monoT_hasParent_col:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and j1pos: "0 < j1" and j1L: "j1 < Lng M"
  shows "hasParent M 0 j1"
proof -
  have le0top: "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
  have j1le: "j1 \<le> Lng M - 1" using j1L by linarith
  have le0j1: "leR M 0 0 j1"
    by (rule m_5_1_ancestor_tree_1[OF MT le0top zero_le j1le])
  have e0lt: "entry M 0 0 < entry M 0 j1"
    by (rule m_5_1_ancestor_basic_1[OF MT j1pos order.refl le0j1])
  have "\<exists>j. 0 \<le> j \<and> j < j1 \<and> nextR M 0 j j1"
    by (rule m_5_1_parent_exists_1[OF MT j1pos j1L e0lt])
  hence "\<exists>j0. nextR M 0 j0 j1" by blast
  thus ?thesis unfolding hasParent_def using idxsum_ex1_parent0_iff by blast
qed

text \<open>Helper: \<open>RedCondB\<close> for ANY reduced \<open>monoT M\<close>.  The sole row-0 parentless
  column of a \<open>monoT M\<close> is column \<open>0\<close> (@{thm [source] kfwd_monoT_hasParent_col}),
  where reducedness pins \<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0\<close> (@{thm [source] kfwd_reduced_monoT_diag00}).\<close>

lemma kfwd_reduced_monoT_condB:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
  shows "RedCondB M"
  unfolding RedCondB_def
proof (intro allI impI)
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  fix j1' assume H: "\<not> hasParent M 0 j1' \<and> j1' \<le> Lng M - 1"
  hence noP: "\<not> hasParent M 0 j1'" and hle: "j1' \<le> Lng M - 1" by simp_all
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have j0: "j1' = 0"
  proof (rule ccontr)
    assume "j1' \<noteq> 0"
    hence j1pos: "0 < j1'" by simp
    have j1L: "j1' < Lng M" using hle LMpos by linarith
    have "hasParent M 0 j1'" by (rule kfwd_monoT_hasParent_col[OF MT mono j1pos j1L])
    thus False using noP by simp
  qed
  have "entry M 0 0 = entry M 1 0" by (rule kfwd_reduced_monoT_diag00[OF M mono])
  thus "entry M 0 j1' = entry M 1 j1'" using j0 by simp
qed

text \<open>\<S>6.6 keystone FORWARD for GENERAL \<open>M\<close>, reduced to the single residual
  \<open>condA_m10pos\<close>: \<open>RedCondA\<close> for a reduced \<open>monoT M\<close> with \<open>entry M 1 0 > 0\<close>.

  Every other case is discharged GREEN (zeroT / multiT recursion / monoT core /
  monoT shift-vacuous), and \<open>RedCondB\<close> is GREEN for the residual monoT m10>0 case
  too (@{thm [source] kfwd_reduced_monoT_condB}).  Strong induction on \<open>Lng M\<close>;
  the multiT branch applies the IH to each strictly-shorter, reduced \<open>P\<close>-block.\<close>

lemma kst_reduced_imp_condAB_cond:
  assumes condA_m10pos:
    "\<And>N. N \<in> RT_PS \<Longrightarrow> monoT N \<Longrightarrow> 0 < entry N 1 0 \<Longrightarrow> RedCondA N"
  assumes M0: "M \<in> RT_PS"
  shows "RedCondA M \<and> RedCondB M"
  using M0
proof (induction M rule: measure_induct_rule[where f = Lng])
  case (less M)
  have M: "M \<in> RT_PS" by (rule less.prems)
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  show ?case
  proof (cases "zeroT M")
    case True
    show ?thesis
      using kst_reduced_iff_cond_zeroT[OF MT True] M by blast
  next
    case nz: False
    show ?thesis
    proof (cases "multiT M")
      case True
      \<comment> \<open>multiT: every block reduced and strictly shorter; IH then concat-lift.\<close>
      have blocksAB: "\<forall>J < length (P M). RedCondA (P M ! J) \<and> RedCondB (P M ! J)"
      proof (intro allI impI)
        fix J assume J: "J < length (P M)"
        have memB: "P M ! J \<in> set (P M)" using J by simp
        have BT: "P M ! J \<in> T_PS"
          using P_blocks_nonempty[OF Mne] memB by (auto simp: T_PS_def)
        have JLng: "J < Lng (P M)" using J by simp
        have BRT: "P M ! J \<in> RT_PS"
          using m_6_6_P_reduced[OF MT] M JLng by blast
        have shorter: "Lng (P M ! J) < Lng M"
          by (rule kfwd_P_block_shorter[OF MT True J])
        show "RedCondA (P M ! J) \<and> RedCondB (P M ! J)"
          by (rule less.IH[OF shorter BRT])
      qed
      show ?thesis
        by (rule m_6_6_RedCond_concat_lift[OF MT True blocksAB])
    next
      case nmu: False
      have mono: "monoT M" using nz nmu by (simp add: monoT_def multiT_def)
      show ?thesis
      proof (cases "0 < entry M 1 0")
        case True
        \<comment> \<open>monoT, m10>0: RedCondB GREEN, RedCondA from the residual.\<close>
        have condB: "RedCondB M" by (rule kfwd_reduced_monoT_condB[OF M mono])
        have condA: "RedCondA M" by (rule condA_m10pos[OF M mono True])
        show ?thesis using condA condB by blast
      next
        case False
        hence e10: "entry M 1 0 = 0" by simp
        show ?thesis
        proof (cases "entry M 0 0 = 0")
          case True
          show ?thesis
            by (rule kst_reduced_imp_condAB_monoT_core[OF M mono True e10])
        next
          case False
          from kfwd_reduced_monoT_shift_vacuous[OF M mono e10 False]
          show ?thesis by simp
        qed
      qed
    qed
  qed
qed

end

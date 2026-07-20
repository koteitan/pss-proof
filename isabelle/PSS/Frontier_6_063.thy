theory Frontier_6_063
  imports Support_6_042
begin

section \<open>Front A (wf15) — \<open>condA_top\<close> in-block last-column entry transfer\<close>

text \<open>WF15 BRICK 1 (in-block entry/index transfer).  For a reduced \<open>monoT\<close> core
  \<open>M\<close> with \<open>M\<^sub>0=(0,0)\<close> on the core-NONTRUNK branch (\<open>TrMax M \<noteq> Lng M-1\<close>), the LAST
  column \<open>Lng M-1\<close> of \<open>M = Red M\<close> sits inside the located last concat block
  \<open>blk J\<^sup>* = (IncrFirst ^^ e\<^bsub>J\<^sup>*\<^esub>)(Red (NJ M J\<^sup>*))\<close> (from the GREEN
  @{thm [source] kfwd_lastblock_locate}) at the block-local index \<open>Lng (NJ M J\<^sup>*)-1\<close>.
  Hence \<open>entry M\<close> on the last column transfers, via the GREEN \<open>incf_pow_*\<close> bricks,
  to \<open>entry (Red (NJ M J\<^sup>*))\<close> on ITS last column (row-0 shifted by \<open>e\<^bsub>J\<^sup>*\<^esub>\<close>, row-1
  unchanged).  This is the pure entry/index half of the in-block witness
  translation (content.md 1198-1216); SOUND — cites only GREEN
  @{thm [source] kfwd_lastblock_locate}, @{thm [source] incf_pow_entry0},
  @{thm [source] incf_pow_entry1}, @{thm [source] incf_pow_hasParent},
  @{thm [source] incf_pow_parent} and the library.

  The remaining (cross-block) half — translating \<open>hasParent\<close>/\<open>parent\<close> of \<open>M\<close>'s
  LAST column to the block (a non-drop-local \<open>nextR\<close> correspondence) — is the
  RESIDUAL; the block-internal \<open>hasParent\<close>/\<open>parent\<close> IncrFirst-invariance is banked
  in conjuncts (5),(6) for assembly once that correspondence is supplied.\<close>

lemma wf15_lastblock_entry_transfer:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  defines "ee \<equiv> Joints M ! Jstar + 1 - npJ M Jstar"
  defines "off \<equiv> Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J))) [0..<Jstar]))"
  defines "kk \<equiv> Lng (NJ M Jstar) - 1"
  shows "Lng M - 1 = off + kk
       \<and> Lng (NJ M Jstar) < Lng M
       \<and> (entry M 0 (Lng M - 1) = entry (Red (NJ M Jstar)) 0 kk + ee)
       \<and> (entry M 1 (Lng M - 1) = entry (Red (NJ M Jstar)) 1 kk)
       \<and> (\<forall>i\<le>1. hasParent ((IncrFirst ^^ ee) (Red (NJ M Jstar))) i kk
              = hasParent (Red (NJ M Jstar)) i kk)
       \<and> (\<forall>i\<le>1. parent ((IncrFirst ^^ ee) (Red (NJ M Jstar))) i kk
              = parent (Red (NJ M Jstar)) i kk)"
proof -
  let ?blk = "\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))"
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have loc: "drop off (Red M) = ?blk Jstar
       \<and> ?blk Jstar = (IncrFirst ^^ (Joints M ! Jstar + 1 - npJ M Jstar)) (Red (NJ M Jstar))
       \<and> Lng (NJ M Jstar) = Lng (Br M ! Jstar)
       \<and> Lng (NJ M Jstar) < Lng M
       \<and> Lng (Br M) \<noteq> 0"
    unfolding Jstar_def off_def
    by (rule kfwd_lastblock_locate[OF M mono e00 e10 tne])
  have dropoff: "drop off M = ?blk Jstar" using loc redM by simp
  have NJlt: "Lng (NJ M Jstar) < Lng M" using loc by simp
  have NJne: "NJ M Jstar \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M Jstar \<in> T_PS" using NJne by (simp add: T_PS_def)
  have lRedNJ: "Lng (Red (NJ M Jstar)) = Lng (NJ M Jstar)"
    by (rule m_6_5_Lng_Red[OF NJT])
  have lblk: "Lng (?blk Jstar) = Lng (NJ M Jstar)" using lRedNJ by simp
  have ldrop: "Lng (drop off M) = Lng M - off" by simp
  have lenrel: "Lng M - off = Lng (NJ M Jstar)"
    using dropoff ldrop lblk by simp
  have NJpos: "0 < Lng (NJ M Jstar)" using NJne by (cases "NJ M Jstar") auto
  have offle: "off \<le> Lng M" using lenrel NJpos by linarith
  have Leq: "Lng M - 1 = off + kk"
    unfolding kk_def using lenrel NJpos offle by linarith
  have kkLT: "kk < Lng (Red (NJ M Jstar))"
    unfolding kk_def using NJpos lRedNJ by linarith
  have entoff: "\<And>i. entry M i (Lng M - 1) = entry (?blk Jstar) i kk"
  proof -
    fix i
    have "M ! (Lng M - 1) = (drop off M) ! ((Lng M - 1) - off)"
      using offle Leq by (simp add: nth_drop)
    also have "\<dots> = (?blk Jstar) ! kk" using dropoff Leq by simp
    finally have "M ! (Lng M - 1) = (?blk Jstar) ! kk" .
    thus "entry M i (Lng M - 1) = entry (?blk Jstar) i kk"
      by (simp add: entry_def)
  qed
  have e0: "entry M 0 (Lng M - 1) = entry (Red (NJ M Jstar)) 0 kk + ee"
    using entoff[of 0] incf_pow_entry0[OF kkLT, of "Joints M ! Jstar + 1 - npJ M Jstar"]
    unfolding ee_def by simp
  have e1: "entry M 1 (Lng M - 1) = entry (Red (NJ M Jstar)) 1 kk"
    using entoff[of 1] incf_pow_entry1[OF kkLT, of "Joints M ! Jstar + 1 - npJ M Jstar"]
    by simp
  have hp: "\<forall>i\<le>1. hasParent ((IncrFirst ^^ ee) (Red (NJ M Jstar))) i kk
                  = hasParent (Red (NJ M Jstar)) i kk"
    by (simp add: incf_pow_hasParent)
  have pp: "\<forall>i\<le>1. parent ((IncrFirst ^^ ee) (Red (NJ M Jstar))) i kk
                  = parent (Red (NJ M Jstar)) i kk"
    by (simp add: incf_pow_parent)
  show ?thesis using Leq NJlt e0 e1 hp pp by blast
qed


text \<open>WF15 BRICK 2 (in-block N-construction core: reduced + monoT + left end).
  For a reduced \<open>monoT\<close> core \<open>M\<close> with \<open>M\<^sub>0=(0,0)\<close> on the nontrunk branch, the
  last branch reduction \<open>R\<^sup>* := Red (NJ M J\<^sup>*)\<close> (\<open>J\<^sup>* = Lng (Br M)-1\<close>) is a reduced
  \<open>T_PS\<close> sequence (idempotence of \<open>Red\<close> on the non-multi \<open>NJ\<close>); prepending the
  diagonal \<open>diagSeq 0 (R\<^sup>*\<^bsub>1,0\<^esub>-1)\<close> yields the article \<open>N\<close>, which is reduced and
  \<open>monoT\<close> with left end \<open>(0,0)\<close> via the GREEN @{thm [source] m_6_6_reduced_leftend}.
  This is the article's "\<open>N\<close> は簡約である" + "\<open>N\<^sub>0 = (0,0)\<close>" step (content.md
  1180-1186 / 1210-1212) for the in-block (\<open>J\<^sub>1>0\<close>) regime.  SOUND — cites only
  GREEN @{thm [source] idem_nonmulti}, @{thm [source] m_6_5_Red_preserves_monoT},
  @{thm [source] m_6_6_reduced_leftend}, @{thm [source] NJ_nonmulti},
  @{thm [source] fin_Red_NJ_leftend} and the library; never a \<open>p_*\<close> stub.\<close>

lemma wf15_inblock_N_core:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and nzNJ: "\<not> zeroT (NJ M (Lng (Br M) - 1))"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  defines "Rs \<equiv> Red (NJ M Jstar)"
  defines "N \<equiv> (if 0 < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs"
  shows "Rs \<in> RT_PS \<and> Rs \<in> T_PS \<and> monoT Rs
       \<and> entry Rs 0 0 = npJ M Jstar
       \<and> Red N = N \<and> monoT N
       \<and> entry N 0 0 = 0 \<and> entry N 1 0 = 0
       \<and> N = (if 0 < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  \<comment> \<open>\<open>Br M \<noteq> []\<close> so \<open>Jstar\<close> is a valid branch index.\<close>
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  have JBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  have NJne: "NJ M Jstar \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M Jstar \<in> T_PS" using NJne by (simp add: T_PS_def)
  have nm: "\<not> multiT (NJ M Jstar)" by (rule NJ_nonmulti[OF Mpt e00 e10 JBr])
  have nzNJ': "\<not> zeroT (NJ M Jstar)" using nzNJ unfolding Jstar_def .
  have monoNJ: "monoT (NJ M Jstar)" using nm nzNJ' by (simp add: multiT_def)
  have NJPT: "NJ M Jstar \<in> PT_PS" using NJT monoNJ by (simp add: PT_PS_def)
  \<comment> \<open>\<open>R\<^sup>*\<close> in \<open>T_PS\<close> (nonempty) and reduced (idempotence on non-multi).\<close>
  have RsT: "Rs \<in> T_PS"
  proof -
    have "Lng (Red (NJ M Jstar)) = Lng (NJ M Jstar)" by (rule m_6_5_Lng_Red[OF NJT])
    hence "Red (NJ M Jstar) \<noteq> []" using NJne by (cases "NJ M Jstar") auto
    thus ?thesis unfolding Rs_def by (simp add: T_PS_def)
  qed
  have RsRT: "Rs \<in> RT_PS"
  proof -
    have "Red (Red (NJ M Jstar)) = Red (NJ M Jstar)" by (rule idem_nonmulti[OF NJT nm])
    thus ?thesis using RsT unfolding Rs_def by (simp add: RT_PS_def)
  qed
  \<comment> \<open>left-end row 0 of \<open>R\<^sup>*\<close>.\<close>
  have Rs00: "entry Rs 0 0 = npJ M Jstar"
    unfolding Rs_def by (rule fin_Red_NJ_leftend[OF Mpt e00 e10 JBr])
  \<comment> \<open>\<open>R\<^sup>*\<close> is monoT (non-zero branch).\<close>
  have monoRs: "monoT Rs"
    unfolding Rs_def by (rule m_6_5_Red_preserves_monoT[OF NJPT])
  have RsPT: "Rs \<in> PT_PS" using RsT monoRs by (simp add: PT_PS_def)
  show ?thesis
  proof (cases "0 < entry Rs 1 0")
    case False
    \<comment> \<open>\<open>R\<^sup>*\<^bsub>1,0\<^esub> = 0\<close>: \<open>N = R\<^sup>*\<close>; \<open>m_6_6_reduced_leftend\<close> with \<open>u=0\<close> gives \<open>N = R\<^sup>*\<close>.\<close>
    have Neq: "N = Rs" unfolding N_def using False by simp
    have z: "(0::nat) \<le> entry Rs 1 0" by simp
    have rl: "Red ((if (0::nat) < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs)
              = ((if (0::nat) < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs)
              \<and> monoT ((if (0::nat) < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs)"
      using m_6_6_reduced_leftend[OF RsRT RsPT z] by simp
    have rN: "Red N = N \<and> monoT N" using rl unfolding N_def by simp
    have e1N: "entry N 1 0 = 0" using Neq False by simp
    \<comment> \<open>row-0 left end: \<open>entry N 0 0 = entry Rs 0 0\<close>; but article needs it \<open>= 0\<close>.\<close>
    have e0N: "entry N 0 0 = entry Rs 0 0" using Neq by simp
    \<comment> \<open>\<open>entry Rs 1 0 = entry (NJ) 1 0 = npJ\<close>; here \<open>=0\<close>, so \<open>npJ=0\<close>.\<close>
    have Rs10: "entry Rs 1 0 = npJ M Jstar"
      unfolding Rs_def using m_6_6_Red_leftend_1[OF NJT] entry_NJ_1_0[of M Jstar] e10 by simp
    have np0: "npJ M Jstar = 0" using False Rs10 by simp
    have e0N0: "entry N 0 0 = 0" using e0N Rs00 np0 by simp
    show ?thesis using RsRT RsT monoRs Rs00 rN e0N0 e1N N_def by blast
  next
    case True
    have Neq: "N = diagSeq 0 (entry Rs 1 0 - 1) @ Rs" unfolding N_def using True by simp
    have z: "(0::nat) \<le> entry Rs 1 0" by simp
    have rl: "Red ((if (0::nat) < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs)
              = ((if (0::nat) < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs)
              \<and> monoT ((if (0::nat) < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs)"
      using m_6_6_reduced_leftend[OF RsRT RsPT z] by simp
    have rN: "Red N = N \<and> monoT N" using rl unfolding N_def by simp
    \<comment> \<open>left end of \<open>diagSeq 0 (k) @ Rs\<close> is \<open>(0,0)\<close>.\<close>
    have e0N0: "entry N 0 0 = 0"
      using Neq entry_diagSeq_append_lo[where k="entry Rs 1 0 - 1" and i=0 and p=0
        and rest=Rs] by simp
    have e1N0: "entry N 1 0 = 0"
      using Neq entry_diagSeq_append_lo[where k="entry Rs 1 0 - 1" and i=0 and p=1
        and rest=Rs] by simp
    show ?thesis using RsRT RsT monoRs Rs00 rN e0N0 e1N0 N_def by blast
  qed
qed

section \<open>Front A (wf16) — \<open>condA_top\<close> in-block parent correspondence\<close>

text \<open>WF16 BRICK 3 (in-block parent/hasParent correspondence at the last column).
  For a reduced \<open>monoT\<close> core \<open>M\<close> with \<open>M\<^sub>0 = (0,0)\<close> on the nontrunk branch, the
  suffix \<open>drop off M\<close> (\<open>off\<close> the last block start) equals the last block
  \<open>(IncrFirst ^^ ee) (Red (NJ M J\<^sup>*))\<close>, and the last column is \<open>Lng M - 1 = off + kk\<close>.
  Hence, for any IN-BLOCK parent index \<open>off \<le> p\<close>, the M-\<open>nextR\<close> at the last column
  corresponds (via the unconditional drop-correspondence
  @{thm [source] poper_nextR_drop}) to the block-local \<open>nextR\<close> at \<open>kk\<close>, and then
  via the GREEN \<open>incf_pow_*\<close> family to \<open>Red (NJ M J\<^sup>*)\<close> itself.  This pins:
    (i) \<open>hasParent M i (Lng M-1)\<close> with parent \<open>off \<le> p\<close> \<Longrightarrow>
        \<open>hasParent (Red (NJ M J\<^sup>*)) i (p - off)\<close> at \<open>kk\<close>'s parent;
    (ii) the entry relation transfers (row-1 verbatim, row-0 with the \<open>+ee\<close> shift,
         which cancels in \<open>condA\<close>).
  This is the IN-BLOCK half of the last-column \<open>condA\<close> witness translation
  (content.md 1198-1216).  SOUND — cites only GREEN @{thm [source] poper_nextR_drop},
  @{thm [source] incf_pow_nextR}, @{thm [source] wf15_lastblock_entry_transfer},
  @{thm [source] kfwd_lastblock_locate} and the library; never a \<open>p_*\<close> stub.

  RESIDUAL (reported, not faked).  Two gaps remain for the full \<open>condA_top_all\<close>:
  (A) the CROSS-BLOCK case (\<open>p < off\<close>): empirically the MAJORITY (60/98 last-column
      parents over reduced monoT cores, values \<le>3 len \<le>4; \<open>python/_condA_loc2.py\<close>),
      where row-0 \<open>p = Joints M J\<^sup>*\<close> (37 cases) and row-1 \<open>p\<close> sits in the diagonal
      trunk with \<open>entry M 1 p = p = npJ - 1\<close> and \<open>entry M 1 (Lng M-1) = npJ\<close> (23
      cases).  This needs the joint/block-start relation
      \<open>entry M i (Lng M-1) = (joint value) + 1\<close> from the \<open>NJ\<close> head construction
      (@{thm [source] entry_NJ_1_0}, @{thm [source] fin_Red_NJ_leftend}) — NOT
      derivable from the in-block drop alone.
  (B) deriving \<open>RedCondA (Red (NJ M J\<^sup>*))\<close> at column \<open>kk\<close> from the IH: the IH
      (@{thm [source] kst_reduced_imp_condAB_monoT_core_cond}) needs left end
      \<open>(0,0)\<close>, but \<open>entry (Red (NJ M J\<^sup>*)) 0 0 = npJ M J\<^sup>*\<close>
      (@{thm [source] wf15_inblock_N_core}); so the IH applies to the diagonal-
      prefixed \<open>N\<close>, and \<open>RedCondA (Red (NJ M J\<^sup>*))\<close> must be transferred back across
      the diagonal-prefix drop (a further drop-correspondence layer on the WHOLE
      \<open>RedCondA\<close>, not just the last column).
  Both are separate multi-lemma programs; \<open>condA_top_all\<close> was NOT closed this run.\<close>

lemma wf16_inblock_parent_corr:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  defines "ee \<equiv> Joints M ! Jstar + 1 - npJ M Jstar"
  defines "off \<equiv> Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J))) [0..<Jstar]))"
  defines "kk \<equiv> Lng (NJ M Jstar) - 1"
  defines "Rs \<equiv> Red (NJ M Jstar)"
  shows "Lng M - 1 = off + kk
       \<and> kk < Lng Rs
       \<and> Lng (NJ M Jstar) < Lng M
       \<and> drop off M = (IncrFirst ^^ ee) Rs
       \<and> (\<forall>i\<le>1. \<forall>p. off \<le> p \<longrightarrow>
              (nextR M i p (Lng M - 1) \<longleftrightarrow> nextR Rs i (p - off) kk))
       \<and> (\<forall>i\<le>1. \<forall>p. off \<le> p \<longrightarrow> hasParent M i (Lng M - 1) \<longrightarrow> parent M i (Lng M - 1) = p
              \<longrightarrow> hasParent Rs i kk \<and> parent Rs i kk = p - off)
       \<and> (entry M 1 (Lng M - 1) = entry Rs 1 kk)
       \<and> (entry M 0 (Lng M - 1) = entry Rs 0 kk + ee)"
proof -
  let ?blk = "(IncrFirst ^^ ee) Rs"
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  \<comment> \<open>Locate the last block (GREEN @{thm [source] kfwd_lastblock_locate}).\<close>
  have loc: "drop off (Red M) = (IncrFirst ^^ (Joints M ! Jstar + 1 - npJ M Jstar)) (Red (NJ M Jstar))
       \<and> (IncrFirst ^^ (Joints M ! Jstar + 1 - npJ M Jstar)) (Red (NJ M Jstar))
            = (IncrFirst ^^ (Joints M ! Jstar + 1 - npJ M Jstar)) (Red (NJ M Jstar))
       \<and> Lng (NJ M Jstar) = Lng (Br M ! Jstar)
       \<and> Lng (NJ M Jstar) < Lng M
       \<and> Lng (Br M) \<noteq> 0"
    unfolding Jstar_def off_def
    by (rule kfwd_lastblock_locate[OF M mono e00 e10 tne])
  have dropoff: "drop off M = ?blk"
    using loc redM unfolding ee_def Rs_def by simp
  have NJlt: "Lng (NJ M Jstar) < Lng M" using loc by simp
  have NJne: "NJ M Jstar \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M Jstar \<in> T_PS" using NJne by (simp add: T_PS_def)
  have lRs: "Lng Rs = Lng (NJ M Jstar)"
    unfolding Rs_def by (rule m_6_5_Lng_Red[OF NJT])
  have lblk: "Lng ?blk = Lng (NJ M Jstar)" using lRs by simp
  have lenrel: "Lng M - off = Lng (NJ M Jstar)"
  proof -
    have "Lng (drop off M) = Lng M - off" by simp
    thus ?thesis using dropoff lblk by simp
  qed
  have NJpos: "0 < Lng (NJ M Jstar)" using NJne by (cases "NJ M Jstar") auto
  have offle: "off \<le> Lng M" using lenrel NJpos by linarith
  have Leq: "Lng M - 1 = off + kk"
    unfolding kk_def using lenrel NJpos offle by linarith
  have kkLT: "kk < Lng Rs"
    unfolding kk_def using NJpos lRs by linarith
  \<comment> \<open>--- nextR correspondence for in-block parent indices \<open>off \<le> p\<close> ---\<close>
  have corr: "\<forall>i\<le>1. \<forall>p::nat. off \<le> p \<longrightarrow>
                (nextR M i p (Lng M - 1) \<longleftrightarrow> nextR Rs i (p - off) kk)"
  proof (intro allI impI)
    fix i p :: nat assume i: "i \<le> 1" and pge: "off \<le> p"
    show "nextR M i p (Lng M - 1) \<longleftrightarrow> nextR Rs i (p - off) kk"
    proof (cases "p < Lng M")
      case pin: True
      have a1: "p - off < Lng M - off" using pge pin by linarith
      have a2: "(Lng M - 1) - off < Lng M - off" using Leq kkLT lRs lenrel by linarith
      have step1: "nextR (drop off M) i (p - off) ((Lng M - 1) - off)
                     = nextR M i (off + (p - off)) (off + ((Lng M - 1) - off))"
        by (rule poper_nextR_drop[OF a1 a2])
      have e_p: "off + (p - off) = p" using pge by simp
      have e_j: "off + ((Lng M - 1) - off) = Lng M - 1" using Leq by simp
      have e_kk: "(Lng M - 1) - off = kk" using Leq by simp
      have stepM: "nextR M i p (Lng M - 1)
                     = nextR (drop off M) i (p - off) kk"
        using step1 e_p e_j e_kk by simp
      have stepB: "nextR (drop off M) i (p - off) kk = nextR Rs i (p - off) kk"
        using dropoff incf_pow_nextR[OF i, of ee Rs "p - off" kk] by simp
      show ?thesis using stepM stepB by simp
    next
      case pout: False
      \<comment> \<open>\<open>p \<ge> Lng M\<close>: both sides false (out of range).\<close>
      have pNL: "\<not> p < Lng M" using pout by simp
      have lhsF: "\<not> nextR M i p (Lng M - 1)"
        unfolding nextR_def nextrel0_def nextrel1_def using pNL by simp
      have poff: "\<not> (p - off) < Lng Rs" using pout offle lenrel lRs by linarith
      have rhsF: "\<not> nextR Rs i (p - off) kk"
        unfolding nextR_def nextrel0_def nextrel1_def using poff by simp
      show ?thesis using lhsF rhsF by simp
    qed
  qed
  \<comment> \<open>--- hasParent/parent transfer for an in-block parent ---\<close>
  have parcorr: "\<forall>i\<le>1. \<forall>p::nat. off \<le> p \<longrightarrow> hasParent M i (Lng M - 1) \<longrightarrow> parent M i (Lng M - 1) = p
              \<longrightarrow> hasParent Rs i kk \<and> parent Rs i kk = p - off"
  proof (intro allI impI)
    fix i p :: nat assume i: "i \<le> 1" and pge: "off \<le> p"
      and hpM: "hasParent M i (Lng M - 1)" and parM: "parent M i (Lng M - 1) = p"
    obtain q where q: "nextR M i q (Lng M - 1)"
      and uq: "\<And>r. nextR M i r (Lng M - 1) \<Longrightarrow> r = q"
      using hpM unfolding hasParent_def by blast
    have parq: "parent M i (Lng M - 1) = q"
      unfolding parent_def using q uq by (rule the_equality)
    have pq: "p = q" using parM parq by simp
    have nM: "nextR M i p (Lng M - 1)" using q pq by simp
    have nB: "nextR Rs i (p - off) kk" using corr i pge nM by blast
    \<comment> \<open>Uniqueness in \<open>Rs\<close>: any \<open>nextR Rs i r kk\<close> pulls back to \<open>nextR M i (off+r) j1\<close>.\<close>
    have uniqB: "\<And>r. nextR Rs i r kk \<Longrightarrow> r = p - off"
    proof -
      fix r assume rr: "nextR Rs i r kk"
      have offr: "off \<le> off + r" by simp
      have "nextR M i (off + r) (Lng M - 1)" using corr i offr rr by simp
      hence "off + r = q" using uq by simp
      thus "r = p - off" using pq by simp
    qed
    have hpB: "hasParent Rs i kk" unfolding hasParent_def using nB uniqB by blast
    have parB: "parent Rs i kk = p - off"
      unfolding parent_def using nB by (rule the_equality) (rule uniqB)
    show "hasParent Rs i kk \<and> parent Rs i kk = p - off" using hpB parB by blast
  qed
  \<comment> \<open>--- entry transfers (from BRICK 1) ---\<close>
  \<comment> \<open>\<open>wf15\<close>'s \<open>kk\<close>/\<open>ee\<close> defines expand to exactly the same inline terms as ours;
     project the two entry conjuncts (conjuncts 3,4 of the brick).\<close>
  note B1 = wf15_lastblock_entry_transfer[OF M mono e00 e10 tne]
  have e0: "entry M 0 (Lng M - 1) = entry Rs 0 kk + ee"
    using conjunct1[OF conjunct2[OF conjunct2[OF B1]]]
    unfolding Rs_def Jstar_def ee_def kk_def by simp
  have e1: "entry M 1 (Lng M - 1) = entry Rs 1 kk"
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF B1]]]]
    unfolding Rs_def Jstar_def kk_def by simp
  show ?thesis
    using Leq kkLT NJlt dropoff corr parcorr e0 e1 by (intro conjI)
qed


section \<open>Front A (wf17) — \<open>condA_top\<close> diagonal-prefix \<open>RedCondA\<close> transfer (B)\<close>

text \<open>WF17 BRICK (B): DIAGONAL-PREFIX \<open>RedCondA\<close> TRANSFER.  For the in-block
  (\<open>J\<^sub>1 > 0\<close>) regime of the keystone forward, the article applies the induction
  hypothesis to the diagonal-prefixed sequence \<open>N := diagSeq 0 d \<oplus> R\<^sup>*\<close>
  (\<open>d = R\<^sup>*\<^bsub>1,0\<^esub>-1\<close>), which has left end \<open>(0,0)\<close> and is strictly shorter, obtaining
  \<open>RedCondA N\<close> (content.md 1170-1216).  This brick transfers \<open>RedCondA\<close> from the
  diagonal-prefixed \<open>N\<close> back to its tail \<open>R\<^sup>*\<close>.

  ROUTE (sound, GREEN-cited; the naive "diagonal columns are never parents of
  crossing-in tail columns" is FALSE — empirically a tail column's \<open>N\<close>-parent
  often lies in the diagonal — so we go the other way): the only direction needed
  for \<open>RedCondA R\<^sup>*\<close> is the FORWARD lift.  Whenever \<open>R\<^sup>*\<close> has a (necessarily unique)
  parent \<open>p\<close> of a column \<open>j\<close> in row \<open>i\<close>, the \<open>nextR\<close> edge lifts UP across the
  diagonal prefix by the unconditional drop-correspondence
  @{thm [source] poper_nextR_drop} (since \<open>drop (Suc d) N = R\<^sup>*\<close> by
  @{thm [source] ecrux_drop_tail}) to \<open>nextR N i (Suc d+p) (Suc d+j)\<close>.  Parents in
  \<open>N\<close> are unique UNCONDITIONALLY (@{thm [source] idxsum_parent0_unique} row 0,
  @{thm [source] nextR1_unique} row 1), so \<open>hasParent N i (Suc d+j)\<close> with parent
  exactly \<open>Suc d+p\<close>; the entry relation of \<open>RedCondA N\<close> at that tail column then
  reads back verbatim (entries past the length-\<open>Suc d\<close> diagonal are \<open>R\<^sup>*\<close>'s entries,
  \<open>nth_append\<close>) to \<open>entry R\<^sup>* i p + 1 = entry R\<^sup>* i j\<close>.  EMPIRICALLY TRUE: 0 failures
  over 17472 arbitrary \<open>(R\<^sup>*, d)\<close> pairs (\<open>python/wf17_general.py\<close>; the implication
  needs neither \<open>monoT\<close> nor reducedness of \<open>R\<^sup>*\<close>).  SOUND — cites only GREEN
  @{thm [source] poper_nextR_drop}, @{thm [source] ecrux_drop_tail},
  @{thm [source] idxsum_parent0_unique}, @{thm [source] nextR1_unique} and the
  library; never a \<open>p_*\<close> stub nor the goal.\<close>

\<comment> \<open>Entries past the length-\<open>Suc d\<close> diagonal prefix are exactly \<open>R\<^sup>*\<close>'s entries.\<close>
lemma wf17_entry_diag_tail:
  "entry (diagSeq 0 d @ Rs) i (Suc d + p) = entry Rs i p"
proof -
  have ld: "length (diagSeq 0 d) = Suc d" by simp
  have "(diagSeq 0 d @ Rs) ! (Suc d + p) = Rs ! p"
    using ld by (simp add: nth_append)
  thus ?thesis by (simp add: entry_def)
qed

\<comment> \<open>Parents in any \<open>M\<close> are unique in both rows (row 0/1 specialisation packaged).\<close>
lemma wf17_nextR_unique:
  assumes "i \<le> 1" "nextR M i a k" "nextR M i b k"
  shows "a = b"
proof (cases "i = 0")
  case True
  thus ?thesis using assms(2,3) by (rule_tac idxsum_parent0_unique) simp_all
next
  case False
  hence "i = 1" using assms(1) by simp
  thus ?thesis using assms(2,3) by (simp add: nextR1_unique)
qed

lemma wf17_RedCondA_diag_tail:
  assumes rcaN: "RedCondA (diagSeq 0 d @ Rs)"
  shows "RedCondA Rs"
  unfolding RedCondA_def
proof (intro allI impI)
  fix i j :: nat
  assume i: "i \<le> 1" and hp: "hasParent Rs i j"
  let ?N = "diagSeq 0 d @ Rs"
  let ?c = "Suc d"
  \<comment> \<open>The (unique) \<open>R\<^sup>*\<close>-parent \<open>p\<close> of \<open>j\<close> in row \<open>i\<close>.\<close>
  obtain p where p: "nextR Rs i p j" and uq: "\<And>r. nextR Rs i r j \<Longrightarrow> r = p"
    using hp unfolding hasParent_def by blast
  have parp: "parent Rs i j = p"
    unfolding parent_def using p uq by (rule the_equality)
  \<comment> \<open>Range bounds from the \<open>nextR\<close> edge: \<open>p < j < Lng R\<^sup>*\<close>.\<close>
  have pj: "p < j" and jL: "j < Lng Rs"
    using p unfolding nextR_def nextrel0_def nextrel1_def
    by (auto split: if_splits)
  have pL: "p < Lng Rs" using pj jL by linarith
  \<comment> \<open>\<open>drop ?c ?N = R\<^sup>*\<close> and the length identity \<open>Lng ?N - ?c = Lng R\<^sup>*\<close>.\<close>
  have dropN: "drop ?c ?N = Rs" by (rule ecrux_drop_tail)
  have LN: "Lng ?N = ?c + Lng Rs" by simp
  have a1: "p < Lng ?N - ?c" using pL LN by simp
  have a2: "j < Lng ?N - ?c" using jL LN by simp
  \<comment> \<open>Lift the parent edge UP across the diagonal prefix (drop-correspondence).\<close>
  have nN: "nextR ?N i (?c + p) (?c + j)"
    using poper_nextR_drop[OF a1 a2, of i] dropN p by simp
  \<comment> \<open>Uniqueness of the \<open>N\<close>-parent of \<open>?c + j\<close> (unconditional, both rows).\<close>
  have uqN: "\<And>r. nextR ?N i r (?c + j) \<Longrightarrow> r = ?c + p"
    by (rule wf17_nextR_unique[OF i _ nN])
  have hpN: "hasParent ?N i (?c + j)"
    unfolding hasParent_def using nN uqN by blast
  have parN: "parent ?N i (?c + j) = ?c + p"
    unfolding parent_def using nN by (rule the_equality) (rule uqN)
  \<comment> \<open>\<open>RedCondA N\<close> at the tail column \<open>?c + j\<close>.\<close>
  have relN: "entry ?N i (parent ?N i (?c + j)) + 1 = entry ?N i (?c + j)"
    using rcaN hpN i unfolding RedCondA_def by blast
  \<comment> \<open>Read entries back to \<open>R\<^sup>*\<close> (entries past the prefix are \<open>R\<^sup>*\<close>'s).\<close>
  have eP: "entry ?N i (?c + p) = entry Rs i p" by (rule wf17_entry_diag_tail)
  have eJ: "entry ?N i (?c + j) = entry Rs i j" by (rule wf17_entry_diag_tail)
  have "entry Rs i p + 1 = entry Rs i j"
    using relN parN eP eJ by simp
  thus "entry Rs i (parent Rs i j) + 1 = entry Rs i j" using parp by simp
qed


section \<open>Front B (wf17-A) — \<open>condA_top\<close> CROSS-BLOCK half (\<open>p < off\<close>) at the last column\<close>

text \<open>WF17-A.  For a reduced \<open>monoT\<close> core \<open>M\<close> with \<open>M\<^sub>0 = (0,0)\<close> on the NONTRUNK
  branch (\<open>TrMax M \<noteq> Lng M - 1\<close>), let \<open>J\<^sup>* = Lng (Br M) - 1\<close> be the last branch and
  \<open>off\<close> the last-block start index.  This is the CROSS-BLOCK half of
  \<open>condA_top\<close> (parent of the last column \<open>p < off\<close>); empirically the MAJORITY
  (60/98 last-column parents over reduced \<open>monoT\<close> cores, \<open>python/_wf17_crossblock.py\<close>).

  BRICK 0 (\<open>off = FirstNodes M ! J\<^sup>*\<close>, unconditional structural identity).  The
  last-block start \<open>off = Suc (TrMax M) + Lng (concat (map blk [0..<J\<^sup>*]))\<close> equals
  the last first node \<open>FirstNodes M ! J\<^sup>* = TrMax M + 1 + IdxSum (Br M) ! J\<^sup>*\<close>,
  because each earlier block \<open>blk J = (IncrFirst\<^bsup>e\<^sub>J\<^esup>)(Red (NJ M J))\<close> has the SAME
  length as \<open>Br M ! J\<close> (@{thm [source] Lng_funpow_IncrFirst},
  @{thm [source] m_6_5_Lng_Red}, @{thm [source] Lng_NJ}), so the cumulative block
  length equals \<open>IdxSum (Br M) ! J\<^sup>*\<close> (@{thm [source] idxsum_nth} +
  @{thm [source] length_concat}).  SOUND — pure length arithmetic over GREEN
  facts; no \<open>p_*\<close> stub.\<close>

lemma wf17_blk_len:
  assumes M: "M \<in> PT_PS" and J: "J < Lng (Br M)"
  shows "Lng ((IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))
         = Lng (Br M ! J)"
proof -
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M J])
  have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
  have "Lng ((IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))
        = Lng (Red (NJ M J))" by (rule Lng_funpow_IncrFirst)
  also have "\<dots> = Lng (NJ M J)" by (rule m_6_5_Lng_Red[OF NJT])
  also have "\<dots> = Lng (Br M ! J)" using brJne by (rule Lng_NJ)
  finally show ?thesis .
qed

lemma wf17_off_eq_firstnode:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  defines "off \<equiv> Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J))) [0..<Jstar]))"
  shows "off = FirstNodes M ! Jstar"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  have JstarBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  let ?blk = "\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))"
  \<comment> \<open>Cumulative block length = \<open>IdxSum (Br M) ! Jstar\<close>.\<close>
  have map_len: "map Lng (map ?blk [0..<Jstar]) = map (\<lambda>J. Lng (Br M ! J)) [0..<Jstar]"
  proof -
    have "map Lng (map ?blk [0..<Jstar]) = map (\<lambda>J. Lng (?blk J)) [0..<Jstar]"
      by simp
    also have "\<dots> = map (\<lambda>J. Lng (Br M ! J)) [0..<Jstar]"
    proof (rule map_cong[OF refl])
      fix J assume "J \<in> set [0..<Jstar]"
      hence "J < Jstar" by simp
      hence "J < Lng (Br M)" using JstarBr unfolding Jstar_def by simp
      thus "Lng (?blk J) = Lng (Br M ! J)" by (rule wf17_blk_len[OF Mpt])
    qed
    finally show ?thesis .
  qed
  have take_eq: "map (\<lambda>J. Lng (Br M ! J)) [0..<Jstar] = map length (take Jstar (Br M))"
  proof (rule nth_equalityI)
    have Jle: "Jstar \<le> Lng (Br M)" using JstarBr by simp
    show "length (map (\<lambda>J. Lng (Br M ! J)) [0..<Jstar]) = length (map length (take Jstar (Br M)))"
      using Jle by simp
    fix k assume "k < length (map (\<lambda>J. Lng (Br M ! J)) [0..<Jstar])"
    hence kJ: "k < Jstar" by simp
    have klt: "k < Lng (Br M)" using kJ JstarBr by simp
    have "map (\<lambda>J. Lng (Br M ! J)) [0..<Jstar] ! k = Lng (Br M ! k)"
      using kJ by simp
    moreover have "map length (take Jstar (Br M)) ! k = length (Br M ! k)"
      using kJ klt by (simp add: take_map[symmetric] min.absorb2 less_or_eq_imp_le)
    ultimately show "map (\<lambda>J. Lng (Br M ! J)) [0..<Jstar] ! k = map length (take Jstar (Br M)) ! k"
      by simp
  qed
  have cblk: "Lng (concat (map ?blk [0..<Jstar])) = sum_list (map length (take Jstar (Br M)))"
    by (simp only: length_concat map_len take_eq)
  have idx: "IdxSum (Br M) ! Jstar = sum_list (map length (take Jstar (Br M)))"
    using JstarBr by (intro idxsum_nth) simp
  have fn: "FirstNodes M ! Jstar = TrMax M + 1 + IdxSum (Br M) ! Jstar"
    by (rule FirstNodes_nth[OF JstarBr])
  show ?thesis
    unfolding off_def using cblk idx fn by simp
qed

text \<open>BRICK 1 (row-0 cross-block, singleton last block \<open>kk = 0\<close>).  When the last
  block is a SINGLETON (\<open>Lng (NJ M J\<^sup>*) = 1\<close>, equivalently \<open>kk = 0\<close>), the last
  column \<open>j\<^sub>1 = Lng M - 1\<close> coincides with the last first node
  \<open>off = FirstNodes M ! J\<^sup>*\<close> (BRICK 0), so its row-0 parent is the joint
  \<open>Joints M ! J\<^sup>* = parent M 0 (FirstNodes M ! J\<^sup>*)\<close> (@{thm [source] Joints_nth}),
  which lies on the diagonal trunk (\<open>Joints M ! J\<^sup>* \<le> TrMax M\<close>,
  @{thm [source] m_6_4_FirstNodes_TrMax_Joints}) where \<open>entry M 0 p = p\<close>
  (@{thm [source] ncons_diag_prefix_entry}); and the block-head value
  \<open>entry M 0 j\<^sub>1 = Joints M ! J\<^sup>* + 1\<close> (@{thm [source] fin_block_head} transported
  through \<open>drop off M = block\<close>) gives \<open>entry M 0 j\<^sub>1 = entry M 0 p + 1\<close>.

  This is the kernel of the CROSS-BLOCK row-0 case of \<open>condA_top\<close>: empirically the
  cross-block row-0 parent ALWAYS has \<open>kk = 0\<close> (217/217 over reduced \<open>monoT\<close> cores,
  \<open>python/_wf17_probe3.py\<close>), so this brick discharges the FULL row-0 cross-block
  obligation once the side-condition \<open>kk = 0\<close> is supplied.  SOUND — cites only
  GREEN @{thm [source] wf17_off_eq_firstnode}, @{thm [source] Joints_nth},
  @{thm [source] m_6_4_FirstNodes_TrMax_Joints}, @{thm [source] ncons_diag_prefix_entry},
  @{thm [source] fin_block_head}, @{thm [source] kfwd_lastblock_locate}; no \<open>p_*\<close> stub.

  RESIDUAL (reported, not faked): deriving \<open>kk = 0\<close> from cross-block-ness
  (\<open>p < off\<close>) is a SEPARATE obligation — empirically \<open>kk > 0\<close> forces the row-0
  parent in-block (206/206, \<open>python/_wf17_probe7.py\<close>), so the contrapositive
  \<open>kk > 0 \<Longrightarrow> off \<le> parent M 0 (Lng M-1)\<close> needs the block-internal row-0
  monotonicity of the reduced \<open>Rs = Red (NJ M J\<^sup>*)\<close> via @{thm [source] wf16_inblock_parent_corr};
  not closed this run.\<close>

lemma wf17_crossblock_row0:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and kk0: "Lng (NJ M (Lng (Br M) - 1)) = 1"
    and hp0: "hasParent M 0 (Lng M - 1)"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  shows "parent M 0 (Lng M - 1) = Joints M ! Jstar
       \<and> entry M 0 (Lng M - 1) = entry M 0 (Joints M ! Jstar) + 1"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  have JstarBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  define ee where "ee \<equiv> Joints M ! Jstar + 1 - npJ M Jstar"
  define off where "off \<equiv> Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J))) [0..<Jstar]))"
  \<comment> \<open>BRICK 0: \<open>off = FirstNodes M ! Jstar\<close>.\<close>
  have offFN: "off = FirstNodes M ! Jstar"
    unfolding off_def Jstar_def
    by (rule wf17_off_eq_firstnode[OF M mono e00 e10 tne])
  \<comment> \<open>kk = 0 means the last column is exactly \<open>off\<close>.\<close>
  note B16 = wf16_inblock_parent_corr[OF M mono e00 e10 tne]
  have Leq: "Lng M - 1 = off + (Lng (NJ M Jstar) - 1)"
    using conjunct1[OF B16] unfolding off_def Jstar_def by simp
  have j1off: "Lng M - 1 = off" using Leq kk0 unfolding Jstar_def by simp
  \<comment> \<open>parent of \<open>off = FirstNodes M ! Jstar\<close> is \<open>Joints M ! Jstar\<close>.\<close>
  have parJ: "parent M 0 (Lng M - 1) = Joints M ! Jstar"
    using j1off offFN Joints_nth[OF JstarBr] by simp
  \<comment> \<open>\<open>entry M 0 (Lng M - 1) = Joints M ! Jstar + 1\<close> (block head).\<close>
  have dropoff: "drop off M = (IncrFirst ^^ ee) (Red (NJ M Jstar))"
  proof -
    have "drop off M = (IncrFirst ^^ (Joints M ! Jstar + 1 - npJ M Jstar)) (Red (NJ M Jstar))"
      using conjunct1[OF kfwd_lastblock_locate[OF M mono e00 e10 tne]] redM
      unfolding off_def Jstar_def by simp
    thus ?thesis unfolding ee_def by simp
  qed
  have offlt: "off < Lng M" using j1off MT by (cases M) (auto simp: T_PS_def)
  have Moff: "M ! off = ((IncrFirst ^^ ee) (Red (NJ M Jstar))) ! 0"
  proof -
    have "M ! off = drop off M ! 0" using offlt by simp
    thus ?thesis using dropoff by simp
  qed
  have bhead: "entry ((IncrFirst ^^ ee) (Red (NJ M Jstar))) 0 0 = Joints M ! Jstar + 1"
    using fin_block_head[OF Mpt e00 e10 JstarBr] unfolding ee_def by simp
  have eoff: "entry M 0 off = Joints M ! Jstar + 1"
    using Moff bhead by (simp add: entry_def)
  have ej1: "entry M 0 (Lng M - 1) = Joints M ! Jstar + 1"
    using eoff j1off by simp
  \<comment> \<open>\<open>Joints M ! Jstar \<le> TrMax M\<close>, so \<open>entry M 0 (Joints M ! Jstar) = Joints M ! Jstar\<close>.\<close>
  have jle: "Joints M ! Jstar \<le> TrMax M"
    using m_6_4_FirstNodes_TrMax_Joints[OF Mpt JstarBr] by simp
  have ejoint: "entry M 0 (Joints M ! Jstar) = Joints M ! Jstar"
    by (rule ncons_diag_prefix_entry[OF M mono e00 e10 tne jle])
  have efinal: "entry M 0 (Lng M - 1) = entry M 0 (Joints M ! Jstar) + 1"
    using ej1 ejoint by simp
  show ?thesis using parJ efinal by blast
qed

text \<open>BRICK 2 (row-1 cross-block, singleton last block \<open>kk = 0\<close>).  Analogue of
  BRICK 1 for row 1.  With \<open>kk = 0\<close> the last column \<open>j\<^sub>1 = off = FirstNodes M ! J\<^sup>*\<close>,
  so its row-1 parent \<open>p = parent M 1 (FirstNodes M ! J\<^sup>*)\<close> satisfies
  \<open>npJ M J\<^sup>* = Suc p\<close> by definition of \<^const>\<open>npJ\<close> (the else-branch, since the branch
  row-1 head \<open>entry (Br M ! J\<^sup>*) 1 0 \<noteq> 0\<close> — required as a side-hypothesis here, and
  empirically forced 123/0 in this case, \<open>python/_wf17_probe9.py\<close>).  The joint sits
  in the diagonal trunk: \<open>npJ M J\<^sup>* \<le> Joints M ! J\<^sup>* + 1 \<le> TrMax M + 1\<close>
  (@{thm [source] npJ_le_Joints_Suc}, @{thm [source] m_6_4_FirstNodes_TrMax_Joints}),
  so \<open>p \<le> TrMax M\<close> and \<open>entry M 1 p = p\<close> (@{thm [source] ncons_diag_prefix_entry}).
  The last column's row-1 value reads the block's row-1 left end
  \<open>entry M 1 j\<^sub>1 = entry (Red (NJ M J\<^sup>*)) 1 0 = npJ M J\<^sup>*\<close>
  (@{thm [source] entry_funpow_IncrFirst1}, @{thm [source] m_6_6_Red_leftend_1},
  @{thm [source] entry_NJ_1_0}).  Hence \<open>entry M 1 j\<^sub>1 = npJ M J\<^sup>* = p + 1\<close>.

  CAVEAT (empirical, content.md 1214): the equation \<open>entry M 1 j\<^sub>1 = npJ M J\<^sup>*\<close> is
  the SINGLETON (\<open>kk = 0\<close>) fact; for \<open>kk > 0\<close> it can FAIL (3/157 at maxlen 5,
  e.g. \<open>M = (0,0)(1,1)(2,0)(2,2)(3,1)\<close> where \<open>entry M 1 j\<^sub>1 = 1\<close> but \<open>npJ M J\<^sup>* = 2\<close>),
  while \<open>entry M 1 j\<^sub>1 = p + 1\<close> survives but is exactly the \<open>condA\<close> conclusion
  (circular).  So BRICK 2 is the SOUND \<open>kk = 0\<close> kernel; the \<open>kk > 0\<close> row-1 case is
  the residual.  SOUND — cites only GREEN facts; no \<open>p_*\<close> stub.\<close>

lemma wf17_crossblock_row1:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and kk0: "Lng (NJ M (Lng (Br M) - 1)) = 1"
    and brnz: "entry (Br M ! (Lng (Br M) - 1)) 1 0 \<noteq> 0"
    and hp1: "hasParent M 1 (Lng M - 1)"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  shows "parent M 1 (Lng M - 1) = npJ M Jstar - 1
       \<and> npJ M Jstar = parent M 1 (Lng M - 1) + 1
       \<and> parent M 1 (Lng M - 1) \<le> TrMax M
       \<and> entry M 1 (parent M 1 (Lng M - 1)) = parent M 1 (Lng M - 1)
       \<and> entry M 1 (Lng M - 1) = npJ M Jstar"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  have JstarBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  define ee where "ee \<equiv> Joints M ! Jstar + 1 - npJ M Jstar"
  define off where "off \<equiv> Suc (TrMax M)
                  + Lng (concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                            (Red (NJ M J))) [0..<Jstar]))"
  have offFN: "off = FirstNodes M ! Jstar"
    unfolding off_def Jstar_def
    by (rule wf17_off_eq_firstnode[OF M mono e00 e10 tne])
  note B16 = wf16_inblock_parent_corr[OF M mono e00 e10 tne]
  have Leq: "Lng M - 1 = off + (Lng (NJ M Jstar) - 1)"
    using conjunct1[OF B16] unfolding off_def Jstar_def by simp
  have j1off: "Lng M - 1 = off" using Leq kk0 unfolding Jstar_def by simp
  \<comment> \<open>\<open>npJ M Jstar = Suc (parent M 1 (FirstNodes M ! Jstar))\<close> (npJ else-branch).\<close>
  have npJeq: "npJ M Jstar = Suc (parent M 1 (FirstNodes M ! Jstar))"
    using brnz unfolding Jstar_def npJ_def parent_def by simp
  have parFN: "parent M 1 (Lng M - 1) = parent M 1 (FirstNodes M ! Jstar)"
    using j1off offFN by simp
  have np_par: "npJ M Jstar = parent M 1 (Lng M - 1) + 1"
    using npJeq parFN by simp
  have par_np: "parent M 1 (Lng M - 1) = npJ M Jstar - 1"
    using np_par by simp
  \<comment> \<open>\<open>p \<le> TrMax M\<close> via \<open>npJ \<le> Joints + 1 \<le> TrMax + 1\<close>.\<close>
  have np_le: "npJ M Jstar \<le> Joints M ! Jstar + 1"
    by (rule npJ_le_Joints_Suc[OF Mpt e10 JstarBr])
  have jl: "Joints M ! Jstar \<le> TrMax M"
    using m_6_4_FirstNodes_TrMax_Joints[OF Mpt JstarBr] by simp
  have pTr: "parent M 1 (Lng M - 1) \<le> TrMax M"
    using np_par np_le jl by linarith
  have epTr: "entry M 1 (parent M 1 (Lng M - 1)) = parent M 1 (Lng M - 1)"
    by (rule ncons_diag_prefix_entry[OF M mono e00 e10 tne pTr])
  \<comment> \<open>\<open>entry M 1 (Lng M - 1) = npJ M Jstar\<close> (block row-1 left end).\<close>
  have dropoff: "drop off M = (IncrFirst ^^ ee) (Red (NJ M Jstar))"
  proof -
    have "drop off M = (IncrFirst ^^ (Joints M ! Jstar + 1 - npJ M Jstar)) (Red (NJ M Jstar))"
      using conjunct1[OF kfwd_lastblock_locate[OF M mono e00 e10 tne]] redM
      unfolding off_def Jstar_def by simp
    thus ?thesis unfolding ee_def by simp
  qed
  have offlt: "off < Lng M" using j1off MT by (cases M) (auto simp: T_PS_def)
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
  have ej1: "entry M 1 (Lng M - 1) = npJ M Jstar"
    using eoff1 j1off by simp
  show ?thesis using par_np np_par pTr epTr ej1 by blast
qed

end

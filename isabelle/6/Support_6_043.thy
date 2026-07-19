theory Support_6_043
  imports Frontier_6_063
begin

section \<open>Front B (wf18) — \<open>condA_top\<close> ROW-1 CROSS-BLOCK at \<open>kk > 0\<close> (the last sub-case)\<close>

text \<open>WF18.  The LAST \<open>condA_top\<close> sub-case: a reduced \<open>monoT\<close> core \<open>M\<close> with
  \<open>M\<^sub>0 = (0,0)\<close> on the NONTRUNK branch (\<open>TrMax M \<noteq> Lng M - 1\<close>), last branch
  \<open>J\<^sup>* = Lng (Br M) - 1\<close>, last-block start \<open>off = FirstNodes M ! J\<^sup>*\<close>,
  \<open>kk = Lng (NJ M J\<^sup>*) - 1 > 0\<close>, and the ROW-1 parent of the last column is
  CROSS-BLOCK: \<open>p := parent M 1 (Lng M - 1) < off\<close>.  Goal:
  \<open>entry M 1 p + 1 = entry M 1 (Lng M - 1)\<close> (the \<open>RedCondA\<close> obligation at the last
  column, row 1).

  EMPIRICAL TRUTH-CHECK (\<open>python\<close> over reduced \<open>monoT\<close> cores, maxlen 5, value 3;
  34 row-1 cross-block \<open>kk > 0\<close> cases).  The GOAL holds 0/34, and the chain below
  holds: \<open>p \<le> TrMax M\<close> 0/34, \<open>entry M 1 p = p\<close> 0/34,
  \<open>entry (Red (NJ M J\<^sup>*)) 1 kk = p + 1\<close> 0/34.  CRUCIALLY the kk=0 route is DEAD for
  \<open>kk > 0\<close>: \<open>entry R\<^sup>* 1 kk = npJ M J\<^sup>*\<close> FAILS 3/34, \<open>p + 1 = npJ M J\<^sup>*\<close> FAILS 3/34,
  \<open>parent M 1 off = p\<close> FAILS 3/34 (witness \<open>M = (0,0)(1,1)(2,0)(2,2)(3,1)\<close>, where
  \<open>p = 0\<close>, \<open>npJ M J\<^sup>* = 2\<close>, \<open>entry M 1 (Lng M-1) = 1 = p+1\<close>); so the row-1 value at
  the last column is \<open>p+1\<close>, NOT \<open>npJ\<close>, and the block-start parent differs from the
  last-column parent.

  STRUCTURE OF THE BRICK.  The two GREEN-derivable steps are banked here:
    (i)  \<open>entry M 1 p = p\<close>: since the cross-block row-1 parent lies in the diagonal
         trunk (hypothesis \<open>pTr : p \<le> TrMax M\<close>), @{thm [source] ncons_diag_prefix_entry}
         pins \<open>entry M 1 p = p\<close>.
    (ii) \<open>entry M 1 (Lng M - 1) = entry (Red (NJ M J\<^sup>*)) 1 kk\<close>: the last column's
         row-1 value is the block-internal left-end-relative value, by the GREEN
         in-block transfer @{thm [source] wf16_inblock_parent_corr} (its row-1
         entry conjunct, IncrFirst-invariant on row 1).
  Combining (i)+(ii) with the value pin \<open>valpin : entry (Red (NJ M J\<^sup>*)) 1 kk = Suc p\<close>
  closes the goal: \<open>entry M 1 (Lng M-1) = entry R\<^sup>* 1 kk = Suc p = entry M 1 p + 1\<close>.

  RESIDUAL (reported honestly, NOT faked — see [[subagent-worktree-pitfalls]]).
  Two obligations are stated as EXPLICIT hypotheses, supplied by Front A:
   - \<open>pTr : p \<le> TrMax M\<close>.  Empirically 0/34, but NOT derivable from \<open>p < off\<close>
     alone (\<open>off = FirstNodes M ! J\<^sup>* > TrMax M\<close> leaves room for earlier blocks
     between \<open>TrMax M\<close> and \<open>off\<close>); it requires that EARLIER blocks never row-1-parent
     the last column, only the diagonal trunk does.  The kk=0 derivation
     (\<open>p+1 = npJ \<le> Joints+1 \<le> TrMax+1\<close>) is INVALID here (\<open>p+1 = npJ\<close> fails 3/34).
   - \<open>valpin : entry (Red (NJ M J\<^sup>*)) 1 kk = Suc p\<close>.  This is EQUIVALENT to the goal
     (since \<open>entry M 1 (Lng M-1) = entry R\<^sup>* 1 kk\<close> by step (ii)).  It CANNOT be
     obtained from \<open>RedCondA (Red (NJ M J\<^sup>*))\<close>: empirically \<open>kk\<close> has NO row-1 parent
     in \<open>R\<^sup>*\<close> (34/34 \<open>\<not> hasParent R\<^sup>* 1 kk\<close>), so \<open>RedCondA R\<^sup>*\<close> is VACUOUS at \<open>kk\<close>.
     The value \<open>p+1\<close> is the raw last branch-tail row-1 value (the tail of
     \<open>Br M ! J\<^sup>*\<close>, unchanged by the \<open>NJ\<close> head and \<open>IncrFirst\<close>); it equals \<open>p+1\<close>
     precisely because \<open>M\<close> is reduced (\<open>RedCondA M\<close> at the last column), which is
     the keystone-forward fact under proof — so it is pinned only by the deeper
     Red-reproduction structure / the IH applied to the diagonal-prefixed
     \<open>N = diagSeq 0 (R\<^sup>*\<^bsub>1,0\<^esub>-1) \<oplus> R\<^sup>*\<close> at a column that DOES carry a parent, NOT
     by a one-step \<open>RedCondA R\<^sup>*\<close> read at \<open>kk\<close>.

  SOUND — cites only GREEN @{thm [source] ncons_diag_prefix_entry},
  @{thm [source] wf16_inblock_parent_corr} and the library; no \<open>p_*\<close> stub, no goal
  self-citation.\<close>

lemma wf18_crossblock_row1_kkpos:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and kkpos: "0 < Lng (NJ M (Lng (Br M) - 1)) - 1"
    and hp1: "hasParent M 1 (Lng M - 1)"
    and pcross: "parent M 1 (Lng M - 1) < FirstNodes M ! (Lng (Br M) - 1)"
    \<comment> \<open>Front A residual (R1): the cross-block row-1 parent lies in the diagonal trunk.\<close>
    and pTr: "parent M 1 (Lng M - 1) \<le> TrMax M"
    \<comment> \<open>Front A residual (R2): block-internal row-1 last value pin (the IH-supplied fact).\<close>
    and valpin: "entry (Red (NJ M (Lng (Br M) - 1))) 1 (Lng (NJ M (Lng (Br M) - 1)) - 1)
                   = Suc (parent M 1 (Lng M - 1))"
  shows "entry M 1 (parent M 1 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1)"
proof -
  define Jstar where "Jstar \<equiv> Lng (Br M) - 1"
  define Rs where "Rs \<equiv> Red (NJ M Jstar)"
  define kk where "kk \<equiv> Lng (NJ M Jstar) - 1"
  define p where "p \<equiv> parent M 1 (Lng M - 1)"
  \<comment> \<open>(i) the diagonal-trunk value of the cross-block parent.\<close>
  have epp: "entry M 1 p = p"
    unfolding p_def by (rule ncons_diag_prefix_entry[OF M mono e00 e10 tne pTr])
  \<comment> \<open>(ii) the last column's row-1 value is the block-internal value at \<open>kk\<close>.\<close>
  note B16 = wf16_inblock_parent_corr[OF M mono e00 e10 tne]
  have e1: "entry M 1 (Lng M - 1) = entry Rs 1 kk"
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF
            conjunct2[OF conjunct2[OF B16]]]]]]]
    unfolding Rs_def Jstar_def kk_def by simp
  \<comment> \<open>Value pin (R2) at \<open>kk\<close>.\<close>
  have ekk: "entry Rs 1 kk = Suc p"
    unfolding Rs_def Jstar_def kk_def p_def by (rule valpin)
  \<comment> \<open>Combine: \<open>entry M 1 p + 1 = Suc p = entry R\<^sup>* 1 kk = entry M 1 (Lng M-1)\<close>.\<close>
  have "entry M 1 p + 1 = Suc p" using epp by simp
  also have "\<dots> = entry Rs 1 kk" using ekk by simp
  also have "\<dots> = entry M 1 (Lng M - 1)" using e1 by simp
  finally show ?thesis unfolding p_def .
qed




section \<open>Front B (wf19) — \<open>valpin\<close>: the last input for \<open>condA_top\<close> row-1 \<open>kk>0\<close> cross-block\<close>

text \<open>WF19 BRICK (\<open>valpin\<close>).  The LAST missing input for @{thm [source]
  wf18_crossblock_row1_kkpos}.  For a reduced \<open>monoT\<close> core \<open>M\<close> with \<open>M\<^sub>0 = (0,0)\<close>
  on the NONTRUNK branch (\<open>TrMax M \<noteq> Lng M - 1\<close>), last branch \<open>J\<^sup>* = Lng (Br M)-1\<close>,
  \<open>R\<^sup>* = Red (NJ M J\<^sup>*)\<close>, \<open>kk = Lng (NJ M J\<^sup>*)-1 > 0\<close>, last-column row-1 parent
  CROSS-BLOCK (\<open>p = parent M 1 (Lng M-1) < FirstNodes M ! J\<^sup>*\<close>) and in the diagonal
  trunk (\<open>p \<le> TrMax M\<close>), the value pin is
  \<open>entry R\<^sup>* 1 kk = Suc p\<close>.

  WHY THE \<open>kk=0\<close> ROUTE IS DEAD AND THE IH IS NEEDED.  In \<open>R\<^sup>*\<close> the last column
  \<open>kk\<close> has NO row-1 parent (\<open>\<not> hasParent R\<^sup>* 1 kk\<close>, 34/34), so \<open>RedCondA R\<^sup>*\<close> is
  VACUOUS at \<open>kk\<close>; the value \<open>p+1\<close> is pinned only after prefixing the diagonal
  \<open>N = diagSeq 0 (R\<^sup>*\<^bsub>1,0\<^esub>-1) \<oplus> R\<^sup>*\<close>: the last column \<open>lastN = Lng N - 1\<close> then DOES
  acquire a row-1 parent FROM the diagonal prefix (the diagonal column whose
  row-1 value equals the parent value \<open>p\<close>), and \<open>RedCondA N\<close> — obtained by the
  keystone IH on the strictly-shorter \<open>N\<close> (Front A supplies it as the explicit
  hypothesis \<open>condA_N\<close>) — reads off \<open>entry N 1 (parent N 1 lastN) + 1
  = entry N 1 lastN\<close>.  With the parent VALUE pin \<open>entry N 1 (parent N 1 lastN) = p\<close>
  and the diagonal-tail entry identity \<open>entry N 1 lastN = entry R\<^sup>* 1 kk\<close>
  (@{thm [source] wf17_entry_diag_tail}, \<open>lastN = Suc d + kk\<close>), this closes
  \<open>entry R\<^sup>* 1 kk = p + 1 = Suc p\<close>.

  EMPIRICAL TRUTH-CHECK (\<open>python/_wf19_valpin.py\<close>, reduced \<open>monoT\<close> cores maxlen 5
  value 3; 34 row-1 cross-block \<open>kk>0\<close> cases).  Over those 34 cases: \<open>RedCondA N
  \<and> RedCondB N\<close> 0/34, the parent-value pin \<open>hasParent N 1 lastN \<and> entry N 1
  (parent N 1 lastN) = p\<close> 0/34, \<open>entry N 1 lastN = entry R\<^sup>* 1 kk\<close> 0/34,
  \<open>entry R\<^sup>* 1 kk = Suc p\<close> 0/34, and \<open>\<not> hasParent R\<^sup>* 1 kk\<close> 0/34 (so the
  one-step \<open>RedCondA R\<^sup>*\<close> read is genuinely vacuous).  The diagonal-parent index is
  \<open>q = entry R\<^sup>* 1 kk - 1 = p\<close> with \<open>entry N 1 q = q\<close> (a diagonal column), and the
  \<open>nextrel1 N 1 q lastN\<close> minimality holds 0/34.

  RESIDUALS (reported honestly, NOT faked — see [[subagent-worktree-pitfalls]]).
  Two facts are stated as EXPLICIT hypotheses (Front A supplies them; the keystone
  IH delivers the first, the diagonal-prefix \<open>nextrel1\<close> structure the second):
   - \<open>condA_N : RedCondA N\<close>.  The keystone IH on \<open>N\<close> (strictly shorter, left end
     \<open>(0,0)\<close>); this is the only non-circular source of the value (\<open>RedCondA R\<^sup>*\<close>
     itself is vacuous at \<open>kk\<close>).
   - \<open>parpin : hasParent N 1 lastN \<and> entry N 1 (parent N 1 lastN) = p\<close>.  The
     parent-VALUE pin of the last column of \<open>N\<close>: \<open>lastN\<close>'s unique row-1 parent in
     \<open>N\<close> is the diagonal column at index \<open>q = entry R\<^sup>* 1 kk - 1\<close>, whose row-1 value
     is \<open>q\<close>, and \<open>q = p\<close> (the diagonal-trunk value of the cross-block last-column
     parent).  Pinning the \<open>nextrel1 N 1 q lastN\<close> EDGE and \<open>q = p\<close> is the
     diagonal-prefix parent-reconstruction (template @{thm [source] a1_if_npJ_Red_pos}),
     a separate multi-lemma program over the \<open>Rs\<close>-tail glued to the diagonal; it is
     NOT discharged here.  Given it, this brick discharges everything else (the
     diagonal-tail entry transfer, the \<open>RedCondA N\<close> application, the arithmetic)
     and closes \<open>valpin\<close>.

  SOUND — cites only GREEN @{thm [source] wf17_entry_diag_tail}, the \<open>RedCondA\<close>
  definition and the library; no \<open>p_*\<close> stub, no goal self-citation
  (\<open>RedCondA R\<^sup>*\<close> is vacuous at \<open>kk\<close>, so this does NOT cite the conclusion).\<close>

lemma wf19_valpin:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and kkpos: "0 < Lng (NJ M (Lng (Br M) - 1)) - 1"
    and hp1: "hasParent M 1 (Lng M - 1)"
    and pcross: "parent M 1 (Lng M - 1) < FirstNodes M ! (Lng (Br M) - 1)"
    and pTr: "parent M 1 (Lng M - 1) \<le> TrMax M"
    \<comment> \<open>The diagonal prefix exists (\<open>R\<^sup>*\<^bsub>1,0\<^esub> > 0\<close>), so \<open>N\<close> carries the diagonal.\<close>
    and eRs10pos: "0 < entry (Red (NJ M (Lng (Br M) - 1))) 1 0"
    \<comment> \<open>Front A residual (IH): \<open>RedCondA N\<close> for the diagonal-prefixed core \<open>N\<close>.\<close>
    and condA_N: "RedCondA ((if 0 < entry (Red (NJ M (Lng (Br M) - 1))) 1 0
                              then diagSeq 0 (entry (Red (NJ M (Lng (Br M) - 1))) 1 0 - 1)
                              else [])
                            @ Red (NJ M (Lng (Br M) - 1)))"
    \<comment> \<open>Front A residual (parent-value pin): the last column of \<open>N\<close> has a row-1 parent
       whose row-1 value is \<open>p\<close>.\<close>
    and parpin:
      "hasParent ((if 0 < entry (Red (NJ M (Lng (Br M) - 1))) 1 0
                    then diagSeq 0 (entry (Red (NJ M (Lng (Br M) - 1))) 1 0 - 1)
                    else [])
                  @ Red (NJ M (Lng (Br M) - 1))) 1
                 (Lng ((if 0 < entry (Red (NJ M (Lng (Br M) - 1))) 1 0
                         then diagSeq 0 (entry (Red (NJ M (Lng (Br M) - 1))) 1 0 - 1)
                         else [])
                       @ Red (NJ M (Lng (Br M) - 1))) - 1)
       \<and> entry ((if 0 < entry (Red (NJ M (Lng (Br M) - 1))) 1 0
                  then diagSeq 0 (entry (Red (NJ M (Lng (Br M) - 1))) 1 0 - 1)
                  else [])
                @ Red (NJ M (Lng (Br M) - 1))) 1
               (parent ((if 0 < entry (Red (NJ M (Lng (Br M) - 1))) 1 0
                          then diagSeq 0 (entry (Red (NJ M (Lng (Br M) - 1))) 1 0 - 1)
                          else [])
                        @ Red (NJ M (Lng (Br M) - 1))) 1
                       (Lng ((if 0 < entry (Red (NJ M (Lng (Br M) - 1))) 1 0
                               then diagSeq 0 (entry (Red (NJ M (Lng (Br M) - 1))) 1 0 - 1)
                               else [])
                             @ Red (NJ M (Lng (Br M) - 1))) - 1))
         = parent M 1 (Lng M - 1)"
  shows "entry (Red (NJ M (Lng (Br M) - 1))) 1 (Lng (NJ M (Lng (Br M) - 1)) - 1)
           = Suc (parent M 1 (Lng M - 1))"
proof -
  define Jstar where "Jstar \<equiv> Lng (Br M) - 1"
  define Rs where "Rs \<equiv> Red (NJ M Jstar)"
  define kk where "kk \<equiv> Lng (NJ M Jstar) - 1"
  define p where "p \<equiv> parent M 1 (Lng M - 1)"
  define d where "d \<equiv> entry Rs 1 0 - 1"
  define N where "N \<equiv> diagSeq 0 d @ Rs"
  \<comment> \<open>\<open>R\<^sup>*\<close> is nonempty (\<open>NJ\<close> is a cons), so \<open>kk = Lng R\<^sup>* - 1\<close> and \<open>Lng N - 1 = Suc d + kk\<close>.\<close>
  have NJne: "NJ M Jstar \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M Jstar \<in> T_PS" using NJne by (simp add: T_PS_def)
  have lRs: "Lng Rs = Lng (NJ M Jstar)"
    unfolding Rs_def by (rule m_6_5_Lng_Red[OF NJT])
  have Rspos: "0 < Lng Rs" using lRs NJne by (cases "NJ M Jstar") auto
  have kklt: "kk < Lng Rs" unfolding kk_def using lRs Rspos by linarith
  \<comment> \<open>The article's if-form diagonal-prefixed core, in local names.\<close>
  define Nif where
    "Nif \<equiv> (if 0 < entry Rs 1 0 then diagSeq 0 (entry Rs 1 0 - 1) else []) @ Rs"
  have eRs10pos': "0 < entry Rs 1 0"
    using eRs10pos unfolding Rs_def Jstar_def by simp
  \<comment> \<open>\<open>N\<close> coincides with the if-form (\<open>R\<^sup>*\<^bsub>1,0\<^esub> > 0\<close>).\<close>
  have NNif: "Nif = N"
    using eRs10pos' unfolding Nif_def N_def d_def by simp
  \<comment> \<open>The two Front A residuals, folded into the local \<open>Nif\<close> abbreviation.\<close>
  have condA_N': "RedCondA Nif"
    using condA_N unfolding Nif_def Rs_def Jstar_def by simp
  have parpin': "hasParent Nif 1 (Lng Nif - 1)
                 \<and> entry Nif 1 (parent Nif 1 (Lng Nif - 1)) = p"
    using parpin unfolding Nif_def Rs_def Jstar_def p_def by simp
  \<comment> \<open>\<open>Lng N = Suc d + Lng R\<^sup>*\<close>, so the last column index is \<open>Suc d + kk\<close>.\<close>
  have lenN: "Lng N = Suc d + Lng Rs" unfolding N_def by simp
  have lastNeq: "Lng N - 1 = Suc d + kk"
    unfolding kk_def using lenN lRs Rspos by linarith
  \<comment> \<open>The diagonal-tail entry identity: row-1 value at \<open>lastN\<close> is \<open>R\<^sup>*\<close>'s at \<open>kk\<close>.\<close>
  have etail: "entry N 1 (Lng N - 1) = entry Rs 1 kk"
    using lastNeq wf17_entry_diag_tail[of d Rs 1 kk] unfolding N_def by simp
  \<comment> \<open>The parent-value pin and \<open>RedCondA N\<close> (Front A residuals) in local names.\<close>
  have hpN: "hasParent N 1 (Lng N - 1)"
    using parpin' NNif by simp
  have parval: "entry N 1 (parent N 1 (Lng N - 1)) = p"
    using parpin' NNif by simp
  have rcaN: "RedCondA N" using condA_N' NNif by simp
  have relN: "entry N 1 (parent N 1 (Lng N - 1)) + 1 = entry N 1 (Lng N - 1)"
    using rcaN hpN unfolding RedCondA_def by blast
  \<comment> \<open>Chain: \<open>p + 1 = entry N 1 (parent ..) + 1 = entry N 1 lastN = entry R\<^sup>* 1 kk\<close>.\<close>
  have "Suc p = entry N 1 (parent N 1 (Lng N - 1)) + 1" using parval by simp
  also have "\<dots> = entry N 1 (Lng N - 1)" by (rule relN)
  also have "\<dots> = entry Rs 1 kk" by (rule etail)
  finally have "entry Rs 1 kk = Suc p" by simp
  thus ?thesis unfolding Rs_def kk_def Jstar_def p_def .
qed

end

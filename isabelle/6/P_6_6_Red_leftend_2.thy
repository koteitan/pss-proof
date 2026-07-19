theory P_6_6_Red_leftend_2
  imports Frontier_6_044
begin

text \<open>補題（\<open>Red\<close>と左端の関係） (2): a leading diagonal prefix is preserved by \<open>Red\<close>.\<close>

text \<open>m: §6.6 補題（\<open>Red\<close>と左端の関係） (2) — discharges
  @{text p_6_6_Red_leftend_2}.  A leading diagonal prefix is preserved by
  \<open>Red\<close>: if the first \<open>j\<^sub>0+1\<close> entries of a \<open>monoT\<close> \<open>M\<close> form the diagonal
  \<open>diagSeq u (j\<^sub>0+u)\<close>, then \<open>(Red M) ! j\<^sub>0 = (j\<^sub>0+u, j\<^sub>0+u)\<close>.

  Structure: \<open>monoT M\<close> excludes the \<open>zeroT\<close>/\<open>multiT\<close> branches.  The diagonal prefix
  forces \<open>entry M 0 0 = entry M 1 0 = u\<close>, so the \<open>m\<^sub>1\<^sub>0 = 0 \<and> m\<^sub>0\<^sub>0 > 0\<close> shift
  branch (case 4) is unreachable.  Two cases remain:
    \<^item> \<open>u = 0\<close> (core, \<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close>): \<open>Red M\<close> is a diagonal prefix
      \<open>diagSeq 0 t\<close> (\<open>t = Lng M - 1\<close> or \<open>t = TrMax M\<close>); since the prefix raises the
      trunk to \<open>j\<^sub>0 \<le> TrMax M \<le> t\<close>, position \<open>j\<^sub>0\<close> reads \<open>(j\<^sub>0, j\<^sub>0)\<close>.
    \<^item> \<open>u > 0\<close> (productive, \<open>m\<^sub>1\<^sub>0 = u > 0\<close>): \<open>Red M\<close> is read off
      \<open>N = Red (coreReduce M)\<close>, whose argument \<open>arg = diagSeq 0 (u-1) @ IncrFirst\<^bsup>u\<^esup>M\<close>
      is core with row-1 identity prefix up to \<open>u + j\<^sub>0\<close> (so \<open>TrMax arg \<ge> u + j\<^sub>0\<close>);
      \<open>arg\<close> unfolds (trunk / non-trunk core) to a diagonal prefix covering
      \<open>u + j\<^sub>0\<close>, giving \<open>N ! (u+j\<^sub>0) = (u+j\<^sub>0, u+j\<^sub>0)\<close>, and the output map yields
      \<open>(j\<^sub>0 + u, j\<^sub>0 + u)\<close>.
  No \<open>Red\<close> induction is needed (the only recursive \<open>Red\<close> call, \<open>N\<close>, is itself
  core and unfolds directly via @{thm [source] Red.psimps}).\<close>

lemma m_6_6_Red_leftend_2:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and j0le: "j0 \<le> Lng M - 1"
    and diag: "seg M 0 j0 = diagSeq u (j0 + u)"
  shows "(Red M) ! j0 = (j0 + u, j0 + u)"
proof -
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have j0lt: "j0 < Lng M" using j0le LMpos by linarith
  have Lseg: "Lng (seg M 0 j0) = Suc j0" by (simp add: Lng_seg)
  \<comment> \<open>entries of \<open>M\<close> on the diagonal prefix\<close>
  have eM: "\<And>i k. k \<le> j0 \<Longrightarrow> entry M i k = u + k"
  proof -
    fix i k assume kle: "k \<le> j0"
    have klt: "k < Lng (seg M 0 j0)" using kle Lseg by simp
    have "entry M i k = entry (seg M 0 j0) i k"
      using entry_seg[OF klt, of i] by simp
    also have "\<dots> = entry (diagSeq u (j0 + u)) i k" using diag by simp
    also have "\<dots> = u + k"
    proof -
      have "k < Suc (j0 + u) - u" using kle by simp
      thus ?thesis by (rule entry_diagSeq)
    qed
    finally show "entry M i k = u + k" .
  qed
  have m00u: "entry M 0 0 = u" using eM[where i=0 and k=0] by simp
  have m10u: "entry M 1 0 = u" using eM[where i=1 and k=0] by simp
  \<comment> \<open>the diagonal prefix raises the trunk to \<open>j\<^sub>0\<close>\<close>
  have trM_ge: "j0 \<le> TrMax M"
  proof -
    have steps: "\<forall>j'<j0. nextR M 1 j' (j' + 1)"
    proof (intro allI impI)
      fix j' assume j'lt: "j' < j0"
      have L: "Suc j' < Lng M" using j'lt j0lt by linarith
      have e0: "entry M 0 j' < entry M 0 (Suc j')"
        using eM[where i=0 and k=j'] eM[where i=0 and k="Suc j'"] j'lt by simp
      have e1: "entry M 1 j' < entry M 1 (Suc j')"
        using eM[where i=1 and k=j'] eM[where i=1 and k="Suc j'"] j'lt by simp
      from nextR1_consecutive[OF L e0 e1] show "nextR M 1 j' (j' + 1)" by simp
    qed
    from le_TrMax_intro[OF MT steps] show ?thesis .
  qed
  \<comment> \<open>\<open>monoT\<close> excludes zeroT / multiT\<close>
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  let ?j1  = "Lng M - 1"
  let ?j1' = "TrMax M"
  let ?m00 = "entry M 0 0"
  let ?m10 = "entry M 1 0"
  show ?thesis
  proof (cases "u = 0")
    case ucore: True
    have c0: "?m00 = 0" using m00u ucore by simp
    have c1: "?m10 = 0" using m10u ucore by simp
    have core: "?m00 = 0 \<and> ?m10 = 0" using c0 c1 by simp
    show ?thesis
    proof (cases "?j1' = ?j1")
      \<comment> \<open>Branch 3a: trunk diagonal output\<close>
      case trunk: True
      have rM: "Red M = diagSeq ?m10 (?m10 + ?j1)"
        using Red.psimps[OF dom] nz nmu c0 c1 trunk by (simp add: Let_def)
      have j0lej1: "j0 \<le> ?j1" using j0le .
      have "(Red M) ! j0 = diagSeq 0 (0 + ?j1) ! j0" using rM c1 by simp
      also have "\<dots> = (j0, j0)"
      proof -
        have lt: "j0 < Suc (0 + ?j1) - 0" using j0lej1 by simp
        show ?thesis using diagSeq_nth[OF lt] by simp
      qed
      finally show ?thesis using ucore by simp
    next
      \<comment> \<open>Branch 3b: diagSeq prefix + branch blocks\<close>
      case ntr: False
      let ?tail = "concat (map (\<lambda>J.
                (IncrFirst ^^ (Joints M ! J + 1
                    - (if entry (Br M ! J) 1 0 = 0 then 0
                       else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
                  (Red ((entry M 0 0 + Joints M ! J + 1,
                         entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                        # tl (Br M ! J))))
              [0..<Lng (Br M)])"
      have rM: "Red M = diagSeq 0 ?j1' @ ?tail"
        using Red.psimps[OF dom] nz nmu c0 c1 ntr by (simp add: Let_def)
      have "(Red M) ! j0 = (diagSeq 0 ?j1' @ ?tail) ! j0" using rM by simp
      also have "\<dots> = diagSeq 0 ?j1' ! j0"
      proof -
        have "j0 < length (diagSeq 0 ?j1')" using trM_ge by simp
        thus ?thesis by (simp add: nth_append)
      qed
      also have "\<dots> = (j0, j0)"
      proof -
        have lt: "j0 < Suc ?j1' - 0" using trM_ge by simp
        show ?thesis using diagSeq_nth[OF lt] by simp
      qed
      finally show ?thesis using ucore by simp
    qed
  next
    \<comment> \<open>Productive case: \<open>u > 0\<close>, so \<open>m\<^sub>1\<^sub>0 = u > 0\<close>.\<close>
    case upos: False
    have c1p: "0 < ?m10" using m10u upos by simp
    have nc: "\<not> (?m00 = 0 \<and> ?m10 = 0)" using c1p by simp
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
    \<comment> \<open>\<open>arg = coreReduce M\<close>, which is \<open>monoT\<close> / core\<close>
    have arg_eq_cr: "?arg = coreReduce M"
      using c1p by (simp add: coreReduce_def)
    have arg_mono: "monoT ?arg"
      using coreReduce_monoT_m10_pos[OF MT mono c1p] arg_eq_cr by simp
    have Larg: "Lng ?arg = ?m10 + Lng M"
      using c1p by (simp add: Lng_funpow_IncrFirst)
    have arg_nz: "\<not> zeroT ?arg"
    proof -
      have "Lng ?arg \<ge> 2" using c1p Larg LMpos by linarith
      thus ?thesis unfolding zeroT_def by linarith
    qed
    have arg_nmu: "\<not> multiT ?arg" using arg_mono by (simp add: multiT_def)
    have arg_c0: "entry ?arg 0 0 = 0" using c1p by (simp add: entry_diagSeq_append_lo)
    have arg_c1: "entry ?arg 1 0 = 0" using c1p by (simp add: entry_diagSeq_append_lo)
    have dom_arg: "Red_dom ?arg" by (rule m_6_5_Red_welldef[OF arg_T])
    \<comment> \<open>entries of \<open>arg\<close>: row 1 is the identity on \<open>0 .. m\<^sub>1\<^sub>0 + j\<^sub>0\<close>,
      row 0 agrees on the diagonal prefix \<open>0 .. m\<^sub>1\<^sub>0 - 1\<close>.\<close>
    have eArg: "\<And>p. p \<le> ?m10 + j0 \<Longrightarrow> entry ?arg 1 p = p"
    proof -
      fix p assume ple: "p \<le> ?m10 + j0"
      show "entry ?arg 1 p = p"
      proof (cases "p < ?m10")
        case True
        have "p \<le> ?m10 - 1" using True by simp
        thus ?thesis by (simp add: entry_diagSeq_append_lo)
      next
        case False
        let ?q = "p - ?m10"
        have pq: "p = ?m10 + ?q" using False by simp
        have qle: "?q \<le> j0" using ple by simp
        have qltM: "?q < Lng M" using qle j0lt by simp
        have qlt: "?q < Lng ((IncrFirst ^^ ?m10) M)" using qltM by simp
        have junc: "entry ?arg 1 (?m10 + ?q) = entry ((IncrFirst ^^ ?m10) M) 1 ?q"
        proof -
          have sk: "Suc (?m10 - 1) = ?m10" using c1p by simp
          have "entry (diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M) 1 (Suc (?m10 - 1) + ?q)
                  = entry ((IncrFirst ^^ ?m10) M) 1 ?q"
            by (rule entry_diagSeq_append_hi[OF qlt])
          thus ?thesis using sk by simp
        qed
        have "entry ((IncrFirst ^^ ?m10) M) 1 ?q = entry M 1 ?q"
          by (rule entry_funpow_IncrFirst1[OF qltM])
        also have "\<dots> = u + ?q" using eM[where i=1 and k="?q"] qle by simp
        also have "\<dots> = ?m10 + ?q" using m10u by simp
        finally show ?thesis using junc pq by simp
      qed
    qed
    \<comment> \<open>exact row-0 value of \<open>arg\<close> on \<open>0 .. m\<^sub>1\<^sub>0 + j\<^sub>0\<close>: identity below the junction,
      then \<open>p + m\<^sub>1\<^sub>0\<close> at / past it.  In all cases it is strictly increasing in \<open>p\<close>.\<close>
    have eArg0: "\<And>p. p \<le> ?m10 + j0 \<Longrightarrow>
                   entry ?arg 0 p = (if p < ?m10 then p else p + ?m10)"
    proof -
      fix p assume ple: "p \<le> ?m10 + j0"
      show "entry ?arg 0 p = (if p < ?m10 then p else p + ?m10)"
      proof (cases "p < ?m10")
        case True
        have "p \<le> ?m10 - 1" using True by simp
        thus ?thesis using True by (simp add: entry_diagSeq_append_lo)
      next
        case False
        let ?q = "p - ?m10"
        have pq: "p = ?m10 + ?q" using False by simp
        have qle: "?q \<le> j0" using ple by simp
        have qltM: "?q < Lng M" using qle j0lt by simp
        have qlt: "?q < Lng ((IncrFirst ^^ ?m10) M)" using qltM by simp
        have junc: "entry ?arg 0 (?m10 + ?q) = entry ((IncrFirst ^^ ?m10) M) 0 ?q"
        proof -
          have sk: "Suc (?m10 - 1) = ?m10" using c1p by simp
          have "entry (diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M) 0 (Suc (?m10 - 1) + ?q)
                  = entry ((IncrFirst ^^ ?m10) M) 0 ?q"
            by (rule entry_diagSeq_append_hi[OF qlt])
          thus ?thesis using sk by simp
        qed
        have "entry ((IncrFirst ^^ ?m10) M) 0 ?q = entry M 0 ?q + ?m10"
          by (rule entry_funpow_IncrFirst0[OF qltM])
        also have "\<dots> = (u + ?q) + ?m10" using eM[where i=0 and k="?q"] qle by simp
        also have "\<dots> = ?m10 + ?q + ?m10" using m10u by simp
        finally have "entry ?arg 0 p = ?m10 + ?q + ?m10" using junc pq by simp
        thus ?thesis using False pq by simp
      qed
    qed
    \<comment> \<open>\<open>arg\<close>'s trunk reaches \<open>m\<^sub>1\<^sub>0 + j\<^sub>0\<close>\<close>
    have trArg_ge: "?m10 + j0 \<le> TrMax ?arg"
    proof -
      have steps: "\<forall>p < ?m10 + j0. nextR ?arg 1 p (p + 1)"
      proof (intro allI impI)
        fix p assume plt: "p < ?m10 + j0"
        have L: "Suc p < Lng ?arg"
          using plt Larg j0lt by linarith
        have e1p:  "entry ?arg 1 p = p"      using eArg[of p] plt by simp
        have e1sp: "entry ?arg 1 (Suc p) = Suc p" using eArg[of "Suc p"] plt by simp
        have e1step: "entry ?arg 1 p < entry ?arg 1 (Suc p)" using e1p e1sp by simp
        \<comment> \<open>row 0 strictly increases at \<open>p\<close>\<close>
        have e0p: "entry ?arg 0 p = (if p < ?m10 then p else p + ?m10)"
          using eArg0[of p] plt by simp
        have e0sp: "entry ?arg 0 (Suc p) = (if Suc p < ?m10 then Suc p else Suc p + ?m10)"
          using eArg0[of "Suc p"] plt by simp
        have e0step: "entry ?arg 0 p < entry ?arg 0 (Suc p)"
          using e0p e0sp c1p by (auto split: if_splits)
        from nextR1_consecutive[OF L e0step e1step]
        show "nextR ?arg 1 p (p + 1)" by simp
      qed
      from le_TrMax_intro[OF arg_T steps] show ?thesis .
    qed
    \<comment> \<open>\<open>N = Red arg\<close> is diagonal up to \<open>TrMax arg\<close>; in particular at \<open>m\<^sub>1\<^sub>0\<close> and
      \<open>m\<^sub>1\<^sub>0 + j\<^sub>0\<close>.\<close>
    have N_diag: "\<And>p. p \<le> ?m10 + j0 \<Longrightarrow> entry ?N 0 p = p \<and> entry ?N 1 p = p"
    proof -
      let ?tail_arg = "concat (map (\<lambda>J.
              (IncrFirst ^^ (Joints ?arg ! J + 1
                  - (if entry (Br ?arg ! J) 1 0 = 0 then 0
                     else Suc (THE j. nextR ?arg 1 j (FirstNodes ?arg ! J)))))
                (Red ((entry ?arg 0 0 + Joints ?arg ! J + 1,
                       entry ?arg 1 0
                       + (if entry (Br ?arg ! J) 1 0 = 0 then 0
                          else Suc (THE j. nextR ?arg 1 j (FirstNodes ?arg ! J))))
                      # tl (Br ?arg ! J))))
            [0..<Lng (Br ?arg)])"
      fix p assume ple: "p \<le> ?m10 + j0"
      show "entry ?N 0 p = p \<and> entry ?N 1 p = p"
      proof (cases "TrMax ?arg = Lng ?arg - 1")
        case tr: True
        have rArg: "Red ?arg = diagSeq 0 (Lng ?arg - 1)"
          using Red.psimps[OF dom_arg] arg_nz arg_nmu arg_c0 arg_c1 tr
          by (simp add: Let_def)
        have plt: "p < Suc (Lng ?arg - 1) - 0"
          using ple trArg_ge tr by simp
        have "entry ?N 0 p = entry (diagSeq 0 (Lng ?arg - 1)) 0 p" using rArg by simp
        moreover have "entry ?N 1 p = entry (diagSeq 0 (Lng ?arg - 1)) 1 p" using rArg by simp
        ultimately show ?thesis using entry_diagSeq[OF plt, of 0] entry_diagSeq[OF plt, of 1] by simp
      next
        case ntr: False
        have rArg: "Red ?arg = diagSeq 0 (TrMax ?arg) @ ?tail_arg"
          using Red.psimps[OF dom_arg] arg_nz arg_nmu arg_c0 arg_c1 ntr
          by (simp add: Let_def)
        have ple_tr: "p \<le> TrMax ?arg" using ple trArg_ge by simp
        have e0: "entry ?N 0 p = p"
        proof -
          have "entry ?N 0 p = entry (diagSeq 0 (TrMax ?arg) @ ?tail_arg) 0 p" using rArg by simp
          also have "\<dots> = p" by (rule entry_diagSeq_append_lo[OF ple_tr])
          finally show ?thesis .
        qed
        have e1: "entry ?N 1 p = p"
        proof -
          have "entry ?N 1 p = entry (diagSeq 0 (TrMax ?arg) @ ?tail_arg) 1 p" using rArg by simp
          also have "\<dots> = p" by (rule entry_diagSeq_append_lo[OF ple_tr])
          finally show ?thesis .
        qed
        show ?thesis using e0 e1 by simp
      qed
    qed
    have N_m10: "entry ?N 0 ?m10 = ?m10 \<and> entry ?N 1 ?m10 = ?m10"
      using N_diag[of ?m10] by simp
    have N_m10j0: "entry ?N 0 (?m10 + j0) = ?m10 + j0 \<and> entry ?N 1 (?m10 + j0) = ?m10 + j0"
      using N_diag[of "?m10 + j0"] by simp
    \<comment> \<open>\<open>Lng N = Lng arg\<close>, so \<open>jN = Lng arg - 1 \<ge> m\<^sub>1\<^sub>0 + j\<^sub>0\<close>; the productive
      (then) branch is taken.\<close>
    have LN: "Lng ?N = Lng ?arg" by (rule m_6_5_Lng_Red[OF arg_T])
    have jN_ge: "?m10 + j0 \<le> ?jN"
    proof -
      have "?m10 + j0 \<le> TrMax ?arg" by (rule trArg_ge)
      also have "\<dots> \<le> Lng ?arg - 1"
        by (rule TrMax_bound[OF arg_T])
      finally show ?thesis using LN by simp
    qed
    have m10_le_jN: "?m10 \<le> ?jN" using jN_ge by simp
    \<comment> \<open>the slice \<open>seg N m10 jN\<close> is in \<open>PT_PS\<close> (productive condition).  We get this
      from the green brick @{thm [source] m_6_5_monoT_Red_m10pos}.\<close>
    have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
    have segN_PT: "seg ?N ?m10 ?jN \<in> PT_PS"
      using m_6_5_monoT_Red_m10pos[OF M_PT c1p] by simp
    have then_cond: "?m10 \<le> ?jN \<and> seg ?N ?m10 ?jN \<in> PT_PS"
      using m10_le_jN segN_PT by simp
    have rM': "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                  entry ?N 1 j))
                           [?m10..<Suc ?jN]"
      using rM then_cond by (simp add: Let_def del: upt_Suc)
    \<comment> \<open>read off position \<open>j\<^sub>0\<close>\<close>
    have idx: "[?m10..<Suc ?jN] ! j0 = ?m10 + j0"
      using jN_ge by (simp add: nth_upt del: upt_Suc)
    have len: "j0 < length [?m10..<Suc ?jN]"
      using jN_ge by (simp del: upt_Suc)
    have rdj0: "(Red M) ! j0 = (entry ?N 0 (?m10 + j0) - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                entry ?N 1 (?m10 + j0))"
    proof -
      have "(Red M) ! j0 = (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10 + entry ?N 1 ?m10,
                                  entry ?N 1 j)) ([?m10..<Suc ?jN] ! j0)"
        using rM' len by (simp add: nth_map del: upt_Suc)
      thus ?thesis using idx by simp
    qed
    have N00: "entry ?N 0 ?m10 = ?m10" using N_m10 by simp
    have N10: "entry ?N 1 ?m10 = ?m10" using N_m10 by simp
    have N0j: "entry ?N 0 (?m10 + j0) = ?m10 + j0" using N_m10j0 by simp
    have N1j: "entry ?N 1 (?m10 + j0) = ?m10 + j0" using N_m10j0 by simp
    have "(Red M) ! j0 = (?m10 + j0 - ?m10 + ?m10, ?m10 + j0)"
      using rdj0 N00 N10 N0j N1j by simp
    also have "\<dots> = (j0 + u, j0 + u)" using m10u by simp
    finally show ?thesis .
  qed
qed



lemma p_6_6_Red_leftend_2:
  assumes "M \<in> T_PS" "monoT M" "j0 \<le> Lng M - 1"
    "seg M 0 j0 = diagSeq u (j0 + u)"
  shows "(Red M) ! j0 = (j0 + u, j0 + u)"
  using assms by (rule m_6_6_Red_leftend_2)

end

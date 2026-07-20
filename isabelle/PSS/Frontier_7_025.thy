theory Frontier_7_025
  imports Support_7_021
begin

text \<open>§7.4 join-lift: if \<open>(s,c,b)\<close> is an scb-decomposition of a single-principal
  \<open>X\<close> around the principal block \<open>c\<close>, then prefixing \<open>X\<close> by \<open>Y\<close> via \<open>+\<^sub>B\<close>
  (which concatenates the principal lists) yields a deterministic
  scb-decomposition of \<open>Y +\<^sub>B X\<close> around the SAME \<open>c\<close>, obtained by re-bracketing
  the leading \<open>Y\<close>-part into the join.  The multi-component bridge transporting the
  \<open>m\<close>-basepoint position from the last \<open>P\<close>-component up to \<open>M\<close> (and identically for
  \<open>Pred M\<close>, since both share the \<open>Trans (take (Pcut M) M)\<close> prefix).\<close>

definition liftS :: "BT \<Rightarrow> Sym list \<Rightarrow> Sym list" where
  "liftS Y s = LP # flatBP (hd (untrm Y))
                  @ concat (map (\<lambda>r. CM # flatBP r) (tl (untrm Y))) @ CM # s"

text \<open>The \<open>Mark\<close>-analogue of @{thm [source] Trans_Pred_multi_last}: for a multi
  \<open>M \<in> RT\<^sub>PS\<close> with non-trivial last \<open>P\<close>-component \<open>PJ = drop (Pcut M) M\<close>, the
  predecessor's mark acts inside the last component (using that \<open>Pred M\<close> is
  itself multi with the same cut and last component \<open>Pred PJ\<close>).\<close>

lemma Mark_Pred_multi_last:
  assumes MR: "M \<in> RT_PS" and mu: "multiT M"
    and LPJ: "1 < Lng (drop (Pcut M) M)"
  shows "Mark (Pred M) m
         = (if Pred (drop (Pcut M) M) = [(0,0)] then Dpt 0 0\<^sub>B
            else Mark (Pred (drop (Pcut M) M)) (m - Pcut M))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  let ?c = "Pcut M"
  let ?A = "take ?c M"
  let ?PJ = "drop ?c M"
  have cut: "0 < ?c \<and> ?c \<le> Lng M - 1" using Pcut_le[OF L] by simp
  have LdropPJ: "Lng ?PJ = Lng M - ?c" by simp
  have cltj1: "?c < Lng M - 1"
  proof -
    have "Lng ?PJ = Lng M - ?c" by simp
    thus ?thesis using LPJ cut by linarith
  qed
  have lenlast_gt1: "1 < Lng (last (P M))"
    using poper_last_P_multi[OF mu L] LPJ by simp
  have predsplit: "Pred M = ?A @ Pred ?PJ"
    by (rule poper_Pred_split[OF cltj1 L])
  have Pdec: "P (Pred M) = butlast (P M) @ [Pred (last (P M))]"
    using pred_P_decomp[OF MT mu] lenlast_gt1 by simp
  have Pdec2: "P (Pred M) = P ?A @ [Pred ?PJ]"
  proof -
    have "butlast (P M) = P ?A" using poper_last_P_multi[OF mu L] by simp
    moreover have "last (P M) = ?PJ" using poper_last_P_multi[OF mu L] by simp
    ultimately show ?thesis using Pdec by simp
  qed
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
  have PAne: "P ?A \<noteq> []" by (rule P_nonempty)
  have lenPpred: "1 < length (P (Pred M))"
    using Pdec2 PAne by (cases "P ?A") auto
  have mupred: "multiT (Pred M)"
    using m_6_2_P_components_2[OF predT] lenPpred by simp
  have Lpred: "1 < Lng (Pred M)"
    by (rule multiT_imp_Lng_gt1[OF predT mupred])
  let ?cP = "Pcut (Pred M)"
  have lastPpred: "last (P (Pred M)) = drop ?cP (Pred M)
                   \<and> butlast (P (Pred M)) = P (take ?cP (Pred M))"
    by (rule poper_last_P_multi[OF mupred Lpred])
  have lastval: "last (P (Pred M)) = Pred ?PJ" using Pdec2 by simp
  have dropPred: "drop ?cP (Pred M) = Pred ?PJ"
    using lastPpred lastval by simp
  have takePred: "take ?cP (Pred M) = ?A"
  proof -
    have "take ?cP (Pred M) @ drop ?cP (Pred M) = Pred M" by simp
    hence "take ?cP (Pred M) @ Pred ?PJ = ?A @ Pred ?PJ"
      using dropPred predsplit by simp
    thus ?thesis by simp
  qed
  have LAc: "Lng ?A = ?c"
  proof -
    have "?c \<le> Lng M" using cut L by linarith
    thus ?thesis by simp
  qed
  have PcutEq: "?cP = ?c"
  proof -
    have "Lng (take ?cP (Pred M)) = Lng ?A" using takePred by simp
    moreover have "Lng (take ?cP (Pred M)) = min ?cP (Lng (Pred M))" by simp
    ultimately have "min ?cP (Lng (Pred M)) = ?c" using LAc by simp
    moreover have "?cP \<le> Lng (Pred M)" using Pcut_le[OF Lpred] by linarith
    ultimately show ?thesis by (simp add: min_def)
  qed
  have domKP: "\<And>k. Trans_Mark_dom (Inr (Pred M, k))"
    by (rule m_7_3_Mark_welldef[OF predRT])
  have LgtP: "\<not> Lng (Pred M) \<le> Suc 0" using Lpred by simp
  have nmonoP: "\<not> monoT (Pred M)" using mupred by (simp add: multiT_def)
  have PJeqP: "P (Pred M) ! (Lng (P (Pred M)) - 1) = drop ?cP (Pred M)"
    by (rule trans_multiT_last_component(1)[OF predT mupred])
  have c1: "(Pred M \<notin> RT_PS) = False" using predRT by simp
  have c2: "(Lng (Pred M) - 1 = 0) = False" using Lpred by simp
  have c3: "monoT (Pred M) = False" using nmonoP by simp
  have cutP: "0 < ?cP \<and> ?cP \<le> Lng (Pred M) - 1" using Pcut_le[OF Lpred] by simp
  have LdJP: "Lng (drop ?cP (Pred M)) = Lng (Pred M) - ?cP" by simp
  have meq2P: "Lng (Pred M) - 1 - Lng (drop ?cP (Pred M)) + 1 = ?cP"
    using LdJP cutP by linarith
  have markP: "Mark (Pred M) m =
      (if drop ?cP (Pred M) = [(0,0)] then Dpt 0 0\<^sub>B
       else Mark (drop ?cP (Pred M)) (m - ?cP))"
  proof -
    have raw: "Mark (Pred M) m =
        (if P (Pred M) ! (Lng (P (Pred M)) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
         else Mark (P (Pred M) ! (Lng (P (Pred M)) - 1))
                (m - (Lng (Pred M) - 1 - Lng (P (Pred M) ! (Lng (P (Pred M)) - 1)) + 1)))"
      by (subst Mark.psimps[OF domKP]) (simp only: c1 c2 c3 if_False Let_def)
    show ?thesis unfolding raw PJeqP using meq2P by simp
  qed
  show ?thesis using markP dropPred takePred PcutEq by simp
qed

lemma scb_addBT_left:
  assumes d: "scb_decomp X s c b"
    and X1: "length (untrm X) = 1"
    and Yne: "untrm Y \<noteq> []"
  shows "scb_decomp (Y +\<^sub>B X) (liftS Y s) c (b @ [RP])"
proof -
  obtain x0 where xs: "untrm X = [x0]" using X1 by (cases "untrm X") auto
  obtain ys where ysd: "untrm Y = ys" by simp
  have ysne: "ys \<noteq> []" using Yne ysd by simp
  have Xne: "X \<noteq> Trm []" using xs by (cases X) auto
  have flatX: "flatBT X = flatBP x0" using xs by (cases X) simp
  from d have eq: "flatBT X = s @ c @ b"
    and ptc: "isPTB_str c" and rb: "\<forall>z \<in> set b. z = RP"
    using Xne by (auto simp: scb_decomp_def)
  have eqX: "flatBP x0 = s @ c @ b" using eq flatX by simp
  obtain p ps where ysc: "ys = p # ps"
    using ysne by (cases ys) auto
  have yx: "Y +\<^sub>B X = Trm (ys @ [x0])"
    using xs ysd by (cases X; cases Y) auto
  obtain q qs where qqs: "ps @ [x0] = q # qs" by (cases ps) auto
  have lst: "ys @ [x0] = p # q # qs" using ysc qqs by simp
  have flatYX: "flatBT (Y +\<^sub>B X)
      = LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (ps @ [x0]))) @ [RP]"
    using yx lst qqs by simp
  have concEq: "concat (map (\<lambda>r. CM # flatBP r) (ps @ [x0]))
      = concat (map (\<lambda>r. CM # flatBP r) ps) @ CM # flatBP x0" by simp
  let ?yf = "flatBP p @ concat (map (\<lambda>r. CM # flatBP r) ps)"
  have flatYX2: "flatBT (Y +\<^sub>B X) = (LP # ?yf @ CM # s) @ c @ (b @ [RP])"
    using flatYX concEq eqX by simp
  have liftSeq: "liftS Y s = LP # ?yf @ CM # s"
    using ysd ysc by (simp add: liftS_def)
  have rb': "\<forall>z \<in> set (b @ [RP]). z = RP" using rb by simp
  show ?thesis
    unfolding scb_decomp_def
    using flatYX2 liftSeq ptc rb' by simp
qed

text \<open>\<open>Trans\<close> of a (reduced) monotone / principal sequence is a single principal
  term (\<open>length (untrm \<dots>) = 1\<close>) when it is nonzero.  By cases on the \<open>Trans\<close>
  recursion: \<open>Lng = 1\<close> gives \<open>D\<^bsub>v\<^esub> 0\<close>; the mono surgery output is \<open>transC2 M\<close>
  (single principal, @{thm [source] transC2_single_principal}); the \<open>t\<^sub>1 = 0\<close>
  branch is \<open>D\<^bsub>0\<^esub>(\<dots>)\<close>.\<close>

lemma Trans_PT_single:
  "M \<in> RT_PS \<longrightarrow> monoT M \<longrightarrow> Trans M \<noteq> 0\<^sub>B \<longrightarrow> (\<exists>p. Trans M = Trm [p])"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (intro impI)
    assume MR: "M \<in> RT_PS" and mono: "monoT M" and tne: "Trans M \<noteq> 0\<^sub>B"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    show "\<exists>p. Trans M = Trm [p]"
    proof (cases "Lng M = 1")
      case True
      obtain v where Mv: "M = [(v, v)]"
        using m_6_6_oneColumn[OF MT] MR True by auto
      have "Trans M = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Mv Trans_singleton by simp
      hence "Trans M = Dpt (enat v) 0\<^sub>B" using tne by (cases "v = 0") auto
      thus ?thesis by auto
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      let ?j1 = "Lng M - 1"
      show ?thesis
      proof (cases "Trans (Pred M) = 0\<^sub>B")
        case t1z: True
        have "Trans M = Dpt 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
          using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
        thus ?thesis by auto
      next
        case t1ne: False
        have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L])
        let ?t1 = "Trans (Pred M)"
        let ?bv = "entry M 1 ?j1"
        define jp where "jp = parent M 0 (Lng M - 1)"
        define c1 where "c1 = Mark (Pred M) (Adm M jp)"
        define vv where "vv = bpHeadV c1"
        define tt2 where "tt2 = bpHeadT c1"
        define JJ1 where "JJ1 = Lng (PB tt2) - 1"
        define pj where "pj = PB tt2 ! JJ1"
        define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
        define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
        define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
        define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                               then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                               else if transCondVI M
                               then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                               else if tt2 = 0\<^sub>B
                               then Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                               else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                                  (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
        define sb1 where "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
        have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
          using Trans.psimps[OF domT] MR Lgt1 mono t1ne
          unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                    tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                    ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                    c2_def[symmetric] sb1_def[symmetric]
          by simp
        have c2eqT: "c2 = transC2 M"
          unfolding c2_def transC2_def Let_def
            vv_def tt2_def c1_def transV_def transT2_def transC1_def transJm1_def
            JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0_def jp_def
          by simp
        have c2pc1: "Lng (PB (transC2 M)) = 1" by (rule transC2_single_principal)
        obtain pc2 where c2p: "c2 = Trm [pc2]"
          using c2pc1 c2eqT by (cases "transC2 M") (auto simp: PB_def length_Suc_conv)
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        have mkdA: "(Pred M, Adm M jp) \<in> Marked"
          using Marked_Pred_Adm[OF MT L hp] jp_def by simp
        have mb1: "(?t1, c1) \<in> MarkedB"
          using m_7_3_Trans_Mark_MarkedB[OF predRT mkdA] c1_def by simp
        have t1neT: "?t1 \<noteq> Trm []" using t1ne by simp
        have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
          using mb1 unfolding MarkedB_def by auto
        have dsome: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
          unfolding sb1_def by (rule someI_ex[OF exsb])
        have iptc1: "isPTB_str (flatBT c1)"
          using dsome t1neT by (simp add: scb_decomp_def)
        then obtain pc where pcl: "flatBT c1 = flatBP pc" by (auto simp: isPTB_str_def)
        have c1p: "c1 = Trm [pc]"
          by (metis pcl flatBT.simps(2) m_7_flatBT_inj)
        have c1TB: "c1 \<in> T_B" using m_7_3_Mark_in_T_B[OF predRT mkdA] c1_def by simp
        obtain wv tb where pcw: "pc = DB wv tb" by (cases pc) auto
        have iptc2': "isPTB_str (flatBT (Trm [pc2]))"
        proof -
          have vne: "transV M \<noteq> \<infinity>"
          proof -
            have "transV M = bpHeadV c1" by (simp add: transV_def transC1_def transJm1_def
                  transJ0_def transJ1_def jp_def c1_def)
            also have "\<dots> = wv" using c1p pcw by simp
            finally show ?thesis using c1TB c1p pcw by (auto simp: T_B_def)
          qed
          have t2df: "dfree_BT (transT2 M)"
          proof -
            have "transT2 M = bpHeadT c1" by (simp add: transT2_def transC1_def transJm1_def
                  transJ0_def transJ1_def jp_def c1_def)
            also have "\<dots> = tb" using c1p pcw by simp
            finally show ?thesis using c1TB c1p pcw by (auto simp: T_B_def)
          qed
          have c2df: "dfree_BT c2" using dfree_transC2[OF vne t2df] c2eqT by simp
          show ?thesis using c2df c2p by (auto simp: isPTB_str_def)
        qed
        \<comment> \<open>IH: \<open>Trans (Pred M)\<close> is single-principal (mono, nonzero)\<close>
        have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
        have predLng: "Lng (Pred M) < Lng M" using L predb by simp
        have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
        have predmono: "monoT (Pred M)"
        proof (cases "Lng (Pred M) = 1")
          case True
          obtain v where Pv: "Pred M = [(v, v)]"
            using m_6_6_oneColumn[OF predT] predRT True by auto
          have "Trans (Pred M) = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
            using Pv Trans_singleton[of v] by simp
          hence vnz: "v \<noteq> 0" using t1ne by (cases "v = 0") auto
          have nz: "\<not> zeroT (Pred M)" using Pv vnz by (simp add: zeroT_def entry_def)
          have "leR (Pred M) 0 0 (Lng (Pred M) - 1)"
            using True by (simp add: leR_def le0_def)
          thus ?thesis using nz by (simp add: monoT_def)
        next
          case False
          have NP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
          have L2: "1 < Lng M - 1" using L False predb by simp
          have j0pos: "0 < Lng M - 2" using L2 by simp
          have j0lt: "Lng M - 2 < Lng M" using L by simp
          have mp: "monoT (seg M 0 (Lng M - 2))"
            by (rule m_6_2_mono_prefix[OF NP j0pos j0lt])
          have "seg M 0 (Lng M - 2) = butlast M"
          proof -
            have suc: "Suc (Lng M - 2) \<le> Lng M" using L2 by simp
            have "seg M 0 (Lng M - 2) = take (Suc (Lng M - 2)) M"
              by (rule seg_0_eq_take[OF suc])
            also have "Suc (Lng M - 2) = Lng M - 1" using L2 by simp
            also have "take (Lng M - 1) M = butlast M" by (simp add: butlast_conv_take)
            finally show ?thesis .
          qed
          thus ?thesis using mp predb by simp
        qed
        obtain pcc where t1p: "Trans (Pred M) = Trm [pcc]"
          using less.IH[OF predLng] predRT predmono t1ne by blast
        \<comment> \<open>\<open>sb1\<close> decomposes the single principal \<open>Trm [pcc]\<close>; \<open>scb_replace_principal_BP\<close>\<close>
        have dsome'': "scb_decomp (Trm [pcc]) (fst sb1) (flatBT (Trm [pc])) (snd sb1)"
          using dsome t1p c1p by simp
        obtain pm where pmf: "flatBP pm = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
            and pmd: "scb_decomp (Trm [pm]) (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
          using scb_replace_principal_BP[OF dsome'' iptc2'] by blast
        have "flatBT (Trm [pm]) = fst sb1 @ flatBT c2 @ snd sb1"
          using pmf c2p by simp
        hence "Trans M = Trm [pm]"
          using trans_val unflatBT_flat[of "Trm [pm]"] by simp
        thus ?thesis by blast
      qed
    qed
  qed
qed

text \<open>§7.4 命題（\<open>Mark\<close> の \<open>Trans\<close> による表示） / \<open>p_7_4_Trans_Mark_Pred\<close>
  (content.md 2490).  For a reduced \<open>M\<close> and a marked column \<open>m < Lng M - 1\<close>, the
  \<open>m\<close>-basepoint sits at the SAME scb-position \<open>(s\<^sub>0,b\<^sub>0)\<close> in \<open>Trans (Pred M)\<close>
  (around \<open>Mark (Pred M) m\<close>) and in \<open>Trans M\<close> (around \<open>Mark M m\<close>).  Strong
  \<open>Lng\<close>-induction.  Uniqueness is pinned by the \<open>Trans (Pred M)\<close>-conjunct
  (@{thm [source] m_7_2_scb_unique_sb}, with the degenerate \<open>Trans (Pred M) = 0\<^sub>B\<close>
  sub-case forcing \<open>([],[])\<close>).  Existence: the mono surgery branch transports the
  \<open>Pred\<close>-side witness through the \<open>c\<^sub>1 \<rightarrow> c\<^sub>2\<close> replacement (cf.
  @{thm [source] trans_inv_B_hard}); the multi branch recurses to the last
  \<open>P\<close>-component and lifts both sides through the SAME \<open>Trans (take (Pcut M) M) +\<^sub>B _\<close>
  prefix (@{thm [source] scb_addBT_left}, @{thm [source] Trans_Pred_multi_last},
  @{thm [source] Mark_Pred_multi_last}).\<close>

lemma addBT_zero_left: "0\<^sub>B +\<^sub>B Y = Y" by (cases Y) simp

end

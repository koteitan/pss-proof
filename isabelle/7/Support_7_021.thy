theory Support_7_021
  imports Frontier_7_024
begin

text \<open>The leftmost index of \<open>Trans M\<close> is \<open>M\<^bsub>1,0\<^esub>\<close> (it is \<open>0\<close> when
  \<open>Trans M = 0\<^sub>B\<close>, which coincides with \<open>entry M 1 0 = 0\<close> there).  Proved by
  strong \<open>Lng\<close>-induction.  The mono surgery branch reuses the
  @{thm [source] trans_inv_B_hard} setup and the @{thm [source] Mark_leftend_form}
  head-preservation argument; the multi branch reuses @{thm [source] trans_inv_C}
  and (in the \<open>Trans (take (Pcut M) M) = 0\<close> sub-case)
  @{thm [source] P_add_Pcut_left_min} + @{thm [source] reduced_e10_zero} to read
  off the leading \<open>0\<close>.\<close>

lemma m_7_3_Trans_leftend:
  "M \<in> RT_PS \<longrightarrow> bpHeadV (Trans M) = enat (entry M 1 0)"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (rule impI)
    assume MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
    \<comment> \<open>small fact: \<open>bpHeadV\<close> of an \<open>+\<^sub>B\<close>-append\<close>
    have headAdd: "\<And>a b. bpHeadV (a +\<^sub>B b)
                          = (if a = 0\<^sub>B then bpHeadV b else bpHeadV a)"
    proof -
      fix a b :: BT
      obtain as where a: "a = Trm as" by (cases a)
      obtain bs where b: "b = Trm bs" by (cases b)
      show "bpHeadV (a +\<^sub>B b) = (if a = 0\<^sub>B then bpHeadV b else bpHeadV a)"
      proof (cases as)
        case Nil
        thus ?thesis using a b by simp
      next
        case (Cons p ps)
        obtain w u where "p = DB w u" by (cases p)
        thus ?thesis using a b Cons by simp
      qed
    qed
    show "bpHeadV (Trans M) = enat (entry M 1 0)"
    proof (cases "Lng M = 1")
      case True
      \<comment> \<open>(A) length 1: \<open>M = [(v,v)]\<close>\<close>
      obtain v where Mv: "M = [(v, v)]"
        using m_6_6_oneColumn[OF MT] MR True by auto
      have tv: "Trans M = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Mv Trans_singleton by simp
      have ev: "entry M 1 0 = v" using Mv by (simp add: entry_def)
      show ?thesis
      proof (cases "v = 0")
        case True thus ?thesis using tv ev by (simp add: zero_enat_def)
      next
        case False thus ?thesis using tv ev by simp
      qed
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      have nzM: "\<not> zeroT M" using notone by (auto simp: zeroT_def)
      let ?j1 = "Lng M - 1"
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        \<comment> \<open>(B) mono branch\<close>
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
        have predLng: "Lng (Pred M) < Lng M" using L by (simp add: Pred_def)
        have predPos: "0 < Lng (Pred M)" using L predb by simp
        note IHp = less.IH[OF predLng, THEN mp, OF predRT]
        have entry0: "entry (Pred M) 1 0 = entry M 1 0"
        proof -
          have "(0::nat) < length (butlast M)" using predb predPos by simp
          thus ?thesis using predb by (simp add: entry_def nth_butlast)
        qed
        show ?thesis
        proof (cases "Trans (Pred M) = 0\<^sub>B")
          case t1z: True
          \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>: \<open>Trans M = D\<^bsub>0\<^esub>(D\<^bsub>M\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0)\<close>, head \<open>0\<close>\<close>
          let ?b = "entry M 1 ?j1"
          have tv: "Trans M = Dpt 0 (Dpt (enat ?b) 0\<^sub>B)"
            using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
          have bp0: "bpHeadV (Trans M) = 0" using tv by (simp add: zero_enat_def)
          have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
          have zP: "zeroT (Pred M)" using m_7_3_Trans_zeroT[OF predRT] t1z by simp
          have LP1: "Lng (Pred M) = 1" using zP by (simp add: zeroT_def)
          obtain w where Pw: "Pred M = [(w, w)]"
            using m_6_6_oneColumn[OF predT] predRT LP1 by auto
          have w0: "w = 0" using zP Pw by (simp add: zeroT_def entry_def)
          have e0: "entry M 1 0 = 0"
          proof -
            have "entry (Pred M) 1 0 = 0" using Pw w0 by (simp add: entry_def)
            thus ?thesis using entry0 by simp
          qed
          show ?thesis using bp0 e0 by (simp add: zero_enat_def)
        next
          case t1ne: False
          \<comment> \<open>(B) \<open>t\<^sub>1 \<noteq> 0\<close>: surgery branch\<close>
          have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L])
          let ?bv = "entry M 1 (Lng M - 1)"
          define jp where "jp = parent M 0 (Lng M - 1)"
          let ?t1 = "Trans (Pred M)"
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
                                 then Dpt vv (Dpt (enat (entry M 1 jp))
                                              (Dpt (enat ?bv) 0\<^sub>B))
                                 else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                                    (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
          define sb1 where
            "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
          have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
            using Trans.psimps[OF domT] MR Lgt1 mono t1ne
            unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                      tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                      ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                      c2_def[symmetric] sb1_def[symmetric]
            by simp
          have transJ1eq: "transJ1 M = ?j1" by (simp add: transJ1_def)
          have transJ0eq: "transJ0 M = jp"
            by (simp add: transJ0_def transJ1_def jp_def)
          have transJm1eq: "transJm1 M = Adm M jp"
            by (simp add: transJm1_def transJ0eq)
          have c1eqT: "c1 = transC1 M"
            by (simp add: c1_def transC1_def transJm1eq)
          have c2eqT: "c2 = transC2 M"
            unfolding c2_def transC2_def Let_def
              vv_def tt2_def c1eqT transV_def transT2_def
              JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
            by simp
          have mkjm1: "(Pred M, Adm M jp) \<in> Marked"
            using Marked_Pred_Adm[OF MT L hp] jp_def by simp
          have NP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
          have J1pos: "transJ1 M > 0" using L by (simp add: transJ1_def)
          have T1ne: "transT1 M \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
          have pc1: "Lng (PB (transC1 M)) = 1"
            by (rule transC1_single_principal[OF MR NP J1pos T1ne])
          have c1ne: "transC1 M \<noteq> 0\<^sub>B"
          proof
            assume "transC1 M = 0\<^sub>B"
            thus False using pc1 by (simp add: PB_def)
          qed
          have c1TB: "transC1 M \<in> T_B"
            using m_7_3_Mark_in_T_B[OF predRT mkjm1]
                  c1eqT[symmetric] c1_def by simp
          have c1Dpt: "transC1 M = Dpt (transV M) (transT2 M)"
            using principal_reconstruct[OF pc1] by (simp add: transV_def transT2_def)
          have c1Dsym: "flatBT c1 = Dsym (transV M) # flatBT (transT2 M)"
            using c1eqT c1Dpt by simp
          have vvT: "vv = transV M" by (simp add: vv_def transV_def c1eqT)
          have bpc2: "bpHeadV c2 = transV M"
          proof -
            have "bpHeadV c2 = vv" by (simp add: c2_def)
            thus ?thesis using vvT by simp
          qed
          have c2pc1: "Lng (PB c2) = 1"
            using transC2_single_principal c2eqT by simp
          have c2Dpt: "c2 = Dpt (transV M) (bpHeadT c2)"
            using principal_reconstruct[OF c2pc1] bpc2 by simp
          have c2Dsym: "flatBT c2 = Dsym (transV M) # flatBT (bpHeadT c2)"
            by (subst c2Dpt) (rule flatBT_principal_head)
          \<comment> \<open>the SOME decomposition of \<open>?t\<^sub>1\<close>\<close>
          have inv1: "(Trans (Pred M), c1) \<in> MarkedB"
            using m_7_3_Trans_Mark_MarkedB[OF predRT mkjm1] c1_def by simp
          have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
            using inv1 unfolding MarkedB_def by auto
          have dsb: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
            unfolding sb1_def by (rule someI_ex[OF exsb])
          have flatt1: "flatBT (Trans (Pred M)) = fst sb1 @ flatBT c1 @ snd sb1"
            using dsb by (simp add: scb_decomp_def)
          \<comment> \<open>the surgery output \<open>Trans M\<close> is the \<open>c\<^sub>2\<close>-replacement, principal\<close>
          have c2df: "dfree_BT c2"
          proof -
            have vne: "transV M \<noteq> \<infinity>" using c1TB c1Dpt by (auto simp: T_B_def)
            have t2df: "dfree_BT (transT2 M)" using c1TB c1Dpt by (auto simp: T_B_def)
            show ?thesis using dfree_transC2[OF vne t2df] c2eqT by simp
          qed
          obtain pc2 where c2p: "c2 = Trm [pc2]"
            using principal_reconstruct[OF c2pc1] by (metis BT.exhaust untrm.simps)
          have iptc2': "isPTB_str (flatBT (Trm [pc2]))"
          proof -
            have "dfree_BT (Trm [pc2])" using c2df c2p by simp
            then obtain p where "pc2 = p" and "dfree_BP p" by auto
            thus ?thesis by (auto simp: isPTB_str_def)
          qed
          obtain pc1' where c1p: "c1 = Trm [pc1']"
            using principal_reconstruct[OF pc1] c1eqT by (metis BT.exhaust untrm.simps)
          have dsb': "scb_decomp ?t1 (fst sb1) (flatBT (Trm [pc1'])) (snd sb1)"
            using dsb c1p by simp
          obtain t' where t'f: "flatBT t' = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
              and t'd: "scb_decomp t' (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
            using scb_replace_principal[OF dsb' iptc2'] by blast
          have transMp: "Trans M = t'"
            using trans_val t'f c2p unflatBT_flat[of t'] by simp
          have flatTM: "flatBT (Trans M) = fst sb1 @ flatBT c2 @ snd sb1"
            using transMp t'f c2p by simp
          \<comment> \<open>both \<open>Trans M\<close> and \<open>Trans (Pred M)\<close> flatten to \<open>fst sb1 @ Dsym (transV M) # _\<close>\<close>
          have flatTMv: "flatBT (Trans M)
                          = fst sb1 @ Dsym (transV M) # (flatBT (bpHeadT c2) @ snd sb1)"
            using flatTM c2Dsym by simp
          have flatt1v: "flatBT (Trans (Pred M))
                          = fst sb1 @ Dsym (transV M) # (flatBT (transT2 M) @ snd sb1)"
            using flatt1 c1Dsym by simp
          have tMne: "Trans M \<noteq> 0\<^sub>B"
          proof
            assume z: "Trans M = 0\<^sub>B"
            hence "flatBT (Trans M) = [Zsym]" by simp
            moreover have "Dsym (transV M) \<in> set (flatBT (Trans M))"
              using flatTMv by simp
            ultimately show False by simp
          qed
          \<comment> \<open>read \<open>bpHeadV\<close> off the first \<open>Dsym\<close> of each flat string\<close>
          let ?P = "\<lambda>x. \<exists>v. x = Dsym v"
          have findM: "find ?P (flatBT (Trans M)) = Some (Dsym (bpHeadV (Trans M)))"
            by (rule bpHeadV_find_Dsym[OF tMne])
          have findt1: "find ?P (flatBT (Trans (Pred M)))
                          = Some (Dsym (bpHeadV (Trans (Pred M))))"
            by (rule bpHeadV_find_Dsym[OF t1ne])
          have findEq: "find ?P (flatBT (Trans M))
                          = find ?P (flatBT (Trans (Pred M)))"
          proof (cases "find ?P (fst sb1)")
            case None
            have "find ?P (flatBT (Trans M))
                    = find ?P (Dsym (transV M) # (flatBT (bpHeadT c2) @ snd sb1))"
              using flatTMv None by (simp add: find_append_local)
            moreover have "find ?P (flatBT (Trans (Pred M)))
                    = find ?P (Dsym (transV M) # (flatBT (transT2 M) @ snd sb1))"
              using flatt1v None by (simp add: find_append_local)
            ultimately show ?thesis by simp
          next
            case (Some r)
            have "find ?P (flatBT (Trans M)) = Some r"
              using flatTMv Some by (simp add: find_append_local)
            moreover have "find ?P (flatBT (Trans (Pred M))) = Some r"
              using flatt1v Some by (simp add: find_append_local)
            ultimately show ?thesis by simp
          qed
          have "Dsym (bpHeadV (Trans M)) = Dsym (bpHeadV (Trans (Pred M)))"
            using findM findt1 findEq by simp
          hence "bpHeadV (Trans M) = bpHeadV (Trans (Pred M))" by simp
          also have "\<dots> = enat (entry (Pred M) 1 0)" using IHp .
          also have "\<dots> = enat (entry M 1 0)" using entry0 by simp
          finally show ?thesis .
        qed
      next
        case nmono: False
        \<comment> \<open>(C) multiT branch\<close>
        have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
        have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
        let ?A = "take (Pcut M) M"
        let ?PJ = "drop (Pcut M) M"
        have Acut_RT: "?A \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF MR muM])
        have LA: "Lng ?A < Lng M"
        proof -
          have "Pcut M < Lng M" using cut L by linarith
          thus ?thesis by (simp add: min_def)
        qed
        have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF MT muM])
        have Pne: "P M \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
        have PJ_RT: "?PJ \<in> RT_PS"
          using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
        have PJT: "?PJ \<in> T_PS" using PJ_RT by (simp add: RT_PS_def)
        have LPJ: "Lng ?PJ < Lng M"
        proof -
          have "Lng ?PJ = Lng M - Pcut M" by simp
          thus ?thesis using cut L by linarith
        qed
        note IHA = less.IH[OF LA, THEN mp, OF Acut_RT]
        note IHJ = less.IH[OF LPJ, THEN mp, OF PJ_RT]
        \<comment> \<open>the recursion value (copy from @{thm [source] trans_inv_C})\<close>
        have nmono': "\<not> monoT M" using muM by (simp add: multiT_def)
        have j0eq: "Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 = Pcut M"
          by (rule trans_multiT_last_component(2)[OF MT muM])
        have LdJ: "Lng ?PJ = Lng M - Pcut M" by simp
        have Aeq2: "seg M 0 (Lng M - 1 - Lng ?PJ + 1 - 1) = ?A"
        proof -
          have "Lng M - 1 - Lng ?PJ + 1 - 1 = Pcut M - 1"
            using LdJ cut by linarith
          moreover have "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
            by (rule seg_0_eq_take) (use cut L in linarith)
          moreover have "Suc (Pcut M - 1) = Pcut M" using cut by simp
          ultimately show ?thesis by simp
        qed
        have c1f: "(M \<notin> RT_PS) = False" using MR by simp
        have c2f: "(Lng M - 1 = 0) = False" using L by simp
        have c3f: "monoT M = False" using nmono' by simp
        have transM: "Trans M = (if ?PJ = [(0, 0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B
                                 else Trans ?A +\<^sub>B Trans ?PJ)"
        proof -
          have raw: "Trans M =
              (if P M ! (Lng (P M) - 1) = [(0, 0)]
               then Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                      +\<^sub>B Dpt 0 0\<^sub>B
               else Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                      +\<^sub>B Trans (P M ! (Lng (P M) - 1)))"
            by (subst Trans.psimps[OF domT]) (simp only: c1f c2f c3f if_False Let_def)
          show ?thesis unfolding raw PJeq Aeq2 ..
        qed
        have entryA: "entry ?A 1 0 = entry M 1 0"
        proof -
          have "(0::nat) < Pcut M" using cut by simp
          thus ?thesis by (simp add: entry_def)
        qed
        show ?thesis
        proof (cases "Trans ?A = 0\<^sub>B")
          case TA0: False
          have bpA: "bpHeadV (Trans ?A) = enat (entry ?A 1 0)" using IHA .
          show ?thesis
          proof (cases "?PJ = [(0, 0)]")
            case True
            have "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM True by simp
            hence "bpHeadV (Trans M) = bpHeadV (Trans ?A)"
              using headAdd[of "Trans ?A" "Dpt 0 0\<^sub>B"] TA0 by simp
            thus ?thesis using bpA entryA by simp
          next
            case False
            have "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM False by simp
            hence "bpHeadV (Trans M) = bpHeadV (Trans ?A)"
              using headAdd[of "Trans ?A" "Trans ?PJ"] TA0 by simp
            thus ?thesis using bpA entryA by simp
          qed
        next
          case TA0: True
          \<comment> \<open>\<open>Trans ?A = 0\<close> so \<open>zeroT ?A\<close>, giving \<open>entry M 1 0 = 0\<close> and
             (via the cut left-minimality + reducedness of \<open>?PJ\<close>)
             \<open>entry ?PJ 1 0 = 0\<close>.\<close>
          have zA: "zeroT ?A" using m_7_3_Trans_zeroT[OF Acut_RT] TA0 by simp
          have LA1: "Lng ?A = 1" using zA by (simp add: zeroT_def)
          have eA10: "entry ?A 1 0 = 0" using zA by (simp add: zeroT_def)
          have eM10: "entry M 1 0 = 0" using eA10 entryA by simp
          \<comment> \<open>row-0 of column 0 is also 0 (since \<open>?A = [(0,0)]\<close>)\<close>
          have AT: "?A \<in> T_PS" using Acut_RT by (simp add: RT_PS_def)
          have eA00: "entry ?A 0 0 = 0"
          proof -
            obtain v where Av: "?A = [(v, v)]"
              using m_6_6_oneColumn[OF AT] Acut_RT LA1 by auto
            have "entry ?A 1 0 = v" using Av by (simp add: entry_def)
            hence "v = 0" using eA10 by simp
            thus ?thesis using Av by (simp add: entry_def)
          qed
          have eM00: "entry M 0 0 = 0"
          proof -
            have "(0::nat) < Pcut M" using cut by simp
            hence "entry ?A 0 0 = entry M 0 0" by (simp add: entry_def)
            thus ?thesis using eA00 by simp
          qed
          \<comment> \<open>row-0 of column \<open>Pcut M\<close> is 0 by left-minimality of the cut\<close>
          have ePcut00: "entry M 0 (Pcut M) = 0"
          proof -
            have "entry M 0 0 \<ge> entry M 0 (Pcut M)"
              using P_add_Pcut_left_min[OF MT muM L, of 0] cut by simp
            thus ?thesis using eM00 by simp
          qed
          have ePJ00: "entry ?PJ 0 0 = 0"
          proof -
            have "(0::nat) < Lng ?PJ" using cut L LdJ by linarith
            hence "entry ?PJ 0 0 = entry M 0 (Pcut M)" by (simp add: entry_def)
            thus ?thesis using ePcut00 by simp
          qed
          \<comment> \<open>and hence row-1 of column \<open>Pcut M\<close> (left end of \<open>?PJ\<close>) is 0\<close>
          have ePJ10: "entry ?PJ 1 0 = 0"
            using reduced_e10_zero PJ_RT ePJ00 by blast
          show ?thesis
          proof (cases "?PJ = [(0, 0)]")
            case True
            have "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM True by simp
            hence "bpHeadV (Trans M) = bpHeadV (Dpt 0 0\<^sub>B)"
              using headAdd[of "Trans ?A" "Dpt 0 0\<^sub>B"] TA0 by simp
            hence "bpHeadV (Trans M) = 0" by (simp add: zero_enat_def)
            thus ?thesis using eM10 by (simp add: zero_enat_def)
          next
            case False
            have tv: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM False by simp
            have bpM: "bpHeadV (Trans M) = bpHeadV (Trans ?PJ)"
              using tv headAdd[of "Trans ?A" "Trans ?PJ"] TA0 by simp
            have bpJ: "bpHeadV (Trans ?PJ) = enat (entry ?PJ 1 0)" using IHJ .
            have "bpHeadV (Trans M) = 0"
              using bpM bpJ ePJ10 by (simp add: zero_enat_def)
            thus ?thesis using eM10 by (simp add: zero_enat_def)
          qed
        qed
      qed
    qed
  qed
qed

end

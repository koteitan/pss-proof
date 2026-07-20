theory P_7_4_Trans_Mark_Pred
  imports Frontier_7_025
begin

lemma m_7_4_Trans_Mark_Pred:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mlt: "m < Lng M - 1"
  shows "\<exists>!sb. scb_decomp (Trans (Pred M)) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)
            \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
proof -
  have ex: "M \<in> RT_PS \<longrightarrow> (\<forall>m. (M, m) \<in> Marked \<longrightarrow> m < Lng M - 1 \<longrightarrow>
       (\<exists>s0 b0.
          scb_decomp (Trans (Pred M)) s0 (flatBT (Mark (Pred M) m)) b0
        \<and> scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0))"
  proof (induction M rule: measure_induct_rule[where f=Lng])
    case (less M)
    show ?case
    proof (intro impI allI)
      fix m
      assume MR: "M \<in> RT_PS" and mM: "(M, m) \<in> Marked" and mlt: "m < Lng M - 1"
      have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
      have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
      have L: "1 < Lng M" using mlt by linarith
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
      have domK: "\<And>k. Trans_Mark_dom (Inr (M, k))" by (rule m_7_3_Mark_welldef[OF MR])
      let ?j1 = "Lng M - 1"
      have nzM: "\<not> zeroT M" using L by (auto simp: zeroT_def)
      show "\<exists>s0 b0. scb_decomp (Trans (Pred M)) s0 (flatBT (Mark (Pred M) m)) b0
                  \<and> scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
      proof (cases "monoT M")
        case mono: True
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
        have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
        have LPred: "Lng (Pred M) = Lng M - 1" using predb by simp
        have mPred: "(Pred M, m) \<in> Marked" by (rule Marked_Pred[OF MT L mM mlt])
        have invP: "(Trans (Pred M), Mark (Pred M) m) \<in> MarkedB"
          by (rule m_7_3_Trans_Mark_MarkedB[OF predRT mPred])
        obtain s0 b0 where d0: "scb_decomp (Trans (Pred M)) s0 (flatBT (Mark (Pred M) m)) b0"
          using invP by (auto simp: MarkedB_def)
        show ?thesis
        proof (cases "Trans (Pred M) = 0\<^sub>B")
          case t1z: True
          have zP: "zeroT (Pred M)" using m_7_3_Trans_zeroT[OF predRT] t1z by simp
          have LP1: "Lng (Pred M) = 1" using zP by (simp add: zeroT_def)
          have L2: "Lng M = 2" using LP1 LPred L by linarith
          have m0: "m = 0" using mlt L2 by simp
          obtain w where Pw: "Pred M = [(w, w)]"
            using m_6_6_oneColumn[OF predT] predRT LP1 by auto
          have w0: "w = 0" using zP Pw by (simp add: zeroT_def entry_def)
          have kP0: "Mark (Pred M) m = 0\<^sub>B"
            using Pw w0 Mark_singleton m0 by simp
          have s0b0: "s0 = [] \<and> b0 = []"
          proof -
            have "flatBT (Trans (Pred M)) = s0 @ flatBT (Mark (Pred M) m) @ b0"
              using d0 by (simp add: scb_decomp_def)
            hence "[Zsym] = s0 @ [Zsym] @ b0" using t1z kP0 by simp
            thus ?thesis by (cases s0) auto
          qed
          let ?bv = "entry M 1 ?j1"
          have tv: "Trans M = Dpt 0 (Dpt (enat ?bv) 0\<^sub>B)"
            using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
          have kv: "Mark M m = Dpt 0 (Dpt (enat ?bv) 0\<^sub>B)"
            using Mark.psimps[OF domK] MR Lgt1 mono t1z m0 by (simp add: Let_def)
          have iptM: "isPTB_str (flatBT (Trans M))"
          proof -
            have "isPTB_str (flatBT (Dpt 0 (Dpt (enat ?bv) 0\<^sub>B)))"
              by (rule isPTB_str_Dpt) (simp_all add: zero_enat_def)
            thus ?thesis using tv by simp
          qed
          have "scb_decomp (Trans M) [] (flatBT (Mark M m)) []"
            using tv kv iptM by (simp add: scb_decomp_def)
          thus ?thesis using d0 s0b0 by auto
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
          then obtain pc where pcl: "flatBT c1 = flatBP pc"
            by (auto simp: isPTB_str_def)
          have c1p: "c1 = Trm [pc]"
          proof -
            have "flatBT c1 = flatBT (Trm [pc])" using pcl by simp
            thus ?thesis by (rule m_7_flatBT_inj)
          qed
          obtain wv tb where pcw: "pc = DB wv tb" by (cases pc) auto
          have vvv: "vv = wv" using vv_def c1p pcw by simp
          have tt2v: "tt2 = tb" using tt2_def c1p pcw by simp
          have c1TB: "c1 \<in> T_B" using m_7_3_Mark_in_T_B[OF predRT mkdA] c1_def by simp
          have wvne: "wv \<noteq> \<infinity>" and tbdf: "dfree_BT tb"
            using c1TB c1p pcw by (auto simp: T_B_def)
          have c2shape: "\<exists>X. c2 = Dpt vv X \<and> dfree_BT X"
          proof -
            consider (A) "transCondI M \<or> transCondIII M \<or> transCondV M"
              | (VI) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "transCondVI M"
              | (Z) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "\<not> transCondVI M"
                    "tt2 = 0\<^sub>B"
              | (E) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "\<not> transCondVI M"
                    "tt2 \<noteq> 0\<^sub>B"
              by blast
            thus ?thesis
            proof cases
              case A
              have x: "c2 = Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)" using A c2_def by simp
              have df: "dfree_BT (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)"
                using tt2v tbdf by (cases tb) auto
              show ?thesis using x df by blast
            next
              case VI
              have x: "c2 = Dpt vv (Dpt (enat ?bv) 0\<^sub>B)" using VI c2_def by simp
              show ?thesis using x by auto
            next
              case Z
              have x: "c2 = Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))"
                using Z c2_def by simp
              show ?thesis using x by auto
            next
              case E
              have x: "c2 = Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                           (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B))"
                using E c2_def by simp
              have df3: "dfree_BT tt3"
              proof -
                have "dfree_BT (SigmaB (take JJ1 (PB tb)))"
                  using tbdf by (cases tb) (auto simp: SigmaB_def PB_def dest!: in_set_takeD)
                thus ?thesis using tt3_def tt2v tbdf by simp
              qed
              have df4: "dfree_BT tt4"
              proof -
                have tbne: "untrm tb \<noteq> []" using E(3) tt2v by (cases tb) auto
                have inr: "JJ1 < Lng (PB tb)"
                  using JJ1_def tt2v tbne by (simp add: PB_def)
                have "pj \<in> set (PB tb)" using pj_def tt2v inr by simp
                hence "dfree_BT pj" using tbdf by (cases tb) (auto simp: PB_def)
                hence "dfree_BT (bpHeadT pj)" by (cases pj rule: bpHeadT.cases) auto
                thus ?thesis using tt4_def tt2v tbdf by simp
              qed
              have dfsum: "dfree_BT (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)"
                using df4 by (cases tt4) auto
              have dfall: "dfree_BT (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                            (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B))"
                using df3 dfsum by (cases tt3) auto
              show ?thesis using x dfall by blast
            qed
          qed
          obtain X2 where c2X: "c2 = Dpt vv X2" and X2df: "dfree_BT X2"
            using c2shape by blast
          have c2df: "dfree_BT c2" using c2X X2df wvne vvv by simp
          have iptc2: "isPTB_str (flatBT c2)"
            using c2X by (intro isPTB_str_Dpt[of vv X2, folded c2X])
                         (use wvne vvv X2df in simp_all)
          obtain pc2 where c2p: "c2 = Trm [pc2]" using c2X by auto
          have iptc2': "isPTB_str (flatBT (Trm [pc2]))" using iptc2 c2p by simp
          have dsome': "scb_decomp ?t1 (fst sb1) (flatBT (Trm [pc])) (snd sb1)"
            using dsome c1p by simp
          obtain t' where t'f: "flatBT t' = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
              and t'd: "scb_decomp t' (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
            using scb_replace_principal[OF dsome' iptc2'] by blast
          have transM: "Trans M = t'"
            using trans_val t'f c2p unflatBT_flat[of t'] by simp
          define c0 where "c0 = Mark (Pred M) m"
          define sm1 where "sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))"
          have mark_val: "Mark M m = (if (c0, c1) \<in> MarkedB
                then unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
                else Dpt (enat ?bv) 0\<^sub>B)"
          proof -
            have raw: "Mark M m = (if (Mark (Pred M) m, c1) \<in> MarkedB
                  then unflatBT
                         (fst (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                          (flatBT c1) (snd sb))
                          @ flatBT c2
                          @ snd (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                            (flatBT c1) (snd sb)))
                  else Dpt (enat ?bv) 0\<^sub>B)"
              using Mark.psimps[OF domK] MR Lgt1 mono t1ne mlt
              unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                        tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                        ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                        c2_def[symmetric]
              by simp
            thus ?thesis by (simp add: c0_def sm1_def)
          qed
          have c0df: "dfree_BT c0"
            using m_7_3_Mark_in_T_B[OF predRT mPred] c0_def by (simp add: T_B_def)
          have d0': "scb_decomp ?t1 s0 (flatBT c0) b0" using d0 c0_def by simp
          have iptc0: "isPTB_str (flatBT c0)"
            using d0' t1neT by (simp add: scb_decomp_def)
          then obtain pc0 where pc0l: "flatBT c0 = flatBP pc0"
            by (auto simp: isPTB_str_def)
          have c0p: "c0 = Trm [pc0]"
          proof -
            have "flatBT c0 = flatBT (Trm [pc0])" using pc0l by simp
            thus ?thesis by (rule m_7_flatBT_inj)
          qed
          have mbc: "(c0, c1) \<in> MarkedB"
          proof -
            have admMm: "adm M m" using mM by (simp add: Marked_def)
            have mjp: "m \<le> jp" using surg_parent_ge[OF mM mono L mlt] jp_def by simp
            have mjm1: "m \<le> Adm M jp" using surg_adm_ge[OF admMm mjp] by simp
            have nest: "(Mark (Pred M) m, Mark (Pred M) (Adm M jp)) \<in> MarkedB"
              using Mark_MarkedB_nest mPred mkdA mjm1 predRT by blast
            thus ?thesis using c0_def c1_def by simp
          qed
          have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
            using mbc unfolding MarkedB_def by auto
          have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
            unfolding sm1_def by (rule someI_ex[OF exsm])
          have dsm': "scb_decomp (Trm [pc0]) (fst sm1) (flatBT (Trm [pc])) (snd sm1)"
            using dsm c0p c1p by simp
          obtain pm where pmf: "flatBP pm = fst sm1 @ flatBT (Trm [pc2]) @ snd sm1"
              and pmd: "scb_decomp (Trm [pm]) (fst sm1) (flatBT (Trm [pc2])) (snd sm1)"
            using scb_replace_principal_BP[OF dsm' iptc2'] by blast
          have markM: "Mark M m = Trm [pm]"
          proof -
            have "flatBT (Trm [pm]) = fst sm1 @ flatBT c2 @ snd sm1"
              using pmf c2p by simp
            thus ?thesis
              using mark_val mbc unflatBT_flat[of "Trm [pm]"] by simp
          qed
          have comp: "scb_decomp ?t1 (s0 @ fst sm1) (flatBT c1) (snd sm1 @ b0)"
            by (rule m_7_2_scb_compose[OF _ _ dsm]) (use c0p d0' in auto)
          have coh: "fst sb1 = s0 @ fst sm1 \<and> snd sb1 = snd sm1 @ b0"
            by (rule m_7_2_scb_unique_sb[OF dsome comp t1neT])
          have t'flat: "flatBT t' = s0 @ flatBT (Trm [pm]) @ b0"
            using t'f coh pmf c2p by simp
          have b0rp: "\<forall>x \<in> set b0. x = RP" using d0' by (simp add: scb_decomp_def)
          have sm_sub: "set (fst sm1) \<subseteq> set (flatBT c0)"
              and bm_sub: "set (snd sm1) \<subseteq> set (flatBT c0)"
            using dsm by (auto simp: scb_decomp_def)
          have mmdf: "dfree_BT (Trm [pm])"
          proof -
            have "\<And>v'. Dsym v' \<in> set (flatBT (Trm [pm])) \<Longrightarrow> v' \<noteq> \<infinity>"
            proof -
              fix v' assume "Dsym v' \<in> set (flatBT (Trm [pm]))"
              hence "Dsym v' \<in> set (flatBT c0) \<or> Dsym v' \<in> set (flatBT c2)"
                using pmf c2p sm_sub bm_sub by auto
              thus "v' \<noteq> \<infinity>" using c0df c2df dfree_flat_BT by blast
            qed
            thus ?thesis using dfree_flat_BT by blast
          qed
          have iptm: "isPTB_str (flatBT (Trm [pm]))"
            using mmdf by (auto simp: isPTB_str_def)
          have "scb_decomp t' s0 (flatBT (Trm [pm])) b0"
            unfolding scb_decomp_def using t'flat iptm b0rp by simp
          hence "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
            using transM markM by simp
          thus ?thesis using d0 by blast
        qed
      next
        case nmono: False
        have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
        have cut: "0 < Pcut M \<and> Pcut M \<le> ?j1" using Pcut_le[OF L] by simp
        let ?A = "take (Pcut M) M"
        let ?PJ = "drop (Pcut M) M"
        have ARTS: "?A \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF MR muM])
        have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF MT muM])
        have Pne: "P M \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
        have PJRT: "?PJ \<in> RT_PS"
          using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
        have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
        have LPJ: "Lng ?PJ = Lng M - Pcut M" by simp
        have LPJlt: "Lng ?PJ < Lng M" using LPJ cut L by linarith
        have cmle: "Pcut M \<le> m" by (rule multi_Marked_last_component(1)[OF MT muM mM])
        have mPJ: "(?PJ, m - Pcut M) \<in> Marked"
          by (rule multi_Marked_last_component(2)[OF MT muM mM])
        have PJj1: "Pcut M < ?j1" using mlt cmle by linarith
        have LPJg1: "1 < Lng ?PJ" using LPJ PJj1 cut L by linarith
        have notPJ00: "?PJ \<noteq> [(0,0)]"
        proof
          assume "?PJ = [(0,0)]"
          hence "Lng ?PJ = 1" by simp
          thus False using LPJg1 by simp
        qed
        have mPJlt: "m - Pcut M < Lng ?PJ - 1" using mlt cmle LPJ cut by linarith
        \<comment> \<open>\<open>PJ\<close> is mono (a non-zero \<open>P\<close>-component)\<close>
        have PJmono: "monoT ?PJ"
        proof -
          have "?PJ \<in> set (P M)" using PJeq Pne J1lt nth_mem by metis
          hence "zeroT ?PJ \<or> monoT ?PJ" using m_6_2_P_components_1[OF MT] by blast
          moreover have "\<not> zeroT ?PJ" using LPJg1 by (auto simp: zeroT_def)
          ultimately show ?thesis by blast
        qed
        have c1f: "(M \<notin> RT_PS) = False" using MR by simp
        have c2f: "(?j1 = 0) = False" using L by simp
        have c3f: "monoT M = False" using nmono by simp
        have Aeq2: "seg M 0 (?j1 - Lng ?PJ + 1 - 1) = ?A"
        proof -
          have "?j1 - Lng ?PJ + 1 - 1 = Pcut M - 1" using LPJ cut by linarith
          moreover have "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
            by (rule seg_0_eq_take) (use cut L in linarith)
          moreover have "Suc (Pcut M - 1) = Pcut M" using cut by simp
          ultimately show ?thesis by simp
        qed
        have transM: "Trans M = Trans ?A +\<^sub>B Trans ?PJ"
        proof -
          have raw: "Trans M =
              (if P M ! (Lng (P M) - 1) = [(0, 0)]
               then Trans (seg M 0 (?j1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1)) +\<^sub>B Dpt 0 0\<^sub>B
               else Trans (seg M 0 (?j1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                      +\<^sub>B Trans (P M ! (Lng (P M) - 1)))"
            by (subst Trans.psimps[OF domT]) (simp only: c1f c2f c3f if_False Let_def)
          have "Trans M = (if ?PJ = [(0, 0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B
                           else Trans ?A +\<^sub>B Trans ?PJ)"
            unfolding raw PJeq Aeq2 ..
          thus ?thesis using notPJ00 by simp
        qed
        have markM_eval: "Mark M m = Mark ?PJ (m - Pcut M)"
        proof -
          have meq2: "m - (?j1 - Lng ?PJ + 1) = m - Pcut M"
          proof -
            have "?j1 - Lng ?PJ + 1 = Pcut M" using LPJ cut by linarith
            thus ?thesis by simp
          qed
          have raw: "Mark M m =
              (if P M ! (Lng (P M) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
               else Mark (P M ! (Lng (P M) - 1)) (m - (?j1 - Lng (P M ! (Lng (P M) - 1)) + 1)))"
            by (subst Mark.psimps[OF domK]) (simp only: c1f c2f c3f if_False Let_def)
          have "Mark M m = (if ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Mark ?PJ (m - Pcut M))"
            unfolding raw PJeq meq2 ..
          thus ?thesis using notPJ00 by simp
        qed
        from less.IH[OF LPJlt] PJRT mPJ mPJlt
        obtain s0 b0 where
          dP_J: "scb_decomp (Trans (Pred ?PJ)) s0 (flatBT (Mark (Pred ?PJ) (m - Pcut M))) b0"
          and dM_J: "scb_decomp (Trans ?PJ) s0 (flatBT (Mark ?PJ (m - Pcut M))) b0"
          by blast
        have tPJne: "Trans ?PJ \<noteq> 0\<^sub>B"
        proof -
          have "\<not> zeroT ?PJ" using LPJg1 by (auto simp: zeroT_def)
          thus ?thesis using m_7_3_Trans_zeroT[OF PJRT] by blast
        qed
        have X1_PJ: "length (untrm (Trans ?PJ)) = 1"
        proof -
          obtain p where "Trans ?PJ = Trm [p]"
            using Trans_PT_single PJRT PJmono tPJne by blast
          thus ?thesis by simp
        qed
        show ?thesis
        proof (cases "Trans ?A = 0\<^sub>B")
          case TA0: True
          have transM': "Trans M = Trans ?PJ" using transM TA0 addBT_zero_left by simp
          have transPM: "Trans (Pred M)
                = Trans ?A +\<^sub>B (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Trans (Pred ?PJ))"
            by (rule Trans_Pred_multi_last[OF MR muM LPJg1])
          have markPM: "Mark (Pred M) m
                = (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Mark (Pred ?PJ) (m - Pcut M))"
            by (rule Mark_Pred_multi_last[OF MR muM LPJg1])
          show ?thesis
          proof (cases "Pred ?PJ = [(0,0)]")
            case PP0: True
            have tPP0: "Trans (Pred ?PJ) = 0\<^sub>B" using PP0 Trans_singleton[of 0] by simp
            have kPP0: "Mark (Pred ?PJ) (m - Pcut M) = 0\<^sub>B"
            proof -
              have "Lng (Pred ?PJ) = 1" using PP0 by simp
              hence "Lng ?PJ = 2" using LPJg1 by (simp add: Pred_def)
              hence "m - Pcut M = 0" using mPJlt by simp
              thus ?thesis using PP0 Mark_singleton[of 0] by simp
            qed
            have markPM0: "Mark (Pred M) m = Dpt 0 0\<^sub>B" using markPM PP0 by simp
            have transPM0: "Trans (Pred M) = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transPM PP0 by simp
            have transPM0': "Trans (Pred M) = Dpt 0 0\<^sub>B" using transPM0 TA0 addBT_zero_left by simp
            have iptD0: "isPTB_str (flatBT (Dpt 0 0\<^sub>B))"
              by (rule isPTB_str_Dpt) (simp_all add: zero_enat_def)
            have dP: "scb_decomp (Trans (Pred M)) [] (flatBT (Mark (Pred M) m)) []"
              using transPM0' markPM0 iptD0 by (simp add: scb_decomp_def)
            have s0b0: "s0 = [] \<and> b0 = []"
            proof -
              have "flatBT (Trans (Pred ?PJ)) = s0 @ flatBT (Mark (Pred ?PJ) (m - Pcut M)) @ b0"
                using dP_J by (simp add: scb_decomp_def)
              hence "[Zsym] = s0 @ [Zsym] @ b0" using tPP0 kPP0 by simp
              thus ?thesis by (cases s0) auto
            qed
            have dM: "scb_decomp (Trans M) [] (flatBT (Mark M m)) []"
              using dM_J s0b0 transM' markM_eval by simp
            show ?thesis using dP dM by blast
          next
            case PPne: False
            have predPJRT: "Pred ?PJ \<in> RT_PS" by (rule Pred_RT_PS[OF PJRT])
            have transM'': "Trans M = Trans ?PJ" using transM TA0 addBT_zero_left by simp
            have transPM': "Trans (Pred M) = Trans (Pred ?PJ)"
              using transPM PPne TA0 addBT_zero_left by simp
            have markPM': "Mark (Pred M) m = Mark (Pred ?PJ) (m - Pcut M)"
              using markPM PPne by simp
            have dP: "scb_decomp (Trans (Pred M)) s0 (flatBT (Mark (Pred M) m)) b0"
              using dP_J transPM' markPM' by simp
            have dM: "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
              using dM_J transM'' markM_eval by simp
            show ?thesis using dP dM by blast
          qed
        next
          case TAne: False
          have Yne: "untrm (Trans ?A) \<noteq> []" using TAne by (cases "Trans ?A") auto
          have transPM: "Trans (Pred M)
                = Trans ?A +\<^sub>B (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Trans (Pred ?PJ))"
            by (rule Trans_Pred_multi_last[OF MR muM LPJg1])
          have markPM: "Mark (Pred M) m
                = (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Mark (Pred ?PJ) (m - Pcut M))"
            by (rule Mark_Pred_multi_last[OF MR muM LPJg1])
          have liftM: "scb_decomp (Trans ?A +\<^sub>B Trans ?PJ) (liftS (Trans ?A) s0)
                          (flatBT (Mark ?PJ (m - Pcut M))) (b0 @ [RP])"
            by (rule scb_addBT_left[OF dM_J X1_PJ Yne])
          have dM: "scb_decomp (Trans M) (liftS (Trans ?A) s0) (flatBT (Mark M m)) (b0 @ [RP])"
            using liftM transM markM_eval by simp
          show ?thesis
          proof (cases "Pred ?PJ = [(0,0)]")
            case PP0: True
            have kPP0: "Mark (Pred ?PJ) (m - Pcut M) = 0\<^sub>B"
            proof -
              have "Lng (Pred ?PJ) = 1" using PP0 by simp
              hence "Lng ?PJ = 2" using LPJg1 by (simp add: Pred_def)
              hence "m - Pcut M = 0" using mPJlt by simp
              thus ?thesis using PP0 Mark_singleton[of 0] by simp
            qed
            have tPP0: "Trans (Pred ?PJ) = 0\<^sub>B" using PP0 Trans_singleton[of 0] by simp
            have s0b0: "s0 = [] \<and> b0 = []"
            proof -
              have "flatBT (Trans (Pred ?PJ)) = s0 @ flatBT (Mark (Pred ?PJ) (m - Pcut M)) @ b0"
                using dP_J by (simp add: scb_decomp_def)
              hence "[Zsym] = s0 @ [Zsym] @ b0" using tPP0 kPP0 by simp
              thus ?thesis by (cases s0) auto
            qed
            have markPM0: "Mark (Pred M) m = Dpt 0 0\<^sub>B" using markPM PP0 by simp
            have transPM0: "Trans (Pred M) = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transPM PP0 by simp
            have iptD0: "isPTB_str (flatBT (Dpt 0 0\<^sub>B))"
              by (rule isPTB_str_Dpt) (simp_all add: zero_enat_def)
            have selfD0: "scb_decomp (Dpt 0 0\<^sub>B) [] (flatBT (Dpt 0 0\<^sub>B)) []"
              using iptD0 by (rule scb_decomp_self)
            have X1D0: "length (untrm (Dpt 0 0\<^sub>B)) = 1" by simp
            have liftP: "scb_decomp (Trans ?A +\<^sub>B Dpt 0 0\<^sub>B) (liftS (Trans ?A) [])
                            (flatBT (Dpt 0 0\<^sub>B)) ([] @ [RP])"
              by (rule scb_addBT_left[OF selfD0 X1D0 Yne])
            have dP: "scb_decomp (Trans (Pred M)) (liftS (Trans ?A) [])
                          (flatBT (Mark (Pred M) m)) ([] @ [RP])"
              using liftP transPM0 markPM0 by simp
            have dMm: "scb_decomp (Trans M) (liftS (Trans ?A) [])
                          (flatBT (Mark M m)) ([] @ [RP])"
              using dM s0b0 by simp
            show ?thesis using dP dMm by blast
          next
            case PPne: False
            have predPJRT: "Pred ?PJ \<in> RT_PS" by (rule Pred_RT_PS[OF PJRT])
            have predPJT: "Pred ?PJ \<in> T_PS" using predPJRT by (simp add: RT_PS_def)
            have LPP: "0 < Lng (Pred ?PJ)" using LPJg1 by (simp add: Pred_def)
            have tPP_ne: "Trans (Pred ?PJ) \<noteq> 0\<^sub>B"
            proof -
              have "\<not> zeroT (Pred ?PJ)"
              proof
                assume z: "zeroT (Pred ?PJ)"
                hence "Lng (Pred ?PJ) = 1" by (simp add: zeroT_def)
                obtain v where Pv: "Pred ?PJ = [(v,v)]"
                  using m_6_6_oneColumn[OF predPJT] predPJRT \<open>Lng (Pred ?PJ) = 1\<close> by auto
                have "v = 0" using z Pv by (simp add: zeroT_def entry_def)
                thus False using PPne Pv by simp
              qed
              thus ?thesis using m_7_3_Trans_zeroT[OF predPJRT] by blast
            qed
            \<comment> \<open>\<open>Pred PJ\<close> is mono or single-column; its \<open>Trans\<close> is single-principal\<close>
            have X1_PPJ: "length (untrm (Trans (Pred ?PJ))) = 1"
            proof (cases "Lng (Pred ?PJ) = 1")
              case True
              obtain v where Pv: "Pred ?PJ = [(v,v)]"
                using m_6_6_oneColumn[OF predPJT] predPJRT True by auto
              have tv: "Trans (Pred ?PJ) = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
                using Pv Trans_singleton[of v] by simp
              hence "v \<noteq> 0" using tPP_ne by (cases "v = 0") auto
              hence "Trans (Pred ?PJ) = Dpt (enat v) 0\<^sub>B" using tv by simp
              thus ?thesis by simp
            next
              case False
              have LPP1: "1 < Lng (Pred ?PJ)" using LPP False by linarith
              have LPJ3: "1 < Lng ?PJ - 1"
                using LPP1 LPJg1 by (simp add: Pred_def)
              \<comment> \<open>\<open>Pred PJ = butlast PJ = seg PJ 0 (Lng PJ - 2)\<close>, a mono prefix of mono \<open>PJ\<close>\<close>
              have predPJmono: "monoT (Pred ?PJ)"
              proof -
                have PJPT: "?PJ \<in> PT_PS" using PJT PJmono by (simp add: PT_PS_def)
                have j0pos: "0 < Lng ?PJ - 2" using LPJ3 by simp
                have j0lt: "Lng ?PJ - 2 < Lng ?PJ" using LPJg1 by simp
                have mp: "monoT (seg ?PJ 0 (Lng ?PJ - 2))"
                  by (rule m_6_2_mono_prefix[OF PJPT j0pos j0lt])
                have segbl: "seg ?PJ 0 (Lng ?PJ - 2) = butlast ?PJ"
                proof -
                  have suc: "Suc (Lng ?PJ - 2) \<le> Lng ?PJ" using LPJ3 by simp
                  have "seg ?PJ 0 (Lng ?PJ - 2) = take (Suc (Lng ?PJ - 2)) ?PJ"
                    by (rule seg_0_eq_take[OF suc])
                  also have "Suc (Lng ?PJ - 2) = Lng ?PJ - 1" using LPJ3 by simp
                  also have "take (Lng ?PJ - 1) ?PJ = butlast ?PJ"
                    by (simp add: butlast_conv_take)
                  finally show ?thesis .
                qed
                have "Pred ?PJ = butlast ?PJ" using LPJg1 by (simp add: Pred_def)
                thus ?thesis using mp segbl by simp
              qed
              obtain p where "Trans (Pred ?PJ) = Trm [p]"
                using Trans_PT_single predPJRT predPJmono tPP_ne by blast
              thus ?thesis by simp
            qed
            have transPM': "Trans (Pred M) = Trans ?A +\<^sub>B Trans (Pred ?PJ)"
              using transPM PPne by simp
            have markPM': "Mark (Pred M) m = Mark (Pred ?PJ) (m - Pcut M)"
              using markPM PPne by simp
            have liftP: "scb_decomp (Trans ?A +\<^sub>B Trans (Pred ?PJ)) (liftS (Trans ?A) s0)
                            (flatBT (Mark (Pred ?PJ) (m - Pcut M))) (b0 @ [RP])"
              by (rule scb_addBT_left[OF dP_J X1_PPJ Yne])
            have dP: "scb_decomp (Trans (Pred M)) (liftS (Trans ?A) s0)
                          (flatBT (Mark (Pred M) m)) (b0 @ [RP])"
              using liftP transPM' markPM' by simp
            show ?thesis using dP dM by blast
          qed
        qed
      qed
    qed
  qed
  obtain s0 b0 where
    H0: "scb_decomp (Trans (Pred M)) s0 (flatBT (Mark (Pred M) m)) b0"
        "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
    using ex MR mM mlt by blast
  show ?thesis
  proof (rule ex1I[of _ "(s0, b0)"])
    show "scb_decomp (Trans (Pred M)) (fst (s0, b0)) (flatBT (Mark (Pred M) m)) (snd (s0, b0))
        \<and> scb_decomp (Trans M) (fst (s0, b0)) (flatBT (Mark M m)) (snd (s0, b0))"
      using H0 by simp
  next
    fix sb
    assume A: "scb_decomp (Trans (Pred M)) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)
             \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
    have dP_sb: "scb_decomp (Trans (Pred M)) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)"
      using A by simp
    show "sb = (s0, b0)"
    proof (cases "Trans (Pred M) = Trm []")
      case t1z: True
      have knil: "flatBT (Mark (Pred M) m) \<noteq> []"
      proof (cases "Mark (Pred M) m")
        case (Trm xs)
        show ?thesis
        proof (cases xs)
          case Nil thus ?thesis using Trm by simp
        next
          case (Cons a as)
          obtain u t' where "a = DB u t'" by (cases a)
          thus ?thesis using Trm Cons by (cases as) auto
        qed
      qed
      have e: "[Zsym] = (fst sb) @ flatBT (Mark (Pred M) m) @ (snd sb)"
        using dP_sb t1z by (simp add: scb_decomp_def)
      have sb0: "fst sb = [] \<and> snd sb = []"
        using e knil by (cases "fst sb"; cases "snd sb" rule: rev_cases) auto
      have e2: "[Zsym] = s0 @ flatBT (Mark (Pred M) m) @ b0"
        using H0(1) t1z by (simp add: scb_decomp_def)
      have s0b0: "s0 = [] \<and> b0 = []"
        using e2 knil by (cases s0; cases b0 rule: rev_cases) auto
      show ?thesis using sb0 s0b0 by (cases sb) auto
    next
      case t1ne: False
      have "fst sb = s0 \<and> snd sb = b0"
        by (rule m_7_2_scb_unique_sb[OF dP_sb H0(1) t1ne])
      thus ?thesis by (cases sb) auto
    qed
  qed
qed

text \<open>系（\<open>Trans\<close>の\<open>Mark\<close>と\<open>Pred\<close>による表示） (§7.4): for any
  \<open>(M,m) \<in> T\<^bsub>PS\<^esub>\<^sup>Marked\<close> (modelled by \<open>(M,m) \<in> Marked\<close>), if \<open>m < Lng M - 1\<close>
  then there exist unique \<open>(s\<^sub>0,b\<^sub>0)\<close> such that \<open>(s\<^sub>0, Mark(Pred M, m), b\<^sub>0)\<close> is an
  scb-decomposition of \<open>Trans(Pred M)\<close> and \<open>(s\<^sub>0, Mark(M, m), b\<^sub>0)\<close> is an
  scb-decomposition of \<open>Trans M\<close>.\<close>


text \<open>This proposition records the corrected form in
  @{file "../../corrections.md"}; the original annotation above is retained for
  comparison.\<close>

lemma p_7_4_Trans_Mark_Pred:
  assumes "(M, m) \<in> Marked" "M \<in> RT_PS"
    and "m < Lng M - 1"
  shows "\<exists>!sb. scb_decomp (Trans (Pred M)) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)
            \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
  using assms by (rule m_7_4_Trans_Mark_Pred)

end

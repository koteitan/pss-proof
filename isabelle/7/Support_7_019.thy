theory Support_7_019
  imports Frontier_7_022
begin

text \<open>命題（\<open>Pred\<close>-on-\<open>Trans\<close> descent）: \<open>1 < Lng M \<Longrightarrow> lessBT (Trans (Pred M)) (Trans M)\<close>
  on \<open>RT\<^sub>PS\<close>.  Strong \<open>Lng\<close>-induction; the mono surgery branch mirrors
  @{thm [source] trans_inv_B_hard} (\<open>c\<^sub>1\<close>/\<open>c\<^sub>2\<close> replacement) closed by
  @{thm [source] transC1_lessBT_transC2_full} + @{thm [source] scbext_lessBT};
  the multi branch recurses on the last \<open>P\<close>-component (smaller \<open>Lng\<close>) via
  @{thm [source] Trans_Pred_multi_last} + @{thm [source] lessBT_addBT_mono_right}.
  Empirically 0 failures / 7042 cases.\<close>

lemma m_7_3_Pred_Trans_descend:
  "M \<in> RT_PS \<longrightarrow> 1 < Lng M \<longrightarrow> lessBT (Trans (Pred M)) (Trans M)"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (rule impI)+
    assume MR: "M \<in> RT_PS" and L: "1 < Lng M"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
    have nzM: "\<not> zeroT M" using L by (auto simp: zeroT_def)
    show "lessBT (Trans (Pred M)) (Trans M)"
    proof (cases "monoT M")
      case mono: True
      have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
      have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
      show ?thesis
      proof (cases "Trans (Pred M) = 0\<^sub>B")
        case t1z: True
        let ?b = "entry M 1 (Lng M - 1)"
        have tv: "Trans M = Dpt 0 (Dpt (enat ?b) 0\<^sub>B)"
          using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
        show ?thesis using t1z tv by simp
      next
        case t1ne: False
        \<comment> \<open>(mono) surgery branch, mirroring @{thm [source] trans_inv_B_hard}\<close>
        have IHt1: "dfree_BT (Trans (Pred M))"
          using Trans_Mark_invariant_aux predRT by blast
        have IHmk: "\<And>m'. (Pred M, m') \<in> Marked
                     \<Longrightarrow> (Trans (Pred M), Mark (Pred M) m') \<in> MarkedB"
          using Trans_Mark_invariant_aux predRT by blast
        have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
        let ?t1 = "Trans (Pred M)"
        let ?bv = "entry M 1 (Lng M - 1)"
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
        \<comment> \<open>identify \<open>c\<^sub>1 = transC1 M\<close>, \<open>c\<^sub>2 = transC2 M\<close>\<close>
        have transJ1eq: "transJ1 M = Lng M - 1" by (simp add: transJ1_def)
        have transJ0eq: "transJ0 M = jp" by (simp add: transJ0_def transJ1_def jp_def)
        have transJm1eq: "transJm1 M = Adm M jp"
          by (simp add: transJm1_def transJ0eq)
        have c1eqT: "c1 = transC1 M"
          by (simp add: c1_def transC1_def transJm1eq)
        have c2eqT: "c2 = transC2 M"
          unfolding c2_def transC2_def Let_def
            vv_def tt2_def c1eqT transV_def transT2_def
            JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
          by simp
        \<comment> \<open>SOME decomposition of \<open>t\<^sub>1\<close> at \<open>flatBT c\<^sub>1\<close>\<close>
        have mkdA: "(Pred M, Adm M jp) \<in> Marked"
          using Marked_Pred_Adm[OF MT L hp] jp_def by simp
        have mb1: "(?t1, c1) \<in> MarkedB" using IHmk[OF mkdA] c1_def by simp
        have t1neT: "?t1 \<noteq> Trm []" using t1ne by simp
        have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
          using mb1 unfolding MarkedB_def by auto
        have dsome: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
          unfolding sb1_def by (rule someI_ex[OF exsb])
        \<comment> \<open>\<open>c\<^sub>1 = Trm [pc]\<close>\<close>
        have iptc1: "isPTB_str (flatBT c1)"
          using dsome t1neT by (simp add: scb_decomp_def)
        then obtain pc where pcf: "dfree_BP pc" and pcl: "flatBT c1 = flatBP pc"
          by (auto simp: isPTB_str_def)
        have c1p: "c1 = Trm [pc]"
        proof -
          have "flatBT c1 = flatBT (Trm [pc])" using pcl by simp
          thus ?thesis by (rule m_7_flatBT_inj)
        qed
        \<comment> \<open>\<open>c\<^sub>2 = Trm [pc2]\<close>, via single-principal reconstruction\<close>
        have NP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
        have J1pos: "transJ1 M > 0" using L by (simp add: transJ1_def)
        have T1ne: "transT1 M \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
        have c2pc1: "Lng (PB (transC2 M)) = 1" by (rule transC2_single_principal)
        have c2recon: "transC2 M = Dpt (bpHeadV (transC2 M)) (bpHeadT (transC2 M))"
          by (rule principal_reconstruct[OF c2pc1])
        obtain pc2 where c2p: "c2 = Trm [pc2]"
          using c2recon c2eqT by (metis BT.exhaust untrm.simps)
        have iptc2: "isPTB_str (flatBT (Trm [pc2]))"
        proof -
          have vne: "transV M \<noteq> \<infinity>"
          proof -
            have pc1: "Lng (PB (transC1 M)) = 1"
              by (rule transC1_single_principal[OF MR NP J1pos T1ne])
            have c1ne: "transC1 M \<noteq> 0\<^sub>B"
            proof
              assume "transC1 M = 0\<^sub>B"
              thus False using pc1 by (simp add: PB_def)
            qed
            have c1TB: "transC1 M \<in> T_B"
              using m_7_3_Mark_in_T_B[OF predRT mkdA] transJm1eq[symmetric]
              by (simp add: transC1_def)
            have c1Dpt: "transC1 M = Dpt (transV M) (transT2 M)"
              using principal_reconstruct[OF pc1]
              by (simp add: transV_def transT2_def)
            thus ?thesis using c1TB unfolding c1Dpt by (auto simp: T_B_def)
          qed
          have t2df: "dfree_BT (transT2 M)"
          proof -
            have pc1: "Lng (PB (transC1 M)) = 1"
              by (rule transC1_single_principal[OF MR NP J1pos T1ne])
            have c1TB: "transC1 M \<in> T_B"
              using m_7_3_Mark_in_T_B[OF predRT mkdA] transJm1eq[symmetric]
              by (simp add: transC1_def)
            have c1Dpt: "transC1 M = Dpt (transV M) (transT2 M)"
              using principal_reconstruct[OF pc1]
              by (simp add: transV_def transT2_def)
            thus ?thesis using c1TB unfolding c1Dpt by (auto simp: T_B_def)
          qed
          have c2df: "dfree_BT c2" using dfree_transC2[OF vne t2df] c2eqT by simp
          have "dfree_BT (Trm [pc2])" using c2df c2p by simp
          then obtain p where "pc2 = p" and "dfree_BP p" by auto
          thus ?thesis by (auto simp: isPTB_str_def)
        qed
        \<comment> \<open>replace the principal \<open>c\<^sub>1\<close> by \<open>c\<^sub>2\<close> to read off \<open>Trans M\<close>\<close>
        have dsome': "scb_decomp ?t1 (fst sb1) (flatBT (Trm [pc])) (snd sb1)"
          using dsome c1p by simp
        obtain t' where t'f: "flatBT t' = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
            and t'd: "scb_decomp t' (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
          using scb_replace_principal[OF dsome' iptc2] by blast
        have transM: "Trans M = t'"
          using trans_val t'f c2p unflatBT_flat[of t'] by simp
        \<comment> \<open>the two flat equalities for \<open>scbext_lessBT\<close>\<close>
        have flat1: "flatBT ?t1 = fst sb1 @ flatBP pc @ snd sb1"
          using dsome c1p by (simp add: scb_decomp_def)
        have flat2: "flatBT (Trans M) = fst sb1 @ flatBP pc2 @ snd sb1"
          using transM t'f by simp
        have brp: "\<forall>x \<in> set (snd sb1). x = RP"
          using dsome by (simp add: scb_decomp_def)
        \<comment> \<open>\<open>lessBP pc pc2\<close> from \<open>lessBT c\<^sub>1 c\<^sub>2\<close>\<close>
        have lbt: "lessBT (transC1 M) (transC2 M)"
          by (rule transC1_lessBT_transC2_full[OF MR NP J1pos T1ne])
        have lbp: "lessBP pc pc2"
        proof -
          have "lessBT (Trm [pc]) (Trm [pc2])" using lbt c1eqT c2eqT c1p c2p by simp
          thus ?thesis by simp
        qed
        show ?thesis
          by (rule scbext_lessBT[OF flat1 flat2 brp lbp])
      qed
    next
      case nmono: False
      \<comment> \<open>(multi) branch: recurse on the last \<open>P\<close>-component\<close>
      have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
      let ?A = "take (Pcut M) M"
      let ?PJ = "drop (Pcut M) M"
      have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
      have AR: "?A \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF MR muM])
      have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
        by (rule trans_multiT_last_component(1)[OF MT muM])
      have Pne: "P M \<noteq> []" by (rule P_nonempty)
      have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
      have PJRT: "?PJ \<in> RT_PS"
        using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
      have LPJ: "Lng ?PJ < Lng M"
      proof -
        have "Lng ?PJ = Lng M - Pcut M" by simp
        thus ?thesis using cut L by linarith
      qed
      \<comment> \<open>\<open>transM\<close> for \<open>M\<close>, mirroring @{thm [source] trans_inv_C}\<close>
      have domTM: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
      have nmono': "\<not> monoT M" using muM by (simp add: multiT_def)
      have j0eqM: "Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 = Pcut M"
        by (rule trans_multiT_last_component(2)[OF MT muM])
      have c1: "(M \<notin> RT_PS) = False" using MR by simp
      have c2: "(Lng M - 1 = 0) = False" using L by simp
      have c3: "monoT M = False" using nmono' by simp
      have LdJ: "Lng ?PJ = Lng M - Pcut M" by simp
      have Aeq2: "seg M 0 (Lng M - 1 - Lng ?PJ + 1 - 1) = ?A"
      proof -
        have "Lng M - 1 - Lng ?PJ + 1 - 1 = Pcut M - 1" using LdJ cut by linarith
        moreover have "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
          by (rule seg_0_eq_take) (use cut L in linarith)
        moreover have "Suc (Pcut M - 1) = Pcut M" using cut by simp
        ultimately show ?thesis by simp
      qed
      have transM: "Trans M = (if ?PJ = [(0, 0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B
                               else Trans ?A +\<^sub>B Trans ?PJ)"
      proof -
        have raw: "Trans M =
            (if P M ! (Lng (P M) - 1) = [(0, 0)]
             then Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                    +\<^sub>B Dpt 0 0\<^sub>B
             else Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                    +\<^sub>B Trans (P M ! (Lng (P M) - 1)))"
          by (subst Trans.psimps[OF domTM]) (simp only: c1 c2 c3 if_False Let_def)
        show ?thesis unfolding raw PJeq Aeq2 ..
      qed
      \<comment> \<open>\<open>PJ \<noteq> [(0,0)]\<close> exactly when \<open>1 < Lng PJ\<close>, but split on \<open>Lng PJ\<close>\<close>
      show ?thesis
      proof (cases "1 < Lng ?PJ")
        case PJ1: False
        \<comment> \<open>\<open>Lng PJ = 1\<close>: \<open>Pcut M = Lng M - 1\<close>, so \<open>Pred M = A\<close>\<close>
        have LPJ1: "Lng ?PJ = 1"
        proof -
          have "Lng ?PJ = Lng M - Pcut M" by simp
          hence "0 < Lng ?PJ" using cut L by linarith
          thus ?thesis using PJ1 by simp
        qed
        have cj1: "Pcut M = Lng M - 1" using LPJ1 LdJ by simp
        have predA: "Pred M = ?A"
        proof -
          have "Pred M = take (Lng M - 1) M" using L by (simp add: Pred_def butlast_conv_take)
          thus ?thesis using cj1 by simp
        qed
        \<comment> \<open>the right summand is nonzero, so \<open>lessBT (Trans A) (Trans A +\<^sub>B nz)\<close>\<close>
        show ?thesis
        proof (cases "?PJ = [(0, 0)]")
          case True
          have tv: "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM True by simp
          have "lessBT (Trans ?A) (Trans ?A +\<^sub>B Dpt 0 0\<^sub>B)"
            by (rule lessBT_addBT_self) simp
          thus ?thesis using tv predA by simp
        next
          case False
          have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
          have nzPJ: "\<not> zeroT ?PJ"
          proof
            assume z: "zeroT ?PJ"
            obtain v where v: "?PJ = [(v, v)]"
              using m_6_6_oneColumn[OF PJT] PJRT LPJ1 by auto
            have "entry ?PJ 1 0 = 0" using z by (simp add: zeroT_def)
            hence "v = 0" using v by (simp add: entry_def)
            thus False using False v by simp
          qed
          have nz: "Trans ?PJ \<noteq> 0\<^sub>B"
            using m_7_3_Trans_zeroT[OF PJRT] nzPJ by simp
          have tv: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM False by simp
          have "lessBT (Trans ?A) (Trans ?A +\<^sub>B Trans ?PJ)"
            by (rule lessBT_addBT_self[OF nz])
          thus ?thesis using tv predA by simp
        qed
      next
        case PJgt1: True
        \<comment> \<open>\<open>1 < Lng PJ\<close>: recurse on \<open>PJ\<close>\<close>
        have notPJ00: "?PJ \<noteq> [(0, 0)]"
        proof
          assume "?PJ = [(0, 0)]"
          hence "Lng ?PJ = 1" by simp
          thus False using PJgt1 by simp
        qed
        have tvM: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM notPJ00 by simp
        \<comment> \<open>helper: \<open>Trans (Pred M) = Trans A +\<^sub>B Z\<close>\<close>
        have tvPred: "Trans (Pred M)
            = Trans ?A +\<^sub>B (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B
                            else Trans (Pred ?PJ))"
          using Trans_Pred_multi_last[OF MR muM PJgt1] by simp
        \<comment> \<open>suffices: \<open>lessBT Z (Trans PJ)\<close>\<close>
        have inner: "lessBT (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B else Trans (Pred ?PJ))
                            (Trans ?PJ)"
        proof (cases "Pred ?PJ = [(0, 0)]")
          case predzero: True
          \<comment> \<open>\<open>Pred PJ = [(0,0)]\<close> \<Rightarrow> \<open>Lng PJ = 2\<close>, \<open>PJ\<close> mono in \<open>t1z\<close> branch\<close>
          have LPredPJ: "Lng (Pred ?PJ) = 1" using predzero by simp
          have predPJb: "Pred ?PJ = butlast ?PJ" using PJgt1 by (simp add: Pred_def)
          have LPJ2: "Lng ?PJ = 2" using LPredPJ predPJb PJgt1 by simp
          \<comment> \<open>\<open>PJ\<close> is the last ancestor-anchored component, hence mono\<close>
          have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
          have lec: "leR M 0 (Pcut M) (Lng M - 1)"
            using P_add_Pcut_props[OF L] by simp
          have cltj1: "Pcut M < Lng M - 1" using LPJ2 LdJ cut by linarith
          have cL: "Pcut M < Lng M" using cut L by linarith
          have monoPJ: "monoT ?PJ"
          proof -
            have "monoT (seg M (Pcut M) (Lng M - 1))"
              by (rule m_6_2_mono_ancestor_slice[OF MT cltj1 lec])
            thus ?thesis using drop_eq_seg[OF cL] by simp
          qed
          \<comment> \<open>\<open>Trans (Pred PJ) = 0\<close> since \<open>Pred PJ = [(0,0)]\<close>\<close>
          have t1zPJ: "Trans (Pred ?PJ) = 0\<^sub>B"
            using predzero Trans_singleton[of 0] by simp
          \<comment> \<open>\<open>PJ\<close> in mono-\<open>t1z\<close> branch: \<open>Trans PJ = Dpt 0 (Dpt (enat b) 0)\<close>\<close>
          have domPJ: "Trans_Mark_dom (Inl ?PJ)" by (rule m_7_3_Trans_welldef[OF PJRT])
          have LPJgt: "\<not> Lng ?PJ \<le> Suc 0" using PJgt1 by simp
          let ?bPJ = "entry ?PJ 1 (Lng ?PJ - 1)"
          have tvPJ: "Trans ?PJ = Dpt 0 (Dpt (enat ?bPJ) 0\<^sub>B)"
            using Trans.psimps[OF domPJ] PJRT LPJgt monoPJ t1zPJ by (simp add: Let_def)
          show ?thesis using predzero tvPJ by simp
        next
          case predne: False
          \<comment> \<open>IH on \<open>PJ\<close>: smaller \<open>Lng\<close>, reduced, \<open>1 < Lng PJ\<close>\<close>
          have ih: "lessBT (Trans (Pred ?PJ)) (Trans ?PJ)"
            using less.IH[OF LPJ] PJRT PJgt1 by blast
          show ?thesis using predne ih by simp
        qed
        have "lessBT (Trans ?A +\<^sub>B (if Pred ?PJ = [(0,0)] then Dpt 0 0\<^sub>B
                                    else Trans (Pred ?PJ)))
                     (Trans ?A +\<^sub>B Trans ?PJ)"
          by (rule lessBT_addBT_mono_right[OF inner])
        thus ?thesis using tvPred tvM by simp
      qed
    qed
  qed
qed

end

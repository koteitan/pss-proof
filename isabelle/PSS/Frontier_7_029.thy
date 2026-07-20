theory Frontier_7_029
  imports Support_7_024
begin

text \<open>§7.4 keystone (towards "Mark preserves order"): a \<open>monoT\<close> reduced sequence
  of length \<open>> 1\<close> has \<open>RightNodes (Trans M)\<close> of length \<open>\<ge> 2\<close>.  \<open>Trans M\<close> is a
  single principal \<open>Trm [DB u a]\<close> (@{thm [source] Trans_PT_single}); its
  right-spine has length \<open>1 + length (RightNodes a)\<close>, so it suffices to show the
  inner argument \<open>a \<noteq> 0\<^bsub>B\<^esub>\<close>.  In the \<open>t\<^sub>1 = 0\<close> branch \<open>Trans M = D\<^bsub>0\<^esub>(D\<^bsub>bv\<^esub> 0)\<close>
  has inner \<open>D\<^bsub>bv\<^esub> 0 \<noteq> 0\<close>; in the \<open>t\<^sub>1 \<noteq> 0\<close> (surgery) branch \<open>flatBT (Trans M)\<close>
  embeds \<open>flatBT (transC2 M)\<close> (length \<open>\<ge> 3\<close>), forcing \<open>length (flatBT a) \<ge> 2\<close>,
  hence \<open>a \<noteq> 0\<close>.\<close>

lemma Trans_mono_RN_ge2:
  assumes MR: "M \<in> RT_PS" and mono: "monoT M" and L: "1 < Lng M"
  shows "2 \<le> length (RightNodes (Trans M))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have nzM: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have tMne: "Trans M \<noteq> 0\<^sub>B" using m_7_3_Trans_zeroT[OF MR] nzM by blast
  \<comment> \<open>\<open>Trans M\<close> is a single principal \<open>Trm [DB u a]\<close>\<close>
  obtain p where Tp: "Trans M = Trm [p]"
    using Trans_PT_single[THEN mp, THEN mp, THEN mp, OF MR mono tMne] by blast
  obtain u a where pua: "p = DB u a" by (cases p)
  have TM: "Trans M = Trm [DB u a]" using Tp pua by simp
  have rnM: "RightNodes (Trans M) = the_enat u # RightNodes a"
    using TM by simp
  \<comment> \<open>suffices: the inner argument \<open>a\<close> is nonzero\<close>
  have suff: "a \<noteq> 0\<^sub>B \<Longrightarrow> 2 \<le> length (RightNodes (Trans M))"
  proof -
    assume "a \<noteq> 0\<^sub>B"
    hence "RightNodes a \<noteq> []" by (simp add: rnsub_RightNodes_empty_iff)
    thus ?thesis using rnM by (cases "RightNodes a") auto
  qed
  have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  let ?j1 = "Lng M - 1"
  show ?thesis
  proof (cases "Trans (Pred M) = 0\<^sub>B")
    case t1z: True
    \<comment> \<open>\<open>Trans M = D\<^bsub>0\<^esub>(D\<^bsub>bv\<^esub> 0)\<close>, inner \<open>= D\<^bsub>bv\<^esub> 0 \<noteq> 0\<close>\<close>
    have tv: "Trans M = Dpt 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
      using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
    have "Trm [DB u a] = Trm [DB 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)]"
      using TM tv by simp
    hence "a = Dpt (enat (entry M 1 ?j1)) 0\<^sub>B" by simp
    hence "a \<noteq> 0\<^sub>B" by simp
    thus ?thesis by (rule suff)
  next
    case t1ne: False
    \<comment> \<open>surgery branch: replicate the \<open>flatBT (Trans M)\<close> = \<open>fst sb1 @ flatBT c2 @ snd sb1\<close> derivation\<close>
    have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
    have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L])
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
    \<comment> \<open>\<open>flatBT (transC2 M)\<close> has length \<open>\<ge> 3\<close> (inner \<open>bpHeadT c2 \<noteq> 0\<close>)\<close>
    have c2tail_ne: "bpHeadT c2 \<noteq> 0\<^sub>B"
      using transC2_inner_nonzero[of M] c2eqT by simp
    have lenc2: "3 \<le> length (flatBT c2)"
    proof -
      have "2 \<le> length (flatBT (bpHeadT c2))"
        by (rule flatBT_len_ge2[OF c2tail_ne])
      thus ?thesis using c2Dsym by simp
    qed
    \<comment> \<open>the surgery output flattens to \<open>fst sb1 @ flatBT c2 @ snd sb1\<close>\<close>
    have inv1: "(Trans (Pred M), c1) \<in> MarkedB"
      using m_7_3_Trans_Mark_MarkedB[OF predRT mkjm1] c1_def by simp
    have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
      using inv1 unfolding MarkedB_def by auto
    have dsb: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
      unfolding sb1_def by (rule someI_ex[OF exsb])
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
      then obtain q where "pc2 = q" and "dfree_BP q" by auto
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
    \<comment> \<open>\<open>length (flatBT (Trans M)) \<ge> 3\<close>, and \<open>flatBT (Trans M) = Dsym u # flatBT a\<close>\<close>
    have flatlen3: "3 \<le> length (flatBT (Trans M))"
      using flatTM lenc2 by simp
    have flatTMua: "flatBT (Trans M) = Dsym u # flatBT a"
      using TM by simp
    have "2 \<le> length (flatBT a)"
      using flatlen3 flatTMua by simp
    hence "flatBT a \<noteq> [Zsym]" by auto
    hence "a \<noteq> 0\<^sub>B" by auto
    thus ?thesis by (rule suff)
  qed
qed

end

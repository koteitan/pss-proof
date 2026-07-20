theory Support_7_031
  imports Frontier_7_036
begin

\<comment> \<open>§7.4 monoT interior (C) Step 1: transCondI/III/V/VI correspondences green.\<close>


section \<open>§7.4 monoT-interior core (Step 3): \<open>Mark M m = Trans (seg M m j\<^sub>1)\<close>\<close>

text \<open>Step 3: the \<open>monoT\<close>-interior core.  Combines identities (1)/(2)/(3) with the
  surgery splice.  \<open>Mark M m\<close> (surgery branch, \<open>m < j\<^sub>1\<close>) and \<open>Trans N\<close>
  (\<open>N = Red(seg M m j\<^sub>1)\<close>, monoT, \<open>t\<^sub>1 \<noteq> 0\<close>) both read off as
  \<open>unflatBT(fst s @ flatBT c\<^sub>2 @ snd s)\<close>; by id1 \<open>c\<^sub>0\<^bsup>M\<^esup> = Mark(Pred M) m = transT1 N\<close>,
  id2 \<open>c\<^sub>1\<^bsup>M\<^esup> = transC1 M = transC1 N\<close> and id3 \<open>c\<^sub>2\<^bsup>M\<^esup> = transC2 M = transC2 N\<close>, so
  the \<open>SOME\<close> decompositions and the spliced terms coincide, giving
  \<open>Mark M m = Trans N = Trans(seg M m j\<^sub>1)\<close> (last step by
  @{thm [source] Trans_slice_eq_Red}).  Takes \<open>ihPred\<close> (keystone IH at \<open>Pred M\<close>,
  for id1) and \<open>markShift\<close> (for id2) as explicit hypotheses (induction-ready,
  mirroring id1/id2); the assembly discharges both from the strong-induction
  hypothesis.  Anchoring (\<open>leR\<close>/\<open>hasParent\<close>/\<open>m \<le> j\<^sub>0\<close>/\<open>j\<^sub>0 < j\<^sub>1\<close>) is derived from
  \<open>monoT M\<close> and \<open>(M,m) \<in> Marked\<close> (\<open>m \<le> j\<^sub>0\<close> via
  @{thm [source] a1_le0_ancestor_le_parent}: a proper \<open>le\<^sub>0\<close>-ancestor is below the
  immediate row-0 parent).\<close>

lemma m_7_4_monoT_interior_core:
  assumes MR: "M \<in> RT_PS" and mono: "monoT M"
    and mM: "(M, m) \<in> Marked" and mint: "m < Lng M - 2"
    and ihPred: "Mark (Pred M) m = Trans (seg (Pred M) m (Lng (Pred M) - 1))"
    and markShift: "Mark (Pred (Red (seg M m (Lng M - 1)))) (transJm1 M - m)
                    = Mark (Pred M) (transJm1 M)"
  shows "Mark M m = Trans (seg M m (Lng M - 1))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have MP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  let ?j1 = "Lng M - 1"  let ?S = "seg M m ?j1"  let ?N = "Red ?S"
  have L: "2 < Lng M" using mint by linarith
  have L1: "1 < Lng M" using L by linarith
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L1 by simp
  have mj1: "m < ?j1" using mint by linarith
  have j1le: "?j1 \<le> Lng M - 1" by simp
  \<comment> \<open>anchoring facts (all derivable from monoT + Marked)\<close>
  have leM: "leR M 0 m ?j1" using mM by (simp add: Marked_def)
  have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L1])
  let ?j0 = "parent M 0 ?j1"
  have parj0: "nextR M 0 ?j0 ?j1"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have j0ltj1: "?j0 < ?j1" using parj0 by (simp add: nextR_def nextrel0_def)
  have le0m: "le0 M m ?j1" using leM by (simp add: leR_def)
  have mnej1: "m \<noteq> ?j1" using mj1 by simp
  have anc0: "m \<le> ?j0"
    by (rule a1_le0_ancestor_le_parent[OF le0m mnej1 parj0])
  have j0lt: "?j0 < ?j1" by (rule j0ltj1)
  \<comment> \<open>\<open>Pred M\<close> reduced, nonzero; \<open>(Pred M, m) \<in> Marked\<close>\<close>
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predb: "Pred M = butlast M" using L1 by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using predb by simp
  have mP: "(Pred M, m) \<in> Marked"
    by (rule Marked_Pred[OF MT L1 mM]) (use mj1 in linarith)
  have nzPred: "\<not> zeroT (Pred M)"
  proof - have "1 < Lng (Pred M)" using LP L by linarith
    thus ?thesis by (auto simp: zeroT_def) qed
  have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B"
    using m_7_3_Trans_zeroT[OF predRT] nzPred by simp
  \<comment> \<open>=== N facts ===\<close>
  have anc: "Red ?N = ?N \<and> monoT ?N
           \<and> ?S = (IncrFirst ^^ (entry M 0 m - entry M 1 m)) ?N"
    by (rule m_6_6_ancestor_slice_Red_IncrFirst[OF MR mj1 j1le leM])
  have monoN: "monoT ?N" using anc by simp
  have NR: "?N \<in> RT_PS" using slice_Red_in_RT_PS[OF MR mj1 j1le leM] by simp
  have NT: "?N \<in> T_PS" using NR by (simp add: RT_PS_def)
  have NP: "?N \<in> PT_PS" using NT monoN by (simp add: PT_PS_def)
  have LN: "Lng ?N = Suc ?j1 - m"
  proof -
    have "Lng ?N = Lng ?S"
      using arg_cong[OF conjunct2[OF conjunct2[OF anc]], of Lng]
      by (simp add: Lng_funpow_IncrFirst)
    thus ?thesis by simp
  qed
  have LNgt2: "2 < Lng ?N" using LN mint by simp
  have LN1: "1 < Lng ?N" using LNgt2 by linarith
  have predNRT: "Pred ?N \<in> RT_PS" by (rule Pred_RT_PS[OF NR])
  have predNb: "Pred ?N = butlast ?N" using LN1 by (simp add: Pred_def)
  have J1Npos: "transJ1 ?N > 0" using LN1 by (simp add: transJ1_def)
  have nzPredN: "\<not> zeroT (Pred ?N)"
  proof - have "Lng (Pred ?N) = Lng ?N - 1" using predNb by simp
    hence "1 < Lng (Pred ?N)" using LNgt2 by linarith
    thus ?thesis by (auto simp: zeroT_def) qed
  have T1N: "transT1 ?N \<noteq> 0\<^sub>B"
    using m_7_3_Trans_zeroT[OF predNRT] nzPredN by (simp add: transT1_def)
  \<comment> \<open>=== identities (1),(2),(3) ===\<close>
  have id1: "Mark (Pred M) m = Trans (Pred ?N)"
    by (rule m_7_4_interior_id1[OF mM MR mint ihPred])
  have ancJm1: "m \<le> transJm1 M"
  proof -
    have admMm: "adm M m" using mM by (simp add: Marked_def)
    have "m \<le> Adm M ?j0" by (rule adm_Adm_max[OF admMm anc0])
    thus ?thesis by (simp add: transJm1_def transJ0_def transJ1_def)
  qed
  have id2: "transC1 M = transC1 ?N"
    by (rule m_7_4_interior_id2[OF MR mint leM hp anc0 j0lt mM ancJm1 markShift])
  note B = repr_transCond_atoms[OF mM MR mint leM hp anc0 j0lt]
  have ej0: "entry ?N 1 (transJ0 ?N) = entry M 1 (transJ0 M)"
    using B(4) by (simp add: transJ0_def transJ1_def)
  have ej1: "entry ?N 1 (transJ1 ?N) = entry M 1 (transJ1 M)"
    using B(3) by (simp add: transJ1_def)
  have cI: "transCondI ?N = transCondI M"
    by (rule repr_transCondI_eq[OF mM MR mint leM hp anc0 j0lt])
  have cIII: "transCondIII ?N = transCondIII M"
    by (rule repr_transCondIII_eq[OF mM MR mint leM hp anc0 j0lt])
  have cV: "transCondV ?N = transCondV M"
    by (rule repr_transCondV_eq[OF mM MR mint leM hp anc0 j0lt])
  have cVI: "transCondVI ?N = transCondVI M"
    by (rule repr_transCondVI_eq[OF mM MR mint leM hp anc0 j0lt])
  have id3: "transC2 M = transC2 ?N"
    by (rule m_7_4_interior_id3[OF id2 ej0 ej1 cI cIII cV cVI])
  \<comment> \<open>=== Mark M m surgery form ===\<close>
  have domK: "\<And>m'. Trans_Mark_dom (Inr (M, m'))" by (rule m_7_3_Mark_welldef[OF MR])
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
  have transJ0eq: "transJ0 M = jp" by (simp add: transJ0_def transJ1_def jp_def)
  have c1eqT: "c1 = transC1 M"
    by (simp add: c1_def transC1_def transJm1_def transJ0eq)
  have c2eqT: "c2 = transC2 M"
    unfolding c2_def transC2_def Let_def
      vv_def tt2_def c1eqT transV_def transT2_def
      JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
    by simp
  have hpN: "hasParent ?N 0 (Lng ?N - 1)"
    by (rule monoT_hasParent0_last[OF NT monoN LN1])
  have mkdAN: "(Pred ?N, Adm ?N (parent ?N 0 (Lng ?N - 1))) \<in> Marked"
    using Marked_Pred_Adm[OF NT LN1 hpN] by simp
  have transC1N: "transC1 ?N = Mark (Pred ?N) (Adm ?N (parent ?N 0 (Lng ?N - 1)))"
    by (simp add: transC1_def transJm1_def transJ0_def transJ1_def)
  have mbN: "(Trans (Pred ?N), transC1 ?N) \<in> MarkedB"
  proof -
    have "(Trans (Pred ?N), Mark (Pred ?N) (Adm ?N (parent ?N 0 (Lng ?N - 1)))) \<in> MarkedB"
      using Trans_Mark_invariant_aux predNRT mkdAN by blast
    thus ?thesis using transC1N by simp
  qed
  have mb0: "(Mark (Pred M) m, c1) \<in> MarkedB"
    using mbN id1 id2 c1eqT by simp
  define sm where
    "sm = (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb) (flatBT c1) (snd sb))"
  have mark_val_raw: "Mark M m = (if (Mark (Pred M) m, c1) \<in> MarkedB
        then unflatBT
               (fst (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                (flatBT c1) (snd sb))
                @ flatBT c2
                @ snd (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                  (flatBT c1) (snd sb)))
        else Dpt (enat ?bv) 0\<^sub>B)"
    using Mark.psimps[OF domK] MR Lgt1 mono t1ne mj1
    unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
              tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
              ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
              c2_def[symmetric]
    by simp
  have mark_val: "Mark M m = unflatBT (fst sm @ flatBT c2 @ snd sm)"
    using mark_val_raw mb0 by (simp add: sm_def)
  \<comment> \<open>=== Trans N surgery form ===\<close>
  have domTN: "Trans_Mark_dom (Inl ?N)" by (rule m_7_3_Trans_welldef[OF NR])
  have LNgt1: "\<not> Lng ?N \<le> Suc 0" using LN1 by simp
  let ?bvN = "entry ?N 1 (Lng ?N - 1)"
  define jpN where "jpN = parent ?N 0 (Lng ?N - 1)"
  define c1N where "c1N = Mark (Pred ?N) (Adm ?N jpN)"
  define vvN where "vvN = bpHeadV c1N"
  define tt2N where "tt2N = bpHeadT c1N"
  define JJ1N where "JJ1N = Lng (PB tt2N) - 1"
  define pjN where "pjN = PB tt2N ! JJ1N"
  define ldjN where "ldjN = (bpHeadV pjN = enat (entry ?N 1 jpN))"
  define tt3N where "tt3N = (if ldjN then SigmaB (take JJ1N (PB tt2N)) else tt2N)"
  define tt4N where "tt4N = (if ldjN then bpHeadT pjN else tt2N)"
  define c2N where "c2N = (if transCondI ?N \<or> transCondIII ?N \<or> transCondV ?N
                          then Dpt vvN (tt2N +\<^sub>B Dpt (enat ?bvN) 0\<^sub>B)
                          else if transCondVI ?N
                          then Dpt vvN (Dpt (enat ?bvN) 0\<^sub>B)
                          else if tt2N = 0\<^sub>B
                          then Dpt vvN (Dpt (enat (entry ?N 1 jpN)) (Dpt (enat ?bvN) 0\<^sub>B))
                          else Dpt vvN (tt3N +\<^sub>B Dpt (enat (entry ?N 1 jpN))
                                             (tt4N +\<^sub>B Dpt (enat ?bvN) 0\<^sub>B)))"
  have t1neN: "Trans (Pred ?N) \<noteq> 0\<^sub>B" using T1N by (simp add: transT1_def)
  have transJ0Neq: "transJ0 ?N = jpN" by (simp add: transJ0_def transJ1_def jpN_def)
  have c1NeqT: "c1N = transC1 ?N"
  proof -
    have step1: "transC1 ?N = Mark (Pred ?N) (Adm ?N (transJ0 ?N))"
      unfolding transC1_def transJm1_def by (rule refl)
    have step2: "Adm ?N (transJ0 ?N) = Adm ?N jpN"
      by (rule arg_cong[where f="Adm ?N", OF transJ0Neq])
    have "transC1 ?N = Mark (Pred ?N) (Adm ?N jpN)"
      by (rule trans[OF step1 arg_cong[where f="Mark (Pred ?N)", OF step2]])
    thus ?thesis unfolding c1N_def by (rule sym)
  qed
  have c2NeqT: "c2N = transC2 ?N"
    unfolding c2N_def transC2_def Let_def
      vvN_def tt2N_def c1NeqT transV_def transT2_def
      JJ1N_def pjN_def ldjN_def tt3N_def tt4N_def transJ1_def transJ0Neq
    by simp
  define sbN where
    "sbN = (SOME sb. scb_decomp (Trans (Pred ?N)) (fst sb) (flatBT c1N) (snd sb))"
  have trans_valN: "Trans ?N = unflatBT (fst sbN @ flatBT c2N @ snd sbN)"
    using Trans.psimps[OF domTN] NR LNgt1 monoN t1neN
    unfolding Let_def jpN_def[symmetric] c1N_def[symmetric] vvN_def[symmetric]
              tt2N_def[symmetric] JJ1N_def[symmetric] pjN_def[symmetric]
              ldjN_def[symmetric] tt3N_def[symmetric] tt4N_def[symmetric]
              c2N_def[symmetric] sbN_def[symmetric]
    by simp
  \<comment> \<open>=== unify the two splices ===\<close>
  have c1c1N: "c1 = c1N" using c1eqT c1NeqT id2 by simp
  have c2c2N: "c2 = c2N" using c2eqT c2NeqT id3 by simp
  have smsbN: "sm = sbN"
    unfolding sm_def sbN_def using id1 c1c1N by simp
  have "Mark M m = unflatBT (fst sm @ flatBT c2 @ snd sm)" by (rule mark_val)
  also have "\<dots> = unflatBT (fst sbN @ flatBT c2N @ snd sbN)"
    using smsbN c2c2N by simp
  also have "\<dots> = Trans ?N" using trans_valN by simp
  also have "\<dots> = Trans ?S"
    by (rule Trans_slice_eq_Red[OF MR mj1 j1le leM, symmetric])
  finally show ?thesis .
qed

end

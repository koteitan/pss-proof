theory Support_7_020
  imports P_7_3_Mark_rightmost1
begin

section \<open>§7.3 命題（右端第2基点の \<open>Mark\<close> の基本性質）— content.md 2334\<close>

text \<open>At the second basepoint \<open>m = j\<^sub>-\<^sub>1 = transJm1 M = Adm M (transJ0 M)\<close>, the
  marked value equals \<open>c\<^sub>2 = transC2 M\<close>.  This is the surgery (\<open>m < j\<^sub>1\<close>) branch of
  @{thm [source] Mark.psimps} (domain from @{thm [source] m_7_3_Mark_welldef}) in
  the mono, \<open>t\<^sub>1 \<noteq> 0\<close> case, but at the basepoint \<open>m = j\<^sub>-\<^sub>1\<close> the replaced
  component \<open>c\<^sub>0 = Mark (Pred M) m\<close> coincides with the \<open>c\<^sub>1\<close> being matched, so the
  scb-decomposition is the trivial self-decomposition \<open>([],[])\<close>
  (@{thm [source] scb_SOME_self}, uniqueness @{thm [source] m_7_2_scb_unique_sb}),
  and the surgery delivers \<open>c\<^sub>2\<close> verbatim.\<close>

lemma m_7_3_Mark_rightmost2:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
  shows "Mark M (transJm1 M) = transC2 M"
proof -
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using J1pos by (simp add: transJ1_def)
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B" using T1 by (simp add: transT1_def)
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  let ?j1 = "Lng M - 1"
  let ?bv = "entry M 1 (Lng M - 1)"
  define jp where "jp = parent M 0 (Lng M - 1)"
  define jm1 where "jm1 = Adm M jp"
  define m where "m = transJm1 M"
  have transJ0eq: "transJ0 M = jp" by (simp add: transJ0_def transJ1_def jp_def)
  have meq: "m = jm1" by (simp add: m_def transJm1_def jm1_def transJ0eq)
  \<comment> \<open>the surgery define-chain, mirroring @{thm [source] Mark_flatIdx_bound}\<close>
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
  \<comment> \<open>\<open>c\<^sub>1 = transC1 M\<close>, \<open>c\<^sub>2 = transC2 M\<close>\<close>
  have c1eqT: "c1 = transC1 M"
    by (simp add: c1_def transC1_def transJm1_def transJ0eq)
  have c2eqT: "c2 = transC2 M"
    unfolding c2_def transC2_def Let_def
      vv_def tt2_def c1eqT transV_def transT2_def
      JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
    by simp
  \<comment> \<open>at the basepoint, \<open>c\<^sub>0 = Mark (Pred M) m\<close> is exactly \<open>c\<^sub>1\<close>\<close>
  have c1eq: "c1 = Mark (Pred M) m" by (simp add: c1_def meq jm1_def)
  \<comment> \<open>\<open>c\<^sub>1\<close> is a single principal term\<close>
  have pc1: "Lng (PB (transC1 M)) = 1"
    by (rule transC1_single_principal[OF MR MP J1pos T1])
  have c1Dpt: "transC1 M = Dpt (transV M) (transT2 M)"
    using principal_reconstruct[OF pc1]
    by (simp add: transV_def transT2_def)
  have mkjm1: "(Pred M, jm1) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp] jp_def jm1_def by simp
  have c1TB: "transC1 M \<in> T_B"
    using m_7_3_Mark_in_T_B[OF predRT mkjm1] c1eq c1eqT meq by simp
  have vne: "transV M \<noteq> \<infinity>" using c1TB c1Dpt by (auto simp: T_B_def)
  have t2df: "dfree_BT (transT2 M)" using c1TB c1Dpt by (auto simp: T_B_def)
  have c1p: "c1 = Trm [DB (transV M) (transT2 M)]"
    using c1eqT c1Dpt by simp
  \<comment> \<open>\<open>c\<^sub>1\<close> is its own scb-self-decomposition, hence \<open>(c\<^sub>1, c\<^sub>1) \<in> MarkedB\<close>\<close>
  have iptc1: "isPTB_str (flatBT c1)"
  proof -
    have "dfree_BP (DB (transV M) (transT2 M))" using vne t2df by simp
    moreover have "flatBT c1 = flatBP (DB (transV M) (transT2 M))" using c1p by simp
    ultimately show ?thesis unfolding isPTB_str_def by blast
  qed
  have c1ne: "c1 \<noteq> Trm []" using c1p by simp
  have mbc: "(c1, c1) \<in> MarkedB"
    using scb_decomp_self[OF iptc1] unfolding MarkedB_def by auto
  \<comment> \<open>positions: \<open>m = jm1 \<le> jp < j\<^sub>1\<close>, hence \<open>m < j\<^sub>1\<close>\<close>
  have jplt: "jp < ?j1"
  proof -
    have "nextR M 0 jp ?j1"
      using hp unfolding hasParent_def parent_def jp_def by (rule theI')
    thus ?thesis by (simp add: nextR_def nextrel0_def)
  qed
  have mlt: "m < ?j1"
  proof -
    have "m \<le> jp" using adm_Adm_le meq jm1_def by simp
    thus ?thesis using jplt by linarith
  qed
  \<comment> \<open>evaluate the surgery branch of \<open>Mark M m\<close>\<close>
  define sm1 where
    "sm1 = (SOME sb. scb_decomp c1 (fst sb) (flatBT c1) (snd sb))"
  have mark_val_raw: "Mark M m = (if (Mark (Pred M) m, c1) \<in> MarkedB
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
  have mark_val: "Mark M m = unflatBT (fst sm1 @ flatBT c2 @ snd sm1)"
    using mark_val_raw mbc c1eq[symmetric] by (simp add: sm1_def)
  \<comment> \<open>the scb-self-decomposition is the unique witness \<open>([],[])\<close>\<close>
  have sm1eq: "sm1 = ([], [])"
    unfolding sm1_def by (rule scb_SOME_self[OF iptc1 c1ne])
  have "Mark M m = unflatBT (flatBT c2)" using mark_val sm1eq by simp
  also have "\<dots> = c2" by (rule unflatBT_flat)
  also have "\<dots> = transC2 M" by (rule c2eqT)
  finally show ?thesis using m_def by simp
qed

end

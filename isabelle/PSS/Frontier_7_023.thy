theory Frontier_7_023
  imports Support_7_019
begin

section \<open>§7.3 系（\<open>Mark\<close> の左端の基本性質）— content.md 2310\<close>

text \<open>\<open>Mark N m\<close> is either \<open>0\<close> or a single principal \<open>D\<^bsub>N\<^sub>1\<^sub>,\<^sub>m\<^esub>(\<dots>)\<close> whose
  left index is exactly \<open>entry N 1 m\<close>.  Empirically verified
  (\<open>bpHeadV (Mark N m) = entry N 1 m\<close> over 9699 marked cases, 0 failures).
  Strong \<open>Lng\<close>-induction, mirroring @{thm [source] Mark_rightmost1_forward} and
  the surgery of @{thm [source] Mark_flatIdx_bound}.\<close>

text \<open>Head-symbol bridge: the first symbol of \<open>flatBT (Trm [DB v t])\<close> is
  \<open>Dsym v\<close>, so a single principal term's leading flat symbol fixes its
  \<open>bpHeadV\<close>.\<close>

lemma flatBT_principal_head:
  "flatBT (Trm [DB v t]) = Dsym v # flatBT t"
  by simp

text \<open>The mono, \<open>t\<^sub>1 \<noteq> 0\<close> (surgery) branch of the marked nesting, taking the
  \<open>Pred M\<close> induction hypothesis as an assumption.  Both \<open>Mark M m\<close> and
  \<open>Mark M m'\<close> are the same principal \<open>c\<^sub>2\<close>-replacement performed inside
  \<open>Mark (Pred M) m\<close> resp. \<open>Mark (Pred M) m'\<close>; since the latter two nest (IH),
  the former two nest by \<open>scb\<close>-composition (@{thm [source] m_7_2_scb_compose},
  @{thm [source] m_7_2_scb_unique_sb}).  The \<open>m' = j\<^sub>1\<close> end is handled by the
  rightmost block \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<close> of \<open>c\<^sub>2\<close>.\<close>

lemma Mark_MarkedB_nest_surgery:
  assumes MR: "M \<in> RT_PS" and mono: "monoT M" and L: "1 < Lng M"
    and t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B"
    and mM: "(M, m) \<in> Marked" and mM': "(M, m') \<in> Marked" and mle: "m \<le> m'"
    and IHpred: "\<And>a b. (Pred M, a) \<in> Marked \<Longrightarrow> (Pred M, b) \<in> Marked
                 \<Longrightarrow> a \<le> b \<Longrightarrow> (Mark (Pred M) a, Mark (Pred M) b) \<in> MarkedB"
  shows "(Mark M m, Mark M m') \<in> MarkedB"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  have leM: "leR M 0 m (Lng M - 1)" using mM by (simp add: Marked_def)
  have mleN: "m < Lng M" using leM by (simp add: leR_def le0_def)
  have mle1: "m \<le> Lng M - 1" using mleN by linarith
  have leM': "leR M 0 m' (Lng M - 1)" using mM' by (simp add: Marked_def)
  have m'leN: "m' < Lng M" using leM' by (simp add: leR_def le0_def)
  have m'le1: "m' \<le> Lng M - 1" using m'leN by linarith
  have admN: "adm M m" using mM by (simp add: Marked_def)
  have admN': "adm M m'" using mM' by (simp add: Marked_def)
  have selfMB_bv: "(Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B,
                    Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B) \<in> MarkedB"
  proof -
    have "scb_decomp (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B) []
            (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) []"
      by (rule scb_decomp_self) (rule isPTB_str_Dpt, simp_all)
    thus ?thesis unfolding MarkedB_def by auto
  qed
  let ?t1 = "Trans (Pred M)"
  let ?bv = "entry M 1 (Lng M - 1)"
  let ?j1 = "Lng M - 1"
  define jp where "jp = parent M 0 (Lng M - 1)"
  define jm1 where "jm1 = Adm M jp"
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
  \<comment> \<open>induction facts for \<open>c\<^sub>1\<close>\<close>
  have mkdA: "(Pred M, Adm M jp) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp] jp_def by simp
  have mb1: "(?t1, c1) \<in> MarkedB"
    using m_7_3_Trans_Mark_MarkedB[OF predRT mkdA] c1_def by simp
  have t1neT: "?t1 \<noteq> Trm []" using t1ne by simp
  define sb1 where "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
  have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
    using mb1 unfolding MarkedB_def by auto
  have dsome: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
    unfolding sb1_def by (rule someI_ex[OF exsb])
  have iptc1: "isPTB_str (flatBT c1)"
    using dsome t1neT by (simp add: scb_decomp_def)
  then obtain pc where pcf: "dfree_BP pc" and pcl: "flatBT c1 = flatBP pc"
    by (auto simp: isPTB_str_def)
  have c1p: "c1 = Trm [pc]"
  proof -
    have "flatBT c1 = flatBT (Trm [pc])" using pcl by simp
    thus ?thesis by (rule m_7_flatBT_inj)
  qed
  obtain wv tb where pcw: "pc = DB wv tb" by (cases pc) auto
  have vvv: "vv = wv" using vv_def c1p pcw by simp
  have tt2v: "tt2 = tb" using tt2_def c1p pcw by simp
  have wvne: "wv \<noteq> \<infinity>" and tbdf: "dfree_BT tb" using pcf pcw by auto
  \<comment> \<open>\<open>c\<^sub>2\<close> is a principal dfree term whose rightmost block is \<open>D\<^bsub>?bv\<^esub> 0\<close>\<close>
  have c2shape: "\<exists>X. c2 = Dpt vv X \<and> dfree_BT X \<and> (X, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
  proof -
    have selfb: "(Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
    proof -
      have "scb_decomp (Dpt (enat ?bv) 0\<^sub>B) [] (flatBT (Dpt (enat ?bv) 0\<^sub>B)) []"
        by (rule scb_decomp_self) (rule isPTB_str_Dpt, simp_all)
      thus ?thesis unfolding MarkedB_def by auto
    qed
    have iptb: "isPTB_str (flatBT (Dpt (enat ?bv) 0\<^sub>B))"
      by (rule isPTB_str_Dpt) simp_all
    have dbne: "Dpt (enat ?bv) 0\<^sub>B \<noteq> 0\<^sub>B" by simp
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
      have mb: "(tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF selfb dbne])
      show ?thesis using x df mb by blast
    next
      case VI
      have x: "c2 = Dpt vv (Dpt (enat ?bv) 0\<^sub>B)" using VI c2_def by simp
      have mb: "(Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB" by (rule selfb)
      show ?thesis using x mb by auto
    next
      case Z
      have x: "c2 = Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))"
        using Z c2_def by simp
      have mb: "(Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B),
                 Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_Dpt_lift[OF selfb iptb])
      show ?thesis using x mb by auto
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
      have mbin: "(tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF selfb dbne])
      have mbmid: "(Dpt (enat (entry M 1 jp)) (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B),
                    Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_Dpt_lift[OF mbin iptb])
      have mbout: "(tt3 +\<^sub>B Dpt (enat (entry M 1 jp)) (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B),
                    Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF mbmid]) simp
      have dfall: "dfree_BT (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                    (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B))"
        using df3 dfsum by (cases tt3) auto
      show ?thesis using x mbout dfall by blast
    qed
  qed
  obtain X2 where c2X: "c2 = Dpt vv X2" and X2df: "dfree_BT X2"
      and X2mb: "(X2, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
    using c2shape by blast
  have c2df: "dfree_BT c2" using c2X X2df wvne vvv by simp
  have iptc2: "isPTB_str (flatBT c2)"
    using c2X by (intro isPTB_str_Dpt[of vv X2, folded c2X])
                 (use wvne vvv X2df in simp_all)
  obtain pc2 where c2p: "c2 = Trm [pc2]" using c2X by auto
  have c2mb: "(c2, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
  proof -
    have iptb: "isPTB_str (flatBT (Dpt (enat ?bv) 0\<^sub>B))"
      by (rule isPTB_str_Dpt) simp_all
    show ?thesis using MarkedB_Dpt_lift[OF X2mb iptb] c2X by simp
  qed
  \<comment> \<open>generic evaluation of a surgery \<open>Mark M k\<close> for \<open>k < j\<^sub>1\<close>\<close>
  have mark_surg: "\<And>k. k < ?j1 \<Longrightarrow> (Mark (Pred M) k, c1) \<in> MarkedB
      \<Longrightarrow> Mark M k = unflatBT
            (fst (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb))
             @ flatBT c2
             @ snd (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb)))"
  proof -
    fix k assume klt: "k < ?j1" and kmb: "(Mark (Pred M) k, c1) \<in> MarkedB"
    have "Mark M k = (if (Mark (Pred M) k, c1) \<in> MarkedB
          then unflatBT
                 (fst (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb))
                  @ flatBT c2
                  @ snd (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb)))
          else Dpt (enat ?bv) 0\<^sub>B)"
      using Mark.psimps[OF domK] MR Lgt1 mono t1ne klt
      unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                c2_def[symmetric]
      by simp
    thus "Mark M k = unflatBT
            (fst (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb))
             @ flatBT c2
             @ snd (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb)))"
      using kmb by simp
  qed
  \<comment> \<open>evaluation of \<open>Mark M j\<^sub>1 = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<close>\<close>
  have mark_last: "Mark M ?j1 = Dpt (enat ?bv) 0\<^sub>B"
    using Mark.psimps[OF domK] MR Lgt1 mono t1ne
    unfolding Let_def jp_def[symmetric]
    by simp
  \<comment> \<open>marked-block / principality of a surgery value at \<open>k < j\<^sub>1\<close>\<close>
  have surg_facts: "\<And>k. (M, k) \<in> Marked \<Longrightarrow> k < ?j1 \<Longrightarrow>
        (Mark (Pred M) k, c1) \<in> MarkedB
      \<and> (\<exists>sm. scb_decomp (Mark (Pred M) k) (fst sm) (flatBT c1) (snd sm)
            \<and> Mark M k = unflatBT (fst sm @ flatBT c2 @ snd sm)
            \<and> flatBT (Mark M k) = fst sm @ flatBT c2 @ snd sm
            \<and> isPTB_str (flatBT (Mark M k))
            \<and> Mark M k \<noteq> Trm []
            \<and> scb_decomp (Mark M k) (fst sm) (flatBT c2) (snd sm))"
  proof -
    fix k assume mMk: "(M, k) \<in> Marked" and klt: "k < ?j1"
    have mPk: "(Pred M, k) \<in> Marked" by (rule Marked_Pred[OF MT L mMk klt])
    \<comment> \<open>\<open>k \<le> jm1 = Adm M jp\<close>, so \<open>c\<^sub>1 = Mark (Pred M) jm1\<close> nests in \<open>Mark (Pred M) k\<close>\<close>
    have admMk: "adm M k" using mMk by (simp add: Marked_def)
    have kjp: "k \<le> jp" using surg_parent_ge[OF mMk mono L klt] jp_def by simp
    have kjm1: "k \<le> Adm M jp" using surg_adm_ge[OF admMk kjp] by simp
    have mbk: "(Mark (Pred M) k, c1) \<in> MarkedB"
      using IHpred[OF mPk mkdA kjm1] c1_def by simp
    define sm where "sm = (SOME sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb))"
    have exsm: "\<exists>sb. scb_decomp (Mark (Pred M) k) (fst sb) (flatBT c1) (snd sb)"
      using mbk unfolding MarkedB_def by auto
    have dsm: "scb_decomp (Mark (Pred M) k) (fst sm) (flatBT c1) (snd sm)"
      unfolding sm_def by (rule someI_ex[OF exsm])
    \<comment> \<open>\<open>Mark (Pred M) k\<close> is a principal term (block of nonzero \<open>Trans (Pred M)\<close>)\<close>
    have mb0: "(?t1, Mark (Pred M) k) \<in> MarkedB"
      by (rule m_7_3_Trans_Mark_MarkedB[OF predRT mPk])
    obtain s0 b0 where d0: "scb_decomp ?t1 s0 (flatBT (Mark (Pred M) k)) b0"
      using mb0 by (auto simp: MarkedB_def)
    have iptc0: "isPTB_str (flatBT (Mark (Pred M) k))"
      using d0 t1neT by (simp add: scb_decomp_def)
    then obtain pc0 where pc0l: "flatBT (Mark (Pred M) k) = flatBP pc0"
      by (auto simp: isPTB_str_def)
    have c0p: "Mark (Pred M) k = Trm [pc0]"
    proof -
      have "flatBT (Mark (Pred M) k) = flatBT (Trm [pc0])" using pc0l by simp
      thus ?thesis by (rule m_7_flatBT_inj)
    qed
    have dsm': "scb_decomp (Trm [pc0]) (fst sm) (flatBT (Trm [pc])) (snd sm)"
      using dsm c0p c1p by simp
    obtain pm where pmf: "flatBP pm = fst sm @ flatBT (Trm [pc2]) @ snd sm"
        and pmd: "scb_decomp (Trm [pm]) (fst sm) (flatBT (Trm [pc2])) (snd sm)"
      using scb_replace_principal_BP[OF dsm' iptc2[unfolded c2p]] by blast
    have markk: "Mark M k = Trm [pm]"
    proof -
      have ev: "Mark M k = unflatBT (fst sm @ flatBT c2 @ snd sm)"
        using mark_surg[OF klt mbk] sm_def by simp
      have "flatBT (Trm [pm]) = fst sm @ flatBT c2 @ snd sm" using pmf c2p by simp
      thus ?thesis using ev unflatBT_flat[of "Trm [pm]"] by simp
    qed
    have flatk: "flatBT (Mark M k) = fst sm @ flatBT c2 @ snd sm"
      using markk pmf c2p by simp
    have brp: "\<forall>x \<in> set (snd sm). x = RP" using dsm by (simp add: scb_decomp_def)
    \<comment> \<open>\<open>Mark (Pred M) k\<close> is \<open>D\<^sub>\<omega>\<close>-free, so its sub-strings are; together with \<open>c\<^sub>2\<close>\<close>
    have c0df: "dfree_BT (Mark (Pred M) k)"
      using m_7_3_Mark_in_T_B[OF predRT mPk] by (simp add: T_B_def)
    have sm_sub: "set (fst sm) \<subseteq> set (flatBT (Mark (Pred M) k))"
        and bm_sub: "set (snd sm) \<subseteq> set (flatBT (Mark (Pred M) k))"
      using dsm by (auto simp: scb_decomp_def)
    have iptk: "isPTB_str (flatBT (Mark M k))"
    proof -
      have "dfree_BT (Trm [pm])"
      proof -
        have "\<And>v'. Dsym v' \<in> set (flatBT (Trm [pm])) \<Longrightarrow> v' \<noteq> \<infinity>"
        proof -
          fix v' assume "Dsym v' \<in> set (flatBT (Trm [pm]))"
          hence "Dsym v' \<in> set (flatBT (Mark (Pred M) k)) \<or> Dsym v' \<in> set (flatBT c2)"
            using pmf c2p sm_sub bm_sub by auto
          thus "v' \<noteq> \<infinity>" using c0df c2df dfree_flat_BT by blast
        qed
        thus ?thesis using dfree_flat_BT by blast
      qed
      thus ?thesis using markk by (auto simp: isPTB_str_def)
    qed
    have knz: "Mark M k \<noteq> Trm []" using markk by simp
    have sdk: "scb_decomp (Mark M k) (fst sm) (flatBT c2) (snd sm)"
      unfolding scb_decomp_def using flatk iptc2 brp by simp
    show "(Mark (Pred M) k, c1) \<in> MarkedB
      \<and> (\<exists>sm. scb_decomp (Mark (Pred M) k) (fst sm) (flatBT c1) (snd sm)
            \<and> Mark M k = unflatBT (fst sm @ flatBT c2 @ snd sm)
            \<and> flatBT (Mark M k) = fst sm @ flatBT c2 @ snd sm
            \<and> isPTB_str (flatBT (Mark M k))
            \<and> Mark M k \<noteq> Trm []
            \<and> scb_decomp (Mark M k) (fst sm) (flatBT c2) (snd sm))"
      using mbk dsm markk[symmetric] flatk iptk knz sdk mark_surg[OF klt mbk] sm_def
      by (intro conjI exI[of _ sm]) (simp_all)
  qed
  \<comment> \<open>the two cases on \<open>m'\<close>\<close>
  show ?thesis
  proof (cases "m' < ?j1")
    case m'lt: True
    have mlt: "m < ?j1" using mle m'lt by simp
    have mPm: "(Pred M, m) \<in> Marked" by (rule Marked_Pred[OF MT L mM mlt])
    have mPm': "(Pred M, m') \<in> Marked" by (rule Marked_Pred[OF MT L mM' m'lt])
    \<comment> \<open>surgery facts at \<open>m\<close> and \<open>m'\<close>\<close>
    from surg_facts[OF mM mlt] obtain sm where
        dsm: "scb_decomp (Mark (Pred M) m) (fst sm) (flatBT c1) (snd sm)"
      and flatm: "flatBT (Mark M m) = fst sm @ flatBT c2 @ snd sm"
      and iptm: "isPTB_str (flatBT (Mark M m))"
      and mnz: "Mark M m \<noteq> Trm []" by blast
    from surg_facts[OF mM' m'lt] obtain sm' where
        dsm': "scb_decomp (Mark (Pred M) m') (fst sm') (flatBT c1) (snd sm')"
      and flatm': "flatBT (Mark M m') = fst sm' @ flatBT c2 @ snd sm'"
      and iptm': "isPTB_str (flatBT (Mark M m'))" by blast
    \<comment> \<open>IH: \<open>Mark (Pred M) m'\<close> nests in \<open>Mark (Pred M) m\<close>\<close>
    have nestpred: "(Mark (Pred M) m, Mark (Pred M) m') \<in> MarkedB"
      by (rule IHpred[OF mPm mPm' mle])
    obtain sA bA where dA: "scb_decomp (Mark (Pred M) m) sA (flatBT (Mark (Pred M) m')) bA"
      using nestpred by (auto simp: MarkedB_def)
    \<comment> \<open>\<open>Mark (Pred M) m'\<close> is principal\<close>
    have mb0': "(?t1, Mark (Pred M) m') \<in> MarkedB"
      by (rule m_7_3_Trans_Mark_MarkedB[OF predRT mPm'])
    obtain s0' b0' where d0': "scb_decomp ?t1 s0' (flatBT (Mark (Pred M) m')) b0'"
      using mb0' by (auto simp: MarkedB_def)
    have iptc0': "isPTB_str (flatBT (Mark (Pred M) m'))"
      using d0' t1neT by (simp add: scb_decomp_def)
    then obtain pc0' where pc0l': "flatBT (Mark (Pred M) m') = flatBP pc0'"
      by (auto simp: isPTB_str_def)
    have c0p': "Mark (Pred M) m' = Trm [pc0']"
    proof -
      have "flatBT (Mark (Pred M) m') = flatBT (Trm [pc0'])" using pc0l' by simp
      thus ?thesis by (rule m_7_flatBT_inj)
    qed
    \<comment> \<open>compose: the \<open>flatBT c\<^sub>1\<close> occurrence inside \<open>Mark (Pred M) m\<close> via \<open>m'\<close> equals \<open>(sm, ...)\<close>\<close>
    have comp: "scb_decomp (Mark (Pred M) m) (sA @ fst sm') (flatBT c1) (snd sm' @ bA)"
      by (rule m_7_2_scb_compose[OF _ dA dsm'])
         (use c0p' in auto)
    have mPredne: "Mark (Pred M) m \<noteq> Trm []"
    proof
      assume z: "Mark (Pred M) m = Trm []"
      have "flatBT (Mark (Pred M) m) = fst sm @ flatBT c1 @ snd sm"
        using dsm by (simp add: scb_decomp_def)
      hence "Dsym wv \<in> set (flatBT (Mark (Pred M) m))"
        using c1p pcw by simp
      thus False using z by simp
    qed
    have coh: "fst sm = sA @ fst sm' \<and> snd sm = snd sm' @ bA"
      by (rule m_7_2_scb_unique_sb[OF dsm comp mPredne])
    \<comment> \<open>hence \<open>flatBT (Mark M m) = sA @ flatBT (Mark M m') @ bA\<close>\<close>
    have flatComp: "flatBT (Mark M m) = sA @ flatBT (Mark M m') @ bA"
      using flatm flatm' coh by simp
    have bArp: "\<forall>x \<in> set bA. x = RP" using dA by (simp add: scb_decomp_def)
    have "scb_decomp (Mark M m) sA (flatBT (Mark M m')) bA"
      unfolding scb_decomp_def using flatComp iptm' bArp by simp
    thus ?thesis unfolding MarkedB_def by auto
  next
    case m'lt_false: False
    have m'j1: "m' = ?j1" using m'lt_false m'le1 by simp
    have markm': "Mark M m' = Dpt (enat ?bv) 0\<^sub>B" using mark_last m'j1 by simp
    show ?thesis
    proof (cases "m < ?j1")
      case mlt: True
      from surg_facts[OF mM mlt] obtain sm where
          flatm: "flatBT (Mark M m) = fst sm @ flatBT c2 @ snd sm"
        and iptm: "isPTB_str (flatBT (Mark M m))"
        and mnz: "Mark M m \<noteq> Trm []"
        and sdk: "scb_decomp (Mark M m) (fst sm) (flatBT c2) (snd sm)" by blast
      \<comment> \<open>\<open>(Mark M m, c\<^sub>2) \<in> MarkedB\<close>, and \<open>(c\<^sub>2, D\<^bsub>?bv\<^esub> 0) \<in> MarkedB\<close>; compose\<close>
      obtain s2 b2 where d2: "scb_decomp c2 s2 (flatBT (Dpt (enat ?bv) 0\<^sub>B)) b2"
        using c2mb by (auto simp: MarkedB_def)
      have comp: "scb_decomp (Mark M m) (fst sm @ s2) (flatBT (Dpt (enat ?bv) 0\<^sub>B)) (b2 @ snd sm)"
        by (rule m_7_2_scb_compose[OF _ sdk d2]) (use c2p in auto)
      hence "(Mark M m, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB" unfolding MarkedB_def by auto
      thus ?thesis using markm' by simp
    next
      case mlt_false: False
      have mj1: "m = ?j1" using mlt_false mle1 by simp
      have "Mark M m = Dpt (enat ?bv) 0\<^sub>B" using mark_last mj1 by simp
      hence "Mark M m = Mark M m'" using markm' by simp
      moreover have "(Mark M m', Mark M m') \<in> MarkedB"
        using markm' selfMB_bv by simp
      ultimately show ?thesis by simp
    qed
  qed
qed

text \<open>Marked nesting: for a reduced \<open>M\<close> and two marked columns \<open>m \<le> m'\<close>, the
  marked image at the later column nests in the one at the earlier column,
  \<open>(Mark M m, Mark M m') \<in> MarkedB\<close>.  Empirically 0/770 failures.  This is the
  structural fact that makes the \<open>(c\<^sub>0,c\<^sub>1) \<notin> MarkedB\<close> default of the \<open>Mark\<close>
  surgery unreachable.\<close>

lemma Mark_MarkedB_nest:
  "(M, m) \<in> Marked \<longrightarrow> (M, m') \<in> Marked \<longrightarrow> m \<le> m' \<longrightarrow> M \<in> RT_PS
   \<longrightarrow> (Mark M m, Mark M m') \<in> MarkedB"
proof (induction M arbitrary: m m' rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (intro impI)
    assume mM: "(M, m) \<in> Marked" and mM': "(M, m') \<in> Marked"
      and mle: "m \<le> m'" and MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
    have leM': "leR M 0 m' (Lng M - 1)" using mM' by (simp add: Marked_def)
    have m'leN: "m' < Lng M" using leM' by (simp add: leR_def le0_def)
    have m'le: "m' \<le> Lng M - 1" using m'leN by linarith
    have mleN: "m < Lng M" using mle m'leN by linarith
    let ?j1 = "Lng M - 1"
    \<comment> \<open>reflexive \<open>MarkedB\<close> for a single principal value\<close>
    have selfMB: "\<And>c. isPTB_str (flatBT c) \<Longrightarrow> (c, c) \<in> MarkedB"
    proof -
      fix c assume "isPTB_str (flatBT c)"
      hence "scb_decomp c [] (flatBT c) []" by (rule scb_decomp_self)
      thus "(c, c) \<in> MarkedB" unfolding MarkedB_def by auto
    qed
    have selfMB0: "(0\<^sub>B, 0\<^sub>B) \<in> MarkedB"
    proof -
      have "scb_decomp 0\<^sub>B [] (flatBT (0\<^sub>B::BT)) []" by (simp add: scb_decomp_def)
      thus ?thesis unfolding MarkedB_def by auto
    qed
    show "(Mark M m, Mark M m') \<in> MarkedB"
    proof (cases "Lng M = 1")
      case True
      \<comment> \<open>(A) length 1: \<open>m = m' = 0\<close>, so reflexive\<close>
      have "m = m'" using mle m'le True by simp
      then obtain v where Mv: "M = [(v, v)]"
        using m_6_6_oneColumn[OF MT] MR True by auto
      have kv: "Mark M m = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Mv Mark_singleton by simp
      show ?thesis
      proof (cases "v = 0")
        case True
        have "Mark M m = 0\<^sub>B" using kv True by simp
        thus ?thesis using \<open>m = m'\<close> selfMB0 by simp
      next
        case False
        have mk: "Mark M m = Dpt (enat v) 0\<^sub>B" using kv False by simp
        have ipt: "isPTB_str (flatBT (Dpt (enat v) 0\<^sub>B))"
          by (rule isPTB_str_Dpt) simp_all
        show ?thesis using mk \<open>m = m'\<close> selfMB[OF ipt] by simp
      qed
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      have j1pos: "0 < ?j1" using L by simp
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
        have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
        have LPred: "Lng (Pred M) = Lng M - 1" using predb by simp
        have LPredlt: "Lng (Pred M) < Lng M" using LPred L by simp
        show ?thesis
        proof (cases "Trans (Pred M) = 0\<^sub>B")
          case t1z: True
          \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>: \<open>Lng M = 2\<close>, \<open>m,m' \<in> {0,1}\<close>\<close>
          have zP: "zeroT (Pred M)" using m_7_3_Trans_zeroT[OF predRT] t1z by simp
          have LP1: "Lng (Pred M) = 1" using zP by (simp add: zeroT_def)
          have L2: "Lng M = 2" using LP1 LPred L by linarith
          have kv: "\<And>k. Mark M k = (if k = 0 then Dpt 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)
                                      else Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
            using Mark.psimps[OF domK] MR Lgt1 mono t1z by (simp add: Let_def)
          let ?Dj = "Dpt (enat (entry M 1 ?j1)) 0\<^sub>B"
          have iptDj: "isPTB_str (flatBT ?Dj)" by (rule isPTB_str_Dpt) simp_all
          show ?thesis
          proof (cases "m' = 0")
            case True
            hence m0: "m = 0" using mle by simp
            have iptD0: "isPTB_str (flatBT (Dpt 0 (?Dj)))"
              by (rule isPTB_str_Dpt) (simp_all add: zero_enat_def)
            have "Mark M m = Dpt 0 (?Dj)" using kv m0 by simp
            moreover have "Mark M m' = Dpt 0 (?Dj)" using kv True by simp
            ultimately show ?thesis using selfMB[OF iptD0] by simp
          next
            case m'ne: False
            have mk': "Mark M m' = ?Dj" using kv m'ne by simp
            show ?thesis
            proof (cases "m = 0")
              case True
              have mk: "Mark M m = Dpt 0 (?Dj)" using kv True by simp
              \<comment> \<open>\<open>?Dj\<close> nests in \<open>Dpt 0 ?Dj\<close> (drop the head \<open>Dsym 0\<close>)\<close>
              have "scb_decomp (Dpt 0 ?Dj) [Dsym 0] (flatBT ?Dj) []"
                using iptDj by (simp add: scb_decomp_def)
              hence "(Dpt 0 ?Dj, ?Dj) \<in> MarkedB" unfolding MarkedB_def by auto
              thus ?thesis using mk mk' by simp
            next
              case False
              have mk: "Mark M m = ?Dj" using kv False by simp
              show ?thesis using mk mk' selfMB[OF iptDj] by simp
            qed
          qed
        next
          case t1ne: False
          \<comment> \<open>(B) \<open>t\<^sub>1 \<noteq> 0\<close> surgery; deferred to a dedicated argument\<close>
          have IHpred: "\<And>a b. (Pred M, a) \<in> Marked \<Longrightarrow> (Pred M, b) \<in> Marked
                 \<Longrightarrow> a \<le> b \<Longrightarrow> (Mark (Pred M) a, Mark (Pred M) b) \<in> MarkedB"
            using less.IH[OF LPredlt] predRT by blast
          show ?thesis
            by (rule Mark_MarkedB_nest_surgery[OF MR mono L t1ne mM mM' mle IHpred])
        qed
      next
        case nmono: False
        \<comment> \<open>(C) multiT branch: both reduce to the same last \<open>P\<close>-component \<open>PJ\<close>\<close>
        have nzM: "\<not> zeroT M" using notone by (auto simp: zeroT_def)
        have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
        have cut: "0 < Pcut M \<and> Pcut M \<le> ?j1" using Pcut_le[OF L] by simp
        let ?PJ = "drop (Pcut M) M"
        have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF MT muM])
        have Pne: "P M \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
        have PJRT: "?PJ \<in> RT_PS"
          using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
        have LPJ: "Lng ?PJ = Lng M - Pcut M" by simp
        have LPJlt: "Lng ?PJ < Lng M" using LPJ cut L by linarith
        have cmle: "Pcut M \<le> m" by (rule multi_Marked_last_component(1)[OF MT muM mM])
        have cmle': "Pcut M \<le> m'" by (rule multi_Marked_last_component(1)[OF MT muM mM'])
        have c1: "(M \<notin> RT_PS) = False" using MR by simp
        have c2: "(?j1 = 0) = False" using L by simp
        have c3: "monoT M = False" using nmono by simp
        have meq2: "\<And>k. k - (?j1 - Lng (drop (Pcut M) M) + 1) = k - Pcut M"
        proof -
          fix k
          have "?j1 - Lng ?PJ + 1 = Pcut M" using LPJ cut by linarith
          thus "k - (?j1 - Lng (drop (Pcut M) M) + 1) = k - Pcut M" by simp
        qed
        have markM: "\<And>k. Mark M k = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                                      else Mark ?PJ (k - Pcut M))"
        proof -
          fix k
          have raw: "Mark M k =
              (if P M ! (Lng (P M) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
               else Mark (P M ! (Lng (P M) - 1))
                      (k - (?j1 - Lng (P M ! (Lng (P M) - 1)) + 1)))"
            by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
          show "Mark M k = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B else Mark ?PJ (k - Pcut M))"
            unfolding raw PJeq meq2 ..
        qed
        show ?thesis
        proof (cases "?PJ = [(0, 0)]")
          case True
          have "Mark M m = Dpt 0 0\<^sub>B" and "Mark M m' = Dpt 0 0\<^sub>B"
            using markM True by simp_all
          moreover have "isPTB_str (flatBT (Dpt 0 0\<^sub>B))" by (rule isPTB_str_Dpt) simp_all
          ultimately show ?thesis using selfMB[of "Dpt 0 0\<^sub>B"] by simp
        next
          case False
          have kvm: "Mark M m = Mark ?PJ (m - Pcut M)" using markM False by simp
          have kvm': "Mark M m' = Mark ?PJ (m' - Pcut M)" using markM False by simp
          have mPJ: "(?PJ, m - Pcut M) \<in> Marked"
            by (rule multi_Marked_last_component(2)[OF MT muM mM])
          have mPJ': "(?PJ, m' - Pcut M) \<in> Marked"
            by (rule multi_Marked_last_component(2)[OF MT muM mM'])
          have mlePJ: "m - Pcut M \<le> m' - Pcut M" using mle by simp
          have "(Mark ?PJ (m - Pcut M), Mark ?PJ (m' - Pcut M)) \<in> MarkedB"
            using less.IH[OF LPJlt] mPJ mPJ' mlePJ PJRT by blast
          thus ?thesis using kvm kvm' by simp
        qed
      qed
    qed
  qed
qed

lemma Mark_leftend_form:
  "(N, m) \<in> Marked \<longrightarrow> N \<in> RT_PS
   \<longrightarrow> (Mark N m = 0\<^sub>B \<or> (\<exists>t. Mark N m = Dpt (enat (entry N 1 m)) t))"
proof (induction N arbitrary: m rule: measure_induct_rule[where f=Lng])
  case (less N)
  show ?case
  proof (intro impI)
    assume mM: "(N, m) \<in> Marked" and NR: "N \<in> RT_PS"
    have NT: "N \<in> T_PS" using NR by (simp add: RT_PS_def)
    have Nne: "N \<noteq> []" using NT by (simp add: T_PS_def)
    have domK: "\<And>m. Trans_Mark_dom (Inr (N, m))" by (rule m_7_3_Mark_welldef[OF NR])
    have leM: "leR N 0 m (Lng N - 1)" using mM by (simp add: Marked_def)
    have mleN: "m < Lng N" using leM by (simp add: leR_def le0_def)
    have mle: "m \<le> Lng N - 1" using mleN by linarith
    let ?j1 = "Lng N - 1"
    show "Mark N m = 0\<^sub>B \<or> (\<exists>t. Mark N m = Dpt (enat (entry N 1 m)) t)"
    proof (cases "Lng N = 1")
      case True
      \<comment> \<open>(A) length 1: \<open>N = [(v,v)]\<close>, \<open>m = 0\<close>\<close>
      obtain v where Nv: "N = [(v, v)]"
        using m_6_6_oneColumn[OF NT] NR True by auto
      have m0: "m = 0" using mle True by simp
      have kv: "Mark N m = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Nv Mark_singleton by simp
      have ev: "entry N 1 m = v" using Nv m0 by (simp add: entry_def)
      show ?thesis
      proof (cases "v = 0")
        case True thus ?thesis using kv by simp
      next
        case False
        have "Mark N m = Dpt (enat (entry N 1 m)) 0\<^sub>B" using kv False ev by simp
        thus ?thesis by blast
      qed
    next
      case notone: False
      have L: "1 < Lng N" using Nne notone by (cases N) auto
      have Lgt1: "\<not> Lng N \<le> Suc 0" using L by simp
      have j1pos: "0 < ?j1" using L by simp
      show ?thesis
      proof (cases "monoT N")
        case mono: True
        have predRT: "Pred N \<in> RT_PS" by (rule Pred_RT_PS[OF NR])
        have predb: "Pred N = butlast N" using L by (simp add: Pred_def)
        have LPred: "Lng (Pred N) = Lng N - 1" using predb by simp
        have LPredlt: "Lng (Pred N) < Lng N" using LPred L by simp
        \<comment> \<open>row-1 entries agree on the kept columns\<close>
        have entryP: "\<And>j. j \<le> Lng N - 2 \<Longrightarrow> entry (Pred N) 1 j = entry N 1 j"
        proof -
          fix j assume "j \<le> Lng N - 2"
          hence "j < Lng N - 1" using L by linarith
          hence "j < length (butlast N)" using L by simp
          thus "entry (Pred N) 1 j = entry N 1 j"
            using predb by (simp add: entry_def nth_butlast)
        qed
        show ?thesis
        proof (cases "Trans (Pred N) = 0\<^sub>B")
          case t1z: True
          \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>: here \<open>Pred N = [(0,0)]\<close>, \<open>Lng N = 2\<close>, \<open>m \<in> {0,1}\<close>\<close>
          have kv: "Mark N m = (if m = 0 then Dpt 0 (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)
                                else Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)"
            using Mark.psimps[OF domK] NR Lgt1 mono t1z by (simp add: Let_def)
          have predT: "Pred N \<in> T_PS" using predRT by (simp add: RT_PS_def)
          have zP: "zeroT (Pred N)" using m_7_3_Trans_zeroT[OF predRT] t1z by simp
          have LP1: "Lng (Pred N) = 1" using zP by (simp add: zeroT_def)
          have L2: "Lng N = 2" using LP1 LPred L by linarith
          obtain w where Pw: "Pred N = [(w, w)]"
            using m_6_6_oneColumn[OF predT] predRT LP1 by auto
          have w0: "w = 0" using zP Pw by (simp add: zeroT_def entry_def)
          have e0: "entry N 1 0 = 0"
          proof -
            have "entry (Pred N) 1 0 = entry N 1 0" using entryP[of 0] L2 by simp
            moreover have "entry (Pred N) 1 0 = 0" using Pw w0 by (simp add: entry_def)
            ultimately show ?thesis by simp
          qed
          show ?thesis
          proof (cases "m = 0")
            case True
            have "Mark N m = Dpt 0 (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)" using kv True by simp
            also have "\<dots> = Dpt (enat (entry N 1 m)) (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)"
              using True e0 by (simp add: zero_enat_def)
            finally show ?thesis by blast
          next
            case False
            have mj1: "m = ?j1" using False mle L2 by simp
            have "Mark N m = Dpt (enat (entry N 1 ?j1)) 0\<^sub>B" using kv False by simp
            hence "Mark N m = Dpt (enat (entry N 1 m)) 0\<^sub>B" using mj1 by simp
            thus ?thesis by blast
          qed
        next
          case t1ne: False
          \<comment> \<open>(B) \<open>t\<^sub>1 \<noteq> 0\<close>\<close>
          have hp: "hasParent N 0 ?j1" by (rule monoT_hasParent0_last[OF NT mono L])
          let ?bv = "entry N 1 (Lng N - 1)"
          define jp where "jp = parent N 0 (Lng N - 1)"
          define jm1 where "jm1 = Adm N jp"
          have transJ1eq: "transJ1 N = ?j1" by (simp add: transJ1_def)
          have transJ0eq: "transJ0 N = jp" by (simp add: transJ0_def transJ1_def jp_def)
          have transJm1eq: "transJm1 N = jm1"
            by (simp add: transJm1_def jm1_def transJ0eq)
          define c1 where "c1 = Mark (Pred N) (Adm N jp)"
          define vv where "vv = bpHeadV c1"
          define tt2 where "tt2 = bpHeadT c1"
          define JJ1 where "JJ1 = Lng (PB tt2) - 1"
          define pj where "pj = PB tt2 ! JJ1"
          define ldj where "ldj = (bpHeadV pj = enat (entry N 1 jp))"
          define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
          define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
          define c2 where "c2 = (if transCondI N \<or> transCondIII N \<or> transCondV N
                         then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                         else if transCondVI N
                         then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                         else if tt2 = 0\<^sub>B
                         then Dpt vv (Dpt (enat (entry N 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                         else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry N 1 jp))
                                            (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
          have c1eqT: "c1 = transC1 N"
            by (simp add: c1_def transC1_def transJm1eq jm1_def)
          have c2eqT: "c2 = transC2 N"
            unfolding c2_def transC2_def Let_def
              vv_def tt2_def c1eqT transV_def transT2_def
              JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
            by simp
          have c1eq: "c1 = Mark (Pred N) jm1"
            by (simp add: c1_def jm1_def)
          have mkjm1: "(Pred N, jm1) \<in> Marked"
            using Marked_Pred_Adm[OF NT L hp] jp_def jm1_def by simp
          have NP: "N \<in> PT_PS" using NT mono by (simp add: PT_PS_def)
          have J1pos: "transJ1 N > 0" using L by (simp add: transJ1_def)
          have T1ne: "transT1 N \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
          have pc1: "Lng (PB (transC1 N)) = 1"
            by (rule transC1_single_principal[OF NR NP J1pos T1ne])
          have c1ne: "transC1 N \<noteq> 0\<^sub>B"
          proof
            assume "transC1 N = 0\<^sub>B"
            thus False using pc1 by (simp add: PB_def)
          qed
          have c1TB: "transC1 N \<in> T_B"
            using m_7_3_Mark_in_T_B[OF predRT mkjm1] c1eq c1eqT by simp
          have c1Dpt: "transC1 N = Dpt (transV N) (transT2 N)"
            using principal_reconstruct[OF pc1]
            by (simp add: transV_def transT2_def)
          have t2TB: "transT2 N \<in> T_B"
            using c1TB unfolding c1Dpt by (auto simp: T_B_def)
          have c1Dsym: "flatBT c1 = Dsym (transV N) # flatBT (transT2 N)"
            using c1eqT c1Dpt by simp
          \<comment> \<open>\<open>bpHeadV c\<^sub>2 = transV N\<close>\<close>
          have bpc2: "bpHeadV c2 = transV N"
          proof -
            have "bpHeadV c2 = vv"
              by (simp add: c2_def)
            also have "vv = transV N"
              by (simp add: vv_def transV_def c1eqT)
            finally show ?thesis .
          qed
          have c2pc1: "Lng (PB c2) = 1"
            using transC2_single_principal c2eqT by simp
          have c2Dpt: "c2 = Dpt (transV N) (bpHeadT c2)"
            using principal_reconstruct[OF c2pc1] bpc2 by simp
          have c2Dsym: "flatBT c2 = Dsym (transV N) # flatBT (bpHeadT c2)"
            by (subst c2Dpt) (rule flatBT_principal_head)
          show ?thesis
          proof (cases "m < ?j1")
            case mlt_false: False
            \<comment> \<open>(B) \<open>m = j\<^sub>1\<close>: \<open>Mark N m = D\<^bsub>N\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0\<close>\<close>
            have mj1: "m = ?j1" using mlt_false mle by simp
            have kv: "Mark N m = Dpt (enat (entry N 1 ?j1)) 0\<^sub>B"
              using Mark.psimps[OF domK] NR Lgt1 mono t1ne mlt_false
              unfolding Let_def jp_def[symmetric]
              by simp
            hence "Mark N m = Dpt (enat (entry N 1 m)) 0\<^sub>B" using mj1 by simp
            thus ?thesis by blast
          next
            case mlt: True
            \<comment> \<open>(B) surgery branch, \<open>m < j\<^sub>1\<close>\<close>
            have mPred: "(Pred N, m) \<in> Marked"
              by (rule Marked_Pred[OF NT L mM mlt])
            have mle2: "m \<le> Lng N - 2" using mlt L by linarith
            have entryPm: "entry (Pred N) 1 m = entry N 1 m" by (rule entryP[OF mle2])
            define c0 where "c0 = Mark (Pred N) m"
            define sm1 where
              "sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))"
            have mark_val_raw: "Mark N m = (if (Mark (Pred N) m, c1) \<in> MarkedB
                  then unflatBT
                         (fst (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                          (flatBT c1) (snd sb))
                          @ flatBT c2
                          @ snd (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                            (flatBT c1) (snd sb)))
                  else Dpt (enat ?bv) 0\<^sub>B)"
              using Mark.psimps[OF domK] NR Lgt1 mono t1ne mlt
              unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                        tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                        ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                        c2_def[symmetric]
              by simp
            have mark_val: "Mark N m = (if (c0, c1) \<in> MarkedB
                  then unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
                  else Dpt (enat ?bv) 0\<^sub>B)"
              using mark_val_raw by (simp add: c0_def sm1_def)
            \<comment> \<open>\<open>c\<^sub>0 = Mark (Pred N) m\<close> is marked, so by IH it is \<open>0\<close> or principal\<close>
            have IH0: "c0 = 0\<^sub>B \<or> (\<exists>t. c0 = Dpt (enat (entry (Pred N) 1 m)) t)"
              using less.IH[OF LPredlt] mPred predRT c0_def by blast
            show ?thesis
            proof (cases "(c0, c1) \<in> MarkedB")
              case mbc_false: False
              \<comment> \<open>Unreachable for \<open>m < j\<^sub>1\<close>: \<open>c\<^sub>1 = Mark (Pred N) jm1\<close> with \<open>m \<le> jm1\<close>,
                 so by the marked nesting \<open>(Mark (Pred N) m, Mark (Pred N) jm1) \<in>
                 MarkedB\<close>, i.e. \<open>(c\<^sub>0, c\<^sub>1) \<in> MarkedB\<close>; contradiction.  Empirically the
                 \<open>(c\<^sub>0,c\<^sub>1) \<notin> MarkedB\<close> default never fires (0/510 marked cases).\<close>
              have admN: "adm N m" using mM by (simp add: Marked_def)
              have mjp: "m \<le> jp"
                using surg_parent_ge[OF mM mono L mlt] jp_def by simp
              have mjm1: "m \<le> jm1"
                using surg_adm_ge[OF admN mjp] jm1_def by simp
              have "(Mark (Pred N) m, Mark (Pred N) jm1) \<in> MarkedB"
                using Mark_MarkedB_nest mPred mkjm1 mjm1 predRT by blast
              hence "(c0, c1) \<in> MarkedB" using c0_def c1eq by simp
              thus ?thesis using mbc_false by simp
            next
              case mbc: True
              \<comment> \<open>the surgery proper: \<open>Mark N m\<close> is principal with head \<open>bpHeadV c\<^sub>0\<close>\<close>
              have c1form: "transC1 N = Trm [DB (transV N) (transT2 N)]"
                using c1Dpt by simp
              have c1p: "c1 = Trm [DB (transV N) (transT2 N)]"
                using c1form c1eqT by simp
              have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
                using mbc unfolding MarkedB_def by auto
              have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
                unfolding sm1_def by (rule someI_ex[OF exsm])
              have c1Dsym2: "flatBT c1 = Dsym (transV N) # flatBT (transT2 N)"
                using c1eqT c1Dpt by simp
              have c0ne: "c0 \<noteq> 0\<^sub>B"
              proof
                assume z: "c0 = 0\<^sub>B"
                have "flatBT c0 = fst sm1 @ flatBT c1 @ snd sm1"
                  using dsm by (simp add: scb_decomp_def)
                hence "Dsym (transV N) \<in> set (flatBT c0)"
                  using c1Dsym2 by simp
                thus False using z by simp
              qed
              \<comment> \<open>by IH, \<open>c\<^sub>0 = Dpt (enat (entry (Pred N) 1 m)) tc0 = Dpt (enat (entry N 1 m)) tc0\<close>\<close>
              obtain tc0 where c0d: "c0 = Dpt (enat (entry (Pred N) 1 m)) tc0"
                using IH0 c0ne by blast
              have c0dN: "c0 = Dpt (enat (entry N 1 m)) tc0"
                using c0d entryPm by simp
              have c0Dsym: "flatBT c0 = Dsym (enat (entry N 1 m)) # flatBT tc0"
                using c0dN by simp
              \<comment> \<open>\<open>Mark N m\<close> is a single principal term (the surgery preserves principality)\<close>
              have c2df: "dfree_BT c2"
              proof -
                have vne: "transV N \<noteq> \<infinity>" using c1TB c1Dpt by (auto simp: T_B_def)
                have t2df: "dfree_BT (transT2 N)"
                  using c1TB c1Dpt by (auto simp: T_B_def)
                show ?thesis using dfree_transC2[OF vne t2df] c2eqT by simp
              qed
              obtain pc2 where c2p: "c2 = Trm [pc2]"
                using principal_reconstruct[OF c2pc1] by (metis BT.exhaust untrm.simps)
              have iptc2: "isPTB_str (flatBT (Trm [pc2]))"
              proof -
                have "dfree_BT (Trm [pc2])" using c2df c2p by simp
                then obtain p where "pc2 = p" and "dfree_BP p" by auto
                thus ?thesis by (auto simp: isPTB_str_def)
              qed
              obtain pc0 where c0p2: "c0 = Trm [pc0]" using c0dN by simp
              have dsm': "scb_decomp (Trm [pc0]) (fst sm1)
                            (flatBT (Trm [DB (transV N) (transT2 N)])) (snd sm1)"
                using dsm c0p2 c1p by simp
              obtain pm where pmf: "flatBP pm = fst sm1 @ flatBT (Trm [pc2]) @ snd sm1"
                  and pmd: "scb_decomp (Trm [pm]) (fst sm1) (flatBT (Trm [pc2])) (snd sm1)"
                using scb_replace_principal_BP[OF dsm' iptc2] by blast
              have markM: "Mark N m = Trm [pm]"
              proof -
                have "flatBT (Trm [pm]) = fst sm1 @ flatBT c2 @ snd sm1"
                  using pmf c2p by simp
                thus ?thesis
                  using mark_val mbc unflatBT_flat[of "Trm [pm]"] by simp
              qed
              \<comment> \<open>the leading flat symbol of \<open>Mark N m\<close> equals that of \<open>c\<^sub>0\<close>\<close>
              have flatMark: "flatBT (Mark N m) = fst sm1 @ flatBT c2 @ snd sm1"
                using markM pmf c2p by simp
              have flatc0: "flatBT c0 = fst sm1 @ flatBT c1 @ snd sm1"
                using dsm by (simp add: scb_decomp_def)
              \<comment> \<open>both \<open>flatBT c\<^sub>1\<close> and \<open>flatBT c\<^sub>2\<close> start with \<open>Dsym (transV N)\<close>, hence
                 \<open>flatBT (Mark N m)\<close> and \<open>flatBT c\<^sub>0\<close> agree on their head\<close>
              have headEq: "hd (flatBT (Mark N m)) = hd (flatBT c0)"
              proof (cases "fst sm1 = []")
                case True
                have "hd (flatBT (Mark N m)) = Dsym (transV N)"
                  using flatMark True c2Dsym by simp
                moreover have "hd (flatBT c0) = Dsym (transV N)"
                  using flatc0 True c1Dsym2 by simp
                ultimately show ?thesis by simp
              next
                case False
                have "hd (flatBT (Mark N m)) = hd (fst sm1)"
                  using flatMark False by simp
                moreover have "hd (flatBT c0) = hd (fst sm1)"
                  using flatc0 False by simp
                ultimately show ?thesis by simp
              qed
              \<comment> \<open>read off \<open>bpHeadV\<close> from the heads\<close>
              have headM: "hd (flatBT (Mark N m)) = Dsym (entry N 1 m)"
              proof -
                have "hd (flatBT c0) = Dsym (enat (entry N 1 m))"
                  using c0Dsym by simp
                thus ?thesis using headEq by simp
              qed
              obtain pm0 where pmDB: "pm = DB (bpHeadV (Trm [pm])) (bpHeadT (Trm [pm]))"
                by (cases pm) auto
              have markDpt: "Mark N m = Dpt (bpHeadV (Mark N m)) (bpHeadT (Mark N m))"
                using markM pmDB by (cases pm) simp
              have flatMarkDsym: "flatBT (Mark N m) = Dsym (bpHeadV (Mark N m)) # flatBT (bpHeadT (Mark N m))"
                by (subst markDpt) (rule flatBT_principal_head)
              have "Dsym (bpHeadV (Mark N m)) = Dsym (enat (entry N 1 m))"
                using flatMarkDsym headM by simp
              hence vEq: "bpHeadV (Mark N m) = enat (entry N 1 m)" by simp
              have "Mark N m = Dpt (enat (entry N 1 m)) (bpHeadT (Mark N m))"
                using markDpt vEq by simp
              thus ?thesis by blast
            qed
          qed
        qed
      next
        case nmono: False
        \<comment> \<open>(C) multiT branch\<close>
        have nzN: "\<not> zeroT N" using notone by (auto simp: zeroT_def)
        have muN: "multiT N" using nzN nmono by (simp add: multiT_def)
        have cut: "0 < Pcut N \<and> Pcut N \<le> ?j1" using Pcut_le[OF L] by simp
        let ?PJ = "drop (Pcut N) N"
        have PJeq: "P N ! (Lng (P N) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF NT muN])
        have Pne: "P N \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P N) - 1 < Lng (P N)" using Pne by (cases "P N") auto
        have PJRT: "?PJ \<in> RT_PS"
          using m_6_6_P_reduced[OF NT] NR J1lt PJeq by auto
        have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
        have LPJ: "Lng ?PJ = Lng N - Pcut N" by simp
        have LPJlt: "Lng ?PJ < Lng N" using LPJ cut L by linarith
        have cmle: "Pcut N \<le> m" by (rule multi_Marked_last_component(1)[OF NT muN mM])
        have c1: "(N \<notin> RT_PS) = False" using NR by simp
        have c2: "(?j1 = 0) = False" using L by simp
        have c3: "monoT N = False" using nmono by simp
        have meq2: "m - (?j1 - Lng (drop (Pcut N) N) + 1) = m - Pcut N"
        proof -
          have "?j1 - Lng ?PJ + 1 = Pcut N"
            using LPJ cut by linarith
          thus ?thesis by simp
        qed
        have markM: "Mark N m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                                 else Mark ?PJ (m - Pcut N))"
        proof -
          have raw: "Mark N m =
              (if P N ! (Lng (P N) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
               else Mark (P N ! (Lng (P N) - 1))
                      (m - (?j1 - Lng (P N ! (Lng (P N) - 1)) + 1)))"
            by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
          show ?thesis unfolding raw PJeq meq2 ..
        qed
        have entryPJ: "\<And>k. k < Lng ?PJ \<Longrightarrow> entry ?PJ 1 k = entry N 1 (Pcut N + k)"
          by (simp add: entry_def)
        have eShift: "entry ?PJ 1 (m - Pcut N) = entry N 1 m"
        proof -
          have mlt: "m - Pcut N < Lng ?PJ" using mle LPJ cut by linarith
          have "entry ?PJ 1 (m - Pcut N) = entry N 1 (Pcut N + (m - Pcut N))"
            by (rule entryPJ[OF mlt])
          also have "Pcut N + (m - Pcut N) = m" using cmle by simp
          finally show ?thesis .
        qed
        show ?thesis
        proof (cases "?PJ = [(0, 0)]")
          case True
          \<comment> \<open>last column is \<open>(0,0)\<close>, so \<open>entry N 1 m = 0\<close>\<close>
          have m_last: "m = ?j1" using multi_Marked_last_component(1)[OF NT muN mM]
            cmle mle LPJ True cut by simp
          have eN0: "entry N 1 m = 0"
          proof -
            have "entry ?PJ 1 (m - Pcut N) = 0"
            proof -
              have "m - Pcut N = 0 \<or> m - Pcut N \<ge> 1" by linarith
              moreover have "Lng ?PJ = 1" using True by simp
              ultimately have "m - Pcut N = 0" using mle LPJ cut cmle by linarith
              thus ?thesis using True by (simp add: entry_def)
            qed
            thus ?thesis using eShift by simp
          qed
          have "Mark N m = Dpt 0 0\<^sub>B" using markM True by simp
          hence "Mark N m = Dpt (enat (entry N 1 m)) 0\<^sub>B" using eN0 by (simp add: zero_enat_def)
          thus ?thesis by blast
        next
          case False
          have kv: "Mark N m = Mark ?PJ (m - Pcut N)" using markM False by simp
          have mPJ: "(?PJ, m - Pcut N) \<in> Marked"
            by (rule multi_Marked_last_component(2)[OF NT muN mM])
          have IHJ: "Mark ?PJ (m - Pcut N) = 0\<^sub>B
                     \<or> (\<exists>t. Mark ?PJ (m - Pcut N) = Dpt (enat (entry ?PJ 1 (m - Pcut N))) t)"
            using less.IH[OF LPJlt] mPJ PJRT by blast
          show ?thesis
          proof (cases "Mark ?PJ (m - Pcut N) = 0\<^sub>B")
            case True
            thus ?thesis using kv by simp
          next
            case Pne2: False
            obtain t where "Mark ?PJ (m - Pcut N) = Dpt (enat (entry ?PJ 1 (m - Pcut N))) t"
              using IHJ Pne2 by blast
            hence "Mark N m = Dpt (enat (entry N 1 m)) t" using kv eShift by simp
            thus ?thesis by blast
          qed
        qed
      qed
    qed
  qed
qed


text \<open>Helper for §7.3 命題（右端第1基点の Mark の基本性質）: every branch of
  @{thm [source] transC2_def} is \<open>D\<^bsub>v\<^esub> X\<close> with \<open>X \<noteq> 0\<^bsub>B\<^esub>\<close>, so the tail
  \<open>bpHeadT (transC2 M)\<close> is non-zero.\<close>

lemma transC2_inner_nonzero: "bpHeadT (transC2 M) \<noteq> 0\<^sub>B"
proof -
  let ?j1 = "transJ1 M"
  let ?jp = "transJ0 M"
  let ?v  = "transV M"
  let ?t2 = "transT2 M"
  let ?J1 = "Lng (PB ?t2) - 1"
  let ?pj = "PB ?t2 ! ?J1"
  let ?ldj = "(bpHeadV ?pj = enat (entry M 1 ?jp))"
  let ?t3 = "(if ?ldj then SigmaB (take ?J1 (PB ?t2)) else ?t2)"
  let ?t4 = "(if ?ldj then bpHeadT ?pj else ?t2)"
  show ?thesis
  proof (cases "transCondI M \<or> transCondIII M \<or> transCondV M")
    case True
    have "transC2 M = Dpt ?v (?t2 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
      using True by (simp add: transC2_def Let_def)
    hence "bpHeadT (transC2 M) = ?t2 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B" by simp
    moreover have "?t2 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B \<noteq> 0\<^sub>B"
      by (cases ?t2) simp
    ultimately show ?thesis by simp
  next
    case notA: False
    show ?thesis
    proof (cases "transCondVI M")
      case True
      have "transC2 M = Dpt ?v (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
        using notA True by (simp add: transC2_def Let_def)
      thus ?thesis by simp
    next
      case notVI: False
      show ?thesis
      proof (cases "?t2 = 0\<^sub>B")
        case True
        have "transC2 M = Dpt ?v (Dpt (enat (entry M 1 ?jp))
                                       (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B))"
          using notA notVI True by (simp add: transC2_def Let_def)
        thus ?thesis by simp
      next
        case t2nz: False
        have "transC2 M = Dpt ?v (?t3 +\<^sub>B Dpt (enat (entry M 1 ?jp))
                                          (?t4 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B))"
          using notA notVI t2nz by (simp add: transC2_def Let_def)
        hence "bpHeadT (transC2 M)
                 = ?t3 +\<^sub>B Dpt (enat (entry M 1 ?jp))
                              (?t4 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)" by simp
        moreover have "?t3 +\<^sub>B Dpt (enat (entry M 1 ?jp))
                              (?t4 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B) \<noteq> 0\<^sub>B"
          by (cases ?t3) simp
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>\<open>flatBT\<close> never produces the empty string.\<close>

lemma flatBT_nonempty: "flatBT t \<noteq> []"
proof -
  obtain ps where tps: "t = Trm ps" by (cases t)
  show ?thesis
  proof (cases ps)
    case Nil thus ?thesis using tps by simp
  next
    case (Cons p qs)
    show ?thesis
    proof (cases qs)
      case Nil
      obtain u a where "p = DB u a" by (cases p)
      thus ?thesis using tps Cons Nil by simp
    next
      case (Cons q rs)
      thus ?thesis using tps \<open>ps = p # qs\<close> by simp
    qed
  qed
qed

text \<open>A non-zero \<open>BT\<close> flattens to a string of length at least \<open>2\<close>
  (\<open>0\<^bsub>B\<^esub>\<close> alone flattens to the single letter \<open>"0"\<close>).\<close>

lemma flatBT_len_ge2:
  assumes "t \<noteq> 0\<^sub>B" shows "2 \<le> length (flatBT t)"
proof -
  obtain ps where tps: "t = Trm ps" by (cases t)
  have psne: "ps \<noteq> []" using assms tps by auto
  show ?thesis
  proof (cases ps)
    case Nil thus ?thesis using psne by simp
  next
    case (Cons p qs)
    show ?thesis
    proof (cases qs)
      case Nil
      obtain u a where pua: "p = DB u a" by (cases p)
      have "flatBT a \<noteq> []" by (rule flatBT_nonempty)
      hence "1 \<le> length (flatBT a)" by (cases "flatBT a") auto
      thus ?thesis using tps Cons Nil pua by simp
    next
      case (Cons q rs)
      thus ?thesis using tps \<open>ps = p # qs\<close> by simp
    qed
  qed
qed

text \<open>命題（右端第1基点の Mark の基本性質） helper (content.md 2294): for
  \<open>m < j\<^sub>1\<close> the tail of \<open>Mark M m\<close> is non-empty, i.e. \<open>Mark M m \<noteq> D\<^bsub>M\<^bsub>1,m\<^esub>\<^esub> 0\<^bsub>B\<^esub>\<close>.
  Strong \<open>Lng\<close>-induction mirroring @{thm [source] Mark_leftend_form}; the mono
  surgery sub-case is closed by a flat-length count
  (\<open>flatBT (transC2 M)\<close> contributes \<open>\<ge> 3\<close> letters, while \<open>D\<^bsub>v\<^esub> 0\<^bsub>B\<^esub>\<close> flattens
  to exactly \<open>2\<close>).\<close>

lemma Mark_tail_nonzero:
  "(M, m) \<in> Marked \<longrightarrow> M \<in> RT_PS \<longrightarrow> m < Lng M - 1
   \<longrightarrow> Mark M m \<noteq> Dpt (enat (entry M 1 m)) 0\<^sub>B"
proof (induction M arbitrary: m rule: measure_induct_rule[where f=Lng])
  case (less N)
  show ?case
  proof (intro impI)
    assume mM: "(N, m) \<in> Marked" and NR: "N \<in> RT_PS" and msmall: "m < Lng N - 1"
    have NT: "N \<in> T_PS" using NR by (simp add: RT_PS_def)
    have Nne: "N \<noteq> []" using NT by (simp add: T_PS_def)
    have domK: "\<And>m. Trans_Mark_dom (Inr (N, m))" by (rule m_7_3_Mark_welldef[OF NR])
    have leM: "leR N 0 m (Lng N - 1)" using mM by (simp add: Marked_def)
    have mleN: "m < Lng N" using leM by (simp add: leR_def le0_def)
    have mle: "m \<le> Lng N - 1" using mleN by linarith
    let ?j1 = "Lng N - 1"
    have L: "1 < Lng N" using msmall by linarith
    have Lgt1: "\<not> Lng N \<le> Suc 0" using L by simp
    have j1pos: "0 < ?j1" using L by simp
    have mlt: "m < ?j1" using msmall by simp
    show "Mark N m \<noteq> Dpt (enat (entry N 1 m)) 0\<^sub>B"
    proof (cases "monoT N")
      case mono: True
      have predRT: "Pred N \<in> RT_PS" by (rule Pred_RT_PS[OF NR])
      show ?thesis
      proof (cases "Trans (Pred N) = 0\<^sub>B")
        case t1z: True
        \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>, \<open>Lng N = 2\<close>, \<open>m < j\<^sub>1 = 1 \<Longrightarrow> m = 0\<close>;
            \<open>Mark N 0 = D\<^sub>0 (D\<^bsub>N\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0)\<close> has a non-trivial tail.\<close>
        have kv: "Mark N m = (if m = 0 then Dpt 0 (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)
                              else Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)"
          using Mark.psimps[OF domK] NR Lgt1 mono t1z by (simp add: Let_def)
        have predRTt: "Pred N \<in> RT_PS" by (rule Pred_RT_PS[OF NR])
        have zP: "zeroT (Pred N)" using m_7_3_Trans_zeroT[OF predRTt] t1z by simp
        have predb: "Pred N = butlast N" using L by (simp add: Pred_def)
        have LPred: "Lng (Pred N) = Lng N - 1" using predb by simp
        have LP1: "Lng (Pred N) = 1" using zP by (simp add: zeroT_def)
        have L2: "Lng N = 2" using LP1 LPred L by linarith
        have m0: "m = 0" using mlt L2 by simp
        have "Mark N m = Dpt 0 (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)" using kv m0 by simp
        thus ?thesis by simp
      next
        case t1ne: False
        have hp: "hasParent N 0 ?j1" by (rule monoT_hasParent0_last[OF NT mono L])
        let ?bv = "entry N 1 (Lng N - 1)"
        define jp where "jp = parent N 0 (Lng N - 1)"
        define jm1 where "jm1 = Adm N jp"
        define c1 where "c1 = Mark (Pred N) (Adm N jp)"
        define vv where "vv = bpHeadV c1"
        define tt2 where "tt2 = bpHeadT c1"
        define JJ1 where "JJ1 = Lng (PB tt2) - 1"
        define pj where "pj = PB tt2 ! JJ1"
        define ldj where "ldj = (bpHeadV pj = enat (entry N 1 jp))"
        define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
        define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
        define c2 where "c2 = (if transCondI N \<or> transCondIII N \<or> transCondV N
                       then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                       else if transCondVI N
                       then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                       else if tt2 = 0\<^sub>B
                       then Dpt vv (Dpt (enat (entry N 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                       else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry N 1 jp))
                                          (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
        have transJ1eq: "transJ1 N = ?j1" by (simp add: transJ1_def)
        have transJ0eq: "transJ0 N = jp" by (simp add: transJ0_def transJ1_def jp_def)
        have transJm1eq: "transJm1 N = jm1"
          by (simp add: transJm1_def jm1_def transJ0eq)
        have c1eqT: "c1 = transC1 N"
          by (simp add: c1_def transC1_def transJm1eq jm1_def)
        have c2eqT: "c2 = transC2 N"
          unfolding c2_def transC2_def Let_def
            vv_def tt2_def c1eqT transV_def transT2_def
            JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
          by simp
        have c1eq: "c1 = Mark (Pred N) jm1"
          by (simp add: c1_def jm1_def)
        have mkjm1: "(Pred N, jm1) \<in> Marked"
          using Marked_Pred_Adm[OF NT L hp] jp_def jm1_def by simp
        \<comment> \<open>\<open>bpHeadT c\<^sub>2 = bpHeadT (transC2 N) \<noteq> 0\<close>, so \<open>flatBT c\<^sub>2\<close> is long\<close>
        have c2pc1: "Lng (PB c2) = 1"
          using transC2_single_principal c2eqT by simp
        have c2Dpt: "c2 = Dpt (bpHeadV c2) (bpHeadT c2)"
          using principal_reconstruct[OF c2pc1] by simp
        have c2tail_ne: "bpHeadT c2 \<noteq> 0\<^sub>B"
          using transC2_inner_nonzero[of N] c2eqT by simp
        have c2Dsym: "flatBT c2 = Dsym (bpHeadV c2) # flatBT (bpHeadT c2)"
          by (subst c2Dpt) (rule flatBT_principal_head)
        have lenc2: "3 \<le> length (flatBT c2)"
        proof -
          have "2 \<le> length (flatBT (bpHeadT c2))"
            by (rule flatBT_len_ge2[OF c2tail_ne])
          thus ?thesis using c2Dsym by simp
        qed
        \<comment> \<open>the surgery, \<open>m < j\<^sub>1\<close>\<close>
        have mPred: "(Pred N, m) \<in> Marked"
          by (rule Marked_Pred[OF NT L mM mlt])
        define c0 where "c0 = Mark (Pred N) m"
        define sm1 where
          "sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))"
        have mark_val_raw: "Mark N m = (if (Mark (Pred N) m, c1) \<in> MarkedB
              then unflatBT
                     (fst (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                      (flatBT c1) (snd sb))
                      @ flatBT c2
                      @ snd (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                        (flatBT c1) (snd sb)))
              else Dpt (enat ?bv) 0\<^sub>B)"
          using Mark.psimps[OF domK] NR Lgt1 mono t1ne mlt
          unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                    tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                    ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                    c2_def[symmetric]
          by simp
        have mark_val: "Mark N m = (if (c0, c1) \<in> MarkedB
              then unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
              else Dpt (enat ?bv) 0\<^sub>B)"
          using mark_val_raw by (simp add: c0_def sm1_def)
        show ?thesis
        proof (cases "(c0, c1) \<in> MarkedB")
          case mbc_false: False
          \<comment> \<open>unreachable for \<open>m < j\<^sub>1\<close> (as in @{thm [source] Mark_leftend_form})\<close>
          have admN: "adm N m" using mM by (simp add: Marked_def)
          have mjp: "m \<le> jp"
            using surg_parent_ge[OF mM mono L mlt] jp_def by simp
          have mjm1: "m \<le> jm1"
            using surg_adm_ge[OF admN mjp] jm1_def by simp
          have "(Mark (Pred N) m, Mark (Pred N) jm1) \<in> MarkedB"
            using Mark_MarkedB_nest mPred mkjm1 mjm1 predRT by blast
          hence "(c0, c1) \<in> MarkedB" using c0_def c1eq by simp
          thus ?thesis using mbc_false by simp
        next
          case mbc: True
          \<comment> \<open>the surgery proper: \<open>Mark N m\<close> is one principal term whose flat
             string contains \<open>flatBT c\<^sub>2\<close> as an infix, hence has length \<open>\<ge> 3\<close>\<close>
          have c1form: "transC1 N = Dpt (transV N) (transT2 N)"
          proof -
            have pc1: "Lng (PB (transC1 N)) = 1"
            proof -
              have NP: "N \<in> PT_PS" using NT mono by (simp add: PT_PS_def)
              have J1pos: "transJ1 N > 0" using L by (simp add: transJ1_def)
              have T1ne: "transT1 N \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
              show ?thesis by (rule transC1_single_principal[OF NR NP J1pos T1ne])
            qed
            show ?thesis using principal_reconstruct[OF pc1]
              by (simp add: transV_def transT2_def)
          qed
          have c1p: "c1 = Trm [DB (transV N) (transT2 N)]"
            using c1form c1eqT by simp
          obtain pc2 where c2p: "c2 = Trm [pc2]"
            using principal_reconstruct[OF c2pc1] by (metis BT.exhaust untrm.simps)
          have c2df: "dfree_BT c2"
          proof -
            have NP: "N \<in> PT_PS" using NT mono by (simp add: PT_PS_def)
            have J1pos: "transJ1 N > 0" using L by (simp add: transJ1_def)
            have T1ne: "transT1 N \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
            have c1TB: "transC1 N \<in> T_B"
              using m_7_3_Mark_in_T_B[OF predRT mkjm1] c1eq c1eqT by simp
            have vne: "transV N \<noteq> \<infinity>" using c1TB c1form by (auto simp: T_B_def)
            have t2df: "dfree_BT (transT2 N)"
              using c1TB c1form by (auto simp: T_B_def)
            show ?thesis using dfree_transC2[OF vne t2df] c2eqT by simp
          qed
          have iptc2: "isPTB_str (flatBT (Trm [pc2]))"
          proof -
            have "dfree_BT (Trm [pc2])" using c2df c2p by simp
            then obtain p where "pc2 = p" and "dfree_BP p" by auto
            thus ?thesis by (auto simp: isPTB_str_def)
          qed
          have IH0: "c0 = 0\<^sub>B \<or> (\<exists>t. c0 = Dpt (enat (entry (Pred N) 1 m)) t)"
            using Mark_leftend_form mPred predRT c0_def by blast
          have c0ne: "c0 \<noteq> 0\<^sub>B"
          proof -
            have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
              using mbc unfolding MarkedB_def by auto
            have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
              unfolding sm1_def by (rule someI_ex[OF exsm])
            have c1Dsym2: "flatBT c1 = Dsym (transV N) # flatBT (transT2 N)"
              using c1eqT c1form by simp
            show ?thesis
            proof
              assume z: "c0 = 0\<^sub>B"
              have "flatBT c0 = fst sm1 @ flatBT c1 @ snd sm1"
                using dsm by (simp add: scb_decomp_def)
              hence "Dsym (transV N) \<in> set (flatBT c0)"
                using c1Dsym2 by simp
              thus False using z by simp
            qed
          qed
          obtain pc0 where c0p2: "c0 = Trm [pc0]" using IH0 c0ne by auto
          have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
            using mbc unfolding MarkedB_def by auto
          have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
            unfolding sm1_def by (rule someI_ex[OF exsm])
          have dsm': "scb_decomp (Trm [pc0]) (fst sm1)
                        (flatBT (Trm [DB (transV N) (transT2 N)])) (snd sm1)"
            using dsm c0p2 c1p by simp
          obtain pm where pmf: "flatBP pm = fst sm1 @ flatBT (Trm [pc2]) @ snd sm1"
              and pmd: "scb_decomp (Trm [pm]) (fst sm1) (flatBT (Trm [pc2])) (snd sm1)"
            using scb_replace_principal_BP[OF dsm' iptc2] by blast
          have markM: "Mark N m = Trm [pm]"
          proof -
            have "flatBT (Trm [pm]) = fst sm1 @ flatBT c2 @ snd sm1"
              using pmf c2p by simp
            thus ?thesis
              using mark_val mbc unflatBT_flat[of "Trm [pm]"] by simp
          qed
          \<comment> \<open>flat length: \<open>flatBT c\<^sub>2\<close> (length \<open>\<ge> 3\<close>) is an infix\<close>
          have flatMark: "flatBT (Mark N m) = fst sm1 @ flatBT c2 @ snd sm1"
            using markM pmf c2p by simp
          have lenMark: "3 \<le> length (flatBT (Mark N m))"
            using flatMark lenc2 by simp
          show ?thesis
          proof
            assume eq: "Mark N m = Dpt (enat (entry N 1 m)) 0\<^sub>B"
            have "flatBT (Mark N m) = [Dsym (enat (entry N 1 m)), Zsym]"
              by (simp add: eq)
            thus False using lenMark by simp
          qed
        qed
      qed
    next
      case nmono: False
      \<comment> \<open>(C) multiT branch: recurse into the last component \<open>?PJ\<close>\<close>
      have nzN: "\<not> zeroT N" using L by (auto simp: zeroT_def)
      have muN: "multiT N" using nzN nmono by (simp add: multiT_def)
      have cut: "0 < Pcut N \<and> Pcut N \<le> ?j1" using Pcut_le[OF L] by simp
      let ?PJ = "drop (Pcut N) N"
      have PJeq: "P N ! (Lng (P N) - 1) = ?PJ"
        by (rule trans_multiT_last_component(1)[OF NT muN])
      have Pne: "P N \<noteq> []" by (rule P_nonempty)
      have J1lt: "Lng (P N) - 1 < Lng (P N)" using Pne by (cases "P N") auto
      have PJRT: "?PJ \<in> RT_PS"
        using m_6_6_P_reduced[OF NT] NR J1lt PJeq by auto
      have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
      have LPJ: "Lng ?PJ = Lng N - Pcut N" by simp
      have LPJlt: "Lng ?PJ < Lng N" using LPJ cut L by linarith
      have cmle: "Pcut N \<le> m" by (rule multi_Marked_last_component(1)[OF NT muN mM])
      have c1: "(N \<notin> RT_PS) = False" using NR by simp
      have c2: "(?j1 = 0) = False" using L by simp
      have c3: "monoT N = False" using nmono by simp
      have meq2: "m - (?j1 - Lng (drop (Pcut N) N) + 1) = m - Pcut N"
      proof -
        have "?j1 - Lng ?PJ + 1 = Pcut N" using LPJ cut by linarith
        thus ?thesis by simp
      qed
      have markM: "Mark N m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                               else Mark ?PJ (m - Pcut N))"
      proof -
        have raw: "Mark N m =
            (if P N ! (Lng (P N) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
             else Mark (P N ! (Lng (P N) - 1))
                    (m - (?j1 - Lng (P N ! (Lng (P N) - 1)) + 1)))"
          by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
        show ?thesis unfolding raw PJeq meq2 ..
      qed
      have entryPJ: "\<And>k. k < Lng ?PJ \<Longrightarrow> entry ?PJ 1 k = entry N 1 (Pcut N + k)"
        by (simp add: entry_def)
      have eShift: "entry ?PJ 1 (m - Pcut N) = entry N 1 m"
      proof -
        have mltJ: "m - Pcut N < Lng ?PJ" using mle LPJ cut by linarith
        have "entry ?PJ 1 (m - Pcut N) = entry N 1 (Pcut N + (m - Pcut N))"
          by (rule entryPJ[OF mltJ])
        also have "Pcut N + (m - Pcut N) = m" using cmle by simp
        finally show ?thesis .
      qed
      show ?thesis
      proof (cases "?PJ = [(0, 0)]")
        case True
        \<comment> \<open>then \<open>m\<close> is forced to be the last index \<open>j\<^sub>1\<close>, contradicting \<open>m < j\<^sub>1\<close>\<close>
        have m_last: "m = ?j1" using multi_Marked_last_component(1)[OF NT muN mM]
          cmle mle LPJ True cut by simp
        thus ?thesis using mlt by simp
      next
        case PJne: False
        have kv: "Mark N m = Mark ?PJ (m - Pcut N)" using markM PJne by simp
        have mPJ: "(?PJ, m - Pcut N) \<in> Marked"
          by (rule multi_Marked_last_component(2)[OF NT muN mM])
        have mltJ: "m - Pcut N < Lng ?PJ - 1"
        proof -
          have "m - Pcut N < ?j1 - Pcut N" using mlt cmle cut by linarith
          moreover have "?j1 - Pcut N = Lng ?PJ - 1" using LPJ cut L by linarith
          ultimately show ?thesis by simp
        qed
        have IHJ: "Mark ?PJ (m - Pcut N) \<noteq> Dpt (enat (entry ?PJ 1 (m - Pcut N))) 0\<^sub>B"
          using less.IH[OF LPJlt] mPJ PJRT mltJ by blast
        show ?thesis using kv IHJ eShift by simp
      qed
    qed
  qed
qed

end

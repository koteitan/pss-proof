theory P_7_4_RightNodes_Mark
  imports Support_7_022
begin

text \<open>系（\<open>RightNodes\<close> と \<open>Mark\<close> の関係） (§7.4, content.md 2691): for a marked
  reduced \<open>(M,m)\<close> with \<open>0 < m < Lng M - 1\<close>, the marked value \<open>Mark M m\<close> sits as a
  common subexpression splitting \<open>RightNodes (Trans M)\<close> at the row-1 entry
  \<open>M\<^bsub>1,m\<^esub>\<close>.  Article: immediate from @{thm [source] m_7_4_Trans_Mark_seg} (the
  common scb position), @{thm [source] Mark_leftend_form} (left end of \<open>Mark M m\<close>
  is \<open>D\<^bsub>M\<^bsub>1,m\<^esub>\<^esub>\<close>), and the \<open>RightNodes\<close>-subexpression engine
  (@{thm [source] m_7_4_RightNodes_subexpr_gen}).\<close>

lemma m_7_4_RightNodes_Mark:
  assumes "(M, m) \<in> Marked" and "M \<in> RT_PS" and "0 < m" and "m < Lng M - 1"
  shows "\<exists>a0 a1. RightNodes (Trans M) = a0 @ [entry M 1 m] @ a1
              \<and> RightNodes (Trans (seg M 0 m)) = a0 @ [entry M 1 m]
              \<and> RightNodes (Mark M m) = [entry M 1 m] @ a1"
proof -
  let ?v = "entry M 1 m"
  have MT: "M \<in> T_PS" using assms(2) by (simp add: RT_PS_def)
  have L0: "1 < Lng M" using assms(3) assms(4) by linarith
  \<comment> \<open>the common scb position \<open>(s,b)\<close> from \<open>m_7_4_Trans_Mark_seg\<close>\<close>
  have exSB: "\<exists>sb. scb_decomp (Trans (seg M 0 m)) (fst sb)
                  (flatBT (Dpt (enat ?v) 0\<^sub>B)) (snd sb)
              \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
    using m_7_4_Trans_Mark_seg[OF assms(1) assms(2) assms(3) assms(4)]
    by (rule ex1_implies_ex)
  obtain sb where
    SB: "scb_decomp (Trans (seg M 0 m)) (fst sb)
            (flatBT (Dpt (enat ?v) 0\<^sub>B)) (snd sb)"
        "scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
    using exSB by blast
  define s where "s = fst sb"
  define b where "b = snd sb"
  have Dseg: "scb_decomp (Trans (seg M 0 m)) s (flatBT (Dpt (enat ?v) 0\<^sub>B)) b"
    using SB(1) s_def b_def by simp
  have DM: "scb_decomp (Trans M) s (flatBT (Mark M m)) b"
    using SB(2) s_def b_def by simp
  have flat0: "flatBT (Trans (seg M 0 m)) = s @ flatBT (Dpt (enat ?v) 0\<^sub>B) @ b"
    using Dseg by (simp add: scb_decomp_def)
  have bRP: "\<forall>x \<in> set b. x = RP"
    using Dseg by (simp add: scb_decomp_def)
  have flatM: "flatBT (Trans M) = s @ flatBT (Mark M m) @ b"
    using DM by (simp add: scb_decomp_def)
  \<comment> \<open>\<open>Trans M \<noteq> Trm []\<close> (else its flat would be \<open>[Zsym]\<close>, no \<open>Dsym\<close>)\<close>
  have nzM: "\<not> zeroT M" using L0 by (auto simp: zeroT_def)
  have tMne: "Trans M \<noteq> Trm []"
    using m_7_3_Trans_zeroT[OF assms(2)] nzM by auto
  \<comment> \<open>so the scb middle \<open>flatBT (Mark M m)\<close> is a principal-term string\<close>
  have iptM: "isPTB_str (flatBT (Mark M m))"
    using DM tMne by (simp add: scb_decomp_def)
  \<comment> \<open>hence \<open>Mark M m \<noteq> 0\<^sub>B\<close>: its flat is not \<open>[Zsym]\<close>\<close>
  have markNZ: "Mark M m \<noteq> 0\<^sub>B"
  proof
    assume z: "Mark M m = 0\<^sub>B"
    have "isPTB_str [Zsym]" using iptM z by simp
    then obtain p where "flatBP p = [Zsym]" unfolding isPTB_str_def by auto
    thus False by (cases p) simp
  qed
  \<comment> \<open>left end of \<open>Mark M m\<close> is \<open>D\<^bsub>v\<^esub>\<close>: \<open>Mark M m = Dpt (enat v) t'\<close>\<close>
  obtain t' where markform: "Mark M m = Dpt (enat ?v) t'"
    using Mark_leftend_form assms(1) assms(2) markNZ by blast
  have markeq: "Dpt (enat ?v) t' = Mark M m" using markform by simp
  \<comment> \<open>body \<open>t' \<in> T\<^bsub>B\<^esub>\<close> (from \<open>Mark M m \<in> T\<^bsub>B\<^esub>\<close>)\<close>
  have markTB: "Mark M m \<in> T_B"
    by (rule m_7_3_Mark_in_T_B[OF assms(2) assms(1)])
  have t'TB: "t' \<in> T_B"
    using markTB markform by (simp add: T_B_def)
  \<comment> \<open>\<open>Trans (seg M 0 m) \<in> T\<^bsub>B\<^esub>\<close>: the slice is reduced\<close>
  have segRT: "seg M 0 m \<in> RT_PS"
    by (rule seg_0_RT_PS[OF assms(2)]) (use assms(4) in linarith)
  have segTB: "Trans (seg M 0 m) \<in> T_B"
    by (rule m_7_3_Trans_in_T_B[OF segRT])
  \<comment> \<open>apply the (principality-free) subexpression engine with \<open>t := t'\<close>\<close>
  have exUA: "\<exists>aa. RightNodes (spineSub (Trans (seg M 0 m)) t') = fst aa @ [?v] @ snd aa
                 \<and> RightNodes (Trans (seg M 0 m)) = fst aa @ [?v]
                 \<and> RightNodes (Dpt (enat ?v) t') = [?v] @ snd aa"
    using m_7_4_RightNodes_subexpr_gen[OF t'TB bRP segTB flat0]
    by (rule ex1_implies_ex)
  obtain aa where
    UA: "RightNodes (spineSub (Trans (seg M 0 m)) t') = fst aa @ [?v] @ snd aa"
        "RightNodes (Trans (seg M 0 m)) = fst aa @ [?v]"
        "RightNodes (Dpt (enat ?v) t') = [?v] @ snd aa"
    using exUA by blast
  define a0 where "a0 = fst aa"
  define a1 where "a1 = snd aa"
  have rnSeg: "RightNodes (Trans (seg M 0 m)) = a0 @ [?v]"
    using UA(2) a0_def by simp
  have rnMark: "RightNodes (Mark M m) = [?v] @ a1"
  proof -
    have "RightNodes (Mark M m) = RightNodes (Dpt (enat ?v) t')"
      using markform by simp
    also have "\<dots> = [?v] @ snd aa" using UA(3) .
    finally show ?thesis using a1_def by simp
  qed
  \<comment> \<open>the substituted term \<open>spineSub (Trans (seg M 0 m)) t'\<close> is \<open>Trans M\<close>,
      by \<open>flatBT\<close> injectivity\<close>
  have flatSub: "flatBT (spineSub (Trans (seg M 0 m)) t')
               = s @ Dsym (enat ?v) # flatBT t' @ b"
  proof -
    have Hf: "flatBT (Trans (seg M 0 m)) = s @ Dsym (enat ?v) # Zsym # b"
      using flat0 by simp
    have "flatBT (spineSub (Trans (seg M 0 m)) t')
            = s @ Dsym (enat ?v) # flatBT t' @ b \<and> spineSub (Trans (seg M 0 m)) t' \<in> T_B"
      using rnsub_flat_main Hf bRP segTB t'TB by blast
    thus ?thesis by simp
  qed
  have flatSub2: "flatBT (spineSub (Trans (seg M 0 m)) t') = flatBT (Trans M)"
  proof -
    have "flatBT (Trans M) = s @ flatBT (Mark M m) @ b" using flatM .
    also have "flatBT (Mark M m) = flatBT (Dpt (enat ?v) t')"
      using markform by simp
    also have "\<dots> = Dsym (enat ?v) # flatBT t'" by simp
    finally have "flatBT (Trans M) = s @ Dsym (enat ?v) # flatBT t' @ b" by simp
    thus ?thesis using flatSub by simp
  qed
  have subEq: "spineSub (Trans (seg M 0 m)) t' = Trans M"
    using flatSub2 by (rule m_7_flatBT_inj)
  have rnTrans: "RightNodes (Trans M) = a0 @ [?v] @ a1"
    using UA(1) subEq a0_def a1_def by simp
  show ?thesis using rnTrans rnSeg rnMark by blast
qed


text \<open>系（\<open>RightNodes\<close>と\<open>Mark\<close>の関係） (§7.4): for any
  \<open>(M,m) \<in> RT\<^bsub>PS\<^esub>\<^sup>Marked\<close> (modelled by \<open>(M,m) \<in> Marked \<and> M \<in> RT\<^bsub>PS\<^esub>\<close>), if
  \<open>0 < m < Lng M - 1\<close> then there exist \<open>a\<^sub>0, a\<^sub>1 \<in> \<nat>\<^bsup><\<omega>\<^esup>\<close> such that
  \<open>RightNodes(Trans M) = a\<^sub>0 \<frown> (M\<^sub>1\<^sub>,\<^sub>m) \<frown> a\<^sub>1\<close>,
  \<open>RightNodes(Trans((M\<^sub>j)\<^bsub>j=0\<^esub>\<^bsup>m\<^esup>)) = a\<^sub>0 \<frown> (M\<^sub>1\<^sub>,\<^sub>m)\<close>, and
  \<open>RightNodes(Mark(M, m)) = (M\<^sub>1\<^sub>,\<^sub>m) \<frown> a\<^sub>1\<close>.  Here the article's \<open>\<oplus>\<^sub>\<nat>\<close> on
  \<open>\<nat>\<^bsup><\<omega>\<^esup>\<close> is list append \<open>@\<close>, and \<open>(M\<^sub>1\<^sub>,\<^sub>m) = [entry M 1 m]\<close>.\<close>

lemma p_7_4_RightNodes_Mark:
  assumes "(M, m) \<in> Marked" "M \<in> RT_PS"
    and "0 < m" "m < Lng M - 1"
  shows "\<exists>a0 a1. RightNodes (Trans M) = a0 @ [entry M 1 m] @ a1
              \<and> RightNodes (Trans (seg M 0 m)) = a0 @ [entry M 1 m]
              \<and> RightNodes (Mark M m) = [entry M 1 m] @ a1"
  using assms by (rule m_7_4_RightNodes_Mark)

end

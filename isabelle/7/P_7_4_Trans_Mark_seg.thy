theory P_7_4_Trans_Mark_seg
  imports P_7_4_Trans_Mark_Pred
begin

text \<open>§7.4 系（\<open>Trans\<close> の \<open>Mark\<close> と切片による表示）— content.md 2646.
  Corollary of @{thm [source] m_7_4_Trans_Mark_Pred}: the same scb position
  \<open>(s\<^sub>0,b\<^sub>0)\<close> inserts \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> 0\<close> into \<open>Trans (seg M 0 m)\<close> and \<open>Mark M m\<close>
  into \<open>Trans M\<close>.  Proof by \<open>Lng\<close>-induction collapsing \<open>M\<close> to \<open>Pred M\<close>:
  on the slice \<open>m \<le> Lng M - 2\<close> so \<open>seg M 0 m = seg (Pred M) 0 m\<close>; the base
  \<open>m = Lng (Pred M) - 1\<close> uses @{thm [source] Mark_rightmost1_forward}
  (\<open>Mark (Pred M) m = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> 0\<close>) with \<open>seg M 0 m = Pred M\<close>; the recursive
  step \<open>m < Lng (Pred M) - 1\<close> applies the IH to \<open>Pred M\<close> and aligns positions
  via @{thm [source] m_7_2_scb_unique_sb} on \<open>Trans (Pred M)\<close>.\<close>

lemma m_7_4_Trans_Mark_seg:
  assumes mM0: "(M, m) \<in> Marked" and MR0: "M \<in> RT_PS"
    and mpos0: "0 < m" and mlt0: "m < Lng M - 1"
  shows "\<exists>!sb. scb_decomp (Trans (seg M 0 m))
                  (fst sb) (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) (snd sb)
            \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
proof -
  have ex: "M \<in> RT_PS \<longrightarrow> (\<forall>m. (M, m) \<in> Marked \<longrightarrow> 0 < m \<longrightarrow> m < Lng M - 1 \<longrightarrow>
       (\<exists>s0 b0.
          scb_decomp (Trans (seg M 0 m)) s0 (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) b0
        \<and> scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0))"
  proof (induction M rule: measure_induct_rule[where f=Lng])
    case (less M)
    show ?case
    proof (intro impI allI)
      fix m
      assume MR: "M \<in> RT_PS" and mM: "(M, m) \<in> Marked"
        and mpos: "0 < m" and mlt: "m < Lng M - 1"
      have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
      have L: "1 < Lng M" using mlt mpos by linarith
      \<comment> \<open>collapse to \<open>P = Pred M\<close>; positions and the slice agree\<close>
      define P where "P = Pred M"
      have predRT: "P \<in> RT_PS" using Pred_RT_PS[OF MR] P_def by simp
      have predb: "P = butlast M" using L P_def by (simp add: Pred_def)
      have LP: "Lng P = Lng M - 1" using predb by simp
      have mPred: "(P, m) \<in> Marked" using Marked_Pred[OF MT L mM mlt] P_def by simp
      have mltP: "m \<le> Lng P - 1" using mlt LP by linarith
      \<comment> \<open>the slice agrees: \<open>seg M 0 m = seg P 0 m\<close>\<close>
      have segeq: "seg M 0 m = seg P 0 m"
      proof -
        have sM: "seg M 0 m = take (Suc m) M"
          by (rule seg_0_eq_take) (use mlt L in linarith)
        have sP: "seg P 0 m = take (Suc m) P"
          by (rule seg_0_eq_take) (use mltP LP L in linarith)
        have "take (Suc m) P = take (Suc m) M"
        proof -
          have "P = take (Lng M - 1) M" using predb by (simp add: butlast_conv_take)
          hence "take (Suc m) P = take (min (Suc m) (Lng M - 1)) M" by (simp add: take_take)
          also have "min (Suc m) (Lng M - 1) = Suc m" using mlt by simp
          finally show ?thesis .
        qed
        thus ?thesis using sM sP by simp
      qed
      \<comment> \<open>row-1 entry agrees on the slice\<close>
      have entryeq: "entry P 1 m = entry M 1 m"
      proof -
        have "m < length (butlast M)" using mlt by simp
        thus ?thesis using predb by (simp add: entry_def nth_butlast)
      qed
      \<comment> \<open>the \<open>Pred\<close>-corollary supplies the position \<open>(s0,b0)\<close>\<close>
      have exP: "\<exists>sb. scb_decomp (Trans (Pred M)) (fst sb)
                          (flatBT (Mark (Pred M) m)) (snd sb)
                      \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
        using m_7_4_Trans_Mark_Pred[OF mM MR mlt] by (rule ex1_implies_ex)
      obtain sbP where
        HP: "scb_decomp (Trans P) (fst sbP) (flatBT (Mark P m)) (snd sbP)"
            "scb_decomp (Trans M) (fst sbP) (flatBT (Mark M m)) (snd sbP)"
        using exP P_def by auto
      define s0 where "s0 = fst sbP"
      define b0 where "b0 = snd sbP"
      have H0: "scb_decomp (Trans P) s0 (flatBT (Mark P m)) b0"
               "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
        using HP s0_def b0_def by simp_all
      have dM: "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0" using H0(2) .
      \<comment> \<open>now match the slice scb at the same position\<close>
      have dseg: "scb_decomp (Trans (seg M 0 m)) s0
                     (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) b0"
      proof (cases "m = Lng P - 1")
        case base: True
        \<comment> \<open>\<open>m\<close> is the last index of \<open>P\<close>: \<open>Mark P m = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> 0\<close> and \<open>seg M 0 m = P\<close>\<close>
        have nzP: "\<not> zeroT P"
        proof
          assume "zeroT P"
          hence "Lng P = 1" by (simp add: zeroT_def)
          thus False using base mpos by simp
        qed
        have markP: "Mark P m = Dpt (enat (entry P 1 m)) 0\<^sub>B"
          using Mark_rightmost1_forward[OF predRT nzP] mPred base by simp
        have markP': "Mark P m = Dpt (enat (entry M 1 m)) 0\<^sub>B"
          using markP entryeq by simp
        have segP: "seg M 0 m = P"
        proof -
          have "seg P 0 m = take (Suc m) P"
            by (rule seg_0_eq_take) (use mltP LP L in linarith)
          also have "Suc m = Lng P" using base LP L by linarith
          also have "take (Lng P) P = P" by simp
          finally show ?thesis using segeq by simp
        qed
        show ?thesis using H0(1) markP' segP by simp
      next
        case rec: False
        have mltP': "m < Lng P - 1" using mltP rec by simp
        have LPlt: "Lng P < Lng M" using LP L by simp
        \<comment> \<open>IH on the smaller \<open>P\<close>\<close>
        from less.IH[OF LPlt] predRT mPred mpos mltP'
        obtain s0' b0' where
          G0: "scb_decomp (Trans (seg P 0 m)) s0'
                  (flatBT (Dpt (enat (entry P 1 m)) 0\<^sub>B)) b0'"
              "scb_decomp (Trans P) s0' (flatBT (Mark P m)) b0'"
          by blast
        \<comment> \<open>\<open>Trans P \<noteq> Trm []\<close>: \<open>m < Lng P - 1\<close> forces \<open>Lng P > 1\<close>, so \<open>\<not> zeroT P\<close>\<close>
        have nzP: "\<not> zeroT P"
        proof
          assume "zeroT P"
          hence "Lng P = 1" by (simp add: zeroT_def)
          thus False using mltP' by simp
        qed
        have tPne: "Trans P \<noteq> Trm []"
          using m_7_3_Trans_zeroT[OF predRT] nzP by auto
        have coh: "s0' = s0 \<and> b0' = b0"
          by (rule m_7_2_scb_unique_sb[OF G0(2) H0(1) tPne])
        have "scb_decomp (Trans (seg P 0 m)) s0
                  (flatBT (Dpt (enat (entry P 1 m)) 0\<^sub>B)) b0"
          using G0(1) coh by simp
        thus ?thesis using segeq entryeq by simp
      qed
      show "\<exists>s0 b0. scb_decomp (Trans (seg M 0 m)) s0
                       (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) b0
                  \<and> scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
        using dseg dM by blast
    qed
  qed
  obtain s0 b0 where
    H: "scb_decomp (Trans (seg M 0 m)) s0 (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) b0"
       "scb_decomp (Trans M) s0 (flatBT (Mark M m)) b0"
    using ex MR0 mM0 mpos0 mlt0 by blast
  \<comment> \<open>uniqueness via \<open>Trans M \<noteq> Trm []\<close>\<close>
  have MT0: "M \<in> T_PS" using MR0 by (simp add: RT_PS_def)
  have L0: "1 < Lng M" using mlt0 mpos0 by linarith
  have nzM: "\<not> zeroT M" using L0 by (auto simp: zeroT_def)
  have tMne: "Trans M \<noteq> Trm []"
    using m_7_3_Trans_zeroT[OF MR0] nzM by auto
  show ?thesis
  proof (rule ex1I[of _ "(s0, b0)"])
    show "scb_decomp (Trans (seg M 0 m)) (fst (s0, b0))
              (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) (snd (s0, b0))
        \<and> scb_decomp (Trans M) (fst (s0, b0)) (flatBT (Mark M m)) (snd (s0, b0))"
      using H by simp
  next
    fix sb
    assume A: "scb_decomp (Trans (seg M 0 m)) (fst sb)
                  (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) (snd sb)
             \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
    have dM_sb: "scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
      using A by simp
    have "fst sb = s0 \<and> snd sb = b0"
      by (rule m_7_2_scb_unique_sb[OF dM_sb H(2) tMne])
    thus "sb = (s0, b0)" by (cases sb) auto
  qed
qed


text \<open>系（\<open>Trans\<close>の\<open>Mark\<close>と切片による表示） (§7.4): for any
  \<open>(M,m) \<in> RT\<^bsub>PS\<^esub>\<^sup>Marked\<close> (modelled by \<open>(M,m) \<in> Marked \<and> M \<in> RT\<^bsub>PS\<^esub>\<close>), if
  \<open>0 < m < Lng M - 1\<close> then there exist unique \<open>(s\<^sub>0,b\<^sub>0)\<close> such that
  \<open>(s\<^sub>0, D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> 0, b\<^sub>0)\<close> is an scb-decomposition of \<open>Trans((M\<^sub>j)\<^bsub>j=0\<^esub>\<^bsup>m\<^esup>)\<close> and
  \<open>(s\<^sub>0, Mark(M, m), b\<^sub>0)\<close> is an scb-decomposition of \<open>Trans M\<close>.  Here
  \<open>(M\<^sub>j)\<^bsub>j=0\<^esub>\<^bsup>m\<^esup> = seg M 0 m\<close> and \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> 0 = Dpt (enat (entry M 1 m)) 0\<^sub>B\<close>.\<close>

lemma p_7_4_Trans_Mark_seg:
  assumes "(M, m) \<in> Marked" "M \<in> RT_PS"
    and "0 < m" "m < Lng M - 1"
  shows "\<exists>!sb. scb_decomp (Trans (seg M 0 m))
                  (fst sb) (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) (snd sb)
            \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
  using assms by (rule m_7_4_Trans_Mark_seg)

end

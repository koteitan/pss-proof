theory P_7_3_Trans_monoT
  imports Frontier_7_044
begin

text \<open>命題（\<open>Trans\<close>が単項性を保つこと） (§7.3, content.md 2358).  \<open>RT\<^bsub>PS\<^esub>\<close>-restricted
  (the §7 convention), with the correction A16 hypothesis \<open>\<not> zeroT (P M ! 0)\<close>
  (a non-zero first \<open>P\<close>-component).  Under that hypothesis \<open>M\<close> is monotone iff its
  translation is principal, i.e. has a single principal component
  \<open>Lng (PB (Trans M)) = 1\<close>.

  The transcribed exceptional-disjunct form
  \<open>Lng (PB (Trans M)) = 1 \<or> (zeroT (P M ! 0) \<and> Lng (P M) = 2)\<close>
  is FALSE (correction A16, 53 counterexamples, e.g. \<open>M = [(0,0),(0,0),(1,1)]\<close>:
  \<open>multiT M\<close> but the right disjunct holds, breaking the iff).  The empirically
  verified corrected form (1269 reduced cases under \<open>\<not> zeroT (P M ! 0)\<close>, 0 CEX)
  is the restricted iff below.

  Forward: \<open>monoT M\<close> gives \<open>P M = [M]\<close> and \<open>Trans M \<noteq> 0\<^sub>B\<close>, and
  @{thm [source] Trans_PT_single} makes \<open>Trans M\<close> single-principal.
  Backward (contrapositive): \<open>\<not> monoT M\<close> with \<open>\<not> zeroT (P M ! 0)\<close> forces
  \<open>multiT M\<close>; the multi \<open>Trans\<close> recursion writes \<open>Trans M = Trans A +\<^sub>B (\<dots>)\<close> with
  both summands principal-nonempty, so \<open>Lng (PB (Trans M)) \<ge> 2\<close>.\<close>

lemma m_7_3_Trans_monoT:
  assumes MR: "M \<in> RT_PS" and P0nz: "\<not> zeroT (P M ! 0)"
  shows "monoT M \<longleftrightarrow> Lng (PB (Trans M)) = 1"
proof
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  \<comment> \<open>\<open>\<not> zeroT (P M ! 0)\<close> rules out the singleton \<open>((0,0))\<close> first component\<close>
  have P0ne: "P M ! 0 \<noteq> [(0, 0)]"
  proof
    assume "P M ! 0 = [(0, 0)]"
    hence "zeroT (P M ! 0)" by (simp add: zeroT_def entry_def)
    thus False using P0nz by simp
  qed
  \<comment> \<open>and \<open>M\<close> itself is not zero (else \<open>P M = [M]\<close> and \<open>P M ! 0 = M\<close> would be zero)\<close>
  have nzM: "\<not> zeroT M"
  proof
    assume zM: "zeroT M"
    have "\<not> (multiT M \<and> 1 < Lng M)" using zM by (simp add: multiT_def)
    hence "P M = [M]" by (rule poper_P_nonmulti)
    hence "P M ! 0 = M" by simp
    thus False using zM P0nz by simp
  qed
  show "monoT M \<Longrightarrow> Lng (PB (Trans M)) = 1"
  proof -
    assume mono: "monoT M"
    \<comment> \<open>\<open>Trans M\<close> is a single principal term\<close>
    have tne: "Trans M \<noteq> 0\<^sub>B"
    proof
      assume "Trans M = 0\<^sub>B"
      hence "zeroT M" using m_7_3_Trans_zeroT[OF MR] by simp
      thus False using nzM by simp
    qed
    obtain p where tp: "Trans M = Trm [p]"
      using Trans_PT_single MR mono tne by blast
    show "Lng (PB (Trans M)) = 1" using tp by (simp add: PB_def)
  qed
next
  \<comment> \<open>backward, by contraposition\<close>
  show "Lng (PB (Trans M)) = 1 \<Longrightarrow> monoT M"
  proof (rule ccontr)
    assume pb1: "Lng (PB (Trans M)) = 1" and nmono: "\<not> monoT M"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    \<comment> \<open>re-establish the two facts derived above (they live in the other branch)\<close>
    have P0ne: "P M ! 0 \<noteq> [(0, 0)]"
    proof
      assume "P M ! 0 = [(0, 0)]"
      hence "zeroT (P M ! 0)" by (simp add: zeroT_def entry_def)
      thus False using P0nz by simp
    qed
    have nzM: "\<not> zeroT M"
    proof
      assume zM: "zeroT M"
      have "\<not> (multiT M \<and> 1 < Lng M)" using zM by (simp add: multiT_def)
      hence "P M = [M]" by (rule poper_P_nonmulti)
      hence "P M ! 0 = M" by simp
      thus False using zM P0nz by simp
    qed
    have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
    have L: "1 < Lng M" using multiT_imp_Lng_gt1[OF MT muM] .
    have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
    let ?A = "take (Pcut M) M"
    let ?PJ = "drop (Pcut M) M"
    have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
    have Acut_RT: "?A \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF MR muM])
    \<comment> \<open>\<open>P\<close>-decomposition: \<open>P M = P ?A @ [?PJ]\<close>, so \<open>P M ! 0 = P ?A ! 0\<close>\<close>
    have PMsplit: "P M = P ?A @ [?PJ]"
      by (rule poper_P_multi) (use muM L in simp)
    have PAne: "P ?A \<noteq> []" by (rule P_nonempty)
    have P0eq: "P M ! 0 = P ?A ! 0"
      using PMsplit PAne by (simp add: nth_append)
    have P0Ane: "P ?A ! 0 \<noteq> [(0, 0)]" using P0ne P0eq by simp
    \<comment> \<open>the multi recursion value (copy from @{thm [source] m_7_3_Trans_leftmost_pc})\<close>
    have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
      by (rule trans_multiT_last_component(1)[OF MT muM])
    have Aeq2: "seg M 0 (Lng M - 1 - Lng ?PJ + 1 - 1) = ?A"
    proof -
      have LdJ: "Lng ?PJ = Lng M - Pcut M" by simp
      have "Lng M - 1 - Lng ?PJ + 1 - 1 = Pcut M - 1"
        using LdJ cut by linarith
      moreover have "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
        by (rule seg_0_eq_take) (use cut L in linarith)
      moreover have "Suc (Pcut M - 1) = Pcut M" using cut by simp
      ultimately show ?thesis by simp
    qed
    have c1f: "(M \<notin> RT_PS) = False" using MR by simp
    have c2f: "(Lng M - 1 = 0) = False" using L by simp
    have c3f: "monoT M = False" using nmono by simp
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
    \<comment> \<open>\<open>Trans ?A \<noteq> 0\<^sub>B\<close>: otherwise \<open>?A\<close> is zero, forcing \<open>P ?A ! 0 = ((0,0))\<close>\<close>
    have TAne: "Trans ?A \<noteq> 0\<^sub>B"
    proof
      assume z: "Trans ?A = 0\<^sub>B"
      have zA: "zeroT ?A" using m_7_3_Trans_zeroT[OF Acut_RT] z by simp
      have LA1: "Lng ?A = 1" using zA by (simp add: zeroT_def)
      have AT: "?A \<in> T_PS" using Acut_RT by (simp add: RT_PS_def)
      obtain w where Aw: "?A = [(w, w)]"
        using m_6_6_oneColumn[OF AT] Acut_RT LA1 by auto
      have w0: "w = 0" using zA by (simp add: zeroT_def Aw entry_def)
      have "P ?A = [?A]" by (rule poper_P_nonmulti) (simp add: Aw)
      hence "P ?A ! 0 = [(0, 0)]" using Aw w0 by simp
      thus False using P0Ane by simp
    qed
    \<comment> \<open>\<open>Lng (PB (Trans ?A)) \<ge> 1\<close>\<close>
    have pbA: "1 \<le> Lng (PB (Trans ?A))"
    proof -
      have "Lng (PB (Trans ?A)) \<noteq> 0"
        using TAne by (subst Lng_PB_eq0_iff) simp
      thus ?thesis by linarith
    qed
    \<comment> \<open>\<open>Lng (PB (right summand)) \<ge> 1\<close> in both branches\<close>
    have pbR: "1 \<le> Lng (PB (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B else Trans ?PJ))"
    proof (cases "?PJ = [(0, 0)]")
      case True
      thus ?thesis by (simp add: PB_def)
    next
      case PJne: False
      \<comment> \<open>\<open>?PJ\<close> is the last \<open>P\<close>-component: reduced; non-\<open>((0,0))\<close> means non-zero\<close>
      have PJin: "?PJ \<in> set (P M)" using PMsplit by simp
      have PJRT: "?PJ \<in> RT_PS"
        using m_6_6_P_reduced[OF MT] MR PJin by (metis in_set_conv_nth)
      have nzPJ: "\<not> zeroT ?PJ"
      proof
        assume zPJ: "zeroT ?PJ"
        have "Lng ?PJ = 1" using zPJ by (simp add: zeroT_def)
        have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
        obtain w where PJw: "?PJ = [(w, w)]"
          using m_6_6_oneColumn[OF PJT] PJRT \<open>Lng ?PJ = 1\<close> by auto
        have "w = 0" using zPJ by (simp add: zeroT_def PJw entry_def)
        thus False using PJne PJw by simp
      qed
      have tPJne: "Trans ?PJ \<noteq> 0\<^sub>B" using m_7_3_Trans_zeroT[OF PJRT] nzPJ by simp
      have "Lng (PB (Trans ?PJ)) \<noteq> 0"
        using tPJne by (subst Lng_PB_eq0_iff) simp
      hence "1 \<le> Lng (PB (Trans ?PJ))" by linarith
      thus ?thesis using PJne by simp
    qed
    have transM': "Trans M = Trans ?A
        +\<^sub>B (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B else Trans ?PJ)"
      using transM by (cases "?PJ = [(0, 0)]") simp_all
    have "Lng (PB (Trans M))
            = Lng (PB (Trans ?A))
              + Lng (PB (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B else Trans ?PJ))"
      by (subst transM') (rule Lng_PB_addBT)
    hence "2 \<le> Lng (PB (Trans M))" using pbA pbR by linarith
    thus False using pb1 by simp
  qed
qed



text \<open>命題（\<open>Trans\<close>が単項性を保つこと） (§7.3, 2358).  A \<open>BT\<close> term is principal
  (\<open>\<in> PT\<^bsub>B\<^esub>\<close>) iff it has a single principal component, i.e. \<open>Lng (P\<^bsub>B\<^esub> t) = 1\<close>.

  CORRECTION A16: the transcribed exceptional-disjunct form
  \<open>monoT M \<longleftrightarrow> (Lng (PB (Trans M)) = 1 \<or> (zeroT (P M ! 0) \<and> Lng (P M) = 2))\<close>
  is FALSE (53 counterexamples, e.g. \<open>M = [(0,0),(0,0),(1,1)]\<close> is \<open>multiT\<close> but
  \<open>Trans M\<close> is single AND the right disjunct holds — the disjunct was added in the
  wrong direction).  The empirically true form (1269 reduced cases, 0 CEX)
  restricts to a non-zero first \<open>P\<close>-component: under \<open>\<not> zeroT (P M ! 0)\<close>,
  \<open>monoT M \<longleftrightarrow> Lng (PB (Trans M)) = 1\<close>.  Stated \<open>RT\<^bsub>PS\<^esub>\<close>-restricted (the §7.3
  convention; \<open>M \<in> T\<^bsub>PS\<^esub>\<close> reduces to \<open>Red M \<in> RT\<^bsub>PS\<^esub>\<close> with \<open>Trans (Red M) = Trans M\<close>).\<close>

lemma p_7_3_Trans_monoT:
  assumes "M \<in> RT_PS" "\<not> zeroT (P M ! 0)"
  shows "monoT M \<longleftrightarrow> Lng (PB (Trans M)) = 1"
  using assms by (rule m_7_3_Trans_monoT)

end

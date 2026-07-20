theory Support_7_037
  imports Frontier_7_042
begin

text \<open>The leftmost principal component of \<open>Trans M\<close> (the article's 最左単項成分):
  the deep clause (2).  By strong \<open>Lng\<close>-induction mirroring
  @{thm [source] m_7_3_Trans_leftend}.  In the mono branch \<open>P M = [M]\<close> and
  \<open>Trans M\<close> is single-principal (@{thm [source] Trans_PT_single}); in the multi
  branch \<open>Trans M = Trans (take (Pcut M) M) +\<^sub>B \<dots>\<close> and the first \<open>P\<close>-component is
  preserved (@{thm [source] poper_P_multi}), so the leftmost PC recurses into the
  prefix.  The hypothesis \<open>P M ! 0 \<noteq> ((0,0))\<close> rules out the \<open>Trans (prefix) = 0\<^sub>B\<close>
  sub-case (verified empirically vacuous).\<close>

lemma m_7_3_Trans_leftmost_pc:
  "M \<in> RT_PS \<longrightarrow> P M ! 0 \<noteq> [(0, 0)] \<longrightarrow> PB (Trans M) ! 0 = Trans (P M ! 0)"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (intro impI)
    assume MR: "M \<in> RT_PS" and P0ne: "P M ! 0 \<noteq> [(0, 0)]"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    show "PB (Trans M) ! 0 = Trans (P M ! 0)"
    proof (cases "Lng M = 1")
      case True
      \<comment> \<open>(A) length 1: \<open>M = [(v,v)]\<close>, \<open>P M = [M]\<close>, \<open>v \<noteq> 0\<close>\<close>
      obtain v where Mv: "M = [(v, v)]"
        using m_6_6_oneColumn[OF MT] MR True by auto
      have PMm: "P M = [M]" by (rule poper_P_nonmulti) (simp add: Mv)
      have P0M: "P M ! 0 = M" using PMm by simp
      have vne: "v \<noteq> 0" using P0ne P0M Mv by auto
      have tv: "Trans M = Dpt (enat v) 0\<^sub>B"
        using Mv Trans_singleton vne by simp
      have "PB (Trans M) ! 0 = Trans M"
        by (rule PB0_principal) (simp add: tv PB_def)
      thus ?thesis using P0M by simp
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      have nzM: "\<not> zeroT M" using notone by (auto simp: zeroT_def)
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        \<comment> \<open>(B) mono: \<open>P M = [M]\<close>, \<open>Trans M\<close> single-principal\<close>
        have PMm: "P M = [M]"
          by (rule poper_P_nonmulti) (simp add: mono multiT_def)
        have P0M: "P M ! 0 = M" using PMm by simp
        \<comment> \<open>\<open>Trans M \<noteq> 0\<^sub>B\<close> since \<open>M\<close> is not zero (leftend core gives nonzero head when
           \<open>entry M 1 0 \<noteq> 0\<close>; but we need it unconditionally here)\<close>
        have tne: "Trans M \<noteq> 0\<^sub>B"
        proof
          assume z: "Trans M = 0\<^sub>B"
          have "zeroT M" using m_7_3_Trans_zeroT[OF MR] z by simp
          thus False using nzM by simp
        qed
        obtain p where tp: "Trans M = Trm [p]"
          using Trans_PT_single MR mono tne by blast
        have "PB (Trans M) ! 0 = Trans M"
          by (rule PB0_principal) (simp add: tp PB_def)
        thus ?thesis using P0M by simp
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
        \<comment> \<open>\<open>P\<close>-decomposition: \<open>P M = P ?A @ [?PJ]\<close>, so \<open>P M ! 0 = P ?A ! 0\<close>\<close>
        have PMsplit: "P M = P ?A @ [?PJ]"
          by (rule poper_P_multi) (use muM L in simp)
        have PAne: "P ?A \<noteq> []" by (rule P_nonempty)
        have P0eq: "P M ! 0 = P ?A ! 0"
          using PMsplit PAne by (simp add: nth_append)
        have P0Ane: "P ?A ! 0 \<noteq> [(0, 0)]" using P0ne P0eq by simp
        note IHA = less.IH[OF LA, THEN mp, OF Acut_RT, THEN mp, OF P0Ane]
        \<comment> \<open>the multi recursion value (copy from @{thm [source] m_7_3_Trans_leftend})\<close>
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
          have "entry ?A 1 0 = w" using Aw by (simp add: entry_def)
          hence w0: "w = 0" using zA by (simp add: zeroT_def Aw entry_def)
          have "P ?A = [?A]" by (rule poper_P_nonmulti) (simp add: Aw)
          hence "P ?A ! 0 = [(0, 0)]" using Aw w0 by simp
          thus False using P0Ane by simp
        qed
        \<comment> \<open>leftmost PC of \<open>Trans M\<close> = leftmost PC of \<open>Trans ?A\<close> = \<open>Trans (P ?A ! 0)\<close>\<close>
        have "PB (Trans M) ! 0 = PB (Trans ?A) ! 0"
        proof (cases "?PJ = [(0, 0)]")
          case True
          have "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM True by simp
          thus ?thesis using PB0_addBT_left[OF TAne] by simp
        next
          case False
          have "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM False by simp
          thus ?thesis using PB0_addBT_left[OF TAne] by simp
        qed
        also have "\<dots> = Trans (P ?A ! 0)" using IHA .
        also have "\<dots> = Trans (P M ! 0)" using P0eq by simp
        finally show ?thesis .
      qed
    qed
  qed
qed

end

theory Frontier_7_022
  imports P_7_3_c1_c2
begin

section \<open>§7.3 命題（\<open>Pred\<close>-on-\<open>Trans\<close> descent）: \<open>lessBT (Trans (Pred M)) (Trans M)\<close>\<close>

text \<open>The multi-term \<open>Pred\<close>-evaluation helper.  For \<open>M \<in> RT\<^sub>PS\<close> multi with a
  non-trivial last \<open>P\<close>-component \<open>PJ = drop (Pcut M) M\<close> (\<open>1 < Lng PJ\<close>), the
  predecessor acts inside that last component: \<open>Pred M = A @ Pred PJ\<close> with
  \<open>A = take (Pcut M) M\<close>, and \<open>Pred M\<close> is itself multi with the SAME cut, prefix
  \<open>A\<close>, last component \<open>Pred PJ\<close>.  Hence \<open>Trans\<close> evaluates the same way:
  \<open>Trans (Pred M) = Trans A +\<^sub>B (if Pred PJ = [(0,0)] then D\<^bsub>0\<^esub> 0 else Trans (Pred PJ))\<close>.
  Built from @{thm [source] pred_P_decomp} + @{thm [source] poper_last_P_multi}.\<close>

lemma Trans_Pred_multi_last:
  assumes MR: "M \<in> RT_PS" and mu: "multiT M"
    and LPJ: "1 < Lng (drop (Pcut M) M)"
  shows "Trans (Pred M)
         = Trans (take (Pcut M) M)
           +\<^sub>B (if Pred (drop (Pcut M) M) = [(0,0)] then Dpt 0 0\<^sub>B
                else Trans (Pred (drop (Pcut M) M)))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  let ?c = "Pcut M"
  let ?A = "take ?c M"
  let ?PJ = "drop ?c M"
  have cut: "0 < ?c \<and> ?c \<le> Lng M - 1" using Pcut_le[OF L] by simp
  have lastPM: "last (P M) = ?PJ" using poper_last_P_multi[OF mu L] by simp
  have LdropPJ: "Lng ?PJ = Lng M - ?c" by simp
  have cltj1: "?c < Lng M - 1"
  proof -
    have "Lng ?PJ = Lng M - ?c" by simp
    thus ?thesis using LPJ cut by linarith
  qed
  have lenlast_gt1: "1 < Lng (last (P M))" using lastPM LPJ by simp
  \<comment> \<open>\<open>Pred M = A @ Pred PJ\<close>\<close>
  have predsplit: "Pred M = ?A @ Pred ?PJ"
    by (rule poper_Pred_split[OF cltj1 L])
  \<comment> \<open>P-decomposition of \<open>Pred M\<close>: butlast (P M) @ [Pred (last (P M))]\<close>
  have Pdec: "P (Pred M) = butlast (P M) @ [Pred (last (P M))]"
    using pred_P_decomp[OF MT mu] lenlast_gt1 by simp
  have Pdec2: "P (Pred M) = P ?A @ [Pred ?PJ]"
  proof -
    have "butlast (P M) = P ?A" using poper_last_P_multi[OF mu L] by simp
    thus ?thesis using Pdec lastPM by simp
  qed
  \<comment> \<open>\<open>Pred M\<close> is reduced, in \<open>T_PS\<close>, and multi (its \<open>P\<close> has \<open>length > 1\<close>)\<close>
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
  have PAne: "P ?A \<noteq> []" by (rule P_nonempty)
  have lenPpred: "1 < length (P (Pred M))"
    using Pdec2 PAne by (cases "P ?A") auto
  have mupred: "multiT (Pred M)"
    using m_6_2_P_components_2[OF predT] lenPpred by simp
  have Lpred: "1 < Lng (Pred M)"
    by (rule multiT_imp_Lng_gt1[OF predT mupred])
  \<comment> \<open>cut of \<open>Pred M\<close>: its last \<open>P\<close>-component is \<open>Pred PJ = drop (Pcut (Pred M)) (Pred M)\<close>\<close>
  let ?cP = "Pcut (Pred M)"
  have lastPpred: "last (P (Pred M)) = drop ?cP (Pred M)
                   \<and> butlast (P (Pred M)) = P (take ?cP (Pred M))"
    by (rule poper_last_P_multi[OF mupred Lpred])
  have lastval: "last (P (Pred M)) = Pred ?PJ"
    using Pdec2 by simp
  have dropPred: "drop ?cP (Pred M) = Pred ?PJ"
    using lastPpred lastval by simp
  \<comment> \<open>\<open>take (Pcut (Pred M)) (Pred M) = A\<close>: from \<open>Pred M = A @ Pred PJ\<close> and the drop\<close>
  have takePred: "take ?cP (Pred M) = ?A"
  proof -
    have "take ?cP (Pred M) @ drop ?cP (Pred M) = Pred M" by simp
    hence "take ?cP (Pred M) @ Pred ?PJ = ?A @ Pred ?PJ"
      using dropPred predsplit by simp
    thus ?thesis by simp
  qed
  \<comment> \<open>evaluate \<open>Trans (Pred M)\<close> via the multi recursion\<close>
  have domTP: "Trans_Mark_dom (Inl (Pred M))" by (rule m_7_3_Trans_welldef[OF predRT])
  have LgtP: "\<not> Lng (Pred M) \<le> Suc 0" using Lpred by simp
  have nmonoP: "\<not> monoT (Pred M)" using mupred by (simp add: multiT_def)
  have PJeqP: "P (Pred M) ! (Lng (P (Pred M)) - 1) = drop ?cP (Pred M)"
    by (rule trans_multiT_last_component(1)[OF predT mupred])
  have j0eqP: "Lng (Pred M) - 1 - Lng (P (Pred M) ! (Lng (P (Pred M)) - 1)) + 1 = ?cP"
    by (rule trans_multiT_last_component(2)[OF predT mupred])
  have c1: "(Pred M \<notin> RT_PS) = False" using predRT by simp
  have c2: "(Lng (Pred M) - 1 = 0) = False" using Lpred by simp
  have c3: "monoT (Pred M) = False" using nmonoP by simp
  have cutP: "0 < ?cP \<and> ?cP \<le> Lng (Pred M) - 1" using Pcut_le[OF Lpred] by simp
  have LdJP: "Lng (drop ?cP (Pred M)) = Lng (Pred M) - ?cP" by simp
  have AeqP: "seg (Pred M) 0 (Lng (Pred M) - 1 - Lng (drop ?cP (Pred M)) + 1 - 1)
              = take ?cP (Pred M)"
  proof -
    have "Lng (Pred M) - 1 - Lng (drop ?cP (Pred M)) + 1 - 1 = ?cP - 1"
      using LdJP cutP by linarith
    moreover have "seg (Pred M) 0 (?cP - 1) = take (Suc (?cP - 1)) (Pred M)"
      by (rule seg_0_eq_take) (use cutP Lpred in linarith)
    moreover have "Suc (?cP - 1) = ?cP" using cutP by simp
    ultimately show ?thesis by simp
  qed
  have transP: "Trans (Pred M)
      = (if drop ?cP (Pred M) = [(0,0)] then Trans (take ?cP (Pred M)) +\<^sub>B Dpt 0 0\<^sub>B
         else Trans (take ?cP (Pred M)) +\<^sub>B Trans (drop ?cP (Pred M)))"
  proof -
    have raw: "Trans (Pred M) =
        (if P (Pred M) ! (Lng (P (Pred M)) - 1) = [(0, 0)]
         then Trans (seg (Pred M) 0
                 (Lng (Pred M) - 1 - Lng (P (Pred M) ! (Lng (P (Pred M)) - 1)) + 1 - 1))
                +\<^sub>B Dpt 0 0\<^sub>B
         else Trans (seg (Pred M) 0
                 (Lng (Pred M) - 1 - Lng (P (Pred M) ! (Lng (P (Pred M)) - 1)) + 1 - 1))
                +\<^sub>B Trans (P (Pred M) ! (Lng (P (Pred M)) - 1)))"
      by (subst Trans.psimps[OF domTP]) (simp only: c1 c2 c3 if_False Let_def)
    show ?thesis unfolding raw PJeqP AeqP ..
  qed
  \<comment> \<open>rewrite using \<open>take = A\<close> and \<open>drop = Pred PJ\<close>; the left guard never fires\<close>
  have notPJ00: "?PJ \<noteq> [(0,0)]"
  proof
    assume "?PJ = [(0,0)]"
    hence "Lng ?PJ = 1" by simp
    thus False using LPJ by simp
  qed
  show ?thesis
    using transP takePred dropPred notPJ00 by simp
qed

end

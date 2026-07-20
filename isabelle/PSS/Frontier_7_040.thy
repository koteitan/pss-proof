theory Frontier_7_040
  imports Support_7_034
begin

section \<open>§7.3 \<open>Pred\<close> preserves \<open>PT\<^bsub>PS\<^esub>\<close> on the \<open>t\<^sub>1 \<noteq> 0\<close> branch (helper for (d)/(e))\<close>

text \<open>For \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> with \<open>j\<^sub>1 > 0\<close> and \<open>t\<^sub>1 = Trans (Pred M) \<noteq> 0\<close>, the
  predecessor \<open>Pred M\<close> is again reduced and mono.  Reducedness is
  @{thm [source] Pred_RT_PS}; monotonicity is the article's
  「単項性の始切片への遺伝性」, here via @{thm [source] m_6_2_mono_prefix}
  (length-\<open>1\<close> case from \<open>t\<^sub>1 \<noteq> 0\<close>).\<close>

lemma Pred_PT_PS_t1ne:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
  shows "Pred M \<in> RT_PS" and "Pred M \<in> PT_PS"
proof -
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using J1pos by (simp add: transJ1_def)
  show predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
  have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B" using T1 by (simp add: transT1_def)
  have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
  have predmono: "monoT (Pred M)"
  proof (cases "Lng (Pred M) = 1")
    case True
    obtain v where Pv: "Pred M = [(v, v)]"
      using m_6_6_oneColumn[OF predT] predRT True by auto
    have "Trans (Pred M) = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
      using Pv Trans_singleton[of v] by simp
    hence vnz: "v \<noteq> 0" using t1ne by (cases "v = 0") auto
    have nz: "\<not> zeroT (Pred M)" using Pv vnz by (simp add: zeroT_def entry_def)
    have "leR (Pred M) 0 0 (Lng (Pred M) - 1)"
      using True by (simp add: leR_def le0_def)
    thus ?thesis using nz by (simp add: monoT_def)
  next
    case False
    have L2: "1 < Lng M - 1" using L False predb by simp
    have j0pos: "0 < Lng M - 2" using L2 by simp
    have j0lt: "Lng M - 2 < Lng M" using L by simp
    have mp: "monoT (seg M 0 (Lng M - 2))"
      by (rule m_6_2_mono_prefix[OF MP j0pos j0lt])
    have "seg M 0 (Lng M - 2) = butlast M"
    proof -
      have suc: "Suc (Lng M - 2) \<le> Lng M" using L2 by simp
      have "seg M 0 (Lng M - 2) = take (Suc (Lng M - 2)) M"
        by (rule seg_0_eq_take[OF suc])
      also have "Suc (Lng M - 2) = Lng M - 1" using L2 by simp
      also have "take (Lng M - 1) M = butlast M" by (simp add: butlast_conv_take)
      finally show ?thesis .
    qed
    thus ?thesis using mp predb by simp
  qed
  show "Pred M \<in> PT_PS" using predT predmono by (simp add: PT_PS_def)
qed

end

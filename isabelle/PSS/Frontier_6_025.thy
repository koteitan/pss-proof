theory Frontier_6_025
  imports Support_6_007
begin

subsection \<open>§6.7 標準形の始切片への遺伝性\<close>

text \<open>補助補題: \<open>ST_PS \<subseteq> T_PS\<close>  (diagSeq non-empty; oper preserves non-emptiness)\<close>

lemma ST_PS_T_PS:
  assumes "M \<in> ST_PS"
  shows "M \<in> T_PS"
using assms proof (induct M rule: ST_PS.induct)
  case (diag u v)
  \<comment> \<open>diag.hyps: u ≤ v\<close>
  have "diagSeq u v \<noteq> []"
    unfolding diagSeq_def using diag by simp
  thus "diagSeq u v \<in> T_PS" by (simp add: T_PS_def)
next
  case (oper M n)
  have MT: "M \<in> T_PS" by (rule oper.hyps(2))
  have n1: "1 \<le> n" by (rule oper.hyps(3))
  show "(M::pairseq)[n] \<in> T_PS"
  proof (cases "Lng M \<le> 1")
    case True
    have LM1: "Lng M = 1" using MT True
      by (simp add: T_PS_def; cases M; auto)
    hence "(M::pairseq)[n] = M"
      by (simp add: oper_def Let_def)
    thus ?thesis using MT by simp
  next
    case False
    hence L: "Lng M > 1" by simp
    have "(M::pairseq)[n] \<noteq> []"
      using poper_oper_nth0[OF MT L n1] by simp
    thus ?thesis by (simp add: T_PS_def)
  qed
qed

text \<open>m: 命題（標準形の始切片への遺伝性） — discharges @{text p_6_7_standard_prefix}.
  (§6.7, 命題（標準形の始切片への遺伝性）)

  Proof: induction on \<open>d = Lng M - 1 - j1'\<close>.
  \<^item> Base (\<open>d = 0\<close>): \<open>j1' = Lng M - 1\<close>, so \<open>seg M 0 j1' = M \<in> ST_PS\<close>.
  \<^item> Step (\<open>d = Suc d'\<close>): \<open>j1' \<le> Lng M - 2\<close>, so \<open>Lng M > 1\<close>.
    Apply \<open>m_5_3_pred_is_oper1\<close> (requires \<open>M \<in> T_PS\<close>, \<open>Lng M > 1\<close>) to get
    \<open>M[1] = Pred M\<close>.  Then \<open>M[1] \<in> ST_PS\<close> (oper rule) and
    \<open>seg M 0 j1' = seg (M[1]) 0 j1'\<close> (both are \<open>take (Suc j1') M\<close>).
    IH applies to \<open>(M[1], j1')\<close> with measure \<open>d'\<close>.\<close>

text \<open>核心補題 (inner): induction on d = Lng M - 1 - j1'.\<close>

lemma ST_PS_seg_0_inner:
  "\<forall>M j1'. M \<in> ST_PS \<longrightarrow> j1' \<le> Lng M - 1 \<longrightarrow> Lng M - 1 - j1' = d \<longrightarrow> seg M 0 j1' \<in> ST_PS"
proof (induction d rule: less_induct)
  case (less d)
  show ?case
  proof (intro allI impI)
    fix M :: pairseq and j1' :: nat
    assume MST: "M \<in> ST_PS"
    assume j1'le: "j1' \<le> Lng M - 1"
    assume deq: "Lng M - 1 - j1' = d"
    have MT: "M \<in> T_PS" by (rule ST_PS_T_PS[OF MST])
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have lM: "Suc j1' \<le> Lng M" using j1'le Mne by (cases M; auto)
    show "seg M 0 j1' \<in> ST_PS"
    proof (cases "j1' = Lng M - 1")
      case True
      \<comment> \<open>j1' = Lng M - 1: seg M 0 j1' = M ∈ ST_PS.\<close>
      have "seg M 0 j1' = take (Suc j1') M"
        by (rule seg_0_eq_take[OF lM])
      also have "\<dots> = M" using lM True by simp
      finally show ?thesis using MST by simp
    next
      case False
      \<comment> \<open>j1' < Lng M - 1: use M[1] = Pred M.\<close>
      have j1'lt: "j1' < Lng M - 1" using j1'le False by linarith
      have L: "Lng M > 1" using j1'lt by linarith
      \<comment> \<open>M[1] = Pred M\<close>
      have pred_eq: "Pred M = (M::pairseq)[1]"
        by (rule m_5_3_pred_is_oper1[OF MT L])
      \<comment> \<open>M[1] ∈ ST_PS\<close>
      have M1ST: "(M::pairseq)[1] \<in> ST_PS"
        by (rule ST_PS.oper[OF MST]) simp
      \<comment> \<open>Lng(M[1]) = Lng M - 1\<close>
      have predL: "Lng (Pred M) = Lng M - 1"
        using L by (simp add: Pred_def)
      have M1L: "Lng ((M::pairseq)[1]) = Lng M - 1"
        using predL pred_eq by simp
      \<comment> \<open>j1' ≤ Lng(M[1]) - 1\<close>
      have j1'le': "j1' \<le> Lng ((M::pairseq)[1]) - 1"
        using j1'lt M1L by linarith
      \<comment> \<open>Measure d' = Lng(M[1]) - 1 - j1' < d = Lng M - 1 - j1'\<close>
      have d'eq: "Lng ((M::pairseq)[1]) - 1 - j1' = d - 1"
        using deq M1L by linarith
      have dlt: "d - 1 < d" using deq j1'lt by linarith
      \<comment> \<open>seg M 0 j1' = seg (M[1]) 0 j1'\<close>
      have Sj1'le: "Suc j1' \<le> Lng M - 1" using j1'lt by linarith
      have predM_take: "Pred M = take (Lng M - 1) M"
        using L by (simp add: Pred_def butlast_conv_take)
      have seg_M: "seg M 0 j1' = take (Suc j1') M"
        by (rule seg_0_eq_take[OF lM])
      have lM1: "Suc j1' \<le> Lng ((M::pairseq)[1])"
        using j1'lt M1L by linarith
      have seg_M1: "seg ((M::pairseq)[1]) 0 j1' = take (Suc j1') ((M::pairseq)[1])"
        by (rule seg_0_eq_take[OF lM1])
      have take_M1_eq_take_M: "take (Suc j1') ((M::pairseq)[1]) = take (Suc j1') M"
      proof -
        have "take (Suc j1') ((M::pairseq)[1]) = take (Suc j1') (Pred M)"
          using pred_eq by simp
        also have "\<dots> = take (Suc j1') (take (Lng M - 1) M)"
          using predM_take by simp
        also have "\<dots> = take (Suc j1') M"
          using Sj1'le by (simp add: take_take min_def)
        finally show ?thesis .
      qed
      have seg_same: "seg M 0 j1' = seg ((M::pairseq)[1]) 0 j1'"
        using seg_M seg_M1 take_M1_eq_take_M by simp
      \<comment> \<open>Apply IH to (M[1], j1') with d-1 < d.\<close>
      have "seg ((M::pairseq)[1]) 0 j1' \<in> ST_PS"
        using less.IH[rule_format, OF dlt M1ST j1'le' d'eq] .
      thus ?thesis using seg_same by simp
    qed
  qed
qed

end

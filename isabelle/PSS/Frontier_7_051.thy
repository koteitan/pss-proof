theory Frontier_7_051
  imports Support_7_046
begin

text \<open>Strict \<open>Trans\<close>-descent along the \<open>take\<close>-prefix chain.  A proper reduced
  initial slice \<open>take n M\<close> (\<open>0 < n < Lng M\<close>) has \<open>Trans\<close> strictly below \<open>Trans M\<close>.
  Built by iterating @{thm [source] m_7_3_Pred_Trans_descend}, using
  \<open>Pred (take (Suc k) M) = take k M\<close> and that every initial slice is reduced
  (@{thm [source] seg_0_RT_PS} / @{thm [source] Pred_pow_RT_PS}).\<close>

lemma Trans_take_lessBT:
  assumes M: "M \<in> RT_PS" and npos: "0 < n" and nlt: "n < Lng M"
  shows "lessBT (Trans (take n M)) (Trans M)"
proof -
  \<comment> \<open>generalise the upper endpoint: descend from \<open>take n M\<close> up to \<open>take (n + d) M\<close>\<close>
  have gen: "\<And>d. n + d \<le> Lng M \<Longrightarrow> 0 < d
              \<Longrightarrow> lessBT (Trans (take n M)) (Trans (take (n + d) M))"
  proof -
    fix d :: nat
    show "n + d \<le> Lng M \<Longrightarrow> 0 < d
            \<Longrightarrow> lessBT (Trans (take n M)) (Trans (take (n + d) M))"
    proof (induction d)
      case 0
      thus ?case by simp
    next
      case (Suc d)
      have hi: "Suc (n + d) \<le> Lng M" using Suc.prems(1) by simp
      have hiLe: "n + d \<le> Lng M - 1" using hi by simp
      \<comment> \<open>\<open>take (Suc (n + d)) M\<close> is reduced and has length \<open>> 1\<close>\<close>
      have UR: "take (Suc (n + d)) M \<in> RT_PS"
      proof -
        have "take (Suc (n + d)) M = seg M 0 (n + d)"
          using seg_0_eq_take[OF hi] by simp
        moreover have "seg M 0 (n + d) \<in> RT_PS"
          by (rule seg_0_RT_PS[OF M hiLe])
        ultimately show ?thesis by simp
      qed
      have LU: "Lng (take (Suc (n + d)) M) = Suc (n + d)"
        using length_take min_absorb2 hi by simp
      have LUgt1: "1 < Lng (take (Suc (n + d)) M)" unfolding LU using npos by simp
      have LUnle: "\<not> Lng (take (Suc (n + d)) M) \<le> 1" unfolding LU using npos by simp
      \<comment> \<open>\<open>Pred (take (Suc (n + d)) M) = take (n + d) M\<close>\<close>
      have predeq: "Pred (take (Suc (n + d)) M) = take (n + d) M"
      proof -
        have "Pred (take (Suc (n + d)) M) = butlast (take (Suc (n + d)) M)"
          unfolding Pred_def using LUnle by (rule if_not_P)
        also have "\<dots> = take (n + d) M"
          using butlast_take[OF hi] by simp
        finally show ?thesis .
      qed
      \<comment> \<open>one descent step (instantiate the descent lemma at \<open>take (Suc (n + d)) M\<close>)\<close>
      have descend: "lessBT (Trans (Pred (take (Suc (n + d)) M)))
                            (Trans (take (Suc (n + d)) M))"
        using m_7_3_Pred_Trans_descend[rule_format, OF UR LUgt1] .
      have step: "lessBT (Trans (take (n + d) M)) (Trans (take (Suc (n + d)) M))"
        using descend predeq by simp
      show ?case
      proof (cases "0 < d")
        case True
        have IH: "lessBT (Trans (take n M)) (Trans (take (n + d) M))"
          using Suc.IH[OF _ True] hi by simp
        show ?thesis using lessBT_trans[OF IH step] by simp
      next
        case False
        hence d0: "d = 0" by simp
        thus ?thesis using step by simp
      qed
    qed
  qed
  \<comment> \<open>instantiate at \<open>d = Lng M - n\<close>, where \<open>take (Lng M) M = M\<close>\<close>
  let ?d = "Lng M - n"
  have dpos: "0 < ?d" using nlt by simp
  have sum: "n + ?d = Lng M" using nlt by simp
  have "lessBT (Trans (take n M)) (Trans (take (n + ?d) M))"
    using gen[of ?d] sum dpos by simp
  thus ?thesis using sum by simp
qed

end

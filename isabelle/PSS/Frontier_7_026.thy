theory Frontier_7_026
  imports P_7_4_Trans_Mark_seg
begin

section \<open>§7.4 系（\<open>RightNodes\<close> と \<open>Mark\<close> の関係） — m_7_4_RightNodes_Mark\<close>

text \<open>Helper: an iterated \<open>Pred\<close> on a reduced sequence stays reduced
  (@{thm [source] Pred_RT_PS} iterated).\<close>

lemma Pred_pow_RT_PS:
  assumes "M \<in> RT_PS"
  shows "(Pred ^^ k) M \<in> RT_PS"
proof (induction k)
  case 0
  thus ?case using assms by simp
next
  case (Suc k)
  have step: "(Pred ^^ Suc k) M = Pred ((Pred ^^ k) M)"
    by (simp only: funpow.simps o_apply)
  show ?case unfolding step by (rule Pred_RT_PS[OF Suc.IH])
qed

text \<open>Helper: a trunk-anchored initial slice \<open>seg M 0 m\<close> (\<open>m \<le> Lng M - 1\<close>) of a
  reduced \<open>M\<close> is reduced.  This is @{thm [source] herd_6_6_reduced_slice} without
  its \<open>TrMax M \<le> m\<close> hypothesis (empirically unneeded): \<open>seg M 0 m = (Pred ^^ k) M\<close>
  for \<open>k = Lng M - 1 - m\<close> (@{thm [source] herd_Pred_pow_take}), and iterated
  \<open>Pred\<close> preserves reducedness (@{thm [source] Pred_pow_RT_PS}).\<close>

lemma seg_0_RT_PS:
  assumes M: "M \<in> RT_PS" and hi: "m \<le> Lng M - 1"
  shows "seg M 0 m \<in> RT_PS"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  let ?k = "Lng M - 1 - m"
  have kLt: "?k < Lng M" using LMpos by linarith
  have LmkE: "Lng M - ?k = Suc m" using hi LMpos by linarith
  have segtake: "seg M 0 m = take (Suc m) M"
    by (rule seg_0_eq_take) (use hi LMpos in linarith)
  have segpow: "seg M 0 m = (Pred ^^ ?k) M"
  proof -
    have "(Pred ^^ ?k) M = take (Lng M - ?k) M" by (rule herd_Pred_pow_take[OF kLt])
    also have "\<dots> = take (Suc m) M" using LmkE by simp
    finally show ?thesis using segtake by simp
  qed
  show ?thesis using segpow Pred_pow_RT_PS[OF M, of ?k] by simp
qed

end

theory P_6_6_reduced_slice
  imports Frontier_6_059
begin

subsection \<open>§6.6 簡約性\<close>

text \<open>命題（簡約性の切片への遺伝性） — a reduced sequence restricts to a reduced
  initial slice (from the trunk root) across the trunk end.
  CORRECTION A5: the article's premise \<open>j0' \<le> TrMax M\<close> is too weak (false for
  e.g. the standard reduced M = (0,0)(1,1)(1,0), slice seg M 1 2); corrected to
  \<open>j0' = 0\<close> (empirically sound, python/red_66_audit.py).  Final premise pending.\<close>

text \<open>命題（簡約性の切片への遺伝性） — a reduced \<open>M\<close> restricts to a reduced
  trunk-anchored initial slice \<open>seg M 0 j\<^sub>1'\<close> (with \<open>TrMax M \<le> j\<^sub>1' \<le> Lng M - 1\<close>;
  domain correction A5: \<open>j\<^sub>0' = 0\<close>).  Article proof (content.md 1026\<dash>1032): from
  \<open>Red\<close>'s recursive definition and the commutativity of \<open>Red\<close> with \<open>Pred\<close>.
  Mechanized: \<open>seg M 0 j\<^sub>1' = (Pred^^k) M\<close> for \<open>k = Lng M - 1 - j\<^sub>1'\<close>
  (@{thm [source] herd_Pred_pow_take}); \<open>Red\<close> commutes with \<open>Pred^^k\<close>
  (@{thm [source] herd_Red_Pred_pow}); and \<open>Red M = M\<close> from \<open>M \<in> RT\<^sub>PS\<close>, so
  \<open>Red (seg M 0 j\<^sub>1') = (Pred^^k)(Red M) = (Pred^^k) M = seg M 0 j\<^sub>1'\<close>.  Empirically
  sound (python/red_model.py; 447 reduced-slice cases + random, 0 failures).\<close>

lemma herd_6_6_reduced_slice:
  assumes M: "M \<in> RT_PS" and j0: "j0' = 0"
    and lo: "TrMax M \<le> j1'" and hi: "j1' \<le> Lng M - 1"
  shows "seg M j0' j1' \<in> RT_PS"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  \<comment> \<open>let \<open>k = Lng M - 1 - j\<^sub>1'\<close>; then \<open>k < Lng M\<close> and \<open>Lng M - k = Suc j\<^sub>1'\<close>.\<close>
  let ?k = "Lng M - 1 - j1'"
  have kLt: "?k < Lng M" using LMpos by linarith
  have LmkE: "Lng M - ?k = Suc j1'" using hi LMpos by linarith
  \<comment> \<open>\<open>seg M 0 j\<^sub>1' = take (Suc j\<^sub>1') M = (Pred^^k) M\<close>.\<close>
  have segtake: "seg M 0 j1' = take (Suc j1') M"
    by (rule seg_0_eq_take) (use hi LMpos in linarith)
  have segpow: "seg M j0' j1' = (Pred ^^ ?k) M"
  proof -
    have "(Pred ^^ ?k) M = take (Lng M - ?k) M" by (rule herd_Pred_pow_take[OF kLt])
    also have "\<dots> = take (Suc j1') M" using LmkE by simp
    finally show ?thesis using segtake j0 by simp
  qed
  \<comment> \<open>\<open>seg M 0 j\<^sub>1' \<in> T\<^sub>PS\<close> (iterated \<open>Pred\<close> preserves \<open>T\<^sub>PS\<close>).\<close>
  have segT: "seg M j0' j1' \<in> T_PS"
    using segpow herd_Pred_pow_T_PS[OF MT, of ?k] by simp
  \<comment> \<open>\<open>Red\<close> commutes with \<open>Pred^^k\<close> and \<open>Red M = M\<close>.\<close>
  have "Red (seg M j0' j1') = Red ((Pred ^^ ?k) M)" using segpow by simp
  also have "\<dots> = (Pred ^^ ?k) (Red M)" by (rule herd_Red_Pred_pow[OF MT])
  also have "\<dots> = (Pred ^^ ?k) M" using redM by simp
  also have "\<dots> = seg M j0' j1'" using segpow by simp
  finally have redseg: "Red (seg M j0' j1') = seg M j0' j1'" .
  show ?thesis using segT redseg by (simp add: RT_PS_def)
qed


lemma p_6_6_reduced_slice:
  assumes "M \<in> RT_PS" "j0' = 0" "TrMax M \<le> j1'" "j1' \<le> Lng M - 1"  \<comment> \<open>A5: was \<open>j0' \<le> TrMax M\<close>\<close>
  shows "seg M j0' j1' \<in> RT_PS"
  using assms by (rule herd_6_6_reduced_slice)

end

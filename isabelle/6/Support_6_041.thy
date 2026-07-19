theory Support_6_041
  imports Frontier_6_060
begin

text \<open>m (§6.6 keystone (e)-CRUX): prepending the length-\<open>m\<^sub>1\<^sub>0\<close> diagonal
  \<open>diagSeq 0 (m\<^sub>1\<^sub>0-1)\<close> to a mono \<open>M\<close> (with \<open>0 < m\<^sub>1\<^sub>0 \<le> m\<^sub>0\<^sub>0\<close>) commutes with
  @{const Red}: the prefix survives intact and \<open>Red M\<close> appears as the tail.
  Proof: \<open>diagSeq 0 k @ M\<close> and \<open>coreReduce M\<close> share the diagonal and differ only
  by tail-@{const IncrFirst}s, which @{const Red} ignores
  (@{thm [source] ecrux_Red_diag_eq_Red_coreReduce}); and \<open>Red (coreReduce M)\<close>
  is \<open>diagSeq 0 k @ Red M\<close> by @{thm [source] b2_N_eq_diag_RedM}.
  Empirically TRUE 6310/0 (monoT, len\<le>4, vals\<le>4, \<open>0 < m\<^sub>1\<^sub>0 \<le> m\<^sub>0\<^sub>0\<close>).\<close>

lemma m_6_6_Red_diag_prefix:
  assumes mono: "monoT M" and pos: "0 < entry M 1 0" and dom: "entry M 1 0 \<le> entry M 0 0"
  shows "Red (diagSeq 0 (entry M 1 0 - 1) @ M) = diagSeq 0 (entry M 1 0 - 1) @ Red M"
proof -
  let ?k = "entry M 1 0 - 1"
  have "0 < Lng M" using mono by (simp add: monoT_def leR_def le0_def)
  hence Mne: "M \<noteq> []" by auto
  have MT: "M \<in> T_PS" using Mne by (simp add: T_PS_def)
  have r0: "?k < entry M 0 0" using pos dom by linarith
  have step1: "Red (diagSeq 0 ?k @ M) = Red (coreReduce M)"
    by (rule ecrux_Red_diag_eq_Red_coreReduce[OF MT mono r0 pos])
  have step2: "Red (coreReduce M) = diagSeq 0 ?k @ Red M"
    by (rule b2_N_eq_diag_RedM[OF MT mono pos])
  show ?thesis using step1 step2 by simp
qed

end

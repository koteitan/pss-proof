theory Support_6_044
  imports Frontier_6_064
begin

text \<open>RESIDUAL (Front A, wf23-fwd): the SOLE remaining obligation for the GENERAL
  \<S>6.6 keystone forward is \<open>RedCondA\<close> for a reduced \<open>monoT M\<close> with \<open>entry M 1 0 > 0\<close>.

  Empirically TRUE (0 counterexamples over all reduced monoT m10>0 sequences,
  values \<le> 3, lengths \<le> 3; 44 such sequences, every one satisfies RedCondA;
  and the full keystone \<open>reduced \<longleftrightarrow> A\<and>B\<close> has 0 forward failures over all 4368
  T_PS sequences at maxlen 3, val 3).

  Structure (article content.md 1156-1218, N-construction): for the reduced mono
  M with \<open>m\<^sub>1\<^sub>0 > 0\<close>, the diagonal-prefixed \<open>N := diagSeq 0 (m\<^sub>1\<^sub>0-1) @ M\<close> is reduced,
  mono and CORE (\<open>entry N 0 0 = entry N 1 0 = 0\<close>) by
  @{thm [source] m_6_6_reduced_leftend} (with \<open>u = 0\<close>); the keystone core
  @{thm [source] kst_reduced_imp_condAB_monoT_core} gives \<open>RedCondA N\<close>.  Each genuine
  row-\<open>i\<close> parent of \<open>M\<close> transfers cleanly to a parent of \<open>N\<close> shifted by \<open>m\<^sub>1\<^sub>0\<close>
  (verified: 0 transfer failures over the 44 sequences), with entries preserved,
  so \<open>RedCondA N\<close> yields \<open>RedCondA M\<close>.  The diagonal junction only ADDS parents to
  M-columns (never removes one), so it cannot break a genuine M-parent relation —
  but mechanizing the \<open>nextR\<close> parent transfer across the \<open>diagSeq @ M\<close> junction is the
  cut-anchored relation work flagged in docs/reducedness.md \<S>9-17 and is left as the
  residual.  This is NOT circular: it cites only the GREEN core keystone and the
  GREEN @{thm [source] m_6_6_reduced_leftend}, never \<open>Red_le\<close>/\<open>p_6_5_Red_monoT\<close>.\<close>

text \<open>The GENERAL \<S>6.6 keystone forward, modulo the single residual hypothesis.
  When \<open>condA_m10pos\<close> lands on HEAD this becomes unconditional.  Cites only GREEN
  facts (no \<open>p_*\<close> stub, no goal self-reference).\<close>

lemma kst_reduced_imp_condAB:
  assumes condA_m10pos:
    "\<And>N. N \<in> RT_PS \<Longrightarrow> monoT N \<Longrightarrow> 0 < entry N 1 0 \<Longrightarrow> RedCondA N"
  assumes M: "M \<in> RT_PS"
  shows "RedCondA M \<and> RedCondB M"
  by (rule kst_reduced_imp_condAB_cond[OF condA_m10pos M])


text \<open>\<S>6.6 KEYSTONE BACKWARD (monoT core) — foundational bricks (tag pss-wf23-bwd).
  Target: \<open>M \<in> T\<^sub>PS \<Longrightarrow> monoT M \<Longrightarrow> entry M 0 0 = 0 \<Longrightarrow> entry M 1 0 = 0 \<Longrightarrow>
  RedCondA M \<Longrightarrow> RedCondB M \<Longrightarrow> Red M = M\<close>.  Mirror of the forward keystone.
  These bricks are pure-structural (no \<open>Red\<close> unfold) and so \<open>A4\<close>-independent.\<close>

text \<open>Position 0 never has a parent (in either row): \<open>nextR M i j0 0\<close> demands
  \<open>j0 < 0\<close>.  Used by the backward base \<open>M\<^bsub>1,0\<^esub>=0 \<and> RedCondB \<Longrightarrow> M\<^bsub>0,0\<^esub>=0\<close>
  (content.md 1222) and by the \<open>RedCondB\<close> obligation of the rebase \<open>N\<close>.\<close>

lemma m_6_6_no_parent_0:
  shows "\<not> hasParent M i 0"
proof -
  have "\<not> (\<exists>j0. nextR M i j0 0)"
  proof
    assume "\<exists>j0. nextR M i j0 0"
    then obtain j0 where "nextR M i j0 0" by blast
    thus False
      by (cases "i = 0")
         (auto simp: nextR_def nextrel0_def nextrel1_def)
  qed
  thus ?thesis unfolding hasParent_def by blast
qed

text \<open>Backward base value (content.md 1222): \<open>RedCondB M \<Longrightarrow> M\<^bsub>0,0\<^esub> = M\<^bsub>1,0\<^esub>\<close>.
  Position 0 has no row-0 parent (@{thm [source] m_6_6_no_parent_0}), so
  \<open>RedCondB\<close> applies at \<open>j = 0\<close>.  Hence with \<open>M\<^bsub>1,0\<^esub> = 0\<close> we get \<open>M\<^bsub>0,0\<^esub> = 0\<close>.\<close>

lemma m_6_6_RedCondB_row0_eq_row1_at0:
  assumes M: "M \<in> T_PS" and condB: "RedCondB M"
  shows "entry M 0 0 = entry M 1 0"
proof -
  have L: "0 \<le> Lng M - 1" by simp
  have np: "\<not> hasParent M 0 0" by (rule m_6_6_no_parent_0)
  show ?thesis
    using condB np L unfolding RedCondB_def by blast
qed

lemma m_6_6_bwd_e00_from_e10:
  assumes M: "M \<in> T_PS" and condB: "RedCondB M" and e10: "entry M 1 0 = 0"
  shows "entry M 0 0 = 0"
  using m_6_6_RedCondB_row0_eq_row1_at0[OF M condB] e10 by simp

end

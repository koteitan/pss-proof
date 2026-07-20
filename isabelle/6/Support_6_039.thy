theory Support_6_039
  imports P_6_5_Red_Pred
begin

(* ===== block from workflow t2-key ===== *)
text \<open>§6.6 keystone (命題 簡約性と係数の関係), \<open>multiT\<close> branch reduction.
  For a \<open>multiT M\<close>, the keystone iff \<open>M \<in> RT\<^bsub>PS\<^esub> \<longleftrightarrow> RedCondA M \<and> RedCondB M\<close>
  reduces to the per-block keystone iff on every block of \<open>P M\<close>.  This is the
  recursive glue of the article's induction on \<open>j\<^sub>1 = Lng M - 1\<close>: when \<open>M\<close> is
  \<open>multiT\<close> the \<open>Red\<close> recursion descends into the (strictly shorter) blocks
  \<open>P M ! J\<close>, so the per-block iff is the induction hypothesis.  Proven from the
  green foundation bricks only — \<open>m_6_6_P_reduced\<close> (reduced \<open>\<longleftrightarrow>\<close> blockwise
  reduced), \<open>m_6_6_RedCond_P_block\<close> (global \<open>A\<and>B\<close> \<open>\<Longrightarrow>\<close> blockwise \<open>A\<and>B\<close>) and
  \<open>m_6_6_RedCond_concat_lift\<close> (blockwise \<open>A\<and>B\<close> \<open>\<Longrightarrow>\<close> global \<open>A\<and>B\<close>) — so it cites
  no unproven \<open>p_*\<close> and no \<open>Red\<close>-output / idempotency machinery.  Empirically the
  full keystone holds on all of \<open>T\<^bsub>PS\<^esub>\<close> (\<open>python/red_66_audit.py\<close>,
  \<open>reduced_iff_cond\<close> 7380/0); this lemma discharges its \<open>multiT\<close> case modulo the
  per-block iter.\<close>

lemma key_reduced_iff_cond_multi:
  assumes M: "M \<in> T_PS" and multi: "multiT M"
    and IH: "\<forall>J < Lng (P M).
               (P M ! J \<in> RT_PS) \<longleftrightarrow> (RedCondA (P M ! J) \<and> RedCondB (P M ! J))"
  shows "(M \<in> RT_PS) \<longleftrightarrow> (RedCondA M \<and> RedCondB M)"
proof
  assume MR: "M \<in> RT_PS"
  \<comment> \<open>Forward: each block is reduced (\<open>m_6_6_P_reduced\<close>), hence (by the per-block
     iff) satisfies \<open>A\<and>B\<close>; lift to global \<open>A\<and>B\<close> (\<open>m_6_6_RedCond_concat_lift\<close>).\<close>
  have blocksRT: "\<forall>J < Lng (P M). P M ! J \<in> RT_PS"
    using m_6_6_P_reduced[OF M] MR by blast
  have blocksAB: "\<forall>J < length (P M). RedCondA (P M ! J) \<and> RedCondB (P M ! J)"
  proof (intro allI impI)
    fix J assume "J < length (P M)"
    hence J: "J < Lng (P M)" by simp
    have "P M ! J \<in> RT_PS" using blocksRT J by blast
    thus "RedCondA (P M ! J) \<and> RedCondB (P M ! J)" using IH J by blast
  qed
  show "RedCondA M \<and> RedCondB M"
    by (rule m_6_6_RedCond_concat_lift[OF M multi blocksAB])
next
  assume AB: "RedCondA M \<and> RedCondB M"
  hence condA: "RedCondA M" and condB: "RedCondB M" by simp_all
  \<comment> \<open>Backward: global \<open>A\<and>B\<close> gives blockwise \<open>A\<and>B\<close> (\<open>m_6_6_RedCond_P_block\<close>), hence
     (by the per-block iff) each block is reduced; lift to \<open>M \<in> RT\<^bsub>PS\<^esub>\<close>
     (\<open>m_6_6_P_reduced\<close>).\<close>
  have blocksRT: "\<forall>J < Lng (P M). P M ! J \<in> RT_PS"
  proof (intro allI impI)
    fix J assume J: "J < Lng (P M)"
    hence JL: "J < length (P M)" by simp
    have "RedCondA (P M ! J) \<and> RedCondB (P M ! J)"
      by (rule m_6_6_RedCond_P_block[OF M multi condA condB JL])
    thus "P M ! J \<in> RT_PS" using IH J by blast
  qed
  show "M \<in> RT_PS" using m_6_6_P_reduced[OF M] blocksRT by blast
qed

end

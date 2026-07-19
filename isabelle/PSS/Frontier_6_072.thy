theory Frontier_6_072
  imports Support_6_051
begin

subsection \<open>Front B (tag pss-stps-condA): \<open>ST_PS \<Longrightarrow> RedCondA\<close> bricks\<close>

text \<open>\<open>Pred\<close> preserves \<open>RedCondA\<close>.  \<open>Pred M = butlast M = seg M 0 (Lng M - 2)\<close>
  is an \<open>M\<close>-prefix; \<open>RedCondA\<close> is inherited by every slice with last index
  \<open>< Lng M\<close> (@{thm [source] fa_RedCondA_seg}).  For \<open>Lng M \<le> 1\<close>, \<open>Pred M = M\<close>.\<close>

lemma RedCondA_Pred:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M"
  shows "RedCondA (Pred M)"
proof (cases "Lng M \<le> 1")
  case True
  thus ?thesis using condA by (simp add: Pred_def)
next
  case False
  hence L: "Lng M > 1" by simp
  let ?b = "Lng M - 2"
  have sb: "Suc ?b \<le> Lng M" using L by simp
  have ar: "Suc ?b = Lng M - 1" using L by simp
  have pred_seg: "Pred M = seg M 0 ?b"
    using seg_0_eq_take[OF sb] L ar by (simp add: Pred_def butlast_conv_take)
  have segT: "seg M 0 ?b \<in> T_PS" using pred_seg Pred_preserves_T_PS[OF MT] by simp
  have bL: "?b < Lng M" using L by simp
  show ?thesis
    using fa_RedCondA_seg[OF MT segT bL condA] pred_seg by simp
qed

text \<open>In the NON-TILING branches of \<open>oper\<close> (the three degenerate cases of §5.3:
  \<open>Lng M = 1\<close>, last column \<open>= (0,0)\<close>, or no unique row-\<open>i\<^sub>1\<close> parent of the last
  column), \<open>M[n] \<in> {M, Pred M}\<close>, so \<open>RedCondA\<close> is preserved by
  @{thm [source] RedCondA_Pred}.  The ONLY remaining branch is the genuine
  tiling expansion (\<open>take j\<^sub>0 M @ \<Oplus>\<^sub>k ...\<close>).\<close>

lemma RedCondA_oper_nontiling:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M" and n1: "1 \<le> n"
    and nontile: "Lng M - 1 = 0
                  \<or> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
                  \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "RedCondA ((M::pairseq)[n])"
proof -
  have "(M::pairseq)[n] = M \<or> (M::pairseq)[n] = Pred M"
    using nontile by (auto simp: oper_def Let_def)
  thus ?thesis
  proof
    assume "(M::pairseq)[n] = M"
    thus ?thesis using condA by simp
  next
    assume "(M::pairseq)[n] = Pred M"
    thus ?thesis using RedCondA_Pred[OF MT condA] by simp
  qed
qed


subsection \<open>Front B (tag pss-stps-condB): \<open>ST_PS \<Longrightarrow> RedCondB\<close> bricks and assembly\<close>

text \<open>\<open>Pred\<close> preserves \<open>RedCondB\<close>.  A row-0 parentless column \<open>j1' \<le> Lng(Pred M)-1
  = Lng M - 2\<close> of \<open>Pred M\<close> is, by @{thm [source] kfwd_hasParent_Pred_iff}, also
  row-0 parentless in \<open>M\<close>, and \<open>j1' \<le> Lng M - 1\<close>; so \<open>RedCondB M\<close> gives
  \<open>entry M 0 j1' = entry M 1 j1'\<close>, and entries agree below the last column
  (@{thm [source] kfwd_entry_Pred_eq}).  For \<open>Lng M \<le> 1\<close>, \<open>Pred M = M\<close>.\<close>

lemma RedCondB_Pred:
  assumes MT: "M \<in> T_PS" and condB: "RedCondB M"
  shows "RedCondB (Pred M)"
proof (cases "Lng M \<le> 1")
  case True
  thus ?thesis using condB by (simp add: Pred_def)
next
  case False
  hence L: "1 < Lng M" by simp
  have LP: "Lng (Pred M) = Lng M - 1" using L by (simp add: Pred_def length_butlast)
  show ?thesis
    unfolding RedCondB_def
  proof (intro allI impI)
    fix j1' assume H: "\<not> hasParent (Pred M) 0 j1' \<and> j1' \<le> Lng (Pred M) - 1"
    hence noPP: "\<not> hasParent (Pred M) 0 j1'" and hle: "j1' \<le> Lng (Pred M) - 1" by simp_all
    have jle: "j1' \<le> Lng M - 2" using hle LP by linarith
    have noP: "\<not> hasParent M 0 j1'"
      using kfwd_hasParent_Pred_iff[OF MT L _ jle] noPP by simp
    have hleM: "j1' \<le> Lng M - 1" using jle by linarith
    have relB: "entry M 0 j1' = entry M 1 j1'"
      using condB noP hleM unfolding RedCondB_def by blast
    have e0: "entry (Pred M) 0 j1' = entry M 0 j1'" by (rule kfwd_entry_Pred_eq[OF L jle])
    have e1: "entry (Pred M) 1 j1' = entry M 1 j1'" by (rule kfwd_entry_Pred_eq[OF L jle])
    show "entry (Pred M) 0 j1' = entry (Pred M) 1 j1'" using relB e0 e1 by simp
  qed
qed

text \<open>In the NON-TILING branches of \<open>oper\<close> (\<open>Lng M = 1\<close>, last column \<open>(0,0)\<close>, or
  no unique row-\<open>i\<^sub>1\<close> parent of the last column), \<open>M[n] \<in> {M, Pred M}\<close>, so
  \<open>RedCondB\<close> is preserved by @{thm [source] RedCondB_Pred} (mirror of
  @{thm [source] RedCondA_oper_nontiling}).\<close>

lemma RedCondB_oper_nontiling:
  assumes MT: "M \<in> T_PS" and condB: "RedCondB M" and n1: "1 \<le> n"
    and nontile: "Lng M - 1 = 0
                  \<or> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
                  \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "RedCondB ((M::pairseq)[n])"
proof -
  have "(M::pairseq)[n] = M \<or> (M::pairseq)[n] = Pred M"
    using nontile by (auto simp: oper_def Let_def)
  thus ?thesis
  proof
    assume "(M::pairseq)[n] = M"
    thus ?thesis using condB by simp
  next
    assume "(M::pairseq)[n] = Pred M"
    thus ?thesis using RedCondB_Pred[OF MT condB] by simp
  qed
qed

end

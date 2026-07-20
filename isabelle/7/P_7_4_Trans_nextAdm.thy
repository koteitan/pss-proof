theory P_7_4_Trans_nextAdm
  imports Frontier_7_029
begin

text \<open>命題（\<open>Trans\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） (§7.4), discharging
  @{text p_7_4_Trans_nextAdm}.  On \<open>RT\<^bsub>PS\<^esub>\<close> (cf.
  @{thm [source] m_7_4_Trans_Mark_Pred}): the unique NextAdm-parent \<open>j\<^sub>0\<close> of
  \<open>j\<^sub>1 = Lng M - 1\<close> satisfies \<open>(M, j\<^sub>0) \<in> Marked\<close> (it is \<open>M\<close>-admissible and an
  ancestor of \<open>j\<^sub>1\<close>) and \<open>j\<^sub>0 < j\<^sub>1\<close>, so the claim is exactly
  @{thm [source] m_7_4_Trans_Mark_Pred} at \<open>m = j\<^sub>0\<close>.\<close>

lemma m_7_4_Trans_nextAdm:
  assumes MR: "M \<in> RT_PS"
    and uniq: "\<exists>!j0. nextAdm M 0 j0 (Lng M - 1)"
  shows "\<exists>!sb. scb_decomp (Trans (Pred M))
                  (fst sb) (flatBT (Mark (Pred M) (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
            \<and> scb_decomp (Trans M)
                  (fst sb) (flatBT (Mark M (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)"
proof -
  let ?m = "THE j0. nextAdm M 0 j0 (Lng M - 1)"
  have na: "nextAdm M 0 ?m (Lng M - 1)" by (rule theI'[OF uniq])
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have leRm: "leR M 0 ?m (Lng M - 1)" using na unfolding nextAdm_def by blast
  have mlt: "?m < Lng M - 1" using na unfolding nextAdm_def by blast
  have admm: "adm M ?m" using na unfolding nextAdm_def by blast
  have mM: "(M, ?m) \<in> Marked" using MT admm leRm by (simp add: Marked_def)
  show ?thesis by (rule m_7_4_Trans_Mark_Pred[OF mM MR mlt])
qed


text \<open>命題（\<open>Trans\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） (§7.4): for \<open>M \<in> T\<^bsub>PS\<^esub>\<close> with
  \<open>j\<^sub>1 = Lng M - 1\<close>, if there is a unique \<open>j\<^sub>0\<close> with
  \<open>(0,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>NextAdm (0,j\<^sub>1)\<close>, then there exist unique
  \<open>(s\<^sub>0,b\<^sub>0) \<in> (\<Sigma>\<^bsup><\<omega>\<^esup>)\<^sup>2\<close> such that
  \<open>(s\<^sub>0, Mark(Pred M, j\<^sub>0), b\<^sub>0)\<close> is an scb-decomposition of \<open>Trans(Pred M)\<close> and
  \<open>(s\<^sub>0, Mark(M, j\<^sub>0), b\<^sub>0)\<close> is an scb-decomposition of \<open>Trans M\<close>.\<close>


text \<open>This proposition records the corrected form in
  @{file "../../corrections.md"}; the original annotation above is retained for
  comparison.\<close>

lemma p_7_4_Trans_nextAdm:
  assumes "M \<in> RT_PS"
    and "\<exists>!j0. nextAdm M 0 j0 (Lng M - 1)"
  shows "\<exists>!sb. scb_decomp (Trans (Pred M))
                  (fst sb) (flatBT (Mark (Pred M) (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
            \<and> scb_decomp (Trans M)
                  (fst sb) (flatBT (Mark M (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)"
  using assms by (rule m_7_4_Trans_nextAdm)

end

theory P_7_4_Mark_nextAdm
  imports Frontier_7_030
begin

text \<open>命題（\<open>Mark\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） (§7.4), discharging
  @{text p_7_4_Mark_nextAdm}.  Stated on \<open>RT\<^bsub>PS\<^esub>\<close> with correction A18:
  the article's \<open>(0,j) \<le>\<^sub>M (0,j\<^sub>0)\<close> ranges over \<^emph>\<open>marked\<close> columns \<open>j\<close> (the domain
  of \<open>Mark\<close> is \<open>RT\<^bsub>PS\<^esub>\<^sup>Marked\<close>), so \<open>(M,j) \<in> Marked\<close> is needed: empirically there
  are reduced \<open>M\<close> with a unique NextAdm-parent \<open>j\<^sub>0\<close> and a row-0 ancestor
  \<open>j \<le>\<^sub>M j\<^sub>0\<close> that is NOT \<open>M\<close>-admissible (e.g. \<open>(0,0)(1,1)(2,2)(3,1)\<close>, \<open>j\<^sub>0=2\<close>,
  \<open>j=1\<close>).  Given marked \<open>j\<close>, this is @{thm [source] Mark_nest_common_marked} at
  \<open>m=j\<close>, \<open>m'=j\<^sub>0\<close> (\<open>j \<le> j\<^sub>0\<close> from the \<open>le0\<close> ancestor relation, \<open>j\<^sub>0 < Lng M-1\<close>
  from \<open>nextAdm\<close>).\<close>

lemma m_7_4_Mark_nextAdm:
  assumes MR: "M \<in> RT_PS"
    and uniq: "\<exists>!j0. nextAdm M 0 j0 (Lng M - 1)"
    and jM: "(M, j) \<in> Marked"
    and jle: "leR M 0 j (THE j0. nextAdm M 0 j0 (Lng M - 1))"
  shows "\<exists>!sb. scb_decomp (Mark (Pred M) j)
                  (fst sb) (flatBT (Mark (Pred M) (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
            \<and> scb_decomp (Mark M j)
                  (fst sb) (flatBT (Mark M (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)"
proof -
  let ?j0 = "THE j0. nextAdm M 0 j0 (Lng M - 1)"
  have na: "nextAdm M 0 ?j0 (Lng M - 1)" by (rule theI'[OF uniq])
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have leR0: "leR M 0 ?j0 (Lng M - 1)" using na unfolding nextAdm_def by blast
  have j0lt: "?j0 < Lng M - 1" using na unfolding nextAdm_def by blast
  have adm0: "adm M ?j0" using na unfolding nextAdm_def by blast
  have j0M: "(M, ?j0) \<in> Marked" using MT adm0 leR0 by (simp add: Marked_def)
  have jle0: "j \<le> ?j0"
  proof -
    have "(nextrel0 M)\<^sup>*\<^sup>* j ?j0" using jle by (simp add: leR_def le0_def)
    thus ?thesis by (rule nextrel0_rtrancl_mono)
  qed
  show ?thesis by (rule Mark_nest_common_marked[OF MR jM j0M jle0 j0lt])
qed


text \<open>系（\<open>Mark\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） (§7.4): under the same hypotheses, with
  \<open>j\<^sub>0\<close> the unique NextAdm-parent of \<open>j\<^sub>1 = Lng M - 1\<close>, for any \<open>j\<close> with
  \<open>(0,j) \<le>\<^sub>M (0,j\<^sub>0)\<close> there exist unique \<open>(s\<^sub>0,b\<^sub>0)\<close> such that
  \<open>(s\<^sub>0, Mark(Pred M, j\<^sub>0), b\<^sub>0)\<close> is an scb-decomposition of \<open>Mark(Pred M, j)\<close> and
  \<open>(s\<^sub>0, Mark(M, j\<^sub>0), b\<^sub>0)\<close> is an scb-decomposition of \<open>Mark(M, j)\<close>.\<close>


text \<open>This proposition records the corrected form in
  @{file "../../corrections.md"}; the original annotation above is retained for
  comparison.\<close>

lemma p_7_4_Mark_nextAdm:
  assumes "M \<in> RT_PS"
    and "\<exists>!j0. nextAdm M 0 j0 (Lng M - 1)"
    and "leR M 0 j (THE j0. nextAdm M 0 j0 (Lng M - 1))" "(M, j) \<in> Marked"
  shows "\<exists>!sb. scb_decomp (Mark (Pred M) j)
                  (fst sb) (flatBT (Mark (Pred M) (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
            \<and> scb_decomp (Mark M j)
                  (fst sb) (flatBT (Mark M (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)"
  by (rule m_7_4_Mark_nextAdm[OF assms(1) assms(2) assms(4) assms(3)])

end

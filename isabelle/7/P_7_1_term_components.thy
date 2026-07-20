theory P_7_1_term_components
  imports P_7_4_Adm_nextAdm
begin

section \<open>§7.1 Buchholz notation: principal components (命題（順序数項の単項成分の基本性質）)\<close>

text \<open>
  Lemma m_7_1_term_components: for \<open>t = Trm ps\<close>, the component list \<open>P\<^bsub>B\<^esub> t\<close>
  is empty iff \<open>t = 0\<close>, and \<open>\<Sigma>\<^bsub>B\<^esub> (P\<^bsub>B\<^esub> t) = t\<close>.
\<close>

lemma m_7_1_term_components:
  \<comment> \<open>m: 命題（順序数項の単項成分の基本性質）(1)(2) (§7.1)\<close>
  assumes "t \<in> T_B"
  shows "(Lng (PB t) = 0 \<longleftrightarrow> t = Trm []) \<and> SigmaB (PB t) = t"
proof (cases t)
  case (Trm ps)
  show ?thesis
    unfolding Trm PB_def SigmaB_def
    by (auto simp: comp_def)
qed

text \<open>命題（順序数項の単項成分の基本性質） (§7.1): with \<open>J\<^sub>1 := Lng(P(t)) - 1\<close>,
  (1) \<open>J\<^sub>1 = -1\<close> (i.e. \<open>Lng(P t) = 0\<close>) iff \<open>t = 0\<close>, and (2) \<open>t = \<Sigma>\<^bsub>B\<^esub>(P t)\<close>.\<close>

lemma p_7_1_term_components:
  assumes "t \<in> T_B"
  shows "(Lng (PB t) = 0 \<longleftrightarrow> t = Trm []) \<and> SigmaB (PB t) = t"
  using assms by (rule m_7_1_term_components)

end

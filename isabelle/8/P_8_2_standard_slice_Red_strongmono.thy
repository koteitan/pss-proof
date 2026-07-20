theory P_8_2_standard_slice_Red_strongmono
  imports Support_8_C
begin

section \<open>§8 停止性 (Termination)\<close>

subsection \<open>§8.2 強単項性 (Strong-monomiality)\<close>

text \<open>Article order is §8.1 < §8.2, but §8.2 is grouped first here because it
  introduces \<open>DT\<^bsub>PS\<^esub>\<close> (= \<open>DT_PS\<close>, 強単項) and \<open>LastStep\<close> used throughout §8;
  all statements are \<open>sorry\<close> so the document order is cosmetic.

  Faithfulness note on 強許容 (strong-admissibility): the article uses the
  phrase \<open>M の強許容性\<close> only inside §8.2 proofs (article 3532/3552/3576/3800),
  never as a separate definition.  At each use it denotes the consequence of
  \<open>descending (Br M)\<close> (the third clause of 強単項) re-expressed in
  \<open>FirstNodes\<close>/\<open>Joints\<close> coordinates (e.g. equal row-0 heads \<open>\<Rightarrow>\<close> descending
  row-1 heads).  Hence it is NOT a primitive needed to state the §8.2
  propositions; it only surfaces in their (deferred) proofs.\<close>

text \<open>命題（標準形の直系先祖による切片の簡約化の強単項性） (§8.2, article 3283):
  for \<open>M \<in> ST\<^bsub>PS\<^esub>\<close>, the reduction of an ancestor slice with \<open>(0,j'\<^sub>0) \<le>\<^sub>M (0,j'\<^sub>1)\<close>
  is strong-monomial.  Builds directly on §6.8 prop1
  (\<open>p_6_8_standard_slice_Br_descending\<close>): the slice \<open>M'\<close> is mono with \<open>Br M'\<close>
  descending, so \<open>Red M'\<close> is reduced + mono + \<open>Br\<close>-descending, i.e. \<open>\<in> DT\<^bsub>PS\<^esub>\<close>.\<close>

lemma p_8_2_standard_slice_Red_strongmono:
  assumes "M \<in> ST_PS" "j0' < j1'" "j1' \<le> Lng M - 1" "leR M 0 j0' j1'"
  shows "Red (seg M j0' j1') \<in> DT_PS"
  by (rule m_8_2_standard_slice_Red_strongmono[OF assms])

end

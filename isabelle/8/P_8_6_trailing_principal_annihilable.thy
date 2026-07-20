theory P_8_6_trailing_principal_annihilable
  imports Support_8_C
begin

text \<open>補題（順序数項の末尾単項の零化可能性） (§8.6, content.md 5621):
  for \<open>t, t' \<in> T\<^bsub>B\<^esub>\<close>, \<open>s, b \<in> \<Sigma>\<^bsup><\<omega>\<^esup>\<close>, and \<open>u, v \<in> \<nat>\<close>, if
  \<open>(s, D\<^sub>u(t' + D\<^sub>v 0), b)\<close> is an scb-decomposition of \<open>t\<close>, then there is
  \<open>k \<in> \<nat>\<close> with \<open>0 < k \<le> v+1\<close> such that \<open>(s, D\<^sub>u t', b)\<close> is an scb-decomposition
  of \<open>t[0]\<^sup>k\<close>.  Transcribable: the scb-decomposition is \<open>scb_decomp\<close> with the
  \<open>c\<close>-component flattened (\<open>flatBT\<close>), and \<open>t[0]\<^sup>k\<close> is the \<open>k\<close>-fold iterate of
  \<open>\<lambda>a. operB a (numBT 0)\<close>.

  FAITHFUL UNPROVEN STUB.  The former correction A25 is \<^bold>\<open>retracted\<close>:
  \<open>corrections-old.md\<close> records that the apparent counterexample used the
  pre-A23 misreading of \<open>operB\<close>, whereas the printed statement holds under the
  corrected fundamental sequence.  Main nevertheless has no proof of the full
  wrapper, so it remains the same documented \<open>sorry\<close>; this is an unproved true
  statement, not an article-false one.  The proved restricted content from main
  is retained in \<open>Support_8_B\<close>: @{thm [source] m_8_6_trailing_principal_peel}
  covers \<open>v = 0 \<or> u \<ge> v\<close>, and @{thm [source] operB_iter_Du_Dw0}
  covers the iterated \<open>t' = 0\<close> case.\<close>

lemma p_8_6_trailing_principal_annihilable:
  fixes t t' :: BT and s b :: "Sym list" and u v :: nat
  assumes "t \<in> T_B" "t' \<in> T_B"
    and "scb_decomp t s (flatBT (Dpt (enat u) (t' +\<^sub>B Dpt (enat v) 0\<^sub>B))) b"
  shows "\<exists>k. 0 < k \<and> k \<le> v + 1
            \<and> scb_decomp (((\<lambda>a. operB a (numBT 0)) ^^ k) t)
                         s (flatBT (Dpt (enat u) t')) b"
  sorry

end

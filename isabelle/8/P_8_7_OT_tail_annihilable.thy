theory P_8_7_OT_tail_annihilable
  imports P_8_6_trailing_principal_annihilable
begin

text \<open>補題（順序数項の末尾項の零化可能性） (§8.7, article 5971):
  for \<open>t \<in> OT\<^bsub>B\<^esub>\<close>, \<open>t' \<in> T\<^bsub>B\<^esub>\<close>, \<open>s, b \<in> \<Sigma>\<^bsup><\<omega>\<^esup>\<close>, \<open>u \<in> \<nat>\<close>, if
  \<open>(s, D\<^sub>u t', b)\<close> is an scb-decomposition of \<open>t\<close>, then some \<open>k\<close> makes
  \<open>(s, D\<^sub>u 0, b)\<close> an scb-decomposition of \<open>t[0]\<^sup>k\<close>
  (\<open>t[0]\<^sup>k = ((\<lambda>a. operB a (numBT 0)) ^^ k) t\<close>).

  FAITHFUL UNPROVEN STUB.  Correction A26 is \<^bold>\<open>retracted\<close> in
  \<open>corrections-old.md\<close>: the former nested-principal counterexample came from
  the pre-A23 misreading of \<open>operB\<close>; with the corrected fundamental sequence
  its orbit reaches the required term at \<open>k = 2\<close>.  Thus the printed statement
  is true, not article-false.  Main has no proof of its full wrapper, so this leaf
  remains the same documented \<open>sorry\<close>.  The proved restricted content is
  retained in \<open>Support_8_B\<close>, including the top-level
  distribution @{thm [source] operB_dist_trailing_single}, the proved leaf-body
  top-level result @{thm [source] m_8_7_toplevel_Dw0_annihilate}, and the general
  top-level well-founded engine @{thm [source] m_8_7_toplevel_OT_tail_annihilate}.\<close>

lemma p_8_7_OT_tail_annihilable:
  assumes "t \<in> OT_B" "t' \<in> T_B"
    and "scb_decomp t s (flatBT (Dpt (enat u) t')) b"
  shows "\<exists>k. scb_decomp (((\<lambda>a. operB a (numBT 0)) ^^ k) t) s
                        (flatBT (Dpt (enat u) 0\<^sub>B)) b"
  sorry

end

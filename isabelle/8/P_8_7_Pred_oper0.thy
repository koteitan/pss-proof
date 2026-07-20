theory P_8_7_Pred_oper0
  imports P_8_7_OT_tail_annihilable
begin

text \<open>補題（\<open>Pred\<close>と\<open>[0]\<close>の関係） (§8.7, article 6014):
  for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> (article writes \<open>PT\<^bsub>B\<^esub>\<close>, a typo for \<open>PT\<^bsub>PS\<^esub>\<close>),
  using the symbols of the recursive definition of \<open>Trans\<close>, if \<open>j\<^sub>1 > 1\<close>,
  \<open>M\<close> fails condition (VI), and \<open>Trans(M)\<close> is an ordinal term, then some \<open>k\<close>
  gives \<open>Trans(M)[0]\<^sup>k = t\<^sub>1\<close>.  The internal \<open>t\<^sub>1\<close> of \<open>Trans\<close> is \<open>Trans (Pred M)\<close>,
  so it is exposed as such here.

  FAITHFUL UNPROVEN STUB.  Correction A27 is \<^bold>\<open>retracted\<close> in
  \<open>corrections-old.md\<close>: it arose from the pre-A23 misreading of \<open>operB\<close>,
  and under the corrected fundamental sequence the printed statement is true.
  Main has no proved \<open>m_\<close> wrapper for it and deliberately does not need it on
  the termination path.  It therefore remains a documented \<open>sorry\<close> leaf,
  while the clean per-branch termination machinery in
  \<open>Support_8_B\<close>/\<open>Support_8_C\<close> remains fully proved.\<close>

lemma p_8_7_Pred_oper0:
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "Lng M - 1 > 1"
    and "\<not> transCondVI M" "Trans M \<in> OT"
  shows "\<exists>k. ((\<lambda>a. operB a (numBT 0)) ^^ k) (Trans M) = Trans (Pred M)"
  sorry

end

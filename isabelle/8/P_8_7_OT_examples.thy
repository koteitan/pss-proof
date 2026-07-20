theory P_8_7_OT_examples
  imports Support_8_C
begin

text \<open>補題（順序数項の基本例） (§8.7, article 6066): four basic memberships in
  \<open>OT\<^bsub>B\<^esub>\<close>.  \<open>D\<^sub>u\<^sup>n 0 = (Dpt (enat u) ^^ n) 0\<^sub>B\<close>; \<open>(D\<^sub>u 0)\<times>(n-1) = multBT (D\<^sub>u 0) (n-1)\<close>.\<close>

lemma p_8_7_OT_examples:
  shows "Dpt (enat u) 0\<^sub>B \<in> OT_B"
    and "Dpt (enat u) (Dpt (enat v) 0\<^sub>B) \<in> OT_B"
    and "n \<ge> 1 \<Longrightarrow> multBT (Dpt (enat u) 0\<^sub>B) (n - 1) \<in> OT_B"
    and "(Dpt (enat u) ^^ n) 0\<^sub>B \<in> OT_B"
  apply (rule m_8_7_OT_examples(1))
  apply (rule m_8_7_OT_examples(2))
  apply (rule m_8_7_OT_examples(3))
  apply assumption
  apply (rule m_8_7_OT_examples(4))
  done

end

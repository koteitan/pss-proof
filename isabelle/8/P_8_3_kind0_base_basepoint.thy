theory P_8_3_kind0_base_basepoint
  imports Support_8_C
begin

text \<open>補題（第\<open>0\<close>種型基本列の基本基点関係） (§8.3, article 3998): for \<open>M \<in> RT\<^bsub>PS\<^esub>\<close>,
  \<open>n \<in> \<nat>\<^sub>+\<close>, with \<open>j\<^sub>1 = Lng M - 1\<close>, if there is a unique \<open>j\<^sub>0\<close> with
  \<open>(0,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>Next (0,j\<^sub>1)\<close>, \<open>j\<^sub>-\<^sub>1 = Adm\<^sub>M(j\<^sub>0)\<close>, and \<open>M\<^bsub>1,j\<^sub>1\<^esub> = 0\<close>, then:
  (1) if \<open>n > 1\<close> then \<open>(M[n], j\<^sub>0+(n-1)(j\<^sub>1-j\<^sub>0)) \<in> RT\<^bsub>PS\<^esub>\<^sup>Marked\<close>;
  (2) if \<open>j\<^sub>0\<close> is non-\<open>M\<close>-admissible then \<open>(M[n], j\<^sub>-\<^sub>1) \<in> RT\<^bsub>PS\<^esub>\<^sup>Marked\<close>.\<close>

lemma p_8_3_kind0_base_basepoint:
  fixes M :: pairseq
  assumes "M \<in> RT_PS" "0 < n"
    and "hasParent M 0 (Lng M - 1)"
    and "entry M 1 (Lng M - 1) = 0"
  shows "n > 1 \<longrightarrow>
           (M[n], parent M 0 (Lng M - 1)
                  + (n-1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) \<in> Marked
           \<and> M[n] \<in> RT_PS"
    and "\<not> adm M (parent M 0 (Lng M - 1)) \<longrightarrow>
           (M[n], Adm M (parent M 0 (Lng M - 1))) \<in> Marked \<and> M[n] \<in> RT_PS"
  apply (rule m_8_3_kind0_base_basepoint(1)[OF assms])
  apply (rule m_8_3_kind0_base_basepoint(2)[OF assms])
  done

end

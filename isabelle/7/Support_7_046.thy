theory Support_7_046
  imports P_7_2_add_scb
begin

section \<open>§7.3 系（\<open>Trans\<close>と非可算基数の関係）: \<open>Trans M = D\<^bsub>v\<^esub> 0 \<longleftrightarrow> M\<close> is one of the two
  canonical witnesses (content.md 2372)\<close>

text \<open>\<open>Trans [(0,0),(0,0)] = D\<^bsub>0\<^esub> 0\<close>.  Note \<open>[(0,0),(0,0)] = cnst 0 1\<close> is \<^emph>\<open>multi\<close>
  (not mono: row 0 is constant \<open>0\<close>, so no \<open>(0,0) <\<^bsub>M\<^esub>\<^sup>Next (0,1)\<close>), so this is the
  \<open>u = 0\<close>, \<open>j\<^sub>1 = 1\<close> instance of @{text m_8_7_cnst_Trans}:
  \<open>multBT (D\<^bsub>0\<^esub> 0) 1 = 0\<^sub>B +\<^sub>B D\<^bsub>0\<^esub> 0 = D\<^bsub>0\<^esub> 0\<close>.\<close>

lemma Trans_two_zero: "Trans [(0,0),(0,0)] = Dpt 0 0\<^sub>B"
proof -
  have ceq: "(cnst 0 1 :: pairseq) = [(0,0),(0,0)]" by simp
  have "Trans [(0,0),(0,0)] = Trans (cnst 0 1 :: pairseq)" using ceq by simp
  also have "\<dots> = multBT (Dpt (enat 0) 0\<^sub>B) 1"
    by (subst m_8_7_cnst_Trans) simp
  also have "\<dots> = 0\<^sub>B +\<^sub>B Dpt 0 0\<^sub>B" by (simp add: zero_enat_def)
  also have "\<dots> = Dpt 0 0\<^sub>B" by simp
  finally show ?thesis .
qed

end

theory P_8_2_condV_terminal_slice_Trans
  imports Support_8_C
begin

text \<open>補題（条件(V)の下での終切片と\<open>Trans\<close>の関係） (§8.2, article 3664):
  same hypotheses as the previous lemma, with \<open>M' = (M\<^sub>j)\<^bsub>j=m\<^esub>\<^bsup>j\<^sub>1\<^esup> = seg M m j\<^sub>1\<close>;
  a unique \<open>t\<^sub>1 \<in> T\<^bsub>B\<^esub>\<close> gives \<open>Trans M = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>0\<^esub> t\<^sub>1\<close> and \<open>Trans M' = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> t\<^sub>1\<close>.\<close>

lemma p_8_2_condV_terminal_slice_Trans:
  fixes M :: pairseq and m :: nat
  defines "j1 \<equiv> Lng M - 1"
  defines "J1 \<equiv> Lng (Br M) - 1"
  defines "j0' \<equiv> Joints M ! J1"
  defines "j1' \<equiv> FirstNodes M ! J1"
  defines "M' \<equiv> seg M m j1"
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "Br M \<noteq> []"
    and "m < j0' \<or> (m = j0' \<and> entry M 0 j1' = entry M 1 j1' \<and> descending (Br M))"
  shows "\<exists>!t1. Trans M = Dpt (enat (entry M 1 0)) t1
            \<and> Trans M' = Dpt (enat (entry M 1 m)) t1"
  unfolding M'_def j1_def
  by (rule m_8_2_condV_terminal_slice_Trans[OF assms(6) assms(7) assms(8)
        assms(9)[unfolded j0'_def j1'_def J1_def]])

end

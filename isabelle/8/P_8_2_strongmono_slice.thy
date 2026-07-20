theory P_8_2_strongmono_slice
  imports Support_8_C
begin

text \<open>補題（強単項性の切片への遺伝性） (§8.2, article 3328):
  for \<open>M \<in> DT\<^bsub>PS\<^esub>\<close>, an ancestor slice \<open>M' = (M\<^sub>j)\<^bsub>j=j'\<^sub>0\<^esub>\<^bsup>j'\<^sub>1\<^esup>\<close> with
  \<open>j'\<^sub>0 < j'\<^sub>1 \<le> Lng M - 1\<close> and \<open>j'\<^sub>0 \<le> Joints(M)\<^bsub>J\<^sub>1\<^esub>\<close> (\<open>J\<^sub>1 = Lng(Br M)-1\<close>)
  is again strong-monomial.\<close>

lemma p_8_2_strongmono_slice:
  fixes M :: pairseq
  defines "J1 \<equiv> Lng (Br M) - 1"
  assumes "M \<in> DT_PS" "j0' < j1'" "j1' \<le> Lng M - 1" "j0' \<le> Joints M ! J1"
  shows "seg M j0' j1' \<in> DT_PS"
  by (rule m_8_2_strongmono_slice[OF assms(2) assms(3) assms(4)
        assms(5)[unfolded J1_def]])

end

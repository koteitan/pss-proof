theory P_8_7_const00_Trans
  imports Support_8_C
begin

subsection \<open>§8.7 主結果 (Main result)\<close>

text \<open>補題（公差\<open>(0,0)\<close>のペア数列の\<open>Trans\<close>の基本性質） (§8.7, article 5857):
  for \<open>u, j\<^sub>1 \<in> \<nat>\<close>, the constant (公差\<open>(0,0)\<close>) sequence
  \<open>M = ((u,u))\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close> (= \<open>replicate (Suc j\<^sub>1) (u,u)\<close>) has
  \<open>Trans(M) = (D\<^sub>0 0)\<times>j\<^sub>1\<close> if \<open>u = 0\<close> and \<open>(D\<^sub>u 0)\<times>(j\<^sub>1+1)\<close> if \<open>u > 0\<close>.
  \<open>(D\<^sub>u 0)\<times>k = multBT (D\<^sub>u 0) k\<close> (\<open>k\<close>-fold \<open>+\<^sub>B\<close>-sum).\<close>

lemma p_8_7_const00_Trans:
  shows "Trans (replicate (Suc j1) (u, u))
           = (if u = 0 then multBT (Dpt (enat u) 0\<^sub>B) j1
              else multBT (Dpt (enat u) 0\<^sub>B) (Suc j1))"
  by (rule m_8_7_const00_Trans)

end

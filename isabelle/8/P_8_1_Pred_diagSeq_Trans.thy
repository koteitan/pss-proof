theory P_8_1_Pred_diagSeq_Trans
  imports Support_8_C
begin

text \<open>系（\<open>Pred\<close>が公差\<open>(1,1)\<close>のペア数列の\<open>Trans\<close>の基本性質） (§8.1, article 2871):
  for \<open>u,v,w,w' \<in> \<nat>\<close> with \<open>u < v\<close>, let \<open>M := ((j,j))\<^bsub>j=u\<^esub>\<^bsup>v\<^esup> \<oplus>\<^bsub>\<nat>\<^sup>2\<^esub> (w',w)\<close>
  (modelled by \<open>diagSeq u v @ [(w', w)]\<close>, the article's \<open>\<oplus>\<^bsub>\<nat>\<^sup>2\<^esub>\<close> being list
  append \<open>@\<close>).  The four cases give the explicit \<open>Trans(M)\<close>.  The article's
  string connective \<open>D\<^sub>u ( a , b )\<close> (with underlined parens/comma) is the
  \<open>BT\<close>-level \<open>Dpt (enat u) (a +\<^sub>B b)\<close> (\<open>+\<^sub>B\<close> realises \<open>\<oplus>\<close> on \<open>T\<^bsub>B\<^esub>\<close>).\<close>

lemma p_8_1_Pred_diagSeq_Trans:
  assumes "u < v"
  shows
    "\<comment> \<open>(1)\<close>
     (w' = v + 1 \<and> u < w \<and> w \<le> v
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) (Dpt (enat w) 0\<^sub>B)))
   \<and> \<comment> \<open>(2)\<close>
     (u < w' \<and> w' \<le> v \<and> w = w'
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B))
   \<and> \<comment> \<open>(3)\<close>
     (u + 1 < w' \<and> w' \<le> v \<and> w < w'
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) 0\<^sub>B
                    +\<^sub>B Dpt (enat (w' - 1)) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B)))
   \<and> \<comment> \<open>(4)\<close>
     (u + 1 = w' \<and> w < w'
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B))"
  by (rule m_8_1_Pred_diagSeq_Trans[OF assms])

end

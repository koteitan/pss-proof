theory P_8_2_subexpr_component_strongmono
  imports Support_8_C
begin

text \<open>補題（強単項性の下での部分表現の単項成分の基本性質） (§8.2, article 3454):
  for \<open>M \<in> DT\<^bsub>PS\<^esub>\<close> (\<open>Br M \<noteq> []\<close>), a unique \<open>t' \<in> T\<^bsub>B\<^esub>\<close> with
  \<open>Trans M = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>0\<^esub> t'\<close> bounds every principal component of \<open>t'\<close> from below.
  「\<open>t'\<close>の各単項成分は \<open>D\<^sub>x 0\<close> 以上」 is modelled as
  \<open>\<forall>p \<in> set (PB t'). leBT (D\<^sub>x 0) p\<close> (the elements of \<open>PB t'\<close> are already the
  principal-component \<^typ>\<open>BT\<close>s, so each summand \<open>p \<ge> D\<^sub>x 0\<close>).\<close>

lemma p_8_2_subexpr_component_strongmono:
  fixes M :: pairseq
  defines "J1 \<equiv> Lng (Br M) - 1"
  defines "j0' \<equiv> Joints M ! J1"
  defines "j1' \<equiv> FirstNodes M ! J1"
  assumes "M \<in> DT_PS" "Br M \<noteq> []"
  shows "\<exists>!t'.
      \<comment> \<open>(1)\<close>
      Trans M = Dpt (enat (entry M 1 0)) t'
    \<and> \<comment> \<open>(2)\<close>
      ((j0' = 0 \<or> entry M 0 j1' = entry M 1 j1')
         \<longrightarrow> (\<forall>p\<in>set (PB t'). leBT (Dpt (enat (entry M 1 j1')) 0\<^sub>B) p))
    \<and> \<comment> \<open>(3)\<close>
      ((0 < j0' \<and> j0' < TrMax M \<and> entry M 0 j1' > entry M 1 j1')
         \<longrightarrow> (\<forall>p\<in>set (PB t'). leBT (Dpt (enat (entry M 1 j0')) 0\<^sub>B) p))
    \<and> \<comment> \<open>(4)\<close>
      ((0 < j0' \<and> j0' = TrMax M)
         \<longrightarrow> (\<forall>p\<in>set (PB t'). leBT (Dpt (enat (entry M 1 (TrMax M))) 0\<^sub>B) p))"
  unfolding J1_def j0'_def j1'_def
  by (rule m_8_2_subexpr_component_strongmono_uncond[OF assms(4) assms(5)])

end

theory P_8_2_subexpr_component_Pred
  imports Support_8_C
begin

text \<open>補題（部分表現の単項成分と\<open>Pred\<close>の関係） (§8.2, article 3360):
  for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> with \<open>j\<^sub>1 = Lng M - 1 > 1\<close>, set \<open>J\<^sub>1 = Lng(Br M)-1\<close>
  (\<open>Br M \<noteq> []\<close>), \<open>j'\<^sub>0 = Joints(M)\<^bsub>J\<^sub>1\<^esub>\<close>, \<open>j'\<^sub>1 = FirstNodes(M)\<^bsub>J\<^sub>1\<^esub>\<close>.  One of four
  cases (1)–(4) holds, each pinning down \<open>Trans(Pred M)\<close> and \<open>Trans M\<close> for a
  unique tuple of \<open>T\<^bsub>B\<^esub>\<close>-terms.  \<open>D\<^sub>x t = Dpt (enat x) t\<close>; \<open>+\<close> = \<open>+\<^sub>B\<close>;
  \<open>0\<close> = \<open>0\<^sub>B\<close>.  Tuples use \<open>fst\<close>/\<open>snd\<close> projections (\<open>(t\<^sub>1,t\<^sub>2,t\<^sub>3)\<close> as \<open>t123\<close>).\<close>

lemma p_8_2_subexpr_component_Pred:
  fixes M :: pairseq
  defines "j1 \<equiv> Lng M - 1"
  defines "J1 \<equiv> Lng (Br M) - 1"
  defines "j0' \<equiv> Joints M ! J1"
  defines "j1' \<equiv> FirstNodes M ! J1"
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "Br M \<noteq> []" "j1 > 1"
  shows
    "\<comment> \<open>(1)\<close>
     (j1' = j1 \<and> (TrMax M = 0 \<or> j0' < TrMax M)
        \<and> (entry M 0 j1' = entry M 1 j1' \<or> adm M j0')
        \<and> (\<exists>!t1. Trans (Pred M) = Dpt (enat (entry M 1 0)) t1
              \<and> Trans M = Dpt (enat (entry M 1 0))
                            (t1 +\<^sub>B Dpt (enat (entry M 1 j1')) 0\<^sub>B)))
   \<or> \<comment> \<open>(2)\<close>
     (j1' = j1 \<and> entry M 0 j1' > entry M 1 j1' \<and> \<not> adm M j0'
        \<and> (\<exists>!t12. Trans (Pred M) = Dpt (enat (entry M 1 0)) (fst t12)
              \<and> Trans M = Dpt (enat (entry M 1 0))
                            (fst t12 +\<^sub>B Dpt (enat (entry M 1 j0')) (snd t12))))
   \<or> \<comment> \<open>(3)\<close>
     (\<exists>!t123. Trans (Pred M)
                = Dpt (enat (entry M 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M 1 j1')) (fst (snd t123)))
            \<and> Trans M = Dpt (enat (entry M 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M 1 j1')) (snd (snd t123))))
   \<or> \<comment> \<open>(4)\<close>
     (\<exists>!t123. Trans (Pred M)
                = Dpt (enat (entry M 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M 1 j0')) (fst (snd t123)))
            \<and> Trans M = Dpt (enat (entry M 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M 1 j0')) (snd (snd t123))))"
  unfolding j1_def J1_def j0'_def j1'_def
  by (rule m_8_2_keystone[OF assms(5) assms(6) assms(7)
        assms(8)[unfolded j1_def]])

end

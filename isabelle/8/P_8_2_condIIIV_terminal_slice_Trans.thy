theory P_8_2_condIIIV_terminal_slice_Trans
  imports Support_8_C
begin

text \<open>命題（条件(II)か(IV)の下での終切片と\<open>Trans\<close>の関係） (§8.2, article 3314):
  for \<open>M \<in> DT\<^bsub>PS\<^esub>\<close>, set \<open>j\<^sub>1 = Lng M - 1\<close>, \<open>J\<^sub>1 = Lng(Br M)-1\<close> (\<open>Br M \<noteq> []\<close>),
  \<open>j'\<^sub>0 = Joints(M)\<^bsub>J\<^sub>1\<^esub>\<close>, \<open>j'\<^sub>1 = FirstNodes(M)\<^bsub>J\<^sub>1\<^esub>\<close>, \<open>J\<^sub>0 = LastStep M\<close>,
  \<open>m\<^sub>1 = FirstNodes(M)\<^bsub>J\<^sub>0\<^esub> - 1\<close>, \<open>N = seg M 0 m\<^sub>1\<close>, \<open>N' = seg M j'\<^sub>0 m\<^sub>1\<close>,
  \<open>M' = seg M j'\<^sub>0 j\<^sub>1\<close>.  If \<open>0 < j'\<^sub>0 < TrMax M\<close> and \<open>M\<^bsub>0,j'\<^sub>1\<^esub> > M\<^bsub>1,j'\<^sub>1\<^esub>\<close>
  then a unique \<open>(t\<^sub>1,t\<^sub>2) \<in> T\<^bsub>B\<^esub>\<^sup>2\<close> satisfies (1)–(4).\<close>

lemma p_8_2_condIIIV_terminal_slice_Trans:
  fixes M :: pairseq
  defines "j1 \<equiv> Lng M - 1"
  defines "J1 \<equiv> Lng (Br M) - 1"
  defines "j0' \<equiv> Joints M ! J1"
  defines "j1' \<equiv> FirstNodes M ! J1"
  defines "J0 \<equiv> LastStep M"
  defines "m1 \<equiv> FirstNodes M ! J0 - 1"
  defines "N \<equiv> seg M 0 m1"
  defines "N' \<equiv> seg M j0' m1"
  defines "M' \<equiv> seg M j0' j1"
  assumes "M \<in> DT_PS" "Br M \<noteq> []"
    and "0 < j0'" "j0' < TrMax M" "entry M 0 j1' > entry M 1 j1'"
  shows "\<exists>!t12.
      \<comment> \<open>(1)\<close> Trans N = Dpt (enat (entry M 1 0)) (fst t12)
    \<and> \<comment> \<open>(2)\<close> Trans N' = Dpt (enat (entry M 1 j0')) (fst t12)
    \<and> \<comment> \<open>(3)\<close> Trans M' = Dpt (enat (entry M 1 j0')) (fst t12 +\<^sub>B snd t12)
              \<and> snd t12 \<noteq> 0\<^sub>B
    \<and> \<comment> \<open>(4)\<close> Trans M = Dpt (enat (entry M 1 0))
                  (fst t12 +\<^sub>B Dpt (enat (entry M 1 j0')) (fst t12 +\<^sub>B snd t12))"
proof -
  have fin: "finite {J. J < Lng (Br M)
      \<and> entry (Br M ! (Lng (Br M) - 1)) 0 0 = entry (Br M ! J) 0 0
      \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0}"
    by (rule finite_subset[of _ "{..<Lng (Br M)}"]) auto
  show ?thesis
    unfolding j1_def J1_def j0'_def j1'_def J0_def m1_def N_def N'_def M'_def
    by (rule hqx_condIIIV_of_DT[OF assms(10) assms(11)
          assms(12)[unfolded j0'_def J1_def]
          assms(13)[unfolded j0'_def J1_def]
          assms(14)[unfolded j1'_def J1_def] fin])
qed

end

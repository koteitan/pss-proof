theory Support_7_038
  imports Frontier_7_043
begin

text \<open>The headline proposition, all three clauses, \<open>RT\<^bsub>PS\<^esub>\<close>-restricted.\<close>

lemma m_7_3_Trans_leftmost:
  assumes MR: "M \<in> RT_PS"
  shows "P M ! 0 = [(0,0)] \<and> Lng (P M) > 1 \<longrightarrow>
            bpHeadV (Trans M) = enat (entry M 1 1)"     \<comment> \<open>(1)\<close>
    and "P M ! 0 \<noteq> [(0,0)] \<longrightarrow>
            PB (Trans M) ! 0 = Trans (P M ! 0)
            \<and> bpHeadV (Trans M) = enat (entry M 1 0)"   \<comment> \<open>(2)\<close>
    and "nextR M 1 0 1 \<longrightarrow>
            bpHeadV (Trans M) = enat (entry M 1 0)
            \<and> (\<exists>t. PB (Trans M) ! 0 = Dpt (enat (entry M 1 0)) t \<and> t \<noteq> 0\<^sub>B)"
                                                         \<comment> \<open>(3)\<close>
proof -
  have core: "bpHeadV (Trans M) = enat (entry M 1 0)"
    using m_7_3_Trans_leftend MR by blast
  \<comment> \<open>(1)\<close>
  show "P M ! 0 = [(0,0)] \<and> Lng (P M) > 1 \<longrightarrow>
          bpHeadV (Trans M) = enat (entry M 1 1)"
  proof (intro impI)
    assume H: "P M ! 0 = [(0,0)] \<and> Lng (P M) > 1"
    have P0z: "P M ! 0 = [(0,0)]" using H by simp
    have LP: "Lng (P M) > 1" using H by simp
    \<comment> \<open>\<open>Lng (P M) > 1\<close> gives \<open>1 < Lng M\<close> (more than one column overall)\<close>
    have L: "1 < Lng M"
    proof -
      have "M \<noteq> []" using MR by (auto simp: RT_PS_def T_PS_def)
      moreover have "Lng M \<noteq> 1"
      proof
        assume "Lng M = 1"
        hence "Lng (P M) = 1" by (metis poper_P_nonmulti One_nat_def
              less_numeral_extra(4) multiT_imp_Lng_gt1 length_Cons list.size(3))
        thus False using LP by simp
      qed
      ultimately show ?thesis by (cases M) auto
    qed
    have "entry M 1 1 = 0" using reduced_P0_zero_e11[OF MR P0z L LP] by simp
    moreover have "entry M 1 0 = 0" using reduced_P0_zero_e11[OF MR P0z L LP] by simp
    ultimately show "bpHeadV (Trans M) = enat (entry M 1 1)"
      using core by simp
  qed
next
  have core: "bpHeadV (Trans M) = enat (entry M 1 0)"
    using m_7_3_Trans_leftend MR by blast
  \<comment> \<open>(2)\<close>
  show "P M ! 0 \<noteq> [(0,0)] \<longrightarrow>
          PB (Trans M) ! 0 = Trans (P M ! 0)
          \<and> bpHeadV (Trans M) = enat (entry M 1 0)"
  proof (intro impI)
    assume P0ne: "P M ! 0 \<noteq> [(0,0)]"
    have "PB (Trans M) ! 0 = Trans (P M ! 0)"
      using m_7_3_Trans_leftmost_pc MR P0ne by blast
    thus "PB (Trans M) ! 0 = Trans (P M ! 0)
          \<and> bpHeadV (Trans M) = enat (entry M 1 0)"
      using core by simp
  qed
next
  have core: "bpHeadV (Trans M) = enat (entry M 1 0)"
    using m_7_3_Trans_leftend MR by blast
  \<comment> \<open>(3)\<close>
  show "nextR M 1 0 1 \<longrightarrow>
          bpHeadV (Trans M) = enat (entry M 1 0)
          \<and> (\<exists>t. PB (Trans M) ! 0 = Dpt (enat (entry M 1 0)) t \<and> t \<noteq> 0\<^sub>B)"
  proof (intro impI)
    assume nx: "nextR M 1 0 1"
    \<comment> \<open>\<open>(1,0) <\<^bsub>M\<^esub>\<^sup>Next (1,1)\<close> needs \<open>Lng M > 1\<close>\<close>
    have L: "1 < Lng M"
      using nx by (auto simp: nextR_def nextrel1_def split: if_splits)
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    \<comment> \<open>the leftmost PC is principal with head \<open>D\<^bsub>entry M 1 0\<^esub>\<close> and nonzero tail
       (whose own head is the second character \<open>D\<^bsub>u\<^esub>\<close>)\<close>
    have lpc: "\<exists>t. PB (Trans M) ! 0 = Dpt (enat (entry M 1 0)) t \<and> t \<noteq> 0\<^sub>B"
      using trans_leftmost_pc_two_chars[OF MR nx] by blast
    show "bpHeadV (Trans M) = enat (entry M 1 0)
          \<and> (\<exists>t. PB (Trans M) ! 0 = Dpt (enat (entry M 1 0)) t \<and> t \<noteq> 0\<^sub>B)"
      using core lpc by simp
  qed
qed

end

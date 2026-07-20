theory Frontier_6_061
  imports Support_6_041
begin

section \<open>§6.6 KEYSTONE chain — (e) 補題（簡約性と左端の関係） and the keystone iff\<close>

text \<open>Helper (b-flavour): in a reduced mono sequence the row-0 left end dominates
  the row-1 left end, \<open>entry M 1 0 \<le> entry M 0 0\<close>.  Empirically 55/0 on reduced
  mono sequences (and \<open>Red\<close>-output always satisfies it, 4368/0).

  Proof.  Unfold \<open>Red M = M\<close> once (\<open>M\<close> mono so neither zero nor multi):
  \<^item> core (\<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close>): \<open>m\<^sub>1\<^sub>0 = 0 \<le> m\<^sub>0\<^sub>0\<close>.
  \<^item> shift (\<open>m\<^sub>1\<^sub>0 = 0\<close>, \<open>m\<^sub>0\<^sub>0 > 0\<close>): \<open>m\<^sub>1\<^sub>0 = 0 \<le> m\<^sub>0\<^sub>0\<close>.
  \<^item> \<open>m\<^sub>1\<^sub>0 > 0\<close>: the dead branch \<^bold>\<open>[20]\<close> is excluded by
    @{thm [source] m_6_5_monoT_Red_m10pos} (the productive guard holds), so
    \<open>Red M\<close> is the rebase \<open>map (\<lambda>j. (N\<^bsub>0,j\<^esub> - N\<^bsub>0,m\<^sub>1\<^sub>0\<^esub> + N\<^bsub>1,m\<^sub>1\<^sub>0\<^esub>, N\<^bsub>1,j\<^esub>)) [m\<^sub>1\<^sub>0..]\<close>;
    its position-0 row-0 value is \<open>N\<^bsub>0,m\<^sub>1\<^sub>0\<^esub> - N\<^bsub>0,m\<^sub>1\<^sub>0\<^esub> + N\<^bsub>1,m\<^sub>1\<^sub>0\<^esub> = N\<^bsub>1,m\<^sub>1\<^sub>0\<^esub>\<close> and its
    position-0 row-1 value is also \<open>N\<^bsub>1,m\<^sub>1\<^sub>0\<^esub>\<close>, so they are equal.\<close>

lemma kst_reduced_row1_le_row0:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
  shows "entry M 1 0 \<le> entry M 0 0"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  let ?j1  = "Lng M - 1"
  let ?j1' = "TrMax M"
  let ?m00 = "entry M 0 0"
  let ?m10 = "entry M 1 0"
  show "?m10 \<le> ?m00"
  proof (cases "?m00 = 0 \<and> ?m10 = 0")
    case True
    thus ?thesis by simp
  next
    case nc: False
    show ?thesis
    proof (cases "?m10 = 0")
      case True
      thus ?thesis by simp
    next
      case False
      hence c1p: "0 < ?m10" by simp
      have MPT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
      let ?arg = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
      have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
        using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
      have arg_T: "?arg \<in> T_PS" using funpow_ne by (simp add: T_PS_def)
      let ?N = "Red ?arg"
      let ?jN = "Lng ?N - 1"
      have rM: "Red M = (let N = ?N; jN = ?jN in
                 if ?m10 \<le> jN \<and> seg N ?m10 jN \<in> PT_PS then
                   map (\<lambda>j. (entry N 0 j - entry N 0 ?m10 + entry N 1 ?m10,
                             entry N 1 j))
                       [?m10..<Suc jN]
                 else M)"
        using Red.psimps[OF dom] nz nmu nc c1p by (simp add: Let_def)
      \<comment> \<open>the dead branch [20] is excluded: the productive guard holds.\<close>
      have segPT: "seg ?N ?m10 ?jN \<in> PT_PS"
        using m_6_5_monoT_Red_m10pos[OF MPT c1p] by simp
      have segne: "seg ?N ?m10 ?jN \<noteq> []"
        using segPT by (simp add: PT_PS_def T_PS_def)
      have m10_le: "?m10 \<le> ?jN"
      proof -
        have "0 < Lng (seg ?N ?m10 ?jN)"
          using segne by (cases "seg ?N ?m10 ?jN") auto
        hence "0 < Suc ?jN - ?m10" by (simp only: Lng_seg)
        thus ?thesis by simp
      qed
      have then_case: "?m10 \<le> ?jN \<and> seg ?N ?m10 ?jN \<in> PT_PS"
        using m10_le segPT by simp
      have rM': "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10
                                    + entry ?N 1 ?m10, entry ?N 1 j))
                             [?m10..<Suc ?jN]"
        using rM then_case by (simp add: Let_def del: upt_Suc)
      have len0: "0 < length [?m10..<Suc ?jN]" using m10_le by (simp del: upt_Suc)
      have idx0: "[?m10..<Suc ?jN] ! 0 = ?m10"
        using m10_le by (simp add: nth_upt del: upt_Suc)
      have nth0: "(Red M) ! 0 = (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10
                                        + entry ?N 1 ?m10, entry ?N 1 j)) ?m10"
        using rM' len0 idx0 by (simp add: nth_map del: upt_Suc)
      have e_rM0: "entry (Red M) 0 0 = entry ?N 1 ?m10"
        using nth0 unfolding entry_def by simp
      have e_rM1: "entry (Red M) 1 0 = entry ?N 1 ?m10"
        using nth0 unfolding entry_def by simp
      have "?m10 = entry (Red M) 1 0" using redM by simp
      also have "\<dots> = entry ?N 1 ?m10" using e_rM1 .
      also have "\<dots> = entry (Red M) 0 0" using e_rM0 by simp
      also have "\<dots> = ?m00" using redM by simp
      finally show ?thesis by simp
    qed
  qed
qed

end

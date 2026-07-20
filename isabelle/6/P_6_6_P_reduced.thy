theory P_6_6_P_reduced
  imports Support_6_032
begin

text \<open>命題（\<open>P\<close>が簡約性を保つこと）.\<close>

text \<open>§6.6 (A3): \<open>M\<close> is reduced iff every fundamental-sequence block \<open>P M ! J\<close>
  is reduced.  Forward: \<open>m_6_6_Red_P_stable\<close> reduces each block; each block is in
  \<open>T_PS\<close> (nonempty, via \<open>P_blocks_nonempty\<close>).  Backward: if \<open>multiT M\<close> then
  \<open>Red M = concat (map Red (P M))\<close> (\<open>Red.psimps\<close>); blocks-reduced gives
  \<open>map Red (P M) = P M\<close> (pointwise via \<open>nth_equalityI\<close>), so
  \<open>Red M = concat (P M) = M\<close> (\<open>idxsum_concat_P\<close>); else \<open>P M = [M]\<close> and the single
  block is \<open>M\<close> itself, reduced.\<close>

lemma m_6_6_P_reduced:
  assumes M: "M \<in> T_PS"
  shows "M \<in> RT_PS \<longleftrightarrow> (\<forall>J < Lng (P M). P M ! J \<in> RT_PS)"
proof
  assume "M \<in> RT_PS"
  hence red: "Red M = M" by (simp add: RT_PS_def)
  have Mne: "M \<noteq> []" using M by (simp add: T_PS_def)
  show "\<forall>J < Lng (P M). P M ! J \<in> RT_PS"
  proof (intro allI impI)
    fix J assume J: "J < Lng (P M)"
    have memB: "P M ! J \<in> set (P M)" using J by simp
    have BT: "P M ! J \<in> T_PS"
      using P_blocks_nonempty[OF Mne] memB by (auto simp: T_PS_def)
    have "Red (P M ! J) = P M ! J" by (rule m_6_6_Red_P_stable[OF M red J])
    thus "P M ! J \<in> RT_PS" using BT by (simp add: RT_PS_def)
  qed
next
  assume blocks: "\<forall>J < Lng (P M). P M ! J \<in> RT_PS"
  have Mne: "M \<noteq> []" using M by (simp add: T_PS_def)
  have redM: "Red M = M"
  proof (cases "multiT M")
    case True
    have nz: "\<not> zeroT M" using True by (simp add: multiT_def)
    have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF M])
    have rM: "Red M = concat (map Red (P M))"
      using Red.psimps[OF domM] nz True by simp
    have blockeq: "map Red (P M) = P M"
    proof (rule nth_equalityI)
      show "length (map Red (P M)) = length (P M)" by simp
    next
      fix J assume "J < length (map Red (P M))"
      hence J: "J < Lng (P M)" by simp
      have "P M ! J \<in> RT_PS" using blocks J by blast
      hence "Red (P M ! J) = P M ! J" by (simp add: RT_PS_def)
      thus "map Red (P M) ! J = P M ! J" using J by simp
    qed
    have "Red M = concat (P M)" using rM blockeq by simp
    also have "\<dots> = M" by (rule idxsum_concat_P)
    finally show ?thesis .
  next
    case False
    have pm: "P M = [M]" using False by (subst P.simps) simp
    have "0 < Lng (P M)" using pm by simp
    hence "P M ! 0 \<in> RT_PS" using blocks by blast
    hence "Red (P M ! 0) = P M ! 0" by (simp add: RT_PS_def)
    thus ?thesis using pm by simp
  qed
  show "M \<in> RT_PS" using M redM by (simp add: RT_PS_def)
qed


lemma p_6_6_P_reduced:
  assumes "M \<in> T_PS"
  shows "M \<in> RT_PS \<longleftrightarrow> (\<forall>J < Lng (P M). P M ! J \<in> RT_PS)"
  using assms by (rule m_6_6_P_reduced)

end

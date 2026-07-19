theory P_6_5_Red_zeroT
  imports Frontier_6_023
begin

text \<open>系（\<open>Red\<close>が零項性を保つこと）.\<close>

lemma m_6_5_Red_zeroT:
  assumes MT: "M \<in> T_PS"
  shows "zeroT M \<longleftrightarrow> zeroT (Red M)"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have LR: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  show ?thesis
  proof (rule iffI)
    \<comment> \<open>Forward: zeroT M \<Longrightarrow> Red M = [(0,0)], which is zeroT.\<close>
    assume z: "zeroT M"
    have rM: "Red M = [(0, 0)]" using Red.psimps[OF domM] z by simp
    show "zeroT (Red M)" by (simp add: rM zeroT_def entry_def)
  next
    \<comment> \<open>Backward: zeroT (Red M) \<Longrightarrow> zeroT M.
        Prove contrapositive: \<not> zeroT M \<Longrightarrow> \<not> zeroT (Red M).\<close>
    assume zRM: "zeroT (Red M)"
    show "zeroT M"
    proof (rule ccontr)
      assume nz: "\<not> zeroT M"
      \<comment> \<open>Lng (Red M) = Lng M, and zeroT (Red M) gives Lng (Red M) = 1.\<close>
      have L1: "Lng M = 1" using LR zRM by (simp add: zeroT_def)
      \<comment> \<open>entry M 1 0 \<noteq> 0 gives entry (Red M) 1 0 \<noteq> 0 by rz_Red_entry1_nz.\<close>
      have ne: "entry (Red M) 1 0 \<noteq> 0" by (rule rz_Red_entry1_nz[OF MT L1 nz])
      \<comment> \<open>But zeroT (Red M) requires entry (Red M) 1 0 = 0. Contradiction.\<close>
      thus False using zRM by (simp add: zeroT_def)
    qed
  qed
qed


lemma p_6_5_Red_zeroT:
  assumes "M \<in> T_PS"
  shows "zeroT M \<longleftrightarrow> zeroT (Red M)"
  using assms by (rule m_6_5_Red_zeroT)

end

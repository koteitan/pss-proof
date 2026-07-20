theory P_6_5_Red_oper
  imports Support_6_073
begin

text \<open>命題（\<open>Red\<close>と基本列の可換性）.\<close>

text \<open>命題（\<open>Red\<close>と基本列の可換性）, A4 final form.\<close>

lemma m_6_5_Red_oper_final:
  assumes M: "M \<in> anchored_slice" and n1: "1 \<le> n"
  shows "(Red M)[n] = Red ((M::pairseq)[n])"
proof -
  have MT: "M \<in> T_PS" by (rule anchored_slice_imp_T_PS[OF M])
  show ?thesis
  proof (cases "zeroT M")
    case True
    have L1: "Lng M = 1" using True by (simp add: zeroT_def)
    have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
    have rM: "Red M = [(0, 0)]" using Red.psimps[OF domM] True by simp
    have opM: "M[n] = M" by (rule roper_oper_Lng1[OF L1])
    have "(Red M)[n] = Red M" using rM by (intro roper_oper_Lng1) simp
    thus ?thesis using opM by simp
  next
    case False
    hence mono: "monoT M" using m_6_5_anchored_zeroT_or_monoT[OF M] by simp
    let ?c = "entry M 0 0"  let ?m = "entry M 1 0"
    have condA: "RedCondA M"
      by (rule m_6_5_anchored_imp_RedCondA[OF M stdCA_ST_PS])
    have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
    have rb: "Red M = rebaseRow0 ?c ?m M"
      using m_6_5_Red_rebase[OF MT condA nmu] rebase_as_pair_map
      by (simp add: rebaseRow0_def)
    \<comment> \<open>\<open>Red M\<close> is reduced, so its oper stays reduced (today's
        @{thm [source] m_6_6_reduced_oper})\<close>
    have LR: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
    have RT: "Red M \<in> T_PS"
    proof -
      have "M \<noteq> []" using MT by (simp add: T_PS_def)
      hence "0 < Lng M" by (cases M) auto
      hence "0 < Lng (Red M)" using LR by simp
      hence "Red M \<noteq> []" using length_greater_0_conv by blast
      thus ?thesis by (simp add: T_PS_def)
    qed
    have YR: "Red M \<in> RT_PS"
      using m_6_5_Red_idem[OF M] RT by (simp add: RT_PS_def)
    have YnR: "(Red M)[n] \<in> RT_PS" by (rule m_6_6_reduced_oper[OF YR n1])
    \<comment> \<open>commute oper with the rebase\<close>
    have comm: "(Red M)[n] = rebaseRow0 ?c ?m (M[n])"
      using rb oper_rebase_commute[OF MT mono] by simp
    \<comment> \<open>\<open>Red\<close> is blind to the rebase of \<open>M[n]\<close>\<close>
    have MnT: "(M::pairseq)[n] \<in> T_PS" by (rule oper_T_PS[OF MT n1])
    have lbn: "\<And>j. j < Lng (M[n]) \<Longrightarrow> ?c \<le> entry ((M::pairseq)[n]) 0 j"
    proof -
      fix j assume "j < Lng (M[n])"
      hence "((M::pairseq)[n]) ! j \<in> set (M[n])" by (rule nth_mem)
      hence "?c \<le> fst (((M::pairseq)[n]) ! j)"
        by (rule oper_row0_floor[OF MT mono])
      thus "?c \<le> entry ((M::pairseq)[n]) 0 j" by (simp add: entry_def)
    qed
    have congn: "congR ((M::pairseq)[n]) (rebaseRow0 ?c ?m (M[n]))"
      by (rule congR_rebaseRow0[OF lbn])
    have "Red ((M::pairseq)[n]) = Red (rebaseRow0 ?c ?m (M[n]))"
      by (rule cdn_red_cong[OF congn MnT])
    also have "\<dots> = Red ((Red M)[n])" using comm by simp
    also have "\<dots> = (Red M)[n]" using YnR by (simp add: RT_PS_def)
    finally show ?thesis by simp
  qed
qed


lemma p_6_5_Red_oper:
  assumes "M \<in> anchored_slice" "n \<ge> 1"  \<comment> \<open>correction A4\<close>
  shows "(Red M)[n] = Red (M[n])"
  using assms by (rule m_6_5_Red_oper_final)

end

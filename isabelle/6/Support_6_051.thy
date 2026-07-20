theory Support_6_051
  imports Frontier_6_071
begin

text \<open>\<open>zeroT M\<close> branch: \<open>Red M = [(0,0)]\<close> (length 1) and \<open>Lng M = 1\<close>, so both
  sides of the headline collapse to \<open>j0 = 0 \<and> j1 = 0\<close> by @{thm [source] leR_Lng1_eq}.\<close>

lemma m_6_5_Red_le_zeroT:
  assumes MT: "M \<in> T_PS" and z: "zeroT M"
  shows "leR M i j0 j1 = leR (Red M) i j0 j1"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have LM1: "Lng M = 1" using z by (simp add: zeroT_def)
  have rM: "Red M = [(0, 0)]" using Red.psimps[OF domM] z by simp
  have LR1: "Lng (Red M) = 1" using rM by simp
  show ?thesis using leR_Lng1_eq[OF LM1] leR_Lng1_eq[OF LR1] by simp
qed

text \<open>The headline \<open>m_6_5_Red_le\<close> = \<open>p_6_5_Red_le\<close>.  Case split via the GREEN
  @{thm [source] m_6_5_anchored_zeroT_or_monoT}:
  \<^item> \<open>zeroT M\<close>: discharged by @{thm [source] m_6_5_Red_le_zeroT}.
  \<^item> \<open>monoT M\<close>: \<open>RedCondA M\<close> (target (1), under \<open>stdCA\<close>) feeds the mono congruence
    hypothesis \<open>monoCong\<close> to give \<open>congR M (Red M)\<close>, then the GREEN bridge
    @{thm [source] m_6_5_congR_imp_leR_inv}.

  \<open>monoCong\<close> is \<open>m_6_5_congR_self_Red_monoT\<close> (Front A); \<open>stdCA\<close> is
  \<open>ST_PS \<subseteq> RT_PS\<close> + the reduced keystone (= unproven \<open>p_6_7_standard_reduced\<close>).
  Both carried as explicit hypotheses to keep the assembly SOUND; the body cites
  only already-GREEN facts.\<close>

lemma m_6_5_Red_le:
  assumes M: "M \<in> anchored_slice"
    and stdCA: "\<And>S. S \<in> ST_PS \<Longrightarrow> RedCondA S"
    and monoCong: "\<And>N. N \<in> T_PS \<Longrightarrow> RedCondA N \<Longrightarrow> monoT N \<Longrightarrow> congR N (Red N)"
  shows "leR M i j0 j1 = leR (Red M) i j0 j1"
proof -
  have MT: "M \<in> T_PS" by (rule anchored_slice_imp_T_PS[OF M])
  from m_6_5_anchored_zeroT_or_monoT[OF M] show ?thesis
  proof
    assume z: "zeroT M"
    show ?thesis by (rule m_6_5_Red_le_zeroT[OF MT z])
  next
    assume mn: "monoT M"
    have condA: "RedCondA M" by (rule m_6_5_anchored_imp_RedCondA[OF M stdCA])
    have R: "congR M (Red M)" by (rule monoCong[OF MT condA mn])
    show ?thesis by (rule m_6_5_congR_imp_leR_inv[OF R])
  qed
qed

end

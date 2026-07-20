theory Support_7_023
  imports Frontier_7_027
begin

text \<open>命題（\<open>RightNodes\<close>と\<open>RightAnces\<close>の関係） (§7.4, 2745), discharging
  @{text p_7_4_RightAnces_RightNodes}.  Stated on \<open>RT\<^bsub>PS\<^esub>\<close> (the domain
  the rest of §7/§8 uses, matching @{thm [source] m_7_3_Trans_Red}).  The article's
  \<open>M \<in> T\<^bsub>PS\<^esub>\<close> form lifts through \<open>Red\<close> once general \<open>Red\<close>-idempotency on
  multi terms (\<open>Red M \<in> RT\<^bsub>PS\<^esub>\<close>, the deferred §6 P-Red-equivariance blocker;
  @{thm [source] p_6_5_Red_idem} is proved only on \<open>anchored_slice\<close>) is available:
  the lift is \<open>RightAnces M = RightAnces (Red M) = RightNodes (Trans (Red M))
  = RightNodes (Trans M)\<close> via \<open>RightAnces.psimps\<close> and @{thm [source] m_7_3_Trans_Red}.\<close>

lemma m_7_4_RightAnces_RightNodes:
  assumes "M \<in> RT_PS"
  shows "RightAnces M = RightNodes (Trans M)"
  by (rule ra_RightAnces_RightNodes_RT[rule_format, OF assms])

end

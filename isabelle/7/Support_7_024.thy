theory Support_7_024
  imports Frontier_7_028
begin

text \<open>系（非零項の \<open>RightAnces\<close> が非空であること） (§7.4, 2809), discharging
  @{text p_7_4_RightAnces_zeroT}.  On \<open>RT\<^bsub>PS\<^esub>\<close> (cf.
  @{thm [source] m_7_4_RightAnces_RightNodes}): immediate from the
  \<open>RightAnces\<close>=\<open>RightNodes\<circ>Trans\<close> correspondence, the empty-\<open>RightNodes\<close>
  characterisation, and @{thm [source] m_7_3_Trans_zeroT}.\<close>

lemma m_7_4_RightAnces_zeroT:
  assumes "M \<in> RT_PS"
  shows "zeroT M \<longleftrightarrow> RightAnces M = []"
proof -
  have "RightAnces M = RightNodes (Trans M)"
    by (rule m_7_4_RightAnces_RightNodes[OF assms])
  moreover have "RightNodes (Trans M) = [] \<longleftrightarrow> Trans M = 0\<^sub>B"
    by (rule rnsub_RightNodes_empty_iff)
  moreover have "Trans M = 0\<^sub>B \<longleftrightarrow> zeroT M"
    using m_7_3_Trans_zeroT[OF assms] by blast
  ultimately show ?thesis by simp
qed

end

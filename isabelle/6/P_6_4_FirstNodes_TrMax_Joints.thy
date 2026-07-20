theory P_6_4_FirstNodes_TrMax_Joints
  imports Frontier_6_015
begin

text \<open>命題（\<open>FirstNodes\<close>と\<open>TrMax\<close>と\<open>Joints\<close>の関係）.  \<open>J\<close> indexes a branch
  component: the article's \<open>J \<le> Lng (Br M) - 1\<close> is rendered \<open>J < Lng (Br M)\<close>
  to avoid the \<^bold>\<open>nat\<close> truncation artifact when \<open>Br M = []\<close> (where \<open>Lng - 1 = 0\<close>
  would spuriously admit \<open>J = 0\<close> and dereference the empty \<open>Joints M\<close>).\<close>

text \<open>m: 命題（\<open>FirstNodes\<close>と\<open>TrMax\<close>と\<open>Joints\<close>の関係） — discharges
  @{text p_6_4_FirstNodes_TrMax_Joints} (statement rendered with
  \<open>J < Lng (Br M)\<close>).  The joint of a branch component is the row-0 parent of its
  first node, which by @{thm [source] m_6_4_mono_slice_next} lies in the trunk
  (\<open>< TrMax M + 1\<close>); its first node lies strictly right of the trunk.\<close>

lemma m_6_4_FirstNodes_TrMax_Joints:
  assumes M: "M \<in> PT_PS" and J: "J < Lng (Br M)"
  shows "Joints M ! J \<le> TrMax M \<and> TrMax M < FirstNodes M ! J"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with J show False by simp
  qed
  with tb have trlt: "TrMax M < Lng M - 1" by linarith
  have brQ: "Br M = P (seg M (TrMax M + 1) (Lng M - 1))"
    using trne by (simp add: Br_def)
  let ?j0 = "TrMax M + 1"
  let ?Q = "P (seg M ?j0 (Lng M - 1))"
  \<comment> \<open>\<open>FirstNodes M ! J = ?j0 + IdxSum (Br M) ! J\<close>\<close>
  have JIdx: "J < length (IdxSum (Br M))" using J by (simp add: IdxSum_def)
  have fnJ: "FirstNodes M ! J = ?j0 + IdxSum (Br M) ! J"
    using JIdx by (simp add: FirstNodes_def)
  \<comment> \<open>apply \<open>m_6_4_mono_slice_next\<close> at \<open>j0 = TrMax M + 1\<close>\<close>
  have lenQ: "Lng ?Q = Lng (Br M)" using brQ by simp
  have Jle: "J \<le> Lng ?Q - 1" using J lenQ by linarith
  from m_6_4_mono_slice_next[OF M _ _ Jle] trlt
  have hp: "hasParent M 0 (?j0 + IdxSum ?Q ! J)"
    and plt: "parent M 0 (?j0 + IdxSum ?Q ! J) < ?j0" by auto
  have idx_fn: "?j0 + IdxSum ?Q ! J = FirstNodes M ! J"
    using fnJ by (simp add: brQ)
  \<comment> \<open>\<open>Joints M ! J\<close> is exactly this parent\<close>
  have joints_parent: "Joints M ! J = parent M 0 (FirstNodes M ! J)"
    using J by (simp add: Joints_def parent_def)
  have "Joints M ! J \<le> TrMax M"
    using plt joints_parent idx_fn by simp
  moreover have "TrMax M < FirstNodes M ! J" using fnJ by simp
  ultimately show ?thesis ..
qed


lemma p_6_4_FirstNodes_TrMax_Joints:
  assumes "M \<in> PT_PS" "J < Lng (Br M)"
  shows "Joints M ! J \<le> TrMax M \<and> TrMax M < FirstNodes M ! J"
  using assms by (rule m_6_4_FirstNodes_TrMax_Joints)

end

theory Frontier_6_005
  imports P_6_2_P_components_2
begin

text \<open>
  m: 命題（\<open>P\<close>の\<open>IncrFirst\<close>同変性） — discharges @{text p_6_2_P_IncrFirst}.
  Follows from the \<open>IncrFirst\<close>-invariance of \<open>\<le>\<^sub>M\<close> (m_6_1).  We first record that
  \<open>zeroT\<close>, \<open>monoT\<close>, \<open>multiT\<close> and \<open>Pcut\<close> are all invariant under \<open>IncrFirst\<close>,
  since they depend only on \<open>Lng M\<close>, \<open>entry M 1 _\<close> (row 1, unchanged) and \<open>leR M\<close>.
\<close>

lemma IncrFirst_zeroT_eq: "zeroT (IncrFirst M) = zeroT M"
proof (cases "Lng M = 0")
  case True thus ?thesis by (simp add: zeroT_def)
next
  case False
  hence "(0::nat) < Lng M" by simp
  thus ?thesis by (simp add: zeroT_def entry_IncrFirst)
qed

lemma IncrFirst_monoT_eq: "monoT (IncrFirst M) = monoT M"
  by (simp add: monoT_def IncrFirst_zeroT_eq m_6_1_le_IncrFirst_inv)

lemma IncrFirst_multiT_eq: "multiT (IncrFirst M) = multiT M"
  by (simp add: multiT_def IncrFirst_zeroT_eq IncrFirst_monoT_eq)

lemma IncrFirst_Pcut_eq: "Pcut (IncrFirst M) = Pcut M"
  by (simp add: Pcut_def m_6_1_le_IncrFirst_inv)

lemma IncrFirst_take: "IncrFirst (take k M) = take k (IncrFirst M)"
  by (simp add: IncrFirst_def take_map)

lemma IncrFirst_drop: "IncrFirst (drop k M) = drop k (IncrFirst M)"
  by (simp add: IncrFirst_def drop_map)

end

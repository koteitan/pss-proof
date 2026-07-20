theory P_6_1_le_IncrFirst_inv
  imports Frontier_6_001
begin

section \<open>§6 ペア数列の基本性質\<close>

subsection \<open>§6.1 最上行のインクリメント\<close>

text \<open>命題（\<open>\<le>\<^sub>M\<close>の\<open>IncrFirst\<close>不変性） — \<open>\<le>\<^sub>M\<close> and \<open>\<le>\<^bsub>IncrFirst M\<^esub>\<close> coincide.\<close>

text \<open>m: 命題（\<open>\<le>\<^sub>M\<close>の\<open>IncrFirst\<close>不変性） — discharges @{text p_6_1_le_IncrFirst_inv}.\<close>

lemma m_6_1_le_IncrFirst_inv: "leR (IncrFirst M) i j0 j1 = leR M i j0 j1"
  by (simp add: leR_def le0_IncrFirst_eq le1_IncrFirst_eq)


lemma p_6_1_le_IncrFirst_inv:
  shows "leR (IncrFirst M) i j0 j1 \<longleftrightarrow> leR M i j0 j1"
  by (rule m_6_1_le_IncrFirst_inv)

end

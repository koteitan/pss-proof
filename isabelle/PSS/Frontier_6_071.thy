theory Frontier_6_071
  imports Support_6_050
begin

subsection \<open>Target (2): assembling \<open>m_6_5_Red_le\<close>\<close>

text \<open>For a length-1 sequence the only in-range index pair is \<open>(0,0)\<close>, on which
  both \<open>le0\<close> and \<open>le1\<close> are reflexively true; so \<open>leR\<close> is determined by \<open>Lng = 1\<close>
  alone (\<open>leR A i j0 j1 \<longleftrightarrow> j0 = 0 \<and> j1 = 0\<close>), independent of the entries.\<close>

lemma leR_Lng1_eq:
  assumes L: "Lng A = 1"
  shows "leR A i j0 j1 \<longleftrightarrow> (j0 = 0 \<and> j1 = 0)"
proof (cases "j0 = 0 \<and> j1 = 0")
  case True
  have "le0 A 0 0" using L by (simp add: le0_def)
  moreover have "le1 A 0 0" using L by (simp add: le1_def)
  ultimately show ?thesis using True by (simp add: leR_def)
next
  case False
  hence "\<not> (j0 < Lng A \<and> j1 < Lng A)" using L by auto
  thus ?thesis using False by (auto simp: leR_def le0_def le1_def)
qed

end

theory P_7_3_Mark_rightmost1
  imports Frontier_7_023
begin

text \<open>命題（右端第1基点の Mark の基本性質）(content.md 2294), with the
  correction A17 (\<open>\<not> zeroT M\<close> excludes the degenerate zero base \<open>[(0,0)]\<close> on
  which the verbatim article form fails).  Forward direction reuses
  @{thm [source] Mark_rightmost1_forward}; the reverse is the contrapositive
  via @{thm [source] Mark_leftend_form} and @{thm [source] Mark_tail_nonzero}.\<close>

lemma m_7_3_Mark_rightmost1:
  assumes "(M, m) \<in> Marked" and "M \<in> RT_PS" and "\<not> zeroT M"
  shows "(m = Lng M - 1) \<longleftrightarrow> (Mark M m = Dpt (enat (entry M 1 m)) 0\<^sub>B)"
proof
  assume mj1: "m = Lng M - 1"
  have "Mark M (Lng M - 1) = Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B"
    using Mark_rightmost1_forward[OF assms(2) assms(3)] assms(1) mj1 by simp
  thus "Mark M m = Dpt (enat (entry M 1 m)) 0\<^sub>B" using mj1 by simp
next
  assume eq: "Mark M m = Dpt (enat (entry M 1 m)) 0\<^sub>B"
  show "m = Lng M - 1"
  proof (rule ccontr)
    assume "m \<noteq> Lng M - 1"
    moreover have "m < Lng M"
    proof -
      have "leR M 0 m (Lng M - 1)" using assms(1) by (simp add: Marked_def)
      thus ?thesis by (simp add: leR_def le0_def)
    qed
    ultimately have mlt: "m < Lng M - 1" by linarith
    have "Mark M m \<noteq> Dpt (enat (entry M 1 m)) 0\<^sub>B"
      using Mark_tail_nonzero assms(1) assms(2) mlt by blast
    thus False using eq by simp
  qed
qed


text \<open>命題（右端第\<open>1\<close>基点の\<open>Mark\<close>の基本性質） (§7.3, 2296).\<close>


text \<open>This proposition records the corrected form in
  @{file "../../corrections.md"}; the original annotation above is retained for
  comparison.\<close>

lemma p_7_3_Mark_rightmost1:
  assumes "(M, m) \<in> Marked" "M \<in> RT_PS" "\<not> zeroT M"
  shows "(m = Lng M - 1) \<longleftrightarrow> (Mark M m = Dpt (enat (entry M 1 m)) 0\<^sub>B)"
  using assms by (rule m_7_3_Mark_rightmost1)

end

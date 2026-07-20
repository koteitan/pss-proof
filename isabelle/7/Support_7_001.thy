theory Support_7_001
  imports pss_paper
begin

section \<open>§7.4 許容的親子関係 (Admissible parent relation)\<close>

text \<open>Transitivity of \<open>\<le>\<^sub>M\<close> on row 1, and the unified \<open>leR\<close>.\<close>

lemma le1_trans:
  assumes "le1 M a b" "le1 M b c"
  shows "le1 M a c"
  using assms by (auto simp: le1_def intro: rtranclp_trans)

lemma leR_trans:
  assumes "leR M i a b" "leR M i b c"
  shows "leR M i a c"
  using assms by (cases "i = 0") (auto simp: leR_def intro: le0_trans le1_trans)

text \<open>A single \<open>nextR\<close>-step is an instance of \<open>\<le>\<^sub>M\<close> (row \<open>i = 0\<close> or row 1).\<close>

lemma nextR_imp_leR:
  assumes "nextR M i j0 j1"
  shows "leR M i j0 j1"
proof (cases "i = 0")
  case True
  hence "nextrel0 M j0 j1" using assms by (simp add: nextR_def)
  thus ?thesis using True
    by (auto simp: leR_def le0_def nextrel0_def intro: r_into_rtranclp)
next
  case False
  hence "nextrel1 M j0 j1" using assms by (simp add: nextR_def)
  thus ?thesis using False
    by (auto simp: leR_def le1_def nextrel1_def intro: r_into_rtranclp)
qed

end

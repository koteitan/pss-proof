theory Frontier_7_039
  imports P_7_4_Mark_Trans_repr
begin

(* ===== integrated from wt-73 ===== *)

section \<open>§7.3 系（条件(II)か(IV)の下で \<open>t\<^sub>2\<close> が \<open>0\<close> でないこと）— content.md 2310\<close>

text \<open>If \<open>j\<close> is non-\<open>M\<close>-admissible then its admissibilization \<open>Adm\<^sub>M(j)\<close> is the
  largest admissible index strictly below \<open>j\<close>, hence \<open>< j\<close>.  (\<open>j = 0\<close> is always
  admissible, so a non-admissible \<open>j\<close> is \<open>> 0\<close>, and \<open>0\<close> witnesses the set whose
  \<open>Max\<close> defines \<open>Adm\<close>.)\<close>

lemma nadm_Adm_lt:
  assumes "\<not> adm M j"
  shows "Adm M j < j"
proof -
  have nad: "nadm M j" using assms by (simp add: adm_def)
  have jpos: "j > 0"
  proof (rule ccontr)
    assume "\<not> j > 0"
    hence "j = 0" by simp
    thus False using nad adm_index0 by (simp add: adm_def)
  qed
  let ?S = "{j'. adm M j' \<and> j' < j}"
  have fin: "finite ?S" by simp
  have ne: "?S \<noteq> {}" using adm_index0 jpos by auto
  have AdmEq: "Adm M j = Max ?S" using assms by (simp add: Adm_def)
  have "Max ?S \<in> ?S" using fin ne by (rule Max_in)
  hence "Max ?S < j" by simp
  thus ?thesis using AdmEq by simp
qed

end

theory Frontier_7_001
  imports Support_7_001
begin

text \<open>
  Chaining: if every index \<open>j'\<close> in \<open>{a+1..j}\<close> is the row-1 child of its
  predecessor (\<open>nextrel1 M (j'-1) j'\<close>), then \<open>a\<close> reaches \<open>j\<close> in row 1.
\<close>

lemma nextrel1_chain:
  assumes "a \<le> j"
    and "\<forall>j'. a < j' \<and> j' \<le> j \<longrightarrow> nextrel1 M (j' - 1) j'"
  shows "(nextrel1 M)\<^sup>*\<^sup>* a j"
  using assms
proof (induction j rule: less_induct)
  case (less j)
  show ?case
  proof (cases "a = j")
    case True
    thus ?thesis by simp
  next
    case False
    with less.prems(1) have aj: "a < j" by simp
    hence j1: "j - 1 < j" by simp
    have alej1: "a \<le> j - 1" using aj by simp
    have hyp: "\<forall>j'. a < j' \<and> j' \<le> j - 1 \<longrightarrow> nextrel1 M (j' - 1) j'"
      using less.prems(2) by auto
    have chain: "(nextrel1 M)\<^sup>*\<^sup>* a (j - 1)"
      by (rule less.IH[OF j1 alej1 hyp])
    have step: "nextrel1 M (j - 1) j"
      using less.prems(2) aj by auto
    from chain step show ?thesis by (rule rtranclp.rtrancl_into_rtrancl)
  qed
qed

text \<open>
  KEY SUB-LEMMA: the admissibilization \<open>Adm\<^sub>M(j)\<close> is a row-1 ancestor of \<open>j\<close>
  (for \<open>j \<le> Lng M - 1\<close>).  Every index strictly between \<open>Adm\<^sub>M(j)\<close> and \<open>j\<close> is
  non-admissible (by maximality of \<open>Adm\<^sub>M(j)\<close>), and a non-admissible index
  below \<open>Lng M\<close> is the row-1 child of its predecessor.
\<close>

lemma adm_row1_ancestry:
  assumes "M \<in> T_PS" "j \<le> Lng M - 1"
  shows "leR M 1 (Adm M j) j"
proof -
  have L: "Lng M \<ge> 1" using assms(1) by (cases M) (auto simp: T_PS_def)
  let ?a = "Adm M j"
  have ale: "?a \<le> j" by (rule adm_Adm_le)
  have jL: "j < Lng M" using assms(2) L by linarith
  have aL: "?a < Lng M" using ale jL by simp
  have steps: "\<forall>j'. ?a < j' \<and> j' \<le> j \<longrightarrow> nextrel1 M (j' - 1) j'"
  proof (intro allI impI)
    fix j' assume a: "?a < j' \<and> j' \<le> j"
    have nadm: "\<not> adm M j'"
    proof
      assume "adm M j'"
      hence "j' \<le> ?a" using adm_Adm_max[of M j' j] a by simp
      with a show False by simp
    qed
    have j'L: "j' < Lng M" using a jL by simp
    from nadm have "nadm M j'" by (simp add: adm_def)
    hence "nextR M 1 (j' - 1) j' \<and> nextR M 1 j' (j' + 1)"
      using j'L by (auto simp: nadm_def)
    thus "nextrel1 M (j' - 1) j'" by (simp add: nextR_def)
  qed
  have chain: "(nextrel1 M)\<^sup>*\<^sup>* ?a j" by (rule nextrel1_chain[OF ale steps])
  show ?thesis using chain ale aL jL by (simp add: leR_def le1_def)
qed

end

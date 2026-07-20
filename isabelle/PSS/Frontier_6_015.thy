theory Frontier_6_015
  imports P_6_4_mono_slice_next
begin

text \<open>The trunk-right-end set is bounded by \<open>Lng M - 1\<close> and contains \<open>0\<close>, so
  \<open>TrMax M\<close> is well-defined and \<open>\<le> Lng M - 1\<close>.\<close>

lemma TrMax_bound:
  assumes "M \<in> T_PS"
  shows "TrMax M \<le> Lng M - 1"
proof -
  let ?S = "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  have LM: "Lng M > 0" using assms by (cases M) (auto simp: T_PS_def)
  \<comment> \<open>\<open>?S \<subseteq> {..Lng M - 1}\<close>: any \<open>j > Lng M - 1\<close> fails at \<open>j' = Lng M - 1\<close>.\<close>
  have sub: "?S \<subseteq> {..Lng M - 1}"
  proof
    fix j assume "j \<in> ?S"
    hence H: "\<forall>j'<j. nextR M 1 j' (j' + 1)" by simp
    show "j \<in> {..Lng M - 1}"
    proof (rule ccontr)
      assume "j \<notin> {..Lng M - 1}"
      hence "Lng M - 1 < j" by simp
      hence "nextR M 1 (Lng M - 1) ((Lng M - 1) + 1)" using H by blast
      hence "(Lng M - 1) + 1 < Lng M" by (simp add: nextR_def nextrel1_def)
      thus False using LM by simp
    qed
  qed
  hence fin: "finite ?S" by (rule finite_subset) simp
  have z: "0 \<in> ?S" by simp
  hence ne: "?S \<noteq> {}" by blast
  have "TrMax M = Max ?S" by (simp add: TrMax_def)
  also have "Max ?S \<le> Lng M - 1"
  proof -
    have "Max ?S \<in> ?S" using fin ne by (rule Max_in)
    thus ?thesis using sub by auto
  qed
  finally show ?thesis .
qed

end

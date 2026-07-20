theory Frontier_6_019
  imports P_6_6_condAB_coeff
begin

text \<open>
  Parent maximality: if \<open>j0\<close> is the (unique) row-\<open>i\<close> parent of \<open>j1\<close> and \<open>j\<close>
  is a row-\<open>i\<close> ancestor of \<open>j1\<close> with \<open>j < j1\<close>, then \<open>j \<le> j0\<close> (the last step
  into \<open>j1\<close> must come from the unique parent \<open>j0\<close>).
\<close>

lemma parent_max:
  assumes "hasParent M i j1" "nextR M i j0 j1"
    and "leR M i j j1" "j < j1"
  shows "j \<le> j0"
proof (cases "i = 0")
  case True
  from assms(3) True have rt: "(nextrel0 M)\<^sup>*\<^sup>* j j1" by (simp add: leR_def le0_def)
  from rt assms(4) obtain p where jp: "(nextrel0 M)\<^sup>*\<^sup>* j p" and pj1: "nextrel0 M p j1"
    by (cases rule: rtranclp.cases) auto
  have "nextR M i p j1" using pj1 True by (simp add: nextR_def)
  hence "p = j0" using assms(1,2) unfolding hasParent_def by (metis (mono_tags))
  moreover have "j \<le> p" using jp by (rule nextrel0_rtrancl_mono)
  ultimately show ?thesis by simp
next
  case False
  from assms(3) False have rt: "(nextrel1 M)\<^sup>*\<^sup>* j j1" by (simp add: leR_def le1_def)
  from rt assms(4) obtain p where jp: "(nextrel1 M)\<^sup>*\<^sup>* j p" and pj1: "nextrel1 M p j1"
    by (cases rule: rtranclp.cases) auto
  have "nextR M i p j1" using pj1 False by (simp add: nextR_def)
  hence "p = j0" using assms(1,2) unfolding hasParent_def by (metis (mono_tags))
  moreover have "j \<le> p" using jp by (rule nextrel1_rtrancl_mono)
  ultimately show ?thesis by simp
qed

end

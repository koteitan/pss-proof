theory Frontier_6_009
  imports P_6_3_adm_slice
begin

text \<open>\<open>0\<close> is always \<open>M\<close>-admissible (\<open>(1,-1) <\<^sup>Next (1,0)\<close> is impossible).\<close>

lemma adm_zero: "adm M 0"
proof -
  have "\<not> nextR M 1 0 0" by (simp add: nextR_def nextrel1_def)
  hence "\<not> nadm M 0" by (auto simp: nadm_def)
  thus ?thesis by (simp add: adm_def)
qed

text \<open>The admissible set below a non-admissible \<open>j\<close> is finite and non-empty.\<close>

lemma adm_below_set_finite: "finite {j'. adm M j' \<and> j' < j}"
  by (rule finite_subset[of _ "{..<j}"]) auto

lemma adm_below_set_nonempty:
  assumes "\<not> adm M j"
  shows "{j'. adm M j' \<and> j' < j} \<noteq> {}"
proof -
  have "0 < j"
  proof (rule ccontr)
    assume "\<not> 0 < j"
    hence "j = 0" by simp
    thus False using assms adm_zero by simp
  qed
  thus ?thesis using adm_zero by blast
qed

text \<open>\<open>Adm M j\<close> is itself \<open>M\<close>-admissible.\<close>

lemma adm_Adm_adm: "adm M (Adm M j)"
proof (cases "adm M j")
  case True thus ?thesis by (simp add: Adm_def)
next
  case False
  let ?S = "{j'. adm M j' \<and> j' < j}"
  have "Max ?S \<in> ?S"
    by (rule Max_in[OF adm_below_set_finite adm_below_set_nonempty[OF False]])
  hence "adm M (Max ?S)" by simp
  thus ?thesis using False by (simp add: Adm_def)
qed

text \<open>\<open>Adm M j \<le> j\<close>.\<close>

lemma adm_Adm_le: "Adm M j \<le> j"
proof (cases "adm M j")
  case True thus ?thesis by (simp add: Adm_def)
next
  case False
  let ?S = "{j'. adm M j' \<and> j' < j}"
  have "Max ?S \<in> ?S"
    by (rule Max_in[OF adm_below_set_finite adm_below_set_nonempty[OF False]])
  hence "Max ?S < j" by simp
  thus ?thesis using False by (simp add: Adm_def)
qed

text \<open>Maximality: any admissible \<open>k \<le> j\<close> is \<open>\<le> Adm M j\<close>.\<close>

lemma adm_Adm_max:
  assumes "adm M k" "k \<le> j"
  shows "k \<le> Adm M j"
proof (cases "adm M j")
  case True thus ?thesis using assms by (simp add: Adm_def)
next
  case False
  let ?S = "{j'. adm M j' \<and> j' < j}"
  have kj: "k < j" using assms False by (cases "k = j") auto
  hence "k \<in> ?S" using assms(1) by simp
  hence "k \<le> Max ?S" by (rule Max_ge[OF adm_below_set_finite])
  thus ?thesis using False by (simp add: Adm_def)
qed

end

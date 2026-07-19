theory Frontier_6_091
  imports P_6_5_Red_marked
begin

section \<open>§6.6 系（\<open>1\<close>列ペア数列の基本性質） / 命題（\<open>P\<close>が簡約性を保つこと）\<close>

text \<open>The value of \<open>Red\<close> on singletons, via the closed form
  @{thm [source] m_6_5_Red_rebase} (a singleton is \<open>zeroT\<close> or \<open>monoT\<close> with
  vacuous \<open>RedCondA\<close>): \<open>Red [(a,b)] = [(b,b)]\<close>.\<close>

lemma Red_singleton: "Red [(a, b)] = [(b, b)]"
proof -
  let ?M = "[(a, b)]"
  have MT: "?M \<in> T_PS" by (simp add: T_PS_def)
  have domM: "Red_dom ?M" by (rule m_6_5_Red_welldef[OF MT])
  show ?thesis
  proof (cases "b = 0")
    case True
    hence z: "zeroT ?M" by (simp add: zeroT_def entry_def)
    show ?thesis using Red.psimps[OF domM] z True by simp
  next
    case False
    hence nz: "\<not> zeroT ?M" by (simp add: zeroT_def entry_def)
    have mono: "monoT ?M"
    proof -
      have "le0 ?M 0 0" by (simp add: le0_def)
      thus ?thesis using nz by (simp add: monoT_def leR_def)
    qed
    have nmu: "\<not> multiT ?M" using mono by (simp add: multiT_def)
    have condA: "RedCondA ?M"
    proof -
      have "\<And>i j1'. \<not> hasParent ?M i j1'"
        by (auto simp: hasParent_def nextR_def nextrel0_def nextrel1_def)
      thus ?thesis by (simp add: RedCondA_def)
    qed
    have "Red ?M = map (\<lambda>j. (entry ?M 0 j - entry ?M 0 0 + entry ?M 1 0,
                              entry ?M 1 j)) [0..<Lng ?M]"
      by (rule m_6_5_Red_rebase[OF MT condA nmu])
    thus ?thesis by (simp add: entry_def)
  qed
qed

end

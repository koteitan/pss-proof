theory Frontier_7_005
  imports Support_7_002
begin

\<comment> \<open>RightNodes only depends on the last principal component.\<close>
lemma rnsub_RightNodes_last:
  "xs \<noteq> [] \<Longrightarrow> RightNodes (Trm xs) = RightNodes (Trm [last xs])"
  by (cases xs) simp_all

\<comment> \<open>\<open>flatBT a\<close> never starts with \<open>Zsym\<close> unless \<open>a = 0\<close>; and never starts with \<open>RP\<close>.\<close>
lemma rnsub_flat_hd:
  "flatBT a = Zsym # rest \<Longrightarrow> a = Trm [] \<and> rest = []"
  by (cases a rule: flatBT.cases) (auto elim: flatBP.elims)

end

theory Frontier_6_001
  imports After_5
begin

section \<open>§6.1 最上行のインクリメント\<close>

lemma Lng_IncrFirst[simp]: "Lng (IncrFirst M) = Lng M"
  by (simp add: IncrFirst_def)

lemma entry_IncrFirst:
  "j < Lng M \<Longrightarrow>
   entry (IncrFirst M) i j = (if i = 0 then Suc (entry M 0 j) else entry M i j)"
  by (simp add: IncrFirst_def entry_def)

lemma nextrel0_IncrFirst_eq: "nextrel0 (IncrFirst M) = nextrel0 M"
proof (intro ext)
  fix j0 j1
  show "nextrel0 (IncrFirst M) j0 j1 = nextrel0 M j0 j1"
    unfolding nextrel0_def by (auto simp: entry_IncrFirst)
qed

lemma le0_IncrFirst_eq: "le0 (IncrFirst M) = le0 M"
  by (intro ext) (simp add: le0_def nextrel0_IncrFirst_eq)

lemma nextrel1_IncrFirst_eq: "nextrel1 (IncrFirst M) = nextrel1 M"
proof (intro ext)
  fix j0 j1
  show "nextrel1 (IncrFirst M) j0 j1 = nextrel1 M j0 j1"
    unfolding nextrel1_def
    by (auto simp: entry_IncrFirst le0_IncrFirst_eq le0_def)
qed

lemma le1_IncrFirst_eq: "le1 (IncrFirst M) = le1 M"
  by (intro ext) (simp add: le1_def nextrel1_IncrFirst_eq)

end

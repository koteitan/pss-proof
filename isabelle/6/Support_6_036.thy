theory Support_6_036
  imports Frontier_6_053
begin

lemma congR_funpow_IncrFirst:
  "congR A X \<Longrightarrow> congR ((IncrFirst ^^ k) A) ((IncrFirst ^^ k) X)"
  by (induction k) (simp_all add: congR_IncrFirst)

end

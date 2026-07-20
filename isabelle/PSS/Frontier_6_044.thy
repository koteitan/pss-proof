theory Frontier_6_044
  imports Support_6_026
begin

text \<open>@{const IdxSum} only reads block lengths, which @{const IncrFirst}
  preserves, so it is invariant under \<open>map IncrFirst\<close>.\<close>

lemma length_o_IncrFirst: "(length \<circ> IncrFirst) = length"
  by (rule ext) (simp add: IncrFirst_def)

lemma IdxSum_map_IncrFirst: "IdxSum (map IncrFirst Q) = IdxSum Q"
  by (simp add: IdxSum_def take_map length_o_IncrFirst)

end

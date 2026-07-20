theory Frontier_6_022
  imports Support_6_005
begin

text \<open>Iterated \<open>IncrFirst\<close>-invariance of \<open>le0\<close>/\<open>le1\<close> (point-free), used by fact2a.\<close>

lemma le0_funpow_IncrFirst_eq: "le0 ((IncrFirst ^^ k) M) = le0 M"
  by (induction k) (simp_all add: le0_IncrFirst_eq)

end

theory Support_7_002
  imports Frontier_7_004
begin

\<comment> \<open>Basic RightNodes computation on a nonempty term.\<close>
lemma rnsub_RightNodes_cons:
  "RightNodes (Trm (x # xs)) =
     (case last (x # xs) of DB u a \<Rightarrow> the_enat u # RightNodes a)"
  by simp

lemma rnsub_RightNodes_Dpt:
  "RightNodes (Dpt (enat v) t) = v # RightNodes t"
  by simp

end

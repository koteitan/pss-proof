theory Support_7_003
  imports Frontier_7_005
begin

lemma rnsub_flat_nonempty: "flatBT a \<noteq> []"
  by (cases a rule: flatBT.cases) (auto elim: flatBP.elims)

\<comment> \<open>\<open>Lng (PB t)\<close> is the number of top-level components.\<close>
lemma rnsub_Lng_PB: "Lng (PB t) = length (untrm t)"
  by (simp add: PB_def)

end

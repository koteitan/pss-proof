theory Support_7_004
  imports Frontier_7_006
begin

\<comment> \<open>spineSub preserves the top-level component count (only the last is touched).\<close>
lemma rnsub_spineSub_len:
  "xs \<noteq> [] \<Longrightarrow> length (untrm (spineSub (Trm xs) t)) = length xs"
  by (cases "last xs") (auto split: list.split)

end

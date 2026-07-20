theory Frontier_7_055
  imports Support_7_050
begin

subsection \<open>The stabilisation predicate and the domain transport\<close>

definition RedStab :: "pairseq \<Rightarrow> bool" where
  "RedStab M \<longleftrightarrow> (\<exists>k. (Red ^^ k) M \<in> RT_PS)"

end

theory Frontier_7_017
  imports Support_7_013
begin

text \<open>Pure paren-depth weight \<open>gs_pw\<close> (\<open>LP \<mapsto> 1\<close>, \<open>RP \<mapsto> -1\<close>, else \<open>0\<close>): unlike
  \<open>flatinj_w\<close> (which charges \<open>Zsym\<close>) this is the genuine bracket depth.  Total over
  a complete flat is \<open>0\<close>; every prefix is \<open>\<ge> 0\<close>.  Used to rule out a complete
  \<open>flatBP\<close> ending exactly at the tuple wrap \<open>RP\<close> (the \<open>b \<noteq> []\<close> obligation).\<close>

fun gs_pw :: "Sym \<Rightarrow> int" where
  "gs_pw LP = 1"
| "gs_pw RP = -1"
| "gs_pw CM = 0"
| "gs_pw Zsym = 0"
| "gs_pw (Dsym u) = 0"

definition gs_pwsum :: "Sym list \<Rightarrow> int" where
  "gs_pwsum xs = sum_list (map gs_pw xs)"

end

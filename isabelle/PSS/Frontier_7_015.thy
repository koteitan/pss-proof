theory Frontier_7_015
  imports Support_7_011
begin

section \<open>Front B (wf14) — scb cut-pinning: \<open>rnsub_cut_ge_pre\<close> and kind-uniqueness\<close>

text \<open>
  The marked principal of an scb-shaped occurrence never starts strictly before
  the canonical last top-level component.  The engine \<open>rnsub_peel_components\<close>
  (below): an scb occurrence \<open>s \<frown> flatBP P \<frown> b\<close> (\<open>b\<close> all-\<open>)\<close>) of a string whose
  leading part is a run of complete top-level components
  \<open>concat (map (\<lambda>r. flatBP r \<frown> [CM]) ms)\<close> must have its cut \<open>s\<close> reach past that
  whole run.  Each unit \<open>flatBP r \<frown> [CM]\<close> ends in a top-level \<open>CM\<close> (weight \<open>+1\<close>,
  depth \<open>0\<close>) which the all-\<open>)\<close> tail cannot contain; a straddle of the marked
  principal across that \<open>CM\<close> is excluded by the @{const flatinj_dsum}
  prefix-nonnegativity of \<open>flatBP P\<close>.
\<close>

\<comment> \<open>A complete principal/term string is nonempty and never ends in \<open>CM\<close>.\<close>
lemma flatBT_last_not_CM:
  "flatBT t \<noteq> [] \<and> last (flatBT t) \<noteq> CM"
  and flatBP_last_not_CM:
  "flatBP p \<noteq> [] \<and> last (flatBP p) \<noteq> CM"
proof (induct t and p rule: flatBT_flatBP.induct)
  case 1 show ?case by simp
next
  case (2 p) thus ?case by simp
next
  case (3 p q ps) show ?case by simp
next
  case (4 u a) thus ?case by simp
qed

end

theory Support_6_054
  imports Frontier_6_074
begin

text \<open>§6.7 oper-tiling brick (Front B, ROW 1): the FULL row-1 obligation of
  \<open>RedCondA (N[n])\<close>, assembled from the GREEN verbatim PREFIX brick
  @{thm [source] operCA_tiling_row1_prefix} (columns \<open>x < j\<^sub>0\<close>) and the WITHIN-BLOCK
  / BOUNDARY obligation \<open>within1\<close> (columns \<open>j\<^sub>0 \<le> x\<close>), carried here as an explicit
  hypothesis.  Splitting on \<open>x < j\<^sub>0\<close> vs \<open>j\<^sub>0 \<le> x\<close> covers every column of \<open>N[n]\<close>,
  so the two pieces together give the row-1 \<open>+1\<close> step for all \<open>x\<close>.  This is the
  unconditional structural glue: once \<open>within1\<close> lands it yields the full row-1
  obligation feeding @{thm [source] operCA_tiling_assemble}.\<close>

lemma operCA_tiling_row1:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and within1: "\<And>x. parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x
                   \<Longrightarrow> hasParent ((N::pairseq)[n]) 1 x
                   \<Longrightarrow> entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
                        = entry ((N::pairseq)[n]) 1 x"
    and hpn: "hasParent ((N::pairseq)[n]) 1 x"
  shows "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
       = entry ((N::pairseq)[n]) 1 x"
proof (cases "x < parent N (idx1 N (Lng N - 1)) (Lng N - 1)")
  case True
  show ?thesis
    by (rule operCA_tiling_row1_prefix[OF L notzero hp j0lt condA True hpn])
next
  case False
  hence ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x" by simp
  show ?thesis by (rule within1[OF ge hpn])
qed

end

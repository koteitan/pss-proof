theory Support_6_053
  imports Frontier_6_073
begin

text \<open>§6.7 oper-tiling brick (Front B, ROW 1): the row-1 entries of \<open>N[n]\<close> are
  VERBATIM at the period base (\<open>d\<^sub>1 = 0\<close> always, since \<open>i\<^sub>1 \<le> 1\<close>).  For any
  column \<open>z < Lng(N[n])\<close>, \<open>entry (N[n]) 1 z = entry N 1 (base z)\<close> where
  \<open>base z = z\<close> on the prefix \<open>z < j\<^sub>0\<close> and \<open>base z = j\<^sub>0 + (z-j\<^sub>0) mod w\<close> on the
  blocks.  Immediate from @{thm [source] operB_gen_entry_prefix} (prefix) and
  @{thm [source] oper_gen_block_entry1} (blocks).\<close>

lemma operCA_tiling_entry1_base:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and zlt: "z < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + n * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "entry ((N::pairseq)[n]) 1 z
       = entry N 1 (if z < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then z
            else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (z - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  have w0: "0 < ?w" using j0lt by linarith
  show ?thesis
  proof (cases "z < ?j0")
    case True
    thus ?thesis using operB_gen_entry_prefix[OF L notzero hp True, of n 1] by simp
  next
    case False
    hence ge: "?j0 \<le> z" by simp
    let ?q = "(z - ?j0) div ?w"  let ?s = "(z - ?j0) mod ?w"
    have sw: "?s < ?w" using w0 by simp
    have zmj: "z - ?j0 < n * ?w" using zlt ge by linarith
    have qn: "?q < n" using less_mult_imp_div_less[OF zmj] .
    have dm: "?q * ?w + ?s = z - ?j0"
      using div_mult_mod_eq[of "z - ?j0" ?w] by (simp add: mult.commute)
    have zsplit: "z = ?j0 + ?q * ?w + ?s" using dm ge by linarith
    have "entry ((N::pairseq)[n]) 1 (?j0 + ?q * ?w + ?s) = entry N 1 (?j0 + ?s)"
      by (rule oper_gen_block_entry1[OF L notzero hp j0lt qn sw])
    thus ?thesis using zsplit False by simp
  qed
qed

end

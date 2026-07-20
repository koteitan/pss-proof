theory Support_6_056
  imports Frontier_6_076
begin

text \<open>§6.7 oper-tiling ROW-1 reflection — helper 1 (periodic row-1 reading).
  For ANY column \<open>z < Lng(N[n])\<close>, the row-1 entry of \<open>N[n]\<close> equals the row-1
  entry of \<open>N\<close> at the period base \<open>base z\<close> (\<open>= z\<close> on the prefix \<open>z < j\<^sub>0\<close>, and
  \<open>j\<^sub>0 + (z-j\<^sub>0) mod w\<close> on the blocks).  Immediate from
  @{thm [source] operCA_tiling_entry1_base} together with the length identity
  @{thm [source] operB_gen_LngM}.  Empirically 0-fail (the entry leg of the
  reflection, /tmp/row1_reflect2.py: 1920/1920).\<close>

lemma operCA_tiling_entry1_base':
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and zlt: "z < Lng ((N::pairseq)[n])"
  shows "entry ((N::pairseq)[n]) 1 z
       = entry N 1 (if z < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then z
            else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (z - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  have zlt': "z < ?j0 + n * ?w"
    using zlt operB_gen_LngM[OF L notzero hp j0lt] by simp
  show ?thesis by (rule operCA_tiling_entry1_base[OF L notzero hp j0lt zlt'])
qed


text \<open>§6.7 oper-tiling ROW-1 reflection — GLUE reducing the within-block row-1
  \<open>+1\<close> obligation to the single PARENT-CHARACTERIZATION fact.  Given (i) the base
  column \<open>x' = base x\<close> has a row-1 parent in \<open>N\<close> (\<open>hpN\<close>), and (ii) the period base
  of the \<open>N[n]\<close>-parent of \<open>x\<close> coincides with the \<open>N\<close>-parent of \<open>x'\<close> in the sense
  that their row-1 \<open>N\<close>-entries agree (\<open>pbase\<close>: \<open>entry N 1 (base (parent (N[n]) 1 x))
  = entry N 1 (parent N 1 x')\<close>), the two @{thm [source]
  operCA_tiling_within1_via_reflect} inputs (\<open>ex\<close>, \<open>ep\<close>) follow from the periodic
  row-1 reading @{thm [source] operCA_tiling_entry1_base'}, and \<open>via_reflect\<close>
  closes the within-block obligation.  This isolates the SINGLE remaining brick to
  \<open>pbase\<close> + \<open>hpN\<close> — the row-1 parent reflection (empirically 0-fail, 1920/1920:
  /tmp/row1_reflect2.py for \<open>ep\<close>/\<open>hpN\<close>, /tmp/valley_check.py for the lifted parent
  \<open>p = j\<^sub>0 + xblk\<cdot>w + (parent N 1 x' - j\<^sub>0)\<close>).\<close>

lemma operCA_tiling_within1_via_pbase:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x"
    and xlt: "x < Lng ((N::pairseq)[n])"
    and plt: "parent ((N::pairseq)[n]) 1 x < Lng ((N::pairseq)[n])"
    and hpN: "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (x - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
    and pbase: "entry N 1 (if parent ((N::pairseq)[n]) 1 x
                              < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                            then parent ((N::pairseq)[n]) 1 x
                            else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (parent ((N::pairseq)[n]) 1 x
                                 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
               = entry N 1 (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + (x - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))))"
  shows "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
       = entry ((N::pairseq)[n]) 1 x"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?x' = "?j0 + (x - ?j0) mod ?w"
  let ?p = "parent ((N::pairseq)[n]) 1 x"
  \<comment> \<open>\<open>ex\<close>: row-1 entry at \<open>x\<close> reads the base \<open>x'\<close> (since \<open>x \<ge> j\<^sub>0\<close>)\<close>
  have nge: "\<not> x < ?j0" using ge by simp
  have ex: "entry ((N::pairseq)[n]) 1 x = entry N 1 ?x'"
    using operCA_tiling_entry1_base'[OF L notzero hp j0lt xlt] nge by simp
  \<comment> \<open>row-1 entry at the \<open>N[n]\<close>-parent reads its own base, which by \<open>pbase\<close>
     coincides with \<open>entry N 1 (parent N 1 x')\<close>\<close>
  have epbase: "entry ((N::pairseq)[n]) 1 ?p
                  = entry N 1 (if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w)"
    by (rule operCA_tiling_entry1_base'[OF L notzero hp j0lt plt])
  have ep: "entry ((N::pairseq)[n]) 1 ?p = entry N 1 (parent N 1 ?x')"
    using epbase pbase by simp
  show ?thesis
    by (rule operCA_tiling_within1_via_reflect[OF condA hpN ex ep])
qed

end

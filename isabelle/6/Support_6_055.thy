theory Support_6_055
  imports Frontier_6_075
begin

text \<open>§6.7 oper-tiling brick (Front A, ROW 0): the \<open>i\<^sub>1\<close>-AGNOSTIC block-floor MIN.
  Every column \<open>y\<close> of \<open>N[n]\<close> at or beyond the first block start \<open>j\<^sub>0\<close> reads a
  row-0 value at least the slice minimum \<open>e\<^sub>0(N,j\<^sub>0)\<close>.  Writing \<open>y = j\<^sub>0+k\<cdot>w+t\<close>
  (\<open>k<n\<close>, \<open>t<w\<close>), the block reading @{thm [source] oper_gen_block_entry0} gives
  \<open>e\<^sub>0(N[n],y) = e\<^sub>0(N,j\<^sub>0+t) + k\<cdot>d\<^sub>0 \<ge> e\<^sub>0(N,j\<^sub>0)\<close>, since the per-block shift
  \<open>k\<cdot>d\<^sub>0 \<ge> 0\<close> and the strict period floor @{thm [source] oper_gen_strict_period_floor}
  gives \<open>e\<^sub>0(N,j\<^sub>0) \<le> e\<^sub>0(N,j\<^sub>0+t)\<close>.  Empirically 0-fail
  (/tmp/frontA_blockmin.py: 20538/0).\<close>

lemma oper_gen_blockfloor_min:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and yge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and ylt: "y < Lng ((N::pairseq)[n])"
  shows "entry N 0 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)) \<le> entry ((N::pairseq)[n]) 0 y"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?d0 = "if 0 < ?i1 then entry N 0 ?j1 - entry N 0 ?j0 else 0"
  let ?Nn = "(N::pairseq)[n]"
  have w0: "0 < ?w" using j0lt by linarith
  have lenNn: "Lng ?Nn = ?j0 + n * ?w" using operB_gen_LngM[OF L notzero hp j0lt] by simp
  let ?k = "(y - ?j0) div ?w"  let ?t = "(y - ?j0) mod ?w"
  have tw: "?t < ?w" using w0 by simp
  have ymj: "y - ?j0 < n * ?w" using ylt lenNn yge by linarith
  have kn: "?k < n" using less_mult_imp_div_less[OF ymj] .
  have dm: "?k * ?w + ?t = y - ?j0"
    using div_mult_mod_eq[of "y - ?j0" ?w] by (simp add: mult.commute)
  have ysplit: "y = ?j0 + ?k * ?w + ?t" using dm yge by linarith
  have eread: "entry ?Nn 0 y = entry N 0 (?j0 + ?t) + ?k * ?d0"
    using oper_gen_block_entry0[OF L notzero hp j0lt kn tw] ysplit by simp
  have floor: "entry N 0 ?j0 \<le> entry N 0 (?j0 + ?t)"
  proof (cases "0 < ?t")
    case True
    have sle: "?t \<le> Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)" using tw by simp
    show ?thesis using oper_gen_strict_period_floor[OF hp j0lt True sle] by simp
  next
    case False
    thus ?thesis by simp
  qed
  have "entry N 0 ?j0 \<le> entry N 0 (?j0 + ?t) + ?k * ?d0" using floor by simp
  thus ?thesis using eread by simp
qed

end

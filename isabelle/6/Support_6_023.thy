theory Support_6_023
  imports Frontier_6_040
begin

text \<open>§6.8 d1pos \<open>\<not>brle\<close> CELL-4 (PERIODIC-TAIL) anchor coincidence — INTERIOR
  sub-case (\<open>c < m\<close>, deep-verified 729/1254).  The slice starts in \<open>M\<close>'s PERIODIC
  TAIL; the \<open>M\<close>-side branch \<open>S = Br M'\<close> source lies ENTIRELY inside block \<open>q\<^sub>0\<close>, so it
  is a CLEAN per-block shift of its block-0 image \<open>Snside = Br N\<^sub>r\<close> source:
  \<open>S = (IncrFirst^^shamt) Snside\<close> (\<open>shamt = q\<^sub>0\<cdot>\<delta>\<close>, deep-verified 729/729,
  python/cell4_periodic_check.py).  Then \<open>P\<close> commutes with the shift
  (@{thm [source] P_funpow_IncrFirst}), so the anchors coincide and the junction
  entries shift by \<open>shamt\<close> (row 0) / are unchanged (row 1).\<close>

lemma oper_d1pos_anchor_coincide_period_interior:
  fixes S :: pairseq and Snside :: pairseq and shamt :: nat
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
      and "cN \<equiv> IdxSum (P Snside) ! (length (P Snside) - 1)"
  assumes SnT: "Snside \<in> T_PS" and multiN: "1 < length (P Snside)"
    and fullShift: "S = (IncrFirst ^^ shamt) Snside"
  shows "c = cN"
    and "entry S 0 c = entry Snside 0 cN + shamt"
    and "entry S 1 c \<le> entry Snside 1 cN"
proof -
  have PS: "P S = map (IncrFirst ^^ shamt) (P Snside)"
    using fullShift by (simp add: P_funpow_IncrFirst)
  have lenEq: "length (P S) = length (P Snside)" using PS by simp
  \<comment> \<open>anchor offset \<open>c = sum_list (map length (butlast (P S)))\<close>; the shift preserves
     all component lengths, so \<open>c = cN\<close>\<close>
  have ceqlen: "c = sum_list (map length (butlast (P S)))"
    unfolding c_def by (simp add: idxsum_nth butlast_conv_take)
  have cNeqlen: "cN = sum_list (map length (butlast (P Snside)))"
    unfolding cN_def by (simp add: idxsum_nth butlast_conv_take)
  have butEq: "butlast (P S) = map (IncrFirst ^^ shamt) (butlast (P Snside))"
    using PS by (simp add: map_butlast)
  show ceqcN: "c = cN"
    using ceqlen cNeqlen butEq by (simp add: o_def Lng_funpow_IncrFirst)
  \<comment> \<open>\<open>c < Lng Snside\<close> (anchor is a valid index of \<open>Snside\<close>)\<close>
  have cNlt: "cN < Lng Snside"
  proof -
    have cle: "cN \<le> Lng Snside - 1" unfolding cN_def
      by (rule oper_d1pos_branch_anchor(2)[OF SnT multiN])
    have Lpos: "0 < Lng Snside"
    proof -
      have "Snside \<noteq> []" using multiN by (cases "Snside = []")
          (auto simp: P.simps multiT_def zeroT_def monoT_def)
      thus ?thesis by (cases Snside) auto
    qed
    show ?thesis using cle Lpos by linarith
  qed
  have cltS: "c < Lng S" using ceqcN cNlt fullShift by simp
  show "entry S 0 c = entry Snside 0 cN + shamt"
  proof -
    have "entry S 0 c = entry ((IncrFirst ^^ shamt) Snside) 0 c" using fullShift by simp
    also have "\<dots> = entry Snside 0 c + shamt" by (rule entry_funpow_IncrFirst0[OF cNlt[unfolded ceqcN[symmetric]]])
    finally show ?thesis using ceqcN by simp
  qed
  show "entry S 1 c \<le> entry Snside 1 cN"
  proof -
    have "entry S 1 c = entry ((IncrFirst ^^ shamt) Snside) 1 c" using fullShift by simp
    also have "\<dots> = entry Snside 1 c" by (rule entry_funpow_IncrFirst1[OF cNlt[unfolded ceqcN[symmetric]]])
    finally show ?thesis using ceqcN by simp
  qed
qed

text \<open>§6.8 d1pos \<open>\<not>brle\<close> CELL-4 (PERIODIC-TAIL) anchor coincidence — BOUNDARY
  sub-case (\<open>c = m\<close>, deep-verified 525/1254).  The \<open>M\<close>-side branch \<open>S\<close> CROSSES the
  period boundary, so its last \<open>P\<close>-component is a singleton at the boundary index
  \<open>m = Lng Snside - 1\<close> (\<open>A + m = j\<^sub>m\<^sub>2 + (q\<^sub>0+1)\<cdot>w\<close>).  We pin \<open>c = cN = m\<close> via
  @{thm [source] anchor_ge_of_leftmin} (the \<open>mLmin\<close> facts: \<open>m\<close> is a row-0 left-min of
  both \<open>S\<close> — up to \<open>shamt\<close> — and \<open>Snside\<close>) together with the upper bound \<open>cle\<close>
  (\<open>cle : c \<le> m\<close>, supplied by the assembly's anchor-bound geometry), and read the
  junction entries from \<open>boundEq0\<close>/\<open>boundEq1\<close> (the period-boundary block decode,
  deep-verified rank 11, python/cell4_periodic_check.py: F8/F9 1254/1254).\<close>

lemma oper_d1pos_anchor_coincide_period_boundary:
  fixes S :: pairseq and Snside :: pairseq and shamt :: nat
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
      and "cN \<equiv> IdxSum (P Snside) ! (length (P Snside) - 1)"
  assumes ST: "S \<in> T_PS" and multi: "1 < length (P S)"
    and SnT: "Snside \<in> T_PS" and multiN: "1 < length (P Snside)"
    and mleS: "Lng Snside - 1 \<le> Lng S - 1"
    and cle: "c = Lng Snside - 1"
    and mLmin_Sn: "\<forall>j < Lng Snside - 1. entry Snside 0 (Lng Snside - 1) \<le> entry Snside 0 j"
    and boundEq0: "entry S 0 (Lng Snside - 1) = entry Snside 0 (Lng Snside - 1) + shamt"
    and boundEq1: "entry S 1 (Lng Snside - 1) \<le> entry Snside 1 (Lng Snside - 1)"
  shows "c = cN"
    and "entry S 0 c = entry Snside 0 cN + shamt"
    and "entry S 1 c \<le> entry Snside 1 cN"
proof -
  let ?m = "Lng Snside - 1"
  have cNle: "cN \<le> ?m" unfolding cN_def
    by (rule oper_d1pos_branch_anchor(2)[OF SnT multiN])
  have mleSn1: "?m \<le> Lng Snside - 1" by simp
  have cNge: "Lng Snside - 1 \<le> cN" unfolding cN_def
    by (rule anchor_ge_of_leftmin[OF SnT mleSn1]) (use mLmin_Sn in simp)
  have cNeqm: "cN = ?m" using cNge cNle by linarith
  show ceqcN: "c = cN" using cle cNeqm by simp
  show "entry S 0 c = entry Snside 0 cN + shamt" using boundEq0 cle cNeqm by simp
  show "entry S 1 c \<le> entry Snside 1 cN" using boundEq1 cle cNeqm by simp
qed

end

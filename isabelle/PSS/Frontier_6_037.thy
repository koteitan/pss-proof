theory Frontier_6_037
  imports Support_6_019
begin

text \<open>§6.8 d1pos ¬brle — the ACROSS-BLOCK \<open>P\<close>-COLLAPSE (the core missing brick).
  Unlike the d0zero fold (where \<open>P\<close> SPLITS into replicate-blocks because the
  block boundaries ARE row-0 left-minima — see @{thm [source] oper_d0zero_seg_P_split}
  / @{thm [source] oper_d0zero_seg_P_hfold} / @{thm [source] oper_d0zero_seg_P_blk1fold}),
  the d1pos case has \<open>\<delta> > 0\<close>, so every block is row-0 SHIFTED by \<open>\<delta>\<close> and the
  boundaries are NOT row-0 left-minima.  Consequently \<open>P\<close> COLLAPSES all the
  across-block growth into a SINGLE non-multi last component: only ONE genuine
  row-0 left-minimum survives inside the branch region (the last \<open>FirstNodes\<close>
  anchor \<open>c\<close>), and the entire tail \<open>seg S c (Lng S - 1)\<close> from there to the slice
  end is one \<open>monoT\<close> (single) \<open>P\<close>-component.

  This lemma packages the collapse as a pure structural identity for a branch
  region \<open>S\<close> presented as the ambient slice \<open>seg M A E\<close> (= \<open>Br M'\<close> after
  the \<open>Br_seg_reshape\<close> reshape, below): with the last-anchor cut \<open>c\<close> a row-0
  left-minimum (\<open>lmin\<close>) whose tail is single (\<open>tailnm\<close>), the LOW prefix being a
  \<open>(IncrFirst^^shamt)\<close>-shift of an \<open>N\<close>-side branch \<open>base\<close> (\<open>lowshift\<close>, the in-block
  shift from @{thm [source] oper_d1pos_LOW_source_eq}/@{thm [source] oper_d1pos_notbrle_LOW_eq}),
  and \<open>base\<close> being the \<open>butlast\<close> source of the \<open>N\<close>-side decomposition \<open>BN\<close>
  (\<open>butl\<close>), one obtains
    \<open>P S = map (IncrFirst^^shamt) (butlast BN) @ [seg S c (Lng S - 1)]\<close>.
  The proof is: additive split at \<open>c\<close> (@{thm [source] oper_d1pos_notbrle_P_split},
  the tail being a single non-multi component), then the LOW prefix
  \<open>P (seg S 0 (c-1)) = P ((IncrFirst^^shamt) base) = map (IncrFirst^^shamt) (P base)
   = map (IncrFirst^^shamt) (butlast BN)\<close> via @{thm [source] P_funpow_IncrFirst}.

  DEEP-VERIFIED at rank 8 (KMAX=8, len=12, val=4; python/d1pos_collapse_struct.py
  and python/d1pos_collapse_target.py): the full collapse and EVERY hypothesis
  (c0/cle/lmin/tailnm/lowshift/butl) hold 1395/1395, 0 failures; 780/1395 of the
  branch regions span \<open>>1\<close> block and ALL collapse to a single tail.\<close>

lemma oper_d1pos_collapse:
  fixes S :: pairseq and base :: pairseq and BN :: "pairseq list"
  assumes ST: "S \<in> T_PS"
    and c0: "0 < c" and cle: "c \<le> Lng S - 1"
    and lmin: "\<And>j. j < c \<Longrightarrow> entry S 0 c \<le> entry S 0 j"
    and tailnm: "\<not> multiT (seg S c (Lng S - 1))"
    and lowshift: "seg S 0 (c - 1) = (IncrFirst ^^ shamt) base"
    and butl: "butlast BN = P base"
  shows "P S = map (IncrFirst ^^ shamt) (butlast BN) @ [seg S c (Lng S - 1)]"
proof -
  \<comment> \<open>additive split at the row-0 left-min cut \<open>c\<close>: tail is a single non-multi component\<close>
  have split: "P S = P (seg S 0 (c - 1)) @ [seg S c (Lng S - 1)]"
    by (rule oper_d1pos_notbrle_P_split[OF ST c0 cle lmin tailnm])
  \<comment> \<open>the LOW prefix is the per-component \<open>(IncrFirst^^shamt)\<close>-shift of \<open>P base\<close>\<close>
  have low: "P (seg S 0 (c - 1)) = map (IncrFirst ^^ shamt) (P base)"
  proof -
    have "P (seg S 0 (c - 1)) = P ((IncrFirst ^^ shamt) base)" using lowshift by simp
    also have "\<dots> = map (IncrFirst ^^ shamt) (P base)" by (rule P_funpow_IncrFirst)
    finally show ?thesis .
  qed
  \<comment> \<open>\<open>P base = butlast BN\<close> identifies the shifted prefix with \<open>map shift (butlast BN)\<close>\<close>
  have lowB: "P (seg S 0 (c - 1)) = map (IncrFirst ^^ shamt) (butlast BN)"
    using low butl by simp
  show ?thesis using split lowB by simp
qed

text \<open>§6.8 d1pos ¬brle — the ANCHOR brick (conc-A).  For ANY \<open>S \<in> T_PS\<close> whose
  \<open>P\<close>-decomposition has \<open>>1\<close> component, the LAST \<open>FirstNodes\<close> anchor
    \<open>c = IdxSum (P S) ! (length (P S) - 1) = Lng S - Lng (last (P S))\<close>
  is a genuine cut satisfying ALL three structural hypotheses of
  @{thm [source] oper_d1pos_collapse}: \<open>0 < c\<close> (\<open>cpos\<close>), \<open>c \<le> Lng S - 1\<close> (\<open>cle\<close>),
  the row-0 left-minimum (\<open>lmin\<close>, from @{thm [source] idxsum_leftend_lmin} at the
  last component), and the single (non-multi) tail (\<open>tailnm\<close>, since the last
  \<open>P\<close>-component is \<open>zeroT \<or> monoT\<close> by @{thm [source] m_6_2_P_components_1}, hence
  \<open>\<not> multiT\<close>).  Moreover the tail slice is exactly the last component
    \<open>seg S c (Lng S - 1) = last (P S)\<close>  (\<open>tailseg\<close>).
  This is PURELY STRUCTURAL (no \<open>d1pos\<close> block-fold needed): the cut is the
  S-local left endpoint of the last \<open>P\<close>-component, identified via
  @{thm [source] m_6_4_P_IdxSum} / @{thm [source] idxsum_diff} /
  @{thm [source] idxsum_concat_P}.
  DEEP-VERIFIED rank 8 (KMAX=8 len 12 val 4, /tmp/conc_a_verify.py): cpos 1395/1395,
  cle 1395/1395, lmin 1395/1395, tailnm 1395/1395, tailseg 1395/1395, 0 failures.\<close>

lemma oper_d1pos_branch_anchor:
  fixes S :: pairseq
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
  assumes ST: "S \<in> T_PS" and multi: "1 < length (P S)"
  shows "0 < c"
    and "c \<le> Lng S - 1"
    and "\<And>j. j < c \<Longrightarrow> entry S 0 c \<le> entry S 0 j"
    and "\<not> multiT (seg S c (Lng S - 1))"
    and "seg S c (Lng S - 1) = last (P S)"
    and "c = Lng S - Lng (last (P S))"
proof -
  let ?Q = "P S"
  let ?J = "length ?Q - 1"
  have ne: "?Q \<noteq> []" by (rule P_nonempty)
  have JL: "?J < length ?Q" using ne by (cases ?Q) auto
  have Jle: "?J \<le> Lng ?Q - 1" by simp
  \<comment> \<open>the last component is the slice between consecutive \<open>IdxSum\<close> values\<close>
  have comp: "?Q ! ?J = seg S (IdxSum ?Q ! ?J) (IdxSum ?Q ! (?J + 1) - 1)"
    by (rule m_6_4_P_IdxSum[OF ST Jle])
  have cdef: "c = IdxSum ?Q ! ?J" using c_def by simp
  \<comment> \<open>the right endpoint of the last component is \<open>Lng S - 1\<close>\<close>
  have idxlast: "IdxSum ?Q ! (?J + 1) = Lng S"
  proof -
    have "?J + 1 = length ?Q" using ne by (cases ?Q) auto
    hence "IdxSum ?Q ! (?J + 1) = sum_list (map length (take (length ?Q) ?Q))"
      by (simp add: idxsum_nth)
    also have "\<dots> = sum_list (map length ?Q)" by simp
    also have "\<dots> = length (concat ?Q)" by (simp add: length_concat)
    also have "concat ?Q = S" by (rule idxsum_concat_P)
    finally show ?thesis by simp
  qed
  \<comment> \<open>last component is the last list element\<close>
  have lastnth: "?Q ! ?J = last ?Q" using ne by (simp add: last_conv_nth)
  \<comment> \<open>tailseg\<close>
  have tailseg: "seg S c (Lng S - 1) = last ?Q"
    using comp cdef idxlast lastnth by simp
  thus "seg S c (Lng S - 1) = last (P S)" .
  \<comment> \<open>length of the last component is positive\<close>
  have lenpos: "0 < length (?Q ! ?J)"
    using idxsum_P_component_nonempty[OF ST JL] by simp
  \<comment> \<open>\<open>IdxSum ?J + length(last) = Lng S\<close>, hence \<open>c = Lng S - Lng(last)\<close>\<close>
  have diff: "IdxSum ?Q ! (?J + 1) = IdxSum ?Q ! ?J + length (?Q ! ?J)"
    by (rule idxsum_diff[OF JL])
  have cval: "c = Lng S - Lng (last ?Q)"
    using diff idxlast cdef lastnth by simp
  thus "c = Lng S - Lng (last (P S))" .
  \<comment> \<open>cpos: the first component is non-empty, so the last endpoint \<open>c > 0\<close> when \<open>>1\<close> comp\<close>
  have cpos: "0 < c"
  proof -
    have "IdxSum ?Q ! 1 \<le> IdxSum ?Q ! ?J"
    proof -
      have a1: "IdxSum ?Q ! 1 = sum_list (map length (take 1 ?Q))"
        using JL multi by (simp add: idxsum_nth)
      have aJ: "IdxSum ?Q ! ?J = sum_list (map length (take ?J ?Q))"
        using JL by (simp add: idxsum_nth less_imp_le_nat)
      have "(1::nat) \<le> ?J" using multi by simp
      thus ?thesis using a1 aJ by (simp add: idxsum_sum_take_mono)
    qed
    moreover have "0 < IdxSum ?Q ! 1"
    proof -
      have z0: "0 < length ?Q" using multi by linarith
      have d0: "IdxSum ?Q ! (0 + 1) = IdxSum ?Q ! 0 + length (?Q ! 0)"
        by (rule idxsum_diff[OF z0])
      have i0: "IdxSum ?Q ! 0 = 0" by (simp add: idxsum_nth)
      have "0 < length (?Q ! 0)"
        using idxsum_P_component_nonempty[OF ST] z0 by simp
      thus ?thesis using d0 i0 by simp
    qed
    ultimately show ?thesis using cdef by simp
  qed
  thus "0 < c" .
  \<comment> \<open>cle and lmin from \<open>idxsum_leftend_lmin\<close> at the last component\<close>
  have lmlast: "IdxSum ?Q ! ?J \<le> Lng S - 1
       \<and> (\<forall>j < IdxSum ?Q ! ?J. entry S 0 (IdxSum ?Q ! ?J) \<le> entry S 0 j)"
    using idxsum_leftend_lmin[OF ST JL] by (simp add: linorder_class.not_le)
  show "c \<le> Lng S - 1" using lmlast cdef by simp
  show "\<And>j. j < c \<Longrightarrow> entry S 0 c \<le> entry S 0 j" using lmlast cdef by simp
  \<comment> \<open>tailnm: the last component is \<open>zeroT \<or> monoT\<close>, hence \<open>\<not> multiT\<close>\<close>
  have lastin: "last ?Q \<in> set ?Q" using ne by simp
  have "zeroT (last ?Q) \<or> monoT (last ?Q)"
    using m_6_2_P_components_1[OF ST] lastin by blast
  hence "\<not> multiT (last ?Q)" by (auto simp: multiT_def)
  thus "\<not> multiT (seg S c (Lng S - 1))" using tailseg by simp
qed

text \<open>§6.8 d1pos ¬brle — ASSEMBLED concrete collapse (conc-A).  Combines the
  ANCHOR brick @{thm [source] oper_d1pos_branch_anchor} (which discharges the
  three STRUCTURAL hypotheses \<open>c0/cle/lmin/tailnm\<close> of
  @{thm [source] oper_d1pos_collapse} at the concrete cut
  \<open>c = IdxSum (P S) ! (length (P S) - 1)\<close>) with the two SHIFT hypotheses
  (\<open>lowshift\<close>: the LOW prefix is an \<open>(IncrFirst^^shamt)\<close>-shift of \<open>base\<close>; \<open>butl\<close>:
  \<open>butlast BN = P base\<close>) to yield the FULL concrete collapse
    \<open>P S = map (IncrFirst^^shamt) (butlast BN) @ [last (P S)]\<close>.
  The two remaining hypotheses are exactly the §6.8 BLOCKER (the \<open>d1pos\<close>
  block-fold + first-node geometry): \<open>butl\<close> is itself a second ANCHOR application
  on the \<open>N\<close>-side reshape (\<open>butlast (Br N\<^sub>p) = P (seg Snside 0 (cN-1))\<close>, deep-verified
  1395/1395), and \<open>lowshift\<close> reduces, in the UNCAPPED regime B (\<open>A \<ge> jm2\<close>,
  single block), to @{thm [source] oper_d1pos_LOW_source_eq} with the block index
  \<open>q = (A - jm2) div w\<close> (deep-verified 1128/1128, where \<open>A = j0' + TrMax M' + 1\<close>;
  the 267 \<open>A < jm2\<close> cases are the regime-A/capped residual).
  DEEP-VERIFIED rank 8 (/tmp/conc_a_verify.py): with this concrete \<open>c\<close>/\<open>base\<close> the
  full collapse holds 1395/1395, 0 failures.\<close>

lemma oper_d1pos_branch_collapse_concrete:
  fixes S :: pairseq and base :: pairseq and BN :: "pairseq list"
  assumes ST: "S \<in> T_PS" and multi: "1 < length (P S)"
    and lowshift: "seg S 0 (IdxSum (P S) ! (length (P S) - 1) - 1) = (IncrFirst ^^ shamt) base"
    and butl: "butlast BN = P base"
  shows "P S = map (IncrFirst ^^ shamt) (butlast BN) @ [last (P S)]"
proof -
  let ?c = "IdxSum (P S) ! (length (P S) - 1)"
  \<comment> \<open>structural hypotheses from the ANCHOR brick\<close>
  have c0: "0 < ?c" by (rule oper_d1pos_branch_anchor(1)[OF ST multi])
  have cle: "?c \<le> Lng S - 1" by (rule oper_d1pos_branch_anchor(2)[OF ST multi])
  have lmin: "\<And>j. j < ?c \<Longrightarrow> entry S 0 ?c \<le> entry S 0 j"
    using oper_d1pos_branch_anchor(3)[OF ST multi] by blast
  have tailnm: "\<not> multiT (seg S ?c (Lng S - 1))"
    by (rule oper_d1pos_branch_anchor(4)[OF ST multi])
  have tailseg: "seg S ?c (Lng S - 1) = last (P S)"
    by (rule oper_d1pos_branch_anchor(5)[OF ST multi])
  \<comment> \<open>assemble via the structural collapse, then rewrite the tail to \<open>last (P S)\<close>\<close>
  have "P S = map (IncrFirst ^^ shamt) (butlast BN) @ [seg S ?c (Lng S - 1)]"
    by (rule oper_d1pos_collapse[OF ST c0 cle lmin tailnm lowshift butl])
  thus ?thesis using tailseg by simp
qed

text \<open>§6.8 d1pos ¬brle — the \<open>butl\<close> hypothesis of
  @{thm [source] oper_d1pos_branch_collapse_concrete} is itself an ANCHOR
  application on the \<open>N\<close>-side reshape (conc-A).  For the \<open>N\<close>-side branch region
  \<open>Snside \<in> T_PS\<close> with \<open>>1\<close> \<open>P\<close>-component, \<open>butlast (P Snside)\<close> is exactly
  \<open>P (seg Snside 0 (cN - 1))\<close> where \<open>cN = IdxSum (P Snside) ! (length (P Snside) - 1)\<close>
  is the last \<open>FirstNodes\<close> anchor of \<open>Snside\<close>.  Since \<open>Br N\<^sub>p = P Snside\<close> (via
  the \<open>Br_seg_reshape\<close> reshape, below), this gives \<open>base = seg Snside 0 (cN - 1)\<close>
  satisfying \<open>butlast BN = P base\<close>.  DEEP-VERIFIED rank 8: 1395/1395.\<close>

lemma oper_d1pos_branch_butl:
  fixes Snside :: pairseq
  defines "cN \<equiv> IdxSum (P Snside) ! (length (P Snside) - 1)"
  assumes ST: "Snside \<in> T_PS" and multi: "1 < length (P Snside)"
  shows "butlast (P Snside) = P (seg Snside 0 (cN - 1))"
proof -
  have c0: "0 < cN" unfolding cN_def by (rule oper_d1pos_branch_anchor(1)[OF ST multi])
  have cle: "cN \<le> Lng Snside - 1" unfolding cN_def
    by (rule oper_d1pos_branch_anchor(2)[OF ST multi])
  have lmin: "\<And>j. j < cN \<Longrightarrow> entry Snside 0 cN \<le> entry Snside 0 j"
    unfolding cN_def using oper_d1pos_branch_anchor(3)[OF ST multi] by blast
  have tailnm: "\<not> multiT (seg Snside cN (Lng Snside - 1))"
    unfolding cN_def by (rule oper_d1pos_branch_anchor(4)[OF ST multi])
  \<comment> \<open>the additive split at \<open>cN\<close>: tail is a single non-multi component\<close>
  have split: "P Snside = P (seg Snside 0 (cN - 1)) @ [seg Snside cN (Lng Snside - 1)]"
    by (rule oper_d1pos_notbrle_P_split[OF ST c0 cle lmin tailnm])
  thus ?thesis by simp
qed

end

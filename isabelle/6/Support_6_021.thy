theory Support_6_021
  imports Frontier_6_038
begin

text \<open>§6.8 d1pos \<open>\<not>brle\<close> REGIME B anchor coincidence — the SHIFT analogue of
  @{thm [source] oper_d1pos_anchor_coincide_regA} (regime B, \<open>j\<^sub>m\<^sub>2 \<le> j'\<^sub>0\<close>).  In
  regime A the all-but-last agreement of \<open>S\<close> (= \<open>Br M'\<close> source) and \<open>Snside\<close>
  (= \<open>Br N\<^sub>p\<close> source) is VERBATIM (\<open>seg S 0 (m-1) = seg Snside 0 (m-1)\<close>); in regime B
  it is a single-block \<open>(IncrFirst^^shamt)\<close>-SHIFT (\<open>shamt = q\<^sub>0\<cdot>\<delta>\<close>), supplied here as
  the hypothesis \<open>shiftEq\<close> — exactly the form delivered by
  @{thm [source] oper_d1pos_branch_lowshift_regB} / @{thm [source] oper_d1pos_LOW_source_eq}
  (DEEP-VERIFIED 1128/1128 at rank 8).  From it we derive, at the anchor cut
  \<open>c = IdxSum (P S) ! (len-1)\<close> / \<open>cN = IdxSum (P Snside) ! (len-1)\<close>:
    \<open>c = cN\<close>  (the anchor offsets coincide: \<open>(IncrFirst^^shamt)\<close> PRESERVES
               component lengths via @{thm [source] Lng_funpow_IncrFirst}, so
               \<open>sum_list (map length (butlast (P S))) = sum_list (map length (butlast (P Snside)))\<close>),
    \<open>F8end : entry S 0 c = entry Snside 0 cN + shamt\<close>  (row-0 \<open>+shamt\<close>,
               @{thm [source] entry_funpow_IncrFirst0}),
    \<open>F9end : entry S 1 c \<le> entry Snside 1 cN\<close>  (row-1 UNSHIFTED — in fact \<open>=\<close>,
               @{thm [source] entry_funpow_IncrFirst1}).
  The P-prefix anchor stability used is the regime-AGNOSTIC
  @{thm [source] P_butlast_take_at_anchor} (applied to BOTH operands), lifted across
  the shift by @{thm [source] P_funpow_IncrFirst} (\<open>P\<close> commutes with the per-component
  shift).  PURELY STRUCTURAL given the shift agreement — no block-fold inside this
  lemma (the single-block realisation \<open>Aform\<close>/\<open>e0lt\<close> behind \<open>shiftEq\<close> is the
  documented residual block-fold geometry, delivered by the lowshift bricks).\<close>

lemma oper_d1pos_anchor_coincide_regB:
  fixes S :: pairseq and Snside :: pairseq and shamt :: nat
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
      and "cN \<equiv> IdxSum (P Snside) ! (length (P Snside) - 1)"
  assumes ST: "S \<in> T_PS" and multi: "1 < length (P S)"
    and SnT: "Snside \<in> T_PS" and multiN: "1 < length (P Snside)"
    and clt: "c < Lng Snside - 1"
    and cNlt: "cN < Lng Snside - 1"
    and LngEq: "Lng S = Lng Snside"
    and shiftEq: "seg S 0 (Lng Snside - 1 - 1)
                = (IncrFirst ^^ shamt) (seg Snside 0 (Lng Snside - 1 - 1))"
  shows "c = cN"
    and "entry S 0 c = entry Snside 0 cN + shamt"
    and "entry S 1 c \<le> entry Snside 1 cN"
proof -
  let ?m = "Lng Snside - 1"
  obtain e where edef: "e = ?m - 1" by blast
  have mpos: "0 < ?m" using cNlt by linarith
  \<comment> \<open>the shift agreement on the all-but-last prefix\<close>
  have shiftEqe: "seg S 0 e = (IncrFirst ^^ shamt) (seg Snside 0 e)"
    using shiftEq edef by simp
  \<comment> \<open>P-prefix anchor stability on both operands (anchors strictly below \<open>m\<close>)\<close>
  have mleS: "?m \<le> Lng S" using LngEq by simp
  have mleSn: "?m \<le> Lng Snside" by linarith
  have cltS: "IdxSum (P S) ! (length (P S) - 1) < ?m" using clt unfolding c_def by simp
  have cltSn: "IdxSum (P Snside) ! (length (P Snside) - 1) < ?m" using cNlt unfolding cN_def by simp
  have butS: "butlast (P (seg S 0 e)) = butlast (P S)"
    using P_butlast_take_at_anchor[OF ST multi cltS mleS] edef by simp
  have butSn: "butlast (P (seg Snside 0 e)) = butlast (P Snside)"
    using P_butlast_take_at_anchor[OF SnT multiN cltSn mleSn] edef by simp
  \<comment> \<open>\<open>P\<close> commutes with the per-component shift on the prefix\<close>
  have PshiftEq: "P (seg S 0 e) = map (IncrFirst ^^ shamt) (P (seg Snside 0 e))"
    using shiftEqe by (simp add: P_funpow_IncrFirst)
  have butlastMap: "butlast (P (seg S 0 e))
                  = map (IncrFirst ^^ shamt) (butlast (P (seg Snside 0 e)))"
    using PshiftEq by (simp add: map_butlast)
  have butEq: "butlast (P S) = map (IncrFirst ^^ shamt) (butlast (P Snside))"
    using butS butSn butlastMap by simp
  \<comment> \<open>\<open>c = cN\<close>: the last \<open>IdxSum\<close> value is the total length of \<open>butlast (P \<cdot>)\<close>;
     the per-component shift preserves lengths, so the totals agree\<close>
  have cbutl: "c = sum_list (map length (butlast (P S)))"
  proof -
    have "c = IdxSum (P S) ! (length (P S) - 1)" unfolding c_def ..
    also have "\<dots> = sum_list (map length (take (length (P S) - 1) (P S)))"
      by (simp add: idxsum_nth)
    also have "take (length (P S) - 1) (P S) = butlast (P S)"
      by (simp add: butlast_conv_take)
    finally show ?thesis .
  qed
  have cNbutl: "cN = sum_list (map length (butlast (P Snside)))"
  proof -
    have "cN = IdxSum (P Snside) ! (length (P Snside) - 1)" unfolding cN_def ..
    also have "\<dots> = sum_list (map length (take (length (P Snside) - 1) (P Snside)))"
      by (simp add: idxsum_nth)
    also have "take (length (P Snside) - 1) (P Snside) = butlast (P Snside)"
      by (simp add: butlast_conv_take)
    finally show ?thesis .
  qed
  have lenPreserve: "map length (map (IncrFirst ^^ shamt) (butlast (P Snside)))
                   = map length (butlast (P Snside))"
  proof -
    have "map length (map (IncrFirst ^^ shamt) (butlast (P Snside)))
        = map (\<lambda>x. length ((IncrFirst ^^ shamt) x)) (butlast (P Snside))"
      by simp
    also have "\<dots> = map length (butlast (P Snside))"
      by (rule map_cong) (simp_all add: Lng_funpow_IncrFirst)
    finally show ?thesis .
  qed
  show ceq: "c = cN"
  proof -
    have "c = sum_list (map length (butlast (P S)))" by (rule cbutl)
    also have "\<dots> = sum_list (map length (map (IncrFirst ^^ shamt) (butlast (P Snside))))"
      using butEq by simp
    also have "\<dots> = sum_list (map length (butlast (P Snside)))"
      by (simp add: o_def)
    also have "\<dots> = cN" using cNbutl by simp
    finally show ?thesis .
  qed
  \<comment> \<open>entry agreement at the anchor cut \<open>c = cN\<close>, lifted across the shift\<close>
  have ccm: "c \<le> e" using clt edef by linarith
  have LngSnseg: "Lng (seg Snside 0 e) = Suc e" using edef mpos by simp
  have cltSeg: "c < Lng (seg Snside 0 e)" using ccm LngSnseg by simp
  \<comment> \<open>row 0: \<open>+shamt\<close>\<close>
  have eqQc0: "entry (seg S 0 e) 0 c = entry (seg Snside 0 e) 0 c + shamt"
    using shiftEqe entry_funpow_IncrFirst0[OF cltSeg] by simp
  \<comment> \<open>row 1: unshifted\<close>
  have eqQc1: "entry (seg S 0 e) 1 c = entry (seg Snside 0 e) 1 c"
    using shiftEqe entry_funpow_IncrFirst1[OF cltSeg] by simp
  \<comment> \<open>reduce the prefix-entries back to \<open>S\<close>/\<open>Snside\<close> entries (\<open>c\<close> in the prefix window)\<close>
  have cltLng: "c < Lng (seg S 0 e)"
  proof -
    have "Lng (seg S 0 e) = Suc e" using edef mpos mleS by simp
    thus ?thesis using ccm by simp
  qed
  have lhs0: "entry (seg S 0 e) 0 c = entry S 0 c"
    using entry_seg[OF cltLng] by simp
  have lhs1: "entry (seg S 0 e) 1 c = entry S 1 c"
    using entry_seg[OF cltLng] by simp
  have rhs0: "entry (seg Snside 0 e) 0 c = entry Snside 0 c"
    using entry_seg[OF cltSeg] by simp
  have rhs1: "entry (seg Snside 0 e) 1 c = entry Snside 1 c"
    using entry_seg[OF cltSeg] by simp
  have e0: "entry S 0 c = entry Snside 0 c + shamt" using eqQc0 lhs0 rhs0 by simp
  have e1: "entry S 1 c = entry Snside 1 c" using eqQc1 lhs1 rhs1 by simp
  show "entry S 0 c = entry Snside 0 cN + shamt" using e0 ceq by simp
  show "entry S 1 c \<le> entry Snside 1 cN" using e1 ceq by simp
qed

end

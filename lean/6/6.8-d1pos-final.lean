import «6».«6.8-d1pos-dispatch»
import «6».«6.8-d1pos-notbrle»
import «6».«6.8-d1pos-anchor-regB»
import «6».«6.8-d1pos-period»
import «6».«6.8-d1pos-cell-regA»
import «6».«6.8-d1pos-cell-regB»
import «6».«6.8-d1pos-cell-boundary»
import «6».«6.8-d1pos-cell-periodic»

/-!
# §6.8 命題（標準形の切片と `Br` の降順性の関係）— 無条件版（campaign 最終配線）

- 原文: `tmp/content.md` L1422 付近; `isabelle/pss_paper.thy` の
  `p_6_8_standard_slice_Br_descending`
- 訂正 A7（帰納対象は「`Br(M′)` が降順」）・A8（タイル長の off-by-one）適用後の主張。
  主張の陳述自体は `6.8-standard-slice-Br-descending.lean` の条件付き版
  `standard_slice_Br_descending_of_d1pos` と同一で、本ファイルはその仮定
  `RankSuccD1posLeg` を実体化して外すだけ。
- Isabelle: `m_6_8_standard_slice_Br_descending` (pss_mechanized.thy:24002)。
- 依存: d1pos campaign の全ファイル（dispatch の 22 named Props を、
  wave A-1〜A-3 の brick ファイル群が `D1pos_*_holds` として全数討伐済み）。
- 状態: ✅ 証明済（sorry 0、公開定理 2 本）。
-/

namespace PSS

/-- §6.8 rank 帰納の d1pos leg。dispatch の 22 brick Props が全て定理化されたので、
`rankSuccD1posLeg_of_bricks` に実引数を与えて無条件化する。 -/
theorem rankSuccD1posLeg_proved : RankSuccD1posLeg :=
  rankSuccD1posLeg_of_bricks
    D1pos_oper_d1pos_notbrle_LOW_take_eq_regA_holds
    D1pos_oper_d1pos_notbrle_LOW_take_eq_regB_holds
    D1pos_oper_d1pos_notbrle_LOW_take_eq_boundary_holds
    D1pos_oper_d1pos_notbrle_LOW_take_eq_periodic_holds
    D1pos_oper_d1pos_ctx_tnc_capped_holds
    D1pos_oper_d1pos_ctx_period_tncstrict_uncapped_holds
    D1pos_oper_d1pos_ctx_stop_direct_holds
    D1pos_oper_d1pos_ctx_stop_direct_strict_holds
    D1pos_oper_d1pos_ctx_period_le0Np_holds
    D1pos_oper_d1pos_ctx_notbrleNp_holds
    D1pos_oper_d1pos_ctx_notbrleNp_verbatim_holds
    D1pos_oper_d1pos_ctx_multiM_holds
    D1pos_oper_d1pos_notbrle_period_fullShift_holds
    D1pos_oper_d1pos_notbrle_period_boundary_geom_holds
    D1pos_oper_d1pos_notbrle_Br_align_regA_holds
    D1pos_oper_d1pos_low_anchor_shamt0_holds
    D1pos_oper_d1pos_lenPSeq_unified_holds
    D1pos_oper_d1pos_period_boundary_cleMB_holds
    D1pos_oper_d1pos_branch_anchor_holds
    D1pos_oper_d1pos_ctx_tnc_prefix_holds
    D1pos_nextR1_boundary_stop_d1pos_holds
    D1pos_oper_d1pos_ctx_le0Np_holds

/-- §6.8 命題（標準形の切片と `Br` の降順性の関係、訂正 A7/A8 適用後）— 無条件版:
任意の `M ∈ ST_PS` と `j₀' < j₁' ≤ Lng M - 1` に対し、`(0,j₀') ≤_M (0,j₁')` ならば
切片 `(M_j)_{j=j₀'}^{j₁'}` は単項で、その `Br` は降順である。 -/
theorem standard_slice_Br_descending
    (M : PS) (j₀' j₁' : ℕ) (hM : STPS M)
    (hlt : j₀' < j₁') (hj₁ : j₁' ≤ Lng M - 1)
    (hanc : leR M 0 j₀' j₁' = true) :
    monoT (seg M j₀' j₁') = true ∧
      descending (Br (seg M j₀' j₁')) :=
  standard_slice_Br_descending_of_d1pos rankSuccD1posLeg_proved
    M j₀' j₁' hM hlt hj₁ hanc

#print axioms rankSuccD1posLeg_proved
#print axioms standard_slice_Br_descending

end PSS

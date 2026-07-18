import «8».«8.4-mnform-corner-dispatch»
import «8».«8.4-c2hole-engine»
import «8».«8.4-d4a-target»

/-!
# §8.4 slicepkg dispatch residuals（`8.4-mnform-corner-dispatch` の `needs` 討伐）

`8.4-mnform-corner-dispatch` は死んだ `mnformBottomResidual_holds ∘ mnformResidual_holds`
合成を `mnformResidual_dispatch_md` に置換し、`Exch84_condIIIIV_slicepkg` を 6 本の named
残差へ縮約した。本ファイルはそのうち **公開 scb エンジンだけで閉じる残差**を discharge する:

* **`TransC2HoleDecomp_md`**（c4, `8.4-mnform-corner-dispatch` 露出。Isabelle `d4c2_sd`）—
  `transC2 M` の末尾 principal `D_{M₁,ₗₙ₋₁} 0_B` を露出する scb 分解。built
  `8.4-exch84-scbdecomp` の private twin `d4c2_sd` は import 越しに見えないが、
  `8.4-c2hole-engine` の公開エンジン `c2hole_scb_ch`（`transC2 M = c2hole_ch M (entry M 1
  (lastIdx M))`、`lastIdx M = Lng M - 1`）が **まさにその穴機構**を露出しているので、
  穴 `a = entry M 1 (Lng M - 1)` を埋めれば無条件（正確には `hcond` 依存のみ）で組める。

RE-DISPATCH の残り 5 本は Lean 未移植の機構を消費するため本ファイルでは discharge しない。
調査結果（次 wave 向け）:

* **`MnformCornerResidual_md`（隅 mnform, Isabelle `oi5_bodyOT`/`c4dx_condIV_k1`）**: 隅では
  collapse 恒等式 `cornerCollapse_holds_cr`（`Trans (s84x_N M)=transC2 M`／`Trans (Pred
  (s84x_N M))=transC1 M`）で `MnformResidual M`（«8».«8.4-exch84-mnform»:93）と語彙が 1:1
  に対応するため、本残差は **corner 版 `MnformResidual`** そのもの＝隅での surgery readout
  束（`Trans (oper M 1)`／`Trans (s84x_L M 1)`／`Trans (s84x_Lp M)`／`Trans (Pred (s84x_Np
  M))` の平坦形＋`scb_kind1 (Trans M)`）。これらは REGS/REGSP 隅 surgery エンジン
  （`c4dx_condIV_k1` ＋読み出し補題群）を要し、Lean 未移植。BLOCKED。

* **`NestScbD4aReducedValue`（簡約host 終切片値, Isabelle `w84x_slice_value_of_reg`/
  `crg_slice_value_of_trunk`）**: `Trans (seg R m (Lng R-1)) = D_{R₁,ₘ} (bpHeadT (Trans R))`
  where `R = Red (Pred (s84x_N M))`。頭形は公開 `slice_Trans_principal_head`
  （«8».«8.2-condIIIV-terminal-slice-Trans»）で `D_{R₁,ₘ}(bpHeadT (Trans (seg R m ..)))`
  まで出るが、**body 保存** `bpHeadT (Trans (seg R m ..)) = bpHeadT (Trans R)` が残る。
  これは `8.3-condII-NotLdjReg-close`:30 の VE body-preservation で得られるが仮定
  `VEReg m R` を要し、その regime membership は «8».«8.4-exch84-regsp» の named 残差
  `Regsp_slx37_regSP`（＝Isabelle `slx37_regSP_uncond`、`wid_*_Pred`/`trunk_entries_offset`
  等未移植）または trunk 対角閉形式のいずれか。どちらも Lean 未移植。BLOCKED。

* `NestScbD4aTransport_ns`／`MnformBottomExtResidual`／`Base0_condIIIIV`／
  `Base1p_condIIIIV` — 本ミッションの対象外（別ファイルの needs）。

- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private helper suffix: `_sr`。
-/

namespace PSS

/-! ## 残差 (1): `TransC2HoleDecomp_md`（c4, Isabelle `d4c2_sd`）を公開エンジンで discharge -/

/-- `transT1 M ≠ 0_B`（`1 < Lng M - 1` 下）。built `8.4-exch84-scbdecomp` の private
`setup_sd` / `8.4-c2hole-engine` の private `setup_sd_ch` の再掲（module 跨ぎ不可）。 -/
private theorem transT1_ne_sr (M : PS) (hMR : RTPS M) (hj1 : 1 < Lng M - 1) :
    transT1 M ≠ BZero := by
  have hlen : 1 < Lng M := by omega
  have hLP : Lng (Pred M) = Lng M - 1 := by simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred M) = false := by
    have hne : ¬ (Lng (Pred M) = 1) := by rw [hLP]; omega
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl hne
  have T1' : Trans (Pred M) ≠ BZero :=
    (Trans_Mark_invariant (Pred M) (RTPS_Pred M hMR)).2.1 nzP
  simpa [transT1] using T1'

/-- **c4 残差 `TransC2HoleDecomp_md` の discharge**（Isabelle `d4c2_sd`）。公開エンジン
`c2hole_scb_ch`（`8.4-c2hole-engine`）を穴 `a = entry M 1 (Lng M - 1)` で埋める。
`transC2 M = c2hole_ch M (entry M 1 (lastIdx M))`（`c2hole_at_j1_ch`、`rfl`）かつ
`lastIdx M = Lng M - 1`（定義）なので、埋めた分解がそのまま c4 の scb 分解になる。 -/
theorem transC2HoleDecomp_holds_sr : TransC2HoleDecomp_md := by
  intro M hST hmono _hp hj1 _hcond
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  have hT1 : transT1 M ≠ BZero := transT1_ne_sr M hMR hj1
  obtain ⟨w, w', W⟩ := c2hole_scb_ch M hMR hMT hmono hJ1pos hT1
  exact ⟨Sym.dsym (transV M) :: w, w', W (entry M 1 (Lng M - 1))⟩

#print axioms transC2HoleDecomp_holds_sr

end PSS

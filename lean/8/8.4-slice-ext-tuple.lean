import «8».«8.4-exch84-from-slice»
import «8».«8.4-exch84-nest-scb»

/-!
# §8.4 `SliceExtTupleResidual` の縮約（`c1` の scb 分解存在を無条件討伐）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係、
  補題（条件(III)か(IV)の下での各種 scb 分解）content.md 4802 の L6）。
- 対象: ビルド済み «8».«8.4-exch84-from-slice» が露出した tight named 残差
  `SliceExtTupleResidual`（＝ Isabelle `m_8_4_various_scb_IIIIV_from_slice`
  @ `n = 1` の残る 3 連言 `c1`/`c7`/`L₁`、isabelle/layerB/pss_wip.thy:60034）を、
  **`c1` の scb 分解存在（Isabelle `s84d_dec1_Trans_N_scb` の dec1 エンジン）を
  Lean のビルド済み Mark/MarkedB 機構で無条件に討伐**した上で、残る engine 束
  （`c1` の kind1 shape ＋ `c7` の右端置換 ＋ `L₁` の塔基底 c2hole）を tight named
  Prop `SliceExtTupleEngines_st` として 1 本に束ねる。

## `c1` の scb 分解存在の討伐（Isabelle `s84d_dec1_Trans_N_scb` = dec1 エンジン）

Isabelle の `s84d_dec1_Trans_N_scb`（layerB/pss_wip.thy:58846）は
`(M, j₋₃) ∈ Marked`（= `s84d_jm3_Marked`）・`Mark M j₋₃ = Trans N`
（= `m_7_4_Mark_Trans_repr`）・`(Trans M, Mark M j₋₃) ∈ MarkedB`
（= `m_7_3_Trans_Mark_MarkedB`）から `scb_decomp (Trans M) s (flatBT (Trans N)) b`
を一意に取り出す。Lean 側は同じ 3 補題がビルド済み:

| Isabelle | Lean（本ファイルで消費） |
|---|---|
| `s84d_jm3_Marked` | `Regs_jm3Marked_holds`（«8».«8.4-exch84-mcond»） |
| `m_7_4_Mark_Trans_repr` | `Mark_Trans_repr`（«7».«7.4-Mark-Trans-repr»） |
| `m_7_3_Trans_Mark_MarkedB` | `Trans_Mark_mem_MarkedB`（«7».«7.3-Trans-welldefined»） |

これにより `SliceExtTupleResidual` の `∃ u0 v0` の witness 生成（dec1 エンジン）は
本ファイルで閉じ、残差 `SliceExtTupleEngines_st` は **その canonical な `(u0, v0)` に
対して** kind1 shape / `c7` / `L₁` を検証すればよい形に絞られる（`c7` は `(u0, v0)`
非依存）。

## 残る 3 engine（`SliceExtTupleEngines_st`、`needs` 参照）

- `c1` の **kind1 shape**（`RightNodes (Trans (s84x_N M))` = `RightAnces (s84x_N M)`
  が [Buc1] 第 1 種パターン: 先頭 < 末尾 ≤ 各内点）。Isabelle `s84c3_RightAnces_chain`
  ＋条件(III)/(IV) 由来の分類。純増スパインは kind1 でないので `s84d_jm3_Marked`
  だけでは出ず、条件(III)/(IV) の深い機構を要する。**未移植**。
- `c7`（`Trans (Lp)` の分解、穴 `D_{e₂}0`）。Isabelle `m_8_4_rightend_Trans`
  （右端置換）＋ `d4b`（`Trans (s84x_Np M)` の分解、本残差の入力に無い）。**未移植**。
- `L₁` 平坦式（塔深さ 1、canonical `(u0, v0)` に依存）。Isabelle
  `s84d_c2hole_scb`/`s84d_c2hole_L1`/`s84d_L1_data`（塔基底の c2hole エンジン）。**未移植**。

- 依存（すべてビルド済み・committed main 56b1dda）: «8».«8.4-exch84-from-slice»
  （`SliceExtTupleResidual` def・`s84x_N`/`s84x_Lp`/`s84x_L`/`s84x_jm2`/`s84x_jm3`・
  `transC1`/`transC2`・`Trans`/`scb_decomp`/`scb_kind1`・`Dprin`/`flatBT`/`BZero`・
  `STPS`/`STPS_RTPS`/`RTPS_TPS`）、«8».«8.4-exch84-nest-scb»（transitively
  «8».«8.4-exch84-mcond» = `Regs_jm3Marked_holds`、«7».«7.4-Mark-Trans-repr» =
  `Mark_Trans_repr`、«7».«7.3-Trans-welldefined» = `Trans_Mark_mem_MarkedB`/`MarkedB`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `c1` の scb 分解存在を無条件討伐。残差 = `SliceExtTupleEngines_st`（本ファイル露出、
  `needs` 参照）＝ kind1 shape ＋ c7 rightend ＋ L₁ c2hole の未移植 engine 束。
- Private helper suffix: `_st`。
-/

namespace PSS

/-! ## 1. 未移植 engine 束の残差（named Prop）

`c1` の scb 分解 `scb_decomp (Trans M) u0 (flatBT (Trans (s84x_N M))) v0` を入力に取り
（本ファイルが供給）、その canonical な `(u0, v0)` に対して kind1 shape・`c7`・`L₁` を
束ねる。`c7` は `(u0, v0)` 非依存。 -/

/-- 残差: `c1` の kind1 shape（Isabelle `s84c3_RightAnces_chain` ＋条件(III)/(IV)
分類）・`c7`（`m_8_4_rightend_Trans` ＋ `d4b`）・`L₁`（`s84d_c2hole_*`/`s84d_L1_data`）
を、dec1 由来の `(u0, v0)` で束ねる未移植 engine 束。 -/
def SliceExtTupleEngines_st : Prop :=
  ∀ (M : PS) (u1 u2 v1 v2 u0 v0 : List Sym),
    STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    scb_decomp (Trans (Pred (s84x_N M)))
      (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 →
    scb_decomp (Trans (s84x_N M))
      (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1 →
    scb_decomp (transC2 M) u2
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2 →
    scb_decomp (Trans (Pred (s84x_Np M)))
      (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 →
    -- `c1` の scb 分解（dec1 エンジンで本ファイルが供給する canonical witness）
    scb_decomp (Trans M) u0 (flatBT (Trans (s84x_N M))) v0 →
      -- `c1`: kind1 shape の付与
      scb_kind1 (Trans M) u0 (flatBT (Trans (s84x_N M))) v0 ∧
      -- `c7`: `Trans (Lp)` の分解（穴 `D_{e₂}0`）
      scb_decomp (Trans (s84x_Lp M))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1 ++ u2)
        (flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)) (v2 ++ v1) ∧
      -- `L₁` 平坦式（塔深さ 1）
      flatBT (Trans (s84x_L M 1))
        = u0 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: (u1 ++ u2 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)])
            ++ [Sym.zero] ++ (v2 ++ v1) ++ v0

/-! ## 2. 縮約本体（house pattern、dec1 エンジンで `c1` の scb 分解を無条件討伐） -/

/-- **`SliceExtTupleResidual` の drop-in**（house pattern）。dec1 エンジン
（`Regs_jm3Marked_holds` ＋ `Mark_Trans_repr` ＋ `Trans_Mark_mem_MarkedB`）で
`c1` の scb 分解 witness `(u0, v0)` を無条件に生成し、残る kind1 shape/`c7`/`L₁` を
`SliceExtTupleEngines_st` から取り、`∃ u0 v0` の 3 連言を組む。 -/
theorem sliceExtTupleResidual_holds (h : SliceExtTupleEngines_st) :
    SliceExtTupleResidual := by
  intro M u1 u2 v1 v2 hST hmono hp hj1 hcond dP d2 d4c2 d4a
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  -- dec1 エンジン: `(M, j₋₃) ∈ Marked`, `j₋₃ < Lng M - 1`
  obtain ⟨mM3, jm3le, jm2lt⟩ := Regs_jm3Marked_holds M hMR hMT hp
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt jm3le jm2lt
  -- `Mark M j₋₃ = Trans N`
  have reprM : Mark M (s84x_jm3 M) = Trans (s84x_N M) :=
    Mark_Trans_repr M (s84x_jm3 M) mM3 hMR jm3lt
  -- `(Trans M, Mark M j₋₃) ∈ MarkedB` → scb 分解を取り出す
  obtain ⟨u0, v0, hd0⟩ := Trans_Mark_mem_MarkedB M (s84x_jm3 M) hMR mM3
  rw [reprM] at hd0
  -- 残る engine 束を適用
  obtain ⟨hk1, hc7, hL1⟩ :=
    h M u1 u2 v1 v2 u0 v0 hST hmono hp hj1 hcond dP d2 d4c2 d4a hd0
  exact ⟨u0, v0, hk1, hc7, hL1⟩

#print axioms sliceExtTupleResidual_holds

end PSS

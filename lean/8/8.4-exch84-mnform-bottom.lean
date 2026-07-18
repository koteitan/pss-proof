import «8».«8.4-exch84-mnform-residual»
import «8».«8.4-exch84-scbdecomp»

/-!
# §8.4 `MnformBottomResidual`（生 scb タプル）の縮約

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 対象: ビルド済み «8».«8.4-exch84-mnform-residual» が露出した底束
  `MnformBottomResidual`（= Isabelle `cpx_various_scb_IIIIV` @ `m=1` の生 scb タプル、
  isabelle/layerB/pss_wip.thy:98539）を、既存の兄弟残差へ縮約する。

## 縮約の内訳

`MnformBottomResidual` の 10 連言（`hflat`/`c1`/`c2`/`c3`/`c4`/`c5`/`c7`/`L₁`/`M[1]`/`ubeq`）
のうち、本ファイルは以下を**無条件に**片付ける:

| 連言 | 本ファイルの導出 |
|---|---|
| `ubeq` | `RTPS_condAB`（§6.6）の RedCondA ランプ（`entry M 1 j₋₂ + 1 = entry M 1 j₁`）から無条件 |
| `c2`/`c3`/`c4`/`c5` | `Exch84_nestScbTriple`（«8».«8.4-exch84-scbdecomp» 露出の nest-scb 三つ組）を
  `Exch84_scbDecompPkg_of_triple` で `Exch84_scbDecompPkg`（`dP`/`d2`/`d4c2`/`d4a`）へ持ち上げ、
  共有 witness `u1 u2 v1 v2` の 4 分解として消費 |

残る 5 連言（挿入段 `ins` の flat 則 `hflat`／`Trans M` の第 1 種分解 `c1`／`Trans (s84x_Lp M)`
の分解 `c7`／`L₁`・`M[1]` の平坦式）は Isabelle `m_8_4_various_scb_IIIIV_from_slice`
（塔・右端置換 surgery を消費）に対応し、REGS/REGSP エンジン塔の未移植部なので、
`Exch84_scbDecompPkg` の witness `u1 u2 v1 v2`（と `c2`/`c3`/`c4`/`c5`）を共有する形の
tight named Prop `MnformBottomExtResidual` として露出する。

これにより `MnformBottomResidual` は 2 本の named 残差
`Exch84_nestScbTriple`（Wave U で露出済・兄弟原子）＋ `MnformBottomExtResidual`（本ファイル）
へ縮約される（`ubeq` と `c2`–`c5` の配線は無条件討伐）。

- 依存（すべてビルド済み・committed main d96fb0b）: «8».«8.4-exch84-mnform-residual»
  (`MnformBottomResidual`・`s84x_N`/`s84x_Np`/`s84x_L`/`s84x_Lp`/`s84x_jm2`/`s84x_jm3`・
  `transC1`/`transC2`・`Trans`/`oper`・`scb_decomp`/`scb_kind1`・`Dprin`・`flatBT`・
  `RTPS_condAB`（推移的、§6.6）)、«8».«8.4-exch84-scbdecomp»
  (`Exch84_nestScbTriple`・`Exch84_scbDecompPkg_of_triple`、推移的に `Exch84_scbDecompPkg`)。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `ubeq` と `c2`–`c5` の配線は無条件。残差 = `Exch84_nestScbTriple`（既出）＋
  `MnformBottomExtResidual`（本ファイル露出、`needs` 参照）。
- Private helper suffix: `_mb`。
-/

namespace PSS

/-! ## 0. `ubeq` の無条件討伐（Isabelle `cpx_condIII_mnform` の `ubeq`、RedCondA ランプ） -/

/-- `entry M 1 (s84x_jm2 M) = entry M 1 (Lng M - 1) - 1`（`s84x_jm2 M = parent M 1 (Lng M-1)`
の RedCondA ランプ）。Isabelle `cpx_condIII_mnform` の `ubeq`（`RedCondA` を消費）を無条件化。
`8.4-s84x-vocab-run.lean:257-265`（`e1x_e1ge_uncond_of_ineq`）と同じランプ。 -/
private theorem ubeq_mb (M : PS) (hST : STPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    entry M 1 (s84x_jm2 M) = entry M 1 (Lng M - 1) - 1 := by
  have condA : RedCondA M = true := (RTPS_condAB M (STPS_RTPS M hST)).1
  have hLM : Lng M - 1 < Lng M := by omega
  simp only [RedCondA, List.all_eq_true] at condA
  have hbody := condA 1 (by decide) (Lng M - 1) (List.mem_range.mpr hLM)
  rw [hp] at hbody
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hbody
  have ramp : entry M 1 (s84x_jm2 M) + 1 = entry M 1 (Lng M - 1) := hbody
  omega

/-! ## 1. tight named 残差（`m_8_4_various_scb_IIIIV_from_slice` の塔・surgery 部） -/

/-- `MnformBottomResidual` の 5 連言（`hflat`/`c1`/`c7`/`L₁`/`M[1]`）を、`Exch84_scbDecompPkg`
の共有 witness `u1 u2 v1 v2`（と `c2`/`c3`/`c4`/`c5`）を仮定した上で要求する tight named Prop。
Isabelle `m_8_4_various_scb_IIIIV_from_slice`（`d2`/`d4a`/`d4b` から L6 タプルの底平坦式・
Lp 分解・第 1 種分解を組む段）の未移植部（塔帰納・右端置換 surgery・`d4vx_ins` 構成）に対応。 -/
def MnformBottomExtResidual : Prop :=
  ∀ (M : PS) (u1 u2 v1 v2 : List Sym),
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
    ∃ (ins : BT → BT) (u0 v0 : List Sym),
      -- `hflat`: 挿入段の flat 則（穴 `dsym ub`、`s0 = u1++u2`、`b0 = v2++v1`）
      (∀ X, flatBT (ins X)
          = (u1 ++ u2) ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞)
              :: flatBT X ++ (v2 ++ v1)) ∧
      -- `c1`: `Trans M` の kind1 分解（穴 `Trans N`）
      scb_kind1 (Trans M) u0 (flatBT (Trans (s84x_N M))) v0 ∧
      -- `c7`: `Trans (Lp)` の分解（穴 `D_{e₂}0`）
      scb_decomp (Trans (s84x_Lp M))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1 ++ u2)
        (flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)) (v2 ++ v1) ∧
      -- `L₁` 平坦式（塔深さ 1）
      flatBT (Trans (s84x_L M 1))
        = u0 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: (u1 ++ u2 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)])
            ++ [Sym.zero] ++ (v2 ++ v1) ++ v0 ∧
      -- `M[1]` 平坦式（塔深さ 0）
      flatBT (Trans (oper M 1))
        = u0 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: u1 ++ flatBT (transC1 M) ++ v1 ++ v0

/-! ## 2. 縮約本体（house pattern） -/

/-- **`MnformBottomResidual` の drop-in**（house pattern）。`Exch84_nestScbTriple`
（→ `Exch84_scbDecompPkg` で `c2`/`c3`/`c4`/`c5` 供給）＋ `MnformBottomExtResidual`
（`hflat`/`c1`/`c7`/`L₁`/`M[1]` 供給）から、`ubeq` を無条件に足して底束を組む。 -/
theorem mnformBottomResidual_holds
    (htriple : Exch84_nestScbTriple) (hext : MnformBottomExtResidual) :
    MnformBottomResidual := by
  have pkg := Exch84_scbDecompPkg_of_triple htriple
  intro M hST hmono hp hj1 hcond
  obtain ⟨_hT1, u1, u2, v1, v2, dP, d2, d4c2, d4a⟩ := pkg M hST hmono hp hj1 hcond
  obtain ⟨ins, u0, v0, hflat, hc1, hc7, hL1flat, hM1flat⟩ :=
    hext M u1 u2 v1 v2 hST hmono hp hj1 hcond dP d2 d4c2 d4a
  have hub := ubeq_mb M hST hp hj1
  exact ⟨ins, u0, u1, u2, v2, v1, v0, hflat, hc1, dP, d2, d4c2, d4a, hc7, hL1flat, hM1flat, hub⟩

#print axioms mnformBottomResidual_holds

end PSS

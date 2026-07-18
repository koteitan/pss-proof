import «8».«8.4-slice-ext-engines»
import «8».«8.4-rightmost-replace-close»
import «8».«8.4-parent-max»
import «7».«7.2-scb-compose»
import «7».«7.3-c1-c2-order»

/-!
# §8.4 `SliceExtTupleEngines_st` の 3 tight Props への攻略（`c7` を rm84 存在へ還元）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係、
  補題（条件(III)か(IV)の下での各種 scb 分解）content.md 4802 の L6）。
- 対象: ビルド済み «8».«8.4-slice-ext-engines» が露出した 3 つの tight named 残差
  `Kind1Shape_se`（`c1` の kind1 shape）・`C7Rightend_se`（`c7` 右端置換）・
  `L1SliceData_se`（`L₁` slice 幾何）。`L₁` 平坦式（塔基底）は engines 側で c2hole
  エンジン ＋ 合成 ＋一意性により無条件討伐済み（`l1Base_se`）。本ファイルは残る
  3 Props を攻める。

## 本ファイルの寄与（`C7Rightend_se` を既存 rm84 資産へ還元）

**`C7Rightend_se`（`c7`）を、既にビルド済みで活発に攻略中の残差
`Rightmost84ReplaceExists`（«8».«8.4-rightmost-replace-close»、rm84 surgery で
`Rm84SurgeryFrame` へ 45/45 数値検証済み）＋ 1 本の clean な slice 幾何残差
`Np_c2decomp_sc3` へ無条件に還元する。** これにより `c7` の「右端置換」内容が rm84
campaign に統合され、opaque な `Trans (s84x_Lp M)` 分解が消える。

Isabelle `m_8_4_various_scb_IIIIV_from_slice`（wip:60034）の `cj7` 段:
- `comp4 = m_7_2_scb_compose[OF c2prin d4b Wj1(=d4c2)]` で `Trans (s84x_Np M)` を
  中心 `D_{e₁ⱼ₁}0` で分解（prefix `D_{e₁ⱼ₋₂} :: u1 ++ u2`, tail `v2 ++ v1`）。
- rm84 存在（`m_8_4_rightend_Trans`, wip:54650）が `Trans (s84x_Np M)`（中心
  `D_{e₁ⱼ₁}0`）と `Trans (s84x_Lp M)`（中心 `D_{e₁ⱼ₋₂}0`）を共有 `(s,b)` で分解。
- `comp4` と rm84 の `Trans (s84x_Np M)` 分解を `scb_unique_decomp_unconditional`
  で pin（中心固定 ⇒ `(s,b)` 一意）し、rm84 の `Trans (s84x_Lp M)` 分解へ移送。

Lean 資産:
- `Rightmost84ReplaceExists`（«8».«8.4-rightmost-replace-close»）＝ rm84 存在。
  `rrLp M = s84x_Lp M`（定義同一、`rfl`）。
- `scb_compose`（«7».«7.2-scb-compose»）／`scb_unique_decomp_unconditional`
  （«7».«7.2-scb-unique»、engines 経由）／`transC2_single_principal`
  （«7».«7.3-c1-c2-order»）。
- 域条件 `s84x_jm2 M + 1 < Lng M - 1` は `regs_jm2_lt_transJ0_holds`
  （«8».«8.4-parent-max»、`j₋₂ < transJ0`）＋ `parent_lt_of_hasParent`
  （`transJ0 < Lng M - 1`）から導出。

**`d4b`（`Trans (s84x_Np M)` の transC2 中心分解）は `SliceExtTupleEngines_st` の
入力に無い**（Lean `SliceExtTupleResidual` 生成時に脱落）ので、Isabelle
`w84x_d4b_dispatch`（wip:79198、`d2` から `d4b` を dispatch。非自明枝は §8.4 正則性
`cfbx_reg`）に忠実な形で tight named 残差 `Np_c2decomp_sc3` として露出する。

## 残る 2 Props（未移植 engine、blueprint と攻め筋を文書化）

- `Kind1Shape_se`: `c1` の kind1 shape。Isabelle `s84c3_RightAnces_chain`
  （wip:55372、`RightAnces` の再帰に沿う chain 不変量 `s84c3_chainOK`/`s84c3_winOK`
  ＋条件(III)/(IV) 由来の top valley）。`RightAnces` 全再帰＋`RightAnces.psimps`／
  `RightAnces_dom_RT`／`adm_zero`／`le0_refl` 群を要する巨大 induction。**未移植**。
- `L1SliceData_se`: `L₁` slice 幾何（`s84x_L M 1` の `Trans (Pred)`/`transC1`/
  `transC2` を `M` 側語彙へ結ぶ純幾何）。Isabelle `s84d_L1_data`（wip:59295、
  `m_8_4_oper_props_2`／`s84c1_Pred_L`／`s84c1_L1_*`／`parent0_eqI`／`row1_last_bound`
  等 ~15 補題）＋`s84d_c2hole_L1`（wip:59433）。**未移植**。

- 依存（すべてビルド済み・main 9ced7bd）: «8».«8.4-slice-ext-engines»
  （`Kind1Shape_se`/`C7Rightend_se`/`L1SliceData_se`・`SliceExtTupleEngines_st`・
  `sliceExtTupleEngines_of_residuals`・`SliceExtTupleResidual`・
  `sliceExtTupleResidual_of_engines_se`・`s84x_*`・`transC1`/`transC2`・`Trans`/
  `scb_decomp`・`Dprin`/`flatBT`/`BZero`・`STPS`/`STPS_RTPS`/`RTPS_TPS`）、
  «8».«8.4-rightmost-replace-close»（`Rightmost84ReplaceExists`/`rrLp`）、
  «8».«8.4-parent-max»（`regs_jm2_lt_transJ0_holds`・推移的に `mono_hasParent_row0`／
  `parent_lt_of_hasParent`）、«7».«7.2-scb-compose»（`scb_compose`）、
  «7».«7.3-c1-c2-order»（`transC2_single_principal`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `C7Rightend_se` を `Rightmost84ReplaceExists`（既存 rm84 残差）＋`Np_c2decomp_sc3`
  （clean d4b dispatch 残差）へ還元。残差 = `Kind1Shape_se` ＋ `L1SliceData_se` ＋
  `Rightmost84ReplaceExists`（→ rm84 surgery）＋`Np_c2decomp_sc3`（→ cfbx_reg）。
- Private helper suffix: `_sc3`。
-/

namespace PSS

/-! ## 1. `d4b` dispatch の残差（Isabelle `w84x_d4b_dispatch`, wip:79198）

`SliceExtTupleEngines_st`（＝`C7Rightend_se`）の入力に `d4b`（`Trans (s84x_Np M)` の
transC2 中心分解）が無いため、Isabelle `w84x_d4b_dispatch`（`d2` の N 側 transC2 分解
から `Np` 側 transC2 分解を dispatch。`j₋₃ = j₋₂` 自明枝＝`Np = N`、`j₋₃ < j₋₂` 非自明枝
＝正則性 `cfbx_reg`）に忠実な tight named Prop として露出する。 -/

/-- 残差 (d4b dispatch): N 側 transC2 分解 `d2` から `Np` 側 transC2 分解 `d4b` を作る。
Isabelle `w84x_d4b_dispatch`（wip:79198）。非自明枝（`j₋₃ < j₋₂`）は §8.4 正則性
`cfbx_reg (j₋₂ - j₋₃) (s84x_N M)` を消費するため **未移植**。 -/
def Np_c2decomp_sc3 : Prop :=
  ∀ (M : PS) (s1 b1 : List Sym),
    STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    scb_decomp (Trans (s84x_N M))
      (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: s1) (flatBT (transC2 M)) b1 →
    scb_decomp (Trans (s84x_Np M))
      (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: s1) (flatBT (transC2 M)) b1

/-! ## 2. 局所補助（`_sc3`） -/

/-- `transC2 M` は単一 principal 項（`transC2_single_principal` から `∃ p, = trm [p]`）。 -/
private theorem transC2_prin_sc3 (M : PS) : ∃ p, transC2 M = BT.trm [p] := by
  have hlen : (untrm (transC2 M)).length = 1 := by
    have := transC2_single_principal M
    simpa [PB, List.length_map] using this
  cases hd : transC2 M with
  | trm ps =>
    rw [hd] at hlen
    simp only [untrm] at hlen
    rcases ps with _ | ⟨p, ps'⟩
    · simp at hlen
    · rcases ps' with _ | ⟨q, ps''⟩
      · exact ⟨p, rfl⟩
      · simp at hlen

/-- 域条件 `s84x_jm2 M + 1 < Lng M - 1`（`j₋₂ < transJ0 < Lng M - 1`）。
Isabelle `m_8_4_various_scb_IIIIV_from_slice` の `rng`。 -/
private theorem jm2_succ_lt_sc3 (M : PS)
    (hST : STPS M) (hmono : monoT M = true) (hp : hasParent M 1 (Lng M - 1) = true)
    (j1gt : 1 < Lng M - 1) (branch : transCondIII M = true ∨ transCondIV M = true) :
    s84x_jm2 M + 1 < Lng M - 1 := by
  have hMT : TPS M := RTPS_TPS M (STPS_RTPS M hST)
  have jm2ltj0 : s84x_jm2 M < transJ0 M :=
    regs_jm2_lt_transJ0_holds M hST hmono hp j1gt branch
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have j0lt : transJ0 M < Lng M - 1 := by
    have h := parent_lt_of_hasParent M 0 (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  omega

/-! ## 3. `C7Rightend_se` の還元（rm84 存在 ＋ d4b dispatch） -/

/-- **`c7` を rm84 存在＋d4b dispatch へ還元**。`comp4`（`scb_compose`）＋rm84 存在＋
一意 pin ＋`rrLp = s84x_Lp`（`rfl`）で `Trans (s84x_Lp M)` の分解を組む。 -/
theorem c7Rightend_of_rm84_np_sc3
    (hRM : Rightmost84ReplaceExists) (hNp : Np_c2decomp_sc3) :
    C7Rightend_se := by
  intro M u1 u2 v1 v2 hST hmono hp j1gt branch _dP d2 d4c2 _d4a
  -- `d4b`（dispatch）
  have d4b := hNp M u1 v1 hST hmono hp j1gt branch d2
  -- `comp4 = scb_compose c2prin d4b d4c2`
  have hc2prin := transC2_prin_sc3 M
  have comp4 := scb_compose (Trans (s84x_Np M)) (transC2 M)
    (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) u2
    (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2 v1
    hc2prin d4b d4c2
  -- rm84 存在
  have hrng : s84x_jm2 M + 1 < Lng M - 1 := jm2_succ_lt_sc3 M hST hmono hp j1gt branch
  obtain ⟨sb, hNpDec, hLpDec⟩ := hRM M hST hmono hp hrng
  -- 中心固定 ⇒ `(s,b)` 一意
  obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (s84x_Np M))
    sb.1 (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1 ++ u2)
    (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) sb.2 (v2 ++ v1)
    hNpDec comp4
  -- `Trans (s84x_Lp M)` へ移送（`rrLp = s84x_Lp`）
  have hLpeq : rrLp M = s84x_Lp M := rfl
  rw [hLpeq] at hLpDec
  rw [← hs, ← hb]
  exact hLpDec

/-! ## 4. 縮約本体（house pattern） -/

/-- **`SliceExtTupleEngines_st` の drop-in**（house pattern）。`c7` を rm84 存在＋
d4b dispatch へ還元し、kind1 shape / `L₁` slice 幾何は named 残差から取る。 -/
theorem sliceExtTupleEngines_of_reduced_sc3
    (hK : Kind1Shape_se) (hRM : Rightmost84ReplaceExists)
    (hNp : Np_c2decomp_sc3) (hLdat : L1SliceData_se) :
    SliceExtTupleEngines_st :=
  sliceExtTupleEngines_of_residuals hK (c7Rightend_of_rm84_np_sc3 hRM hNp) hLdat

/-- 4 残差から `SliceExtTupleResidual`（from_slice 底タプル）までの全鎖。 -/
theorem sliceExtTupleResidual_of_reduced_sc3
    (hK : Kind1Shape_se) (hRM : Rightmost84ReplaceExists)
    (hNp : Np_c2decomp_sc3) (hLdat : L1SliceData_se) :
    SliceExtTupleResidual :=
  sliceExtTupleResidual_of_engines_se hK (c7Rightend_of_rm84_np_sc3 hRM hNp) hLdat

#print axioms c7Rightend_of_rm84_np_sc3
#print axioms sliceExtTupleEngines_of_reduced_sc3
#print axioms sliceExtTupleResidual_of_reduced_sc3

end PSS

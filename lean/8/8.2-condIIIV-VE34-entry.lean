import «8».«8.2-condIIIV-terminal-slice-Trans»
import «8».«8.2-condV-VE-base»

/-!
# §8.2 条件(II)/(IV) の値方程式 `VE2`/`VE3`/`VE4` の後ろ剥がしキャンペーンの入口

- 原文: `tmp/content.md` L3314 付近（条件(II)か(IV)の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分
  （「subexpr-component-`Pred`」補題、L3360）。この帰納法が
  `condIIIV_terminal_slice_Trans_modVE`（`8.2-condIIIV-terminal-slice-Trans`）の
  名前付き仮定 `VE2`/`VE3`/`VE4` を供給する。
- 訂正: なし（本ファイルの主張はいずれも Isabelle 側で証明済みの補題の逐語移植か、
  その骨格）。
- Isabelle: condII/IV VE キャンペーンの入口ブロック（`isabelle/layerB/pss_wip.thy`
  93171–108761、prefix `vg2x_`/`vg3x_`/`vg4x_`/`vg7x_`/`bfx_`/`bgx_`/`hqx_`、約 15.6k 行）。
  そのうち本ファイルが移植する**入口の語彙と後ろ剥がし骨格**は:
  - `vg2x_reg2` (93178, definition) → `VE34Reg`（条件(II)/(IV) の体制。
    `N ∈ RT_PS ∧ N ∈ PT_PS ∧ Br N ≠ []`。`PT_PS = {M ∈ T_PS ∧ monoT M}` かつ
    `RT_PS ⊆ T_PS` なので `RTPS N ∧ monoT N ∧ Br N ≠ []` と同値に書く。
    条件(V) 双子の `VEReg`（`8.2-condV-VE-base`）から `m` の場合分け連言を落とした形）
  - `vg2x_VE34` (93181, abbreviation) → `VE34goal`（成長項 `t₂` の存在。
    `condIIIV_terminal_slice_Trans_modVE` の `VE3`/`t₂ ≠ 0_B`/`VE4` を束ねた形）
  - `vg2x_VE34_backpeel` (93197) → `VE34_backpeel`（`Lng` に関する強帰納法と二分岐
    `cfbx_j1p N ≤ Lng N - 1` を消化する後ろ剥がし骨格。**無条件**で
    `{BASE, STEP, RPERS}` の三つ組に還元する。条件(V) 双子の `VE_backpeel`
    そのものの構造）
  - `vg2x_VE34_of_reg` (93247) → `VE34_of_reg`（体制からの end-to-end 還元）
  - `vg2x_VE2` (93126) → `VE2goal`（値方程式の一本目。本ファイルは Prop 定義のみ。
    その完全な閉包は `vg2x_cfbx_reg`/`vg2x_VE2_reg`/`vg2x_VE2_trunk`（93037 以下）の
    連鎖で、`vgx_LastStep_lt_of_guard`/`vg2x_N_DT`/`vgx_VE2_of_reg`/
    `crg_slice_value_of_trunk` 等の前座が要り、単一ファイルの射程外）
- **`cfbx_j1p`（＝最終枝の左端）は条件(V) と条件(II)/(IV) で共通**なので、
  `8.2-condV-VE-base` の `VEj1p` をそのまま再利用する。二分岐のキー
  `cfbx_j1p N ≤ Lng N - 1` も両者共通（`a1_FN_lt`、本ファイルの `VEj1p_lt_v34`）。
- 依存の全体像（次以降のブリック、Isabelle の依存スパイン）:
  `vg2x_VE34_of_reg`（本ファイル、`{BASE, STEP, RPERS}` modulo）
  → `vg3x_VE34_of_DT` (94529) → `vg4x_VE34_of_DT` (95296) → `vg7x_VE34_of_DT` (97503)
  → `vg7x_condIIIV_of_DT` (97539)。BASE の実体は `bfx_*` (104483–105477)、
  `bgx_*` (106276–107275)、`hqx_*` (108411–108722) の連鎖で、最終的に
  `hqx_condIIIV_of_DT` (108722) が `VE2`/`VE3`/`VE4` を無条件で供給する。
  本ファイルはその**最下段の入口**（骨格＋語彙）だけを緑で提供し、
  次のブリック `{VE34Base, VE34Step, VE34Rpers}` と `VE2goal` を名前付き Prop に
  露出する。
- 依存 module: `8.2-condIIIV-terminal-slice-Trans`（`LastStep`・切片幾何・
  `condIIIV_terminal_slice_Trans_modVE`・`DTPS`/`DTPS_iff` を推移的に）、
  `8.2-condV-VE-base`（`VEj1p`＝`cfbx_j1p`）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。公開定理は無条件（骨格）または名前付き Prop
  `{VE34Base, VE34Step, VE34Rpers}` / `VE2goal` を仮定に持つ。原文の値方程式
  三つ組（`vg2x_VE2` + `vg2x_VE34`）の完全な閉包は上記の back-peel 連鎖が与えるが、
  約 15k 行あり本ファイルの射程外。
-/

namespace PSS

/-! ## 条件(II)/(IV) の体制と目標（Isabelle `vg2x_reg2` / `vg2x_VE34`） -/

/-- **Isabelle `vg2x_reg2` (layerB 93178)**: 条件(II)/(IV) の後ろ剥がし帰納法の体制。

Isabelle は `N ∈ RT_PS ∧ N ∈ PT_PS ∧ Br N ≠ []` と書くが、
`PT_PS = {M ∈ T_PS ∧ monoT M}` かつ `RT_PS ⊆ T_PS`（`RTPS_TPS`）なので、
ここでは同値な `RTPS N ∧ monoT N ∧ Br N ≠ []` と書く。条件(V) 双子の
`VEReg`（`8.2-condV-VE-base`）から `m` の場合分け連言を落とした形。 -/
def VE34Reg (N : PS) : Prop :=
  RTPS N ∧ monoT N = true ∧ Br N ≠ []

instance (N : PS) : Decidable (VE34Reg N) := by
  unfold VE34Reg RTPS; infer_instance

/-- **Isabelle `vg2x_VE34` (layerB 93181, abbreviation)**: 成長項 `t₂` の存在。

`condIIIV_terminal_slice_Trans_modVE`（`8.2-condIIIV-terminal-slice-Trans`）の
名前付き仮定 `VE3`・`t₂ ≠ 0_B`・`VE4` を束ねた形そのもの。
記号（訂正 A9 後）: `j'₀ = Joints(M)_{J₁}`（`J₁ = Lng(Br M) - 1`）、
`m₁ = FirstNodes(M)_{J₀} - 1`（`J₀ = LastStep M`）、`j₁ = Lng M - 1`、
`N = seg M 0 m₁`、`M' = seg M j'₀ j₁`。 -/
def VE34goal (M : PS) : Prop :=
  ∃ t2 : BT,
    bpHeadT (Trans (seg M ((Joints M).getD ((Br M).length - 1) 0) (Lng M - 1)))
      = addBT (bpHeadT (Trans (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)))) t2
    ∧ t2 ≠ BZero
    ∧ bpHeadT (Trans M)
      = addBT (bpHeadT (Trans (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))))
          (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
            (bpHeadT (Trans (seg M ((Joints M).getD ((Br M).length - 1) 0) (Lng M - 1)))))

/-- **Isabelle `vg2x_VE2` (layerB 93126) の結論**: 値方程式の一本目
（`condIIIV_terminal_slice_Trans_modVE` の名前付き仮定 `VE2`）。本ファイルは
Prop 定義のみを提供し、その閉包（`vg2x_cfbx_reg`/`vg2x_VE2_reg`/`vg2x_VE2_trunk`）は
射程外。 -/
def VE2goal (M : PS) : Prop :=
  bpHeadT (Trans (seg M ((Joints M).getD ((Br M).length - 1) 0)
                        ((FirstNodes M).getD (LastStep M) 0 - 1)))
    = bpHeadT (Trans (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)))

/-! ### 転記の数値検証（体制の判定を `decide` で照合） -/

-- witness `M = (0,0)(1,1)(2,2)(2,0)`（`8.2-condIIIV-terminal-slice-Trans` の
-- `witness_c24` と同じ）は体制に属する。
#guard decide (VE34Reg [(0,0),(1,1),(2,2),(2,0)]) = true
-- 幹（`Br = []`）は体制に属さない。
#guard decide (VE34Reg [(0,0),(1,1),(2,2)]) = false

/-! ## 私的補助（suffix `_v34`） -/

/-- `leR M 0 a b` は両添字を `Lng M` 未満に閉じ込める（Isabelle では `le0` の
定義から直接）。条件(V) `leR0_bounds_ve` の双子。 -/
private theorem leR0_bounds_v34 (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- Isabelle `a1_FN_lt` (pss_mechanized 33186): 枝の左端は `Lng` 未満。
条件(V) `FN_lt_ve` の双子。 -/
private theorem FN_lt_v34 (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M :=
  (leR0_bounds_v34 M _ _
    (nextR_implies_row0 M 0 _ _ (Joints_nextR_FirstNodes M J hM hmono hJ)).2).2

/-- 体制の下で `VEj1p N < Lng N`（＝`cfbx_j1p N < Lng N`、Isabelle 版の
`a1_FN_lt[OF MP J1lt]`）。 -/
private theorem VEj1p_lt_v34 (N : PS) (hreg : VE34Reg N) : VEj1p N < Lng N := by
  obtain ⟨hR, hmono, hBrne⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  exact FN_lt_v34 N _ hM hmono hJ

/-- `Lng (Pred N) = Lng N - 1`（`1 < Lng N` のとき）。条件(V) `Lng_Pred_ve` の双子。 -/
private theorem Lng_Pred_v34 (N : PS) (h : 1 < Lng N) :
    Lng (Pred N) = Lng N - 1 := by
  have hle : ¬ (Lng N ≤ 1) := by omega
  simp [Pred, hle, Lng]

/-! ## 後ろ剥がし帰納法の残差（Isabelle `vg2x_VE34_backpeel` の三仮定） -/

/-- `BASE` 枝（`j₁' = j₁`、最終列が現最終枝の中）。Isabelle `vg2x_VE34_backpeel`
の第一仮定。 -/
def VE34Base : Prop :=
  ∀ N : PS, VE34Reg N → VEj1p N = Lng N - 1 → VE34goal N

/-- `STEP` 枝（`j₁' < j₁`、帰納枝、IH `VE34goal (Pred N)` を消費）。
Isabelle `vg2x_VE34_backpeel` の第二仮定。 -/
def VE34Step : Prop :=
  ∀ N : PS, VE34Reg N → VEj1p N < Lng N - 1 →
    VE34Reg (Pred N) → VE34goal (Pred N) → VE34goal N

/-- `RPERS`（`j₁' < j₁` の場合に体制が `Pred N` へ遺伝）。
Isabelle `vg2x_VE34_backpeel` の第三仮定。 -/
def VE34Rpers : Prop :=
  ∀ N : PS, VE34Reg N → VEj1p N < Lng N - 1 → VE34Reg (Pred N)

/-! ## 後ろ剥がし骨格（Isabelle `vg2x_VE34_backpeel`, layerB 93197） -/

/-- **Isabelle `vg2x_VE34_backpeel` (layerB 93197)** の逐語移植。

`Lng` に関する強帰納法と二分岐 `VEj1p N ≤ Lng N - 1`（`VEj1p_lt_v34`）を
**無条件**で消化し、条件(II)/(IV) の値方程式目標 `VE34goal` を
`{VE34Base, VE34Step, VE34Rpers}` の三つ組へ還元する。条件(V) 双子の
`VE_backpeel`（`8.2-condV-VE-base`）と構造は同一（`m` の場合分け連言だけが無い）。 -/
theorem VE34_backpeel (hBase : VE34Base) (hStep : VE34Step) (hRpers : VE34Rpers)
    (M : PS) (hM : VE34Reg M) : VE34goal M := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | _ n ih =>
      subst hn
      have hj1lt : VEj1p M < Lng M := VEj1p_lt_v34 M hM
      by_cases hbase : VEj1p M = Lng M - 1
      · exact hBase M hM hbase
      · have hlt : VEj1p M < Lng M - 1 := by omega
        have hL2 : 1 < Lng M := by omega
        have hregP : VE34Reg (Pred M) := hRpers M hM hlt
        have hLP : Lng (Pred M) = Lng M - 1 := Lng_Pred_v34 M hL2
        have hveP : VE34goal (Pred M) :=
          ih (Lng (Pred M)) (by omega) (Pred M) hregP rfl
        exact hStep M hM hlt hregP hveP

/-- **Isabelle `vg2x_VE34_of_reg` (layerB 93247)** の逐語移植: 体制からの
end-to-end 還元。 -/
theorem VE34_of_reg (hBase : VE34Base) (hStep : VE34Step) (hRpers : VE34Rpers)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true) (hBrne : Br M ≠ []) :
    VE34goal M :=
  VE34_backpeel hBase hStep hRpers M ⟨hR, hmono, hBrne⟩

/-! ## `VE2` + `VE34goal` から `condIIIV` の主張へ（本キャンペーンの帰着先）

`condIIIV_terminal_slice_Trans_modVE`（`8.2-condIIIV-terminal-slice-Trans`）は
`VE2`/`VE3`/`VE4`/`t₂ ≠ 0_B` を個別に仮定に持つが、本ファイルの `VE34goal` は
`VE3`/`t₂ ≠ 0_B`/`VE4` を存在量化された `t₂` で束ねている。両者の橋渡し。 -/

/-- 値方程式が `VE2goal M` と `VE34goal M` の形で供給されれば、§8.2 条件(II)/(IV)
命題の結論（`condIIIV_terminal_slice_Trans_modVE`）が従う。VE34 キャンペーンが
最終的に閉じる先を明示する橋渡し補題。 -/
theorem condIIIV_of_VE2_VE34 (M : PS) (hMD : DTPS M) (hBrne : Br M ≠ [])
    (hj0pos : 0 < (Joints M).getD ((Br M).length - 1) 0)
    (hj0lt : (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
    (hguard : entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
            < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0))
    (hVE2 : VE2goal M) (hVE34 : VE34goal M) :
    ∃! t12 : BT × BT,
      Trans (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))
        = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
      Trans (seg M ((Joints M).getD ((Br M).length - 1) 0)
                   ((FirstNodes M).getD (LastStep M) 0 - 1))
        = Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞) t12.1 ∧
      Trans (seg M ((Joints M).getD ((Br M).length - 1) 0) (Lng M - 1))
        = Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
            (addBT t12.1 t12.2) ∧
      t12.2 ≠ BZero ∧
      Trans M = Dprin (entry M 1 0 : ℕ∞)
        (addBT t12.1 (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
          (addBT t12.1 t12.2))) := by
  obtain ⟨t2, hVE3, ht2ne, hVE4⟩ := hVE34
  exact condIIIV_terminal_slice_Trans_modVE M t2 hMD hBrne hj0pos hj0lt hguard
    hVE2 hVE3 ht2ne hVE4

#print axioms VE34_backpeel
#print axioms VE34_of_reg
#print axioms condIIIV_of_VE2_VE34

end PSS

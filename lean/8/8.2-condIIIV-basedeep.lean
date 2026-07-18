import «8».«8.2-condIIIV-ve34-base»

/-!
# §8.2 条件(II)/(IV) VE34 の**非極小基底（run 領域）** `VE3BaseDeep`/`VE4BaseDeep` を攻める

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分
  （「subexpr-component-`Pred`」補題、L3360）。`8.2-condIIIV-ve34-base` は BASE 二残差
  `{VE3Base, VE4Base}` の**極小基底 `Lng N = TrMax N + 2`**（＝`j₁ - TrMax = 1`）を無条件
  討伐し（`VE3_minbase_vb`/`VE4_minbase_vb`）、残差を run 領域 `TrMax N + 2 < Lng N` の
  二つ `{VE3BaseDeep, VE4BaseDeep}` に露出した。本ファイルはこの**run 領域**を
  Isabelle の同名メカ（`bfx_`/`hqx_` の後ろ剥がし same-head-run 帰納法）に沿って
  攻め、run-peel の**幾何骨格を無条件で供給**しつつ、残る中身を鋭い名前付き Prop
  （`RunPeelPreserved_bd`／`VE3RunBase_bd`（SPLIT0）／`VE3RunStep_bd`（成長輸送）／
  `PIN_bd`／`TSPIN_bd`）に**還元** する。

- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植、または名前付き Prop 骨格）。

- Isabelle（`isabelle/layerB/pss_wip.thy`, r46-BASEF, `bfx_` prefix, 104360–105477、
  `hqx_` 108411–108722）: BASE スロットを SAME-HEAD-RUN 帰納法として機械化したもの。
  `bfx_VE34_backpeel_fin3`（105253）が `Lng` 強帰納法で BASE 脚を run 二分岐
  （`LastStep N = J₁` の run-base、`LastStep N < J₁` の run-step）に割り、run-peel の
  regime/fin/front/terminal 安定（`bfx_RPERS_base` 等）を**内部で証明**、carry する残差は
  `{TSPIN, PIN, SPLIT0}`（いずれも経験的に真）。VE3 の run-step 輸送 `bfx_VE3_base_step`
  はキーストーン `kyx_terminal_slice_keystone` modulo で**閉じている**が、Lean には
  キーストーン未移植（`8.2-condIIIV-ve34-step` ヘッダ参照）なので、Lean 側では VE3
  run-step は名前付き残差 `VE3RunStep_bd` に露出する。

- 本ファイルの割り方（VE3 と VE4 は Lean で分離済み）:
  - **VE4 は pointwise**（IH 非消費）: `Trans N` の外側 pinned 形 `PIN_bd` ＋ 輸送方程式
    `TSPIN_bd` から `VE4goal N` を**無条件アセンブル**（`bfx_VE34_base_run0_modTSPIN` の
    VE4 部を逐語）。よって `VE4BaseDeep ⟸ {PIN_bd, TSPIN_bd}`。
  - **VE3 は run 帰納法**: `Lng` 強帰納法で run-base（`SPLIT0`＝`VE3RunBase_bd`）と
    run-step（成長輸送 `VE3RunStep_bd`、IH `VE3goal (Pred N)` を消費）に割り、run-peel の
    regime＋base 保存 `RunPeelPreserved_bd`（Isabelle `bfx_RPERS_base`＋base 保存）で
    `Pred N` へ降りる。`Pred N` が極小基底に達したら `VE3_minbase_vb` で閉じる（IH 不要）。
    よって `VE3BaseDeep ⟸ {RunPeelPreserved_bd, VE3RunBase_bd, VE3RunStep_bd}`。

- 幾何: BASE `VEj1p N = Lng N - 1` では最終列は単一列の最終枝（`0 < j₀' < TrMax N`）。
  run 領域 `TrMax N + 2 < Lng N` では `Pred N` が最終列を剥がし `Lng` を 1 減らす。
  run-step（`LastStep N < J₁`）では前枝も同頭単一列なので `Pred N` は再び BASE、
  `Lng N = TrMax N + 3` で極小基底に到達（`TrMax` は `Pred` 下不変、`TrMax_Pred_nontrunk`）。

- 依存 module: `8.2-condIIIV-ve34-base`（`VE3BaseDeep`/`VE4BaseDeep`/`VE3_minbase_vb`/
  `VE4_minbase_vb`/`condIIIVterminalSlice_of_deepBase`/`VE3goal`/`VE4goal`/`VE34Reg4`/
  `VEj1p`/`VE3Step`/`VE4Step`/`LastStep`/`length_Pred`/`TrMax_Pred_nontrunk`/`RTPS_TPS`/
  `LastStep_lt_Lng_Br`/`Trans`/`bpHeadT`/`Dprin`/`addBT`/`entry`/`seg`/`Br`/`Joints`/
  `FirstNodes`/`TrMax` を推移的に）。

- 状態: ⚠️ 部分（sorry 0、rc=0）。BASE-host 幾何 `baseDeepGeom_bd` を無条件供給、
  `VE4BaseDeep` を `{PIN_bd, TSPIN_bd}` に、`VE3BaseDeep` を
  `{RunPeelPreserved_bd, VE3RunBase_bd, VE3RunStep_bd}` に**還元**。run-peel の
  regime＋base 保存および値レベルの残差（SPLIT0／成長輸送／PIN／TSPIN＝§7.4 頭シフト
  readback surgery、非許容 joint での Mark-surgery naturality）は名前付き Prop に露出。

- Private suffix: `_bd`。
-/

namespace PSS

/-! ## 私的補助（suffix `_bd`） -/

/-- `bpHeadT (Dprin a b) = b`（principal 項の内部項読み出し、`rfl`）。
`8.2-condIIIV-ve34-base` の `bpHeadT_Dprin_vb` の再掲。 -/
private theorem bpHeadT_Dprin_bd (a : ℕ∞) (b : BT) : bpHeadT (Dprin a b) = b := rfl

/-! ## BASE-host（run 領域）幾何（Isabelle `bfx_base_setup`, layerB 104483） -/

/-- **Isabelle `bfx_base_setup` (layerB 104483)** の逐語移植（run 領域版）。

訂正版体制 `VE34Reg4 N`・BASE `VEj1p N = Lng N - 1`・非極小基底 `TrMax N + 2 < Lng N`
から、run-peel が消費する共有幾何を返す: 基本体制（`RTPS`/`monoT`/`Br ≠ []`/`TPS`/
`2 < Lng N`）、`TrMax N ≠ Lng N - 1`／`TrMax N < Lng N - 1`、最終 joint の非許容境界
`0 < j₀' < TrMax N`、そして `Pred N = N.dropLast`（`Lng N > 1` から）。 -/
theorem baseDeepGeom_bd (N : PS) (reg : VE34Reg4 N)
    (_hbase : VEj1p N = Lng N - 1) (hdeep : TrMax N + 2 < Lng N) :
    RTPS N ∧ monoT N = true ∧ Br N ≠ [] ∧ TPS N ∧ 2 < Lng N ∧
    TrMax N ≠ Lng N - 1 ∧ TrMax N < Lng N - 1 ∧
    0 < (Joints N).getD ((Br N).length - 1) 0 ∧
    (Joints N).getD ((Br N).length - 1) 0 < TrMax N ∧
    Pred N = N.dropLast := by
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0lt⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  refine ⟨hR, hmono, hBrne, hM, by omega, by omega, by omega, hj0pos, hj0lt, ?_⟩
  simp [Pred, show ¬Lng N ≤ 1 by omega]

/-! ## 残差 Prop（run-peel の carry 残差、Isabelle `{TSPIN, PIN, SPLIT0}` 対応）

すべて非極小基底（run 領域）`TrMax N + 2 < Lng N` の BASE ホストに限定する。 -/

/-- **run-peel regime＋base 保存**（Isabelle `bfx_RPERS_base` (105063) ＋ base 保存）。
run-step（`LastStep N < J₁`）では `Pred N` が訂正版体制 `VE34Reg4` と BASE
`VEj1p (Pred N) = Lng (Pred N) - 1` を保つ。Isabelle は `bfx_JEQ`（run の同頭 squeeze
＋`nextR` 一意性）＋`wid_*` 族で証明。 -/
def RunPeelPreserved_bd : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    VE34Reg4 (Pred N) ∧ VEj1p (Pred N) = Lng (Pred N) - 1

/-- **VE3 run-base 残差（Isabelle `SPLIT0`）**: run-base（`LastStep N = J₁`）での
成長分割 `bpHeadT (Trans M') = F +_B t₂`、`t₂ ≠ 0_B`（`F = bpHeadT (Trans (Pred N))`、
原文 part(3) の自己相似核）。 -/
def VE3RunBase_bd : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N = (Br N).length - 1 → VE3goal N

/-- **VE3 run-step 輸送残差（Isabelle `bfx_VE3_base_step`、キーストーン modulo で閉）**:
run-step（`LastStep N < J₁`）で IH `VE3goal (Pred N)` を成長輸送して `VE3goal N` を得る。
Lean にはキーストーン `kyx_terminal_slice_keystone` 未移植ゆえ名前付き残差。 -/
def VE3RunStep_bd : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 → VE3goal (Pred N) → VE3goal N

/-- **PIN 残差（Isabelle `PIN`）**: BASE ホストで `Trans N` は外側 principal 形
`D_{N₁,0}(F +_B D_{N₁,j₀'} a)`（`F = bpHeadT (Trans (front slice))`）に pinned。
原文 part(1)（`brN`）。 -/
def PIN_bd : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    ∃ a : BT, Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞) a))

/-- **TSPIN 残差（Isabelle `TSPIN`、base ホスト拡張）**: pinned 形の内部項 `a` は
終切片頭 `bpHeadT (Trans (terminal slice))` に一致（非許容 joint での Mark-surgery
naturality、原文 content.md 3360）。 -/
def TSPIN_bd : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    ∀ a : BT, Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞) a)) →
      a = bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))

/-! ## VE4 の pointwise アセンブル（`PIN_bd` ＋ `TSPIN_bd`、Isabelle
`bfx_VE34_base_run0_modTSPIN` の VE4 部） -/

/-- **VE4 非極小基底脚を `{PIN_bd, TSPIN_bd}` から放出**。VE4 は IH を消費しない
（pointwise）ので run 帰納法不要。pinned 形 `PIN` の外側頭を読み、内部項 `a` を輸送
方程式 `TSPIN` で終切片頭に固定するだけ。 -/
theorem VE4BaseDeep_of_pin_tspin (hPIN : PIN_bd) (hTSPIN : TSPIN_bd) : VE4BaseDeep := by
  intro N reg hbase hdeep
  obtain ⟨a, hform⟩ := hPIN N reg hbase hdeep
  have haeq : a = bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))) :=
    hTSPIN N reg hbase hdeep a hform
  unfold VE4goal
  rw [hform, bpHeadT_Dprin_bd, haeq]

/-! ## VE3 の run-peel 帰納法（Isabelle `bfx_VE34_backpeel_fin3` の VE3 脚） -/

/-- **VE3 非極小基底脚を run-peel 残差三つ組から放出**。`Lng N` 強帰納法。
non-極小基底 `TrMax N + 2 < Lng N` の BASE ホストで:
- `LastStep N = J₁`（run-base）→ `VE3RunBase_bd`（SPLIT0）。
- `LastStep N < J₁`（run-step）→ `RunPeelPreserved_bd` で `Pred N` へ降り、`Pred N` が
  極小基底なら `VE3_minbase_vb`、そうでなければ IH で `VE3goal (Pred N)` を得、
  `VE3RunStep_bd` で成長輸送。 -/
theorem VE3BaseDeep_of_residuals
    (hpres : RunPeelPreserved_bd) (hRB : VE3RunBase_bd) (hRS : VE3RunStep_bd) :
    VE3BaseDeep := by
  intro N reg hbase hdeep
  generalize hn : Lng N = n
  induction n using Nat.strong_induction_on generalizing N with
  | _ n ih =>
    subst hn
    have hBrne : Br N ≠ [] := reg.1.1.2.2
    have hLSle : LastStep N ≤ (Br N).length - 1 := by
      have := LastStep_lt_Lng_Br N hBrne; omega
    by_cases hrun : LastStep N = (Br N).length - 1
    · exact hRB N reg hbase hdeep hrun
    · have hrunstep : LastStep N < (Br N).length - 1 := by omega
      obtain ⟨hregP, hbaseP⟩ := hpres N reg hbase hdeep hrunstep
      have hL1 : 1 < Lng N := by omega
      have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
      have hM : TPS N := RTPS_TPS N reg.1.1.1
      have htrne : TrMax N ≠ Lng N - 1 := by omega
      have hTrP : TrMax (Pred N) = TrMax N := TrMax_Pred_nontrunk N hM hL1 htrne
      have hVE3P : VE3goal (Pred N) := by
        by_cases hpmin : Lng (Pred N) = TrMax (Pred N) + 2
        · exact VE3_minbase_vb (Pred N) hregP hbaseP hpmin
        · have hpdeep : TrMax (Pred N) + 2 < Lng (Pred N) := by
            rw [hLP, hTrP] at hpmin ⊢; omega
          exact ih (Lng (Pred N)) (by omega) (Pred N) hregP hbaseP hpdeep rfl
      exact hRS N reg hbase hdeep hrunstep hVE3P

/-! ## キャップストーン: `condIIIVts` フィールドを run-peel 残差束 modulo で供給

`8.2-condIIIV-ve34-base` の `condIIIVterminalSlice_of_deepBase`
（`{VE3BaseDeep, VE3Step, VE4BaseDeep, VE4Step}` から `CondIIIVterminalSlice`）に、
本ファイルで放出した `VE3BaseDeep`/`VE4BaseDeep` を差し込む。 -/

/-- **run-peel 残差版キャップストーン**: `condIIIVts` フィールドを
`{RunPeelPreserved_bd, VE3RunBase_bd, VE3RunStep_bd, PIN_bd, TSPIN_bd, VE3Step, VE4Step}`
から供給する。 -/
theorem condIIIVterminalSlice_of_runpeel
    (hpres : RunPeelPreserved_bd) (hRB : VE3RunBase_bd) (hRS : VE3RunStep_bd)
    (hPIN : PIN_bd) (hTSPIN : TSPIN_bd) (hV3s : VE3Step) (hV4s : VE4Step) :
    CondIIIVterminalSlice :=
  condIIIVterminalSlice_of_deepBase
    (VE3BaseDeep_of_residuals hpres hRB hRS) hV3s
    (VE4BaseDeep_of_pin_tspin hPIN hTSPIN) hV4s

/-! ## 転記の数値検証（非極小基底 run-step 領域の量化域が非空）

witness `W = (0,0)(1,1)(2,2)(2,0)(2,0)` は `VE34Reg4` に属し、BASE `VEj1p = 4 = Lng - 1`
かつ非極小基底 `Lng = 5 > 4 = TrMax + 2`（`TrMax = 2`）。さらに最終枝は 2 本
（`J₁ = 1`）で `LastStep = 0 < J₁` ＝ **run-step** ホスト（run-peel 帰納法の降下枝を
実際に発火する）。 -/
#guard decide (VE34Reg4 [(0,0),(1,1),(2,2),(2,0),(2,0)] ∧
  VEj1p [(0,0),(1,1),(2,2),(2,0),(2,0)] = Lng [(0,0),(1,1),(2,2),(2,0),(2,0)] - 1 ∧
  TrMax [(0,0),(1,1),(2,2),(2,0),(2,0)] + 2 < Lng [(0,0),(1,1),(2,2),(2,0),(2,0)] ∧
  LastStep [(0,0),(1,1),(2,2),(2,0),(2,0)] < (Br [(0,0),(1,1),(2,2),(2,0),(2,0)]).length - 1)
  = true

#print axioms baseDeepGeom_bd
#print axioms VE4BaseDeep_of_pin_tspin
#print axioms VE3BaseDeep_of_residuals
#print axioms condIIIVterminalSlice_of_runpeel

end PSS

import «8».«8.2-condIIIV-ve-values»

/-!
# §8.2 条件(II)/(IV) VE34 run-peel — **統一 back-peel 強帰納法**（BASE 保存を撤去）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、`j₁ - TrMax M` に関する数学的帰納法（run-peel、原文 L3360 の
  「subexpr-component-`Pred`」補題）。

- **背景（Wave AM の反証）**: `8.2-condIIIV-runsqueeze` は、`8.2-condIIIV-ve-next` の
  run-peel 帰納法 `VE3BaseDeepD_of_residuals` が仮定する **BASE 保存**
  （`RunPeelPreservedD_vc2`＝run-step BASE ホストの `Pred` がまた BASE に留まる）が
  **偽**であることを機械証明した（反例 `(0,0)(1,1)(2,2)(2,0)(3,1)(2,0)`: 前枝が
  長さ 2 ゆえ剥がすと STEP になる）。よって「BASE 脚だけを後ろ剥がしで閉じる」設計は
  破綻している。正しい設計は Isabelle `bfx_VE34_backpeel_fin3`
  （`isabelle/layerB/pss_wip.thy:105252`）の **統一強帰納法** で、IH は
  「体制＋`fin` を満たす**全ホスト**」上で量化され、`Pred N` が BASE でも STEP でも
  区別なく `VE34goal (Pred N)` を与える（BASE 保存を一切要求しない）。

- **本ファイルの成果**: Isabelle `bfx_VE34_backpeel_fin3` を Lean へ移植する。
  補正体制 `VE34Reg4D`（＝Isabelle `vg7x_reg4`）と `fin` 述語 `FinRun_up`
  （＝Isabelle の run-branch 有限集合、Lean では枝添字上界ゆえ**常に真**）上で、
  `Lng` 強帰納法を**三分岐**に割る:
  1. **BASE-run-base**（`VEj1p N = Lng N - 1` ∧ 非極小基底 ∧ `LastStep N = J₁`）→ 残差
     `BaseRunBase_up`。
  2. **BASE-run-step**（`VEj1p N = Lng N - 1` ∧ 非極小基底 ∧ `LastStep N < J₁`）→ IH を
     `Pred N` に適用（BASE 保存**不要**）し残差 `BaseRunStep_up`。
  3. **STEP**（`VEj1p N < Lng N - 1`）→ IH を `Pred N` に適用し残差 `Step_up`。
  極小基底（`Lng N = TrMax N + 2`）は `VE3_minbase_vb`/`VE4_minbase_vb` で**内部討伐**
  （残差不要）。三分岐は Isabelle の `BASE0f`/`BASERf`/`STEPf` スロットに一対一で対応。

- **regime/fin 持続の扱い**（Isabelle は内部で `bfx_RPERS_base`/`bfx_fin_Pred_base`/
  `vg7x_RPERS`/`bpx_fin_Pred` を使用）:
  - `fin` 持続 `bfx_fin_Pred_base_up` は**証明済み**（`FinRun_up` は常に真）。
  - run-step BASE の regime 持続は、descending 半 `dtps_Pred_of_runstep_vc2`
    （`8.2-condIIIV-ve-continue`、**証明済み**）＋ guard/joint 半 `RunStepGuardJoint_up`
    （残差、**BASE 保存を含まない**＝反証済み連言を落とした正しい形）から
    `regD_Pred_runstep_up` で `VE34Reg4D (Pred N)` を組む。
  - STEP の regime 持続 `StepRegPres_up`（＝Isabelle `vg7x_RPERS`）は残差。

- **スロットの葉残差への分解**（本ファイルで供給、`VE34goal ⟺ VE3goal ∧ VE4goal`
  ＝`VE34goal_iff` 経由）:
  - `BaseRunBase_up ⟸ {PIN_bd, TSPIN_bd, VE3RunBase_bd}`（VE4 は pinned 形＋輸送、
    VE3 は run-base 分割＝Isabelle `bfx_VE34_base_run0_modTSPIN`）。
  - `BaseRunStep_up ⟸ {PIN_bd, TSPIN_bd, VE3RunStep_bd}`（VE4 同、VE3 は IH の
    `VE3goal (Pred N)` を成長輸送＝Isabelle `bfx_VE34_base_step_modTSPIN`）。
    さらに `VE3RunStep_bd ⟸ {TerminalSliceReady_vv, FrontPredBaseTransport_vv,
    TermPredBaseTransport_vv}`（`8.2-condIIIV-ve-values` の `VE3RunStep_of_reductions_vv`、
    keystone modulo）。
  - `Step_up ⟸ {VE3Step, VE4Step}`（STEP 領域の pointwise 残差、IH 非消費）。

- **キャップストーン**: `VE34goal_on_reg4D_of_residuals_up` は、補正体制 `VE34Reg4D` の
  **全ホスト**で `VE34goal` を、honest 残差束
  `{RunStepGuardJoint_up, StepRegPres_up, PIN_bd, TSPIN_bd, VE3RunBase_bd, VE3RunStep_bd,
  VE3Step, VE4Step}` から供給する。`VE34goal_on_reg4D_of_geom_residuals_up` は `VE3RunStep_bd`
  を ve-values の幾何 3 Props へ差し替えた版。

- ⚠️ **未達（次のブリック）**: 露出した honest 残差
  `{RunStepGuardJoint_up（guard/joint 持続）, StepRegPres_up（STEP regime 持続＝
  `vg7x_RPERS`）, PIN_bd, TSPIN_bd, VE3RunBase_bd, TerminalSliceReady_vv,
  FrontPredBaseTransport_vv, TermPredBaseTransport_vv, VE3Step, VE4Step}` の値証明本体、
  および `CondIIIVterminalSlice` フィールド（DTPS ホスト）から補正体制 `VE34Reg4D` 残差へ
  降ろす field-level 再配線（`VE34Reg4D ⊆ VE34Reg4` で向きが逆＝中間補題群の descending
  体制での引き直しが要る）は本ファイルの射程外。naive prefix-append／BASE 保存帰納は
  反証済（禁止）。

- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植、または名前付き Prop 骨格）。
  本ファイルが撤去した「BASE 保存」は Lean 移植側の欠陥であって原文の誤りではない。

- 依存 module: `8.2-condIIIV-ve-values`（`VE34Reg4D`/`VE34Reg4D_VE34Reg4`/
  `dtps_Pred_of_runstep_vc2`/`PIN_bd`/`TSPIN_bd`/`VE3RunBase_bd`/`VE3RunStep_bd`/
  `VE4BaseDeep_of_pin_tspin`/`VE3RunStep_of_reductions_vv`/`TerminalSliceReady_vv`/
  `FrontPredBaseTransport_vv`/`TermPredBaseTransport_vv`/`VE3_minbase_vb`/`VE4_minbase_vb`/
  `VE3Step`/`VE4Step`/`VE34goal`/`VE34goal_iff`/`VE3goal`/`VE4goal`/`VE34Reg`/`VE34Reg4`/
  `VEj1p`/`LastStep`/`length_Pred`/`LastStep_lt_Lng_Br`/`DTPS_iff`/`RTPS_TPS`/
  `FirstNodes_TrMax_Joints`/`Br`/`Joints`/`FirstNodes`/`TrMax`/`Pred`/`entry`/`leR`/`le0`/
  `nextR_implies_row0`/`Joints_nextR_FirstNodes` を推移的に）。

- 状態: ⚠️ 部分（sorry 0、rc=0）。統一 back-peel 強帰納法 `VE34_backpeel_fin3_up` を
  緑で着地（BASE 保存撤去、極小基底内部討伐、`fin` 持続証明済み、regime 持続の
  descending 半証明済み）。三スロットを葉残差へ分解し、補正体制全ホストでの `VE34goal` を
  honest 残差束 modulo で供給。

- Private suffix: `_up`。
-/

namespace PSS

/-! ## `fin` 述語（Isabelle `finite {J. J < Lng(Br N) ∧ head 共有 ∧ guard}`）

Isabelle の run-branch 有限集合。Lean では枝添字が `J < (Br N).length` に上界されるので
`Set.Iio` の部分集合＝**常に有限**。よって `fin` 述語・その `Pred` 持続はともに無条件で
真だが、Isabelle の帰納法構造（`bfx_VE34_backpeel_fin3` が `fin` を threading する）を
忠実に写すため名前付きで保持する。 -/

/-- **`fin` 述語**（Isabelle `bfx_VE34_backpeel_fin3` の `finite {...}` 仮定）。 -/
def FinRun_up (N : PS) : Prop :=
  {J : ℕ | J < (Br N).length ∧
    entry ((Br N).getD ((Br N).length - 1) []) 0 0 = entry ((Br N).getD J []) 0 0 ∧
    entry ((Br N).getD J []) 1 0 < entry ((Br N).getD J []) 0 0}.Finite

/-- `FinRun_up` は**常に真**（`J < (Br N).length` の内包は `Set.Iio` の部分集合）。 -/
theorem finRun_up_all (N : PS) : FinRun_up N :=
  (Set.finite_Iio (Br N).length).subset (fun _ hJ => hJ.1)

/-- **`fin` 持続の移植**（Isabelle `bfx_fin_Pred_base` 105318／`bpx_fin_Pred`）: 常に真な
`FinRun_up` から自明。BASE-run-step 脚・STEP 脚の両方で使う。 -/
theorem bfx_fin_Pred_base_up (N : PS) (_h : FinRun_up N) : FinRun_up (Pred N) :=
  finRun_up_all (Pred N)

/-! ## 私的補助（suffix `_up`）— 他ファイルで private な補題の再導出 -/

/-- `leR M 0 a b` は両添字を `Lng M` 未満に閉じ込める（`8.2-condIIIV-VE34-reg`
`leR0_bounds_v34` の再掲）。 -/
private theorem leR0_bounds_up (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- 枝の左端は `Lng` 未満（Isabelle `a1_FN_lt`, pss_mechanized 33186、`FN_lt_v34` の再掲）。 -/
private theorem FN_lt_up (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M :=
  (leR0_bounds_up M _ _
    (nextR_implies_row0 M 0 _ _ (Joints_nextR_FirstNodes M J hM hmono hJ)).2).2

/-- 体制 `VE34Reg4` の下で `TrMax N + 2 ≤ Lng N`（`reg4_TrMax_le_vb` の再掲）。
BASE 二分岐 `Lng N = TrMax N + 2` / `TrMax N + 2 < Lng N` に必要。 -/
private theorem reg4_TrMax_le_up (N : PS) (reg : VE34Reg4 N) : TrMax N + 2 ≤ Lng N := by
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _⟩, _, _⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  have hgeom := (FirstNodes_TrMax_Joints N _ hM hmono hJ).2
  have hfnlt := FN_lt_up N _ hM hmono hJ
  omega

/-- 体制の下で `VEj1p N < Lng N`（`VEj1p_lt_v34` の再掲）。 -/
private theorem VEj1p_lt_up (N : PS) (hreg : VE34Reg N) : VEj1p N < Lng N := by
  obtain ⟨hR, hmono, hBrne⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  exact FN_lt_up N _ hM hmono hJ

/-! ## regime 持続の残差（BASE 保存を**含まない**正しい形）

`8.2-condIIIV-ve-continue` の `RunPeelGuardJointBase_vc2` は四連言だったが、その第四連言
`VEj1p (Pred N) = Lng (Pred N) - 1`（＝BASE 保存）は **反証済み**（`8.2-condIIIV-runsqueeze`）。
本ファイルの統一帰納法は BASE 保存を要さないので、guard/joint の三連言だけを残差にする。 -/

/-- **run-step BASE の guard/joint 持続残差**（Isabelle `bfx_gtP_base`＝guard／
`bfx_Joints_Pred_last`＝joint 境界）。**BASE 保存は含まない**。`Pred N` の最終枝左端での
非対角ガードと、最終 joint の非許容境界 `0 < · < TrMax (Pred N)`。 -/
def RunStepGuardJoint_up : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    entry (Pred N) 1 (VEj1p (Pred N)) < entry (Pred N) 0 (VEj1p (Pred N))
    ∧ 0 < (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
    ∧ (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0 < TrMax (Pred N)

/-- **STEP regime 持続残差**（Isabelle `vg7x_RPERS`）: STEP ホスト（`VEj1p N < Lng N - 1`）で
補正体制が `Pred N` へ遺伝する。 -/
def StepRegPres_up : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 → VE34Reg4D (Pred N)

/-- **run-step BASE の regime 持続を組む**: descending 半 `dtps_Pred_of_runstep_vc2`
（証明済み）＋ guard/joint 半 `RunStepGuardJoint_up`（残差）から `VE34Reg4D (Pred N)`。
`RunPeelPreservedD_of_geom_vc2`（ve-continue）の BASE-保存-free 版。 -/
theorem regD_Pred_runstep_up (hRSgj : RunStepGuardJoint_up)
    (N : PS) (regD : VE34Reg4D N) (hbase : VEj1p N = Lng N - 1)
    (hdeep : TrMax N + 2 < Lng N) (hrunstep : LastStep N < (Br N).length - 1) :
    VE34Reg4D (Pred N) := by
  obtain ⟨hDP, hBrPne⟩ := dtps_Pred_of_runstep_vc2 N regD hbase hdeep hrunstep
  obtain ⟨hRP, hmonoP, hdescP⟩ := (DTPS_iff (Pred N)).mp hDP
  obtain ⟨hg, hj0p, hj0l⟩ := hRSgj N regD hbase hdeep hrunstep
  exact ⟨⟨⟨⟨hRP, hmonoP, hBrPne⟩, hg⟩, hj0p, hj0l⟩, hdescP⟩

/-! ## 三スロット残差（Isabelle `BASE0f`／`BASERf`／`STEPf`）

いずれも補正体制 `VE34Reg4D` ＋ `FinRun_up` 上で量化する。deep 版スロット
（run-base／run-step）は非極小基底 `TrMax N + 2 < Lng N` を持つ（極小基底は帰納法内部で
討伐するので）。BASE-run-step／STEP スロットは IH 結果 `VE34goal (Pred N)`（**BASE 限定
ではない**）を消費する。 -/

/-- **BASE-run-base スロット**（Isabelle `BASE0f`）。 -/
def BaseRunBase_up : Prop :=
  ∀ N : PS, VE34Reg4D N → FinRun_up N → VEj1p N = Lng N - 1 →
    TrMax N + 2 < Lng N → LastStep N = (Br N).length - 1 → VE34goal N

/-- **BASE-run-step スロット**（Isabelle `BASERf`）。IH `VE34goal (Pred N)` を消費。 -/
def BaseRunStep_up : Prop :=
  ∀ N : PS, VE34Reg4D N → FinRun_up N → VEj1p N = Lng N - 1 →
    TrMax N + 2 < Lng N → LastStep N < (Br N).length - 1 →
    VE34Reg4D (Pred N) → VE34goal (Pred N) → VE34goal N

/-- **STEP スロット**（Isabelle `STEPf`）。IH `VE34goal (Pred N)` を消費。 -/
def Step_up : Prop :=
  ∀ N : PS, VE34Reg4D N → FinRun_up N → VEj1p N < Lng N - 1 →
    VE34Reg4D (Pred N) → VE34goal (Pred N) → VE34goal N

/-! ## 統一 back-peel 強帰納法（Isabelle `bfx_VE34_backpeel_fin3`, 105252）

`Lng` に関する強帰納法。BASE（`VEj1p N = Lng N - 1`）と STEP（`< Lng N - 1`）に割り、
BASE をさらに極小基底（内部討伐）／deep-run-base（`BASE0f`）／deep-run-step（`BASERf`）に
割る。IH は補正体制＋`fin` の**全ホスト**で量化されるので、`Pred N` が BASE でも STEP でも
`VE34goal (Pred N)` を与える（**BASE 保存を要求しない**のが Wave AM 反証への修正の核心）。 -/
theorem VE34_backpeel_fin3_up
    (hBase0 : BaseRunBase_up) (hBaseR : BaseRunStep_up) (hStep : Step_up)
    (hRSgj : RunStepGuardJoint_up) (hStepReg : StepRegPres_up)
    (M : PS) (hM : VE34Reg4D M) (hfin : FinRun_up M) : VE34goal M := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    subst hn
    have reg4 : VE34Reg4 M := VE34Reg4D_VE34Reg4 M hM
    have regBase : VE34Reg M := reg4.1.1
    have hBrne : Br M ≠ [] := regBase.2.2
    have hj1lt : VEj1p M < Lng M := VEj1p_lt_up M regBase
    by_cases hbase : VEj1p M = Lng M - 1
    · -- BASE 領域（`VEj1p M = Lng M - 1`）
      have hleq : TrMax M + 2 ≤ Lng M := reg4_TrMax_le_up M reg4
      by_cases hmin : Lng M = TrMax M + 2
      · -- 極小基底: 内部討伐（残差不要）
        exact (VE34goal_iff M).mpr
          ⟨VE3_minbase_vb M reg4 hbase hmin, VE4_minbase_vb M reg4 hbase hmin⟩
      · -- deep: run-base / run-step で二分岐
        have hdeep : TrMax M + 2 < Lng M := by omega
        have hLSle : LastStep M ≤ (Br M).length - 1 := by
          have := LastStep_lt_Lng_Br M hBrne; omega
        by_cases hrun : LastStep M = (Br M).length - 1
        · -- run-base スロット
          exact hBase0 M hM hfin hbase hdeep hrun
        · -- run-step: IH を `Pred M` に適用（BASE 保存不要）
          have hrunstep : LastStep M < (Br M).length - 1 := by omega
          have hregP : VE34Reg4D (Pred M) :=
            regD_Pred_runstep_up hRSgj M hM hbase hdeep hrunstep
          have hL1 : 1 < Lng M := by omega
          have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hL1
          have hfinP : FinRun_up (Pred M) := bfx_fin_Pred_base_up M hfin
          have ihP : VE34goal (Pred M) :=
            ih (Lng (Pred M)) (by omega) (Pred M) hregP hfinP rfl
          exact hBaseR M hM hfin hbase hdeep hrunstep hregP ihP
    · -- STEP 領域（`VEj1p M < Lng M - 1`）
      have hlt : VEj1p M < Lng M - 1 := by omega
      have hregP : VE34Reg4D (Pred M) := hStepReg M hM hlt
      have hL1 : 1 < Lng M := by omega
      have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hL1
      have hfinP : FinRun_up (Pred M) := bfx_fin_Pred_base_up M hfin
      have ihP : VE34goal (Pred M) :=
        ih (Lng (Pred M)) (by omega) (Pred M) hregP hfinP rfl
      exact hStep M hM hfin hlt hregP ihP

/-! ## スロットの葉残差への分解（`VE34goal ⟺ VE3goal ∧ VE4goal`＝`VE34goal_iff`）

Isabelle `bfx_VE34_base_run0_modTSPIN`／`bfx_VE34_base_step_modTSPIN`／
`bpx_VE34_step_modTSPIN` の Lean 対応。VE4 は pinned 形＋輸送（`VE4BaseDeep_of_pin_tspin`）、
VE3 は run-base 分割（`VE3RunBase_bd`）／IH 成長輸送（`VE3RunStep_bd`）／STEP pointwise
（`VE3Step`）。 -/

/-- **BASE-run-base スロットを `{PIN_bd, TSPIN_bd, VE3RunBase_bd}` から**。 -/
theorem BaseRunBase_of_leaves_up (hPIN : PIN_bd) (hTSPIN : TSPIN_bd) (hRB : VE3RunBase_bd) :
    BaseRunBase_up := by
  intro N regD _hfin hbase hdeep hrun
  have reg4 : VE34Reg4 N := VE34Reg4D_VE34Reg4 N regD
  have hVE4 : VE4goal N := VE4BaseDeep_of_pin_tspin hPIN hTSPIN N reg4 hbase hdeep
  have hVE3 : VE3goal N := hRB N reg4 hbase hdeep hrun
  exact (VE34goal_iff N).mpr ⟨hVE3, hVE4⟩

/-- **BASE-run-step スロットを `{PIN_bd, TSPIN_bd, VE3RunStep_bd}` から**。IH 結果
`VE34goal (Pred N)` の VE3 成分を成長輸送に流す。 -/
theorem BaseRunStep_of_leaves_up (hPIN : PIN_bd) (hTSPIN : TSPIN_bd) (hRS : VE3RunStep_bd) :
    BaseRunStep_up := by
  intro N regD _hfin hbase hdeep hrunstep _regDP ihP
  have reg4 : VE34Reg4 N := VE34Reg4D_VE34Reg4 N regD
  have hVE4 : VE4goal N := VE4BaseDeep_of_pin_tspin hPIN hTSPIN N reg4 hbase hdeep
  have hVE3P : VE3goal (Pred N) := ((VE34goal_iff (Pred N)).mp ihP).1
  have hVE3 : VE3goal N := hRS N reg4 hbase hdeep hrunstep hVE3P
  exact (VE34goal_iff N).mpr ⟨hVE3, hVE4⟩

/-- **STEP スロットを `{VE3Step, VE4Step}` から**（pointwise、IH 非消費）。 -/
theorem Step_of_legs_up (hV3s : VE3Step) (hV4s : VE4Step) : Step_up := by
  intro N regD _hfin hlt _regDP _ihP
  have reg4 : VE34Reg4 N := VE34Reg4D_VE34Reg4 N regD
  have hVE3 : VE3goal N := hV3s N reg4 hlt
  have hVE4 : VE4goal N := hV4s N reg4 hlt
  exact (VE34goal_iff N).mpr ⟨hVE3, hVE4⟩

/-! ## キャップストーン: 補正体制全ホストでの `VE34goal` を honest 残差束 modulo で供給 -/

/-- **統一 back-peel の end-to-end 還元**: 補正体制 `VE34Reg4D` の全ホストで `VE34goal` を、
honest 残差束
`{RunStepGuardJoint_up, StepRegPres_up, PIN_bd, TSPIN_bd, VE3RunBase_bd, VE3RunStep_bd,
VE3Step, VE4Step}` から供給する（`fin` は `finRun_up_all` で内部供給）。 -/
theorem VE34goal_on_reg4D_of_residuals_up
    (hRSgj : RunStepGuardJoint_up) (hStepReg : StepRegPres_up)
    (hPIN : PIN_bd) (hTSPIN : TSPIN_bd)
    (hRB : VE3RunBase_bd) (hRS : VE3RunStep_bd)
    (hV3s : VE3Step) (hV4s : VE4Step)
    (M : PS) (hM : VE34Reg4D M) : VE34goal M :=
  VE34_backpeel_fin3_up
    (BaseRunBase_of_leaves_up hPIN hTSPIN hRB)
    (BaseRunStep_of_leaves_up hPIN hTSPIN hRS)
    (Step_of_legs_up hV3s hV4s)
    hRSgj hStepReg M hM (finRun_up_all M)

/-- **幾何 3 Props 版キャップストーン**: `VE3RunStep_bd` を ve-values の
`VE3RunStep_of_reductions_vv`（keystone modulo）経由で幾何 3 Props
`{TerminalSliceReady_vv, FrontPredBaseTransport_vv, TermPredBaseTransport_vv}` へ差し替えた版。 -/
theorem VE34goal_on_reg4D_of_geom_residuals_up
    (hRSgj : RunStepGuardJoint_up) (hStepReg : StepRegPres_up)
    (hPIN : PIN_bd) (hTSPIN : TSPIN_bd) (hRB : VE3RunBase_bd)
    (hready : TerminalSliceReady_vv) (hfront : FrontPredBaseTransport_vv)
    (hterm : TermPredBaseTransport_vv)
    (hV3s : VE3Step) (hV4s : VE4Step)
    (M : PS) (hM : VE34Reg4D M) : VE34goal M :=
  VE34goal_on_reg4D_of_residuals_up hRSgj hStepReg hPIN hTSPIN hRB
    (VE3RunStep_of_reductions_vv hready hfront hterm) hV3s hV4s M hM

/-! ## 転記の数値検証（統一帰納法の三分岐が実際に発火するホスト）

- `witUP = (0,0)(1,1)(2,2)(2,0)(2,0)`（ve-continue の `witW_vc2`）は補正体制 `VE34Reg4D` の
  **deep run-step BASE** ホスト（`VEj1p = 4 = Lng - 1`、`TrMax + 2 = 4 < 5`、
  `LastStep = 0 < 1 = Br.length - 1`）＝run-step 脚を発火。かつ `RunStepGuardJoint_up` の
  三連言（guard／joint 正／joint < TrMax）が `Pred witUP` で成立。
- `witCex = (0,0)(1,1)(2,2)(2,0)(3,1)(2,0)`（runsqueeze の反証 `witCexRS`）も同じく
  **deep run-step BASE** の `VE34Reg4D` ホストで、`RunStepGuardJoint_up` の三連言は
  `Pred witCex` で**成立**（`Pred` は `VE34Reg4D` を保つ）が、**BASE 保存は成立しない**
  （`VEj1p (Pred) = 3 ≠ 4 = Lng(Pred)-1`＝前枝が長さ 2 で剥がすと STEP になる）。これが
  「BASE 保存を撤去し IH を全ホストで量化する」統一帰納法が必要な理由の数値裏付け。
- `witMin = (0,0)(1,1)(2,2)(2,0)` は `VE34Reg4` の **極小基底** ホスト
  （`VEj1p = 3 = Lng - 1`、`Lng = 4 = TrMax + 2`）で、`LastStep = 0 = Br.length - 1`
  ＝run-base ＝内部討伐（極小基底 ⟹ run-base の数値裏付け）。 -/

def witUP : PS := [(0,0),(1,1),(2,2),(2,0),(2,0)]
def witCex : PS := [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]
def witMin : PS := [(0,0),(1,1),(2,2),(2,0)]

-- witUP は deep run-step BASE ホスト（run-step 脚を発火）。
#guard decide (VE34Reg4D witUP
  ∧ VEj1p witUP = Lng witUP - 1
  ∧ TrMax witUP + 2 < Lng witUP
  ∧ LastStep witUP < (Br witUP).length - 1) = true

-- `RunStepGuardJoint_up` の三連言が witUP の `Pred` で成立（guard／joint 正／joint < TrMax）。
#guard decide (entry (Pred witUP) 1 (VEj1p (Pred witUP)) < entry (Pred witUP) 0 (VEj1p (Pred witUP))
  ∧ 0 < (Joints (Pred witUP)).getD ((Br (Pred witUP)).length - 1) 0
  ∧ (Joints (Pred witUP)).getD ((Br (Pred witUP)).length - 1) 0 < TrMax (Pred witUP)) = true

-- witCex も deep run-step BASE ホストで、`Pred` は `VE34Reg4D` を保つ（RunStepGuardJoint 成立）…
#guard decide (VE34Reg4D witCex
  ∧ VEj1p witCex = Lng witCex - 1
  ∧ TrMax witCex + 2 < Lng witCex
  ∧ LastStep witCex < (Br witCex).length - 1
  ∧ entry (Pred witCex) 1 (VEj1p (Pred witCex)) < entry (Pred witCex) 0 (VEj1p (Pred witCex))
  ∧ 0 < (Joints (Pred witCex)).getD ((Br (Pred witCex)).length - 1) 0
  ∧ (Joints (Pred witCex)).getD ((Br (Pred witCex)).length - 1) 0 < TrMax (Pred witCex)) = true

-- 🚨 …しかし witCex の `Pred` で **BASE 保存は成立しない**（撤去した設計が誤りである証拠）。
#guard decide (VE34Reg4D (Pred witCex)
  ∧ ¬ (VEj1p (Pred witCex) = Lng (Pred witCex) - 1)) = true

-- witMin は極小基底かつ run-base（`LastStep = Br.length - 1`）＝内部討伐対象。
#guard decide (VE34Reg4 witMin
  ∧ VEj1p witMin = Lng witMin - 1
  ∧ Lng witMin = TrMax witMin + 2
  ∧ LastStep witMin = (Br witMin).length - 1) = true

#print axioms finRun_up_all
#print axioms bfx_fin_Pred_base_up
#print axioms regD_Pred_runstep_up
#print axioms VE34_backpeel_fin3_up
#print axioms BaseRunBase_of_leaves_up
#print axioms BaseRunStep_of_leaves_up
#print axioms Step_of_legs_up
#print axioms VE34goal_on_reg4D_of_residuals_up
#print axioms VE34goal_on_reg4D_of_geom_residuals_up

end PSS

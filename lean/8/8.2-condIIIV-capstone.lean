import «8».«8.2-condIIIV-geometry»
import «8».«8.2-condIIIV-runstep-pin»
import «8».«8.2-condIIIV-tspin-close»
import «8».«8.2-condIIIV-VE34-assembly»

/-!
# §8.2 条件(II)/(IV) VE34 — **最終キャップストーンの再配線**（残差を `TspinAssemblyIH_tc` 一本に）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、`j₁ - TrMax M` に関する数学的帰納法（run-peel / STEP surgery）の**最終配線**。
  本ファイルは Wave AT の配線指示を実施する: 統一 back-peel 強帰納法
  `VE34_backpeel_fin3_up`（`8.2-condIIIV-unified-peel`）の三スロットを、run-step BASE を
  **IH ルートで無条件**に、STEP を IH 持ち込みの単一残差 `TspinAssemblyIH_tc` modulo で
  埋め直し、キャップストーンの露出残差を **`TspinAssemblyIH_tc` ただ 1 本**に絞る。

## 背景（geometry からの改良）

`8.2-condIIIV-geometry` の `ve34_on_reg4D_modulo_gm` は露出残差が **2 本**
`{TransPinRunStepD_pt, TSPINStep_ss}` だった。両者はいずれも点wise には証明不能
（`TransPinRunStepD_pt` は `bgx_VE34_base_step` の isleft-selector が IH の VE4 を本質使用、
`TSPINStep_ss` は `tsx_assembly` の `ihVE4` step が本質使用）。Wave AT/AS は両者を
**IH 持ち込み**版へ再定式化し、消費側スロットが scope に持つ IH `ihP : VE34goal (Pred N)`
で埋めることで無条件化した:

- run-step BASE: `VE4goal_runstep_of_IH_rp`（`8.2-condIIIV-runstep-pin`、IH 保持 pinned
  assembly `transPinRunStepIH_rp` の外側頭読み）が、点wise `VE4BaseDeepD_of_runstep_pt hRS`
  （`TransPinRunStepD_pt` modulo）を **無条件**に置換。
- STEP: `step_up_of_assembly_tc`（`8.2-condIIIV-tspin-close`）が、点wise `TSPINStep_ss` を
  **IH 持ち込みの単一残差 `TspinAssemblyIH_tc`（= Isabelle `tsx_assembly` 104073）modulo**
  に置換。

## 本ファイルの成果（mission (1)–(3)）

1. **`baseRunStep_up_cw : BaseRunStep_up`（無条件、残差ゼロ）**: geometry の
   `baseRunStep_up_gm` の VE4 脚 `VE4BaseDeepD_of_runstep_pt hRS`（`TransPinRunStepD_pt`
   依存）を、IH 保持版 `VE4goal_runstep_of_IH_rp … ihP` に差し替える。スロット
   `BaseRunStep_up` は `ihP : VE34goal (Pred N)` を scope に持つ（Wave AT で確認）。VE3 脚
   `VE3RunStepD_of_reductions_pv`（幾何 2 Props `terminalSliceReadyD_holds`/
   `frontPredBaseTransportD_holds` は討伐済）は不変。
2. **`ve34_on_reg4D_cw : TspinAssemblyIH_tc → ∀ M, VE34Reg4D M → VE34goal M`**: geometry の
   `ve34_on_reg4D_modulo_gm` の組立を、三スロット
   `{baseRunBase_up_gm, baseRunStep_up_cw, step_up_of_assembly_tc hAsm}` ＋ regime 持続
   `{runStepGuardJoint_up_holds, stepRegPres_up_holds}`（reg-pres で討伐済）で組み直す。
   **露出残差は `TspinAssemblyIH_tc` ただ 1 本**（run-step BASE は IH ルートで無条件化）。
3. **BONUS — consumer chain（`CondIIIVterminalSlice` フィールドへの接続）**:
   `ve34goal_on_dtps_cw`（DTPS ホストで `VE34goal`）を経て、§8.2 命題の無条件形
   `CondIIIVterminalSlice`（termination の `condIIIVts` フィールド、`8.3-condII-Boundary-close`）
   を **`TspinAssemblyIH_tc` ＋ VE2 大域残差 `VE2Residual` modulo** で供給する
   （`condIIIVterminalSlice_of_assembly_cw`）。合成が可能な限りを緑で組み、genuine gap を
   `needs` に明示する（下記）。

## consumer chain の genuine gap（`needs` に報告）

`CondIIIVterminalSlice` は VE3/VE4（＝`VE34goal`）に**加えて** VE2（値方程式の一本目
`VE2goal`）を要する。`TspinAssemblyIH_tc` は VE3/VE4 のみを供給するので **VE2 は本ルートの
射程外**であり、`VE2Residual`（Isabelle `vg3x_VE2` 94418 = 純幹閉形式 `crg_slice_value_of_trunk`
＋ `cfbx_reg` 機構、`{VE2TrunkLeg, VE2RegLeg}`）を仮定として残す。もう一つの経路
（`condIIIVterminalSlice_of_VE`）は `VE3All`/`VE4All` を **`VE34Reg4`（descending 抜き）** 上で
要求するが、本ルートの `VE34goal` は **`VE34Reg4D`（descending 込み）** 上でしか出ない
（`VE34Reg4D → VE34Reg4` の field-rewiring は向きが狭→広で逆＝out-of-scope）。本ファイルは
この不整合を DTPS ホスト側（DTPS は descending を含む）で `VE34Reg4D_of_dtps_host` を使い
per-M に迂回するので、gap は **VE2 のみ**に限局する。

- 訂正: なし（討伐済 `_gm`/`_rp`/`_tc`/`_holds`/`_pv` 群の LIVE 合成）。
- 依存 module: `8.2-condIIIV-geometry`（`baseRunBase_up_gm`/`runStepGuardJoint_up_holds`/
  `stepRegPres_up_holds`/`terminalSliceReadyD_holds`/`frontPredBaseTransportD_holds`/
  `VE3RunStepD_of_reductions_pv`/`VE34_backpeel_fin3_up`/`finRun_up_all`/`BaseRunStep_up`/
  `VE34Reg4D`/`VE34goal`/`VE4goal`/`VE3goal`/`VE34goal_iff` 推移）,
  `8.2-condIIIV-runstep-pin`（`VE4goal_runstep_of_IH_rp`）,
  `8.2-condIIIV-tspin-close`（`TspinAssemblyIH_tc`/`step_up_of_assembly_tc`）,
  `8.2-condIIIV-VE34-assembly`（`VE2Residual`/`CondIIIVterminalSlice`、および `VE2goal`/
  `condIIIV_of_VE2_VE34`/`VE34Reg4D_of_dtps_host` を推移的に）。
- 状態: ⚠️ 部分（sorry 0、rc=0、公理 `[propext, Classical.choice, Quot.sound]` のみ）。
  キャップストーン `ve34_on_reg4D_cw` を露出残差 **`TspinAssemblyIH_tc` 一本**で着地。
  consumer chain を `CondIIIVterminalSlice`（`condIIIVts` フィールド）まで、VE2 gap を残して接続。
- Private suffix: `_cw`。
-/

namespace PSS

/-! ## (1) run-step BASE スロットを IH ルートで無条件供給（geometry `baseRunStep_up_gm` の
IH 保持版、`TransPinRunStepD_pt` 依存を落とす） -/

/-- **`baseRunStep_up_cw : BaseRunStep_up`（無条件、残差ゼロ）**: geometry の
`baseRunStep_up_gm (hRS : TransPinRunStepD_pt)` から `hRS` 依存を落とした版。VE4 脚を、
点wise `VE4BaseDeepD_of_runstep_pt hRS`（`TransPinRunStepD_pt` modulo）ではなく、IH 保持
`VE4goal_runstep_of_IH_rp N regD hbase hdeep hrunstep ihP`（`8.2-condIIIV-runstep-pin`）で
供給する。スロット `BaseRunStep_up` は `ihP : VE34goal (Pred N)` を scope に持つ。VE3 脚
`VE3RunStepD_of_reductions_pv`（幾何 2 Props 討伐済）は geometry と同一。 -/
theorem baseRunStep_up_cw : BaseRunStep_up := by
  intro N regD _hfin hbase hdeep hrunstep _regDP ihP
  have hVE4 : VE4goal N := VE4goal_runstep_of_IH_rp N regD hbase hdeep hrunstep ihP
  have hVE3P : VE3goal (Pred N) := ((VE34goal_iff (Pred N)).mp ihP).1
  have hVE3 : VE3goal N :=
    VE3RunStepD_of_reductions_pv terminalSliceReadyD_holds frontPredBaseTransportD_holds
      N regD hbase hdeep hrunstep hVE3P
  exact (VE34goal_iff N).mpr ⟨hVE3, hVE4⟩

/-! ## (2) キャップストーン: 補正体制全ホストでの `VE34goal` を残差 exactly 1 本 modulo で供給

`VE34_backpeel_fin3_up`（統一 back-peel 強帰納法）の三スロット＋regime 持続 2 本を、
LIVE 供給で埋める。**開いている残差は `TspinAssemblyIH_tc`（= Isabelle `tsx_assembly` 104073、
STEP の唯一の深い §7.4 Mark-surgery naturality 頭輸送）ただ 1 本のみ**:
- run-base BASE: `baseRunBase_up_gm`（geometry、census 閉形式 2 本＋HEADEQ0 で討伐済）。
- run-step BASE: `baseRunStep_up_cw`（本ファイル、IH ルートで**無条件**）。
- STEP: `step_up_of_assembly_tc hAsm`（tspin-close、IH 持ち込み残差 `TspinAssemblyIH_tc` modulo）。
- regime 持続: `runStepGuardJoint_up_holds`/`stepRegPres_up_holds`（reg-pres で討伐済）。

🚨 **反証済み `PIN_bd`/`TSPIN_bd`／pointwise `TransPinRunStepD_pt`/`TSPINStep_ss`/`VE3RunBase_bd`
に一切依存しない**——すべて LIVE / IH 保持経路。geometry の 2 残差版
`ve34_on_reg4D_modulo_gm` から `TransPinRunStepD_pt` を消去した改良版。 -/
theorem ve34_on_reg4D_cw (hAsm : TspinAssemblyIH_tc)
    (M : PS) (hM : VE34Reg4D M) : VE34goal M :=
  VE34_backpeel_fin3_up
    baseRunBase_up_gm
    baseRunStep_up_cw
    (step_up_of_assembly_tc hAsm)
    runStepGuardJoint_up_holds
    stepRegPres_up_holds
    M hM (finRun_up_all M)

/-! ## (3) BONUS — consumer chain を `CondIIIVterminalSlice`（`condIIIVts` フィールド）へ

`ve34_on_reg4D_cw` は `VE34Reg4D`（descending 込み）ホストで `VE34goal` を出す。§8.2 命題の
無条件形 `CondIIIVterminalSlice`（`8.3-condII-Boundary-close`、termination の `condIIIVts`
フィールド）は DTPS ホスト上の ∃! で、VE3/VE4（`VE34goal`）に加え VE2（`VE2goal`）を要する。
DTPS ホストでは `VE34Reg4D_of_dtps_host` で補正体制を組めるので `VE34goal` は本ルートで出る。
残る VE2 は本ルート（`TspinAssemblyIH_tc`）の射程外＝`VE2Residual` を仮定に残す（needs）。 -/

/-- **`ve34goal_on_dtps_cw`**: DTPS ホスト＋condII/IV ガードで `VE34goal M` を
`TspinAssemblyIH_tc` から供給する（`VE34Reg4D_of_dtps_host` で補正体制を組み
`ve34_on_reg4D_cw` を適用）。ガードは `VEj1p M = (FirstNodes M).getD ((Br M).length-1) 0`
の定義展開で `FirstNodes` 形と一致する。 -/
theorem ve34goal_on_dtps_cw (hAsm : TspinAssemblyIH_tc)
    (M : PS) (hD : DTPS M) (hBrne : Br M ≠ [])
    (hj0pos : 0 < (Joints M).getD ((Br M).length - 1) 0)
    (hj0lt : (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
    (hguard : entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
            < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)) :
    VE34goal M :=
  ve34_on_reg4D_cw hAsm M (VE34Reg4D_of_dtps_host M hD hBrne hj0pos hj0lt hguard)

/-- **`condIIIVterminalSlice_of_assembly_cw`**（consumer chain の到達点、BONUS）: §8.2 条件(II)/(IV)
終切片命題の無条件形 `CondIIIVterminalSlice`（termination `condIIIVts` フィールド）を、
STEP の単一残差 `TspinAssemblyIH_tc` と VE2 大域残差 `VE2Residual` から供給する。VE3/VE4 は
`ve34goal_on_dtps_cw`（本ファイル、`TspinAssemblyIH_tc` modulo）、VE2 は仮定 `hVE2`、
∃! への組立は `condIIIV_of_VE2_VE34`（`8.2-condIIIV-VE34-entry`、無条件）。

🚨 **genuine gap = VE2**（`VE2Residual`、`TspinAssemblyIH_tc` では供給不能）。 -/
theorem condIIIVterminalSlice_of_assembly_cw
    (hAsm : TspinAssemblyIH_tc) (hVE2 : VE2Residual) : CondIIIVterminalSlice := by
  intro M hMD hBrne hj0pos hj0lt hguard
  have hVE34 : VE34goal M := ve34goal_on_dtps_cw hAsm M hMD hBrne hj0pos hj0lt hguard
  have hVE2M : VE2goal M := hVE2 M hMD hBrne hj0pos hj0lt hguard
  exact condIIIV_of_VE2_VE34 M hMD hBrne hj0pos hj0lt hguard hVE2M hVE34

/-! ## 転記の数値検証（三スロットが実際に発火するホスト） -/

-- 補正体制 STEP 証人（tspin-close の witness `w1_tc`）が STEP スロットを発火。
#guard decide (VE34Reg4D [(0,0),(1,1),(2,2),(2,1),(3,1)] ∧
  VEj1p [(0,0),(1,1),(2,2),(2,1),(3,1)] < Lng [(0,0),(1,1),(2,2),(2,1),(3,1)] - 1) = true

-- 補正体制 run-step BASE 証人（runstep-pin の witness `witRS`）が run-step BASE スロットを発火。
#guard decide (VE34Reg4D [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]
  ∧ VEj1p [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] = Lng [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] - 1
  ∧ LastStep [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] < (Br [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]).length - 1)
  = true

-- run-base BASE 証人（geometry/bgx-reduction の hostBG）が run-base BASE スロットを発火。
#guard decide (VE34Reg4D [(0,0),(1,1),(2,2),(2,2),(2,0)]
  ∧ VEj1p [(0,0),(1,1),(2,2),(2,2),(2,0)] = Lng [(0,0),(1,1),(2,2),(2,2),(2,0)] - 1
  ∧ LastStep [(0,0),(1,1),(2,2),(2,2),(2,0)] = (Br [(0,0),(1,1),(2,2),(2,2),(2,0)]).length - 1) = true

#print axioms baseRunStep_up_cw
#print axioms ve34_on_reg4D_cw
#print axioms ve34goal_on_dtps_cw
#print axioms condIIIVterminalSlice_of_assembly_cw

end PSS

import «8».«8.2-condIIIV-VE34-step»
import «8».«8.3-condII-Boundary-close»

/-!
# §8.2 条件(II)/(IV) VE34 後ろ剥がしキャンペーンの締め（`hqx_condIIIV_of_DT` 接続）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）。
  原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べる部分（「subexpr-component-`Pred`」
  補題、L3360）の**キャップストーン**。入口 (`8.2-condIIIV-VE34-entry`)／体制機械
  (`-reg`、訂正版体制＋無条件 RPERS＋BASE 幾何)／STEP 再組立 (`-step`) の上に、
  後ろ剥がし組立と `hqx_condIIIV_of_DT` 接続を載せ、§8.2 条件(II)/(IV) 終切片命題の
  **無条件形** `CondIIIVterminalSlice`（`8.3-condII-Boundary-close`、termination の
  `condIIIVts` フィールドそのもの）を、最小の名前付き残差集合 modulo で供給する。
- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植、または名前付き Prop 骨格）。
- Isabelle（`isabelle/layerB/pss_wip.thy`）: STEP `8.2-condIIIV-VE34-step`
  （`vs2x_VE34_step`／`vs2x_VE34_step_of_residuals`）の次のブリック。本ファイルは
  `hqx_condIIIV_of_DT` (108722) と `vg7x_condIIIV_of_DT` (97539) の骨格を移植する:
  - `vg7x_condIIIV_of_DT` (97539) → `condIIIVterminalSlice_of_residuals`
    （後ろ剥がし組立版。残差 `{VE34Base4, VE3Residual, VE4Residual, VE2Residual}`）
  - `hqx_condIIIV_of_DT` (108722) → 最小残差版 `condIIIVterminalSlice_of_VE`
    （BASE を pointwise に吸収し、原文の三本の値方程式 `{VE2Residual, VE3All, VE4All}`
    ちょうどに還元する。`vg2x_VE34` は reg4 ホスト上で POINTWISE に成立するので
    ――python/ve34_deep2.py 5/5 whole――BASE の後ろ剥がしは原文の証明経路であって
    主張には不要）
- **BASE/VE の実体は本ファイルの射程外**: 三残差 `{VE2Residual, VE3All, VE4All}` は
  それぞれ Isabelle の `vg3x_VE2` (94418, 無条件)／`hqx_VE34_of_DT` (108701) の VE3/VE4
  で discharge されるが、その中身は condII/IV 専用の VE chain（≈15590 行、`bfx_`/`bgx_`/
  `hqx_` の base 塔含む）で、いずれも §7.4 共有 scb-context 頭シフト readback surgery
  （`m_7_4_Trans_Mark_Pred`＋`m_7_4_Mark_Trans_repr`）に帰着する深い readback 残差
  （`TSPIN`/`PIN`/`SPLIT0`/`HEADEQ` 族）に底を突く。本ファイルはその**組立と接続**のみを
  緑で供給し、深い値部分を三つの名前付き Prop に露出する。
- 依存 module: `8.2-condIIIV-VE34-step`（`VE34Reg4`/`VE34goal`/`VE3goal`/`VE4goal`/
  `VE3Residual`/`VE4Residual`/`VE34Base4`/`VE34goal_iff`/`condIIIV_ts_of_residuals`/
  `VEj1p`/`DTPS`/`Br`/`Joints`/`FirstNodes`/`TrMax`/`entry`/`LastStep`/`Trans`/`seg`/
  `bpHeadT`/`addBT`/`Dprin`/`BZero` を推移的に）、`8.3-condII-Boundary-close`
  （残差フィールド定義 `CondIIIVterminalSlice`＝termination の `condIIIVts`）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。`condIIIVts` フィールドを最小三残差
  `{VE2Residual, VE3All, VE4All}` modulo で供給。三残差の実体（VE 値方程式＝
  §7.4 頭シフト readback surgery）は本ファイルの射程外＝次のブリック。
-/

namespace PSS

/-! ## VE2 の大域残差（Isabelle `vg3x_VE2`, 94418）

STEP `8.2-condIIIV-VE34-step` の `condIIIV_ts_of_residuals` は各 `M` ごとに
`VE2goal M` を仮定に持つ。それを、条件(II)/(IV) のガード付き `DT_PS` ホスト上で
普遍的に量化した大域残差 `VE2Residual` にまとめる（`CondIIIVterminalSlice` の
仮定にちょうど揃えた形）。 -/

/-- **Isabelle `vg3x_VE2`（layerB 94418、無条件）の大域残差形**: 条件(II)/(IV) の
ガード付き `DT_PS` ホストで、値方程式の一本目 `VE2goal`（接頭辞頭の一致）が成立する。 -/
def VE2Residual : Prop :=
  ∀ M : PS, DTPS M → Br M ≠ [] →
    0 < (Joints M).getD ((Br M).length - 1) 0 →
    (Joints M).getD ((Br M).length - 1) 0 < TrMax M →
    entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
      < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) →
    VE2goal M

/-! ## 後ろ剥がし組立版キャップストーン（Isabelle `vg7x_condIIIV_of_DT`, 97539） -/

/-- **Isabelle `vg7x_condIIIV_of_DT` (layerB 97539) の逐語形**: §8.2 条件(II)/(IV)
終切片命題の無条件形 `CondIIIVterminalSlice`（＝termination の `condIIIVts` フィールド）を、
後ろ剥がしの三残差 `{VE34Base4, VE3Residual, VE4Residual}`（RPERS は `-reg` で無条件討伐済み、
STEP は `-step` の `VE34Step4_of_residuals` 経由）と VE2 大域残差 `VE2Residual` から供給する。

STEP `8.2-condIIIV-VE34-step` の `condIIIV_ts_of_residuals`（各 `M` の `VE2goal M` 版）に、
`VE2Residual` を差し込むだけ。 -/
theorem condIIIVterminalSlice_of_residuals
    (hBase : VE34Base4) (hVE3 : VE3Residual) (hVE4 : VE4Residual) (hVE2 : VE2Residual) :
    CondIIIVterminalSlice := by
  intro M hMD hBrne hj0pos hj0lt hguard
  exact condIIIV_ts_of_residuals hBase hVE3 hVE4 M hMD hBrne hj0pos hj0lt hguard
    (hVE2 M hMD hBrne hj0pos hj0lt hguard)

/-! ## 最小残差版キャップストーン（Isabelle `hqx_condIIIV_of_DT`, 108722）

STEP `8.2-condIIIV-VE34-step` が記録するとおり、`vg2x_VE34`（＝`VE34goal`）は reg4 ホスト上で
**POINTWISE** に成立する（python/ve34_deep2.py 5/5 whole）――後ろ剥がし帰納法は原文の
証明経路であって主張には不要。したがって成長成分 VE3（`VE3goal`）と頭シフト成分 VE4
（`VE4goal`）を、`j₁'` の場合分けなしに reg4 ホスト全域で量化した二残差
`VE3All`/`VE4All` に還元できる。これにより BASE の後ろ剥がしスロット `VE34Base4` は
不要になり、`condIIIVts` フィールドは**原文の三本の値方程式** `{VE2Residual, VE3All, VE4All}`
**ちょうど**に還元される。 -/

/-- **VE3 の pointwise 残差**: 訂正版体制 reg4 ホスト全域（BASE `j₁' = j₁` と
STEP `j₁' < j₁` の双方）で成長成分 `VE3goal` が成立する。Isabelle `hqx_VE34_of_DT`
(108701) の VE3 側。 -/
def VE3All : Prop :=
  ∀ Q : PS, VE34Reg4 Q → VE3goal Q

/-- **VE4 の pointwise 残差**: 訂正版体制 reg4 ホスト全域で頭シフト成分 `VE4goal` が
成立する。Isabelle `hqx_VE34_of_DT` (108701) の VE4 側。 -/
def VE4All : Prop :=
  ∀ Q : PS, VE34Reg4 Q → VE4goal Q

/-- BASE スロット `VE34Base4`（`8.2-condIIIV-VE34-reg`）を pointwise 二残差から放出する。
`VE34goal_iff`（`8.2-condIIIV-VE34-step`）の `∃`-シャッフルで `VE3goal ∧ VE4goal` を束ねる
だけ。BASE 条件 `VEj1p N = Lng N - 1` は消費しない（pointwise なので不要）。 -/
theorem VE34Base4_of_all (h3 : VE3All) (h4 : VE4All) : VE34Base4 :=
  fun N reg _ => (VE34goal_iff N).mpr ⟨h3 N reg, h4 N reg⟩

/-- STEP 残差 `VE3Residual`（`8.2-condIIIV-VE34-step`）を pointwise 残差 `VE3All` から
放出する（STEP 制約 `VEj1p Q < Lng Q - 1` を落とす）。 -/
theorem VE3Residual_of_all (h3 : VE3All) : VE3Residual :=
  fun Q reg _ => h3 Q reg

/-- STEP 残差 `VE4Residual`（`8.2-condIIIV-VE34-step`）を pointwise 残差 `VE4All` から
放出する。 -/
theorem VE4Residual_of_all (h4 : VE4All) : VE4Residual :=
  fun Q reg _ => h4 Q reg

/-- **Isabelle `hqx_condIIIV_of_DT` (layerB 108722) の逐語形**: §8.2 条件(II)/(IV)
終切片命題の無条件形 `CondIIIVterminalSlice`（＝termination の `condIIIVts` フィールド）を、
**原文の三本の値方程式** `{VE2Residual, VE3All, VE4All}` **ちょうど**から供給する。

BASE スロットは `VE34Base4_of_all` で pointwise に吸収し、STEP スロットは
`VE3Residual_of_all`/`VE4Residual_of_all` で供給する（RPERS は `-reg` で無条件討伐済み）。
残る三残差はいずれも VE 値方程式そのもの＝§7.4 頭シフト readback surgery に帰着する
深い残差で、本ファイルの射程外。 -/
theorem condIIIVterminalSlice_of_VE (hVE2 : VE2Residual) (h3 : VE3All) (h4 : VE4All) :
    CondIIIVterminalSlice :=
  condIIIVterminalSlice_of_residuals (VE34Base4_of_all h3 h4)
    (VE3Residual_of_all h3) (VE4Residual_of_all h4) hVE2

/-! ## 下流への接続（condII 停止性フィールド `CondII_masterCF`）

三残差 `{VE2Residual, VE3All, VE4All}` を閉じれば、`8.3-condII-Boundary-close` の
`condII_masterCF_of_condIIIV` を通じて condII 停止性エンジン `CondII_masterCF`
（`8.3-TransCondII-engine`）が落ちる。本ファイルが termination の `condIIIVts` フィールドを
最小残差へ絞ったことの下流インパクトを明示する。 -/

/-- 三つの VE 値方程式残差から condII 停止性フィールド `CondII_masterCF` を供給する。
`condIIIVterminalSlice_of_VE` で `CondIIIVterminalSlice` を作り、`8.3-condII-Boundary-close`
の `condII_masterCF_of_condIIIV` へ渡す。 -/
theorem condII_masterCF_of_VE (hVE2 : VE2Residual) (h3 : VE3All) (h4 : VE4All) :
    CondII_masterCF :=
  condII_masterCF_of_condIIIV (condIIIVterminalSlice_of_VE hVE2 h3 h4)

/-! ## 転記の数値検証（残差 regime の非空性）

三残差はいずれも「条件(II)/(IV) のガード付き reg4 ホスト」上で量化されている。その
regime が空虚でないことを、`8.2-condIIIV-VE34-reg` と同じ witness
`M = (0,0)(1,1)(2,2)(2,0)` で確認する（VE34Reg4 に属し、かつ DT_PS のガード条件
`0 < j₀' < TrMax`・非対角ガードを満たす）。 -/

-- witness は訂正版体制 reg4 に属する（`VE3All`/`VE4All` の量化域が非空）。
#guard decide (VE34Reg4 [(0,0),(1,1),(2,2),(2,0)]) = true
-- witness は DT_PS のガード regime に属する（`VE2Residual`/`CondIIIVterminalSlice` の
-- 量化域が非空）。
#guard decide (DTPS [(0,0),(1,1),(2,2),(2,0)] ∧ Br [(0,0),(1,1),(2,2),(2,0)] ≠ []) = true

#print axioms condIIIVterminalSlice_of_residuals
#print axioms VE34Base4_of_all
#print axioms VE3Residual_of_all
#print axioms VE4Residual_of_all
#print axioms condIIIVterminalSlice_of_VE
#print axioms condII_masterCF_of_VE

end PSS

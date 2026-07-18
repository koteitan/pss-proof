import «8».«8.2-condIIIV-VE34-assembly»

/-!
# §8.2 条件(II)/(IV) VE34 キャップストーンの残差を体制別に尖鋭化する

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分
  （「subexpr-component-`Pred`」補題、L3360）。キャップストーン
  `8.2-condIIIV-VE34-assembly` は `condIIIVts` フィールド（`CondIIIVterminalSlice`）を
  **三つの値方程式残差** `{VE2Residual, VE3All, VE4All}` ちょうどに還元した。本ファイルは
  その三残差を、Isabelle の後ろ剥がし証明構造そのものに沿って**六つの体制別残差**へ
  分解する（各残差は Isabelle の別々の surgery ブロックが閉じる対象）。分解の接着はすべて
  無条件（緑）であり、深い readback 部分は名前付き Prop に露出する。
- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植、または名前付き Prop 骨格）。
- Isabelle（`isabelle/layerB/pss_wip.thy`、prefix `vg2x_`/`vg3x_`/`vg4x_`/`bfx_`/`bgx_`/
  `hqx_`、92559–108722、約 15.6k 行）の証明構造:
  - **VE2**: `vg3x_VE2` (94418) は `LastStep M = 0`（純幹接頭辞）で場合分けし、
    純幹側は幹の閉形式 `crg_slice_value_of_trunk` (91399, `vg2x_VE2_trunk`)、非幹側は
    `cfbx_reg` 機構 (`vg2x_VE2_reg` 93037, `vgx_VE2_of_reg`) で閉じる。本ファイルは
    その `LastStep` 場合分けを移植し、VE2 を `{VE2TrunkLeg, VE2RegLeg}` に分ける。
  - **VE3/VE4**: 後ろ剥がし帰納法 (`vg4x_VE34_backpeel` 95133) は最終列が現最終枝の中に
    ある基底 (`VEj1p N = Lng N - 1`、BASE) と、新しい枝を開く帰納枝 (`VEj1p N < Lng N - 1`、
    STEP) に分かれる。BASE の実体は `bfx_*` (104483–105477)／`hqx_*` (108411–108722)、
    STEP の実体は `vg2x_`/`bpx_` の連鎖で、いずれも §7.4 共有 scb-context 頭シフト
    readback surgery (`m_7_4_Trans_Mark_Pred`＋`m_7_4_Mark_Trans_repr`) に帰着する
    深い残差（`TSPIN`/`PIN`/`SPLIT0`/`HEADEQ` 族）に底を突く。本ファイルはその**体制分割**
    （BASE/STEP）を移植し、VE3 を `{VE3Base, VE3Step}`、VE4 を `{VE4Base, VE4Step}` に分ける。
- 分解の意義: キャップストーンの三残差 `{VE2Residual, VE3All, VE4All}` を、Isabelle の
  それぞれ独立した surgery 対象へ 1:1 対応する**六残差**
  `{VE2TrunkLeg, VE2RegLeg, VE3Base, VE3Step, VE4Base, VE4Step}` に絞る。各残差の量化域
  （体制ガード）は Isabelle の対応ブロックのそれと逐語一致する。分解の接着（`_of_legs`）は
  すべて無条件で緑。
- 依存 module: `8.2-condIIIV-VE34-assembly`（`VE2Residual`/`VE3All`/`VE4All`/`VE34Reg4`/
  `VEj1p`/`VE2goal`/`VE3goal`/`VE4goal`/`CondIIIVterminalSlice`/`CondII_masterCF`/
  `condIIIVterminalSlice_of_VE`/`condII_masterCF_of_VE` と `DTPS`/`Br`/`Joints`/
  `FirstNodes`/`LastStep`/`TrMax`/`entry`/`Lng` を推移的に）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。三残差 → 六残差の無条件（緑）分解を供給。六残差の実体
  （VE2 の幹閉形式／`cfbx_reg`、VE3/VE4 の BASE `bfx_`/`hqx_` 頭シフト readback surgery、
  STEP `vg2x_`/`bpx_` surgery）は本ファイルの射程外＝次のブリック。
-/

namespace PSS

/-! ## 私的補助（suffix `_v24`）

体制からの `VEj1p N < Lng N` 境界（`8.2-condIIIV-VE34-entry` の `VEj1p_lt_v34`、
`8.2-condIIIV-VE34-reg` の `VEj1p_lt_vr` の双子）。BASE `VEj1p N = Lng N - 1` と
STEP `VEj1p N < Lng N - 1` の二分岐に必要。 -/

/-- `leR M 0 a b` は両添字を `Lng M` 未満に閉じ込める。入口 `leR0_bounds_v34` の再掲。 -/
private theorem leR0_bounds_v24 (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- 枝の左端は `Lng` 未満（Isabelle `a1_FN_lt`, pss_mechanized 33186）。
入口 `FN_lt_v34` の再掲。 -/
private theorem FN_lt_v24 (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M :=
  (leR0_bounds_v24 M _ _
    (nextR_implies_row0 M 0 _ _ (Joints_nextR_FirstNodes M J hM hmono hJ)).2).2

/-- 体制の下で `VEj1p N < Lng N`（入口 `VEj1p_lt_v34` の `VE34Reg4` 版）。 -/
private theorem VEj1p_lt_v24 (N : PS) (hreg : VE34Reg4 N) : VEj1p N < Lng N := by
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _⟩, _, _⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  exact FN_lt_v24 N _ hM hmono hJ

/-! ## VE3/VE4 の体制別残差（BASE / STEP）

後ろ剥がし帰納法 `vg4x_VE34_backpeel` (95133) は `VEj1p N = Lng N - 1`（BASE、最終列が
現最終枝の中）と `VEj1p N < Lng N - 1`（STEP、新しい枝を開く帰納枝）に分かれる。
両体制で異なる surgery が要る（BASE=`bfx_`/`hqx_`、STEP=`vg2x_`/`bpx_`）ので、
pointwise 残差 `VE3All`/`VE4All` を体制別に二分割する。 -/

/-- **VE3 BASE 残差**（`VEj1p Q = Lng Q - 1`）。Isabelle `hqx_VE34_of_DT` (108701) /
`bfx_*` (104483–105477) の VE3 側の量化域。 -/
def VE3Base : Prop :=
  ∀ Q : PS, VE34Reg4 Q → VEj1p Q = Lng Q - 1 → VE3goal Q

/-- **VE3 STEP 残差**（`VEj1p Q < Lng Q - 1`）。Isabelle STEP surgery `vg2x_`/`bpx_` の
VE3 側の量化域。 -/
def VE3Step : Prop :=
  ∀ Q : PS, VE34Reg4 Q → VEj1p Q < Lng Q - 1 → VE3goal Q

/-- **VE4 BASE 残差**（`VEj1p Q = Lng Q - 1`）。Isabelle `hqx_VE34_of_DT` (108701) /
`bfx_*` の VE4 側の量化域。 -/
def VE4Base : Prop :=
  ∀ Q : PS, VE34Reg4 Q → VEj1p Q = Lng Q - 1 → VE4goal Q

/-- **VE4 STEP 残差**（`VEj1p Q < Lng Q - 1`）。Isabelle STEP surgery の VE4 側の量化域。 -/
def VE4Step : Prop :=
  ∀ Q : PS, VE34Reg4 Q → VEj1p Q < Lng Q - 1 → VE4goal Q

/-- pointwise 残差 `VE3All`（`8.2-condIIIV-VE34-assembly`）を体制別二残差
`{VE3Base, VE3Step}` から放出する。体制ガード `VEj1p Q < Lng Q`（`VEj1p_lt_v24`）で
`VEj1p Q = Lng Q - 1` を二分岐する。 -/
theorem VE3All_of_legs (hBase : VE3Base) (hStep : VE3Step) : VE3All := by
  intro Q reg
  have hlt : VEj1p Q < Lng Q := VEj1p_lt_v24 Q reg
  by_cases hb : VEj1p Q = Lng Q - 1
  · exact hBase Q reg hb
  · exact hStep Q reg (by omega)

/-- pointwise 残差 `VE4All`（`8.2-condIIIV-VE34-assembly`）を体制別二残差
`{VE4Base, VE4Step}` から放出する。 -/
theorem VE4All_of_legs (hBase : VE4Base) (hStep : VE4Step) : VE4All := by
  intro Q reg
  have hlt : VEj1p Q < Lng Q := VEj1p_lt_v24 Q reg
  by_cases hb : VEj1p Q = Lng Q - 1
  · exact hBase Q reg hb
  · exact hStep Q reg (by omega)

/-! ## VE2 の `LastStep` 別残差（純幹接頭辞 / 非幹）

Isabelle `vg3x_VE2` (94418) は `LastStep M = 0`（純幹接頭辞、`N = seg M 0 (TrMax M)` が
対角幹で終切片値が幹閉形式 `crg_slice_value_of_trunk` で固定）と `0 < LastStep M`
（非幹、`cfbx_reg` 機構）に分かれる。両者で異なる surgery が要るので `VE2Residual` を
`LastStep` で二分割する。 -/

/-- **VE2 純幹残差**（`LastStep M = 0`）。Isabelle `vg2x_VE2_trunk` (93069) の量化域。
純幹接頭辞では終切片値は幹の閉形式で固定される。 -/
def VE2TrunkLeg : Prop :=
  ∀ M : PS, DTPS M → Br M ≠ [] →
    0 < (Joints M).getD ((Br M).length - 1) 0 →
    (Joints M).getD ((Br M).length - 1) 0 < TrMax M →
    entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
      < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) →
    LastStep M = 0 →
    VE2goal M

/-- **VE2 非幹残差**（`0 < LastStep M`）。Isabelle `vg2x_VE2_reg` (93037) の量化域。
非幹の場合は `cfbx_reg`（後ろ剥がし体制）機構で終切片値が固定される。 -/
def VE2RegLeg : Prop :=
  ∀ M : PS, DTPS M → Br M ≠ [] →
    0 < (Joints M).getD ((Br M).length - 1) 0 →
    (Joints M).getD ((Br M).length - 1) 0 < TrMax M →
    entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
      < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) →
    0 < LastStep M →
    VE2goal M

/-- **Isabelle `vg3x_VE2` (94418) の場合分け構造の逐語移植**: `VE2Residual`
（`8.2-condIIIV-VE34-assembly`）を `LastStep M = 0` で二分割し、`{VE2TrunkLeg, VE2RegLeg}`
から放出する。 -/
theorem VE2Residual_of_legs (hTrunk : VE2TrunkLeg) (hReg : VE2RegLeg) : VE2Residual := by
  intro M hMD hBrne hj0pos hj0lt hguard
  by_cases hLS : LastStep M = 0
  · exact hTrunk M hMD hBrne hj0pos hj0lt hguard hLS
  · exact hReg M hMD hBrne hj0pos hj0lt hguard (Nat.pos_of_ne_zero hLS)

/-! ## 六残差版キャップストーン

キャップストーン `8.2-condIIIV-VE34-assembly` の `condIIIVterminalSlice_of_VE`
（三残差版）に、本ファイルの三つの `_of_legs` を差し込む。これで `condIIIVts` フィールドの
無条件形 `CondIIIVterminalSlice` が**六つの体制別残差**
`{VE2TrunkLeg, VE2RegLeg, VE3Base, VE3Step, VE4Base, VE4Step}` ちょうどに還元される。 -/
theorem condIIIVterminalSlice_of_deep6
    (hV2t : VE2TrunkLeg) (hV2r : VE2RegLeg)
    (hV3b : VE3Base) (hV3s : VE3Step)
    (hV4b : VE4Base) (hV4s : VE4Step) :
    CondIIIVterminalSlice :=
  condIIIVterminalSlice_of_VE
    (VE2Residual_of_legs hV2t hV2r)
    (VE3All_of_legs hV3b hV3s)
    (VE4All_of_legs hV4b hV4s)

/-- 六残差から condII 停止性フィールド `CondII_masterCF`（`8.3-TransCondII-engine`）を供給する。
`8.2-condIIIV-VE34-assembly` の `condII_masterCF_of_VE` へ橋渡しする。 -/
theorem condII_masterCF_of_deep6
    (hV2t : VE2TrunkLeg) (hV2r : VE2RegLeg)
    (hV3b : VE3Base) (hV3s : VE3Step)
    (hV4b : VE4Base) (hV4s : VE4Step) :
    CondII_masterCF :=
  condII_masterCF_of_VE
    (VE2Residual_of_legs hV2t hV2r)
    (VE3All_of_legs hV3b hV3s)
    (VE4All_of_legs hV4b hV4s)

/-! ## 転記の数値検証（体制別残差の量化域が非空）

BASE/STEP の witness を `decide` で照合する。BASE witness `M = (0,0)(1,1)(2,2)(2,0)`
（`8.2-condIIIV-VE34-reg` の `witness_c24`）は `VE34Reg4` に属し、最終枝の左端
`VEj1p = 3 = Lng - 1` なので BASE 体制。STEP witness は最終枝が長さ ≥ 2 のもの。 -/

-- BASE witness: VE34Reg4 に属し VEj1p = Lng - 1（`VE3Base`/`VE4Base` の量化域が非空）。
#guard decide (VE34Reg4 [(0,0),(1,1),(2,2),(2,0)] ∧
  VEj1p [(0,0),(1,1),(2,2),(2,0)] = Lng [(0,0),(1,1),(2,2),(2,0)] - 1) = true
-- VE2 の量化域（DT_PS ホスト）が非空。
#guard decide (DTPS [(0,0),(1,1),(2,2),(2,0)] ∧ Br [(0,0),(1,1),(2,2),(2,0)] ≠ []) = true

#print axioms VE3All_of_legs
#print axioms VE4All_of_legs
#print axioms VE2Residual_of_legs
#print axioms condIIIVterminalSlice_of_deep6
#print axioms condII_masterCF_of_deep6

end PSS

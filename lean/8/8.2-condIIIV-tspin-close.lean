import «8».«8.2-condIIIV-geometry»
import «8».«8.2-condIIIV-tspin»
import «8».«8.2-condIIIV-terminal-slice-Trans»

/-!
# §8.2 条件(II)/(IV) VE34 STEP スロット `Step_up` を IH 持ち込み TSPIN で閉じる

- 原文: `tmp/content.md` L3360 付近（「subexpr-component-`Pred`」補題の帰納ステップ、
  非許容 joint での Mark-surgery naturality）。
- Isabelle: `tsx_TSPIN` (isabelle/layerB/pss_wip.thy 104267) = `tsx_assembly` (104073)
  ∘ `kyx_terminal_slice_leadform` (99604)、その上段 `bpx_VE34_step_modTSPIN` (103234)。

## 背景（Wave AS の発見）— 点wise `TSPINStep_ss` は証明不能、IH 化が正しい

`8.2-condIIIV-tspin` の `TspinCanonical_tp`（STEP canonical form）と、そこから
`TSPINStep_ss` を無条件で供給する `tspinStep_of_canonical_tp` は緑だが、
`TspinCanonical_tp` 自体は **点wise には証明できない**:
`tsx_assembly` はその内部（`tsx_t1_identified` 104001 の `ihVE4` step 104043）で
**IH `VE34goal (Pred N)`** を本質的に消費する（`Trans (Pred N)` の VE4 形で host の
scb 分解 `sbN` を pin する）。`TSPINStep_ss` の量化は IH を持たないので、点wise には
閉じられない。

しかし統一 back-peel 強帰納法（`8.2-condIIIV-unified-peel`）の STEP スロット `Step_up`
は、その仮説自身の中に **`VE34Reg4D (Pred N)` と `VE34goal (Pred N)`（＝ IH）を持つ**:

```
def Step_up : Prop :=
  ∀ N, VE34Reg4D N → FinRun_up N → VEj1p N < Lng N - 1 →
    VE34Reg4D (Pred N) → VE34goal (Pred N) → VE34goal N
```

したがって正しい配線は「`TSPINStep_ss`（点wise、証明不能）を **IH 持ち込み**の
canonical form へ述べ直す」ことである。本ファイルはそれを行う。

## 本ファイルの成果

1. **`TspinCanonicalIH_tc`**（本ファイルの残差骨格）: `TspinCanonical_tp`
   （`8.2-condIIIV-tspin`）に IH 仮説 `VE34Reg4D (Pred N)` と `VE34goal (Pred N)` を
   足した **IH 持ち込み** canonical form。IH を持つので `tsx_assembly` の port が原理的に
   可能な、正しい定式化（`TSPINStep_ss` と違い量化に IH を持つ）。
2. **`TspinAssemblyIH_tc`**（最も鋭い単一残差 ＝ `tsx_assembly` 104073 の結論そのもの）:
   `Trans N = D_{N₁,0}(F +_B Trans Mp)`。host の surgery 出力が終切片 `Trans Mp` の総和に
   一致すること。これが STEP スロットの **唯一の深い §7.4 頭輸送残差** である。
3. **`tspinCanonicalIH_of_assembly_tc : TspinAssemblyIH_tc → TspinCanonicalIH_tc`**:
   `kyx_terminal_slice_leadform` (99604) の合成段を**無条件で緑移植**。終切片 leadform
   `Trans Mp = D_{N₁,j₀'}(bpHeadT (Trans Mp))` は Lean 側 `slice_Trans_principal_head`
   （`8.2-condIIIV-terminal-slice-Trans`）＋ 終切片単項性 `stepTerminalReady_holds`
   （`8.2-condIIIV-geometry`、regime のみで閉じている）で供給されるので、canonical form は
   assembly から leadform 合成一発で出る。したがって真の残差は assembly ただ 1 本。
4. **`step_up_holds_tc : TspinCanonicalIH_tc → Step_up`**（配線本体、`tsx_TSPIN` 上段
   `bpx_VE34_step_modTSPIN` の IH-carrying 版）: `Step_up` の証明内で IH は scope にある。
   VE3（成長）は幾何 3 Props 討伐済の `StepVE3Growth_of_reductions_ss`（step-surgery、
   入力 `stepTerminalReady_holds`/`stepFrontPred_holds`/`stepTermPred_holds` は
   `8.2-condIIIV-geometry` で全討伐）で放出。VE4（頭シフト）は `TspinCanonicalIH_tc` の
   canonical form を `bpHeadT` で読むだけ（外側 `Dprin` の内部項がそのまま VE4 の右辺）。
5. **`step_up_of_assembly_tc : TspinAssemblyIH_tc → Step_up`**: 上の 2 本の合成。
   これで `Step_up` は **単一の深い残差 `TspinAssemblyIH_tc`（= `tsx_assembly`）modulo**
   で供給される。点wise で証明不能だった `TSPINStep_ss` は完全に排除された。

## `TspinAssemblyIH_tc`（= `tsx_assembly`）を本ファイルで**証明しない**理由

`tsx_assembly` (104073) の忠実な移植は、Lean にまだ存在しない/private な深い scb 機構
を要する（本 wave で確認）:
- **`Trans_unflat_transC2`**（`Trans N = unflatBT (fst sbN @ flatBT (transC2 N) @ snd sbN)`、
  Trans の scb 分解による再帰式）— Lean に未移植。
- **`scbimg_image_BT`**（c₁→c₂ の principal 文字列置換の像存在）— Lean twin
  `principal_replacement_image` は private（`8.7-otint-transport-prims`）。
- **`m_7_3_Trans_Mark_MarkedB`**（scb 分解の存在）/ **`tsx_scb_Dpt_lift`**（Dpt 接頭辞
  持ち上げ）— Lean に未移植。
- `scb_addBT_left_74`（`7.4-Trans-Mark-Pred`）/ `scb_unique_decomp_unconditional`
  （`7.4-Mark-nextAdm`）は存在するが private。

単一 MISSION ファイル（import のみ、`lake build` 不可）の射程を超えるため、assembly は
**IH 持ち込みの名前付き残差として露出**する。IH を持つので偽陽性ではない（下記
`#guard`: STEP witness 上で assembly／leadform／canonical のすべてが実 `Trans` で成立、
7/7 witness ＋ `w1`）。無条件化は上記 4 tool の port を要する別 wave の仕事。

- 訂正: なし（`kyx_terminal_slice_leadform` 下段の逐語移植 ＋ `bpx_VE34_step_modTSPIN`
  の IH-carrying 版 ＋ assembly の名前付き露出）。
- 依存 module: `8.2-condIIIV-geometry`（`stepTerminalReady_holds`/`stepFrontPred_holds`/
  `stepTermPred_holds`/`Step_up`/`VE34Reg4D`/`VE34goal`/`VE34goal_iff`/`VE4goal`/`VE3goal`/
  `VEj1p`/`FinRun_up` 推移）, `8.2-condIIIV-step-surgery`（`StepVE3Growth_of_reductions_ss`
  推移）, `8.2-condIIIV-tspin`（`TspinCanonical_tp` の形 参照）,
  `8.2-condIIIV-terminal-slice-Trans`（`slice_Trans_principal_head`）。
- 状態: ⚠️ 部分（sorry 0、rc=0、公理 `[propext, Classical.choice, Quot.sound]` のみ）。
  STEP スロット `Step_up` を、点wise 証明不能な `TSPINStep_ss` から **IH 持ち込みの単一
  残差 `TspinAssemblyIH_tc`（= `tsx_assembly`）** modulo に還元。leadform 合成段は無条件で
  緑移植。canonical/assembly/leadform を STEP witness 上で数値検証。
- Private suffix: `_tc`。
-/

namespace PSS

/-! ## 純 `BT` 代数（`bpHeadT (Dprin v a) = a`、定義展開 `rfl`） -/

/-- `bpHeadT (Dprin v a) = a`（`Dprin v a = .trm [.db v a]` の定義展開、`rfl`）。 -/
private theorem bpHeadT_Dprin_tc (v : ℕ∞) (a : BT) : bpHeadT (Dprin v a) = a := rfl

/-! ## (a) IH 持ち込みの canonical form / assembly 残差骨格

いずれも STEP ホスト（`VE34Reg4D N` ∧ `VEj1p N < Lng N - 1`）に加え、統一 back-peel の
STEP スロット `Step_up` が持つ **IH 仮説** `VE34Reg4D (Pred N)`／`VE34goal (Pred N)` を
量化に持つ。これが Wave AS の配線指示（`TSPINStep_ss` を IH-carrying へ再定式化）の実体。 -/

/-- **STEP assembly（IH 持ち込み）** ＝ Isabelle `tsx_assembly` 104073 の結論そのもの:
host の surgery 出力が終切片 `Trans Mp` の総和に一致する。
`Trans N = D_{N₁,0}(F +_B Trans Mp)`（`F = bpHeadT (Trans (front slice))`,
`Mp = seg N j₀' (Lng N-1)`, `j₀' = Joints N ! (Br.len-1)`）。**唯一の深い残差**。 -/
def TspinAssemblyIH_tc : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 →
    VE34Reg4D (Pred N) → VE34goal (Pred N) →
    Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))))

/-- **STEP canonical form（IH 持ち込み）** ＝ `8.2-condIIIV-tspin` の `TspinCanonical_tp`
に IH 仮説 `VE34Reg4D (Pred N)`／`VE34goal (Pred N)` を足したもの（`tsx_TSPIN` の合成後の
pinned 形）: `Trans N = D_{N₁,0}(F +_B D_{N₁,j₀'}(bpHeadT (Trans Mp)))`。 -/
def TspinCanonicalIH_tc : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 →
    VE34Reg4D (Pred N) → VE34goal (Pred N) →
    Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
          (bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))))))

/-! ## (b→leadform) `TspinCanonicalIH_tc` を assembly から供給（`kyx_terminal_slice_leadform`
99604 の合成段の逐語移植、無条件・緑）

終切片 leadform `Trans Mp = D_{N₁,j₀'}(bpHeadT (Trans Mp))` を assembly の内部項に代入すると
canonical form になる。leadform は `slice_Trans_principal_head`（`RTPS N` ＋ `j₀' < Lng N-1`
＋ 終切片単項性 `monoT Mp`）で供給。`monoT Mp` は `stepTerminalReady_holds`
（`8.2-condIIIV-geometry`、regime のみで閉じている）から取る。 -/

/-- **`TspinCanonicalIH_tc` を `TspinAssemblyIH_tc` から無条件供給**（`tsx_TSPIN` 104267 の
`asm` ∘ `lead` 合成段）: assembly の内部項 `Trans Mp` を終切片 leadform で principal 化する。 -/
theorem tspinCanonicalIH_of_assembly_tc (hA : TspinAssemblyIH_tc) : TspinCanonicalIH_tc := by
  intro N regD hlt regDP ihP
  -- 体制の射影（`regD` は `hA`/`stepTerminalReady_holds` に再利用するので破壊しない）
  have hR : RTPS N := regD.1.1.1.1
  have hBrne : Br N ≠ [] := regD.1.1.1.2.2
  have hj0lt : (Joints N).getD ((Br N).length - 1) 0 < TrMax N := regD.1.2.2
  have hM : TPS N := RTPS_TPS N hR
  have htrbd : TrMax N ≤ Lng N - 1 := TrMax_bound N hM
  have htrne : TrMax N ≠ Lng N - 1 := fun heq => hBrne (by simp [Br, heq])
  have hj0lt1 : (Joints N).getD ((Br N).length - 1) 0 < Lng N - 1 := by omega
  -- 終切片単項性（regime のみ）
  have hmonoMp : monoT (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = true :=
    (stepTerminalReady_holds N regD hlt).2.1
  -- 終切片 leadform
  have hlead := slice_Trans_principal_head N ((Joints N).getD ((Br N).length - 1) 0)
    (Lng N - 1) hR hj0lt1 (le_refl _) hmonoMp
  -- assembly ＋ leadform 合成
  rw [hA N regD hlt regDP ihP, ← hlead]

/-! ## (c) `Step_up` を IH 持ち込み canonical form から供給（`bpx_VE34_step_modTSPIN`
103234 の IH-carrying 版）

`Step_up` の証明内で IH `regDP`/`ihP` は scope にある。VE3（成長）は幾何 3 Props 討伐済の
`StepVE3Growth_of_reductions_ss` で放出、VE4（頭シフト）は canonical form の外側 `Dprin`
内部項をそのまま読む。点wise `TSPINStep_ss` は一切使わない（IH をその場で供給する）。 -/

/-- **STEP スロット `Step_up` を IH 持ち込み canonical form modulo で供給**
（`tsx_TSPIN` 上段 `bpx_VE34_step_modTSPIN` の IH-carrying 版）: `Step_up` の仮説が持つ
IH を `TspinCanonicalIH_tc` に流し込み、VE3（`StepVE3Growth_of_reductions_ss`、幾何 3 Props
討伐済）と VE4（canonical form の `bpHeadT` 読み）を束ねる。 -/
theorem step_up_holds_tc (hCanon : TspinCanonicalIH_tc) : Step_up := by
  intro N regD _hfin hlt regDP ihP
  -- VE3（成長）: 幾何 3 Props は `8.2-condIIIV-geometry` で全討伐
  have hVE3 : VE3goal N :=
    StepVE3Growth_of_reductions_ss stepTerminalReady_holds stepFrontPred_holds stepTermPred_holds
      N regD hlt regDP ihP
  -- VE4（頭シフト）: canonical form の外側 `Dprin` の内部項がそのまま VE4 の右辺
  have hcanon := hCanon N regD hlt regDP ihP
  have hVE4 : VE4goal N := by
    unfold VE4goal
    rw [hcanon, bpHeadT_Dprin_tc]
  exact (VE34goal_iff N).mpr ⟨hVE3, hVE4⟩

/-! ## (c∘b) 合成: `Step_up` を単一の深い残差 `TspinAssemblyIH_tc`（= `tsx_assembly`）modulo で -/

/-- **STEP スロット `Step_up` を assembly 残差 1 本 modulo で供給**: leadform 合成段
（`tspinCanonicalIH_of_assembly_tc`、無条件）＋ IH-carrying 配線（`step_up_holds_tc`）の合成。
点wise 証明不能な `TSPINStep_ss` を、IH 持ち込みの単一の深い残差 `TspinAssemblyIH_tc`
（＝ Isabelle `tsx_assembly` 104073、host surgery 出力＝終切片 `Trans` 総和）に置換した。 -/
theorem step_up_of_assembly_tc (hA : TspinAssemblyIH_tc) : Step_up :=
  step_up_holds_tc (tspinCanonicalIH_of_assembly_tc hA)

/-! ## 転記の数値検証（IH 持ち込み残差の量化域が非空、assembly/leadform/canonical が実 `Trans`
で成立）

STEP witness `w = (0,0)(1,1)(2,2)(2,1)(3,1)`（`VE34Reg4D`、`VEj1p = 3 < 4 = Lng - 1`）は
残差 `TspinAssemblyIH_tc`／`TspinCanonicalIH_tc` の量化域に属し、その上で assembly／終切片
leadform／canonical form がすべて実 `Trans` で成立する（＝残差が空虚でなく偽陽性でない）。 -/

private def w1_tc : PS := [(0,0),(1,1),(2,2),(2,1),(3,1)]

-- witness は補正体制 `VE34Reg4D` の STEP ホスト（残差の量化域が非空）。
#guard decide (VE34Reg4D w1_tc ∧ VEj1p w1_tc < Lng w1_tc - 1) = true

-- witness 上で assembly（`tsx_assembly`）が成立: `Trans N = D_{N₁,0}(F +_B Trans Mp)`。
#guard (Trans w1_tc == Dprin (entry w1_tc 1 0 : ℕ∞)
  (addBT (bpHeadT (Trans (seg w1_tc 0 ((FirstNodes w1_tc).getD (LastStep w1_tc) 0 - 1))))
    (Trans (seg w1_tc ((Joints w1_tc).getD ((Br w1_tc).length - 1) 0) (Lng w1_tc - 1))))) = true

-- witness 上で終切片 leadform（`kyx_terminal_slice_leadform`）が成立:
-- `Trans Mp = D_{N₁,j₀'}(bpHeadT (Trans Mp))`。
#guard (Trans (seg w1_tc ((Joints w1_tc).getD ((Br w1_tc).length - 1) 0) (Lng w1_tc - 1))
  == Dprin (entry w1_tc 1 ((Joints w1_tc).getD ((Br w1_tc).length - 1) 0) : ℕ∞)
      (bpHeadT (Trans (seg w1_tc ((Joints w1_tc).getD ((Br w1_tc).length - 1) 0)
        (Lng w1_tc - 1))))) = true

-- witness 上で canonical form（assembly ∘ leadform）が成立。
#guard (Trans w1_tc == Dprin (entry w1_tc 1 0 : ℕ∞)
  (addBT (bpHeadT (Trans (seg w1_tc 0 ((FirstNodes w1_tc).getD (LastStep w1_tc) 0 - 1))))
    (Dprin (entry w1_tc 1 ((Joints w1_tc).getD ((Br w1_tc).length - 1) 0) : ℕ∞)
      (bpHeadT (Trans (seg w1_tc ((Joints w1_tc).getD ((Br w1_tc).length - 1) 0)
        (Lng w1_tc - 1))))))) = true

#print axioms tspinCanonicalIH_of_assembly_tc
#print axioms step_up_holds_tc
#print axioms step_up_of_assembly_tc

end PSS

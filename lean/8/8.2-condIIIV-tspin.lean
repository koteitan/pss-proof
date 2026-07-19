import «8».«8.2-condIIIV-step-surgery»

/-!
# §8.2 条件(II)/(IV) VE34 STEP スロットの `TSPINStep_ss`（Isabelle `tsx_TSPIN`/`tsx_assembly`）

- 原文: `tmp/content.md` L3360 付近（「subexpr-component-`Pred`」補題の帰納ステップ、
  非許容 joint での Mark-surgery naturality）。
- 対象: `8.2-condIIIV-step-surgery` が STEP スロットの唯一の深い残差として露出した
  `TSPINStep_ss`（Isabelle `tsx_TSPIN` 104267）:

  > `∀ N, VE34Reg4D N → VEj1p N < Lng N - 1 → ∀ a,`
  > `Trans N = D_{N₁,0}(F +_B D_{N₁,j₀'} a) → a = bpHeadT (Trans Mp)`

  ここで `F = bpHeadT (Trans (front slice))`, `j₀' = Joints N ! (Br.len-1)`,
  `Mp = seg N j₀' (Lng N-1)`（終切片）。

## Isabelle の証明構造（`tsx_TSPIN` 104267）

`tsx_TSPIN` は 2 段で閉じる:
  1. **`tsx_assembly` (104073)**: `Trans N = D_{N₁,0}(F +_B Trans Mp)`
     （**canonical form**、host の surgery 出力が終切片の `Trans` 総和に一致）。
  2. **`kyx_terminal_slice_leadform` (99604)**: `Trans Mp = D_{N₁,j₀'}(bpHeadT (Trans Mp))`
     （終切片 leadform）。
  1+2 を合成すると **canonical form**（本ファイルの `TspinCanonical_tp`）:
     `Trans N = D_{N₁,0}(F +_B D_{N₁,j₀'}(bpHeadT (Trans Mp)))`
  が得られ、仮定形 `Trans N = D_{N₁,0}(F +_B D_{N₁,j₀'} a)` と外側 `Dpt` ／末尾 principal
  で照合して `a = bpHeadT (Trans Mp)` を結論する（`vg6x_addBT_split_lastD`）。

## 本ファイルの内容（`tsx_TSPIN` の下段＝合成と照合の逐語移植）

- **`TspinCanonical_tp`**: 上記 canonical form を名前付き Prop として露出する。これは
  `tsx_assembly`（深い §7.4 頭輸送）と leadform を**合成した唯一の残差**であり、STEP
  スロットの深部そのもの。数値検証で真であることを確認済み（下記 `#guard`、STEP witness
  7/7＋`w1`）。
- **`tspinStep_of_canonical_tp : TspinCanonical_tp → TSPINStep_ss`**: `tsx_TSPIN` の下段
  （合成後の照合）を**純 `BT` 代数**（外側 `Dprin` 単射＋末尾 principal 分割）で逐語移植。
  これで `TSPINStep_ss` は単一の等式残差 `TspinCanonical_tp` へ**無条件で還元**される。

## `TspinCanonical_tp` を本ファイルで**証明しない**理由（残差として露出する根拠）

- **`tsx_assembly` は IH `vg2x_VE34 (Pred N)` を要する**: `tsx_assembly` は
  `tsx_t1_identified` (104001) 経由で `Trans (Pred N) = D_{N₁,0}(F +_B Trans (Pred Mp))`
  という **`Pred N` の VE4 形（IH）** を使って host の scb 分解 `sbN` を pin する
  （104043 `ihVE4 ... using ihP`）。ところが `TSPINStep_ss` の量化は IH を**持たない**
  （`VE34Reg4D N` と STEP 条件のみ）。IH は back-peel 強帰納の STEP スロットで供給される
  もので、pointwise には可用でない（§8.2 の campaign 全体がまさにこれを証明する対象）。
- **leadform 側は `monoT (Mp)` を要する**: `slice_Trans_principal_head`
  （`8.2-condIIIV-terminal-slice-Trans`）で leadform を出すには `monoT (seg N j₀' (Lng N-1))`
  が要るが、これは `StepTerminalReady_ss`（`8.2-condIIIV-step-surgery`）の geometry 残差の
  一部で、pointwise には未確立。
- したがって canonical form は「数値的に真だが、その faithful な証明は IH（＋終切片幾何）を
  要する」深部残差であり、**単一の等式 Prop として露出する**のが正しい。無条件化は
  back-peel の IH-carrying context（`Step_up` の `regDP`/`ihP`）から供給されるべきもので、
  最終的な配線替え（`TSPINStep_ss` を IH 付きに述べ直す or STEP context から
  canonical を渡す）は親の仕事。攻略に用いる道具は `tsx_assembly` の移植: `m_7_4_Trans_Mark_Pred`
  ＋`Mark_Trans_repr`＋`Mark_transJm1_eq_transC2`＋`trans_surgery_localized_v6p`
  （共有 scb 対）＋`slice_Trans_principal_head`（leadform）。

- 訂正: なし（Isabelle 側 sorry 0 の `tsx_TSPIN` 下段の逐語移植＋深部の名前付き露出）。
- 依存 module: `8.2-condIIIV-step-surgery`（`TSPINStep_ss`/`VE34Reg4D`/`VEj1p`/`Lng`/`Br`/
  `Joints`/`FirstNodes`/`LastStep`/`entry`/`Trans`/`seg`/`bpHeadT`/`addBT`/`Dprin`）を推移的に。
- 状態: ⚠️ 部分（sorry 0、rc=0）。`TSPINStep_ss` を単一の canonical form 残差
  `TspinCanonical_tp`（= `tsx_assembly` ∘ leadform、IH 依存の深部）へ無条件で還元。数値検証で
  canonical form の真を確認。深部 canonical の証明（IH 供給）は残る。
- Private suffix: `_tp`。
-/

namespace PSS

/-! ## 純 `BT` 代数（`tsx_TSPIN` 下段の照合、`vg6x_addBT_split_lastD` 相当） -/

/-- `bpHeadT (Dprin v a) = a`（`Dprin v a = .trm [.db v a]` の定義展開、`rfl`）。 -/
private theorem bpHeadT_Dprin_tp (v : ℕ∞) (a : BT) : bpHeadT (Dprin v a) = a := rfl

/-- 外側頭が等しい principal の内部項一致（`Dpt` 単射の Lean 版）。 -/
private theorem Dprin_inner_tp {v : ℕ∞} {a b : BT} (h : Dprin v a = Dprin v b) : a = b := by
  have h2 := congrArg bpHeadT h
  simpa only [bpHeadT_Dprin_tp] using h2

/-- **末尾 principal 分割（内部項）**（Isabelle `vg6x_addBT_split_lastD` の左因子共有版）:
接頭辞 `p` と末尾頭指標 `v` を共有する `addBT p (Dprin v a) = addBT p (Dprin v b)` から
末尾内部項 `a = b`。principal リスト連結の `List.getLast?` 単射による。 -/
private theorem addBT_split_last2_tp {p a b : BT} {v : ℕ∞}
    (h : addBT p (Dprin v a) = addBT p (Dprin v b)) : a = b := by
  obtain ⟨ps⟩ := p
  simp only [addBT, Dprin] at h
  have hl : ps ++ [BP.db v a] = ps ++ [BP.db v b] := BT.trm.inj h
  have hg := congrArg List.getLast? hl
  simp only [List.getLast?_concat, Option.some.injEq, BP.db.injEq] at hg
  exact hg.2

/-! ## STEP の canonical form 残差（`tsx_assembly` ∘ `kyx_terminal_slice_leadform`）

`Trans N` の外側 principal 形の内部項が「front 頭 `F` に終切片 `Trans Mp` の leadform
`D_{N₁,j₀'}(bpHeadT (Trans Mp))` を末尾追加した形」であること。これが STEP スロットの
**唯一の深い §7.4 頭輸送残差**（IH 依存、上記ヘッダ参照）。 -/

/-- **STEP canonical form**（Isabelle `tsx_assembly` 104073 ＋ `kyx_terminal_slice_leadform`
99604 の合成）: 補正体制 `VE34Reg4D` の STEP ホスト（`VEj1p N < Lng N - 1`）で `Trans N` は
front 頭 `F` と終切片 leadform の pinned 形をとる。 -/
def TspinCanonical_tp : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 →
    Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
          (bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))))))

/-! ## `TSPINStep_ss` を canonical form から供給（`tsx_TSPIN` 下段の逐語移植）

仮定形 `Trans N = D_{N₁,0}(F +_B D_{N₁,j₀'} a)` と canonical form を照合して内部項 `a` を
終切片頭に固定する。純 `BT` 代数（`Dprin_inner_tp` ＋ `addBT_split_last2_tp`）のみ。 -/

/-- **`TSPINStep_ss` を canonical form 残差 `TspinCanonical_tp` から無条件に供給する**
（Isabelle `tsx_TSPIN` 104267 の下段）: canonical form と仮定形の外側 `Dprin` を剥がし、
接頭辞 `F` と末尾頭指標 `N₁,j₀'` を共有する末尾 principal を分割して `a = bpHeadT (Trans Mp)`。 -/
theorem tspinStep_of_canonical_tp (hC : TspinCanonical_tp) : TSPINStep_ss := by
  intro N regD hlt a hform
  -- canonical form（内部項 = 終切片頭）
  have hc := hC N regD hlt
  -- 仮定形で置換: `D_{N₁,0}(F +_B D_{N₁,j₀'} a) = D_{N₁,0}(F +_B D_{N₁,j₀'}(bpHeadT (Trans Mp)))`
  rw [hform] at hc
  -- 外側 `Dprin` を剥がす
  have h1 := Dprin_inner_tp hc
  -- 接頭辞 `F` 共有の末尾 principal（頭 `N₁,j₀'` 共有）を分割
  exact addBT_split_last2_tp h1

/-! ## 転記の数値検証

STEP witness `w = (0,0)(1,1)(2,2)(2,1)(3,1)`（`VE34Reg4D`、`VEj1p = 3 < 4 = Lng - 1`）は
残差 `TspinCanonical_tp` の量化域に属し、その上で canonical form が実際に成立する
（`tsx_assembly ∘ leadform` が数値的に真＝残差が空虚でない）。 -/

-- witness は補正体制 `VE34Reg4D` の STEP ホスト（残差の量化域が非空）。
#guard decide (VE34Reg4D [(0,0),(1,1),(2,2),(2,1),(3,1)] ∧
  VEj1p [(0,0),(1,1),(2,2),(2,1),(3,1)] < Lng [(0,0),(1,1),(2,2),(2,1),(3,1)] - 1) = true

-- witness 上で canonical form（`tsx_assembly ∘ leadform`）が成立する。
#guard (Trans [(0,0),(1,1),(2,2),(2,1),(3,1)] ==
  Dprin (entry [(0,0),(1,1),(2,2),(2,1),(3,1)] 1 0 : ℕ∞)
    (addBT (bpHeadT (Trans (seg [(0,0),(1,1),(2,2),(2,1),(3,1)] 0
        ((FirstNodes [(0,0),(1,1),(2,2),(2,1),(3,1)]).getD
          (LastStep [(0,0),(1,1),(2,2),(2,1),(3,1)]) 0 - 1))))
      (Dprin (entry [(0,0),(1,1),(2,2),(2,1),(3,1)] 1
          ((Joints [(0,0),(1,1),(2,2),(2,1),(3,1)]).getD
            ((Br [(0,0),(1,1),(2,2),(2,1),(3,1)]).length - 1) 0) : ℕ∞)
        (bpHeadT (Trans (seg [(0,0),(1,1),(2,2),(2,1),(3,1)]
            ((Joints [(0,0),(1,1),(2,2),(2,1),(3,1)]).getD
              ((Br [(0,0),(1,1),(2,2),(2,1),(3,1)]).length - 1) 0)
            (Lng [(0,0),(1,1),(2,2),(2,1),(3,1)] - 1))))))) = true

#print axioms tspinStep_of_canonical_tp

end PSS

import «8».«8.2-condIIIV-ve-next»

/-!
# §8.2 条件(II)/(IV) VE34 run-peel — 🚨 `RunSqueeze_vn` は **偽**（10 個目の反証）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  run-peel（原文 L3360「subexpr-component-`Pred`」）。本ファイルは、`8.2-condIIIV-ve-next`
  が「次のブリック」で討伐対象とした N レベル run-squeeze 残差 `RunSqueeze_vn` を
  **discharge しようとして、代わりにそれが偽であることを機械証明した**。

- **本ファイルの結論（🚨 反証）**: `RunSqueeze_vn` の第三連言（BASE 単一列幾何
  `FirstNodes N ! (Lng(Br N) - 2) = Lng N - 2`、＝**前枝も単項**）は、run-step BASE deep の
  `VE34Reg4D` ホスト一般では成立しない。反例
  `witCexRS = (0,0)(1,1)(2,2)(2,0)(3,1)(2,0)` は `VE34Reg4D`・BASE（`VEj1p = 5 = Lng-1`）・
  deep（`TrMax+2 = 4 < 6`）・run-step（`LastStep = 0 < 1 = Br.length-1`）を全て満たすが、
  その **前枝（`Br` の末尾から 2 番目）は長さ 2**（`(Br witCexRS).map Lng = [2, 1]`）ゆえ
  `FirstNodes witCexRS ! 0 = 3 ≠ 4 = Lng - 2`。連言 (a)（run 前枝ガード）と (b)（JEQ）は
  witCexRS で成立するので、破れているのは (c) のみ（全て Lean `decide` で確認）。

- **なぜ (c)＝BASE 保存は偽か（根本原因）**: (c) は下流ブリッジ
  `RunPeelGuardJointBase_of_squeeze_vn`（ve-next）で `VEj1p (Pred N) = Lng (Pred N) - 1`
  すなわち「`Pred` が BASE に留まる」を導くためだけに使われている。しかし BASE で単項なのは
  **最終枝のみ**であり、前枝が長さ 2 以上のとき、最終枝を剥がした `Pred N` の新しい最終枝
  （旧・前枝）は左端が `Lng - 3 = Lng(Pred N) - 2` にあり、`Pred N` は **STEP ホスト**に
  なる（BASE ではない）。反例 witCexRS で `VEj1p (Pred witCexRS) = 3 ≠ 4 = Lng(Pred)-1`。
  よって `8.2-condIIIV-ve-continue` の補正 run-peel 持続 `RunPeelPreservedD_vc2`
  （＝`VE34Reg4D (Pred N) ∧ VEj1p (Pred N) = Lng (Pred N) - 1`）も **偽**（同反例で機械証明）。

- **Isabelle 版との対応（設計の食い違い）**: Isabelle の run-peel back-peel
  `bfx_VE34_backpeel_fin3`（`isabelle/layerB/pss_wip.thy:105252`）は、BASE-run-step 分岐で
  IH を `Pred M0` に適用する際に **BASE 保存を一切要求しない**（IH の量化域は
  「`vg7x_reg4 ∧ finite` を満たす全ホスト」であり、BASE でも STEP でもよい統一帰納
  ＝`gen : ∀ M0. vg7x_reg4 M0 ∧ finite ... → vg2x_VE34 M0`）。Lean 側の
  `VE3BaseDeepD_of_residuals`（`ve-next`）は `RunPeelPreservedD_vc2` で **BASE 保存を仮定** し
  IH を BASE 限定 `VE3goal (Pred N)` に適用する設計で、この点が Isabelle と食い違って
  いる。**修正の方向**: Lean 側の run-peel 帰納を Isabelle の統一帰納
  （`vg7x_reg4` 全ホスト上、BASE/STEP 分岐を IH の内部で処理）に置き換える。すると
  `RunPeelPreservedD_vc2`／`RunSqueeze_vn`（BASE 保存版）は不要になる。

- 訂正: 本ファイルは Lean 移植側の設計欠陥（run-peel 帰納が BASE 保存を仮定する点）を
  同定した。原文 §8.2 の証明にはこの欠陥はない（原文は run 全体を一度に扱う）。

- 依存 module: `8.2-condIIIV-ve-next`（`RunSqueeze_vn`／`RunPeelPreservedD_vc2`／
  `VE34Reg4D`／`VEj1p`／`LastStep`／`Br`／`Joints`／`FirstNodes`／`TrMax`／`Pred`／`Lng` を
  推移的に）。

- 状態: ⚠️ 反証（sorry 0、rc=0）。`RunSqueeze_vn` と `RunPeelPreservedD_vc2` の両方を、
  単一の機械検証済み反例 `witCexRS` で偽と証明。ミッションが依頼した discharge は
  **不可能**（対象命題が偽）。

- Private suffix: `_rs2`。
-/

namespace PSS

/-! ## 反例 `witCexRS`（run-step BASE deep の `VE34Reg4D` ホストだが前枝が長さ 2）

`witCexRS = (0,0)(1,1)(2,2)(2,0)(3,1)(2,0)`。幹は列 0..2（`TrMax = 2`）、枝は
`P (seg _ 3 5) = [ [(2,0),(3,1)], [(2,0)] ]`（前枝は長さ 2、最終枝は単項）。
`FirstNodes = [3, 5, 6]`、`Joints = [1, 1]`、`VEj1p = FirstNodes ! 1 = 5 = Lng - 1`（BASE）。 -/

def witCexRS : PS := [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]

-- **反例は `RunSqueeze_vn` の量化域（run-step BASE deep の `VE34Reg4D`）に属す**。
#guard decide (VE34Reg4D witCexRS
  ∧ VEj1p witCexRS = Lng witCexRS - 1
  ∧ TrMax witCexRS + 2 < Lng witCexRS
  ∧ LastStep witCexRS < (Br witCexRS).length - 1) = true

-- **連言 (a)（run 前枝ガード）と (b)（JEQ）は反例でも成立**（破れは (c) のみ）。
#guard decide (entry witCexRS 1 (Lng witCexRS - 2) < entry witCexRS 0 (Lng witCexRS - 2)
  ∧ (Joints witCexRS).getD ((Br witCexRS).length - 2) 0
      = (Joints witCexRS).getD ((Br witCexRS).length - 1) 0) = true

-- **🚨 連言 (c)（BASE 単一列幾何）は偽**: 前枝が長さ 2 ゆえ `FirstNodes ! 0 = 3 ≠ 4 = Lng-2`。
#guard decide (¬ ((FirstNodes witCexRS).getD ((Br witCexRS).length - 2) 0 = Lng witCexRS - 2)) = true

-- **枝長は `[2, 1]`**（前枝が長さ 2 ＝ (c) 破れの根本原因）。
#guard decide ((Br witCexRS).map Lng = [2, 1]) = true

-- **`Pred` は BASE に留まらない**（最終枝を剥がすと旧・前枝が新・最終枝＝STEP になる）。
-- `VEj1p (Pred witCexRS) = 3`、`Lng (Pred witCexRS) - 1 = 4`。
#guard decide (VE34Reg4D (Pred witCexRS)
  ∧ ¬ (VEj1p (Pred witCexRS) = Lng (Pred witCexRS) - 1)) = true

/-! ## 反証定理

`RunSqueeze_vn` は BASE 単一列幾何 (c) を全 `VE34Reg4D` run-step BASE deep ホストで要求するが、
`witCexRS` で (c) が破れる。 -/

/-- **🚨 `RunSqueeze_vn`（`8.2-condIIIV-ve-next`）は偽**。反例 `witCexRS`（前枝が長さ 2）で
BASE 単一列幾何の連言 (c) `FirstNodes N ! (Lng(Br N) - 2) = Lng N - 2` が破れる。 -/
theorem RunSqueeze_vn_refuted_rs2 : ¬ RunSqueeze_vn := by
  intro h
  -- 反例は量化域に属す（VE34Reg4D / BASE / deep / run-step は全て `decide` で真）
  have hcex := h witCexRS (by decide) (by decide) (by decide) (by decide)
  -- 連言の第三成分 (c) を取り出し、それが偽であることと矛盾させる
  exact absurd hcex.2.2 (by decide)

/-- **🚨 補正 run-peel 持続 `RunPeelPreservedD_vc2`（`8.2-condIIIV-ve-continue`）も偽**。
同じ反例で `Pred witCexRS` が BASE に留まらない（`VEj1p (Pred) = 3 ≠ 4 = Lng(Pred)-1`）。
これは Lean 側 run-peel 帰納が BASE 保存を仮定する設計欠陥を示す（Isabelle
`bfx_VE34_backpeel_fin3` は BASE 保存を要求しない統一帰納）。 -/
theorem RunPeelPreservedD_vc2_refuted_rs2 : ¬ RunPeelPreservedD_vc2 := by
  intro h
  have hcex := h witCexRS (by decide) (by decide) (by decide) (by decide)
  -- 結論の第二成分 `VEj1p (Pred N) = Lng (Pred N) - 1` が反例で偽
  exact absurd hcex.2 (by decide)

#print axioms RunSqueeze_vn_refuted_rs2
#print axioms RunPeelPreservedD_vc2_refuted_rs2

end PSS

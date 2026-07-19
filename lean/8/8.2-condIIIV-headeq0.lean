import «8».«8.2-condIIIV-ve-next»

/-!
# §8.2 条件(II)/(IV) VE34 — **HEADEQ0 キャンペーン**（`VE3All`/`VE4All` を一挙に閉じる route）

- 原文: `tmp/content.md` L1624 付近（命題「条件(II)か(IV)の下での終切片と `Trans` の関係」）。
  Isabelle 側の**真の閉路**は `layerB/pss_wip.thy` の `hqx_`/`bgx_` HEADEQ0 route
  (106236–108760, r47-BASEFAM＋r48-HEADEQ0)。これ 1 本で `VE3All`/`VE4All`（＝Isabelle
  `vg2x_VE34` の VE3/VE4 側）が全 `vg7x_reg4`(=`VE34Reg4D`) ホストで閉じる。
  ⚠️ Wave AM の `RunSqueeze_vn`/BASE 保存設計は反証済（10 個目）。統一 backpeel
  帰納 `bfx_VE34_backpeel_fin3`(105252) が正しいフレームだが、その閉路は本 HEADEQ0 route。

## Isabelle の依存スパイン（この route の地図）

```
hqx_condIIIV_of_DT  (108722)  §8.2 命題（∃! 形、VE2＋VE34 を束ねる = 最終消費者）
  └ hqx_VE34_of_DT  (108701)  DT ホスト capstone（残差 0）
      └ bgx_VE34_of_DT_modHEADEQ (107275)  DTPS→reg4 場組立（VE34Reg4D_of_dtps_host に対応）
          └ hqx_VE34_of_reg (108690)  reg4 capstone（残差 0）
              ├ bgx_VE34_of_reg_modHEADEQ (107245)  VE34 ⟸ HEADEQ0（= reduction 本体）
              │   ├ bgx_VE34_of_reg_modNOTLEFT_HEADEQ (106728)  NOTLEFT0＋HEADEQ0 modulo
              │   │   └ base-recursion family: bgx_base_core / bgx_base_form_{left,notleft}
              │   │       / bgx_Mp_form / bgx_VE34_base_step / bgx_front_run0
              │   │       / bgx_VE34_base_run0_mod  （§7.4/§8 surgery、~1000 行）
              │   └ bgx_notleft_run0 (106972)  NOTLEFT0 = census 経路
              │       └ bgx_trunk_Trans (106875) / bgx_headedge (106…) / bgx_lastPB …
              └ hqx_HEADEQ0 (108441)  ★単一原子 HEADEQ0 の討伐（240 行、2 ケース）
                  ├ [trunk corner]  diagSeq 閉形式  m_8_1_diagSeq_Trans（Lean 移植済）
                  └ [branching]  regime cfbx_reg j₀ (Pred N) を組んで
                       **vcx_VE_all[OF regQ]** を適用（★ハード原子）
                  └ hqx_Pred_seg (108411)  Pred(終切片)=一列短い切片（本ファイルで移植）
```

## (2) の検証: 「vcx_VE_all が HEADEQ0 brick を既に討伐」の真偽

- `vcx_VE_all` は Lean 移植済（`8.2-condV-VE-close.lean:1652`,
  `vcx_VE_all (m) (M) (VEReg m M) : VEeq m M`）＝**ハード原子は既にツリー内**。
- ただし `hqx_HEADEQ0` の中で `vcx_VE_all` を使うのは**分岐ケースのみ**
  (`pss_wip.thy:108667` `have VEQ: cfbx_VE ?j0 ?Q by rule vcx_VE_all[OF regQ]`)。
  trunk-corner ケースは `m_8_1_diagSeq_Trans` の閉形式で別途処理する。
  すなわち `hqx_HEADEQ0` は「vcx_VE_all の一行応用」ではなく、regime `cfbx_reg j₀ (Pred N)`
  の構築（`bgx_headedge`/`bfx_gtN`/`wid_*`/`m_6_4_*`/`entry_FirstNodes_*` 依存）＋
  trunk-corner の diagSeq 論法を含む 2 ケース 240 行の証明。
  よって Wave-T の「vcx_VE_all closes only its HEADEQ0 brick」は
  **分岐ケースの deep value 供給に限り真**（残る glue は本ファイルの `HEADEQ0All_hq` 内）。

## (3) 本ファイルの移植（bottom-up、緑維持、残差は名前付き Prop で露出）

- ✅ `hqx_Pred_seg_hq` — `Pred (seg N a (Lng N-1)) = seg N a (Lng N-2)`
  （HEADEQ0 の最下段 brick、`seg`.dropLast で無条件に移植）。
- 📛 `HEADEQ0All_hq` — 単一残差 HEADEQ0 を ∀-形の**名前付き Prop** として定義
  （＝`hqx_HEADEQ0` の結論、全 `VE34Reg4D` ホスト BASE run-base 上）。
- 📛 `BgxVE34RedHE0_hq` — bgx reduction を**名前付き Prop** として定義
  （＝`bgx_VE34_of_reg_modHEADEQ`：HEADEQ0 から `VE34goal` を放出）。
- ✅ `hqx_VE34_of_reg_hq` / `hqx_VE34_of_DT_hq` — capstone を上記 2 残差 modulo で緑組立。
  DTPS→reg4 場組立は `VE34Reg4D_of_dtps_host`（移植済）で**本物**。
- ✅ `hqx_VE3goal_of_reg_hq` / `hqx_VE4goal_of_reg_hq` — `VE34goal_iff` で VE3/VE4 に分解
  （`VE3All`/`VE4All` への橋。残る `VE34Reg4D → VE34Reg4` の field-rewiring は out-of-scope）。

- 訂正: なし（Isabelle 済補題の逐語移植、または名前付き Prop 骨格）。

- 状態: ⚠️ 部分（sorry 0、rc=0）。HEADEQ0 route のスパインを Lean で骨格化し、
  最下段 brick `hqx_Pred_seg_hq` を無条件討伐、capstone を 2 残差 modulo で緑放出。
  残差本体 = `BgxVE34RedHE0_hq`（bgx base-recursion family）と
  `HEADEQ0All_hq`（vcx_VE_all＋diagSeq）＝`needs` に報告。

- 依存 module: `8.2-condIIIV-ve-next`（`VE34Reg4D`/`VE34Reg4D_of_dtps_host`/`VE34goal`/
  `VE34goal_iff`/`VE3goal`/`VE4goal`/`VEj1p`/`DTPS`/`Br`/`Joints`/`FirstNodes`/`LastStep`/
  `bpHeadT`/`Trans`/`Pred`/`seg`/`length_seg`/`entry` を推移的に）。

- Private suffix: `_hq`。
-/

namespace PSS

/-! ## 最下段 brick: `hqx_Pred_seg`（`Pred` of 終切片 = 一列短い切片） -/

/-- `(seg M a b).dropLast = seg M a (b-1)`（`1 ≤ b`）。既存 private helper
（`8.4-corner-redesign` の `seg_dropLast_cr` 等）の再掲。 -/
private theorem seg_dropLast_hq (M : PS) (a b : ℕ) (hb : 1 ≤ b) :
    (seg M a b).dropLast = seg M a (b - 1) := by
  apply List.ext_getElem
  · simp only [List.length_dropLast, length_seg]; omega
  · intro i h1 h2
    simp only [List.getElem_dropLast, seg, List.getElem_map, List.getElem_range']

/-- **`hqx_Pred_seg`** (Isabelle `pss_wip.thy:108411`): 終切片 `seg N a (Lng N-1)` の
`Pred`（＝末尾一列落とし）は、一列短い切片 `seg N a (Lng N-2)` に等しい。HEADEQ0 討伐の
最下段 brick。`a < Lng N - 1` が終切片の長さ `> 1`（`Pred` が `dropLast` になる）を保証する。 -/
theorem hqx_Pred_seg_hq (N : PS) (a : ℕ) (hL : 1 < Lng N) (halt : a < Lng N - 1) :
    Pred (seg N a (Lng N - 1)) = seg N a (Lng N - 2) := by
  have hlenseg : Lng (seg N a (Lng N - 1)) = (Lng N - 1) + 1 - a := length_seg N a (Lng N - 1)
  have hgt1 : ¬ Lng (seg N a (Lng N - 1)) ≤ 1 := by rw [hlenseg]; omega
  have hpred : Pred (seg N a (Lng N - 1)) = (seg N a (Lng N - 1)).dropLast := by
    unfold Pred; rw [if_neg hgt1]
  have hb : 1 ≤ Lng N - 1 := by omega
  have he : Lng N - 1 - 1 = Lng N - 2 := by omega
  rw [hpred, seg_dropLast_hq N a (Lng N - 1) hb, he]

/-! ## 単一残差 HEADEQ0（名前付き Prop）

Isabelle `hqx_HEADEQ0` (108441) の結論の ∀-形。run-base BASE ホスト
（`VE34Reg4D N`＝`vg7x_reg4 N`, BASE `VEj1p N = Lng N-1`, run-base `LastStep N =
(Br N).length - 1`）について、終切片の `Pred` の deep head が host の `Pred` の deep head に
等しい。⚠️ Isabelle の `fin`（`LastStep` の `Min`-集合有限性）は Lean では
`{J | J < (Br N).length ∧ …} ⊆ range` が自動的に有限なので不要（correction-A9 領域）。 -/
def HEADEQ0All_hq : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → LastStep N = (Br N).length - 1 →
    bpHeadT (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))))
      = bpHeadT (Trans (Pred N))

/-! ## bgx reduction（名前付き Prop）

Isabelle `bgx_VE34_of_reg_modHEADEQ` (107245): 単一残差 HEADEQ0 から、全 `VE34Reg4D`
ホストで `VE34goal`（＝`vg2x_VE34`）を放出する reduction。本体は base-recursion family
`bgx_base_*`/`bgx_Mp_form`/`bgx_VE34_base_*`/`bgx_notleft_run0`（~1000 行、§7.4/§8 surgery、
未移植）＝`needs`。 -/
def BgxVE34RedHE0_hq : Prop :=
  ∀ M : PS, VE34Reg4D M → HEADEQ0All_hq → VE34goal M

/-! ## capstone（2 残差 modulo で緑組立） -/

/-- **`hqx_VE34_of_reg`** (Isabelle `pss_wip.thy:108690`): 全 `VE34Reg4D`(=`vg7x_reg4`)
ホストで `VE34goal`（＝`vg2x_VE34`）。bgx reduction `BgxVE34RedHE0_hq` に単一残差
`HEADEQ0All_hq` を食わせるだけ。 -/
theorem hqx_VE34_of_reg_hq (hred : BgxVE34RedHE0_hq) (hHE0 : HEADEQ0All_hq)
    (M : PS) (hreg : VE34Reg4D M) : VE34goal M :=
  hred M hreg hHE0

/-- **`hqx_VE34_of_DT`** (Isabelle `pss_wip.thy:108701`): §8.2 条件(II)/(IV) VE34
dispatcher。DTPS ホストの場（`Br M ≠ []`, guard, `0 < j₀ < TrMax`）から補正体制
`VE34Reg4D` を組み（`VE34Reg4D_of_dtps_host`＝**本物の glue**）、`hqx_VE34_of_reg_hq` を適用。 -/
theorem hqx_VE34_of_DT_hq (hred : BgxVE34RedHE0_hq) (hHE0 : HEADEQ0All_hq)
    (M : PS) (hD : DTPS M) (hBrne : Br M ≠ [])
    (hj0pos : 0 < (Joints M).getD ((Br M).length - 1) 0)
    (hj0lt : (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
    (hguard : entry M 1 (VEj1p M) < entry M 0 (VEj1p M)) :
    VE34goal M :=
  hqx_VE34_of_reg_hq hred hHE0 M
    (VE34Reg4D_of_dtps_host M hD hBrne hj0pos hj0lt hguard)

/-! ## `VE3All`/`VE4All` への橋（`VE34goal_iff` で分解）

⚠️ `VE3All`/`VE4All` は `VE34Reg4`（descending なし）上の ∀。以下は `VE34Reg4D`
（descending 込み）上での VE3/VE4。残る `VE34Reg4D → VE34Reg4` の field-rewiring は
Wave AL/AM で out-of-scope と明記（向きが狭→広で逆、DTPS ホスト側で埋める）。 -/

/-- `VE34Reg4D` ホストで VE3（頭シフト成分の存在）。 -/
theorem hqx_VE3goal_of_reg_hq (hred : BgxVE34RedHE0_hq) (hHE0 : HEADEQ0All_hq)
    (M : PS) (hreg : VE34Reg4D M) : VE3goal M :=
  ((VE34goal_iff M).mp (hqx_VE34_of_reg_hq hred hHE0 M hreg)).1

/-- `VE34Reg4D` ホストで VE4（外側 context 方程式）。 -/
theorem hqx_VE4goal_of_reg_hq (hred : BgxVE34RedHE0_hq) (hHE0 : HEADEQ0All_hq)
    (M : PS) (hreg : VE34Reg4D M) : VE4goal M :=
  ((VE34goal_iff M).mp (hqx_VE34_of_reg_hq hred hHE0 M hreg)).2

#print axioms hqx_Pred_seg_hq
#print axioms hqx_VE34_of_reg_hq
#print axioms hqx_VE34_of_DT_hq
#print axioms hqx_VE3goal_of_reg_hq
#print axioms hqx_VE4goal_of_reg_hq

end PSS

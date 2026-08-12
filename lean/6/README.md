[← Back](../README.md)

# 第6章 定理目次

各項目の [lean] は形式証明、[md] は日本語・MathJax 版の証明を指す。
[md] がない項目は、Markdown 版をまだ作成していない。

## §6.1

- 6.1 命題（`≤_M` の `IncrFirst` 不変性） [lean](6.1-le-IncrFirst-invariance.lean)

## §6.2

- 6.2 命題（`P` の `IncrFirst` 同変性） [lean](6.2-P-IncrFirst-equivariance.lean)
- 6.2 命題（`P` の加法性） [lean](6.2-P-additivity.lean)
- 6.2 命題（`P` の各成分の非複項性） [lean](6.2-P-components-nonmulti.lean)
- 6.2 命題（`P` と基本列の関係） [lean](6.2-P-fseq.lean)
- 6.2 命題（単項性の直系先祖による切片への遺伝性） [lean](6.2-mono-ancestor-slice.lean)
- 6.2 系（単項性の始切片への遺伝性） [lean](6.2-mono-prefix.lean)
- 6.2 命題（複項性の判定条件） [lean](6.2-multi-criterion.lean)
- 6.2 命題（非複項性と基本列の関係） [lean](6.2-nonmulti-fseq.lean)

## §6.3

- 6.3 命題（許容性の切片への遺伝性） [lean](6.3-adm-slice.lean)
- 6.3 命題（許容化の切片への遺伝性） [lean](6.3-admof-slice.lean)
- 6.3 命題（基点の切片への遺伝性） [lean](6.3-marked-slice.lean)

## §6.4

- 6.4 系（`FirstNodes` と `Joints` の単調性） [lean](6.4-FirstNodes-Joints-mono.lean)
- 6.4 命題（`FirstNodes` と `TrMax` と `Joints` の関係） [lean](6.4-FirstNodes-TrMax-Joints.lean)
- 6.4 系（`P` と `IdxSum` の合成の特徴付け） [lean](6.4-P-IdxSum-characterization.lean)
- 6.4 命題（`P` と `IdxSum` の関係） [lean](6.4-P-IdxSum.lean)
- 6.4 命題（`P` の各成分の左端の単調性） [lean](6.4-P-leftend-mono.lean)
- 6.4 命題（切片の単項成分と `<^Next` の関係） [lean](6.4-mono-slice-next.lean)
- 6.4 系（単項性の切片への遺伝性） [lean](6.4-mono-slice.lean)

## §6.5

- 6.5 命題（`Lng` の `Red` 不変性） [lean](6.5-Lng-Red-invariance.lean)
- 6.5 系（`P` の `Red` 同変性） [lean](6.5-P-Red-equivariance.lean)
- 6.5 命題（`Red` の `IncrFirst` 不変性） [lean](6.5-Red-IncrFirst-invariance.lean)
- 6.5 命題（`Red` と `Pred` の可換性） [lean](6.5-Red-Pred-commute.lean)
- 6.5 命題（`Red` と基本列の可換性） [lean](6.5-Red-fseq-commute.lean)
- 6.5 命題（`Red` の冪等性） [lean](6.5-Red-idempotence.lean)
- 6.5 `Red`・祖先関係補助基盤 [lean](6.5-Red-le-core.lean)
- 6.5 系（直系先祖の `Red` 不変性） [lean](6.5-Red-le-invariance.lean)
- 6.5 命題（`Red` が許容性を保つこと） [lean](6.5-Red-preserves-adm.lean)
- 6.5 系（`Red` が基点を保つこと） [lean](6.5-Red-preserves-marked.lean)
- 6.5 系（`Red` が単項性を保つこと） [lean](6.5-Red-preserves-monoT.lean)
- 6.5 系（`Red` が零項性を保つこと） [lean](6.5-Red-preserves-zeroT.lean)
- 6.5 命題（`Red` の well-defined 性） [lean](6.5-Red-welldefined.lean)
- 6.5 系（許容化の `Red` 不変性） [lean](6.5-admof-Red-invariance.lean)
- 6.5 命題（単項性と `Red` の関係） [lean](6.5-monoT-Red.lean)

## §6.6

- 6.6 `P` ブロックと係数条件 (A), (B) [lean](6.6-P-condAB.lean)
- 6.6 命題（`P` が簡約性を保つこと） [lean](6.6-P-preserves-reduced.lean)
- 6.6 `RT_PS` と `Red` の像の関係 [lean](6.6-RT-image-of-Red.lean)
- 6.6 補題（`Red` と左端の関係） [lean](6.6-Red-leftend.lean)
- 6.6 RED2: two reductions reach a reduced pair sequence [lean](6.6-Red2.lean)
- 6.6 系（直系先祖による切片と `Red` と `IncrFirst` の関係） [lean](6.6-ancestor-slice-Red-IncrFirst.lean)
- 6.6 補題（条件 (A), (B) と係数の基本性質） [lean](6.6-condAB-coeff.lean)
- 6.6 系（`1` 列ペア数列の基本性質） [lean](6.6-one-column.lean)
- 6.6 補題（簡約性と係数の基本性質） [lean](6.6-reduced-coeff.lean)
- 6.6 命題（簡約性が基本列で保たれること） [lean](6.6-reduced-fseq.lean)
- 6.6 命題（簡約性と係数の関係） [lean](6.6-reduced-iff-condAB.lean)
- 6.6 補題（簡約性と左端の関係） [lean](6.6-reduced-leftend.lean)
- 6.6 命題（簡約性の切片への遺伝性） [lean](6.6-reduced-slice.lean)

## §6.7

- 6.7 命題（標準形の単項成分が標準形であること） [lean](6.7-standard-P-components.lean)
- 6.7 命題（標準形の始切片への遺伝性） [lean](6.7-standard-prefix.lean)
- 6.7 命題（標準形の簡約性） [lean](6.7-standard-reduced.lean)

## §6.8

- 6.8 d1pos regime-A アンカー一致層（anchor-regA brick 族） [lean](6.8-d1pos-anchor-regA.lean)
- 6.8 d1pos regime-B/A2 anchor 層 ＋ ctx brick 群 [lean](6.8-d1pos-anchor-regB.lean)
- 6.8 d1pos 基礎 brick（ブロック幾何と le0 背骨） [lean](6.8-d1pos-base.lean)
- 6.8 d1pos ¬brle BOUNDARY セル ＋ 周期境界 anchor brick 群 [lean](6.8-d1pos-cell-boundary.lean)
- 6.8 d1pos CELL-4 (PERIODIC-TAIL) take-eq セル ＋ shamt=0 anchor 束 [lean](6.8-d1pos-cell-periodic.lean)
- 6.8 d1pos CELL-1（regime A）＋ notbrleNp ctx brick 族 [lean](6.8-d1pos-cell-regA.lean)
- 6.8 d1pos ¬brle regime-B cell（LOW take-eq、`j₋₂ ≤ j0'`） [lean](6.8-d1pos-cell-regB.lean)
- 6.8 d1pos leg — green-modulo dispatch（`RankSuccD1posLeg` の brick 分解） [lean](6.8-d1pos-dispatch.lean)
- 6.8 命題（標準形の切片と `Br` の降順性の関係）— 無条件版（campaign 最終配線） [lean](6.8-d1pos-final.lean)
- 6.8 d1pos ブロック内 le0 ＋ tnc 文脈 brick 層 [lean](6.8-d1pos-le0.lean)
- 6.8 d1pos ¬brle — P-split / Br-align 層（notbrle brick 族） [lean](6.8-d1pos-notbrle.lean)
- 6.8 d1pos 周期レジーム層（CELL-4 PERIODIC-TAIL brick 群）＋即討ち Props [lean](6.8-d1pos-period.lean)
- 6.8 補題（d1pos 跨りスライスの `TrMax` 対応 brick 層） [lean](6.8-d1pos-trmax.lean)
- 6.8 命題（標準形の単項成分が降順であること） [lean](6.8-standard-P-descending.lean)
- 6.8 命題（標準形の切片と `Br` の降順性の関係） [lean](6.8-standard-slice-Br-descending.lean)


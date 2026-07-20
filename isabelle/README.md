[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# isabelle/ — Isabelle/HOL 形式化のファイル構成

ペア数列システムの停止性の Isabelle/HOL 版。**停止性は仮定ゼロ・`sorry` ゼロで証明済み**
（ビルド時に ML 監査ブロックが強制）。

`lean/` と同型のレイアウト（章ディレクトリ＋1 命題 1 ファイル＋共有 `PSS/` 層）への再編は
**完了済み**。

## ディレクトリ構成

```
isabelle/
├── ROOT                    セッション定義（PSS_A ← PSS_B ← PSS_C）
├── pss_defs.thy            §4–§6 の定義
├── PSS/                    共有層 154：跨章ヘルパ
│   ├── Pre_5.thy           §5 の前段
│   ├── Frontier_NNN.thy    連番の共有ヘルパ（148）
│   └── After_5/6/7.thy     章境界を露出させる節点
├── 5/                      §5：命題 13 ＋ 章ローカルヘルパ 1
├── 6/                      §6：命題 55 ＋ 章ローカルヘルパ 73
├── 7/                      §7：命題 27 ＋ 章ローカルヘルパ 51
├── 8/                      §8：命題 33 ＋ 章ローカルヘルパ 3 ＋ audit
│   ├── P_8_7_termination.thy   主定理
│   ├── Support_8_A/B/C.thy     §8 内で共有される大型ヘルパ
│   └── audit.thy               ML 監査（PSS_A の最終 theory）
├── pss_paper.thy           外部文献 [Buc1] の転記（定義＋引用 3 補題）
├── pss_mechanized.thy      再編後の互換シム
├── layerB/pss_wip.thy      凍結層
└── layerC/pss_scratch.thy  作業層
```

ファイル名の規約：`P_<節>_<slug>.thy` が原文の命題 1 個（証明込み）、`Support_*.thy` が
その章だけで使うヘルパ、`PSS/Frontier_*.thy` が複数章で使う共有ヘルパ。

## ヘルパの振り分け

各補助補題を **usage-chapter set** で機械的に配置している：**≥2 章が（推移的に）使う → 共有
`PSS/`**、**1 章のみ → その章ディレクトリ**。依存 DAG 解析（reorg Phase 0、`phase0/REPORT.md`）で
4,353 fact の非巡回 DAG を抽出し、共有 2,288 / 章ローカル 1,283 に分割した。

## セッション構成

| セッション | ディレクトリ | 内容 | 役割 |
|---|---|---|---|
| `PSS_A` | `.` | `pss_defs` ＋ `PSS/` ＋ `5/`〜`8/` ＋ `pss_paper` ＋ `8/audit` | 凍結ベース |
| `PSS_B` | `layerB` | `pss_wip` | 凍結ベース |
| `PSS_C` | `layerC` | `pss_scratch` | 作業層 |

`8/audit.thy` は `PSS_A` の最終 theory なので、**`PSS_A` が緑になること自体が監査合格**を意味する。
停止性の定理群が `sorry` を持つ言明に到達したら `error` でビルドが落ちる。

## ビルド

フルビルド：

```
cd isabelle && isbman build -d . -v PSS_A PSS_B PSS_C
```

毎ラウンドは作業中の最上層だけ：

```
cd isabelle && isbman build -d . -v PSS_C
```

緑の判定は `Finished PSS_C` がちょうど 1 行、`***` で始まる行が 0 行、`AUDIT FAILED` が 0 行。

## 残る `sorry`（8 件、いずれも停止性の証明が参照しない）

- `pss_paper.thy` 3 件 — 外部文献 [Buc1] の引用補題（2.2 / 3.2a / 3.3）。うち 3.2a と 3.3 は
  `7/` に自前の証明 `m_buc1_*` がある
- `8/` 5 件 — 原文の命題のうち未証明のもの。`P_8_1_condI_III_c1_around` は原文が偽
  （訂正 A20 / A21）、残り 4 件は原文は真だが未証明

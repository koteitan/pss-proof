[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# isabelle/ — Isabelle/HOL 形式化のファイル構成

ペア数列システムの停止性の Isabelle/HOL 版。**停止性は仮定ゼロ・`sorry` ゼロで証明済み**
（ビルド時に ML 監査ブロックが強制）。状態は**完了・凍結**。

## ディレクトリ構成

```
isabelle/
├── ROOT                    入れ子セッション定義 PSS_A ← PSS_B ← PSS_C
├── pss_defs.thy            §4–§6 の定義の形式化（共有）              542 行
├── pss_paper.thy           論文の命題・補題・系・定理の主張のみ転記（全 sorry） 2,334 行
├── pss_mechanized.thy      独自の機械化証明（pss_paper の sorry を解消） 65,913 行
├── layerB/
│   └── pss_wip.thy         旧キャンペーンの証明済み本体（凍結）        119,055 行
├── layerC/
│   └── pss_scratch.thy     作業中の最上層＋停止性の仕上げ＋ML 監査ブロック 25,102 行
├── docs/                   設計ノート（red-termination, buchholz, thy-toc …）
├── task.md                 進捗ツリー（全 ✅）
├── memo.md                 設計メモ・死路
└── agent-workflow.md       サブエージェント規約
```

## 層分割セッション（ROOT）

巨大な証明本体を凍結ヒープに置き、毎回はアクティブ最上層だけを建て直す設計。

| セッション | dir | theory | 役割 | 緑判定 |
|---|---|---|---|---|
| `PSS_A` | `.` | `pss_defs`＋`pss_paper`＋`pss_mechanized` | 凍結ベース | `Finished PSS_A` |
| `PSS_B` | `layerB` | `pss_wip` | 凍結ベース | `Finished PSS_B` |
| `PSS_C` | `layerC` | `pss_scratch` | アクティブ最上層 | `Finished PSS_C` |

import 連鎖：`pss_defs ← pss_paper ← pss_mechanized ← pss_wip ← pss_scratch`
（後ろ 2 つはセッション修飾で import）。

## 命名

- `p_<§>_<slug>` ＝論文の主張（`pss_paper.thy`）、`m_<§>_<slug>` ＝独自証明（`pss_mechanized.thy`）。
- 補助補題は内容接頭辞（`idxsum_`, `poper_`, `seg_`, `adm_`, `scb_`, `Lng_` …）。

## ビルド

ルート [../README.md](../README.md) のビルド節を参照。フルビルドは
`cd isabelle && isbman build -d . -v PSS_A PSS_B PSS_C`。緑の判定は `Finished PSS_C` が
ちょうど 1 行、`***` で始まる行が 0 行、`AUDIT FAILED` が 0 行。

## 予定（Lean 化）

この層分割 monolith を `lean/` と同型 ── 章ディレクトリ `5/ 6/ 7/ 8/` ＋ 1 命題 1 ファイル
＋ 共有 `PSS/` 層 ── へ再編する作業を計画・進行中。約 128 命題・約 4,400 補助補題を、
usage-chapter set（≥2 章で使うヘルパ＝共有 `PSS/`、1 章のみ＝章ローカル）で機械的に振り分ける。

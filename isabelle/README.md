[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# isabelle/ — Isabelle/HOL 形式化のファイル構成

ペア数列システムの停止性の Isabelle/HOL 版。**停止性は仮定ゼロ・`sorry` ゼロで証明済み**
（ビルド時に ML 監査ブロックが強制）。

> **状態**：`lean/` と同型のレイアウト（章ディレクトリ＋1 命題 1 ファイル＋共有 `PSS/` 層）へ
> **再編中**。以下は**再編後の目標構成**。共有/章ローカルの正確な境界とセッション構成は
> 依存 DAG 解析（reorg Phase 0）で確定する。

## ディレクトリ構成（目標）

```
isabelle/
├── ROOT                    セッション定義（DAG 順: PSS ← §5 ← §6 ← §7 ← §8）
├── PSS/                    共有層：定義＋跨章ヘルパ（≥2 章が使うもの、~482）
│   ├── Defs.thy            §4–§6 の定義
│   ├── Seg.thy             seg_* entry_* le0_*
│   ├── Idxsum.thy          idxsum_* oper_* poper_*
│   ├── Mono.thy            単調性 / IncrFirst
│   ├── Adm.thy             adm_*（許容性）
│   ├── Red.thy             §6.5 Red 簡約
│   ├── Standard.thy        ST_PS / RT_PS
│   ├── Scb.thy             scb_*
│   ├── Buchholz.thy        §7 [Buc1] 表記系（operB_* domB_* TrMax_* …）
│   └── Trans.thy           Trans（tran* repr_* rnsub_* …）
├── 5/                      §5: 13 命題（+局所ヘルパ 5）
│   ├── p_5_1_parent_exists_1.thy
│   │   …
│   └── p_5_4_F_oper_val.thy
├── 6/                      §6: 55 命題（+局所ヘルパ 636）
├── 7/                      §7: 27 命題（+局所ヘルパ 199）
└── 8/                      §8: 33 命題（+局所ヘルパ 2,171）
    ├── p_8_7_termination.thy   主定理
    │   …
    └── audit.thy               ML 監査（全定理の sorry 依存をビルド時に検査）
```

## ヘルパの振り分け

各補助補題を **usage-chapter set** で機械的に配置する：**≥2 章が（推移的に）使う → 共有
`PSS/`**、**1 章のみ → その章ディレクトリのローカル**。約 4,400 補助補題のうち共有は
~482（13%）、残りは章ローカル（§8 が 2,171 で最大）。

## セッション（ROOT）

依存 DAG に沿った層：`PSS`（共有・凍結）← `PSS_5` ← `PSS_6` ← `PSS_7` ← `PSS_8`。
各セッションは一度だけビルド＝凍結ヒープの再処理なし。ML 監査は最上位セッションの
`8/audit.thy` 末尾に置く。

## 命名

- ファイル名＝命題名 `p_<§>_<slug>.thy`（例 `p_8_7_termination.thy`）、theory 名も同じ。
  独自証明は `m_<§>_<slug>`、補助補題は内容接頭辞（`seg_`, `idxsum_`, `adm_`, `scb_` …）。
- **Isabelle の theory 名はドット/ハイフン不可・数字始まり不可**。`lean` の
  `8.7-termination.lean` 相当は `p_8_7_termination.thy`（ディレクトリ名 `5/`…`8/` は可）。

## ビルド

フルビルドは最上位セッションを建てる（依存で `PSS`・§5–§7 も建つ）：
`cd isabelle && isbman build -d . -v PSS_8`。緑の判定は対象セッションの `Finished` が
ちょうど 1 行、`***` で始まる行が 0 行、`AUDIT FAILED` が 0 行。

# pss-proof

Version: **v0.3.0**

ペア数列システム（pair sequence system）の停止性証明を形式検証するプロジェクト。

P進大好きbot 氏のブログ記事「ペア数列の停止性」（巨大数研究 Wiki）の証明を、できるだけ忠実に形式化することを目標とする。

| ディレクトリ | 内容 | 状態 |
|---|---|---|
| [`isabelle/`](isabelle/) | Isabelle/HOL 版 | **完了**（停止性を仮定ゼロ・`sorry` ゼロで証明） |
| [`corrections/`](corrections/) | Isabelle/HOL の反例・経験検証資料（独立セッション） | 機械検査済みアーカイブ |
| [`memo/`](memo/) | 停止性に採用しなかった Isabelle/HOL 証明キャンペーン | 機械検査済みアーカイブ |
| [`lean/`](lean/) | Lean 4 版（原文の命題 1 つ = ファイル 1 つ） | **作業中** |
| `python/` | 反例探索・数値検証モデル | 共通 |
| `tools/` | 原文処理 | 共通 |

## 結果

**ペア数列システムの停止性は、仮定ゼロ・`sorry` ゼロで形式証明されている。**

```isabelle
theorem y5_PSS_wf : "wf y3_PSSrel"          (* 停止性 = 展開関係の整礎性 *)
theorem y5_Fdom   : ...                     (* 原文の言明 p_8_7_termination の逐語形 *)
```

- 外部文献 [Buc1] の補題（2.1 / 2.2 / 3.2a / 3.3）も**すべて自前で証明**しており、引用による穴は無い。
- `sorry` に依存していないことは **ML の監査ブロックがビルド時に強制**する（`isabelle/8/audit.thy`）。
  停止性の定理群が `isabelle/pss_paper.thy` の 131 個の `sorry` のいずれかに到達したら、`error` でビルドが落ちる。
  **緑ビルド＝監査合格**であり、negative control（意図的に汚した定理を混ぜるとビルドが落ちる）で検証済み。

原文の全命題・補題・系・定理の形式化も完了している（[`isabelle/task.md`](isabelle/task.md) の進捗ツリー参照）。
その過程で原文の訂正案を 30 件見つけた（下記）。

## ファイル構成（Isabelle 版）

| ファイル | 役割 |
|---|---|
| `isabelle/pss_defs.thy` | 論文の定義の形式化（共通） |
| `isabelle/pss_paper.thy` | 論文の命題・補題・系・定理のステートメントのみを転記（すべて `sorry`） |
| `isabelle/pss_mechanized.thy` | 独自の機械化証明（`sorry` を解消） |
| `isabelle/layerB/pss_wip.thy` | 証明済みの本体（凍結層） |
| `isabelle/layerC/pss_scratch.thy` | 作業層の互換エンドポイント |
| `isabelle/ROOT` | Isabelle セッション定義（`PSS_A` ← `PSS_B` ← `PSS_C` の入れ子） |
| `corrections/ROOT` | 反例資料の独立セッション `PSS_CORRECTIONS` |
| `memo/ROOT` | 不採用キャンペーンの独立セッション `PSS_MEMO` |

Lean 版の構成は [`lean/spec.md`](lean/spec.md)、進捗は [`lean/task.md`](lean/task.md)、
作業手順は [`lean/step.md`](lean/step.md) にある。

各事実は `<§番号>_<内容>` 形式で命名し、コメントに元論文の節番号（§）と日本語名を付けて
元論文と対応付けられるようにしている。`pss_paper.thy` の `p_` 接頭辞が論文の主張、
`pss_mechanized.thy` の `m_` 接頭辞が独自証明に対応する。

## 進捗

各命題・補題・系・定理の証明状況は [`isabelle/task.md`](isabelle/task.md) と [`lean/task.md`](lean/task.md) に進捗ツリー（未証明🚨 / 証明済✅ / 原文偽❌ / 作業中🤖）としてまとめている。

## 原文への訂正案

形式化の過程で見つかった原論文の訂正案は [`corrections.md`](corrections.md) に、原文 HTML への修正として集約している。**30 件**（取り下げた 16 件は [`corrections-old.md`](corrections-old.md)）。

## ビルド

**Isabelle** — フルビルド（`PSS_A → PSS_B → PSS_C` を最初から全部建てる）：

```
cd isabelle && isbman build -d . -v PSS_A PSS_B PSS_C
```

毎ラウンドは作業中の最上層だけ：

```
cd isabelle && isbman build -d . -v PSS_C
```

緑の判定は `Finished PSS_C` がちょうど 1 行、`***` で始まる行が 0 行、`AUDIT FAILED` が 0 行。

停止性木と独立した Isabelle アーカイブ：

```
cd isabelle && isbman build -d . -d ../corrections -d ../memo -v PSS_MEMO
```

**Lean**：

```
cd lean && lake build
```

ただし `lake build` は `sorry` を warning でしか報告しない。証明の判定には
[`lean/step.md`](lean/step.md) の「緑の定義」に従い `python3 python/check_lean.py <file>` を使う。

## 出典・引用 (Reference)
- W. Buchholz, "[A new system of proof-theoretic ordinal functions](https://www.sciencedirect.com/science/article/pii/0168007286900527)", Annals of Pure and Applied Logic, Volume 32, 1986, pp. 195–207.
- Bashicu, "[BASIC 言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=15603&useskin=oasis)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2015.8.21.
- koteitan, "[バシク行列の亜種ルールの分類](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E4%BA%9C%E7%A8%AE%E3%83%AB%E3%83%BC%E3%83%AB%E3%81%AE%E5%88%86%E9%A1%9E)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2018.6.2.
- P進大好きbot. "[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2018.11.11.

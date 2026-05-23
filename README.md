# pss-proof

Version: **v0.1.5**

ペア数列システム（pair sequence system）の停止性証明を Isabelle/HOL で形式検証するプロジェクト。

P進大好きbot 氏のブログ記事「ペア数列の停止性」（巨大数研究 Wiki）の証明を、できるだけ忠実に形式化することを目標とする。

## ファイル構成

| ファイル | 役割 |
|---|---|
| `pss_defs.thy` | 論文の定義の形式化（共通） |
| `pss_paper.thy` | 論文の命題・補題・系・定理のステートメントのみを転記（すべて `sorry`） |
| `pss_mechanized.thy` | 独自の機械化証明（`sorry` を解消） |
| `ROOT` | Isabelle セッション定義（`session PSS = HOL`） |

各事実は `<§番号>_<内容>` 形式で命名し、コメントに元論文の節番号（§）と日本語名を付けて
元論文と対応付けられるようにしている。`pss_paper.thy` の `p_` 接頭辞が論文の主張、
`pss_mechanized.thy` の `m_` 接頭辞が独自証明に対応する。

## ビルド

```
isbman build -d . -v PSS
```

# pss-proof

Version: **v0.1.11**

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

## 進捗

各命題・補題・系・定理の証明状況は [`task.md`](task.md) に進捗ツリー（未証明🚨 / 証明済✅ / 証明不可🚫 / 作業中🤖）としてまとめている。

## 原文への訂正案

形式化の過程で見つかった原論文の誤記・訂正案は [`corrections.md`](corrections.md) に、原文 HTML への修正として集約している（著者フィードバック用）。

## ビルド

```
isbman build -d . -v PSS
```

## 出典・引用 (Reference)
- W. Buchholz, "A new system of proof-theoretic ordinal functions", Annals of Pure and Applied Logic, Volume 32, 1986, pp. 195–207.
- Bashicu, "[BASIC 言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=15603&useskin=oasis)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2015.8.21.
- koteitan, "[バシク行列の亜種ルールの分類](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E4%BA%9C%E7%A8%AE%E3%83%AB%E3%83%BC%E3%83%AB%E3%81%AE%E5%88%86%E9%A1%9E)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2018.6.2.
- P進大好きbot. "[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=15603&useskin=oasis)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2018.11.11.


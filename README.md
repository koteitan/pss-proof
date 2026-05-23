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

## ビルド

```
isbman build -d . -v PSS
```

## 出典・引用 (Reference)

本プロジェクトが形式化の対象とする原論文：

> P進大好きbot. 「ペア数列の停止性」. 巨大数研究 Wiki, 2018年11月11日.
> https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7

BibTeX:

```bibtex
@misc{pshinkdaisukibot2018pairseq,
  author       = {P進大好きbot},
  title        = {ペア数列の停止性},
  howpublished = {巨大数研究 Wiki},
  year         = {2018},
  month        = {11},
  day          = {11},
  url          = {https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7}
}
```

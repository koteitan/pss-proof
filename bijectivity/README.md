[← Back](../README.md)

# bijectivity/ — 変換写像 `Trans` の全単射性

Naruyoko,「ペア数列システムの停止性証明に用いられた変換写像の全単射性」,
巨大数研究 Wiki ユーザーブログ, 2022-07-27
（[原文](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Naruyoko/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%82%B7%E3%82%B9%E3%83%86%E3%83%A0%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7%E8%A8%BC%E6%98%8E%E3%81%AB%E7%94%A8%E3%81%84%E3%82%89%E3%82%8C%E3%81%9F%E5%A4%89%E6%8F%9B%E5%86%99%E5%83%8F%E3%81%AE%E5%85%A8%E5%8D%98%E5%B0%84%E6%80%A7)）
の Lean 4 形式化。

主定理: \(\textrm{Trans}\) は
\(CT_{\textrm{PS}}\to\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}\)
上で全域かつ全単射であり、特に同型写像である。

## 方針

**原文に忠実**であることを目的とする。定理が証明できればよいのではなく、
原文と同じ証明をたどる。したがって原文が順序数（評価写像 \(o\)、\(\psi\)、
\(\textrm{cof}\)）を用いる箇所は、順序数を用いない別証明に置き換えない。

原文の命題 1 つ = ファイル 1 つ。ファイル名の数字は原文中の出現順。
各ファイルの docstring に原文の言明と証明を引用してある。

## 構成

`bijectivity/lean/Bijectivity/` に置き、既存の `lean` パッケージの
`lean_lib «Bijectivity»`（`srcDir = "../bijectivity/lean"`）としてビルドする。
`T_PS`、`Lng`、`Pred`、`M[n]`、`ST_PS`、`Trans`、`OT`、`OT_B` 等は既存の `PSS`
名前空間のものを再利用する。`OT_{\textrm{B}\omega}`（\(D_\omega\) を許す順序数項）は
既存の `PSS.OT` がそのまま該当する。

| ファイル | 内容 |
|---|---|
| `Defs.lean` | この記事で新たに導入される記法 \(<_{\textrm{PS}}\)、\(\leq_{\textrm{PS}[]}\)、\(CT_{\textrm{PS}}\) |
| `Cited.lean` | **外部引用**（評価写像 \(o\)、\(\psi_0\psi_\omega0\) ほか）を `axiom` として隔離 |
| `01`–`14` | ペア数列上の順序論（`12a`–`12c` は `12` の補助） |
| `15`–`22` | \(\textrm{Trans}\) 側および順序数側 |
| `23` | 主定理 |

外部引用を `axiom` として 1 ファイルに隔離してあるので、各定理が何を仮定しているかは
`#print axioms` で機械的に追跡できる。

## 状態: **`16` 以外は全部証明済み**

`bijectivity/lean/Bijectivity/` に残る `sorry` は **3 か所だけ**である。

| 場所 | 種類 |
|---|---|
| `16-fseq-relation.lean` | **唯一の未証明命題**（下記） |
| `05-exp-implies-lex.lean` | 逐語形が**偽**（訂正 `B1`、訂正形は証明済み・何からも使われない） |
| `11-path-to-initial-segment.lean` | 逐語形が**偽**（訂正 `B2`、同上） |

したがって原文の 23 命題は、**`16` を仮定すれば全部証明されている**。
主定理 `trans_bijOn` の `#print axioms` は `sorryAx`（`16` 由来のみ）と
`Cited.lean` の外部引用と標準 3 公理だけを挙げる。

### 外部引用に依存しない部分

`01`–`16` のうち `16` 以外、および `18`,`19`,`20`,`23` の同型写像・全域性・単射性は
**外部引用ゼロ・`sorry` ゼロ**である。特に

\[
\textrm{Trans}:CT_{\textrm{PS}}\longrightarrow
\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}
\]

が **well-defined かつ単射な順序同型埋め込み**であること
（`trans_mapsTo` / `trans_injOn` / `trans_order_iso`）は完全に機械検証されている。

### 外部引用に依存する部分

順序数側（`17`,`21`,`22`,`23` の全射性）は `Cited.lean` の 8 本の `axiom` を使う。
いずれも原文が [Buc1]/[Buc2] から引くと明記している事実で、原文が使う形のまま置いてある。

| axiom | 出典 |
|---|---|
| `o` / `psi0psiOmega0` / `o_DzeroDomegaZero` | [Buc1] の評価写像と \(\psi_0\psi_\omega0\) |
| `o_lt_of_lessBT` / `o_surj_below` | [Buc1] Lemma 2.2(c)（\(o\) が順序同型） |
| `o_BZero` / `o_DzeroZero` / `o_addBT` | [Buc1] の加法標準形 |
| `o_iSup_operB` | [Buc2] Theorem 1.4(a) / Lemma 1.6 |

原文が全射性で引く **[3] の命題 11 は公理化していない**。非有界性・
命題（後続な項の基本列）・命題（基本列の収束性）から超限帰納で直接証明してある
（`21-ordinal-bijectivity.lean` の `oTrans_surjOn`）。

### 残る `16`

原文: 任意の \(M\in ST_{\textrm{PS}}\) と \(m\) に対し、
\(\textrm{dom}(\textrm{Trans}(M))=\omega\) ならばある \(n\in\mathbb{N}_+\) が存在して
\(\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])\)。

必要なのは [1] の 条件 (I)–(VI) の下での \(\textrm{Trans}\) と基本列の交換関係のうち

* 条件 (I) → 結論 (1)（**Lean 済**: `8/8.1-Trans-fseq-condI.lean` の `p_8_1_Trans_fseq_condI`）
* 条件 (II) → 結論 (2)（未移植）
* 条件 (III)/(IV) → 結論 (3)（未移植）
* 条件 (V) → 結論 (3)（未移植）
* 条件 (VI) → 結論 (2)（未移植）

の 5 本。Lean 側の §8 は停止性に必要な**降下側だけ**を移植しており
（`8/8.3-Trans-fseq-condII.lean` の MODELLING NOTE）、条件 (I) 以外は (1)–(3) が
deferred のままである。`8/8.7-fseq-descend.lean` の `FseqDesc_exchI`〜`exchVI` は
無条件に証明済みだが**向きが逆**（`Trans(M[n]) ≤ Trans(M)[k]`）で `16` には使えない。
Isabelle 側には `y3j_p_8_3_condII_exchange_1/2/3` 等の形で存在するので、移植が残作業。

## 原文への訂正案

形式化の過程で見つかった原文の訂正案は [`corrections.md`](corrections.md) に集約している
（現在 3 件）。

| id | 内容 |
|---|---|
| `B1` | 命題（辞書式的順序が基本列的順序を含意すること）に \(\textrm{Lng}(N)>1\) が要る |
| `B2` | 補題（標準形の始切片への経路）の結論は \(\leq_{\textrm{PS}[]}\) |
| `B3` | 命題（基本列的順序が辞書式的順序を含意すること）の内側の帰納法に基底段階が無い |

## ビルド

```
cd lean && lake build Bijectivity
```

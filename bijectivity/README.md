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

## 証明済み

`#print axioms` が標準 3 公理のみ（`sorryAx` なし）:

`01` 系（辞書式的順序が辞書式順序であること）、
`02` 系（辞書式的順序の線形性）、
`03` 命題（基本列的順序が推移性）、
`04` 命題（基本列の辞書式的縮小性）、
`05` 命題（辞書式的順序が基本列的順序を含意すること）**の訂正形**、
`06` 命題（基本列の切片の不変性）、
`07` 命題（展開と `Pred` の関係）、
`08` 補題（最左列の不変性）、
`09` 補題（標準形と基本列的順序の関係）、
`10` 命題（可算な標準形の起源）、
`11` 補題（標準形の始切片への経路）**の訂正形**、
`12` 命題（基本列的順序が辞書式的順序を含意すること）、
`13` 系（順序の等価性）、
`14` 系（順序の線形性）、
`15` 命題（後続な項の基本列）の後半 `successor_fseq_of_last_zero`、
`18` 命題（\(\textrm{Trans}\) が順序を保つこと）、
`19` 補題（対応する項の上界未満の字母）、
`20` 命題（対応する項の上界）(1)(2)、
`21`,`22`,`23` の**全域性（`MapsTo`）と単射性（`InjOn`）**、
`23` 定理（変換写像の全単射性）の同型写像部分 `trans_order_iso` と
定義域・値域の被覆 `ctps_cover` / `transRange_cover`。

すなわち **ペア数列上の順序論（`01`–`14`）は完了**しており、
\(\leq_{\textrm{PS}}\) と \(\leq_{\textrm{PS}[]}\) が \(CT_{\textrm{PS}}\) 上で
一致する全順序であること、および

\[
M<_{\textrm{PS}}N\iff\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(N)
\quad(M,N\in CT_{\textrm{PS}})
\]

が機械検証されている。さらに主定理については

\[
\textrm{Trans}:CT_{\textrm{PS}}\longrightarrow
\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}
\]

が**well-defined かつ単射な順序同型埋め込み**であることが、外部引用ゼロ・`sorry` ゼロで
証明されている（`trans_mapsTo` / `trans_injOn` / `trans_order_iso`）。
`18` は既存の `lean/8/8.7-termination.lean` の `Trans_fseq_descend`（仮定 0、`sorry` 0）、
`23` の全域性は同 `Trans_STPS_OT_B` を用いる。

残るのは**全射性だけ**であり、依存は

```
23 SurjOn ← 22(2) SurjOn ← 21 SurjOn ← { 15 前半, 17 } ,  17 ← 16
```

と一本道に整理済み（帰着は証明済み。`23` の全射性は原文どおり 系（ペア数列の解析）(2)
へ機械的に帰着してある）。

残りは言明を逐語転記した上で `sorry` を置いてある（各ファイルに原文の証明を引用済み）。

| | 残っている部分 |
|---|---|
| `15` 後続な項の基本列 | **前半のみ**。\(\textrm{dom}(\textrm{Trans}(M))=1\Rightarrow M_{\textrm{Lng}(M)-1}=(0,0)\)（\(\textrm{Trans}\) の値の形からペア数列の形への読み戻し）。原文は [1] の 系（\(\textrm{Trans}\) と非可算基数の関係）から導くが、その系は repo に移植されていない。後半 `successor_fseq_of_last_zero` は証明済み |
| `16` 基本列の関係 | [1] の条件 (I)–(VI) の下での \(\textrm{Trans}\) と基本列の交換関係（`lean/8/8.1`–`8.6`）を全部束ねる必要がある |
| `17` 基本列の収束性 | `16` 待ち。加えて [5] Theorem 1.4(a) / Lemma 1.6 を `Cited.lean` に足す必要がある |
| `21`,`22`,`23` の全射性 | 上の一本道のとおり `15` 前半と `17` 待ち。加えて [4] Lemma 2.2(c) の全射側・2.3(b)（\(\textrm{dom}=\textrm{cof}\)）を `Cited.lean` に足す必要がある |

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

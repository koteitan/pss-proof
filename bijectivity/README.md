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
| `15`–`22` | \(\textrm{Trans}\) 側および順序数側（`16a`–`16d` は `16` の補助） |
| `23` | 主定理 |

外部引用を `axiom` として 1 ファイルに隔離してあるので、各定理が何を仮定しているかは
`#print axioms` で機械的に追跡できる。

## 状態: **原文の 23 命題すべてを証明済み**

`bijectivity/lean/Bijectivity/` に残る `sorry` は **2 か所だけ**で、どちらも
**原文の言明が偽である**ために意図的に残した逐語形である（訂正形は証明済みで、
下流はそちらを使う）。

| 場所 | 種類 |
|---|---|
| `05-exp-implies-lex.lean` | 逐語形が**偽**（訂正 `B1`、訂正形 `ltExpPS_ltPS_of_lng` は証明済み） |
| `11-path-to-initial-segment.lean` | 逐語形が**偽**（訂正 `B2`、訂正形は証明済み） |

主定理 `trans_bijOn` の `#print axioms` は `Cited.lean` の外部引用 8 本と
標準 3 公理だけを挙げる（**`sorryAx` は現れない**）。

### 外部引用に依存しない部分

`01`–`16` と `18`,`19`,`20`、および `23` の同型写像・全域性・単射性は
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
| `o_iSup_operB` | [Buc2] Theorem 1.4(a) / Lemma 1.6（`Audit-operB.lean` で経験検証） |

原文が全射性で引く **[3] の命題 11 は公理化していない**。非有界性・
命題（後続な項の基本列）・命題（基本列の収束性）から超限帰納で直接証明してある
（`21-ordinal-bijectivity.lean` の `oTrans_surjOn`）。

#### 🚨 公理はすべて \(OT_{\textrm{B}\omega}\) 上でしか主張していない

`BT`（Buchholz 項の型）全体では \(<_{\textrm{B}}\) は**整礎ではない**。
`lessBT (D_0 t) (D_0 t') = lessBT t t'` かつ任意の \(t\) に対して
\(D_0t<_{\textrm{B}}D_10\) なので、\(x_0=D_10\)、\(x_{n+1}=D_0x_n\) が
無限降下列になる（`Cited.lean` の `descChain` / `descChain_lt` で機械検証、
`descChain_not_OT` のとおり \(n\geq2\) で順序数項から外れる）。

したがって \(o\) の単調性を `BT` 全体で述べると順序数の無限降下列が作れて
**公理系が矛盾する**。`o_lt_of_lessBT` / `o_addBT` / `o_iSup_operB` には
`OT` の仮定を付けてある（`o_addBT` は和が入ることも要る。`o_addBT` と
`o_iSup_operB` は使う場所がすべて \(OT_{\textrm{B}}\) なので、そちらに絞ってある）。
この形なら模型がある: \((OT_{\textrm{B}\omega},<_{\textrm{B}})\) は [Buc1] により
整礎な線形順序なので順序型を持ち、\(o\) をその順序同型（`OT` の外では \(0\)）と
取ればすべての公理が成り立つ。

### `16`（補題（基本列の関係））の内訳

原文が引く [1] の 5 つの交換関係は、すべて `lean/8/` の無条件版から供給できた。

| 条件 | 原文が引く結論 | Lean での供給元 |
|---|---|---|
| (I) | (1) | `8/8.1-Trans-fseq-condI` の `condI_exchange1`（＋ `scx_condI_j0pos_masterCF`） |
| (II) | (2) | `16d-condII-fseq-rel.lean`（`8/8.3-condII-masterCF` の `condII_masterCF_exact_of_tailval` から数え上げを逆に解く） |
| (III)/(IV) | (3) | `8/8.4-Trans-fseq-condIII-IV` の `Trans_oper_exchange` 第 2 結論 |
| (V) | (3) | `8/8.5-Trans-fseq-condV-close` の `Trans_oper_exchange_condV_adm_uncond_vc` 第 4 結論（許容枝）／`ExchV_nf3x` の閉形式（非許容枝） |
| (VI) | (2) | `8/8.6-Trans-fseq-condVI-close` の `p_8_6_Trans_fseq_condVI_uncond` 第 2 結論 |

条件 (III)/(IV) の「\(j_1\) が段 1 に親を持たない」枝は
`Exch84_noParent_domTag_holds` が \(\textrm{dom}(\textrm{Trans}(M))=T_{e-1}\neq\omega\)
を与えるので、仮定の下では起こらない。

補助ファイル:

| ファイル | 内容 |
|---|---|
| `16a-fseq-addBT.lean` | \((t_0+t_1)[m]=t_0+(t_1[m])\) と複項 → 単項の帰着 |
| `16b-mono-fseq-rel.lean` | 単項の場合（\(t_1=0\) の 2 例 ＋ 条件 (I)–(VI)） |
| `16c-operB-mono.lean` | `operB` の添字単調性（Isabelle `y4_N_mono_le`）。条件 (V) 非許容枝の \(m=0\) 用 |
| `16d-condII-fseq-rel.lean` | 条件 (II) の交換関係 (2) |

## 監査（ビルド時ゲート）

[`lean/Bijectivity/Audit.lean`](lean/Bijectivity/Audit.lean) が原文 23 項目それぞれの
`#print axioms` の出力を `#guard_msgs` で固定している。どれかが `sorry` に依存し始めたり
（`sorryAx` が増える）、`Cited.lean` の外部引用が増えたりすると**ビルドが落ちる**。
Isabelle 側の `isabelle/8/audit.thy` にあたる。緑ビルド＝監査合格である。

`sorryAx` を期待しているのは `05` と `11` の**逐語形 2 本だけ**で、これは原文の言明が
偽であるため（訂正 `B1` / `B2`）。

[`lean/Bijectivity/Audit-operB.lean`](lean/Bijectivity/Audit-operB.lean) は残る外部引用の
うち深いほう `o_iSup_operB`（[Buc2] Theorem 1.4(a) ＝ 基本列の共終性）を、小さな
\(OT_{\textrm{B}}\) 項のプール上で全数検証する。本リポジトリの `operB` は
[Buc2] の定義そのものではなく**訂正 A23 を当てた形**なので、引用だけで済ませずに
確かめている（プール 496 項・\(\textrm{dom}=\omega\) の項 361 個で反例 0）。

## 原文への訂正案

形式化の過程で見つかった原文の訂正案は [`corrections.md`](corrections.md) に集約している
（現在 7 件、うち `B6`/`B7` は軽微）。

| id | 内容 |
|---|---|
| `B1` | 命題（辞書式的順序が基本列的順序を含意すること）に \(\textrm{Lng}(N)>1\) が要る |
| `B2` | 補題（標準形の始切片への経路）の結論は \(\leq_{\textrm{PS}[]}\) |
| `B3` | 命題（基本列的順序が辞書式的順序を含意すること）の内側の帰納法に基底段階が無い |
| `B4` | 補題（基本列の関係）の複項の場合の最後の計算は \(\leq_{\textrm{B}}\) で添字も違う |
| `B5` | 補題（基本列の関係）の条件 (V) 非許容枝では \(m=0\) が [1] の交換関係で覆えない |
| `B6` | 命題（対応する項の上界）(1) の連鎖の 1 つ目は \(\leq_{\textrm{B}}\)（軽微） |
| `B7` | 命題（対応する項の上界）(2) の \(D_0D_u=0\textrm{Trans}\) は誤植（軽微） |

## ビルド

```
cd lean && lake build Bijectivity
```

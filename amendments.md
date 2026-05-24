# 原文訂正案 (amendments to tmp/original.html)

巨大数研究 Wiki「ペア数列の停止性」(P進大好きbot 著) の**原文 HTML**
(`tmp/original.html`) に対する訂正案を集約する。著者へのフィードバック用。

- 原文はあくまで HTML（内部の LaTeX ソース）なので、訂正は HTML 内 LaTeX 記述
  に対する修正として記す。
- 位置は `original.html` のバイト位置と、整形テキスト `tmp/content.md` の行番号で示す。
- 形式化（Isabelle）側でどう扱ったかも併記する。
- 数式は MathJax 記法（`$...$` / `$$...$$`）で書く。

---

## A1. §5.4 命題（$F_M$ と基本列の関係）: 再帰先の第2引数 $n$ → $f(n)$

**位置**
- §5.4 ペア数列システム / 命題（$F_M$ と基本列の関係）
- `original.html` byte ≈ 192272（該当数式 $F_M(n) = F_{M[n]}(n)$）
- `content.md` line 380（(2)）, line 382（(3)）

**原文**
- (2) $(M[n],n) \in \textrm{Dom}(F)$
- (3) $(M,n) \in \textrm{Dom}(F)$ かつ $(M[n],n) \in \textrm{Dom}(F)$ かつ $F_M(n) = F_{M[n]}(n)$

**問題点**

§5.4 の $F$ の再帰的定義（`content.md` line 368 = `original.html` byte ≈ 191157）は

$$F_M(n) := F_{M[n]}(f(n))$$

と、再帰先の第2引数が $f(n)$。命題は同じ $n$ を使っており定義と矛盾する。

- 反例: $M = ((0,0),(0,0))$, $f(n)=n+1$, $n=1$。
  - 定義: $F_M(1) = F_{M[1]}(f(1)) = F_{((0,0))}(2) = f(2) = 3$。
  - 命題: $F_M(1) = F_{M[1]}(1) = F_{((0,0))}(1) = f(1) = 2$。
  - よって $3 \neq 2$ で矛盾。
- 補足: $\textrm{Lng}(M)=1$ のときは $M[n]=M$, $F_M(n)=f(n)=F_{M[n]}(n)$ なので原文の
  $n$ が正しい。$\textrm{Lng}(M)>1$ のときに $f(n)$ でなければならない。**単一の固定
  引数では両ケースを両立できない。**

**訂正案**

命題を $\textrm{Lng}(M)>1$ の場合に限定し、第2引数を $f(n)$ にする:
- (2) $(M[n],f(n)) \in \textrm{Dom}(F)$
- (3) $F_M(n) = F_{M[n]}(f(n))$
- （$\textrm{Lng}(M)=1$ の場合は $M[n]=M$ で自明なので除外して差し支えない）

**形式化での扱い**

`pss_paper.thy` の `p_5_4_F_oper_dom` / `p_5_4_F_oper_val` を訂正版
（$\textrm{Lng}\,M > 1$, 第2引数 $f\,n$）で記述し、`pss_mechanized.thy` の
`m_5_4_*` で証明済み。

---

## A2. §6.6 系（直系先祖による切片と $\textrm{Red}$ と $\textrm{IncrFirst}$ の関係）: 指数の添字 $m$ → $j'_0$

**位置**
- §6.6 簡約性 / 系（直系先祖による切片と $\textrm{Red}$ と $\textrm{IncrFirst}$ の関係）
- `content.md` line 1302（命題本文）

**原文**

$(M_j)_{j=j'_0}^{j'_1} = \textrm{IncrFirst}^{M_{0,m} - M_{1,m}}(N)$

**問題点**

ステートメント中の指数 $M_{0,m} - M_{1,m}$ に現れる添字 $m$ は、この系では
未定義（$m$ はこの命題のスコープに導入されていない）。証明本体（`content.md`
line 1308–1316）では一貫して $M_{0,j'_0} - M_{1,j'_0}$ を用いており、$m$ は
$j'_0$ の誤記と判断される。

**訂正案**

$(M_j)_{j=j'_0}^{j'_1} = \textrm{IncrFirst}^{M_{0,j'_0} - M_{1,j'_0}}(N)$

**形式化での扱い**

`pss_paper.thy` の `p_6_6_ancestor_slice_Red_IncrFirst` を訂正版
（指数 $\textrm{entry}\,M\,0\,j'_0 - \textrm{entry}\,M\,1\,j'_0$）で記述。

---

## A3. §6.4 系（$\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性）(4): 偽（反例あり）

**位置**
- §6.4 幹と枝 / 系（$\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性）の主張 (4)
- `content.md` line 791（主張 (4)）、line 793（証明）

**原文**

(4) 任意の $i \in \{0,1\}$ に対し $M_{i,\textrm{Joints}(M)_{J'_0}} > M_{i,\textrm{Joints}(M)_{J'_1}}$ である。

証明：（2）と（4）は $\textrm{FirstNodes}$ と $\textrm{TrMax}$ と $\textrm{Joints}$ の関係と（3）から即座に従う。

**問題点（主張 (4) は偽）**

主張 (4) は**狭義不等号** ($>$) だが、複数の枝が幹上の**同一の joint に接続**し得るため、
一般の $M \in PT_{\textrm{PS}}$ で成り立たない。反例（**標準形 $ST_{\textrm{PS}}$ かつ単項**、
`yaBMS` の `bms -s` で標準形と確認済）:

$$M = (0,0)(1,1)(2,1)(3,1)(2,0)$$

- $\textrm{TrMax}(M) = 1$（幹 = 索引 0,1）
- $\textrm{Br}(M) = [\,(2,1)(3,1),\ (2,0)\,]$（枝2本）
- $\textrm{FirstNodes}(M) = [2,4]$、$\textrm{Joints}(M) = [1,1]$（**両枝とも索引1で接続**）
- よって $J'_0=0 < J'_1=1$ で $M_{i,\textrm{Joints}_0} = M_{i,\textrm{Joints}_1} = M_{i,1}$ となり、
  $i\in\{0,1\}$ 両方で $M_{i,\textrm{Joints}_0} > M_{i,\textrm{Joints}_1}$（$1>1$）は**偽**。

証明文の「(3) から即座に従う」は、(3) が**弱い不等号** ($\geq$、$P$ の各成分の左端の
単調性 = 左端極小性経由で等号を許す) であるのに (4) で狭義性を主張しており、joint が
一致する一手を見落としている。標準形のペア数列を多数調べたところ、単項かつ枝2本以上の
ものの中に part (4) 違反が多数あり（いずれも joint 一致パターン）、上の最小反例はその一例。

**訂正案（候補）**

(4) を成立させるには追加の仮定（例: 連続枝の左端 $M_{0,\textrm{FirstNodes}_J}$ の**狭義**
減少、または許容性 $\textrm{Adm}$ 由来の joint 相異性）が要る。あるいは (4) を
**弱い不等号** $\geq$ に直す（(2) と幹の単調性から従う）。下流での (4) の用途を確認の上で
最小限の修正を選ぶべき（**TODO: `content.md` で (4) 狭義性の下流依存を精査**）。

**形式化での扱い**

`pss_paper.thy` の `p_6_4_FirstNodes_Joints_mono` を主張 (1)(2)(3) のみに弱める
（既証明 `m_6_4_FirstNodes_Joints_mono_aux` が discharge）。主張 (4) は本 amendment の
誤りとして除外。下流（§6.5 `Red` 等）では (4) を未使用のため波及なし。

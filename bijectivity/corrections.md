[← Back](README.md)

# 原文訂正案 (proposed corrections) — 全単射性の記事

Naruyoko「ペア数列システムの停止性証明に用いられた変換写像の全単射性」に対する訂正案を
集約する。著者へのフィードバック用。

- **対象記事**: Naruyoko「ペア数列システムの停止性証明に用いられた変換写像の全単射性」
  巨大数研究 Wiki ユーザーブログ, 2022.7.27.
  <https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Naruyoko/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%82%B7%E3%82%B9%E3%83%86%E3%83%A0%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7%E8%A8%BC%E6%98%8E%E3%81%AB%E7%94%A8%E3%81%84%E3%82%89%E3%82%8C%E3%81%9F%E5%A4%89%E6%8F%9B%E5%86%99%E5%83%8F%E3%81%AE%E5%85%A8%E5%8D%98%E5%B0%84%E6%80%A7>

訂正 id は [`diff/README.md`](diff/README.md) の監査 id をそのまま使う。
この文書が扱うのは、そのうち原文の字面を直す必要がある 3 分類である。

| 分類 | 条件 | 件数 |
|---|---|---|
| 🚨**X** | 原文をそのまま形式化すると矛盾する。本質的、または規模が大きい | 1 |
| ⚠️**Y** | 原文をそのまま形式化すると矛盾する。誤記の類 | 17 |
| 🚨**Z** | 原文に飛躍がある。飛躍が本質的で大きい | 1 |

残りの分類（W／S／R）は原文の字面を直す必要が無いので載せない。ただし一件だけ、
原文の一文が引用先で裏づけられていない W を末尾の[補足](#補足)に挙げる。

元記事「ペア数列の停止性」への訂正案 `A1`〜 は [`../corrections.md`](../corrections.md)。

## 🚨X-1. 命題（辞書式的順序が基本列的順序を含意すること）: $`\textrm{Lng}(N)\gt 1`$ の仮定が要る

### 位置
命題（辞書式的順序が基本列的順序を含意すること）

### 原文
任意の$`M,N\in CT_{\textrm{PS}}`$に対して、$`M\lt_{\textrm{PS}[]}N`$ならば$`M\lt_{\textrm{PS}}N`$である。

### 訂正案
任意の$`M,N\in CT_{\textrm{PS}}`$に対して、$`\textrm{Lng}(N)\gt 1`$かつ$`M\lt_{\textrm{PS}[]}N`$ならば$`M\lt_{\textrm{PS}}N`$である。

### 原文の問題点
原文は $`\lt_{\textrm{PS}[]}`$ を「$`a\neq()`$ なる $`a\in\mathbb{N}_+^{\lt\omega}`$ が存在して
$`M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]`$」と定義しているが、この定義は $`M\neq N`$ を
含意しない。$`\textrm{Lng}(N)=1`$ のとき $`N[n]=N`$ だからである。

- 反例: $`N=((0,0))\in CT_{\textrm{PS}}`$、$`a=(1)`$。
  - $`\textrm{Lng}(N)=1`$ より $`N[1]=N`$ なので $`M=N[1]=N=((0,0))`$。
  - $`M\lt_{\textrm{PS}[]}N`$ は（$`a=(1)\neq()`$ なので）成り立つ。
  - しかし $`M=N`$ なので $`M\lt_{\textrm{PS}}N`$ は偽。
- 原文の証明は「$`M=N`$ とすると条件と反する」とするが、それは上記の定義からは従わない。
- $`\textrm{Lng}(N)\gt 1`$ を補えば原文の証明がそのまま通る。

訂正の仕方は一意ではない。仮定に $`\textrm{Lng}(N)\gt 1`$（あるいは $`M\neq N`$）を足す道と、
$`\lt_{\textrm{PS}[]}`$ の定義自体を狭義になるよう直す道があり、前者を採ると下流の系
（順序の等価性）で $`\textrm{Lng}(N)\leq1`$ の場合を別扱いする分岐が要る。機械的な誤記の
訂正ではないので **X** とした。

### 形式化
`bijectivity/lean/Bijectivity/05-exp-implies-lex.lean`。逐語形が**偽であること**を
`not_ltExpPS_ltPS` として上の反例で証明してある。訂正形は `ltExpPS_ltPS_of_lng`。

## ⚠️Y-1. 命題（基本列の切片の不変性）: 証明が $`j_0,j_1`$ を二重の意味で使っている

### 位置
命題（基本列の切片の不変性）の証明。

### 原文
（命題）任意の$`M\in T_{\textrm{PS}}`$と$`j_0,j_1\in\mathbb{N}`$と$`m,n\in\mathbb{N}_+`$に対して、$`j_0\leq j_1`$かつ$`j_1\lt\textrm{Lng}(M[m])`$かつ$`j_1\lt\textrm{Lng}(M[n])`$ならば$`(M[m]_j)_{j=j_0}^{j_1}=(M[n]_j)_{j=j_0}^{j_1}`$である。

（証明の冒頭）$`\textrm{operator}[]`$の定義中の記号を$`M`$に対して定義する。

（証明中）よって$`m\neq n`$かつ$`j_1\gt 0`$かつ$`M_{j_1}\neq(0,0)`$かつある非負整数$`j_0`$が存在して$`(i_1,j_0)\lt^{\textrm{Next}}_M(i_1,j_1)`$であるとする。

### 訂正案
証明の冒頭を「$`\textrm{operator}[]`$の定義中の記号を$`M`$に対して$`j'_0,j'_1`$として定義する」
とし、定義側の意味で使っている箇所を $`j'_0,j'_1`$ に書き替える。すなわち

（証明中）よって$`m\neq n`$かつ$`j'_1\gt 0`$かつ$`M_{j'_1}\neq(0,0)`$かつある非負整数$`j'_0`$が存在して$`(i_1,j'_0)\lt^{\textrm{Next}}_M(i_1,j'_1)`$であるとする。

とする。$`\textrm{Lng}(M[n])=j'_0+n(j'_1-j'_0)`$ も同様。

### 原文の問題点
命題の $`j_0,j_1`$ は切片の端点で、仮定は $`j_0\leq j_1\lt\textrm{Lng}(M[m])`$ である。
一方、証明の冒頭「$`\textrm{operator}[]`$ の定義中の記号を $`M`$ に対して定義する」により
$`j_1:=\textrm{Lng}(M)-1`$、$`j_0:=`$ 一意な親、と同じ文字が再定義される。

- 証明中の「$`j_1\gt 0`$ かつ $`M_{j_1}\neq(0,0)`$ かつある非負整数 $`j_0`$ が存在して
  $`(i_1,j_0)\lt^{\textrm{Next}}_M(i_1,j_1)`$」は定義側の意味でしか読めない。
- 最後の「$`j_0\leq j_1\lt\textrm{Lng}(M[m])`$ であるから」は命題側の意味でしか読めない。
- 定義側の意味で読むと、非退化分岐では $`\textrm{Lng}(M[m])=j_0+m(j_1-j_0)`$ なので
  $`m=1`$ のとき $`\textrm{Lng}(M[1])=j_1`$ となり、仮定 $`j_1\lt\textrm{Lng}(M[m])`$ が偽になる。

直し方は定義側の記号を別名にするだけなので機械的である。

### 形式化
`bijectivity/lean/Bijectivity/06-fseq-segment-invariance.lean` の `oper_seg_invariance`。
命題の端点と定義中の親・末尾添字を別の変数にしている。

## ⚠️Y-2. 命題（展開と $`\textrm{Pred}`$ の関係）: $`\textrm{Lng}(M)\gt 1`$ の仮定が要る

### 位置
命題（展開と$`\textrm{Pred}`$の関係）

### 原文
任意の$`M\in T_{\textrm{PS}}`$と$`n\in\mathbb{N}_+`$に対し、$`j_1=\textrm{Lng}(M)-1`$と置くと、$`\textrm{Lng}(M[n])\geq j_1`$かつ$`(M[n]_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)`$である。

### 訂正案
任意の$`M\in T_{\textrm{PS}}`$と$`n\in\mathbb{N}_+`$に対し、$`j_1=\textrm{Lng}(M)-1`$と置くと、$`\textrm{Lng}(M)\gt 1`$ならば$`\textrm{Lng}(M[n])\geq j_1`$かつ$`(M[n]_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)`$である。

### 原文の問題点
$`\textrm{Lng}(M)=1`$ すなわち $`j_1=0`$ のとき、左辺 $`(M[n]_j)_{j=0}^{j_1-1}`$ は空区間の
切片すなわち空列であり、右辺は $`\textrm{Pred}(M)=M`$ で長さ $`1`$ なので等しくない。
第 1 主張 $`\textrm{Lng}(M[n])\geq0`$ のほうはこのとき自明に成り立つ。

この命題を使う次の 補題（最左列の不変性）は $`\textrm{Lng}(Q_k)=1`$ と
$`\textrm{Lng}(Q_k)\gt 1`$ に場合分けし、後者でしかこの命題を引かないので下流は変わらない。
なおこの仮定により、原文の場合分けのうち $`M[n]=M`$（定義の $`j_1=0`$ の分岐）は
起こらなくなり、退化枝は $`M[n]=\textrm{Pred}(M)`$ だけになる。

### 形式化
`bijectivity/lean/Bijectivity/07-oper-pred.lean` の `oper_take_pred`（仮定 `1 < Lng M`）。

## ⚠️Y-3. 補題（標準形と基本列的順序の関係）: 帰納段の添字が 1 つずれている

### 位置
補題（標準形と基本列的順序の関係）の証明 (⇐)。

### 原文
任意の非負整数$`i\lt\textrm{Lng}(a)`$に対して$`Q_0=((j,j))_{j=u}^v`$、$`Q_{i+1}=Q_i[a_i]`$とする。

（中略）任意の非負整数$`k\lt\textrm{Lng}(a)`$を取り、$`Q_k\in ST_{\textrm{PS}}`$であると仮定すると、$`Q_{k+1}=Q_k[a_{k+1}]\in ST_{\textrm{PS}}`$である。

### 訂正案
任意の非負整数$`k\lt\textrm{Lng}(a)`$を取り、$`Q_k\in ST_{\textrm{PS}}`$であると仮定すると、$`Q_{k+1}=Q_k[a_k]\in ST_{\textrm{PS}}`$である。

### 原文の問題点
$`Q_{i+1}=Q_i[a_i]`$ と定義しておきながら、帰納段では $`Q_{k+1}=Q_k[a_{k+1}]`$ と書いている。
定義どおりなら $`Q_{k+1}=Q_k[a_k]`$ である。$`k\lt\textrm{Lng}(a)`$ の範囲で
$`k=\textrm{Lng}(a)-1`$ を取ると $`a_{k+1}=a_{\textrm{Lng}(a)}`$ となり項が存在しないので、
そのままでは形式化できない。直し方は $`a_{k+1}`$ を $`a_k`$ に替えるだけで一意であり、
証明の構造は変わらない。

### 形式化
`bijectivity/lean/Bijectivity/09-standard-iff-exp.lean` の `stps_expand`
（$`N[(n)\oplus a']=(N[n])[a']`$ の形で定義どおりに回している）と `stps_iff_leExpPS`。

## ⚠️Y-4. 命題（可算な標準形の起源）: 包含 $`ST_{\textrm{PS}}\subset CT_{\textrm{PS}}`$ は向きが逆

### 位置
命題（可算な標準形の起源）の証明 (⇒) の冒頭。

### 原文
(⇒) $`ST_{\textrm{PS}}\subset CT_{\textrm{PS}}`$であるから、標準形と基本列的順序の関係より、ある$`u,v\in\mathbb{N}`$が存在して$`u\leq v`$かつ$`M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v`$である。

### 訂正案
(⇒) $`CT_{\textrm{PS}}\subset ST_{\textrm{PS}}`$であるから、標準形と基本列的順序の関係より、ある$`u,v\in\mathbb{N}`$が存在して$`u\leq v`$かつ$`M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v`$である。

### 原文の問題点
(⇒) で必要なのは $`M\in CT_{\textrm{PS}}`$ から $`M\in ST_{\textrm{PS}}`$ を出すこと、すなわち
$`CT_{\textrm{PS}}\subset ST_{\textrm{PS}}`$ である。原文の $`ST_{\textrm{PS}}\subset CT_{\textrm{PS}}`$
は実際に偽である。

- 反例: $`u=v=1`$ の対角列 $`((1,1))=((j,j))_{j=1}^1\in ST_{\textrm{PS}}`$。
  $`M_0=(1,1)\neq(0,0)`$ なので $`CT_{\textrm{PS}}`$ に属さない。

包含の向きを入れ替えるだけの機械的な訂正で、証明の構造は変わらない。

### 形式化
`bijectivity/lean/Bijectivity/10-countable-standard-origin.lean` の `ctps_iff_leExpPS`。
$`CT_{\textrm{PS}}`$ が連言そのものなので、正しい向きの包含は第 1 連言肢の取り出しになり、
補題として立てる必要が無い。

## ⚠️Y-5. 補題（標準形の始切片への経路）: 結論は $`\leq_{\textrm{PS}[]}`$

### 位置
補題（標準形の始切片への経路）

### 原文
任意の$`M\in ST_{\textrm{PS}}`$と$`j_1'\in\mathbb{N}`$に対し、$`j_1=\textrm{Lng}(M)-1`$と置くと、$`j_1'\leq j_1`$ならば$`(M_j)_{j=0}^{j_1'}\lt_{\textrm{PS}[]}M`$である。

### 訂正案
任意の$`M\in ST_{\textrm{PS}}`$と$`j_1'\in\mathbb{N}`$に対し、$`j_1=\textrm{Lng}(M)-1`$と置くと、$`j_1'\leq j_1`$ならば$`(M_j)_{j=0}^{j_1'}\leq_{\textrm{PS}[]}M`$である。

### 原文の問題点
$`j_1'=j_1`$ のとき $`(M_j)_{j=0}^{j_1'}=M`$ なので、原文の結論は $`M\lt_{\textrm{PS}[]}M`$ を
主張することになる。$`\textrm{Lng}(M)\gt 1`$ ではこれは偽である（$`M[1]=\textrm{Pred}(M)\neq M`$
であり、以降どれだけ展開しても $`M`$ には戻らない）。

原文自身、後の 命題（基本列的順序が辞書式的順序を含意すること）の証明では、この補題を
$`((j,j))_{j=0}^{v^M}\leq_{\textrm{PS}[]}((j,j))_{j=0}^v`$ と $`\leq`$ で用いている。
よって結論を $`\leq_{\textrm{PS}[]}`$ とするのが正しい。狭義にしたい場合は仮定を
$`j_1'\lt j_1`$ とする。

### 形式化
`bijectivity/lean/Bijectivity/11-path-to-initial-segment.lean`。逐語形が**偽であること**を
`not_seg_ltExpPS` として反例 $`M=((0,0),(1,1))`$, $`j_1'=1`$ で証明してある。
訂正形は `seg_leExpPS`。

## ⚠️Y-6. 命題（基本列的順序が辞書式的順序を含意すること）: 「高々 $`(j_1^N)^2`$ 個」は偽

### 位置
命題（基本列的順序が辞書式的順序を含意すること）の証明、$`f=j_1^N`$ の場合。

### 原文
従って$`\textrm{Lng}(M')=\textrm{Lng}(N)`$かつ$`(M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}`$である$`M'\in CT_{\textrm{PS}}`$は高々$`(j_1^N)^2`$個である。

### 訂正案
従って$`\textrm{Lng}(M')=\textrm{Lng}(N)`$かつ$`(M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}`$である$`M'\in CT_{\textrm{PS}}`$は高々$`(j_1^N+1)(j_1^N+2)/2`$個である。

### 原文の問題点
条件を満たす $`M'`$ は最後の対 $`(M'_{0,j_1^N},M'_{1,j_1^N})`$ だけで決まり、直前の行で得た
$`M'_{1,j_1^N}\leq M'_{0,j_1^N}\leq j_1^N`$ から候補は $`(j_1^N+1)(j_1^N+2)/2`$ 個以下である。
これは $`j_1^N\leq3`$ では $`(j_1^N)^2`$ を上回る。

- 反例: $`j_1^N=1`$（$`\textrm{Lng}(N)=2`$、$`N_0=(0,0)`$）のとき、
  $`((0,0),(0,0))`$、$`((0,0),(1,0))`$、$`((0,0),(1,1))`$ の 3 個がいずれも
  $`CT_{\textrm{PS}}`$ に属する（$`((0,0),(1,1))=((j,j))_{j=0}^{1}`$、
  $`((0,0),(1,0))=((j,j))_{j=0}^{1}[2]`$、$`((0,0),(0,0))=((j,j))_{j=0}^{1}[2][2]`$）。
  $`(j_1^N)^2=1`$ を超える。

原文がこの評価から使うのは有限性だけなので、個数を直せば下流は変わらない。

### 形式化
`bijectivity/lean/Bijectivity/12b-ctps-finite.lean` の `ctps_finite`。個数は数えず、
$`\{M'\in CT_{\textrm{PS}}\mid\textrm{Lng}(M')\leq L\}`$ の有限性を示している。

## ⚠️Y-7. 命題（基本列的順序が辞書式的順序を含意すること）: $`M\lt_{\textrm{PS}}N'[a_{g_0}]`$ は $`\leq_{\textrm{PS}}`$

### 位置
命題（基本列的順序が辞書式的順序を含意すること）の証明、$`g_0`$ を取った直後。

### 原文
辞書式的順序が基本列的順序を含意することより$`M\lt_{\textrm{PS}}N'[a_{g_0}]\lt_{\textrm{PS}}N`$である。

### 訂正案
辞書式的順序が基本列的順序を含意することより$`M\leq_{\textrm{PS}}N'[a_{g_0}]\lt_{\textrm{PS}}N`$である。

### 原文の問題点
$`M=N'[a_{g_0}][a_{g_0+1}]\cdots[a_{\textrm{Lng}(a)-1}]`$ なので、$`g_0=\textrm{Lng}(a)-1`$ の
ときは $`M=N'[a_{g_0}]`$ であり狭義にはならない。$`g_0=\textrm{Lng}(a)-1`$ は実際に起こりうる
（$`a`$ の最後の 1 手で初めて $`N`$ を下回る場合）。

下流でこの不等式を使うのは最後の挟み撃ちだけで、そこは $`\leq_{\textrm{PS}}`$ で足りる。

### 形式化
`bijectivity/lean/Bijectivity/12c-big-step.lean` の `big_step`。反復展開が
$`\leq_{\textrm{PS}}`$ を下げることから $`M\leq_{\textrm{PS}}N'[a_{g_0}]`$ を得ている。

## ⚠️Y-8. 命題（後続な項の基本列）: 「$`P(M)_{J_1}`$ は単項であり」は「非複項であり」

### 位置
命題（後続な項の基本列）の証明、$`M`$ が複項である場合。

### 原文
[1]の$`P`$の各成分の非複項性、$`\textrm{Trans}`$が零項性を保つこと、$`\textrm{Trans}`$が単項性を保つこと、$`\textrm{Trans}`$の定義及び仮定より$`P(M)_{J_1}`$は単項であり、かつ$`P(M)_{J_1}=((0,0))`$または$`\textrm{Trans}(P(M)_{J_1})=D_00`$である。

### 訂正案
[1]の$`P`$の各成分の非複項性、$`\textrm{Trans}`$が零項性を保つこと、$`\textrm{Trans}`$が単項性を保つこと、$`\textrm{Trans}`$の定義及び仮定より$`P(M)_{J_1}`$は非複項であり、かつ$`P(M)_{J_1}=((0,0))`$または$`\textrm{Trans}(P(M)_{J_1})=D_00`$である。

### 原文の問題点
原文はここで $`P(M)_{J_1}`$ が単項であると述べ、その直後に $`P(M)_{J_1}=((0,0))`$ と
結論する。$`((0,0))`$ は零項であって単項ではないので、この 2 文をそのまま形式化すると
矛盾する。

[1] の $`P`$ の各成分について言えるのは非複項性（零項または単項）であり、
$`P(M)_{J_1}=((0,0))`$ を排除できるのは $`\textrm{Trans}(P(M)_{J_1})=D_00`$ を仮定した
第 2 の選言肢の中だけである。「単項」を「非複項」に替えるか、「単項であり」を第 2 の
選言肢の中へ移すかで直る。

### 形式化
`bijectivity/lean/Bijectivity/15-successor-fseq.lean` の `successor_fseq`。末尾ブロックを
非複項として扱い、$`((0,0))`$ かどうかで場合分けしてから、$`((0,0))`$ でない側でのみ
零項性を排除して単項に絞る。

## ⚠️Y-9. 命題（後続な項の基本列）: 最後の等式の切片の添字が誤植

### 位置
命題（後続な項の基本列）の証明の末尾。

### 原文
上より$`\textrm{Trans}(M)=\textrm{Trans}((M_j)_{j_0}^{j_0-1})+D_00=\textrm{Trans}((M_j)_{j_0}^{j_1-1})+D_00=\textrm{Trans}(\textrm{Pred}(M))+D_00=\textrm{Trans}(M[n])+D_00`$である。

### 訂正案
上より$`\textrm{Trans}(M)=\textrm{Trans}((M_j)_{j=0}^{j_0-1})+D_00=\textrm{Trans}((M_j)_{j=0}^{j_1-1})+D_00=\textrm{Trans}(\textrm{Pred}(M))+D_00=\textrm{Trans}(M[n])+D_00`$である。

### 原文の問題点
原文の他の箇所では切片を $`(M_j)_{j=0}^{j_1-1}`$ のように「$`j=`$」付きで書いている。
ここは $`(M_j)_{j=0}^{j_0-1}`$ と $`(M_j)_{j=0}^{j_1-1}`$ の誤植である。字義どおりに読むと
最初の切片は $`j`$ が $`j_0`$ から $`j_0-1`$ までの空列になり、$`\textrm{Trans}`$ の定義の
複項枝（$`\textrm{Trans}(M)=\textrm{Trans}((M_j)_{j=0}^{j_0-1})+D_00`$）とも合わない。

### 形式化
`bijectivity/lean/Bijectivity/15-successor-fseq.lean` の `successor_fseq`。
$`(M_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)`$ の形で使う。

## ⚠️Y-10. 補題（基本列の関係）: 複項の場合の最後の計算は $`\leq_{\textrm{B}}`$ で添字も違う

### 位置
補題（基本列の関係）の証明、$`M`$ が複項である場合の末尾。

### 原文
よって

```math
\begin{array}{l}\textrm{Trans}(M)[m]\cr =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1}[m]\cr =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+(P(M)_{J_1}^+[m])\cr =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+(\textrm{Trans}(P(M)_{J_1})[m])\cr =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+\textrm{Trans}(P(M)_{J_1}[m])\cr =\textrm{Trans}(M[m])\cr \leq_{\textrm{B}}\textrm{Trans}(M[m])\end{array}
```

である。

### 訂正案
上より $`m`$ に対しある $`n\in\mathbb{N}_+`$ が存在して $`\textrm{Trans}(P(M)_{J_1})[m]\leq_{\textrm{B}}\textrm{Trans}(P(M)_{J_1}[n])`$ である。この $`n`$ に対して

```math
\begin{array}{l}\textrm{Trans}(M)[m]\cr =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+(\textrm{Trans}(P(M)_{J_1})[m])\cr \leq_{\textrm{B}}\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+\textrm{Trans}(P(M)_{J_1}[n])\cr =\textrm{Trans}(M[n])\end{array}
```

である。

### 原文の問題点
直前で示した単項の場合の結論は「ある $`n\in\mathbb{N}_+`$ が存在して
$`\textrm{Trans}(P(M)_{J_1})[m]\leq_{\textrm{B}}\textrm{Trans}(P(M)_{J_1}[n])`$」であって、
$`n=m`$ とは限らず、また等号ではない。原文の 4 行目は
$`\textrm{Trans}(P(M)_{J_1})[m]=\textrm{Trans}(P(M)_{J_1}[m])`$ を使っており、これは
単項の場合の結論より強い（実際、条件 (III)/(IV)/(V) では等号は成り立たない）。

$`+_{\textrm{B}}`$ は右引数について狭義単調（$`t_0+t_1\lt_{\textrm{B}}t_0+t_1'`$ if
$`t_1\lt_{\textrm{B}}t_1'`$）なので、$`\leq_{\textrm{B}}`$ と添字 $`n`$ をそのまま持ち上げれば
結論は変わらない。

### 形式化
`bijectivity/lean/Bijectivity/16a-fseq-addBT.lean` の `fseq_relation_of_mono`。

## ⚠️Y-11. 補題（基本列の関係）: $`(D_0D_10)[n]`$ は $`D_0`$ 1 個ぶん多い

### 位置
補題（基本列の関係）の証明、単項で $`t_1=0`$、$`M=((0,0),(1,1))`$ の例。

### 原文
$`\textrm{dom}(D_10)=\Omega_1`$であるから$`[]`$の定義より任意の$`n\in\mathbb{N}`$に対して$`(D_0D_10)[n]=D_0D_0^nD_0D_00=D_0^{n+3}0`$である。

### 訂正案
$`\textrm{dom}(D_10)=\Omega_1`$であるから$`[]`$の定義より任意の$`n\in\mathbb{N}`$に対して$`(D_0D_10)[n]=D_0D_0^{n+1}0=D_0^{n+2}0`$である。

### 原文の問題点
$`[]`$ の第 1 種の枝は $`a=D_vb`$、$`\textrm{dom}(b)=T_u`$、$`v\leq u`$ のとき
$`a[n]=D_v(b[x_n])`$、$`x_0=D_u0`$、$`x_{i+1}=D_u(b[x_i])`$（訂正 A23 後の読み）である。
いま $`v=u=0`$、$`b=D_10`$ で $`b[y]=y`$ だから $`x_i=D_0^{i+1}0`$、
$`a[n]=D_0(x_n)=D_0^{n+2}0`$。原文の書き方 $`D_0D_0^nD_0D_00`$ は $`x_0=D_0D_00`$ と
置いたことに相当する。訂正前の脚注の読み（$`x_i=b[D_ux_{i-1}]`$）でも $`x_i=D_0^{i+1}0`$ で
結果は $`D_0^{n+2}0`$ なので、どちらの読みでも $`n+3`$ にはならない。

結論 $`\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[m+3])`$ 自体は
$`D_0^{m+2}0\leq_{\textrm{B}}D_0^{m+3}0`$ なので真のままである。

### 形式化
`bijectivity/lean/Bijectivity/16-fseq-relation.lean` の `fseq_relation`。等号が立つ
$`n=m+2`$ を取る。

## ⚠️Y-12. 補題（基本列の関係）: $`\textrm{Trans}(M[n])=D_0^n0`$ は $`n=1`$ で偽

### 位置
補題（基本列の関係）の証明、単項で $`t_1=0`$、$`M=((0,0),(1,1))`$ の例。

### 原文
$`\textrm{Trans}(M)=D_0D_10`$かつ任意の$`n\in\mathbb{N}`$に対して$`\textrm{Trans}(M[n])=D_0^n0`$である。

### 訂正案
$`\textrm{Trans}(M)=D_0D_10`$かつ$`\textrm{Trans}(M[1])=0`$かつ任意の$`n\in\mathbb{N}`$に対して、$`n\neq1`$ならば$`\textrm{Trans}(M[n])=D_0^n0`$である。

### 原文の問題点
$`M=((0,0),(1,1))`$ のとき $`M[1]=\textrm{Pred}(M)=((0,0))`$ で $`\textrm{Trans}(M[1])=0`$
だが、$`D_0^10=D_00\neq0`$ である。

[1] の公差 $`(1,0)`$ の列の $`\textrm{Trans}`$ はこの例外を明示していて、
$`((u+j,u))_{j=0}^{k}`$ の $`\textrm{Trans}`$ は $`k=0`$ かつ $`u=0`$ のときだけ $`0`$、
それ以外は $`D_u^{k+1}0`$ である。原文はこの $`1`$ 例外を書かずに「任意の
$`n\in\mathbb{N}`$ に対して」と書いている。結論では $`n\geq3`$ しか使わないので
下流は変わらない。

### 形式化
`bijectivity/lean/Bijectivity/16-fseq-relation.lean` の `fseq_relation`
（例外込みの `PSS.FseqDesc_m_8_6_rcseq_Trans_holds` を引いている）。

## ⚠️Y-13. 補題（基本列の関係）: $`PT_{\textrm{PS}}\cup ST_{\textrm{PS}}`$ の $`\cup`$ は $`\cap`$

### 位置
補題（基本列の関係）の証明、$`M`$ が複項である場合。

### 原文
[1]の$`P`$の各成分の非複項性及び標準形の単項成分が標準形であることより$`P(M)_{J_1}\in PT_{\textrm{PS}}\cup ST_{\textrm{PS}}`$である。

### 訂正案
[1]の$`P`$の各成分の非複項性及び標準形の単項成分が標準形であることより$`P(M)_{J_1}\in PT_{\textrm{PS}}\cap ST_{\textrm{PS}}`$である。

### 原文の問題点
直前で示した中間結論は「任意の $`M\in PT_{\textrm{PS}}\cap ST_{\textrm{PS}}`$ に対して…」で
あり、その次の行でそれを $`P(M)_{J_1}`$ に適用するのだから、必要なのは
$`P(M)_{J_1}\in PT_{\textrm{PS}}\cap ST_{\textrm{PS}}`$ である。$`\cup`$ では適用できない。

引かれている 2 つの事実（[1] の $`P`$ の各成分の非複項性、標準形の単項成分が標準形で
あること）もそれぞれ単項性と標準形性を別々に与えるので、結論は $`\cap`$ になる。

### 形式化
`bijectivity/lean/Bijectivity/16-fseq-relation.lean` の `fseq_relation`。標準形性と
単項性を別々に立てている。

## ⚠️Y-14. 補題（対応する項の上界未満の字母）: 証明中の $`T_{\textrm{PS}}`$ は $`T_{\textrm{B}}`$

### 位置
補題（対応する項の上界未満の字母）の証明、$`t=0`$ の場合・単項の場合・複項の場合・
まとめの行・最終行の 5 箇所。

### 原文
$`t=0`$ならば$`t\in T_{\textrm{PS}}`$である。

（中略）上より$`a`$は字母$`D_\omega`$を含まないから$`t\in T_{\textrm{PS}}`$である。

（中略）上より任意の非負整数$`0\leq i\lt\textrm{Lng}(a)`$に対して$`a_i`$は字母$`D_\omega`$を含まないから$`t\in T_{\textrm{PS}}`$である。

よっていずれの場合でも$`t\in T_{\textrm{PS}}`$である。

よって$`t\in OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{PS}}`$である。

### 訂正案
5 箇所の $`T_{\textrm{PS}}`$ をすべて $`T_{\textrm{B}}`$ に置き換える。すなわち最終行は

よって$`t\in OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}`$である。

とする。

### 原文の問題点
$`t`$ は Buchholz の項であって、ペア数列全体 $`T_{\textrm{PS}}`$ の元ではない。ここで
示しているのは「$`t`$ が字母 $`D_\omega`$ を含まない」であるから、いずれも
$`T_{\textrm{B}}`$ が正しい。$`T_{\textrm{PS}}`$ をそのまま形式化すると、示すべき
$`t\in OT_{\textrm{B}}`$ が得られない。直し方は一意であり、証明の構造は変わらない。

### 形式化
`bijectivity/lean/Bijectivity/19-alphabet-below-bound.lean` の `OT_iff_OT_B_of_lt`。
$`OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}`$ を定義として採っている。

## ⚠️Y-15. 命題（対応する項の上界）(1): 結論の連鎖の 1 つ目は $`\leq_{\textrm{B}}`$

### 位置
命題（対応する項の上界）(1) の証明の最終行。

### 原文
$`\textrm{Trans}`$が順序を保つことより$`\textrm{Trans}(M)\lt_{\textrm{B}}\textrm{Trans}(((j,j))_{j=0}^v)\lt_{\textrm{B}}D_0D_\omega0`$である。

### 訂正案
$`\textrm{Trans}`$が順序を保つことより$`\textrm{Trans}(M)\leq_{\textrm{B}}\textrm{Trans}(((j,j))_{j=0}^v)\lt_{\textrm{B}}D_0D_\omega0`$である。

### 原文の問題点
直前の行で得ているのは $`M\leq_{\textrm{PS}}((j,j))_{j=0}^v`$（等号込み）なので、
命題（$`\textrm{Trans}`$ が順序を保つこと）から出るのは $`\leq_{\textrm{B}}`$ である。
$`M=((j,j))_{j=0}^v\in CT_{\textrm{PS}}`$ のとき両辺は等しいので $`\lt_{\textrm{B}}`$ は偽
（$`\lt_{\textrm{B}}`$ は非反射的）。

連鎖の 2 つ目が狭義なので結論 $`\textrm{Trans}(M)\lt_{\textrm{B}}D_0D_\omega0`$ は変わらない。

### 形式化
`bijectivity/lean/Bijectivity/20-term-upper-bound.lean` の `trans_lt_bound`。
$`((j,j))_{j=0}^{v+1}`$ を取り直して $`\leq_{\textrm{B}}`$ と
$`D_0D_v0\lt_{\textrm{B}}D_0D_{v+1}0`$ を合成している。

## ⚠️Y-16. 命題（対応する項の上界）(2): $`t'`$ の成分は $`OT_{\textrm{B}}`$ ではなく $`T_{\textrm{B}}`$

### 位置
命題（対応する項の上界）(2) の証明、$`t'`$ が単項の場合と複項の場合。

### 原文
ある$`u\in\mathbb{N}`$と$`a\in OT_{\textrm{B}}`$が存在して$`t'=D_ua`$である。

（中略）ある$`u\in\mathbb{N}`$と$`a\in OT_{\textrm{B}}`$と$`s\in\Sigma^{\lt\omega}`$が存在して$`t'=\underline{(}D_ua\underline{,}s\underline{)}`$である。

### 訂正案
ある$`u\in\mathbb{N}`$と$`a\in T_{\textrm{B}}`$が存在して$`t'=D_ua`$である。

（中略）ある$`u\in\mathbb{N}`$と$`a\in T_{\textrm{B}}`$と$`s\in\Sigma^{\lt\omega}`$が存在して$`t'=\underline{(}D_ua\underline{,}s\underline{)}`$である。

### 原文の問題点
そこでの仮定は $`t'\in T_{\textrm{B}}`$ だけであり、$`t'`$ が順序数項であるとは仮定されて
いないので、成分 $`a`$ が $`OT_{\textrm{B}}`$ に属する保証は無い。

- 反例: $`t'=D_0(\underline{(}D_00\underline{,}D_10\underline{)})`$ は $`\omega`$ を含まない
  単項な項だが、成分 $`\underline{(}D_00\underline{,}D_10\underline{)}`$ は principal 成分が
  広義降順でないので順序数項ではない。

原文自身、後半の $`t`$ についての分解では $`a\in T_{\textrm{B}}`$ と正しく書いている。
この $`a`$ は $`t'`$ についての議論のどこでも使われないため下流も変わらない。

### 形式化
`bijectivity/lean/Bijectivity/20-term-upper-bound.lean` の `exists_trans_gt`。
終始 $`T_{\textrm{B}}`$ で通している。

## ⚠️Y-17. 命題（対応する項の上界）(2): $`D_0D_u=0\textrm{Trans}`$ は誤植

### 位置
命題（対応する項の上界）(2) の証明の最終行。

### 原文
[1]の公差$`(1,1)`$のペア数列の$`\textrm{Trans}`$の基本性質より$`t\lt_{\textrm{B}}D_0D_u=0\textrm{Trans}(((j,j))_{j=0}^u)=D_0D_u0`$である。

### 訂正案
[1]の公差$`(1,1)`$のペア数列の$`\textrm{Trans}`$の基本性質より$`t\lt_{\textrm{B}}D_0D_u0=\textrm{Trans}(((j,j))_{j=0}^u)`$である。

### 原文の問題点
`D_0D_u=0\textrm{Trans}` は `D_0D_u0=\textrm{Trans}` の誤植（`0` と `=` の入れ替わり）。
また末尾の `=D_0D_u0` は同じ項の繰り返しなので削れる。

### 形式化
`bijectivity/lean/Bijectivity/20-term-upper-bound.lean` の `exists_trans_gt`
（`Trans_diagSeq_zero` が $`\textrm{Trans}(((j,j))_{j=0}^v)=D_0D_v0`$）。

## 🚨Z-1. 命題（基本列的順序が辞書式的順序を含意すること）: 内側の帰納法に基底段階が無い

### 位置
命題（基本列的順序が辞書式的順序を含意すること）の証明、
「$`\textrm{Lng}(N)`$及び$`(N_j)_{j=0}^{j_1^N-1}`$を固定したときの帰納法により」の箇所

### 原文
従って$`\textrm{Lng}(M')=\textrm{Lng}(N)`$かつ$`(M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}`$である$`M'\in CT_{\textrm{PS}}`$は高々$`(j_1^N)^2`$個である。

（…中略…）$`\textrm{Lng}(N)`$及び$`(N_j)_{j=0}^{j_1^N-1}`$を固定したときの帰納法により、任意の$`N'\in CT_{\textrm{PS}}`$に対して、$`N\leq_{\textrm{PS}}N'`$ならば$`M\lt_{\textrm{PS}[]}N'`$である。

### 訂正案
[1] の簡約性と係数の関係、条件(A)と(B)と係数の基本性質(1)及び(2)、標準形の簡約性及び$`CT_{\textrm{PS}}`$の定義より任意の$`M'\in CT_{\textrm{PS}}`$と非負整数$`j\lt\textrm{Lng}(M')`$に対して$`M'_{1,j}\leq M'_{0,j}\leq j`$である。

従って$`\textrm{Lng}(M')\leq L`$である$`M'\in CT_{\textrm{PS}}`$は有限個である。

（…中略…）$`L=\textrm{Lng}(M)`$と置いて$`\{M'\in CT_{\textrm{PS}}\mid\textrm{Lng}(M')\leq L\}`$上の$`\lt_{\textrm{PS}}`$に関する下降帰納法により、任意の$`N'\in CT_{\textrm{PS}}`$に対して、$`N\leq_{\textrm{PS}}N'`$ならば$`M\lt_{\textrm{PS}[]}N'`$である。

### 原文の問題点
原文の内側の帰納法は
$`S=\{M'\in CT_{\textrm{PS}}\mid\textrm{Lng}(M')=\textrm{Lng}(N)\land(M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}\}`$
という有限集合の上での $`\lt_{\textrm{PS}}`$ に関する**下降**帰納である。実際、証明の各段は
$`N`$ について結論が既知であるとして、$`S`$ の中で $`N`$ の直下にある $`M'`$ について結論を導いている。

しかし下降帰納には $`S`$ の $`\lt_{\textrm{PS}}`$-最大元での基底段階が要る。最大元 $`X`$ では
$`X`$ より上の元が $`S`$ に無いので帰納法の仮定が使えないが、結論
「任意の $`N'\in CT_{\textrm{PS}}`$ に対して $`X\lt_{\textrm{PS}}N'`$ ならば
$`X\lt_{\textrm{PS}[]}N'`$」は自明ではない（$`N'`$ は $`S`$ の外を動く）。原文はこの段階を扱っていない。

### 修正の要点
帰納の台を「長さと先頭 $`j_1^N`$ 項を固定した集合」から
$`\{M'\in CT_{\textrm{PS}}\mid\textrm{Lng}(M')\leq L\}`$ に取り替えればよい。

- この集合も有限である。原文が引く係数評価 $`M'_{1,j}\leq M'_{0,j}\leq j`$ が
  各添字 $`j`$ で成り立つので、長さ $`L`$ 以下の元は高々 $`\prod_{j\lt L}(j+1)^2`$ 個。
- 相手 $`N'`$ の長さは、原文の $`f`$ による帰着（$`N'`$ を $`(N'_j)_{j=0}^f`$ に置き換える操作）
  で $`\textrm{Lng}(M)`$ 以下に落とせるので、帰納の台の外に出ない。
- この台なら最大元 $`X`$ では $`X\lt_{\textrm{PS}}N'`$ なる $`N'`$ が台の中に存在しないため、
  主張が空虚に成り立ち、基底段階が自動的に閉じる。

それ以外の論法（$`f`$ による場合分け、共通の上界 $`((j,j))_{j=0}^v`$ の導入、$`g_0`$ の最小性、
$`N=N'`$ の導出）は原文のままでよい。

### 形式化
`bijectivity/lean/Bijectivity/12-lex-implies-exp.lean`（訂正形で証明済み）。
有限性は `12b-ctps-finite.lean` の `ctps_finite`、主要部は `12c-big-step.lean` の
`big_step`。

## 補足

分類 W（原文の飛躍が通常どおり小さいもの）は原文の字面を直す必要が無いので上に載せて
いないが、次の 1 件だけは原文の一文が引用先で裏づけられていないので挙げておく。

### W-34. 補題（基本列の関係）: 条件 (V) の非許容枝では $`m=0`$ が [1] の交換関係で覆えない

#### 位置
補題（基本列の関係）の証明、$`M`$ が単項で $`t_1\neq0`$、条件 (V) の場合。

#### 原文
$`M`$が条件(I)-(VI)を満たすとき、それぞれ[1]の条件(I)の下でのTransと基本列の交換関係(1)、条件(II)の下でのTransと基本列の交換関係(2)、条件(III)か(IV)の下でのTransと基本列の交換関係(3)、条件(V)の下でのTransと基本列の交換関係(3)及び条件(VI)の下でのTransと基本列の交換関係(2)よりある$`n\in\mathbb{N}_+`$が存在して$`\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])`$である。

#### 訂正案
（同文に次を補う）ただし条件 (V) で $`j_0`$ が $`M`$ 許容でない場合は $`m_n=n`$ であり、
$`n\in\mathbb{N}_+`$ より $`m_n\geq1`$ なので、$`m=0`$ は交換関係 (3) では覆えない。
この場合は $`[]`$ の単調性、すなわち $`\textrm{dom}(t)=\omega`$ なる $`t\in OT_{\textrm{B}\omega}`$
と $`m\leq m'`$ に対し $`t[m]\leq_{\textrm{B}}t[m']`$ であることから
$`\textrm{Trans}(M)[0]\leq_{\textrm{B}}\textrm{Trans}(M)[1]\leq_{\textrm{B}}\textrm{Trans}(M[2])`$
とすればよい。

#### 原文の問題点
[1] の 条件 (V) の下での $`\textrm{Trans}`$ と基本列の交換関係 (3) は
$`\textrm{Trans}(M)[m_n]\leq_{\textrm{B}}\textrm{Trans}(M[n+1])`$ の形で、
$`m_n=\textrm{if }j_0\text{ が }M\text{ 許容 then }n-1\text{ else }n`$ である。
許容枝では $`n=1`$ で $`m_n=0`$ となり $`m=0`$ も覆えるが、非許容枝では
$`n\geq1`$ に対し $`m_n=n\geq1`$ なので $`m=0`$ に対応する $`n`$ が無い。

他の 4 条件では $`m=0`$ も覆える（条件 (I) は $`n=1`$、条件 (II) は $`n=1`$ または $`2`$、
条件 (III)/(IV) は $`n=2`$、条件 (VI) は $`n=1`$ または $`2`$）。

#### 形式化
`bijectivity/lean/Bijectivity/16c-operB-mono.lean` の `operB_numBT_mono_holds`
（`lean/OTB-well-founded-syntactic/OTB-well-founded-syntactic-cofinality.lean` の
`y4_N_mono_le` への配線）。
使用箇所は `16b-mono-fseq-rel.lean` の `mono_fseq_rel` の条件 (V) 非許容枝。

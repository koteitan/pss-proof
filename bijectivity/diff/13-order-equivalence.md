[< back](README.md)

# 13: 系 (順序の等価性)

## 原文

### 命題

原文に命題番号は無く、見出しは「系 (順序の等価性)」である。

任意の $M,N\in CT_{\textrm{PS}}$ に対して、$M\leq_{\textrm{PS}}N$ は $M\leq_{\textrm{PS}[]}N$ と同値である。

### 証明

証明

基本列的順序が辞書式的順序を含意すること及び辞書式的順序が基本列的順序を含意することより即座に従う。□

## Lean

### Lean での命題

用いる定義は原文どおりである。反復展開を

$$\textrm{expand}(N,())=N,\qquad \textrm{expand}(N,(n)\frown a)=\textrm{expand}(N[n],a)$$

と書けば $\textrm{expand}(N,a)=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ であり、

$$M\leq_{\textrm{PS}[]}N:\Longleftrightarrow\exists a\in\mathbb{N}_+^{\lt\omega},~M=\textrm{expand}(N,a)$$

$$M\lt_{\textrm{PS}[]}N:\Longleftrightarrow\exists a\in\mathbb{N}_+^{\lt\omega}\setminus\lbrace()\rbrace,~M=\textrm{expand}(N,a)$$

$$M\leq_{\textrm{PS}}N:\Longleftrightarrow M=N\lor M\lt_{\textrm{PS}}N$$

$$CT_{\textrm{PS}}=\lbrace M\mid M\in ST_{\textrm{PS}}\land M_0=(0,0)\rbrace$$

である。証明されている主張は原文と同じで、

任意の $M,N$ に対して、$M\in CT_{\textrm{PS}}$ かつ $N\in CT_{\textrm{PS}}$ ならば

$$M\leq_{\textrm{PS}}N\Longleftrightarrow M\leq_{\textrm{PS}[]}N$$

である。

### Lean での証明

同値の 2 方向を別々に示す。

**($\Rightarrow$) $M\leq_{\textrm{PS}}N$ ならば $M\leq_{\textrm{PS}[]}N$。**
$\leq_{\textrm{PS}}$ の定義（$M=N$ または $M\lt_{\textrm{PS}}N$）で分岐する。

- $M=N$ のとき。$a=()$ を証拠に取る。$a\in\mathbb{N}_+^{\lt\omega}$ の条件「$a$ の各成分が
  $\geq1$」は成分が無いので空虚に成り立ち、$\textrm{expand}(N,())=N$ は $\textrm{expand}$ の
  定義の第 1 式そのものだから $M=N=\textrm{expand}(N,())$ である。よって $\leq_{\textrm{PS}[]}$ の
  定義から $M\leq_{\textrm{PS}[]}N$。この分岐では $M,N\in CT_{\textrm{PS}}$ を使わない。
- $M\lt_{\textrm{PS}}N$ のとき。仮定の $M\in CT_{\textrm{PS}}$、$N\in CT_{\textrm{PS}}$ を付けて
  基本列的順序が辞書式的順序を含意すること（任意の $M,N\in CT_{\textrm{PS}}$ に対して
  $M\lt_{\textrm{PS}}N$ ならば $M\lt_{\textrm{PS}[]}N$）を適用し、$M\lt_{\textrm{PS}[]}N$ を得る。
  その定義を開いて、$a\neq()$ かつ各成分が $\geq1$ かつ $M=\textrm{expand}(N,a)$ なる $a$ を取り、
  条件 $a\neq()$ だけを捨てて、同じ $a$ を $\leq_{\textrm{PS}[]}$ の証拠に使う。

**($\Leftarrow$) $M\leq_{\textrm{PS}[]}N$ ならば $M\leq_{\textrm{PS}}N$。**
$\leq_{\textrm{PS}[]}$ の定義を開き、各成分が $\geq1$ かつ $M=\textrm{expand}(N,a)$ なる
$a$ を取る。$a$ の形で場合分けする。

- $a=()$ のとき。$\textrm{expand}(N,())=N$ は $\textrm{expand}$ の定義の第 1 式だから $M=N$ であり、
  $\leq_{\textrm{PS}}$ の定義の等号側で閉じる。
- $a=(n)\frown a'$ のとき。さらに $\textrm{Lng}(N)$ で 2 分岐する（自然数の全順序性により
  $1\lt\textrm{Lng}(N)$ か $\textrm{Lng}(N)\leq1$ のいずれかである）。
  - $1\lt\textrm{Lng}(N)$ のとき。$a=(n)\frown a'\neq()$ なので、いま取った $a$ は
    そのまま $M\lt_{\textrm{PS}[]}N$ の証拠になる。これに、辞書式的順序が基本列的順序を
    含意することの訂正形（$\textrm{Lng}(N)\gt1$ かつ $M\lt_{\textrm{PS}[]}N$ ならば
    $M\lt_{\textrm{PS}}N$。$CT_{\textrm{PS}}$ は仮定しない）を $\textrm{Lng}(N)\gt1$ とともに
    適用して $M\lt_{\textrm{PS}}N$ を得、$\leq_{\textrm{PS}}$ の定義の狭義側で閉じる。
  - $\textrm{Lng}(N)\leq1$ のとき。自明展開（$\textrm{Lng}(N)\leq1$ ならば、成分に条件を課さない
    任意の $a$ に対して $\textrm{expand}(N,a)=N$）を列 $(n)\frown a'$ に適用すると
    $\textrm{expand}(N,(n)\frown a')=N$ である。$M=\textrm{expand}(N,a)$ とつないで $M=N$ を得、
    $\leq_{\textrm{PS}}$ の定義の等号側で閉じる。

この方向では $M,N\in CT_{\textrm{PS}}$ をどこでも使わない。

## 原文通りに書けなかった理由

- **[W]** 「即座に従う」は $\leq$ を $=$ と $\lt$ に開く場合分けを隠している

  原文が引く 2 命題はいずれも狭義の順序どうしの含意（$M\lt_{\textrm{PS}}N\Rightarrow M\lt_{\textrm{PS}[]}N$ と $M\lt_{\textrm{PS}[]}N\Rightarrow M\lt_{\textrm{PS}}N$）であるのに対し、
  系の主張は広義の $\leq_{\textrm{PS}}$ と $\leq_{\textrm{PS}[]}$ の同値である。したがって
  両方向とも等号の場合が引用の外に残る。

  ($\Rightarrow$) では $M=N$ の場合が残り、$M\leq_{\textrm{PS}[]}N$ の証拠として
  $a=()$ を自分で与えなければならない（$\leq_{\textrm{PS}[]}$ が $a\in\mathbb{N}_+^{\lt\omega}$ に
  $a\neq()$ を課さないので、これは定義から出る）。($\Leftarrow$) では取った $a$ が $()$ の場合が残り、
  $\textrm{expand}(N,())=N$ から $M=N$ を出して $\leq_{\textrm{PS}}$ の等号側に落とす必要がある。
  原文はこの 2 か所を書いていない。埋めるのに要るのは定義の展開だけなので W とした。

- **[W]** 引用先が逐語形では偽なので、$\textrm{Lng}(N)\leq1$ の場合を別に処理している

  原文が ($\Leftarrow$) 方向に引く「辞書式的順序が基本列的順序を含意すること」は、逐語形
  （任意の $M,N\in CT_{\textrm{PS}}$ に対して $M\lt_{\textrm{PS}[]}N$ ならば $M\lt_{\textrm{PS}}N$）
  では偽である。反例は $M=N=((0,0))\in CT_{\textrm{PS}}$、$a=(1)$ で、$\textrm{Lng}(N)=1$ より
  $N[1]=N$ だから $a\neq()$ にもかかわらず $M=\textrm{expand}(N,a)$、すなわち
  $M\lt_{\textrm{PS}[]}N$ が成り立つのに $M\lt_{\textrm{PS}}N$ は成り立たない。この否定自体も
  形式化されている。よってこの系の ($\Leftarrow$) 方向を引用だけで「即座に従う」とはできない。

  ただし系そのものは真である。Lean は $\textrm{Lng}(N)\gt1$ を仮定に足した訂正形を使い、
  残る $\textrm{Lng}(N)\leq1$ の場合を自明展開で直接 $M=N$ に落とす。埋める作業は分岐 1 つと
  既存の補題 1 本なので W とした。

  なお $N\in CT_{\textrm{PS}}$ の下では $\textrm{Lng}(N)\leq1$ は $N=((0,0))$ を意味するが
  （$N$ は空列でなく $N_0=(0,0)$ だから）、Lean の分岐はこの事実を使わず
  $\textrm{Lng}(N)$ の大小だけで進む。

- **[R]** ($\Leftarrow$) 方向では $CT_{\textrm{PS}}$ の仮定が要らなかった

  原文は系を $M,N\in CT_{\textrm{PS}}$ に限って述べ、証明も $CT_{\textrm{PS}}$ を仮定に持つ
  2 命題の引用だけである。しかし Lean の ($\Leftarrow$) 方向が使うのは上記の訂正形と自明展開の
  2 本で、どちらも $CT_{\textrm{PS}}$ を仮定しない（訂正形が課すのは $\textrm{Lng}(N)\gt1$ のみ、
  自明展開が課すのは $\textrm{Lng}(N)\leq1$ のみである）。したがってこの方向は任意のペア数列
  $M,N$ について成り立っている。

  ($\Rightarrow$) 方向では $CT_{\textrm{PS}}$ が要る。基本列的順序が辞書式的順序を含意することが
  この仮定を必要とするからである。Lean の定理の主張は原文どおり両側で
  $M,N\in CT_{\textrm{PS}}$ を仮定した形にしてあり、($\Leftarrow$) 側でその仮定が使われないだけである。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $M\lt_{\textrm{PS}}N$ | `ltPS` | `lean/Bijectivity/Defs.lean` |
| $M\leq_{\textrm{PS}}N$ | `lePS` | 同上 |
| $M\lt_{\textrm{PS}[]}N$ | `ltExpPS` | 同上 |
| $M\leq_{\textrm{PS}[]}N$ | `leExpPS` | 同上 |
| $\textrm{expand}(N,a)=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ | `expand` | 同上 |
| $CT_{\textrm{PS}}$ | `CTPS` | 同上 |
| $M[n]$ | `PSS.oper` | `lean/PSS/Defs.lean` |
| $\textrm{Lng}(M)$ | `PSS.Lng` | 同上 |
| 系（順序の等価性） | `lePS_iff_leExpPS` | `lean/Bijectivity/13-order-equivalence.lean` |
| 基本列的順序が辞書式的順序を含意すること | `ltPS_ltExpPS` | `lean/Bijectivity/12-lex-implies-exp.lean` |
| 辞書式的順序が基本列的順序を含意することの訂正形 | `ltExpPS_ltPS_of_lng` | `lean/Bijectivity/05-exp-implies-lex.lean` |
| 自明展開 | `expand_of_lng_le_one` | 同上 |
| 逐語形の否定（反例 $M=N=((0,0))$、$a=(1)$） | `not_ltExpPS_ltPS` | 同上 |

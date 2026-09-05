[< back](README.md)

# 05: 命題 (辞書式的順序が基本列的順序を含意すること)

## 原文

### 命題

原文に命題番号は無く、見出しは「命題 (辞書式的順序が基本列的順序を含意すること)」である。

任意の $M,N\in CT_{\textrm{PS}}$ に対して、$M\lt_{\textrm{PS}[]}N$ ならば $M\lt_{\textrm{PS}}N$ である。

### 証明

証明

$\lt_{\textrm{PS}[]}$ の定義よりある $a\in\mathbb{N}_+^{\lt\omega}\setminus\lbrace()\rbrace$ が存在して $M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ である。

$N=(0,0)$ とすると、任意の $n\in\mathbb{N}_+$ に対して $N[n]=N$ であるから、$M=N$ となり、これは条件と反するから $N\neq(0,0)$ である。

上より $\textrm{Lng}(N)\gt1$ である。

任意の非負整数 $i\lt\textrm{Lng}(a)$ に対して $Q_0=N$、$Q_{i+1}=Q_i[a_i]$ とする。

よって基本列の辞書式的縮小性より $Q_1=N[a_0]\lt_{\textrm{PS}}N$ である。

任意の非負整数 $1\leq i\lt\textrm{Lng}(a)$ をとり、$Q_i\lt_{\textrm{PS}}N$ と仮定すると、辞書式的順序の線形性及び基本列の辞書式的縮小性より $Q_{i+1}=Q_i[a_i]\leq_{\textrm{PS}}Q_i\lt_{\textrm{PS}}N$ である。

帰納法により任意の非負整数 $1\leq i\leq\textrm{Lng}(a)$ に対して $Q_i\lt_{\textrm{PS}}N$ である。

よって $M=Q_{\textrm{Lng}(a)}\lt_{\textrm{PS}}N$ である。□

## Lean

### Lean での命題

用いる定義は原文どおりである。反復展開を

$$\textrm{expand}(N,())=N,\qquad \textrm{expand}(N,(n)\frown a)=\textrm{expand}(N[n],a)$$

と書けば $\textrm{expand}(N,a)=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ であり、

$$M\lt_{\textrm{PS}[]}N:\Longleftrightarrow\exists a\in\mathbb{N}_+^{\lt\omega}\setminus\lbrace()\rbrace,~M=\textrm{expand}(N,a)$$

$$M\leq_{\textrm{PS}}N:\Longleftrightarrow M=N\lor M\lt_{\textrm{PS}}N$$

$$CT_{\textrm{PS}}=\lbrace M\mid M\in ST_{\textrm{PS}}\land M_0=(0,0)\rbrace$$

である。この節では原文の命題そのものではなく、次の 2 つが証明されている。

**(a) 逐語形の否定。**

$$\lnot\Bigl(\forall M,N\in CT_{\textrm{PS}},~M\lt_{\textrm{PS}[]}N\Rightarrow M\lt_{\textrm{PS}}N\Bigr)$$

**(b) 訂正形。** 任意のペア数列 $M,N$（$CT_{\textrm{PS}}$ でなくてよい）に対して、
$\textrm{Lng}(N)\gt1$ かつ $M\lt_{\textrm{PS}[]}N$ ならば $M\lt_{\textrm{PS}}N$ である。

補助として次の 3 つも証明されている。

**(c) 反復展開の広義縮小性。** 任意の $a\in\mathbb{N}_+^{\lt\omega}$ と任意のペア数列 $N$ に対して
$\textrm{expand}(N,a)\leq_{\textrm{PS}}N$ である。

**(d) 自明展開。** $\textrm{Lng}(N)\leq1$ ならば、任意の（成分に条件を課さない）$a$ に対して
$\textrm{expand}(N,a)=N$ である。

**(e)** $((0,0))\in CT_{\textrm{PS}}$ である。

### Lean での証明

**(c) 反復展開の広義縮小性。** $a$ に関する構造帰納法。

- $a=()$ のとき。$\textrm{expand}(N,())=N$ なので $\leq_{\textrm{PS}}$ の定義の等号側 $N=N$ で済む。
- $a=(n)\frown a'$ のとき。仮定より $n\in a$ だから $1\leq n$ であり、$a'$ の各成分も $a$ の成分なので
  $1\leq a'_i$ である。定義より $\textrm{expand}(N,(n)\frown a')=\textrm{expand}(N[n],a')$。
  帰納法の仮定を数列 $a'$ と初期値 $N[n]$ に適用して
  $\textrm{expand}(N[n],a')\leq_{\textrm{PS}}N[n]$ を得る。次に基本列の辞書式的縮小性の弱形
  （$1\leq n$ のみを仮定し、$\textrm{Lng}(N)\gt1$ なら基本列の辞書式的縮小性そのもの、
  $\textrm{Lng}(N)\leq1$ なら $\textrm{operator}[]$ の定義の第 1 分岐で $N[n]=N$ となる、という
  場合分けで $N[n]\leq_{\textrm{PS}}N$ を出すもの）を使う。最後に辞書式的順序の線形性が与える
  $\leq_{\textrm{PS}}$ の推移律で
  $\textrm{expand}(N[n],a')\leq_{\textrm{PS}}N[n]\leq_{\textrm{PS}}N$ をつなぐ。

**(d) 自明展開。** $a$ に関する構造帰納法。

- $a=()$ のとき。$\textrm{expand}(N,())=N$ で定義そのもの。
- $a=(n)\frown a'$ のとき。$\textrm{Lng}(N)\leq1$ より $\textrm{Lng}(N)-1=0$ であり、
  $\textrm{operator}[]$ の定義は $j_1=\textrm{Lng}(N)-1=0$ の分岐で $N[n]=N$ を返す。
  よって $\textrm{expand}(N,(n)\frown a')=\textrm{expand}(N[n],a')=\textrm{expand}(N,a')$ となり、
  帰納法の仮定（$N$ は同じ、$\textrm{Lng}(N)\leq1$ も同じ）で $=N$。

**(e) $((0,0))\in CT_{\textrm{PS}}$。** $CT_{\textrm{PS}}$ の定義は $ST_{\textrm{PS}}$ 所属と先頭成分
$M_0=(0,0)$ の連言である。先頭成分の条件は定義の展開で直ちに従う。$ST_{\textrm{PS}}$ 所属は、
$((0,0))=((j,j))_{j=0}^{0}$ であることを使い、$ST_{\textrm{PS}}$ の生成規則のうち対角列の規則を
$u=v=0$（$u\leq v$）で適用して得る。

**(a) 逐語形の否定。** 逐語形を仮定して矛盾を導く。$M=N=((0,0))$、$a=(1)$ と置く。

- $a\neq()$ である。
- $a$ の唯一の成分は $1$ なので $1\leq1$、すなわち $a\in\mathbb{N}_+^{\lt\omega}$ である。
- $\textrm{Lng}(((0,0)))=1\leq1$ だから (d) より $\textrm{expand}(N,(1))=N$、すなわち
  $M=\textrm{expand}(N,a)$ である。

以上の 3 点から $\lt_{\textrm{PS}[]}$ の定義により $M\lt_{\textrm{PS}[]}N$ が成り立つ。また (e) より
$M,N\in CT_{\textrm{PS}}$ である。よって逐語形を適用すると $M\lt_{\textrm{PS}}M$ を得るが、これは
辞書式的順序の線形性が与える $\lt_{\textrm{PS}}$ の非反射性に反する。

**(b) 訂正形。** $M\lt_{\textrm{PS}[]}N$ の定義を開いて、$a\neq()$、$a$ の各成分が $\geq1$、
$M=\textrm{expand}(N,a)$ なる $a$ を取る。$a$ の形で場合分けする。

- $a=()$ のとき。$a\neq()$ に反するので、この場合は起こらない。
- $a=(n)\frown a'$ のとき。
  - $n\in a$ より $1\leq n$。仮定 $\textrm{Lng}(N)\gt1$ と合わせて基本列の辞書式的縮小性を $N$ と
    $n$ に適用し、$N[n]\lt_{\textrm{PS}}N$ を得る。これが原文の
    $Q_1=N[a_0]\lt_{\textrm{PS}}N$ に当たる。
  - $a'$ の各成分は $a$ の成分なので $\geq1$。(c) を数列 $a'$ と初期値 $N[n]$ に適用して
    $M=\textrm{expand}(N,(n)\frown a')=\textrm{expand}(N[n],a')\leq_{\textrm{PS}}N[n]$ を得る。
  - $\leq_{\textrm{PS}}$ の定義（$=$ か $\lt_{\textrm{PS}}$）で分岐する。
    - $\textrm{expand}(N[n],a')=N[n]$ のとき。$M=N[n]$ なので、目標 $M\lt_{\textrm{PS}}N$ は
      上で得た $N[n]\lt_{\textrm{PS}}N$ そのものである。
    - $\textrm{expand}(N[n],a')\lt_{\textrm{PS}}N[n]$ のとき。辞書式的順序の線形性が与える
      $\lt_{\textrm{PS}}$ の推移律を $M\lt_{\textrm{PS}}N[n]\lt_{\textrm{PS}}N$ に適用して
      $M\lt_{\textrm{PS}}N$ を得る。

## 原文通りに書けなかった理由

- **[X]** 原文の言明は逐語形では偽であり、$\textrm{Lng}(N)\gt1$ を補う必要がある

  原文の証明は「$N=(0,0)$ とすると（中略）$M=N$ となり、これは条件と反する」と述べるが、
  $M\neq N$ は $\lt_{\textrm{PS}[]}$ の定義から従わない。$\lt_{\textrm{PS}[]}$ が要求するのは
  $a\neq()$ だけで、$M\neq N$ ではないからである。実際 $\textrm{Lng}(N)\leq1$ のときは
  任意の $n\in\mathbb{N}_+$ に対して $N[n]=N$ であり（この事実は原文自身が同じ行で書いている）、
  $a$ をいくら長く取っても $\textrm{expand}(N,a)=N$ のままである。よって
  $N=M=((0,0))\in CT_{\textrm{PS}}$、$a=(1)$
  は $M\lt_{\textrm{PS}[]}N$ を満たすが $M\lt_{\textrm{PS}}N$ を満たさない反例になる。Lean は
  この反例を組み立てて逐語形の否定 (a) を証明し、そのうえで仮定に $\textrm{Lng}(N)\gt1$ を
  足した (b) を主張として置いている。

  訂正の仕方は一意ではない。仮定に $\textrm{Lng}(N)\gt1$（あるいは $M\neq N$）を足す道と、
  $\lt_{\textrm{PS}[]}$ の定義自体を狭義になるよう直す道があり、前者を採ると定理の形が変わって
  下流の系（順序の等価性）で $\textrm{Lng}(N)\leq1$ の場合を別扱いする分岐が要る。
  機械的な誤記の訂正ではないので **X** とした。

- **[R]** $CT_{\textrm{PS}}$ の仮定が要らなかった

  原文が $CT_{\textrm{PS}}$ を使うのは「$N\neq(0,0)$ から $\textrm{Lng}(N)\gt1$」の一歩だけである。
  ここでは $N_0=(0,0)$ を使って、$\textrm{Lng}(N)=1$ なら $N=(N_0)=((0,0))$ となることを言っている。
  $ST_{\textrm{PS}}$ 所属のほうは証明のどこでも使われない。したがってこの一歩を仮定
  $\textrm{Lng}(N)\gt1$ に置き換えると $CT_{\textrm{PS}}$ は完全に落ち、Lean の訂正形 (b) は
  $M,N$ が任意のペア数列である場合に成り立つ形になっている。

- **[W]** 原文の $Q_{i+1}=Q_i[a_i]\leq_{\textrm{PS}}Q_i$ は、引用した命題の直接の帰結ではない

  原文は「辞書式的順序の線形性及び基本列の辞書式的縮小性より
  $Q_{i+1}=Q_i[a_i]\leq_{\textrm{PS}}Q_i$」と書くが、基本列の辞書式的縮小性は
  $\textrm{Lng}(Q_i)\gt1$ を仮定して $Q_i[a_i]\lt_{\textrm{PS}}Q_i$ を結論する命題であり、
  原文は $\textrm{Lng}(Q_i)\gt1$ を確かめていない。しかも $\textrm{Lng}(Q_i)=1$ は実際に起こる。
  たとえば $N=((0,0),(1,1))\in CT_{\textrm{PS}}$、$a=(1,1)$ とすると、$[1]$ による展開は前者
  $\textrm{Pred}$ に一致するので $Q_1=N[1]=\textrm{Pred}(N)=((0,0))$ で $\textrm{Lng}(Q_1)=1$ となり、
  $i=1$ の段で引用が空振りする。原文が結論を $\lt_{\textrm{PS}}$ でなく $\leq_{\textrm{PS}}$ と
  広義に書いているのはこの場合を吸収するためだが、場合分け自体は書かれていない。

  Lean はこの穴を、$1\leq n$ だけを仮定する弱形 $M[n]\leq_{\textrm{PS}}M$ を用意して埋めている。
  弱形の証明は $\textrm{Lng}(M)$ による 2 分岐で、$\textrm{Lng}(M)\gt1$ なら基本列の辞書式的縮小性を
  そのまま使い、$\textrm{Lng}(M)\leq1$ なら $\textrm{operator}[]$ の定義の第 1 分岐から
  $M[n]=M$ を出して等号側で閉じる。

- **[S]** 帰納法の向きが原文と違う

  原文は $Q_0=N$、$Q_{i+1}=Q_i[a_i]$ と添字列を先頭から食わせる列を定義し、不変量
  「$Q_i\lt_{\textrm{PS}}N$」で $i$ に関する帰納法を回す。すなわち $N$ を固定したまま、毎段で
  基本列の辞書式的縮小性と推移律を使う。

  Lean は先頭の $a_0$ だけを剥がして狭義の一歩 $N[a_0]\lt_{\textrm{PS}}N$ を作り、残りの
  $a_1,\ldots,a_{\textrm{Lng}(a)-1}$ は独立した補題 (c)「反復展開の広義縮小性
  $\textrm{expand}(N,a)\leq_{\textrm{PS}}N$」に押し込む。(c) の帰納法の不変量は $N$ を固定せず、
  各段で初期値を $N[n]$ に取り替える形になっている。最後に $\leq_{\textrm{PS}}$ と
  $\lt_{\textrm{PS}}$ を 1 回だけ合成して結論を出す。

  推移律を使う回数と使う場所が原文と入れ替わるだけで、証明する命題も、使う原文の命題
  （基本列の辞書式的縮小性、辞書式的順序の線形性）も同じであり、下流の内容は変わらない。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $M\lt_{\textrm{PS}}N$ | `ltPS` | `lean/Bijectivity/Defs.lean` |
| $M\leq_{\textrm{PS}}N$ | `lePS` | 同上 |
| $M\lt_{\textrm{PS}[]}N$ | `ltExpPS` | 同上 |
| $\textrm{expand}(N,a)=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ | `expand` | 同上 |
| $CT_{\textrm{PS}}$ | `CTPS` | 同上 |
| $M[n]$、$\textrm{operator}[]$ の定義 | `PSS.oper` | `lean/PSS/Defs.lean` |
| $\textrm{Lng}(M)$ | `PSS.Lng` | 同上 |
| $ST_{\textrm{PS}}$ と対角列の生成規則 | `PSS.STPS`、`PSS.STPS.diag` | `lean/PSS/Standard.lean` |
| $((j,j))_{j=u}^{v}$ | `PSS.diagSeq` | `lean/PSS/Red.lean` |
| (c) 反復展開の広義縮小性 | `expand_lePS` | `lean/Bijectivity/05-exp-implies-lex.lean` |
| (d) 自明展開 | `expand_of_lng_le_one` | 同上 |
| (e) $((0,0))\in CT_{\textrm{PS}}$ | `ctps_zero_singleton` | 同上 |
| (a) 逐語形の否定 | `not_ltExpPS_ltPS` | 同上 |
| (b) 訂正形 | `ltExpPS_ltPS_of_lng` | 同上 |
| 基本列の辞書式的縮小性 | `oper_ltPS` | `lean/Bijectivity/04-fseq-lex-decreasing.lean` |
| 基本列の辞書式的縮小性の弱形 | `oper_lePS` | 同上 |
| 辞書式的順序の線形性（非反射性） | `ltPS_irrefl` | `lean/Bijectivity/02-lex-linear.lean` |
| 辞書式的順序の線形性（$\lt_{\textrm{PS}}$ の推移律） | `ltPS_trans` | 同上 |
| 辞書式的順序の線形性（$\leq_{\textrm{PS}}$ の推移律） | `lePS_trans` | 同上 |

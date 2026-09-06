[← Back](README.md)

# Buchholz (1986) §2.1 — 項と辞書式順序

出典：W. Buchholz, *A new system of proof-theoretic ordinal functions*,
Annals of Pure and Applied Logic 32 (1986), §2.

<a id="buc86-2-1-syntax"></a>
## 項と主項の構文 [BUC86-2-1-SYNTAX]

添字集合を

```math
\mathbb N_\omega=\mathbb N\cup\{\omega\}
```

とする。Buchholz 項 $`T`$ と主項 $`P`$ を相互帰納的に

```math
\begin{aligned}
p&::=D_u a
&&\qquad (u\in\mathbb N_\omega,\ a\in T),\cr 
a&::=(p_0,\ldots,p_{k-1})
&&\qquad (k\in\mathbb N,\ p_i\in P)
\end{aligned}
\tag{1}
```

で定める。（すなわち、主項 $`D_ua`$ の本体は再び Buchholz 項であり、
一般の項は主項の有限列である。この二つを同時に最小の有限構文として
生成するので、循環した無限項は含まれない。）

空列を

```math
0:=()
\tag{2}
```

と書く。また主項 $`D_ua`$ を一般項として使う場合は、一要素列

```math
D_ua:=(D_ua)
\tag{3}
```

と同一視する。(2), (3) は異なる構文を混同する略記ではなく、空の主項列と
一要素の主項列をそれぞれ項へ包む操作である。

<a id="buc86-2-1-eq"></a>
## 構造的等値判定 [BUC86-2-1-EQ]

添字の等値判定を $`[u=v]\in\{0,1\}`$ と書く。項、主項、主項列の
構造的等値判定 $`E_T,E_P,E_L`$ を同時再帰で定める。

```math
\begin{aligned}
E_T((p_0,\ldots,p_{k-1}),(q_0,\ldots,q_{\ell-1}))
&:=E_L([p_0,\ldots,p_{k-1}],[q_0,\ldots,q_{\ell-1}]),\cr 
E_P(D_ua,D_vb)
&:=[u=v]\land E_T(a,b),\cr 
E_L([],[])&:=1,\cr 
E_L([],q::qs)&:=0,\cr 
E_L(p::ps,[])&:=0,\cr 
E_L(p::ps,q::qs)&:=E_P(p,q)\land E_L(ps,qs).
\end{aligned}
\tag{4}
```

ここで $`\land`$ は $`0,1`$ 上の論理積である。

<a id="buc86-2-1-eq-refl"></a>
### 構造的等値判定の反射性 [BUC86-2-1-EQ-REFL]

項、主項、主項列について次を同時に示す。

```math
E_T(a,a)=1,\qquad E_P(p,p)=1,\qquad E_L(ps,ps)=1.
\tag{5}
```

三種類の主張を

```math
\begin{aligned}
R_T(a)&:\quad E_T(a,a)=1,\cr 
R_P(p)&:\quad E_P(p,p)=1,\cr 
R_L(ps)&:\quad E_L(ps,ps)=1
\end{aligned}
```

とおき、項、主項、主項列の生成に関する相互構造帰納法で
$`R_T(a),R_P(p),R_L(ps)`$ を同時に示す。

**項の場合。**
$`a=(p_0,\ldots,p_{k-1})`$ とし、
$`\bar p=[p_0,\ldots,p_{k-1}]`$ とおく。

```math
E_L(\bar p,\bar p)=1
```

を仮定する。(4) の第一式から

```math
E_T(a,a)
=E_T((p_0,\ldots,p_{k-1}),(p_0,\ldots,p_{k-1}))
=E_L(\bar p,\bar p)
=1.
```

従って $`R_T(a)`$ が成り立つ。

**主項の場合。**
$`p=D_ua`$ とする。

```math
E_T(a,a)=1
```

を仮定する。また添字の等値判定について $`[u=u]=1`$ であるから、(4) の
第二式により

```math
\begin{aligned}
E_P(p,p)
&=E_P(D_ua,D_ua)\cr 
&=[u=u]\land E_T(a,a)\cr 
&=1\land1\cr 
&=1.
\end{aligned}
```

従って $`R_P(p)`$ が成り立つ。

**主項列の場合。**
空列については (4) の第三式から

```math
E_L([],[])=1
```

である。次に非空列 $`p::ps`$ を考え、

```math
E_P(p,p)=1,\qquad E_L(ps,ps)=1
```

を仮定する。(4) の第六式により

```math
\begin{aligned}
E_L(p::ps,p::ps)
&=E_P(p,p)\land E_L(ps,ps)\cr 
&=1\land1\cr 
&=1.
\end{aligned}
```

従って $`R_L([])`$ と $`R_L(p::ps)`$ がともに成り立つ。以上で、一般項、
主項、空の主項列、非空の主項列の全ての場合が示されたので、相互構造帰納法
により (5) を得る。

<a id="buc86-2-1-eq-sound"></a>
### 構造的等値判定の正当性 [BUC86-2-1-EQ-SOUND]

逆に、判定結果が $`1`$ なら構文が等しいことを、三種類について同時に示す。

```math
\begin{aligned}
E_T(a,b)=1&\Longrightarrow a=b,\cr 
E_P(p,q)=1&\Longrightarrow p=q,\cr 
E_L(ps,qs)=1&\Longrightarrow ps=qs.
\end{aligned}
\tag{6}
```

主項 $`D_ua,D_vb`$ について $`E_P(D_ua,D_vb)=1`$ とする。(4) より

```math
[u=v]=1,\qquad E_T(a,b)=1.
```

従って $`u=v`$ であり、帰納法の仮定から $`a=b`$。よって
$`D_ua=D_vb`$ である。

主項列では、空列と非空列の組合せは (4) により判定値 $`0`$ なので、
仮定 $`E_L(ps,qs)=1`$ の下では起こらない。両方が空なら等しい。
両方が非空で

```math
ps=p::ps',\qquad qs=q::qs'
```

と書ける場合、(4) から

```math
E_P(p,q)=1,\qquad E_L(ps',qs')=1.
```

帰納法の仮定により $`p=q`$ かつ $`ps'=qs'`$ なので
$`p::ps'=q::qs'`$ である。最後に項の判定を主項列へ戻せば
第一式も従う。

(5), (6) を合わせると

```math
E_T(a,b)=1\Longleftrightarrow a=b,\qquad
E_P(p,q)=1\Longleftrightarrow p=q,\qquad
E_L(ps,qs)=1\Longleftrightarrow ps=qs.
\tag{7}
```

従って (4) は構文的等値性の正しい決定手続きである。

<a id="buc86-2-1-order-def"></a>
## 辞書式順序の定義 [BUC86-2-1-ORDER-DEF]

主項については

```math
D_ua\lt_P D_vb
\quad\Longleftrightarrow\quad
u\lt v\ \lor\ (u=v\land a\lt_T b)
\tag{8}
```

と定める。主項列の辞書式順序 $`\lt_L`$ は

```math
\begin{aligned}
\neg([]\lt_L[]),\qquad&
[]\lt_L(q::qs),\qquad
\neg((p::ps)\lt_L[]),\cr 
(p::ps)\lt_L(q::qs)
\quad\Longleftrightarrow\quad&
p\lt_Pq\ \lor\ (p=q\land ps\lt_Lqs)
\end{aligned}
\tag{9}
```

である。項の順序は、その主項列の順序によって

```math
(p_0,\ldots,p_{k-1})\lt_T(q_0,\ldots,q_{\ell-1})
\quad\Longleftrightarrow\quad
[p_0,\ldots,p_{k-1}]\lt_L[q_0,\ldots,q_{\ell-1}]
\tag{10}
```

と定める。

(9) から、空項 $`0`$ は任意の非零項より小さい。また非空項同士では、
最初に異なる主項で大小が決まり、それ以前の主項が全て等しい場合だけ
尾部の比較へ進む。

広義順序は

```math
a\leq b
\quad\Longleftrightarrow\quad
a\lt_Tb\ \lor\ a=b
\tag{11}
```

と定める。これらは全て有限構文に対する再帰的な比較であり、順序数への
意味論的評価を用いない。

<a id="buc86-2-1-decomp"></a>
## 主項成分の分解と再合成 [BUC86-2-1-DECOMP]

項 $`a=(p_0,\ldots,p_{k-1})`$ の主項成分列を

```math
PB(a):=[(p_0),\ldots,(p_{k-1})]
\tag{12}
```

と定める。右辺の各 $`(p_i)`$ は一要素の主項列なので、それぞれ一般項である。
逆に項列 $`a_0,\ldots,a_{m-1}`$ を、それぞれの主項列を順番に連結して

```math
\Sigma_B(a_0,\ldots,a_{m-1})
:=\Bigl(
\operatorname{untrm}(a_0)\mathbin{+\!\!+}\cdots
\mathbin{+\!\!+}\operatorname{untrm}(a_{m-1})
\Bigr)
\tag{13}
```

と定める。ここで $`\operatorname{untrm}`$ は項を包んでいる主項列を取り出し、
$`+\!\!+`$ は有限列の連結を表す。(13) の外側の括弧は、連結して得た
主項列を再び一個の項として包むことを表す。

定義から

```math
PB(0)=[],\qquad PB(D_ua)=[D_ua],
\tag{14}
```

および

```math
\Sigma_B(PB(a))=a
\tag{15}
```

が成り立つ。(15) を確認するため
$`a=(p_0,\ldots,p_{k-1})`$ と書く。(12) の各成分から
$`\operatorname{untrm}((p_i))=[p_i]`$ を取り出し、(13) で順に連結すると

```math
[p_0]\mathbin{+\!\!+}\cdots\mathbin{+\!\!+}[p_{k-1}]
=[p_0,\ldots,p_{k-1}]
```

となる。これを再び項として包めば元の $`a`$ である。空列の場合も、
空個の連結が空列なので同じ計算が成り立つ。

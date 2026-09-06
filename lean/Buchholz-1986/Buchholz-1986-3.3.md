[← Back](README.md)

# Buchholz (1986) 補題3.3 — 基本列は順序数項を保つ

<a id="buc86-3-3"></a>
## 補題3.3 [BUC86-3-3]

$`a\in OT_B`$、$`a\neq0`$ とする。このとき、任意の $`n\in\mathbb N`$ について

```math
a[\bar n]\in OT_B
```

である。ここで $`\bar n`$ は自然数 $`n`$ を表す Buchholz 項である。

実際には、次の強化形を証明する。

<a id="buc86-3-3-general"></a>
### 基本列閉包の強化形 [BUC86-3-3-GENERAL]

$`a,z\in OT`$ がともに $`D_\omega`$-自由で、

```math
a\neq0,\qquad
z\in\operatorname{dom}(a)\cup\mathbb N_B
```

ならば

```math
a[z]\in OT
\qquad\text{かつ}\qquad
a[z]\text{ は }D_\omega\text{-自由}
```

である。ここで

```math
\mathbb N_B=\{\bar n:n\in\mathbb N\},
\qquad
a[z]=\operatorname{oper}(a,z)
```

と書く。

## 準備

### 順序と有限集合の比較

[BUC86-2-1](Buchholz-1986-2.1-order.md#buc86-2-1) により、Buchholz 項の
辞書式順序 $`\lt`$ は狭義線型順序である。以下、$`a\leq b`$ は
$`a\lt b`$ または $`a=b`$ を表す。従って

```math
\begin{gathered}
a\leq a,\cr 
a\leq b\leq c\Longrightarrow a\leq c,\cr 
a\leq b\lt c\Longrightarrow a\lt c,\qquad
a\lt b\leq c\Longrightarrow a\lt c,\cr 
a\leq b\land b\leq a\Longrightarrow a=b,\cr 
a\leq b\ \lor\ b\leq a,\qquad 0\leq a
\end{gathered}
\tag{1}
```

が成り立つ。

項集合 $`M,N`$ に対して

```math
M\preccurlyeq N
\quad\Longleftrightarrow\quad
\forall x\in M\ \exists y\in N\ (x\leq y)
\tag{2}
```

と定める。この関係には次の性質がある。

```math
\begin{aligned}
M\subseteq N&\Longrightarrow M\preccurlyeq N,\cr 
M\preccurlyeq N\subseteq N'&\Longrightarrow M\preccurlyeq N',\cr 
M_1\preccurlyeq N\land M_2\preccurlyeq N
&\Longrightarrow M_1\cup M_2\preccurlyeq N.
\end{aligned}
\tag{3}
```

いずれも (2) の証人をそのまま用いればよい。第一式では $`x`$ 自身を証人に取る。

### $`G`$-集合の構造

$`G_u(a)`$ は、項 $`a`$ の内部で水準 $`u`$ 以上の崩壊記号の本体を集めた
有限集合である。定義から

```math
\begin{aligned}
G_u(a+b)&=G_u(a)\cup G_u(b),\cr 
G_u(D_vb)&=
\begin{cases}
\{b\}\cup G_u(b),&u\leq v,\cr 
\varnothing,&v\lt u,
\end{cases}\cr 
G_u(\bar n)&\subseteq\{0\}
\end{aligned}
\tag{4}
```

を得る。

項の構造的大きさを $`|a|`$ と書く。項、主項、主項列について同時に構造帰納を
行うと、次の三性質が従う。

<a id="buc86-3-3-g-structure"></a>
#### $`G`$-集合の推移性と反単調性 [BUC86-3-3-G-STRUCTURE]

```math
\begin{aligned}
x\in G_u(a)&\Longrightarrow |x|\lt |a|,\cr 
x\in G_u(a)&\Longrightarrow G_u(x)\subseteq G_u(a),\cr 
u\leq v&\Longrightarrow G_v(a)\subseteq G_u(a).
\end{aligned}
\tag{5}
```

第一式では、$`x`$ は $`a`$ の真部分項の本体またはその中の $`G`$-要素なので、
構造的大きさが真に減少する。第二式では、$`x`$ が直接の本体なら
$`G_u(x)`$ は (4) の右辺に含まれ、より深い位置にある場合は帰納法の仮定を
一回合成する。第三式では、水準 $`v`$ 以上の添字は $`u\leq v`$ のとき必ず
水準 $`u`$ 以上でもある。主項列については和集合を取ればよい。

### 三項 $`G`$-関係

基本列を取る際に必要な不変量を次で定める。

```math
\begin{aligned}
\operatorname{TriG}(z,b,a)
\quad\Longleftrightarrow\quad
\forall u\,\forall c\,
\bigl(&b\leq c\leq a\cr 
&\Longrightarrow
G_u(b)\preccurlyeq
G_u(c)\cup G_u(z)\cup\{0\}\bigr).
\end{aligned}
\tag{6}
```

ここで $`b`$ は基本列要素 $`a[z]`$ を表す。重要なのは、単純な集合包含ではなく、
$`G_u(b)`$ の各要素を右辺のどれかの要素で上から押さえることである。

<a id="buc86-3-4-g-control"></a>
### $`G`$-条件の移送 [BUC86-3-4-G-CONTROL]

次を示す。固定した $`u`$ に対し

```math
\begin{gathered}
\operatorname{TriG}(z,b,a),\qquad b\leq a,\cr 
\forall x\in G_u(a)\ (x\lt a),\qquad
\forall x\in G_u(z)\ (x\lt b)
\end{gathered}
```

ならば

```math
\forall x\in G_u(b)\ (x\lt b)
\tag{7}
```

が成り立つ。

まず

```math
x\in G_u(b),\qquad b\leq x
\tag{8}
```

を同時に満たす $`x`$ は存在しないことを、$`|x|`$ に関する強い帰納法で示す。
(6) を $`c=a`$ に適用すると、ある $`y`$ が存在して

```math
x\leq y,\qquad
y\in G_u(a)\cup G_u(z)\cup\{0\}
\tag{9}
```

となる。

- $`y\in G_u(a)`$ なら $`y\lt a`$ なので $`x\leq y\lt a`$、従って $`x\lt a`$。
- $`y\in G_u(z)`$ なら $`y\lt b`$ なので
  $`b\leq x\leq y\lt b`$ となり、$`b\lt b`$ に矛盾する。
- $`y=0`$ なら $`x\leq0\leq x`$ より $`x=0`$ である。さらに
  $`b\leq0\leq b`$ より $`b=0`$ となるが、
  $`x\in G_u(b)=G_u(0)=\varnothing`$ に矛盾する。

従って矛盾する二場合を除けば $`x\lt a`$ であり、特に $`x\leq a`$ である。
今度は (6) を $`c=x`$ に適用する。ある $`y`$ について

```math
x\leq y,\qquad
y\in G_u(x)\cup G_u(z)\cup\{0\}
\tag{10}
```

を得る。後二場合は (9) と同じ矛盾を与える。$`y\in G_u(x)`$ の場合は、
(5) より

```math
y\in G_u(b),\qquad |y|\lt |x|,
```

かつ $`b\leq x\leq y`$ である。従って強い帰納法の仮定を $`y`$ に適用でき、
再び矛盾する。これで (8) は不可能だと分かった。

最後に任意の $`x\in G_u(b)`$ を取る。三分律により
$`x\lt b`$、$`x=b`$、$`b\lt x`$ のいずれかである。後二場合はいずれも
$`b\leq x`$ を与えて (8) に反する。従って $`x\lt b`$ であり、(7) が示された。

### 区間に挟まれた項の形

<a id="buc86-3-3-sandwich-prefix"></a>
#### 共通前置列の保存 [BUC86-3-3-SANDWICH-PREFIX]

主項列 $`p,x,y`$ と項 $`c`$ について

```math
p+x\leq c\leq p+y
\tag{11}
```

ならば、ある主項列 $`d`$ が存在して

```math
c=p+d,\qquad x\leq d\leq y
\tag{12}
```

となる。

これは前置列 $`p`$ の長さに関する帰納法で示す。$`p`$ が空なら $`d=c`$ と取る。
$`p=p_0+p'`$ とし、$`c`$ の先頭を $`q`$ とする。$`c=0`$ なら
$`p+x\leq0`$ に反する。辞書式順序で (11) の両側の先頭は $`p_0`$ なので、
$`p_0\lt q`$ と $`q\lt p_0`$ は同時には起こらない。従って $`q=p_0`$ であり、
両不等式は尾部の

```math
p'+x\leq c'\leq p'+y
```

に帰着する。帰納法の仮定から $`c'=p'+d`$ と (12) を得る。

<a id="buc86-3-3-sandwich-d"></a>
#### 同じ崩壊記号に挟まれた項 [BUC86-3-3-SANDWICH-D]

```math
D_vx\leq c\leq D_vy
\tag{13}
```

ならば、ある項 $`c_0`$ と主項列 $`r`$ が存在して

```math
c=D_vc_0+r,\qquad x\leq c_0\leq y.
\tag{14}
```

実際、$`c=0`$ は左の不等式に反する。$`c`$ の先頭を $`D_wc_0`$ とする。
左の不等式から $`v\leq w`$、右の不等式から $`w\leq v`$ が従うので $`w=v`$。
同じ添字の主項比較を本体へ戻すと $`x\leq c_0\leq y`$ を得る。

<a id="buc86-3-3-trig-cong"></a>
#### $`\operatorname{TriG}`$ の文脈保存 [BUC86-3-3-TRIG-CONG]

```math
\operatorname{TriG}(z,b_0,b)
\tag{15}
```

ならば、任意の前置列 $`p`$ と添字 $`v`$ について

```math
\begin{aligned}
\operatorname{TriG}(z,p+b_0,p+b),\cr 
\operatorname{TriG}(z,D_vb_0,D_vb)
\end{aligned}
\tag{16}
```

が成り立つ。

第一式を示すため $`p+b_0\leq c\leq p+b`$ とする。
[BUC86-3-3-SANDWICH-PREFIX](#buc86-3-3-sandwich-prefix) により
$`c=p+d`$、$`b_0\leq d\leq b`$ と書ける。(4) より

```math
G_u(p+b_0)=G_u(p)\cup G_u(b_0).
```

$`G_u(p)`$ の要素は同じ前置列をもつ $`c`$ の $`G_u`$-集合にそのまま入る。
$`G_u(b_0)`$ の要素には (15) を $`d`$ について適用し、得られた
$`G_u(d)`$ の要素を $`G_u(c)=G_u(p)\cup G_u(d)`$ へ入れればよい。

第二式では $`D_vb_0\leq c\leq D_vb`$ とする。
[BUC86-3-3-SANDWICH-D](#buc86-3-3-sandwich-d) により
$`c=D_vc_0+r`$、$`b_0\leq c_0\leq b`$ と書ける。
$`u\gt v`$ なら $`G_u(D_vb_0)=\varnothing`$ なので自明である。
$`u\leq v`$ なら

```math
G_u(D_vb_0)=\{b_0\}\cup G_u(b_0).
```

$`b_0`$ は $`c_0\in G_u(c)`$ によって上から押さえられる。
$`G_u(b_0)`$ には (15) を $`c_0`$ について適用する。
その証人が $`G_u(c_0)`$ に属すれば、(5) と
$`c_0\in G_u(c)`$ から $`G_u(c_0)\subseteq G_u(c)`$ である。
残りの $`G_u(z)`$ と $`\{0\}`$ はそのまま使える。これで (16) が従う。

### $`T_w`$ 定義域における基本列

<a id="buc86-3-3-oper-mono"></a>
#### 基本列の引数に関する単調性 [BUC86-3-3-OPER-MONO]

```math
\operatorname{dom}(a)=T_w,\quad
z_1,z_2\in T_w,\quad z_1\lt z_2
\quad\Longrightarrow\quad
a[z_1]\lt a[z_2].
\tag{17}
```

$`|a|`$ に関する強い帰納法で示す。複項 $`a=p+b`$ では
$`a[z]=p+b[z]`$ なので、帰納法の仮定を $`b`$ に適用し、共通前置列 $`p`$ を
付け戻す。

単項 $`a=D_vb`$ では定義域の定義を調べる。

- $`b=0`$ で $`\operatorname{dom}(a)=T_w`$ となるのは、有限後続添字の場合である。
  このとき $`a[z]=z`$ なので (17) は仮定そのものである。
- $`b\neq0`$、$`\operatorname{dom}(b)=T_u`$、$`v\gt u`$ の場合は
  $`w=u`$ かつ $`a[z]=D_v(b[z])`$ である。帰納法の仮定から
  $`b[z_1]\lt b[z_2]`$ であり、同じ添字 $`v`$ を付けて (17) を得る。
- $`\operatorname{dom}(b)=T_u`$、$`v\leq u`$ なら
  $`\operatorname{dom}(a)=\mathbb N_B`$ なので、現在の仮定には現れない。
  $`\operatorname{dom}(b)=\varnothing,\{0\},\mathbb N_B`$ の各場合も、
  定義から外側の定義域は $`T_w`$ にならないため除かれる。

以上で全ての分岐を尽くした。

<a id="buc86-3-3-oper-lower"></a>
#### 基本列要素の下界 [BUC86-3-3-OPER-LOWER]

```math
a\in OT,\quad \operatorname{dom}(a)=T_w,\quad z\in T_w
\quad\Longrightarrow\quad
z\leq a[z].
\tag{18}
```

複項 $`a=D_hc+p`$ では、$`a\in OT`$ の降順条件と
$`\operatorname{dom}(a)=T_w`$ から $`w\lt h`$ が従う。$`z\in T_w`$ の全ての
主項添字は $`h`$ より小さいので

```math
z\lt D_hc+p[z]=a[z].
```

単項 $`a=D_v0`$ で定義域が $`T_w`$ なら $`a[z]=z`$。
単項 $`a=D_vb`$、$`b\neq0`$ では、定義域が $`T_w`$ となる非自明な場合は
$`\operatorname{dom}(b)=T_w`$ かつ $`w\lt v`$ である。このとき
$`a[z]=D_v(b[z])`$ であり、添字境界から $`z\lt D_v(b[z])`$ を得る。
従って全場合で (18) が成り立つ。

### 反復項と定義域に関する補助事実

塔を

```math
X_0=D_w0,\qquad X_{i+1}=D_w(b[X_i])
\tag{19}
```

と定める。定義から

```math
X_i\in T_w
\tag{20}
```

である。

<a id="buc86-3-3-repeat"></a>
#### 同一主項の有限反復 [BUC86-3-3-REPEAT]

主項 $`q`$ の $`k`$ 回反復を $`q^{[k]}`$ と書く。主項 $`q`$ が順序数主項で
$`D_\omega`$-自由なら

```math
q^{[k]}\in OT_B.
\tag{21}
```

実際、同じ主項を並べた列は広義降順であり、各成分の $`OT`$ 性と
$`D_\omega`$-自由性はそのまま保たれる。形式的には $`k`$ に関して帰納し、
$`k+1`$ の場合に先頭の $`q`$ と帰納法で得た $`q^{[k]}`$ を連結する。
先頭比較は $`q\leq q`$ で閉じる。また $`k=n+1`$ のとき

```math
G_u(q^{[n+1]})=G_u(q),\qquad q\leq q^{[n+1]}.
\tag{22}
```

第一式は $`n`$ に関する帰納法で、(4) と
$`G_u(q)\cup G_u(q)=G_u(q)`$ を使う。第二式では両辺の先頭が同じ $`q`$ であり、
左辺の空の尾部は右辺の残りの尾部以下なので、辞書式順序の定義から従う。

<a id="buc86-3-3-g-above"></a>
#### 上位水準の $`G`$-集合の消滅 [BUC86-3-3-G-ABOVE]

さらに

```math
z\in T_w,\quad w\lt v
\quad\Longrightarrow\quad
G_v(z)=\varnothing
\tag{23}
```

である。$`z`$ の全主項添字は $`w`$ 以下なので、(4) の条件 $`v\leq h`$ を
満たす主項が一つもないからである。

定義域については次の二命題を使う。

<a id="buc86-3-3-dom-empty"></a>
**空定義域の特徴づけ [BUC86-3-3-DOM-EMPTY]**

```math
\operatorname{dom}(a)=\varnothing\Longrightarrow a=0,
\tag{24}
```

<a id="buc86-3-3-nat-nonzero"></a>
**自然数定義域における非零性 [BUC86-3-3-NAT-NONZERO]**

```math
\operatorname{dom}(a)=\mathbb N_B\Longrightarrow a[z]\neq0.
\tag{25}
```

[BUC86-3-3-DOM-EMPTY](#buc86-3-3-dom-empty) は
$`|a|`$ に関する強い帰納法で示す。複項なら末尾も空定義域をもち、
帰納法の仮定で末尾が $`0`$ となって、非空の主項列であることに反する。
単項 $`D_vb`$ では、基本列の定義の各分岐を調べると、空定義域が残るのは
$`\operatorname{dom}(b)=\varnothing`$ の場合だけであり、帰納法の仮定から
$`b=0`$ となる。しかし $`D_v0`$ の定義域はいずれも空でない。

[BUC86-3-3-NAT-NONZERO](#buc86-3-3-nat-nonzero) を示す。零項 $`a=0`$ は
$`\operatorname{dom}(0)=\varnothing\neq\mathbb N_B`$ なので前提を満たさない。
以下、$`\operatorname{dom}(a)=\mathbb N_B`$ となる $`a`$ の形を基本列の定義に
沿って尽くす。$`0`$ は空の主項列 $`\operatorname{Trm}[\,]`$ だから、$`a[z]`$ の
主項列が非空であることを各場合で示せば $`a[z]\neq0`$ が従う。

**複項 $`a=p+b`$（$`b\neq0`$）。** 基本列は尾部だけに作用するので
$`a[z]=p+b[z]`$ であり、先頭主項 $`p`$ がそのまま残る。従って主項列は非空で
あり $`a[z]\neq0`$。

**単項 $`a=D_v0`$。** 定義域は $`v=0`$ のとき $`\{0\}`$、有限後続 $`v`$ のとき
$`T_{v-1}`$、$`v=\omega`$ のとき $`\mathbb N_B`$ である。前提を満たすのは
$`v=\omega`$ の場合のみで、このとき $`(D_\omega0)[\bar n]`$ は有限添字をもつ
主項 $`D_{n+1}0`$ であり、単項なので非零である。

**単項 $`a=D_vb`$（$`b\neq0`$）。**
[BUC86-3-3-DOM-EMPTY](#buc86-3-3-dom-empty) より
$`\operatorname{dom}(b)=\varnothing`$ は起こらない。残る三場合について
外側の定義域 $`\operatorname{dom}(D_vb)`$ と基本列要素を調べる。

- $`\operatorname{dom}(b)=\{0\}`$：外側は $`\operatorname{dom}(D_vb)=\mathbb N_B`$
  である。$`z=\bar n`$ と書けて、基本列の定義（本証明の (51)）から
  $`(D_vb)[\bar n]=(D_v(b[0]))^{[n+1]}`$。これは主項 $`D_v(b[0])`$ を
  $`n+1\;(\geq1)`$ 個並べた非空の主項列だから非零である。
- $`\operatorname{dom}(b)=\mathbb N_B`$：外側も $`\mathbb N_B`$ である。基本列の
  定義（(54)）から $`(D_vb)[z]=D_v(b[z])`$ であり、単項なので非零である。
- $`\operatorname{dom}(b)=T_w`$ かつ $`v\leq w`$（塔分岐）：外側は
  $`\mathbb N_B`$ である。$`z=\bar n`$ と書けて、基本列の定義から
  $`(D_vb)[\bar n]=D_v(b[X_n])`$ であり、単項なので非零である。
- $`\operatorname{dom}(b)=T_w`$ かつ $`v\gt w`$：外側の定義域は
  $`\operatorname{dom}(b)=T_w`$ であって $`\mathbb N_B`$ ではないから、前提に
  現れない。

以上で $`\operatorname{dom}(a)=\mathbb N_B`$ となる全ての場合を尽くし、いずれも
$`a[z]\neq0`$ である。

<a id="buc86-3-3-close-d"></a>
#### 主項と反復の閉包 [BUC86-3-3-CLOSE-D]

```math
\begin{gathered}
y\in OT_B,\qquad v\lt\omega,\qquad
\forall x\in G_v(y)\ (x\lt y)
\cr 
\Longrightarrow D_vy\in OT_B.
\end{gathered}
\tag{26}
```

これは $`OT`$ の主項生成条件そのものである。$`v\lt\omega`$ と
$`y`$ の $`D_\omega`$-自由性から $`D_vy`$ も $`D_\omega`$-自由である。
[BUC86-3-3-REPEAT](#buc86-3-3-repeat) と合わせると、任意の $`n`$ について

```math
(D_vy)^{[n+1]}\in OT_B
\tag{27}
```

も得られる。

## 塔分岐

<a id="buc86-3-3-tower"></a>
### 塔分岐の同時不変量 [BUC86-3-3-TOWER]

```math
b\in OT,\quad b\neq0,\quad
\operatorname{dom}(b)=T_w,\quad v\leq w,
\quad
\forall x\in G_v(b)\ (x\lt b)
\tag{28}
```

とする。また全ての $`t\in T_w`$ について、帰納法の仮定として

```math
\operatorname{TriG}(t,b[t],b)
\tag{29}
```

および

```math
t\in OT_B\Longrightarrow b[t]\in OT_B
\tag{30}
```

を仮定する。塔 $`X_i`$ を (19) で定め、

```math
Y_i=b[X_i]
\tag{31}
```

と置く。示すべき外側の基本列要素は

```math
(D_vb)[\bar n]=D_vY_n
\tag{32}
```

である。

### 塔と基本列の単調性

(20)、(29)、および基本列の降下性
[BUC86-3-2A](Buchholz-1986-3.2-descent.md#buc86-3-2a) から

```math
\operatorname{TriG}(X_i,Y_i,b),\qquad Y_i\lt b
\tag{33}
```

を得る。[BUC86-3-3-OPER-LOWER](#buc86-3-3-oper-lower) から

```math
X_i\leq Y_i
\tag{34}
```

である。特に $`Y_0=0`$ と仮定すると
$`X_0\leq0\leq X_0`$ より $`X_0=0`$ となるが、
$`X_0=D_w0\neq0`$ なので

```math
Y_0\neq0.
\tag{35}
```

次に

```math
X_i\lt X_{i+1},\qquad Y_i\lt Y_{i+1}
\tag{36}
```

を $`i`$ に関する帰納法で示す。$`i=0`$ では、(35) より
$`0\lt Y_0`$ なので

```math
D_w0\lt D_wY_0,
```

すなわち $`X_0\lt X_1`$ である。
帰納段階では $`X_i\lt X_{i+1}`$ と (20) に
[BUC86-3-3-OPER-MONO](#buc86-3-3-oper-mono) を適用して
$`Y_i\lt Y_{i+1}`$ を得る。同じ添字 $`D_w`$ を付ければ
$`X_{i+1}\lt X_{i+2}`$ である。従って (36) が全ての $`i`$ で成立する。

### 第一不変量：$`G(Y_i)`$ の区間移送

任意の $`i,c,u`$ について

```math
Y_i\leq c\leq b
\Longrightarrow
G_u(Y_i)\preccurlyeq \{c\}\cup G_u(c)\cup\{0\}
\tag{37}
```

を $`i`$ に関する帰納法で示す。

$`i=0`$ では (33) を $`c`$ に適用すると

```math
G_u(Y_0)\preccurlyeq G_u(c)\cup G_u(X_0)\cup\{0\}.
```

$`X_0=D_w0`$ なので (4) より $`G_u(X_0)\subseteq\{0\}`$ であり、(37) を得る。

$`i+1`$ では (33) を $`X_{i+1}`$ について用いる。右辺に現れる
$`G_u(X_{i+1})`$ は、$`X_{i+1}=D_wY_i`$ より、空集合または
$`\{Y_i\}\cup G_u(Y_i)`$ である。

- 証人が $`Y_i`$ なら、(36) と $`Y_{i+1}\leq c`$ から $`Y_i\leq c`$ なので、
  $`c`$ 自身を新しい証人に取る。
- 証人が $`G_u(Y_i)`$ に属すれば、(36) から
  $`Y_i\leq Y_{i+1}\leq c`$ であるため、帰納法の仮定 (37) を適用する。
- 証人が $`G_u(c)`$ または $`\{0\}`$ に属すればそのままでよい。

不等式は必要に応じて推移律で合成する。これで (37) が示された。

### 第二不変量：塔の閉包と外側の $`G_v`$-条件

全ての $`i`$ について

```math
X_i\in OT_B
\quad\text{かつ}\quad
\forall x\in G_v(X_i)\ (x\lt Y_i)
\tag{38}
```

を帰納法で示す。

$`i=0`$ では $`X_0=D_w0\in OT_B`$ である。$`v\leq w`$ なので
$`G_v(X_0)=\{0\}`$ であり、(35) から $`0\lt Y_0`$。従って (38) が成り立つ。

$`i`$ で (38) が成り立つとする。(30) より $`Y_i=b[X_i]\in OT_B`$。
(33)、$`Y_i\leq b`$、(28)、および (38) に
[BUC86-3-4-G-CONTROL](#buc86-3-4-g-control) を適用すると

```math
\forall x\in G_v(Y_i)\ (x\lt Y_i)
\tag{39}
```

を得る。

また $`v\leq w`$ と (5) から

```math
G_w(b)\subseteq G_v(b),\qquad
G_w(X_i)\subseteq G_v(X_i).
```

従って同じ $`G`$-制御を水準 $`w`$ で適用して

```math
\forall x\in G_w(Y_i)\ (x\lt Y_i)
\tag{40}
```

を得る。(26) により

```math
X_{i+1}=D_wY_i\in OT_B.
```

さらに $`v\leq w`$ なので

```math
G_v(X_{i+1})=\{Y_i\}\cup G_v(Y_i).
```

$`Y_i\lt Y_{i+1}`$ は (36) から従う。$`x\in G_v(Y_i)`$ なら
(39) より $`x\lt Y_i\lt Y_{i+1}`$。従って (38) が $`i+1`$ でも成立する。

### 外側の主項の閉包

$`n`$ を固定する。(38) と (30) から $`Y_n\in OT_B`$。
(33)、$`Y_n\leq b`$、(28)、および (38) の $`G_v(X_n)`$ 条件を
[BUC86-3-4-G-CONTROL](#buc86-3-4-g-control) に入れると

```math
\forall x\in G_v(Y_n)\ (x\lt Y_n)
\tag{41}
```

となる。$`D_vb`$ が $`D_\omega`$-自由なので $`v\lt\omega`$ であり、(26) から

```math
D_vY_n\in OT_B.
\tag{42}
```

### 外側の $`\operatorname{TriG}`$

最後に

```math
\operatorname{TriG}(\bar n,D_vY_n,D_vb)
\tag{43}
```

を示す。$`D_vY_n\leq c\leq D_vb`$ とする。
[BUC86-3-3-SANDWICH-D](#buc86-3-3-sandwich-d) により

```math
c=D_vc_0+r,\qquad Y_n\leq c_0\leq b
\tag{44}
```

と書ける。$`u\gt v`$ なら $`G_u(D_vY_n)=\varnothing`$ なので自明である。
$`u\leq v`$ なら

```math
G_u(D_vY_n)=\{Y_n\}\cup G_u(Y_n).
```

$`Y_n`$ は $`c_0\in G_u(c)`$ によって上から押さえられる。
$`x\in G_u(Y_n)`$ なら (37) を $`c_0`$ に適用し、

```math
x\leq y,\qquad y\in\{c_0\}\cup G_u(c_0)\cup\{0\}
```

となる $`y`$ を取る。$`y=c_0`$ なら $`y\in G_u(c)`$。
$`y\in G_u(c_0)`$ なら $`c_0\in G_u(c)`$ と (5) から再び $`y\in G_u(c)`$。
$`y=0`$ ならそのままでよい。従って

```math
G_u(D_vY_n)\preccurlyeq G_u(c)\cup G_u(\bar n)\cup\{0\}
```

であり、(43) が示された。(42) と (43) が塔分岐で必要な二つの結論である。

## 強化同時帰納

<a id="buc86-3-3-master"></a>
### 基本列閉包と $`G`$-制御の同時命題 [BUC86-3-3-MASTER]

$`a\in OT`$ が $`D_\omega`$-自由で、$`a\neq0`$、かつ
$`z\in\operatorname{dom}(a)\cup\mathbb N_B`$ とする。次を同時に示す。

```math
\operatorname{TriG}(z,a[z],a),
\tag{45}
```

および

```math
z\in OT_B\Longrightarrow a[z]\in OT_B.
\tag{46}
```

$`|a|`$ に関する強い帰納法を行う。(45) は (46) より強い補助成分であり、
外側の主項を $`OT`$ に戻すための $`G`$-条件を供給する。

### 零項

$`a=0`$ は $`a\neq0`$ に反する。

### 単項 $`a=D_vb`$

$`D_vb\in OT`$ と $`D_\omega`$-自由性の定義から

```math
b\in OT_B,\qquad v\lt\omega,\qquad
\forall x\in G_v(b)\ (x\lt b)
\tag{47}
```

を得る。

#### $`b=0,\ v=0`$

定義から

```math
(D_00)[z]=0.
```

$`G_u(0)=\varnothing`$ なので (45) は空集合について自明であり、$`0\in OT_B`$
なので (46) も成り立つ。

#### $`b=0,\ v\neq0`$

$`v\lt\omega`$ なので $`v`$ は有限後続添字であり、

```math
(D_v0)[z]=z.
```

(46) は仮定 $`z\in OT_B`$ そのものである。(45) については、
$`z\leq c\leq D_v0`$ のとき

```math
G_u(z)\preccurlyeq G_u(c)\cup G_u(z)\cup\{0\}
```

が包含関係から従う。

以下 $`b\neq0`$ とする。$`\operatorname{dom}(b)=\varnothing`$ は
[BUC86-3-3-DOM-EMPTY](#buc86-3-3-dom-empty) により $`b=0`$ を与えるので
不可能である。残る三場合を調べる。

#### $`\operatorname{dom}(b)=\{0\}`$

この場合、外側の定義域は $`\mathbb N_B`$ である。従って
$`z=\bar n`$ となる $`n\in\mathbb N`$ が一意に存在する。

```math
X=b[0]
```

と置く。帰納法の仮定を $`b,0`$ に適用すると

```math
\operatorname{TriG}(0,X,b),\qquad X\in OT_B
\tag{48}
```

を得る。[BUC86-3-2A](Buchholz-1986-3.2-descent.md#buc86-3-2a) から
$`X\lt b`$ である。$`G_u(0)=\varnothing`$ なので
[BUC86-3-4-G-CONTROL](#buc86-3-4-g-control) を (48) と (47) に適用し、

```math
\forall x\in G_v(X)\ (x\lt X)
\tag{49}
```

を得る。

$`G_u(0)=\varnothing`$ だから、(48) の $`\operatorname{TriG}`$ に現れる $`0`$ を
$`z`$ に置き換えても右辺の集合は広がるだけである。従って
$`\operatorname{TriG}(z,X,b)`$。これを
[BUC86-3-3-TRIG-CONG](#buc86-3-3-trig-cong) で $`D_v`$ の文脈へ持ち上げ、
[BUC86-3-3-REPEAT](#buc86-3-3-repeat) を用いると

```math
\operatorname{TriG}\bigl(z,(D_vX)^{[n+1]},D_vb\bigr).
\tag{50}
```

基本列の定義は

```math
(D_vb)[z]=(D_vX)^{[n+1]}.
\tag{51}
```

(47)、(48)、(49)、および [BUC86-3-3-CLOSE-D](#buc86-3-3-close-d) から
右辺は $`OT_B`$ に属する。
(50), (51) が (45), (46) を与える。

#### $`\operatorname{dom}(b)=\mathbb N_B`$

外側の定義域も $`\mathbb N_B`$ なので、$`z\in\mathbb N_B`$ である。
帰納法の仮定を $`b,z`$ に適用し、

```math
\operatorname{TriG}(z,b[z],b),\qquad
z\in OT_B\Longrightarrow b[z]\in OT_B
\tag{52}
```

を得る。降下性 [BUC86-3-2A](Buchholz-1986-3.2-descent.md#buc86-3-2a)
から $`b[z]\lt b`$。また
[BUC86-3-3-NAT-NONZERO](#buc86-3-3-nat-nonzero) より $`b[z]\neq0`$。

$`z=\bar m`$ と書けば (4) より $`G_v(z)\subseteq\{0\}`$ であり、
$`b[z]\neq0`$ から $`0\lt b[z]`$。従って

```math
\forall x\in G_v(z)\ (x\lt b[z]).
```

[BUC86-3-4-G-CONTROL](#buc86-3-4-g-control) を (47), (52) に適用して

```math
\forall x\in G_v(b[z])\ (x\lt b[z])
\tag{53}
```

を得る。基本列の定義は

```math
(D_vb)[z]=D_v(b[z]).
\tag{54}
```

(52), (53), (26) から右辺は $`OT_B`$ に属する。また (52) の
$`\operatorname{TriG}`$ を (16) で $`D_v`$ の文脈へ持ち上げれば (45) を得る。

#### $`\operatorname{dom}(b)=T_w,\ v\leq w`$

この場合は外側の定義域が $`\mathbb N_B`$ である。従って
$`z=\bar n`$ と書ける。基本列の定義から

```math
(D_vb)[z]
=D_v\!\left(b[X_n]\right).
```

$`b`$ は $`a`$ の真部分項なので、全ての $`t\in T_w`$ に帰納法の仮定を
適用できる。従って (29), (30) が成立する。
[BUC86-3-3-TOWER](#buc86-3-3-tower) を適用すると (45), (46) を得る。

#### $`\operatorname{dom}(b)=T_w,\ v\gt w`$

この場合は

```math
(D_vb)[z]=D_v(b[z]).
\tag{55}
```

帰納法の仮定を $`b,z`$ に適用して

```math
\operatorname{TriG}(z,b[z],b),\qquad
z\in OT_B\Longrightarrow b[z]\in OT_B
\tag{56}
```

を得る。$`z\in T_w`$ または $`z\in\mathbb N_B\subseteq T_w`$ であり、
$`w\lt v`$ なので [BUC86-3-3-G-ABOVE](#buc86-3-3-g-above) より
$`G_v(z)=\varnothing`$。
降下性から $`b[z]\lt b`$ である。従って
[BUC86-3-4-G-CONTROL](#buc86-3-4-g-control) を (47), (56) に適用して

```math
\forall x\in G_v(b[z])\ (x\lt b[z])
\tag{57}
```

を得る。(56), (57), (26) から (55) は $`OT_B`$ に属する。
(56) の $`\operatorname{TriG}`$ を (16) で持ち上げれば (45) も得る。

これで単項の全分岐を尽くした。

### 複項 $`a=p+b`$

$`p`$ を先頭主項、$`b\neq0`$ を残りの非空尾部とする。順序数項と
$`D_\omega`$-自由性の定義から

```math
p\text{ は順序数主項かつ }D_\omega\text{-自由},\qquad b\in OT_B,
```

また $`p`$ は $`b`$ の先頭主項以上である。$`\operatorname{dom}(a)= \operatorname{dom}(b)`$ なので、$`z`$ は $`b`$ に対する帰納法の条件も満たす。
帰納法の仮定から

```math
\operatorname{TriG}(z,b[z],b),\qquad
z\in OT_B\Longrightarrow b[z]\in OT_B.
\tag{58}
```

基本列は尾部だけに作用するから

```math
a[z]=p+b[z].
\tag{59}
```

(58) の第一式を
[BUC86-3-3-TRIG-CONG](#buc86-3-3-trig-cong) で前置主項 $`p`$ の文脈へ
持ち上げると (45) が従う。

残るのは (59) が順序数項であることの確認である。
$`b[z]=0`$ なら $`p+b[z]=p`$ であり、既に得た $`p`$ の順序数主項性と
$`D_\omega`$-自由性から $`p\in OT_B`$ である。
$`b[z]\neq0`$ とし、その先頭を $`q'`$、$`b`$ の先頭を $`q`$ とする。
降下性 [BUC86-3-2A](Buchholz-1986-3.2-descent.md#buc86-3-2a)
により

```math
b[z]\lt b.
```

辞書式順序の定義から $`q'\leq q`$ である。元の $`a=p+b`$ が順序数項なので
$`q\leq p`$。従って

```math
q'\leq q\leq p.
```

よって $`p+b[z]`$ の主項列も広義降順である。各成分の $`OT`$ 性は
(58) と $`p`$ の仮定から、$`D_\omega`$-自由性も同じ二つから従う。
従って (59) は $`OT_B`$ に属し、複項の場合の (46) も示された。

強い帰納法が完了し、[BUC86-3-3-MASTER](#buc86-3-3-master) が成立する。

## 補題3.3の導出

まず $`a,z\in OT`$ が $`D_\omega`$-自由で、
$`a\neq0`$、$`z\in\operatorname{dom}(a)\cup\mathbb N_B`$ とする。
[BUC86-3-3-MASTER](#buc86-3-3-master) の (46) を適用すれば

```math
a[z]\in OT_B
```

を得る。これが [BUC86-3-3-GENERAL](#buc86-3-3-general) である。

最後に $`a\in OT_B`$、$`a\neq0`$、$`n\in\mathbb N`$ とする。
$`\bar n\in\mathbb N_B`$ であり、自然数項は順序数項かつ $`D_\omega`$-自由である。
従って強化形を $`z=\bar n`$ に適用して

```math
a[\bar n]\in OT_B
```

を得る。これが [BUC86-3-3](#buc86-3-3) である。□

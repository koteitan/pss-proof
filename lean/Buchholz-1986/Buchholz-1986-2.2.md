[← Back](README.md)

# Buchholz (1986) §2.2 — $`G_u`$、$`T_B`$、$`OT_B`$

出典：W. Buchholz, *A new system of proof-theoretic ordinal functions*,
Annals of Pure and Applied Logic 32 (1986), §2.

<a id="buc86-2-2-g"></a>
## フィルトレーション $`G_u`$

項に現れる崩壊記号のうち、水準 $`u`$ 以上のものの本体を再帰的に集める。
主項 $`D_vb`$（[定義](Buchholz-1986-2.1.md#buc86-2-1-syntax)）について

```math
G_u(D_v b)=
\begin{cases}
\{b\}\cup G_u(b),&u\leq v,\cr 
\varnothing,&v\lt u,
\end{cases}
```

一般の項について

```math
G_u(a_0,\ldots,a_{k-1})
=\bigcup_{i\lt k}G_u(a_i)
```

とする。

<a id="buc86-2-2-otb"></a>
<a id="buc86-2-2-ot"></a>
## 項クラス [BUC86-2-2-OTB]

各 $`v\in\mathbb N_\omega`$ に対して

```math
T_v
:=
\{0\}
\cup
\bigcup_{n\in\mathbb N}
\left\{
(D_{u_0}a_0,\ldots,D_{u_n}a_n)
\mathrel{}\middle|\mathrel{}
\begin{gathered}
u_0,\ldots,u_n\in\mathbb N_\omega,\quad
a_0,\ldots,a_n\in T,\cr 
\forall i\leq n\;(u_i\leq v)
\end{gathered}
\right\}.
\tag{1}
```

（従って (1) が制限するのは、外側の主項列
$`(D_{u_0}a_0,\ldots,D_{u_n}a_n)`$ の添字 $`u_0,\ldots,u_n`$ である。
各本体 $`a_i`$ の内部に現れる添字には、この条件を再帰的には課さない。）

一方、項に対する条件 $`F_T`$ と主項に対する条件 $`F_P`$ を相互再帰的に

```math
\begin{aligned}
F_T((p_0,\ldots,p_{k-1}))
&\Longleftrightarrow
\forall i\lt k\;F_P(p_i),\cr 
F_P(D_u b)
&\Longleftrightarrow
u\neq\omega\ \land\ F_T(b)
\end{aligned}
\tag{2}
```

と定め、

```math
T_B:=\{a\in T\mid F_T(a)\}
\tag{3}
```

とする。（(2) の第二式が主項 $`D_u b`$ の本体 $`b`$ に対して再び
$`F_T(b)`$ を要求するため、外側だけでなく任意の深さに現れる全ての
主項の添字が $`\omega`$ と異なることになる。）

主項列が広義降順であることを $`\operatorname{desc}`$ と書く。順序数項の
集合 $`OT`$ を次の構造的条件で定める。

```math
\begin{aligned}
0&\in OT,\cr 
D_vb\in OT
&\Longleftrightarrow
b\in OT\ \land\ \forall x\in G_v(b)\;(x\lt b),\cr 
(a_0,\ldots,a_{k-1})\in OT
&\Longleftrightarrow
\bigwedge_{i\lt k}a_i\in OT
\ \land\
a_0\geq\cdots\geq a_{k-1}.
\end{aligned}
```

停止性証明で用いる表記系は

```math
OT_B=OT\cap T_B
```

である。

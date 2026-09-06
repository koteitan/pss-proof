[← Back](README.md)

# $`OT_B`$ の整礎性の構文的証明 — Bachmann 共終性

<a id="otb-bc"></a>
## Bachmann 共終性定理 [OTB-BC]

$`a,b\in OT_B`$（[定義](../Buchholz-1986/Buchholz-1986-2.2.md#buc86-2-2-otb)）かつ $`b\lt a`$ とする。

<a id="otb-bc-nat"></a>
### 数項定義域の場合 [OTB-BC-NAT]

$`\operatorname{dom}(a)\in\{\{0\},\mathbb N\}`$ なら

```math
\exists n\in\mathbb N\quad b\leq a[n].
```

<a id="otb-bc-t"></a>
### $`T_m`$ 定義域の場合 [OTB-BC-T]

$`\operatorname{dom}(a)=T_m`$ なら

```math
\exists z\in T_m\cap OT_B\quad b\leq a[z].
```

これは基本列が $`a`$ の下に共終であるという Bachmann 型の性質である。

## 準備

まず次の事実を項の構造から示す。

```math
\begin{aligned}
z_1\lt z_2,\ z_1,z_2\in T_m
&\Longrightarrow a[z_1]\lt a[z_2]
&&(\operatorname{dom}(a)=T_m),\cr 
x\in G_u(t),\ t\in OT
&\Longrightarrow x\in OT,\cr 
a_0\geq\cdots\geq a_k
&\Longrightarrow
\text{各末尾列も降順}.
\end{aligned}
```

塔

```math
x_0=D_u0,\qquad x_{n+1}=D_u(c[x_n])
```

については

```math
x_n\in T_u,\qquad x_n\lt x_{n+1}
```

を帰納法で得る。

さらに $`\operatorname{dom}(c)=T_u`$、$`e\lt c`$ で
$`G_u(e)\lt c`$ なら

```math
\exists n\quad e\leq c[x_n]
\tag{*}
```

を示す。$`e`$ の $`G_u`$-要素を順に内部帰納へ送り、有限個の証人番号の
最大値を取る。塔の単調性により、それより後の一つの $`x_n`$ が全ての
要求を同時に満たす。これが崩壊分岐の共終性である。

## 主証明

$`a`$ の構造的大きさに関する強い帰納法を行う。

複項
```math
a=p+c
```
では、$`b\lt a`$ の最初の不一致位置を調べる。先頭主項が $`p`$ より小さければ、
どの $`a[z]`$ も $`b`$ より上にある。先頭が一致する場合は尾部 $`c`$ に
帰納法の仮定を適用し、共通の前置主項を付け戻す。

単項 $`a=D_vc`$ では次の場合に分ける。

- $`c=0,v=0`$：$`b\lt D_00`$ は $`b=0`$ を強制し、$`a[0]=0`$ でよい。
- $`c=0,v=u+1`$：$`a[z]=z`$。$`b\lt a`$ から $`b\in T_u`$ が従うので
  $`z=b`$ と取る。
- $`\operatorname{dom}(c)=\{0\}`$：
  $`a[n]`$ は $`D_v(c[0])`$ の $`n+1`$ 個の和である。
  $`b`$ の同じ添字をもつ先頭本体に帰納法を適用し、必要なら $`b`$ の
  残りの主項数だけ反復数を増やす。
- $`\operatorname{dom}(c)=T_u,\ v\leq u`$：
  ```math
  a[n]=D_v(c[x_n]).
  ```
  同じ添字をもつ $`b`$ の先頭本体を $`e`$ とすれば、順序数項の
  $`G`$-条件から $`(*)`$ の仮定が満たされる。従ってある $`n`$ について
  $`e\leq c[x_n]`$、ゆえに $`b\leq a[n]`$ である。
- その他：$`a[z]=D_v(c[z])`$ なので $`c`$ への帰納法で証人 $`z`$ を得る。
  定義域が $`T_m`$ の場合、等号に止まった証人には $`D_00`$ を加えて
  狭義に上げる。基本列の単調性により必要な不等式が得られる。

以上で全ての定義域について共終性が成立する。□

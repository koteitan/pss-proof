[← Back](README.md)

# Buchholz (1986) 補題3.2(a) — 基本列は降下する

<a id="buc86-3-2a"></a>
## 基本列の降下性 [BUC86-3-2A]

$`a\in OT_B`$、$`a\neq0`$ とし、

```math
z\in\operatorname{dom}(a)\cup\mathbb N
```

とする。このとき

```math
a[z]\lt a.
```

特に任意の $`n\in\mathbb N`$ について

```math
a[n]\lt a
```

である。

## 証明

項 $`a`$ の構造的大きさに関する強い帰納法を行う。同時に、
定義域が $`T_w`$ であるとき

```math
z\in T_w,\qquad a\in OT
\quad\Longrightarrow\quad z\lt\operatorname{head}(a)
```

という補助事実を用いる。

### 零項と複項

零項は $`a\neq0`$ に反する。複項

```math
a=a_0+\cdots+a_k\qquad(k\geq1)
```

では基本列は末尾成分だけを変えるので

```math
a[z]=a_0+\cdots+a_{k-1}+a_k[z].
```

帰納法の仮定から $`a_k[z]\lt a_k`$ であり、共通の前置列を付けても
辞書式順序は保存されるから $`a[z]\lt a`$ である。

### $`D_v0`$

$`v=0`$ なら $`(D_00)[z]=0\lt D_00`$。
$`v=u+1`$ なら $`(D_{u+1}0)[z]=z`$ であり、
$`z\in T_u`$ の全ての最上位添字は $`u+1`$ より小さいため
$`z\lt D_{u+1}0`$ である。
$`v=\omega`$ では $`(D_\omega0)[n]=D_{n+1}0\lt D_\omega0`$ である。

### $`\operatorname{dom}(b)=\{0\}`$

```math
(D_vb)[n]=(D_vb[0])\cdot(n+1).
```

帰納法の仮定から $`b[0]\lt b`$ である。したがって各コピーの主項
$`D_vb[0]`$ は $`D_vb`$ より小さく、その有限和も辞書式順序で
$`D_vb`$ より小さい。

### 塔の場合

$`\operatorname{dom}(b)=T_u`$ かつ $`v\leq u`$ とする。このとき

```math
(D_vb)[n]=D_v(b[x_n]).
```

補助列の構成から $`x_n\in T_u=\operatorname{dom}(b)`$ である。
帰納法の仮定を $`b`$ に適用して

```math
b[x_n]\lt b
```

を得る。同じ添字 $`v`$ の主項では本体の狭義順序が保存されるので
```math
D_v(b[x_n])\lt D_vb.
```

### 残りの場合

それ以外は

```math
(D_vb)[z]=D_v(b[z])
```

である。$`b`$ は真部分項なので帰納法の仮定から $`b[z]\lt b`$、
従って $`D_v(b[z])\lt D_vb`$ である。

全ての場合に $`a[z]\lt a`$ が示された。□

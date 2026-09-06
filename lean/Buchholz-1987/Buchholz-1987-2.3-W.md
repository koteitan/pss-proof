[← Back](README.md)

# Buchholz (1987) §2 — $`W_v`$ の反復帰納的定義

出典：W. Buchholz, *An independence result for $`(\Pi^1_1\text{-CA})+\mathrm{BI}`$*,
Annals of Pure and Applied Logic 33 (1987), pp. 137–138
（1984年11月27日受理）。

## 作用素 $`A_v`$

既に $`u\lt v`$ に対する集合 $`W_u`$ が定義されているとする。
集合 $`X`$ に対し、$`A_v(X)`$ を次のいずれかを満たす項 $`a`$ の集合とする。

```math
\begin{aligned}
&a=0,\cr 
&\operatorname{dom}(a)\in\{\{0\},\mathbb N\}
\ \land\ \forall n\in\mathbb N\;(a[n]\in X),\cr 
&\exists u\lt v\;
\bigl(\operatorname{dom}(a)=T_u
\land \forall z\in W_u\;(a[z]\in X)\bigr).
\end{aligned}
```

$`A_v`$ は $`X`$ について単調である。そこで

```math
W_v=\operatorname{lfp}(A_v)
```

と定める。ただし $`W_u`$ が下位水準の引数として現れるため、族
$`(W_v)`$ は $`v`$ の小さい方から順に反復して構成する。

最小不動点の性質から次を得る。

<a id="buc87-a1"></a>
**不動点性 [BUC87-A1]**

```math
A_v(W_v)=W_v
```

<a id="buc87-a2"></a>
**最小性 [BUC87-A2]**

```math
A_v(X)\subseteq X\Longrightarrow W_v\subseteq X
```

を得る。

<a id="buc87-w-mono"></a>
## 水準単調性 [BUC87-W-MONO]

```math
u\leq v\Longrightarrow W_u\subseteq W_v
```

を示す。$`A_u(X)\subseteq A_v(X)`$ は、第三分岐の条件 $`r\lt u`$ から
$`r\lt v`$ が従うことによる。$`W_v`$ が $`A_v`$ の不動点であることと
[BUC87-A2](#buc87-a2) を用いれば、$`W_u`$ の生成に関する帰納法で結論を得る。

<a id="buc87-dfree-bounded"></a>
## 有界な $`D_\omega`$-自由項 [BUC87-DFREE-BOUNDED]

後の [BUC87-2-4B](Buchholz-1987-2.4-2.8.md#buc87-2-4b) と
[BUC87-2-8](Buchholz-1987-2.4-2.8.md#buc87-2-8) を用いると、最上位添字が $`m`$ 以下で
$`D_\omega`$ を含まない項 $`a`$ は

```math
a\in W_m
```

となる。各主項をまずそれ自身の水準の $`W`$ に入れ、水準単調性で
$`W_m`$ へ持ち上げ、加法閉包で再び一つの項へ組み立てればよい。

<a id="buc87-dfree-total"></a>
### $`D_\omega`$-自由項の被覆 [BUC87-DFREE-TOTAL]

また任意の $`D_\omega`$-自由項には有限な添字上界が存在するため、

```math
\forall a\in T_B\;\exists m\;(a\in W_m)
```

を得る。

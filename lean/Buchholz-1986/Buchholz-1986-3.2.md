[← Back](README.md)

# Buchholz (1986) §3.2 — 加法、定義域、基本列の準備

出典：W. Buchholz, *A new system of proof-theoretic ordinal functions*,
Annals of Pure and Applied Logic 32 (1986), pp. 203–204.

## 加法と自然数倍

項を主項列とみなし、加法を列の連結として定める。

```math
(a_0,\ldots,a_{k-1})+(b_0,\ldots,b_{\ell-1})
=(a_0,\ldots,a_{k-1},b_0,\ldots,b_{\ell-1}).
```

自然数倍は

```math
a\cdot0=0,\qquad a\cdot(n+1)=a\cdot n+a
```

である。自然数 $`n`$ は $`D_0 0`$ を $`n`$ 個並べた項として表す。

## 定義域

各項 $`a`$ の基本列の定義域は、次の四種類のいずれかである。

```math
\operatorname{dom}(a)\in
\{\varnothing,\{0\},\mathbb N,T_u\}.
```

零項では空集合、複項では末尾主項の定義域を採用する。単項 $`D_vb`$ では
本体 $`b`$ の形に従って分岐する。

```math
\begin{array}{c|c}
\text{形}&\operatorname{dom}\cr  \hline
D_0 0&\{0\}\cr 
D_{u+1}0&T_u\cr 
D_\omega0&\mathbb N\cr 
D_vb,\ \operatorname{dom}(b)=\{0\}&\mathbb N\cr 
D_vb,\ \operatorname{dom}(b)=T_u,\ v\leq u&\mathbb N\cr 
D_vb,\ \text{その他}&\operatorname{dom}(b).
\end{array}
```

この有限な場合分けによって、後の基本列演算を完全な再帰関数として扱える。

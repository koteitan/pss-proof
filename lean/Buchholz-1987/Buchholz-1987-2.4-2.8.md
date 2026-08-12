[← Back](README.md)

# Buchholz (1987) 補題2.4–2.8 — \(W_v\) の閉包

出典：W. Buchholz, *An independence result for \((\Pi^1_1\text{-CA})+\mathrm{BI}\)*,
Annals of Pure and Applied Logic 33 (1987), pp. 138–140
（1984年11月27日受理）。

基本列の塔分岐には、未公刊 [Buc2] p.6 Definition 6 の

\[
x_0=D_u0,\qquad x_{i+1}=D_u(b[x_i])
\]

を用いる。

<a id="buc87-2-4"></a>
## 補題2.4 [BUC87-2-4]

\(A_v(X)\subseteq X\) かつ \(a\in X\) とする。

\[
X^{(a)}=\{y\mid a+y\in X\}
\]

と置くと次が成り立つ。

<a id="buc87-2-4a"></a>
**補助閉包 [BUC87-2-4A]**

\[
A_v(X^{(a)})\subseteq X^{(a)}.
\]

実際、\(b\in A_v(X^{(a)})\) の生成分岐ごとに調べれば、
\(\operatorname{dom}(a+b)=\operatorname{dom}(b)\) かつ
\((a+b)[z]=a+b[z]\) である。従って全ての直前項が \(X\) に入り、
\(a+b\in A_v(X)\subseteq X\) となる。

[BUC87-A2](Buchholz-1987-2.3-W.md#buc87-a2) を適用して次を得る。

<a id="buc87-2-4b"></a>
**加法閉包 [BUC87-2-4B]**

\[
a,b\in W_v\Longrightarrow a+b\in W_v
\]

を得る。従って \(a\in W_v\) なら全ての \(n\) について \(a\cdot n\in W_v\) である。

<a id="buc87-2-5"></a>
## 補題2.5 [BUC87-2-5]

\(A_v(X)\subseteq X\)、\(a\in X\) なら

\[
D_u b\in X
\]

を、\(b\) の定義域によって場合分けして示す。零本体、\(\{0\}\)、
\(\mathbb N\)、\(T_k\) の各場合で、基本列の値が既に \(X\) に入ることを
[BUC87-2-4](#buc87-2-4) と帰納法から得る。

特に

\[
D_{u+1}0\in W_{u+1}
\]

であり、塔分岐に現れる全ての \(x_i\) も適切な \(W\) に属する。

<a id="buc87-2-6"></a>
## 補題2.6 [BUC87-2-6]

\[
W^*=\{x\mid \forall u\in\mathbb N\;(D_ux\in W_u)\}
\]

と置く。このとき

\[
A_\omega(W^*)\subseteq W^*.
\]

\(b\in A_\omega(W^*)\) と \(v<\omega\) を固定し、\(D_vb\in W_v\) を示す。
本体が零の場合、後続の場合、定義域が \(\{0\}\)、\(\mathbb N\)、\(T_u\)
の場合に分ける。

核心は \(\operatorname{dom}(b)=T_u\) かつ \(v\leq u\) の場合である。
このとき

\[
(D_vb)[n]=D_v(b[x_n]).
\]

補助列についての帰納法から \(x_n\in W_u\) を得るので、
\(b[x_n]\in W^*\)、従って \(D_v(b[x_n])\in W_v\) である。
よって (W2) から \(D_vb\in W_v\) となる。

<a id="buc87-2-7"></a>
## 補題2.7 [BUC87-2-7]

\(A_\omega(X)\subseteq X\) とする。\(D_\omega\) を含まない項 \(a\) について

\[
a\in X
\]

を項の長さに関する帰納法で示す。

零項は直ちに \(X\) に入る。複項は前置部と末尾部に分け、
[BUC87-2-4A](#buc87-2-4a) を用いて和を復元する。主項 \(D_vb\) では、
帰納法の仮定から \(b\in W^*\) を得て、[BUC87-2-6](#buc87-2-6) と
[BUC87-A2](Buchholz-1987-2.3-W.md#buc87-a2) によって \(D_vb\in X\) を導く。

<a id="buc87-2-8"></a>
## 補題2.8 [BUC87-2-8]

[BUC87-2-7](#buc87-2-7) を \(X=W^*\) に適用すると、全ての
\(D_\omega\)-自由項について

\[
a\in W^*
\]

となる。特に

\[
D_u a\in W_u.
\]

この主項閉包と [BUC87-2-4B](#buc87-2-4b) の加法閉包を合わせれば、任意の
\(D_\omega\)-自由な \(T_u\)-項が \(W_u\) に属する。□

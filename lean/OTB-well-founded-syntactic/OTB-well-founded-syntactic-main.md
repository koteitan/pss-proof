[← Back](README.md)

# \(OT_B\) の整礎性 — 順序数意味論を使わない構文的証明

PSS 原文はこの整礎性を独立した命題として用い、その根拠に [Buc1] Lemma 2.2 を挙げる。
[Buc1] Lemma 2.2 自体は評価写像 \(o\) の意味論的性質であり、以下の定理とは異なる。
ここでは評価写像を使わず、Buchholz 項、基本列、\(W_u\) と可到達性だけから
PSS 原文が必要とする整礎性を直接証明する。

## 記法

Buchholz 項全体を \(T\) とし、零項を \(0\) と書く。項 \(a\) の基本列を

\[
a[z]=\operatorname{oper}(a,z)
\]

と書き、自然数 \(n\) を表す項を \(\bar n\) とする。また

\[
\operatorname{DF}(a)
\]

は \(a\) が \(D_\omega\) を含まないことを表す。このとき

\[
a\in OT_B
\quad\Longleftrightarrow\quad
a\in OT\ \land\ \operatorname{DF}(a).
\tag{0}
\]

以下では

\[
R(a,b)
\quad\Longleftrightarrow\quad
a\in OT_B\ \land\ b\in OT_B\ \land\ a<b
\tag{1}
\]

と定める。したがって \(R(a,b)\) は「\(a\) が \(b\) の真に小さい
\(OT_B\)-前者である」という向きの関係である。

関係 \(R\) に関する項 \(c\) の可到達性を

\[
\operatorname{Acc}_R(c)
\]

と書く。可到達性の導入則と逆向きの使用則は、それぞれ

\[
\frac{\forall b\,(R(b,c)\Rightarrow \operatorname{Acc}_R(b))}
     {\operatorname{Acc}_R(c)},
\qquad
\frac{\operatorname{Acc}_R(c)\qquad R(b,c)}
     {\operatorname{Acc}_R(b)}
\tag{2}
\]

である。

<a id="otb-wf"></a>
## \(OT_B\) の整礎性 [OTB-WF]

関係 \(R\) は整礎である。すなわち

\[
\forall c\in T\quad \operatorname{Acc}_R(c)
\tag{3}
\]

が成り立つ。

## 準備1：零項と定義域

任意の項 \(y\) について

\[
\neg(y<0)
\tag{4}
\]

である。実際、Buchholz 項を principal 項の有限列として表すと、\(0\) は空列である。
辞書式順序の定義上、空列も非空列も空列より真に小さくはならない。

また

\[
\operatorname{dom}(0)=\varnothing
\tag{5}
\]

であり、次の三集合はいずれも空でない。

\[
\{0\}\neq\varnothing,
\qquad
\mathbb N_B:=\{\bar n:n\in\mathbb N\}\neq\varnothing,
\qquad
T_m\neq\varnothing.
\tag{6}
\]

最初の二つにはそれぞれ \(0\) と \(\bar0=0\) が属し、\(0\in T_m\) でもあるからである。
従って

\[
\operatorname{dom}(c)\in\bigl\{\{0\},\mathbb N_B,T_m\bigr\}
\quad\Longrightarrow\quad c\neq0.
\tag{7}
\]

実際、もし \(c=0\) なら (5) により、(6) のいずれかの非空集合が空集合に等しいことに
なってしまう。

## 準備2：反復帰納的集合 \(W_u\)

自然数 \(u\) と項集合 \(X\subseteq T\) に対して作用素 \(A_u\) を次で定める。

\[
\begin{aligned}
c\in A_u(X)\quad\Longleftrightarrow\quad{}
&c=0\\
&\lor\Bigl(
  \bigl(\operatorname{dom}(c)=\{0\}\lor
        \operatorname{dom}(c)=\mathbb N_B\bigr)
  \land \forall n\in\mathbb N\;c[\bar n]\in X
  \Bigr)\\
&\lor\Bigl(
  \exists m<u\;\bigl(
    \operatorname{dom}(c)=T_m
    \land \forall z\in W_m\;c[z]\in X
  \bigr)
  \Bigr).
\end{aligned}
\tag{8}
\]

ここで \(W_u\) は \(A_u\) の最小不動点である。従って
[BUC87-A2](../Buchholz-1987/Buchholz-1987-2.3-W.md#buc87-a2) の帰納法原理を使える。

\[
A_u(Y)\subseteq Y
\quad\Longrightarrow\quad
W_u\subseteq Y.
\tag{9}
\]

<a id="otb-dfree-in-w"></a>
### 有界な \(D_\omega\)-自由項の閉包 [OTB-DFREE-IN-W]

以下で必要となる \(W_m\) の閉包性は

\[
\operatorname{DF}(z)\land z\in T_m
\quad\Longrightarrow\quad
z\in W_m
\tag{10}
\]

である。これを確認しておく。\(z\) を principal 項の有限列

\[
z=D_{k_1}b_1+\cdots+D_{k_r}b_r
\]

に分解する。\(z\in T_m\) より各 \(k_i\le m\) であり、
\(\operatorname{DF}(z)\) より \(k_i<\omega\) かつ
\(\operatorname{DF}(b_i)\) である。
[BUC87-2-8](../Buchholz-1987/Buchholz-1987-2.4-2.8.md#buc87-2-8) から

\[
D_{k_i}b_i\in W_{k_i}
\]

を得る。[BUC87-W-MONO](../Buchholz-1987/Buchholz-1987-2.3-W.md#buc87-w-mono) と
[BUC87-2-4B](../Buchholz-1987/Buchholz-1987-2.4-2.8.md#buc87-2-4b) の加法閉包を
順に用いると、
principal 項を左から再び足し合わせて \(z\in W_m\) を得る。空列の場合は
\(z=0\in W_m\) である。これで (10) が従う。

<a id="otb-bc-w"></a>
## 準備3：Bachmann 共終性の \(W\)-形 [OTB-BC-W]

\(a,b\in OT_B\) かつ \(b<a\) とする。Bachmann 共終性定理
[OTB-BC-NAT](OTB-well-founded-syntactic-cofinality.md#otb-bc-nat) と
[OTB-BC-T](OTB-well-founded-syntactic-cofinality.md#otb-bc-t) から
次を得る。

<a id="otb-bc-w-nat"></a>
### 数項定義域の場合 [OTB-BC-W-NAT]

\[
\operatorname{dom}(a)=\{0\}
\ \lor\
\operatorname{dom}(a)=\mathbb N_B
\quad\Longrightarrow\quad
\exists n\in\mathbb N\quad b\le a[\bar n].
\tag{11}
\]

<a id="otb-bc-w-t"></a>
### \(T_m\) 定義域の場合 [OTB-BC-W-T]

\[
\operatorname{dom}(a)=T_m
\quad\Longrightarrow\quad
\exists z\;\left\{
\begin{array}{l}
z\in W_m,\\
z\in\operatorname{dom}(a),\\
z\in OT,\\
\operatorname{DF}(z),\\
b\le a[z].
\end{array}\right.
\tag{12}
\]

(12) のうち、Bachmann 共終性が直接与えるのは後ろ四条件である。
\(z\in\operatorname{dom}(a)=T_m\) と \(\operatorname{DF}(z)\) に
[OTB-DFREE-IN-W](#otb-dfree-in-w) を適用すれば、残る \(z\in W_m\) も得られる。

さらに、基本列閉包の強化形
[BUC86-3-3-GENERAL](../Buchholz-1986/Buchholz-1986-3.3.md#buc86-3-3-general)
により次が成り立つ。

\[
\begin{aligned}
&a\in OT_B, a\neq0
  &&\Longrightarrow& a[\bar n]&\in OT_B,\\
&a\in OT_B, a\neq0, z\in\operatorname{dom}(a),\ z\in OT_B
  &&\Longrightarrow& a[z]&\in OT_B.
\end{aligned}
\tag{13}
\]

二行目はより正確には、\(a,z\) のそれぞれについて \(OT\) 性と
\(D_\omega\)-自由性を分けて仮定し、結論でもその二条件を別々に得る形である。
(0) によって上の簡潔な形へまとめられる。

## 証明

### 1. \(W_u\) の全要素が可到達であること

集合

\[
Y:=\{c\in T:\operatorname{Acc}_R(c)\}
\tag{14}
\]

を取る。任意の \(u\) について

\[
W_u\subseteq Y
\tag{15}
\]

を示すため、(9) により

\[
A_u(Y)\subseteq Y
\tag{16}
\]

を証明すればよい。そこで \(c\in A_u(Y)\) とする。

まず \(c\notin OT_B\) の場合を処理する。このとき任意の \(y\) に対し
\(R(y,c)\) ならば、その定義 (1) から \(c\in OT_B\) が従い、仮定に反する。
従って \(c\) は \(R\)-前者を持たず、(2) により

\[
\operatorname{Acc}_R(c)
\]

である。以下では \(c\in OT_B\) と仮定し、(8) の三分岐を調べる。

#### 分岐1：\(c=0\)

\(R(y,c)\) と仮定すると \(y<c=0\) であるが、これは (4) に反する。
従ってこの場合も \(c\) は前者を持たず、\(\operatorname{Acc}_R(c)\) である。

#### 分岐2：\(\operatorname{dom}(c)=\{0\}\) または \(\mathbb N_B\)

(8) のこの分岐から

\[
\forall n\in\mathbb N\quad c[\bar n]\in Y
\tag{17}
\]

も得ている。(7) により \(c\neq0\) である。

\(R(b,c)\) を満たす任意の \(b\) を取る。(1) より

\[
b\in OT_B,\qquad c\in OT_B,\qquad b<c.
\tag{18}
\]

[OTB-BC-W-NAT](#otb-bc-w-nat) を適用して

\[
\exists n\quad b\le c[\bar n]
\tag{19}
\]

を得る。この \(n\) を固定する。(17) より

\[
\operatorname{Acc}_R(c[\bar n])
\tag{20}
\]

であり、[BUC86-3-3](../Buchholz-1986/Buchholz-1986-3.3.md#buc86-3-3) より
\(c[\bar n]\in OT_B\) である。

広義順序の定義により (19) は

\[
b<c[\bar n]
\quad\lor\quad
b=c[\bar n]
\tag{21}
\]

に分かれる。前者なら

\[
R(b,c[\bar n])
\]

であるから、(20) と (2) により \(\operatorname{Acc}_R(b)\) を得る。後者なら
(20) の等号による置換だけで同じ結論を得る。従って全ての \(R\)-前者 \(b\) が
可到達であり、(2) から \(\operatorname{Acc}_R(c)\) が従う。

#### 分岐3：\(\operatorname{dom}(c)=T_m\)

ある \(m<u\) が存在して

\[
\operatorname{dom}(c)=T_m,
\qquad
\forall z\in W_m\quad c[z]\in Y
\tag{22}
\]

を得ている。(7) により再び \(c\neq0\) である。

任意の \(R(b,c)\) を取る。[OTB-BC-W-T](#otb-bc-w-t) により、
ある \(z\) が存在して

\[
z\in W_m,\qquad
z\in\operatorname{dom}(c),\qquad
z\in OT_B,\qquad
b\le c[z]
\tag{23}
\]

を得る。(22) と \(z\in W_m\) から

\[
\operatorname{Acc}_R(c[z])
\tag{24}
\]

である。また
[BUC86-3-3-GENERAL](../Buchholz-1986/Buchholz-1986-3.3.md#buc86-3-3-general) と
(23) により \(c[z]\in OT_B\) である。最後に
\(b\le c[z]\) を

\[
b<c[z]
\quad\lor\quad
b=c[z]
\tag{25}
\]

と分ける。前者では \(R(b,c[z])\) と (24) に (2) を適用し、後者では等号で
置換する。いずれも \(\operatorname{Acc}_R(b)\) を得るので、
\(\operatorname{Acc}_R(c)\) である。

以上で (8) の全生成分岐について \(c\in Y\) を示した。従って (16) が成り立ち、
最小不動点帰納法 (9) により (15) を得る。

### 2. 全ての項が可到達であること

任意の項 \(t\in T\) を取る。

まず \(\operatorname{DF}(t)\) と仮定する。\(t\) の最上位 principal 項に現れる
添字は有限個の自然数なので、それらの上界 \(m\) を取れる。従って \(t\in T_m\) であり、
[OTB-DFREE-IN-W](#otb-dfree-in-w) から

\[
t\in W_m
\tag{26}
\]

を得る。(15) をこの \(m\) に適用すれば

\[
\operatorname{Acc}_R(t)
\tag{27}
\]

である。

次に \(\neg\operatorname{DF}(t)\) と仮定する。この場合、もし \(R(y,t)\) なら
(1) から \(t\in OT_B\) であり、さらに (0) から \(\operatorname{DF}(t)\) が従う。
これは仮定に反する。従って \(t\) は \(R\)-前者を持たず、(2) により
\(\operatorname{Acc}_R(t)\) である。

従って \(\operatorname{DF}(t)\) の真偽によらず、任意の \(t\in T\) について
\(\operatorname{Acc}_R(t)\) が成り立つ。これは (3) そのものである。

よって \(R\) は整礎である。□

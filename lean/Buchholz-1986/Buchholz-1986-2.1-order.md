[← Back](README.md)

# Buchholz (1986) 補題2.1 — 辞書式順序は線型順序である

出典：W. Buchholz, *A new system of proof-theoretic ordinal functions*,
Annals of Pure and Applied Logic 32 (1986), Lemma 2.1.

<a id="buc86-2-1"></a>
## 辞書式順序の線型性 [BUC86-2-1]

Buchholz 項上の関係 \(<\) は狭義線型順序である。すなわち任意の
項 \(a,b,c\) について

\[
\neg(a<a),
\tag{1}
\]

\[
a<b\land b<c\Longrightarrow a<c,
\tag{2}
\]

\[
a<b\ \lor\ a=b\ \lor\ b<a
\tag{3}
\]

が成り立つ。証明では項、主項、主項列の三種類を同時に扱う。

## 順序の再帰式

辞書式順序の定義
[BUC86-2-1-ORDER-DEF](Buchholz-1986-2.1.md#buc86-2-1-order-def) を使う。
項 \(a=(p_0,\ldots,p_{k-1})\) の比較は、その主項列の比較である。
主項では

\[
D_ua<D_vb
\quad\Longleftrightarrow\quad
u<v\ \lor\ (u=v\land a<b),
\tag{4}
\]

主項列では

\[
\begin{aligned}
\neg([]<[]),\qquad&
[]<(q::qs),\qquad
\neg((p::ps)<[]),\\
(p::ps)<(q::qs)
\quad\Longleftrightarrow\quad&
p<q\ \lor\ (p=q\land ps<qs)
\end{aligned}
\tag{5}
\]

である。

<a id="buc86-2-1-irrefl"></a>
## 非反射性 [BUC86-2-1-IRREFL]

次の三命題を相互帰納法で同時に示す。

\[
\begin{aligned}
I_T(a)&:\ \neg(a<a),\\
I_P(p)&:\ \neg(p<p),\\
I_L(ps)&:\ \neg(ps<ps).
\end{aligned}
\tag{6}
\]

### 項の場合

\(a=(p_0,\ldots,p_{k-1})\) とする。項の比較は主項列の比較そのものなので、
\(a<a\) は

\[
[p_0,\ldots,p_{k-1}]<[p_0,\ldots,p_{k-1}]
\]

と同値である。これは主項列についての帰納法の仮定 \(I_L\) に反する。

### 主項の場合

\(p=D_ua\) とする。(4) により

\[
D_ua<D_ua
\quad\Longleftrightarrow\quad
u<u\ \lor\ (u=u\land a<a).
\tag{7}
\]

\(u<u\) は添字順序の非反射性に反する。第二項は本体についての帰納法の仮定
\(I_T(a)\) に反する。従って \(I_P(D_ua)\) が成り立つ。

### 主項列の場合

空列については (5) から \(\neg([]<[])\)。
非空列 \(p::ps\) では

\[
p::ps<p::ps
\quad\Longleftrightarrow\quad
p<p\ \lor\ (p=p\land ps<ps).
\tag{8}
\]

第一項は \(I_P(p)\)、第二項は \(I_L(ps)\) に反する。これで三種類の
相互帰納が閉じ、特に項について (1) を得る。

<a id="buc86-2-1-trans"></a>
## 推移性 [BUC86-2-1-TRANS]

次の三命題を相互帰納法で同時に示す。

\[
\begin{aligned}
T_T(a,b,c)&:\ a<b\land b<c\Longrightarrow a<c,\\
T_P(p,q,r)&:\ p<q\land q<r\Longrightarrow p<r,\\
T_L(xs,ys,zs)&:\ xs<ys\land ys<zs\Longrightarrow xs<zs.
\end{aligned}
\tag{9}
\]

### 項の場合

\[
a=(a_0,\ldots,a_{k-1}),\quad
b=(b_0,\ldots,b_{\ell-1}),\quad
c=(c_0,\ldots,c_{m-1})
\]

とする。\(a<b\) と \(b<c\) は対応する主項列の二つの不等式である。
主項列についての帰納法の仮定 \(T_L\) を適用して、\(a<c\) を得る。

### 主項の場合

\[
D_ua<D_vb,\qquad D_vb<D_wc
\tag{10}
\]

とする。(4) により、第一の比較は

\[
u<v
\quad\text{または}\quad
u=v\land a<b,
\tag{11}
\]

第二の比較は

\[
v<w
\quad\text{または}\quad
v=w\land b<c
\tag{12}
\]

である。四つの組合せを調べる。

1. \(u<v\) かつ \(v<w\) なら、添字順序の推移性から \(u<w\)。
   よって (4) の第一分岐から \(D_ua<D_wc\)。
2. \(u<v\) かつ \(v=w\land b<c\) なら \(u<w\) なので同じ結論を得る。
3. \(u=v\land a<b\) かつ \(v<w\) なら \(u<w\) なので同じ結論を得る。
4. \(u=v\land a<b\) かつ \(v=w\land b<c\) なら \(u=w\)。
   本体についての帰納法の仮定 \(T_T(a,b,c)\) から \(a<c\) を得る。
   従って (4) の第二分岐から \(D_ua<D_wc\)。

これで主項の推移性が示された。

### 主項列の空・非空の場合

\[
xs<ys,\qquad ys<zs
\tag{13}
\]

とする。

- \(xs=[]\)、\(ys=[]\) なら、第一の不等式が
  \([]<[]\) となり (5) に反する。
- \(xs=[]\)、\(ys\neq[]\) なら、第二の不等式から \(zs\neq[]\)。
  従って (5) より \([]<zs\)。
- \(xs\neq[]\)、\(ys=[]\) なら、第一の不等式が (5) に反する。
- \(ys\neq[]\)、\(zs=[]\) なら、第二の不等式が (5) に反する。

従って残る非自明な場合では三列とも非空であり、

\[
xs=x::xs',\qquad ys=y::ys',\qquad zs=z::zs'
\]

と書ける。(5) により

\[
x<y\ \lor\ (x=y\land xs'<ys')
\tag{14}
\]

および

\[
y<z\ \lor\ (y=z\land ys'<zs')
\tag{15}
\]

を得る。再び四つの組合せを調べる。

1. \(x<y\) かつ \(y<z\) なら、主項についての帰納法の仮定 \(T_P\) から
   \(x<z\)。従って \(xs<zs\)。
2. \(x<y\) かつ \(y=z\) なら \(x<z\) なので \(xs<zs\)。
3. \(x=y\) かつ \(y<z\) なら \(x<z\) なので \(xs<zs\)。
4. \(x=y\)、\(y=z\)、\(xs'<ys'\)、\(ys'<zs'\) なら、
   尾部についての帰納法の仮定 \(T_L\) から \(xs'<zs'\)。
   先頭が \(x=z\) なので (5) の第二分岐から \(xs<zs\)。

これで \(T_L\) が示され、相互帰納から項について (2) を得る。

<a id="buc86-2-1-trichotomy"></a>
## 三分律 [BUC86-2-1-TRICHOTOMY]

次の三命題を相互帰納法で同時に示す。

\[
\begin{aligned}
C_T(a,b)&:\ a<b\ \lor\ a=b\ \lor\ b<a,\\
C_P(p,q)&:\ p<q\ \lor\ p=q\ \lor\ q<p,\\
C_L(xs,ys)&:\ xs<ys\ \lor\ xs=ys\ \lor\ ys<xs.
\end{aligned}
\tag{16}
\]

### 項の場合

\(a,b\) の主項列をそれぞれ \(as,bs\) とする。主項列についての帰納法の仮定
\(C_L(as,bs)\) を適用する。\(as<bs\) なら \(a<b\)、\(as=bs\) なら
項の構文から \(a=b\)、\(bs<as\) なら \(b<a\) である。

### 主項の場合

\(p=D_ua\)、\(q=D_vb\) とする。添字の三分律により

\[
u<v,\qquad u=v,\qquad v<u
\tag{17}
\]

のいずれかである。

- \(u<v\) なら (4) から \(p<q\)。
- \(v<u\) なら (4) から \(q<p\)。
- \(u=v\) なら、本体についての帰納法の仮定
  \[
  a<b\ \lor\ a=b\ \lor\ b<a
  \]
  を使う。第一の場合は \(p<q\)、第二の場合は構文的に \(p=q\)、
  第三の場合は \(q<p\) である。

従って \(C_P(p,q)\) が成り立つ。

### 主項列の場合

空・非空を分ける。

- \(xs=[]\)、\(ys=[]\) なら \(xs=ys\)。
- \(xs=[]\)、\(ys\neq[]\) なら (5) より \(xs<ys\)。
- \(xs\neq[]\)、\(ys=[]\) なら (5) より \(ys<xs\)。
- 両方が非空なら \(xs=x::xs'\)、\(ys=y::ys'\) と書く。

最後の場合、主項についての帰納法の仮定 \(C_P(x,y)\) を適用する。
\(x<y\) なら (5) より \(xs<ys\)、\(y<x\) なら \(ys<xs\)。
\(x=y\) なら尾部についての帰納法の仮定

\[
xs'<ys'\ \lor\ xs'=ys'\ \lor\ ys'<xs'
\]

を用いる。第一と第三の場合は (5) の第二分岐によって列の狭義比較へ戻り、
第二の場合は先頭と尾部がともに等しいので \(xs=ys\) である。
これで \(C_L\) が示され、相互帰納から項について (3) を得る。

## 結論

[BUC86-2-1-IRREFL](#buc86-2-1-irrefl)、
[BUC86-2-1-TRANS](#buc86-2-1-trans)、
[BUC86-2-1-TRICHOTOMY](#buc86-2-1-trichotomy) により、項上の \(<\) は
非反射的、推移的、かつ任意の二項が比較可能である。従って \(<\) は
狭義線型順序であり、広義関係

\[
a\leq b\quad\Longleftrightarrow\quad a<b\ \lor\ a=b
\]

は対応する線型順序である。これが
[BUC86-2-1](#buc86-2-1) の主張である。□

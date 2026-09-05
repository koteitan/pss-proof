[← back](README.md)

# 04: 命題 (基本列の辞書式的縮小性)

## 原文

### 命題

命題 (基本列の辞書式的縮小性)

任意の $M\in T_{\textrm{PS}}$ と $n\in\mathbb{N}_+$ に対して、$\textrm{Lng}(M)>1$ ならば $M[n]<_{\textrm{PS}}M$ である。

### 証明

　証明

　$\textrm{operator}[]$ の定義中の記号を $M$ に対して定義する。

　条件より $j_1>0$ である。

　$M[n]=\textrm{Pred}(M)$ ならば明らかに $M[n]<_{\textrm{PS}}M$ である。

　よって $M_{j_1}\neq(0,0)$ かつある非負整数 $j_0$ が存在して $(i_1,j_0)<^{\textrm{Next}}_M(i_1,j_1)$ であるとする。

　　[1] の $\textrm{Pred}$ が $[1]$ で表されることより $n=1$ ならば $M[n]=\textrm{Pred}(M)$ であり、$M[n]=\textrm{Pred}(M)$ の場合は考えなくていいから $n>1$ とする。

```math
\begin{aligned}M[n]&=G\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}B\right)\cr&=G\oplus_{\mathbb{N}^2}B_0\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}\right)\cr&=(M_j)_{j=0}^{j_0-1}\oplus_{\mathbb{N}^2}(M_j)_{j=j_0}^{j_1-1}\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}\right)\cr&=(M_j)_{j=0}^{j_1-1}\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}\right)\end{aligned}
```

　　である。

　　よって $M[n]<_{\textrm{PS}}M$ は $\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}<_{\textrm{PS}}(M_{j_1})$ と同値である。

　　$\left(\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}\right)_0=(B_1)_0=(M_{0,j_0}+\delta_0,M_{1,j_0}+\delta_1)$ である。

　　$i_1=0$ とする。

　　　$(M_{0,j_0}+\delta_0,M_{1,j_0}+\delta_1)=(M_{0,j_0},M_{1,j_0})$ である。

　　　$<^{\textrm{Next}}$ の定義より、$M_{0,j_0}< M_{0,j_1}$ である。

　　　よって $\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}<_{\textrm{PS}}(M_{j_1})$ である。

　　$i_1=1$ とする。

　　　$(M_{0,j_0}+\delta_0,M_{1,j_0}+\delta_1)=(M_{0,j_1},M_{1,j_0})$ である。

　　　$<^{\textrm{Next}}$ の定義より、$M_{1,j_0}< M_{1,j_1}$ である。

　　　よって $\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}<_{\textrm{PS}}(M_{j_1})$ である。

　　よっていずれの場合でも $\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}<_{\textrm{PS}}(M_{j_1})$ である。

　　従って $M[n]<_{\textrm{PS}}M$ である。

　よっていずれの場合でも $M[n]<_{\textrm{PS}}M$ である。□

## Lean

### Lean での命題

任意のペア数列 $M$ と $n\geq1$ に対して、$\textrm{Lng}(M)>1$ ならば $M[n]<_{\textrm{PS}}M$ である。

原文の $M\in T_{\textrm{PS}}$ は仮定に置いていない。$M$ の型がペア数列（対の有限列）そのもので、
$\textrm{Lng}(M)>1$ から $M\neq()$、すなわち $M\in T_{\textrm{PS}}$ が従うからである。

これに加えて、下流（辞書式的順序が基本列的順序を含意すること）で使う弱形

任意のペア数列 $M$ と $n\geq1$ に対して $M[n]\leq_{\textrm{PS}}M$ である

も系として置いてある。$\textrm{Lng}(M)>1$ なら本命題から、$\textrm{Lng}(M)\leq1$ なら
$j_1=0$ で $M[n]=M$ だから等号で成り立つ。

### Lean での証明

**記号**（[1] の $\textrm{operator}[]$ の定義そのもの）。$j_1=\textrm{Lng}(M)-1$ とし、
$i_1$ を $M_{1,j_1}>0$ のとき $1$、そうでないとき $0$ とする。$j_0$ を段 $i_1$ における $j_1$ の親、

```math
\delta_0=\begin{cases}M_{0,j_1}-M_{0,j_0}&(0<i_1)\cr 0&(0\geq i_1)\end{cases}\qquad
\delta_1=\begin{cases}M_{1,j_1}-M_{1,j_0}&(1<i_1)\cr 0&(1\geq i_1)\end{cases}
```

```math
G=(M_j)_{j=0}^{j_0-1},\qquad B_k=\left((M_{0,j}+k\delta_0,\ M_{1,j}+k\delta_1)\right)_{j=j_0}^{j_1-1}
```

とすると、$M[n]$ は次の 4 分岐で定義される。

- $j_1=0$ のとき $M[n]=M$
- $M_{j_1}=(0,0)$ のとき $M[n]=\textrm{Pred}(M)$
- 段 $i_1$ に一意な親が無いとき $M[n]=\textrm{Pred}(M)$
- それ以外のとき $M[n]=G\oplus_{\mathbb{N}^2}\bigoplus_{k=0}^{n-1}B_k$

**準備補題**。

(a) 真の接頭辞は $<_{\textrm{PS}}$ で小さい。すなわち $k<\textrm{Lng}(M)$ ならば
$(M_j)_{j=0}^{k-1}<_{\textrm{PS}}M$。証明は $M$ の長さに関する再帰である。$M$ が空列なら
$k<0$ で矛盾。$M=p\oplus_{\mathbb{N}^2}M'$ で $k=0$ なら左辺は空列で、$<_{\textrm{PS}}$ の
空列規約（空列は非空列より小さい）から従う。$k=k'+1$ なら両辺の先頭が同じ $p$ なので
$<_{\textrm{PS}}$ の定義の第 3 の場合に落ち、$(M'_j)_{j=0}^{k'-1}<_{\textrm{PS}}M'$ を再帰で得る。

(b) 共通接頭辞は消去できる。すなわち任意の $A,B,C$ に対して
$(A\oplus_{\mathbb{N}^2}B)<_{\textrm{PS}}(A\oplus_{\mathbb{N}^2}C)$ は
$B<_{\textrm{PS}}C$ と同値。証明は $A$ の長さに関する再帰である。$A$ が空列なら両辺は同一。
$A=p\oplus_{\mathbb{N}^2}A'$ なら先頭が一致するので $<_{\textrm{PS}}$ の第 1・第 2 の場合が消え、
第 3 の場合だけが残って再帰する。

(c) $(0,j_0)<^{\textrm{Next}}_M(0,j_1)$ ならば $M_{0,j_0}<M_{0,j_1}$。上段の
$<^{\textrm{Next}}$ の定義の連言成分そのものを取り出す。

(d) $(1,j_0)<^{\textrm{Next}}_M(1,j_1)$ ならば $M_{1,j_0}<M_{1,j_1}$ であり、かつ
$(0,j_0)\leq_M(0,j_1)$ である。どちらも下段の $<^{\textrm{Next}}$ の定義の連言成分である。

(e) $(0,j_0)\leq_M(0,j_1)$ ならば $M_{0,j_0}\leq M_{0,j_1}$。$\leq_M$（上段）は上段の
$<^{\textrm{Next}}$ の反射推移閉包で、この形式化では鎖の長さの上界 $\textrm{Lng}(M)$ を
燃料とする再帰で定義されている。その燃料に関する帰納法で示す。燃料 $0$ のときは
$j_0=j_1$ なので等号。燃料 $f+1$ のときは $j_0=j_1$ であるか、ある $j<j_1$ が存在して
$(0,j)<^{\textrm{Next}}_M(0,j_1)$ かつ $(0,j_0)\leq_M(0,j)$（燃料 $f$）であるかのいずれかで、
後者では帰納法の仮定 $M_{0,j_0}\leq M_{0,j}$ と (c) の $M_{0,j}<M_{0,j_1}$ を推移律でつなぐ。

**本体**

(0) $\textrm{Lng}(M)>1$ より $M\neq()$、および $j_1=\textrm{Lng}(M)-1\neq0$
（原文の「条件より $j_1>0$ である」）。以下、$M_{j_1}=(0,0)$ か否か、段 $i_1$ に一意な親が
あるか否かで場合を分ける。これは $M[n]$ の定義の分岐そのものである。

(1) $M_{j_1}=(0,0)$ のとき。定義の第 2 分岐から $M[n]=\textrm{Pred}(M)$。
$\textrm{Lng}(M)>1$ のとき $\textrm{Pred}(M)=(M_j)_{j=0}^{j_1-1}$ であり、
$j_1<\textrm{Lng}(M)$ だから (a) より $M[n]<_{\textrm{PS}}M$。
（原文の「$M[n]=\textrm{Pred}(M)$ ならば明らかに $M[n]<_{\textrm{PS}}M$ である」に当たる。）

(2) $M_{j_1}\neq(0,0)$ かつ段 $i_1$ に一意な親が無いとき。定義の第 3 分岐から
$M[n]=\textrm{Pred}(M)$ なので (1) と同じ。これも原文の
「$M[n]=\textrm{Pred}(M)$ ならば」に含まれる場合である。

(3) $M_{j_1}\neq(0,0)$ かつ段 $i_1$ に一意な親 $j_0$ があるとき。以下は原文の
「よって $M_{j_1}\neq(0,0)$ かつある非負整数 $j_0$ が存在して … とする」以降と同じ筋をたどる。

(3-1) $n=1$ のとき。[1] の「$\textrm{Pred}$ が $[1]$ で表されること」（$M\in T_{\textrm{PS}}$、
$\textrm{Lng}(M)>1$ のとき $\textrm{Pred}(M)=M[1]$）より $M[1]=\textrm{Pred}(M)$ なので (1) と同じ。
原文が「$n=1$ ならば $M[n]=\textrm{Pred}(M)$ であり … $n>1$ とする」と述べる一歩に当たる。

(3-2) $n\geq2$ のとき。$n=m+2$ と書く。

・親の性質から $j_0<j_1$。

・定義の第 4 分岐を展開して $M[n]=G\oplus_{\mathbb{N}^2}\bigoplus_{k=0}^{m+1}B_k$。

・$k$ の走る範囲 $0,1,\dots,m+1$ を $k=0$、$k=1$、$2\leq k\leq m+1$ の 3 つに分割し、
$\bigoplus_{k=0}^{m+1}B_k=B_0\oplus_{\mathbb{N}^2}\left(B_1\oplus_{\mathbb{N}^2}\bigoplus_{k=2}^{m+1}B_k\right)$
とする。

・$k=0$ の項は $0\cdot\delta_0=0\cdot\delta_1=0$ より $B_0=(M_j)_{j=j_0}^{j_1-1}$。

・接頭辞の分割 $(M_j)_{j=0}^{j_1-1}=(M_j)_{j=0}^{j_0-1}\oplus_{\mathbb{N}^2}(M_j)_{j=j_0}^{j_1-1}$
（$j_0\leq j_1\leq\textrm{Lng}(M)$ のもとで、両辺の長さと各成分を突き合わせて示す）を使って
$G\oplus_{\mathbb{N}^2}B_0=(M_j)_{j=0}^{j_1-1}$。以上を合わせて

```math
M[n]=(M_j)_{j=0}^{j_1-1}\oplus_{\mathbb{N}^2}\left(B_1\oplus_{\mathbb{N}^2}\bigoplus_{k=2}^{m+1}B_k\right)
```

を得る。これは原文の 4 段の等式と同じ変形である。

・$M$ の側も $M=(M_j)_{j=0}^{j_1-1}\oplus_{\mathbb{N}^2}(M_{j_1})$ と分ける。$M$ を先頭 $j_1$ 項と
残りに切り、残りの長さが $\textrm{Lng}(M)-j_1=1$ であること、その第 $0$ 項が
$(M_{0,j_1},M_{1,j_1})$ であることを成分ごとに確認する。

・(b) を共通接頭辞 $(M_j)_{j=0}^{j_1-1}$ に適用して、$M[n]<_{\textrm{PS}}M$ は

```math
B_1\oplus_{\mathbb{N}^2}\bigoplus_{k=2}^{m+1}B_k<_{\textrm{PS}}(M_{j_1})
```

と同値である。原文の「よって $M[n]<_{\textrm{PS}}M$ は
$\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}<_{\textrm{PS}}(M_{j_1})$ と同値である」に当たる。

・$j_0<j_1$ より $B_1$ は空列でなく、その先頭は $(M_{0,j_0}+\delta_0,M_{1,j_0}+\delta_1)$ である。
右辺は長さ $1$ の列 $(M_{j_1})$ なので、$<_{\textrm{PS}}$ の定義の第 1 の場合
（第 0 成分が狭義に小さい）か第 2 の場合（第 0 成分が等しく第 1 成分が狭義に小さい）の
どちらかを示せばよい。

・一意な親であることから $(i_1,j_0)<^{\textrm{Next}}_M(i_1,j_1)$。

・$i_1=0$ のとき。$0<i_1$ も $1<i_1$ も偽だから $\delta_0=\delta_1=0$ で、先頭は
$(M_{0,j_0},M_{1,j_0})$ である。(c) より $M_{0,j_0}<M_{0,j_1}$ なので、$<_{\textrm{PS}}$ の
第 1 の場合で結論を得る。

・$i_1\neq0$ のとき。$i_1$ の定義（$M_{1,j_1}>0$ なら $1$、そうでなければ $0$）から $i_1=1$。
よって $\delta_0=M_{0,j_1}-M_{0,j_0}$、$\delta_1=0$ である。まず (d) から
$(0,j_0)\leq_M(0,j_1)$ を取り、(e) を適用して $M_{0,j_0}\leq M_{0,j_1}$ を得る。これにより
自然数の切り捨て差でも $M_{0,j_0}+\delta_0=M_{0,j_0}+(M_{0,j_1}-M_{0,j_0})=M_{0,j_1}$ となり、
第 0 成分は等しい。第 1 成分は (d) の $M_{1,j_0}<M_{1,j_1}$ と $\delta_1=0$ から
$M_{1,j_0}+\delta_1<M_{1,j_1}$。よって $<_{\textrm{PS}}$ の第 2 の場合で結論を得る。

以上いずれの場合でも $M[n]<_{\textrm{PS}}M$ である。

**系の証明**。$\textrm{Lng}(M)>1$ なら本命題から $M[n]<_{\textrm{PS}}M$。
$\textrm{Lng}(M)\leq1$ なら $j_1=\textrm{Lng}(M)-1=0$ で定義の第 1 分岐から $M[n]=M$ なので
$M[n]\leq_{\textrm{PS}}M$ の左（等号）で成り立つ。

## 原文通りに書けなかった理由

- **[W]** 「$M[n]=\textrm{Pred}(M)$ ならば明らかに」は、真の接頭辞が $<_{\textrm{PS}}$ で
  小さいというリスト補題を隠している

  原文はこの分岐を一行で片付けるが、$\textrm{Pred}(M)<_{\textrm{PS}}M$ は
  $<_{\textrm{PS}}$ の定義から直ちには出ない。$\textrm{Lng}(M)>1$ のとき
  $\textrm{Pred}(M)=(M_j)_{j=0}^{j_1-1}$ であることを使ったうえで、準備補題 (a)
  「$k<\textrm{Lng}(M)$ ならば $(M_j)_{j=0}^{k-1}<_{\textrm{PS}}M$」を列の長さに関する
  再帰で証明している。再帰の底は空列と非空列の比較（$<_{\textrm{PS}}$ の再帰的定義が
  最後に到達する空列の規約）で、再帰段は先頭が一致するので定義の第 3 の場合に落ちる。

- **[S]** 原文の場合分け「ある $j_0$ が存在して $(i_1,j_0)<^{\textrm{Next}}_M(i_1,j_1)$」を、
  Lean は「段 $i_1$ に親が**一意に**存在する」で行っている

  $M[n]$ の定義は [1] の形式化をそのまま使っており、そこでは第 3 分岐の条件が
  「段 $i_1$ における $j_1$ の親の候補がちょうど 1 個であること」と書かれている
  （この形式化には、それが $j_1$ の親の一意存在と同値であることの補題も入っている）。
  したがって Lean の場合分けは「一意な親がある／無い」となり、原文の
  「存在する／しない」とは字面が違う。もっとも親は存在すれば一意である。
  $j_0<j_0'$ がともに段 $i$ における $j_1$ の親だとすると、$j_0$ の側の条件
  （$j_0<j<j_1$ なる $j$ すべてについて $M_{i,j_1}\leq M_{i,j}$。下段では
  さらに $(0,j)\leq_M(0,j_1)$ を満たす $j$ に限る）を $j=j_0'$ に適用して
  $M_{i,j_1}\leq M_{i,j_0'}$ を得るが、$j_0'$ の側の条件は $M_{i,j_0'}<M_{i,j_1}$ で
  矛盾するからである。よって 2 つの場合分けは一致し、どちらでも
  $M[n]=\textrm{Pred}(M)$ になるか第 4 分岐になるかは変わらないので、
  命題の言明にも下流にも影響しない。

- **[W]** 「同値である」は、共通接頭辞の消去と $M$ 側の分解を隠している

  原文は $M[n]=(M_j)_{j=0}^{j_1-1}\oplus_{\mathbb{N}^2}\bigoplus(B_i)_{i=1}^{n-1}$ を得た直後に
  「よって $M[n]<_{\textrm{PS}}M$ は $\bigoplus(B_i)_{i=1}^{n-1}<_{\textrm{PS}}(M_{j_1})$ と
  同値である」と書くが、この一行には (i) $M$ 自身を
  $M=(M_j)_{j=0}^{j_1-1}\oplus_{\mathbb{N}^2}(M_{j_1})$ と分解すること、(ii) 共通接頭辞
  $(M_j)_{j=0}^{j_1-1}$ を $<_{\textrm{PS}}$ の比較から落とせること、の 2 つが要る。
  Lean では (i) を $M$ の先頭 $j_1$ 項と残りへの分割（残りが長さ $1$ でその値が $M_{j_1}$）
  として成分ごとに示し、(ii) を準備補題 (b) として $A$ の長さに関する再帰で示している。
  どちらも形式化の範疇の作業だが、原文には対応する一歩が無い。

- **[W]** $i_1=1$ の場合の等式 $(M_{0,j_0}+\delta_0,M_{1,j_0}+\delta_1)=(M_{0,j_1},M_{1,j_0})$ には
  $M_{0,j_0}\leq M_{0,j_1}$ が要る

  $\delta_0=M_{0,j_1}-M_{0,j_0}$ は非負整数上の差なので、$M_{0,j_0}+\delta_0=M_{0,j_1}$ が
  成り立つのは $M_{0,j_0}\leq M_{0,j_1}$ のときに限る（切り捨て差では一般に
  $M_{0,j_0}+(M_{0,j_1}-M_{0,j_0})=\max(M_{0,j_0},M_{0,j_1})$）。原文はこの不等式に触れず
  等式を書いている。Lean では下段の $<^{\textrm{Next}}$ の定義に含まれる
  $(0,j_0)\leq_M(0,j_1)$（準備補題 (d)）を取り出し、さらに上段の直系先祖関係に沿って
  第 0 成分が広義単調であること（準備補題 (e)）を、$\leq_M$ を定義する再帰の燃料に関する
  帰納法で証明して $M_{0,j_0}\leq M_{0,j_1}$ を得ている。この (c)(d)(e) の 3 補題が
  原文に対応物を持たない追加分である。

- **[S]** Lean は長さの条件を外した弱形 $M[n]\leq_{\textrm{PS}}M$ を系として追加している

  原文の命題は $\textrm{Lng}(M)>1$ を仮定する。下流の「辞書式的順序が基本列的順序を
  含意すること」では、展開列の各段で $\textrm{Lng}$ が $1$ より大きいことをいちいち
  持ち回らずに済ませたいので、$\textrm{Lng}(M)\leq1$ のとき $M[n]=M$（定義の第 1 分岐）で
  等号が成り立つことを足した弱形を置いてある。原文の命題自体は変えておらず、
  弱形は本命題から導かれるだけなので、原文の主張にも下流の内容にも差は無い。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $M<_{\textrm{PS}}N$ | `ltPS` | `lean/Bijectivity/Defs.lean` |
| $M\leq_{\textrm{PS}}N$ | `lePS` | 同上 |
| $T_{\textrm{PS}}$、$\textrm{Lng}(M)$、$M_{i,j}$ | `PSS.TPS`、`PSS.Lng`、`PSS.entry` | `lean/PSS/Defs.lean` |
| $\textrm{Pred}(M)$ | `PSS.Pred` | 同上 |
| $M[n]$（$G$、$B_k$、$\delta_0$、$\delta_1$ を含む定義） | `PSS.oper` | 同上 |
| $i_1$ | `PSS.idx1` | 同上 |
| 段 $i$ に一意な親があること、その親 $j_0$ | `PSS.hasParent`、`PSS.parent` | 同上 |
| $(i,j_0)<^{\textrm{Next}}_M(i,j_1)$ | `PSS.nextR`（`PSS.nextrel0`／`PSS.nextrel1`） | 同上 |
| $(0,j_0)\leq_M(0,j_1)$ | `PSS.le0`（燃料付き本体は `PSS.le0Aux`） | 同上 |
| (a) 真の接頭辞は小さい | `ltPS_take` | `lean/Bijectivity/02b-lex-list-lemmas.lean` |
| (b) 共通接頭辞の消去 | `ltPS_append_cancel` | 同上 |
| 接頭辞の分割 $(M_j)_{j=0}^{j_1-1}=(M_j)_{j=0}^{j_0-1}\oplus(M_j)_{j=j_0}^{j_1-1}$ | `take_split` | `lean/Bijectivity/07-oper-pred.lean` |
| $\textrm{Pred}(M)=(M_j)_{j=0}^{j_1-1}$ | `PSS.Pred_eq_take` | `lean/6/6.5-Red-Pred-commute.lean` |
| $\textrm{Pred}(M)=M[1]$（[1] の命題） | `PSS.pred_is_oper1` | `lean/5/5.3-pred-is-oper1.lean` |
| 親は $j_0<j_1$ を満たす | `PSS.parent_lt_of_hasParent` | `lean/6/6.6-condAB-coeff.lean` |
| 親は $(i_1,j_0)<^{\textrm{Next}}_M(i_1,j_1)$ を満たす | `PSS.hasParent_next_fseq` | `lean/6/6.2-P-fseq.lean` |
| (c) 上段の $<^{\textrm{Next}}$ は第 0 成分を狭義に増やす | `nextrel0_entry0_lt` | `lean/Bijectivity/04-fseq-lex-decreasing.lean` |
| (d) 下段の $<^{\textrm{Next}}$ は第 1 成分を狭義に増やす／$\leq_M$ を含む | `nextrel1_entry1_lt`／`nextrel1_le0` | 同上 |
| (e) $\leq_M$ に沿って第 0 成分は広義単調 | `le0Aux_entry0_le`／`le0_entry0_le` | 同上 |
| 退化枝（$M[n]=\textrm{Pred}(M)$）の補題 | `oper_ltPS_of_pred` | 同上 |
| 基本列の辞書式的縮小性 | `oper_ltPS` | 同上 |
| 弱形の系 $M[n]\leq_{\textrm{PS}}M$ | `oper_lePS` | 同上 |

[< back](README.md)

# 17: 命題 (基本列の収束性)

## 原文

### 命題

命題 (基本列の収束性)

任意の $M\in ST_{\textrm{PS}}$ に対して、$\textrm{dom}(\textrm{Trans}(M))=\omega$ ならば $\sup_{n\in\mathbb{N}_+}o(\textrm{Trans}(M[n]))=o(\textrm{Trans}(M))$ である。

### 証明

基本列の関係、[1] の基本列の降下性、[5] の Theorem 1.4(a) 及び Lemma 1.6 より $\{o(\textrm{Trans}(M[n]))\mid n\in\mathbb{N}_+\}$ は $o(\textrm{Trans}(M))$ の非有界な部分集合であることから即座に従う。□

## Lean

### Lean での命題

$$M\in ST_{\textrm{PS}}\ \land\ \textrm{dom}(\textrm{Trans}(M))=\omega
\ \Longrightarrow\ \sup_{n\in\mathbb{N}_+}o(\textrm{Trans}(M[n]))=o(\textrm{Trans}(M))$$

右辺左辺とも順序数であり、$\sup$ は $\{n\in\mathbb{N}\mid 1\leq n\}$ を添字集合とする
順序数族の上限である（添字型は空でないので上限は $0$ に潰れない）。

命題に現れる 2 つの記号について、この形式化での作り方を述べる。原文は「表記」節で
$o$ と $\textrm{dom}$ をどちらも [4] から引くと宣言しているが、こちらは引用ではなく
定義している。

**$o$。** $OT_{\textrm{B}}=OT\cap T_{\textrm{B}}$（構造的な順序数項であって字母 $D_\omega$ を
含まないもの）の上で

* $\{(a,b)\mid a,b\in OT_{\textrm{B}}\land a<_{\textrm{B}}b\}$ は整礎（[Buc1] 2.2 にあたる
  事実を、リポジトリ本体が仮定ゼロで証明している）
* $<_{\textrm{B}}$ は $OT_{\textrm{B}}$ 上で三分律と推移律を満たす

が成り立つので、$(OT_{\textrm{B}},<_{\textrm{B}})$ は整列順序である。そこで $o$ を
その順序型への順序同型、すなわち $t\in OT_{\textrm{B}}$ に
$\{u\in OT_{\textrm{B}}\mid u<_{\textrm{B}}t\}$ の順序型を対応させる写像として定める。
$OT_{\textrm{B}}$ の外では $o$ の値を $0$ と置く（例外は $D_0D_\omega0$ の一点で、
そこだけ $\{t\in OT_{\textrm{B}}\mid t<_{\textrm{B}}D_0D_\omega0\}$ の順序型を値とする。
本命題には $OT_{\textrm{B}}$ の元しか現れないので、この例外は効かない）。

**$\textrm{dom}$。** [Buc1] の $\textrm{dom}(t)$ は $\emptyset$、$\{0\}$、$\omega$、
$T_u$ の 4 通りしか取らないので、この形式化では 4 値のタグを項に割り当て、
$\textrm{dom}(t)$ をそのタグが表す集合として定義する。$\omega$ に当たるタグの表す集合は
Buchholz の数項 $\{\underbrace{D_00+\cdots+D_00}_{m}\mid m\in\mathbb{N}\}$ 全体であり、
$\textrm{dom}(t)=\omega$ は「$t$ のタグが $\omega$ のタグである」ことで表す。
$t[m]$ は $t$ の基本列の第 $m$ 項（[Buc1] の $t[z]$ に数項 $m$ を入れたもの）である。

### Lean での証明

原文が引く 3 つの道具のうち、基本列の関係（項目 16）と [1] の基本列の降下性は
既証の定理としてそのまま使う。[5] の Theorem 1.4(a)／Lemma 1.6 は引用せず、
それに当たる主張を $o$ の構成から証明する。以下 0 節が $o$ の性質、1 節が
[5] の代わりに証明した主張、2 節が本命題である。

#### 0. $o$ の構成から出る性質

$o$ を順序型への同型として定めたので、次の 4 つが定理になる。

**(o1) 単調性（[Buc1] Lemma 2.1 にあたる）.** $s,t\in OT_{\textrm{B}}$ かつ
$s<_{\textrm{B}}t$ ならば $o(s)<o(t)$。順序型への同型が順序を保つことそのもの。

**(o2) 初期切片への全射性（[Buc1] Lemma 2.2(c) にあたる）.** $t_0\in OT_{\textrm{B}}$、
$\alpha<o(t_0)$ ならば、ある $t\in OT_{\textrm{B}}$ が存在して $t<_{\textrm{B}}t_0$ かつ
$o(t)=\alpha$。$\alpha<o(t_0)<$（$(OT_{\textrm{B}},<_{\textrm{B}})$ の順序型）なので
$\alpha$ は順序型未満、よって $o(t)=\alpha$ なる $t\in OT_{\textrm{B}}$ が取れ、
$o(t)=\alpha<o(t_0)$ と (o1) の逆向き（同型なので同値）から $t<_{\textrm{B}}t_0$。

**(o3) 初期切片の上限表示.** $t\in OT_{\textrm{B}}$ ならば
$$o(t)=\sup\{\,o(u)+1\ \mid\ u\in OT_{\textrm{B}},\ u<_{\textrm{B}}t\,\}.$$
「$\leq$」: 右辺 $<o(t)$ と仮定すると、(o2) を $\alpha=$ 右辺 に使って
$w\in OT_{\textrm{B}}$、$w<_{\textrm{B}}t$、$o(w)=$ 右辺 が取れる。しかし上限の定義から
$o(w)+1\leq$ 右辺 $=o(w)$ で矛盾。
「$\geq$」: 各 $u\in OT_{\textrm{B}}$、$u<_{\textrm{B}}t$ に (o1) で $o(u)<o(t)$、
よって $o(u)+1\leq o(t)$。上限を取って右辺 $\leq o(t)$。

**(o4) $\leq_{\textrm{B}}$ 版（[Buc1] Lemma 2.2(c)）.** $a,b\in OT_{\textrm{B}}$ かつ
$a\leq_{\textrm{B}}b$ ならば $o(a)\leq o(b)$。$\leq_{\textrm{B}}$ は
$a<_{\textrm{B}}b$ または $a=b$ の定義なので、前者は (o1)、後者は等号。

#### 1. [5] Theorem 1.4(a) に当たる主張

$$t\in OT_{\textrm{B}},\ \textrm{dom}(t)=\omega\ \Longrightarrow\
\sup_{m\in\mathbb{N}}o(t[m])=o(t)$$

準備として $t\neq0$ を出す。$t=0$ なら $\textrm{dom}(0)=\emptyset$ でタグが
$\omega$ のタグにならないので、仮定に反する。
次に各 $m\in\mathbb{N}$ で $t[m]\in OT_{\textrm{B}}$ である（[Buc1] Lemma 3.3 の数項形。
適用に $t\in OT_{\textrm{B}}$ と $t\neq0$ が要る）。

「$\leq$」: 各 $m$ に [Buc1] Lemma 3.2(a) の数項形 $t[m]<_{\textrm{B}}t$
（適用に $t\in OT_{\textrm{B}}$ と $t\neq0$ が要る）と (o1) を使って
$o(t[m])<o(t)$、したがって $\sup_m o(t[m])\leq o(t)$。

「$\geq$」: (o3) で $o(t)$ を $\sup\{o(u)+1\mid u\in OT_{\textrm{B}},u<_{\textrm{B}}t\}$ に
書き換える。上限の各項を評価すればよいので、$u\in OT_{\textrm{B}}$、$u<_{\textrm{B}}t$ を
1 つ取り、$o(u)+1\leq\sup_n o(t[n])$ を示す。

1. 基本列の共終性（$\textrm{dom}(t)=\omega$ のとき $t$ 未満の $OT_{\textrm{B}}$ の元は
   どれかの $t[m]$ 以下）より、ある $m\in\mathbb{N}$ が存在して
   $u\leq_{\textrm{B}}t[m]$。
2. (o4) より $o(u)\leq o(t[m])$。
3. 基本列の添字単調性 $t[m]<_{\textrm{B}}t[m+1]$（$t\in OT_{\textrm{B}}$ と
   $\textrm{dom}(t)=\omega$ を要する）と (o1) より $o(t[m])<o(t[m+1])$。
4. $o(t[m+1])\leq\sup_n o(t[n])$。
5. 2, 3, 4 をつないで $o(u)<\sup_n o(t[n])$、順序数なので
   $o(u)+1\leq\sup_n o(t[n])$。

上限を取って $o(t)\leq\sup_n o(t[n])$。両向きから等号。

この節で $t[m]<_{\textrm{B}}t[m+1]$ を挟むのは、共終性が $\leq_{\textrm{B}}$ しか
与えないのに (o3) の右辺が後続 $o(u)+1$ の上限だからである。

#### 2. 本命題

$M\in ST_{\textrm{PS}}$ と $\textrm{dom}(\textrm{Trans}(M))=\omega$ を仮定する。

**側条件をそろえる。**

1. $M\in ST_{\textrm{PS}}$ から $M\in RT_{\textrm{PS}}$（標準形は簡約形）、
   さらに $M\in T_{\textrm{PS}}$（$M\neq()$）。
2. $\textrm{Lng}(M)>1$。$\textrm{Lng}(M)=1$ の簡約形 $M=((a,b))$ を仮定して矛盾を出す。
   $b=0$ のときは $\textrm{zeroT}(M)$ より $M=((0,0))$、$\textrm{Trans}(M)=0$ で
   $\textrm{dom}(0)=\emptyset\neq\omega$。$b\neq0$ のときは
   $\textrm{Trans}(M)=D_b0$ で、$b\neq0$ かつ $b\neq\omega$ だから
   $\textrm{dom}(D_b0)=\Omega_b\neq\omega$。いずれも仮定に反する。
3. $\textrm{Trans}(M)\in OT_{\textrm{B}}$。$\textrm{Trans}$ が標準形を $OT_{\textrm{B}}$ へ
   送ること（原文 §8.7 の補題にあたる、リポジトリ本体の定理）による。
4. 各 $n\geq1$ で $\textrm{Trans}(M[n])\in OT_{\textrm{B}}$。$ST_{\textrm{PS}}$ の生成規則
   「標準形の正の基本列は標準形」で $M[n]\in ST_{\textrm{PS}}$ とし、3 と同じ定理を使う。
5. $\textrm{Trans}(M)\neq0$。$\textrm{Trans}$ が零項性を保つこと
   （$\textrm{zeroT}(M)\Leftrightarrow\textrm{Trans}(M)=0$、$M\in T_{\textrm{PS}}$ を要する）と
   $\textrm{zeroT}(M)\Leftrightarrow(\textrm{Lng}(M)=1\land M_{1,0}=0)$ から、
   $\textrm{Trans}(M)=0$ は $\textrm{Lng}(M)=1$ を含意し、2 に反する。

**「$\leq$」向き（原文の「部分集合」）.** 各 $n\geq1$ に [1] の基本列の降下性
$$\textrm{Trans}(M[n])<_{\textrm{B}}\textrm{Trans}(M)$$
（適用に $M\in ST_{\textrm{PS}}$、$n\geq1$、$\textrm{Lng}(M)>1$ が要る）を使い、
4 と 3 の下で (o1) を当てて $o(\textrm{Trans}(M[n]))<o(\textrm{Trans}(M))$。
上限を取って $\sup_{n\in\mathbb{N}_+}o(\textrm{Trans}(M[n]))\leq o(\textrm{Trans}(M))$。

**「$\geq$」向き（原文の「非有界」）.** 1 節の主張を $t=\textrm{Trans}(M)$ に適用して
（3 と仮定 $\textrm{dom}(\textrm{Trans}(M))=\omega$ を使う）
$$o(\textrm{Trans}(M))=\sup_{m\in\mathbb{N}}o(\textrm{Trans}(M)[m])$$
と書き換える。あとは各 $m\in\mathbb{N}$ について
$o(\textrm{Trans}(M)[m])\leq\sup_{n\in\mathbb{N}_+}o(\textrm{Trans}(M[n]))$ を示せばよい。

1. 補題（基本列の関係、項目 16）を $M$ と $m$ に使う。仮定
   $M\in ST_{\textrm{PS}}$、$\textrm{dom}(\textrm{Trans}(M))=\omega$ の下で、ある
   $n\geq1$ が存在して $\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])$。
2. $\textrm{Trans}(M)[m]\in OT_{\textrm{B}}$（[Buc1] Lemma 3.3 の数項形、3 と 5 を使う）
   と $\textrm{Trans}(M[n])\in OT_{\textrm{B}}$（4）の下で (o4) を当て、
   $o(\textrm{Trans}(M)[m])\leq o(\textrm{Trans}(M[n]))$。
3. 右辺は添字 $n$ での上限以下なので
   $o(\textrm{Trans}(M)[m])\leq\sup_{n\in\mathbb{N}_+}o(\textrm{Trans}(M[n]))$。

上限を取って $o(\textrm{Trans}(M))\leq\sup_{n\in\mathbb{N}_+}o(\textrm{Trans}(M[n]))$。
両向きから等号を得る。□

## 原文通りに書けなかった理由

- **[U]** $o$ を [4] からの引用ではなく、$(OT_{\textrm{B}},<_{\textrm{B}})$ の順序型への
  順序同型として構成している

  原文は $o$ を [4] の記号としてそのまま使い、その性質（順序保存、初期切片への全射性）も
  [4] の Lemma 2.1／2.2(c) の引用で済ませる。この形式化では [4] の $\psi_u$ による
  $o$ の再帰的定義は書かず、$(OT_{\textrm{B}},<_{\textrm{B}})$ が整列順序であること
  （整礎性・三分律・推移律はいずれもリポジトリ内で証明済み）から $o$ を順序型への同型として
  定義した。そのため原文が引用する性質はすべて定理になり、この項目の外部引用はゼロである。
  2 つの $o$ が一致することは、[4] Lemma 2.2(c) を認めれば「順序数への順序同型で像が
  初期切片になるものは一意」から従うが、この形式化はその一致を述べていない。
  $OT_{\textrm{B}}$ の外では値が $0$（$D_0D_\omega0$ の一点だけ別値）なので [4] の $o$ とは
  異なるが、本命題に現れる項はすべて $OT_{\textrm{B}}$ の元なので効かない。
  したがって本命題は「構成した $o$ について」の主張であって、原文が [4] の $o$ について
  述べている主張そのものではない。下流（項目 21 以降）も同じ $o$ で一貫しているので、
  形式化の内部で齟齬は生じない。

- **[S]** [5] の Theorem 1.4(a) と Lemma 1.6 を引用せず、当たる主張を証明している

  原文は $\{o(\textrm{Trans}(M[n]))\}$ の非有界性を [5] の 2 つの結果から引く。
  この形式化では [5] を引かず、「$t\in OT_{\textrm{B}}$ かつ $\textrm{dom}(t)=\omega$ なら
  $\sup_m o(t[m])=o(t)$」を、リポジトリ内で仮定ゼロで証明済みの構文的な共終性
  （$\textrm{dom}(t)=\omega$ のとき $t$ 未満の $OT_{\textrm{B}}$ の元はどれかの $t[m]$ 以下）、
  [Buc1] Lemma 3.2(a)／3.3 の数項形、基本列の添字単調性、および $o$ の構成から出る
  (o1)-(o4) から証明した（上の 1 節）。主張の形は原文が引く Theorem 1.4(a) と同じで、
  この命題より下流でもこの形のまま使うので内容は変わらない。
  なお、共終性が与えるのは $u\leq_{\textrm{B}}t[m]$ という $\leq$ の形だけなので、
  $o(t)=\sup_{u<_{\textrm{B}}t}(o(u)+1)$ の右辺の後続を越えるために
  $t[m]<_{\textrm{B}}t[m+1]$ を 1 段挟む必要がある。原文は「非有界」の一語で通しており、
  この段には触れていない。

- **[W]** 原文が触れない側条件 $\textrm{Lng}(M)>1$ を仮定から導いている

  [1] の基本列の降下性 $\textrm{Trans}(M[n])<_{\textrm{B}}\textrm{Trans}(M)$ は
  $\textrm{Lng}(M)>1$ を要する。実際 $\textrm{Lng}(M)=1$ なら $M[n]=M$ で降下しない。
  原文は「[1] の基本列の降下性より」と書くだけでこの条件に触れないが、この形式化では
  $\textrm{dom}(\textrm{Trans}(M))=\omega$ から $\textrm{Lng}(M)>1$ を導く段
  （$\textrm{Lng}(M)=1$ の簡約形は $\textrm{Trans}$ で $0$ か $D_b0$ に写り、
  $\textrm{dom}$ がそれぞれ $\emptyset$、$\Omega_b$ になって $\omega$ にならない）を
  挟んでいる。$\textrm{Trans}(M)\neq0$ も同じ計算から出て、[Buc1] Lemma 3.2(a)／3.3 の
  適用条件に使う。

- **[W]** $o$ の単調性が $OT_{\textrm{B}}$ 上でしか成り立たないので、$OT_{\textrm{B}}$ 所属を
  毎回添えている

  $<_{\textrm{B}}$ は Buchholz 項全体では整礎でない（$D_10$、$D_0D_10$、$D_0D_0D_10$、… が
  狭義降下列になる）ので、(o1) や (o4) を項全体で述べると順序数の無限降下列ができて
  矛盾する。したがってこの形式化では $o$ の単調性に $OT_{\textrm{B}}$ 所属が必須で、
  $\textrm{Trans}(M)$、$\textrm{Trans}(M[n])$（$n\geq1$）、$\textrm{Trans}(M)[m]$ の 3 つに
  ついて所属を用意している。前 2 者は $\textrm{Trans}$ が標準形を $OT_{\textrm{B}}$ に送ること
  （原文 §8.7 の補題）と $ST_{\textrm{PS}}$ が基本列で閉じることから、
  3 つめは [Buc1] Lemma 3.3 の数項形から出る。原文は $o$ の適用範囲に触れないので、
  この確認はどこにも現れない。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $M[n]$（ペア数列の基本列） | `PSS.oper` | `lean/PSS/Defs.lean` |
| $\textrm{Lng}(M)$ | `PSS.Lng` | 同上 |
| $M_{i,j}$ | `PSS.entry` | 同上 |
| $T_{\textrm{PS}}$ | `PSS.TPS` | 同上 |
| $RT_{\textrm{PS}}$（簡約形） | `PSS.RTPS` | `lean/PSS/Red.lean` |
| $ST_{\textrm{PS}}$ | `PSS.STPS` | `lean/PSS/Standard.lean` |
| 標準形の正の基本列は標準形 | `PSS.STPS.oper` | 同上 |
| $\textrm{zeroT}(M)$ | `PSS.zeroT` | `lean/PSS/Mono.lean` |
| $\textrm{Trans}(M)$ | `PSS.Trans` | `lean/PSS/Trans.lean` |
| $a<_{\textrm{B}}b$ | `PSS.lessBT` | `lean/Buchholz-1986/Buchholz-1986-2.1.lean` |
| $a\leq_{\textrm{B}}b$ | `PSS.leBT` | 同上 |
| $<_{\textrm{B}}$ の三分律・推移律 | `PSS.lessBT_linear_trichotomy`, `PSS.lessBT_linear_trans` | `lean/Buchholz-1986/Buchholz-1986-2.1-order.lean` |
| $OT_{\textrm{B}}$ | `PSS.OT_B` | `lean/Buchholz-1986/Buchholz-1986-2.2.lean` |
| $OT_{\textrm{B}}$ 上の $<_{\textrm{B}}$ の整礎性 | `PSS.OT_B_wellFounded` | `lean/OTB-well-founded-syntactic/OTB-well-founded-syntactic-main.lean` |
| 数項 $\underbrace{D_00+\cdots+D_00}_{m}$ | `PSS.numBT` | `lean/Buchholz-1986/Buchholz-1986-3.2.lean` |
| $\textrm{dom}$ のタグ | `PSS.domTag` | 同上 |
| $\textrm{dom}(t)$ | `PSS.domB` | 同上 |
| $t[z]$（Buchholz の基本列） | `PSS.operB` | `lean/Buchholz-rel-ord/Buchholz-rel-ord-6.lean` |
| $\textrm{dom}(t)=\omega$ | `Bijectivity.domIsOmega` | `lean/Bijectivity/Cited.lean` |
| $(OT_{\textrm{B}},<_{\textrm{B}})$ | `Bijectivity.OTBsub`, `Bijectivity.rOTB` | 同上 |
| 順序型への同型 | `Bijectivity.tpOTB`（`Ordinal.typein`） | 同上 |
| $o$ | `Bijectivity.o` | 同上 |
| (o1) 単調性 | `Bijectivity.o_lt_of_lessBT` | 同上 |
| (o2) 初期切片への全射性 | `Bijectivity.o_surj_below` | 同上 |
| (o3) 初期切片の上限表示 | `Bijectivity.o_eq_iSup_below` | 同上 |
| (o4) $\leq_{\textrm{B}}$ 版 | `Bijectivity.o_le_of_leBT` | `lean/Bijectivity/17-fseq-convergence.lean` |
| 基本列の共終性 | `Bijectivity.fseq_cofinal`（`PSS.y4_bachmann`） | `lean/Bijectivity/Cited.lean`（`lean/OTB-well-founded-syntactic/OTB-well-founded-syntactic-cofinality.lean`） |
| $<_{\textrm{B}}$ が項全体では整礎でない証拠 | `Bijectivity.descChain_lt`, `Bijectivity.descChain_not_OT` | `lean/Bijectivity/Cited.lean` |
| [Buc1] Lemma 3.2(a) の数項形 $t[m]<_{\textrm{B}}t$ | `PSS.buchholz_fseq_lt` | `lean/Buchholz-1986/Buchholz-1986-3.2-descent.lean` |
| [Buc1] Lemma 3.3 の数項形 $t[m]\in OT_{\textrm{B}}$ | `PSS.buchholz_fseq_closed` | `lean/Buchholz-1986/Buchholz-1986-3.3.lean` |
| 添字単調性 $t[m]<_{\textrm{B}}t[m+1]$ | `Bijectivity.operB_numBT_step`（`PSS.y4_N_mono`） | `lean/Bijectivity/16c-operB-mono.lean` |
| [5] Theorem 1.4(a) に当たる主張（1 節） | `Bijectivity.o_iSup_operB` | `lean/Bijectivity/17-fseq-convergence.lean` |
| 補題（基本列の関係） | `Bijectivity.fseq_relation` | `lean/Bijectivity/16-fseq-relation.lean` |
| $\textrm{dom}(\textrm{Trans}(M))=\omega\Rightarrow\textrm{Lng}(M)>1$ | `Bijectivity.one_lt_lng_of_domIsOmega` | `lean/Bijectivity/15-successor-fseq.lean` |
| $ST_{\textrm{PS}}\subseteq RT_{\textrm{PS}}$ | `PSS.STPS_RTPS` | `lean/6/6.7-standard-reduced.lean` |
| $RT_{\textrm{PS}}\subseteq T_{\textrm{PS}}$ | `PSS.RTPS_TPS` | `lean/6/6.6-reduced-leftend.lean` |
| $\textrm{zeroT}(M)\Leftrightarrow\textrm{Trans}(M)=0$ | `PSS.Trans_preserves_zeroT` | `lean/7/7.3-Trans-preserves-zeroT.lean` |
| $\textrm{Trans}(ST_{\textrm{PS}})\subseteq OT_{\textrm{B}}$ | `PSS.Trans_STPS_OT_B` | `lean/8/8.7-termination.lean` |
| [1] の基本列の降下性 | `PSS.Trans_fseq_descend` | 同上 |
| 本命題 | `Bijectivity.fseq_convergence` | `lean/Bijectivity/17-fseq-convergence.lean` |
| 順序数の上限・後続の性質 | `Ordinal.iSup_le_iff`, `Ordinal.le_iSup`, `Order.succ_le_of_lt`, `Ordinal.typein_surj` | なし（Mathlib） |

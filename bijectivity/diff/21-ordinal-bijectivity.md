[← back](README.md)

# 21: 命題 (変換写像の順序数への全単射性)

## 原文

### 命題

命題 (変換写像の順序数への全単射性)（原文に番号は振られていない）

$`o\circ\textrm{Trans}`$は$`CT_{\textrm{PS}}\to\psi_0\psi_\omega0`$上で全域かつ全単射である。

### 証明

&nbsp;&nbsp;証明  
&nbsp;&nbsp;対応する項の上界未満の字母、対応する項の上界(1)と(2)及び[1]の$`\textrm{Trans}`$が標準形を保つことより$`\{\textrm{Trans}(M)\mid M\in CT_{\textrm{PS}}\}`$は$`\{t\mid t\in OT_{\textrm{B}\omega}\land t\lt_{\textrm{B}}D_0D_\omega0\}`$の$`\lt_{\textrm{B}}`$に対して非有界な部分集合である。  
&nbsp;&nbsp;[4]のLemma 2.2(c)より$`\{o(\textrm{Trans}(M))\mid M\in CT_{\textrm{PS}}\}`$は$`o(D_0D_\omega0)=\psi_0\psi_\omega0`$の非有界な部分集合である。  
&nbsp;&nbsp;[4]のLemma 2.3(b)及び[5]のLemma 1.6より任意の$`t\in\{t\mid t\in OT_{\textrm{B}\omega}\land t\lt_{\textrm{B}}D_10\}`$に対して$`\textrm{dom}(t)=\textrm{cof}(o(t))`$である。  
&nbsp;&nbsp;後続な項の基本列及び[1]の標準形の簡約性より任意の$`M\in CT_{\textrm{PS}}`$に対して、$`\textrm{cof}(o(\textrm{Trans}(M)))=1`$ならば$`o(\textrm{Trans}(M))=o(\textrm{Trans}(M[1])+D_00)=o(\textrm{Trans}(M[1]))+o(D_00)=o(\textrm{Trans}(M[1]))+1`$である。  
&nbsp;&nbsp;基本列の収束性より任意の$`M\in CT_{\textrm{PS}}`$に対して、$`\textrm{cof}(o(\textrm{Trans}(M)))=\omega`$ならば$`o(\textrm{Trans}(M))=\sup_{n\in\mathbb{N}_+}o(\textrm{Trans}(M[n]))`$である。  
&nbsp;&nbsp;[3]の命題11より$`o\circ\textrm{Trans}`$は$`CT_{\textrm{PS}}\to\psi_0\psi_\omega0`$上で全射である。  
&nbsp;&nbsp;$`\textrm{Trans}`$が順序を保つこと、[4]のLemma 2.1及びLemma 2.2(c)より$`o\circ\textrm{Trans}`$は$`CT_{\textrm{PS}}\to\psi_0\psi_\omega0`$上で単射である。  
&nbsp;&nbsp;よって$`o\circ\textrm{Trans}`$は$`CT_{\textrm{PS}}\to\psi_0\psi_\omega0`$上で全域かつ全単射である。□

## Lean

### Lean での命題

```math
\tilde o\circ\textrm{Trans}\ \text{は}\ \{M\mid M\in CT_{\textrm{PS}}\}\to\{\alpha\mid\alpha\lt\tilde\psi\}\ \text{上で全域かつ全単射である}
```

さらに、上界を Buchholz の値そのものに置いた形

```math
\tilde o\circ\textrm{Trans}\ \text{は}\ \{M\mid M\in CT_{\textrm{PS}}\}\to\{\alpha\mid\alpha\lt\psi_0(\psi_\omega(0))\}\ \text{上で全域かつ全単射である}
```

も証明されている。記号は次のとおりである。

- 項・principal 項・$`0`$・$`D_va`$・$`\lt_{\textrm{B}}`$・$`\leq_{\textrm{B}}`$・$`T_{\textrm{B}}`$・$`D_0D_\omega0`$、および $`CT_{\textrm{PS}}`$・$`\lt_{\textrm{PS}}`$・$`\leq_{\textrm{PS}[]}`$・対角列・$`\textrm{Trans}`$ は 20 のページと同じ定義である。添字は $`\mathbb{N}\cup\{\omega\}`$ で、$`\omega`$ はその最大元である。
- $`G_ut`$ は項 $`t`$ から集める部分項の有限列で、$`G_u(\underline{(}p_0\underline{,}\cdots\underline{)})=G_up_0\oplus\cdots`$、$`G_u(D_va)=a\frown G_ua`$（$`u\leq v`$ のとき）、$`G_u(D_va)=()`$（$`u\gt v`$ のとき）である。
- 原文の $`OT_{\textrm{B}\omega}`$（$`D_\omega`$ を許す順序数項）は、principal 列が広義降順であり、各 principal $`D_va`$ について $`a`$ が順序数項でかつ $`G_va`$ の各元が $`\lt_{\textrm{B}}a`$ である、という構造的判定である。原文の $`OT_{\textrm{B}}`$ はこれと $`T_{\textrm{B}}`$ の共通部分である。
- $`\textrm{dom}(t)`$ は構文的なタグで、$`0`$ には空、$`D_00`$ には $`1`$、$`D_\omega0`$ には $`\omega`$、$`D_v0`$（$`0\lt v\lt\omega`$）には $`T_{v-1}`$ を返し、$`a\neq0`$ の $`D_va`$ では $`\textrm{dom}(a)`$ から決まり、複項では末尾 principal のタグを返す。原文の $`\textrm{dom}(t)=1`$、$`\textrm{dom}(t)=\omega`$ はこのタグが $`1`$、$`\omega`$ であることである。
- $`\Omega_u`$ は $`\Omega_0=1`$、$`\Omega_u=\aleph_u`$（$`0\lt u\lt\omega`$）、$`\Omega_\omega=\aleph_\omega`$ であり、$`\Omega_{u+1}`$ は別に $`\Omega_{\omega+1}=\aleph_{\omega+1}`$ まで込めて定める（$`\mathbb{N}\cup\{\omega\}`$ では $`\omega+1=\omega`$ になってしまうため）。
- $`C_u(\alpha)`$ は次の 4 条件を満たす順序数の集合のうち最小のものである。$`\psi_u(\alpha)=\min\{\beta\mid\beta\notin C_u(\alpha)\}`$ であり、$`C`$ と $`\psi`$ は $`\alpha`$ についての整礎再帰で同時に定める。

```math
\beta\lt\Omega_u\Rightarrow\beta\in X,\qquad 0\in X,\qquad x,y\in X\Rightarrow x+y\in X,
```

```math
x\in X\ \land\ x\lt\alpha\ \land\ v\leq\omega\ \land\ x\in C_v(x)\ \Rightarrow\ \psi_v(x)\in X
```

- $`o`$ は [4] の評価写像そのもので、$`o(0)=0`$、$`o(D_va)=\psi_v(o(a))`$、$`o(t_0+t_1)=o(t_0)+o(t_1)`$ を満たす。項は principal 項の列なので、列の評価は先頭から順に加えたものとして定義されている。
- $`\tilde o`$ は $`(OT_{\textrm{B}},\lt_{\textrm{B}})`$ の順序型への同型であり、$`\tilde\psi`$ は $`\{t\mid t\in OT_{\textrm{B}}\land t\lt_{\textrm{B}}D_0D_\omega0\}`$ の順序型である。$`D_0D_\omega0`$ 自身は $`D_\omega`$ を含むので $`OT_{\textrm{B}}`$ の外にあり、そこだけ $`\tilde o(D_0D_\omega0)=\tilde\psi`$ と定めてある。$`\tilde o=o`$（$`D_0D_\omega0`$ 未満の順序数項の上）と $`\tilde\psi=\psi_0(\psi_\omega(0))`$ は証明されている。

### Lean での証明

全単射性は全域性・単射性・全射性の 3 本の合成である。すなわち

```math
\forall M\in CT_{\textrm{PS}},\ \tilde o(\textrm{Trans}(M))\lt\tilde\psi
```

```math
\forall M,N\in CT_{\textrm{PS}},\ \tilde o(\textrm{Trans}(M))=\tilde o(\textrm{Trans}(N))\Rightarrow M=N
```

```math
\forall\alpha\lt\tilde\psi,\ \exists M\in CT_{\textrm{PS}},\ \tilde o(\textrm{Trans}(M))=\alpha
```

の 3 つを示す。原文もこの 3 つを示していて、全域性は第 1 行の「$`\{\textrm{Trans}(M)\mid M\in CT_{\textrm{PS}}\}`$ は $`\{t\mid t\in OT_{\textrm{B}\omega}\land t\lt_{\textrm{B}}D_0D_\omega0\}`$ の部分集合」にあたる。ただし原文と違い、その前に原文が [4] からの引用で済ませている $`\psi_u`$ と $`o`$ を構成する段が要る。第 0 段がその構成、第 1 段が全域性、第 2 段が単射性、第 3 段が全射性である。

#### 0. $`\psi_u`$、$`o`$、$`\tilde o`$、$`\tilde\psi`$ の構成

**$`\psi_u(\alpha)`$ の存在。** $`C_u(\alpha)`$ の生成を段階に分けたもの $`C_u^0(\alpha)=\{\beta\mid\beta\lt\Omega_u\}\cup\{0\}`$、$`C_u^{n+1}(\alpha)=C_u^n(\alpha)\cup\{x+y\mid x,y\in C_u^n(\alpha)\}\cup\{\psi_v(x)\mid v\leq\omega,\ x\in C_u^n(\alpha),\ x\lt\alpha\}`$ を置く。閉包に関する帰納法（4 条件を満たす述語は $`C_u(\alpha)`$ を含む）で $`C_u(\alpha)\subseteq\bigcup_nC_u^n(\alpha)`$。基数 $`\kappa_u=\max(|\Omega_u|,\aleph_0)`$ について $`|C_u^n(\alpha)|\leq\kappa_u`$ が $`n`$ の帰納法で出る（和の集合は $`C_u^n(\alpha)^2`$ の像、$`\psi`$ の集合は $`(\mathbb{N}\cup\{\omega\})\times(C_u^n(\alpha)\cap\alpha)`$ の像で、$`\kappa_u\cdot\kappa_u=\kappa_u`$）。よって $`|C_u(\alpha)|\leq\aleph_0\cdot\kappa_u=\kappa_u`$。一方 $`\kappa_u\lt|\Omega_{u+1}|`$ なので $`\Omega_{u+1}`$ 未満に $`C_u(\alpha)`$ の外の元があり、$`\min`$ が実在して $`\psi_u(\alpha)\lt\Omega_{u+1}`$。また $`\beta\lt\Omega_u`$ はすべて $`C_u(\alpha)`$ に入るから $`\Omega_u\leq\psi_u(\alpha)`$。

**$`\psi`$ の基本性質。** $`x\leq y\Rightarrow C_u(x)\subseteq C_u(y)`$（閉包帰納法。$`\psi`$ の枝で $`x\lt`$ の条件だけが緩む）から $`\psi_u(x)\leq\psi_u(y)`$。さらに $`x\lt y`$ かつ $`x\in C_u(y)`$ かつ $`x\in C_u(x)`$ なら、等号のとき $`\psi_u(x)=\psi_u(y)\in C_u(y)`$ となって $`\psi_u(y)\notin C_u(y)`$ に反するので $`\psi_u(x)\lt\psi_u(y)`$。加法的 principal 性 $`x,y\lt\psi_u(\alpha)\Rightarrow x+y\lt\psi_u(\alpha)`$ は、$`\psi_u(\alpha)\leq x+y`$ とすると $`\psi_u(\alpha)-x\leq y`$ で $`x+(\psi_u(\alpha)-x)=\psi_u(\alpha)`$ が加法閉包から $`C_u(\alpha)`$ に入ってしまうことによる。吸収律 $`\beta\lt\psi_u(\alpha)\Rightarrow\beta+\psi_u(\alpha)=\psi_u(\alpha)`$ もこれから出る。

**崩壊の要（[Buc1] 1.5）。** $`C_u(\alpha)\cap\Omega_{u+1}=\psi_u(\alpha)`$。$`\supseteq`$ は $`\psi_u(\alpha)`$ 未満が $`C_u(\alpha)`$ に入ること（$`\min`$ の定義）と $`\psi_u(\alpha)\lt\Omega_{u+1}`$。$`\subseteq`$ は閉包帰納法で、$`\psi_v(x)`$ の枝では $`\Omega_v\leq\psi_v(x)\lt\Omega_{u+1}`$ から $`v\leq u`$ が出て、$`v\lt u`$ なら $`\psi_v(x)\lt\Omega_{v+1}\leq\Omega_u\leq\psi_u(\alpha)`$、$`v=u`$ なら上の狭義単調性による。

**[Buc1] 1.2(g) と 1.4。** $`\gamma\in C_u(a)`$ かつ $`\gamma=x+y`$ なら $`y\in C_u(a)`$（閉包帰納法。和の枝では $`x`$ が左成分の内か外かで差を取って分ける）。また $`\gamma`$ 以下の加法的 principal のうち最大のものは $`C_u(a)`$ に属する。この 2 つから反転（1.4(b)）: $`\gamma\in C_u(a)`$ が加法的 principal で $`\Omega_u\leq\gamma`$ なら、ある $`v`$ と $`x\lt a`$ が存在して $`x\in C_u(a)`$、$`x\in C_v(x)`$、$`\gamma=\psi_v(x)`$。一意性（1.4(a)）: $`x\in C_u(x)`$、$`y\in C_v(y)`$、$`\psi_u(x)=\psi_v(y)`$ なら $`u=v`$ かつ $`x=y`$（$`u\neq v`$ は $`\Omega`$ の階層で潰し、$`x\neq y`$ は狭義単調性で潰す）。この 2 つを合わせて、順序数側の逆向き橋渡し「$`w\leq v`$、$`x\in C_v(x)`$、$`\psi_v(x)\in C_w(b)`$ ならば $`x\lt b`$ かつ $`x\in C_w(b)`$」が出る。

**[Buc1] Lemma 2.1。** $`s,t\in OT_{\textrm{B}\omega}`$、$`s\lt_{\textrm{B}}t`$ ならば $`o(s)\lt o(t)`$。項・principal・列の 3 つを、項の重さについての整礎相互再帰で同時に証明する。principal 同士 $`D_ua\lt_{\textrm{B}}D_vb`$ では、$`u\lt v`$ のとき $`\psi_u(o(a))\lt\Omega_{u+1}\leq\Omega_v\leq\psi_v(o(b))`$、$`u=v`$ かつ $`a\lt_{\textrm{B}}b`$ のとき帰納法から $`o(a)\lt o(b)`$ で、狭義単調性を使うために $`o(a)\in C_u(o(b))`$ と $`o(a)\in C_u(o(a))`$ が要る。これは橋渡し「$`G_ut`$ の各元の評価が $`b`$ 未満なら $`o(t)\in C_u(b)`$」（項の重さの再帰で、$`\psi`$ の閉包規則をそのまま使う）に、順序数項の条件「$`G_ua`$ の各元は $`\lt_{\textrm{B}}a`$」と帰納法を与えて得る。列同士では、先頭 principal が真に小さければ、降順性から残りの成分も先頭以下なので、$`\psi`$ の加法的 principal 性で列全体が右辺の先頭 principal 未満になる。先頭が等しければ残りの列に帰納法を使う。逆向きは $`\lt_{\textrm{B}}`$ の三分律から出るので、$`s\lt_{\textrm{B}}t\iff o(s)\lt o(t)`$ と $`o`$ の単射性が従う。

**[Buc1] Lemma 2.2(c)。** $`\{o(t)\mid t\in OT_{\textrm{B}\omega}\land t\lt_{\textrm{B}}D_0D_\omega0\}=\{\alpha\mid\alpha\lt\psi_0(\psi_\omega(0))\}`$。$`\subseteq`$ は Lemma 2.1 と $`o(D_0D_\omega0)=\psi_0(\psi_\omega(0))`$。$`\supseteq`$ は「$`C_0(\psi_\omega(0))`$ の元はすべて順序数項の評価である」を閉包帰納法で示す。$`\beta\lt\Omega_0=1`$ と $`0`$ は空列。$`x+y`$ は加法標準形への正規化が要る: 左の項の principal 成分のうち右の先頭より小さいものを落として連結する。落とした部分の評価が右の先頭 principal 未満であること（降順性と Lemma 2.1）と吸収律から、連結の評価が和になる。$`\psi_v(x)`$ は $`x`$ を表す項 $`s`$ から $`D_vs`$ を作る。これが順序数項であるためには $`G_vs`$ の各元が $`\lt_{\textrm{B}}s`$ であることが要り、閉包規則が持っている条件 $`x\in C_v(x)`$ に構文側の逆向き橋渡し（列の評価が $`C_w(b)`$ に属するなら各 principal 成分の評価も属する、を 1.2(g) と先頭 principal の補題で出し、順序数側の逆向き橋渡しに繋ぐ）を通して $`G_vs`$ の各元の評価が $`x`$ 未満であることを出し、Lemma 2.1 の逆向きで $`\lt_{\textrm{B}}s`$ に戻す。

**順序型による $`\tilde o`$。** $`(OT_{\textrm{B}},\lt_{\textrm{B}})`$ は整礎（本リポジトリの構文的整礎性証明）で、三分律と推移律を満たすので整列順序である。$`\tilde o(t)`$ をその順序型への同型、$`\tilde\psi`$ を $`\sup\{\tilde o(t)+1\mid t\in OT_{\textrm{B}},\ t\lt_{\textrm{B}}D_0D_\omega0\}`$ と定める。ここから $`\tilde o`$ の順序保存、$`t\lt_{\textrm{B}}D_0D_\omega0\Rightarrow\tilde o(t)\lt\tilde\psi`$、初期切片への全射性（$`\alpha\lt\tilde o(t_0)`$ なら $`\tilde o(t)=\alpha`$ かつ $`t\lt_{\textrm{B}}t_0`$ なる $`t`$ がある）、その $`\tilde\psi`$ 版（$`\alpha\lt\tilde\psi`$ なら $`t\lt_{\textrm{B}}D_0D_\omega0`$ なる $`t`$ で $`\tilde o(t)=\alpha`$ なるものがある）、$`\tilde o(0)=0`$、$`\tilde o(D_00)=1`$、上限表示 $`\tilde o(t)=\sup\{\tilde o(u)+1\mid u\in OT_{\textrm{B}},\ u\lt_{\textrm{B}}t\}`$ が出る。さらに直後者補題として、$`s\lt_{\textrm{B}}s+_{\textrm{B}}D_00`$ と「$`s\lt_{\textrm{B}}u\lt_{\textrm{B}}s+_{\textrm{B}}D_00`$ なる $`u`$ は無い」を列の比較の計算で示し、初期切片への全射性と合わせて $`\tilde o(s+_{\textrm{B}}D_00)=\tilde o(s)+1`$ を得る。$`OT_{\textrm{B}}`$ の仮定が落とせないことの確認として、$`x_0=D_10`$、$`x_{n+1}=D_0x_n`$ が $`\lt_{\textrm{B}}`$ について狭義降下し $`n\geq2`$ で順序数項でないことも機械検証されている。

**$`\tilde o=o`$ と $`\tilde\psi=\psi_0(\psi_\omega(0))`$。** $`o`$ の側も、Lemma 2.2(c) から同じ上限表示 $`o(t)=\sup\{o(u)+1\mid u\in OT_{\textrm{B}},\ u\lt_{\textrm{B}}t\}`$（$`t\lt_{\textrm{B}}D_0D_\omega0`$ のとき）を満たす。$`\lt_{\textrm{B}}`$ の整礎性による帰納法で、$`D_0D_\omega0`$ 未満の順序数項の上で $`\tilde o=o`$。両者の $`\tilde\psi`$ 版・Lemma 2.2(c) 版の全射性から $`\tilde\psi=\psi_0(\psi_\omega(0))`$。

**共終性。** 後段では使わないが、この構成の上に [5] Theorem 1.4(a) にあたる「$`\textrm{dom}(t)=\omega`$ のとき基本列 $`t[0],t[1],\dots`$ は $`\{u\in OT_{\textrm{B}}\mid u\lt_{\textrm{B}}t\}`$ で共終」も、本リポジトリの構文的な共終性定理の $`\textrm{dom}=\omega`$ 枝としてそのまま得られている。これは 17（基本列の収束性）が使う。

#### 1. 全域性

$`M\in CT_{\textrm{PS}}`$ とする。$`CT_{\textrm{PS}}`$ の第 1 肢 $`M\in ST_{\textrm{PS}}`$ と [1] の $`\textrm{Trans}`$ が標準形を保つことから $`\textrm{Trans}(M)\in OT_{\textrm{B}}`$。対応する項の上界 (1) から $`\textrm{Trans}(M)\lt_{\textrm{B}}D_0D_\omega0`$。この 2 つに $`t\lt_{\textrm{B}}D_0D_\omega0\Rightarrow\tilde o(t)\lt\tilde\psi`$ を適用して $`\tilde o(\textrm{Trans}(M))\lt\tilde\psi`$。

#### 2. 単射性

項の側から述べる。$`M,N\in CT_{\textrm{PS}}`$ で $`\textrm{Trans}(M)=\textrm{Trans}(N)`$ とする。$`\lt_{\textrm{PS}}`$ の三分律で 3 つに分ける。$`M\lt_{\textrm{PS}}N`$ なら $`\textrm{Trans}`$ が順序を保つことより $`\textrm{Trans}(M)\lt_{\textrm{B}}\textrm{Trans}(N)`$ で、仮定の等号で書き換えると $`\textrm{Trans}(N)\lt_{\textrm{B}}\textrm{Trans}(N)`$ となり $`\lt_{\textrm{B}}`$ の非反射性に反する。$`N\lt_{\textrm{PS}}M`$ も同じ。よって $`M=N`$。

順序数の側も同じ形である。$`\tilde o(\textrm{Trans}(M))=\tilde o(\textrm{Trans}(N))`$ とし、三分律で 3 分岐して、$`M\lt_{\textrm{PS}}N`$ の枝では $`\textrm{Trans}(M)\lt_{\textrm{B}}\textrm{Trans}(N)`$ に $`\tilde o`$ の順序保存を適用して $`\tilde o(\textrm{Trans}(M))\lt\tilde o(\textrm{Trans}(N))`$ を得、仮定の等号と非反射性で潰す。$`N\lt_{\textrm{PS}}M`$ も同じ。

#### 3. 全射性

**補助（$`CT_{\textrm{PS}}`$ は基本列で閉じている）。** $`M\in CT_{\textrm{PS}}`$、$`n\geq1`$ ならば $`M[n]\in CT_{\textrm{PS}}`$。可算な標準形の起源 $`M\in CT_{\textrm{PS}}\iff\exists v\in\mathbb{N},\ M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v`$ で $`v`$ を取り、$`n\geq1`$ に対する $`M[n]\leq_{\textrm{PS}[]}M`$ と $`\leq_{\textrm{PS}[]}`$ の推移律で $`M[n]\leq_{\textrm{PS}[]}((j,j))_{j=0}^v`$ を得、同じ同値の逆向きを使う。

**非有界性。** $`\alpha\lt\tilde\psi`$ とする。$`\tilde o`$ の初期切片への全射性（$`\tilde\psi`$ 版）から、$`t\in OT_{\textrm{B}}`$ で $`t\lt_{\textrm{B}}D_0D_\omega0`$ かつ $`\tilde o(t)=\alpha`$ なるものが取れる。$`OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}`$ の第 2 成分 $`t\in T_{\textrm{B}}`$ を対応する項の上界 (2) に渡して、$`M\in CT_{\textrm{PS}}`$ で $`t\lt_{\textrm{B}}\textrm{Trans}(M)`$ なるものを得る。$`\tilde o`$ の順序保存で $`\alpha=\tilde o(t)\lt\tilde o(\textrm{Trans}(M))`$。

**本体。** $`\alpha\lt\tilde\psi`$ を取り、

```math
S=\{\beta\mid\alpha\leq\beta\ \land\ \exists M\in CT_{\textrm{PS}},\ \tilde o(\textrm{Trans}(M))=\beta\}
```

と置く。非有界性から $`S\neq\emptyset`$。順序数の整礎性で $`S`$ の極小元 $`\beta`$ と、その証人 $`M\in CT_{\textrm{PS}}`$（$`\tilde o(\textrm{Trans}(M))=\beta`$）を取る。$`\alpha\leq\beta`$ を $`\alpha=\beta`$ と $`\alpha\lt\beta`$ に分ける。$`\alpha=\beta`$ なら $`M`$ が求める原像である。以下 $`\alpha\lt\beta`$ として矛盾を導く。

$`\textrm{Trans}(M)\neq0`$: もし $`\textrm{Trans}(M)=0`$ なら $`\beta=\tilde o(0)=0`$ となり $`\alpha\lt0`$ で矛盾。

$`\textrm{Trans}(M)\in OT_{\textrm{B}\omega}`$ と $`\textrm{Trans}(M)\lt_{\textrm{B}}D_0D_\omega0`$ と $`\textrm{Trans}(M)\neq0`$ に 19 のページの $`\textrm{dom}`$ の二分類を適用して、$`\textrm{dom}(\textrm{Trans}(M))`$ は $`1`$ か $`\omega`$ のいずれかである。

**後続の場合**（$`\textrm{dom}(\textrm{Trans}(M))=1`$）。[1] の標準形の簡約性で $`M`$ は簡約形なので、後続な項の基本列を $`n=1`$ に適用して

```math
(\textrm{Trans}(M)=D_00\ \land\ \textrm{Trans}(M[1])=0)\quad\text{または}\quad\textrm{Trans}(M[1])+_{\textrm{B}}D_00=\textrm{Trans}(M)
```

を得る。補助より $`M[1]\in CT_{\textrm{PS}}`$ なので、$`\tilde o(\textrm{Trans}(M[1]))`$ が $`S`$ の元であることと $`\lt\beta`$ であることを示せば極小性に反する。第 1 の枝では $`\beta=\tilde o(D_00)=1`$ なので $`\alpha\lt1`$ すなわち $`\alpha=0`$ であり、$`\tilde o(\textrm{Trans}(M[1]))=\tilde o(0)=0`$ だから $`\alpha\leq\tilde o(\textrm{Trans}(M[1]))`$ と $`\tilde o(\textrm{Trans}(M[1]))=0\lt1=\beta`$ がともに言える。第 2 の枝では直後者補題から

```math
\beta=\tilde o(\textrm{Trans}(M[1])+_{\textrm{B}}D_00)=\tilde o(\textrm{Trans}(M[1]))+1
```

であり、$`\tilde o(\textrm{Trans}(M[1]))\lt\beta`$ は明らか、$`\alpha\leq\tilde o(\textrm{Trans}(M[1]))`$ は背理法（$`\tilde o(\textrm{Trans}(M[1]))\lt\alpha`$ なら $`\beta=\tilde o(\textrm{Trans}(M[1]))+1\leq\alpha`$ で $`\alpha\lt\beta`$ に反する）による。

**極限の場合**（$`\textrm{dom}(\textrm{Trans}(M))=\omega`$）。15 のページの補題から $`1\lt\textrm{Lng}(M)`$。基本列の収束性より

```math
\sup_{n\in\mathbb{N}_+}\tilde o(\textrm{Trans}(M[n]))=\tilde o(\textrm{Trans}(M))=\beta .
```

すべての $`n\geq1`$ で $`\tilde o(\textrm{Trans}(M[n]))\leq\alpha`$ だとすると上限も $`\leq\alpha`$ となり $`\beta\leq\alpha`$ で $`\alpha\lt\beta`$ に反する。よってある $`n\geq1`$ で $`\alpha\lt\tilde o(\textrm{Trans}(M[n]))`$。補助より $`M[n]\in CT_{\textrm{PS}}`$ だから $`\tilde o(\textrm{Trans}(M[n]))\in S`$。一方 [1] の基本列の降下性を $`n\geq1`$ と $`1\lt\textrm{Lng}(M)`$ に適用して $`\textrm{Trans}(M[n])\lt_{\textrm{B}}\textrm{Trans}(M)`$ を得、$`\tilde o`$ の順序保存で $`\tilde o(\textrm{Trans}(M[n]))\lt\beta`$。$`\beta`$ の極小性に反する。

いずれの場合も矛盾するので $`\alpha=\beta`$、すなわち $`\alpha`$ は $`\tilde o\circ\textrm{Trans}`$ の像である。

#### 4. 結論

第 1 段・第 2 段・第 3 段を組にして、$`\tilde o\circ\textrm{Trans}`$ は $`CT_{\textrm{PS}}\to\{\alpha\mid\alpha\lt\tilde\psi\}`$ 上で全域かつ全単射である。第 0 段の $`\tilde\psi=\psi_0(\psi_\omega(0))`$ で上界を書き換えれば、値域の上界が Buchholz の $`\psi_0(\psi_\omega(0))`$ そのものである形も得られる。

このほか、上界の項 $`D_0D_\omega0`$ が順序数項であること、$`D_00\in OT_{\textrm{B}}`$、$`\textrm{Trans}(M)\in OT_{\textrm{B}\omega}`$ が決定手続きによる計算として置かれている（前 2 つは以降で使われない）。

## 原文通りに書けなかった理由

- **[W]** 原文が [4] からの引用で済ませている $`\psi_u`$、$`o`$、Lemma 2.1、Lemma 2.2(c) を、この形式化は順序数として構成して証明している

  原文は「表記」節で $`\psi_ua`$、$`D_ua`$、$`G_ua`$、$`o`$ を [4] から引くと書き、証明でも Lemma 2.1 と Lemma 2.2(c) を引用で使う。この形式化にはこれらに対応する公理が無く、$`\Omega_u`$ の定義から $`C_u(\alpha)`$ を「4 条件を満たす最小の集合」として $`\alpha`$ についての整礎再帰で定め、$`|C_u(\alpha)|\leq\max(|\Omega_u|,\aleph_0)\lt|\Omega_{u+1}|`$ の基数評価で $`\psi_u(\alpha)`$ の存在を出し、[Buc1] の 1.2(g)・1.4(a)(b)・1.5 にあたる補題を経て Lemma 2.1 と Lemma 2.2(c) を定理として証明している。省略しているのは原文の側なので分類は W だが、量は本ページの他のどの差異よりも大きい（閉包の基数評価、加法標準形への正規化、$`G_u`$ と $`C_u`$ の双方向の橋渡しがそれぞれ要る）。

- **[S]** 主定理の評価写像は $`(OT_{\textrm{B}},\lt_{\textrm{B}})`$ の順序型による代用で、[4] の評価写像との一致は別に証明している

  主定理は順序型評価 $`\tilde o`$ で述べられていて、値域の上界も $`\{t\in OT_{\textrm{B}}\mid t\lt_{\textrm{B}}D_0D_\omega0\}`$ の順序型 $`\tilde\psi`$ である。$`\tilde\psi=\psi_0(\psi_\omega(0))`$ と、$`D_0D_\omega0`$ 未満の順序数項の上での $`\tilde o=o`$ が証明されているので、上界を Buchholz の $`\psi_0(\psi_\omega(0))`$ に置いた形の主定理も置かれている。ただし写像そのものを $`o`$ に書き換えた形（22 の系には置かれている）は 21 には無い。全単射性は定義域上の値しか見ないので、上の一致から一行で移る。なお、原文が第 1 行の材料に挙げる 対応する項の上界未満の字母 は、$`\tilde o`$ が $`OT_{\textrm{B}}`$ の上で定義されているため全域性にも非有界性にも現れず、$`OT_{\textrm{B}\omega}`$ と $`OT_{\textrm{B}}`$ を同一視する $`\tilde o=o`$ の橋渡しの側で使われている。

- **[W]** 単射性には始域側の $`\lt_{\textrm{PS}}`$ の三分律が要る

  原文は単射性の材料に「$`\textrm{Trans}`$ が順序を保つこと、[4] の Lemma 2.1 及び Lemma 2.2(c)」を挙げる。しかし $`\textrm{Trans}`$ が順序を保つことは $`M\lt_{\textrm{PS}}N\Rightarrow\textrm{Trans}(M)\lt_{\textrm{B}}\textrm{Trans}(N)`$ の一方向でしかないので、$`\tilde o(\textrm{Trans}(M))=\tilde o(\textrm{Trans}(N))`$ から $`M=N`$ を出すには「$`M\lt_{\textrm{PS}}N`$、$`M=N`$、$`N\lt_{\textrm{PS}}M`$ のいずれかが成り立つ」という始域側の三分律（14 の命題（順序の線形性））が要る。原文はこれを材料に挙げていない。逆に、値域側で実際に使われるのは $`\tilde o`$ が $`\lt_{\textrm{B}}`$ を保つことと $`\lt_{\textrm{B}}`$ の非反射性だけで、原文が挙げる 2 つの補題のうち初期切片への全射性は単射性の議論には現れない。

- **[W]** $`M[n]\in CT_{\textrm{PS}}`$ を原文は確かめていない

  全射性の議論は $`\tilde o(\textrm{Trans}(M[1]))`$ や $`\tilde o(\textrm{Trans}(M[n]))`$ を「$`CT_{\textrm{PS}}`$ の元の像」として扱うので、$`M[n]`$ が定義域に入っていることが要る。原文はこの確認に触れない。この形式化では 可算な標準形の起源、$`n\geq1`$ に対する $`M[n]\leq_{\textrm{PS}[]}M`$、$`\leq_{\textrm{PS}[]}`$ の推移律から補っている。

- **[W]** 原文が [3] の命題 11 に委ねている全射性の一歩を、順序数の整礎性による最小反例の議論で埋めている

  原文は「非有界性」「$`\textrm{cof}=1`$ の場合の値」「$`\textrm{cof}=\omega`$ の場合の値」を並べたうえで [3] の命題 11 を引いて全射性を結ぶ。この形式化にはその引用が無く、同じ 3 つの材料から直接示す。$`\alpha\lt\tilde\psi`$ に対して $`S=\{\beta\mid\alpha\leq\beta\land\beta\in\textrm{Im}(\tilde o\circ\textrm{Trans})\}`$ を取り、非有界性から $`S\neq\emptyset`$、順序数の整礎性から極小元 $`\beta`$ とその証人 $`M`$ を取り、$`\alpha\lt\beta`$ を仮定して、後続の場合は $`M[1]`$ の像が、極限の場合はある $`M[n]`$ の像が $`S`$ に属してかつ $`\beta`$ 未満であることを示して極小性に反させる。この筋には原文が挙げていない材料も入る。極限の場合に $`\tilde o(\textrm{Trans}(M[n]))\lt\beta`$ を言うために [1] の 基本列の降下性 $`\textrm{Trans}(M[n])\lt_{\textrm{B}}\textrm{Trans}(M)`$ と、その適用条件 $`1\lt\textrm{Lng}(M)`$（15 のページの補題が $`\textrm{dom}(\textrm{Trans}(M))=\omega`$ から与える）を使う。

- **[W]** $`\textrm{dom}`$ の場合分けが尽くされていることに要る $`\textrm{Trans}(M)\neq0`$ の除外を原文は書いていない

  原文は $`\textrm{cof}(o(\textrm{Trans}(M)))=1`$ と $`=\omega`$ の 2 つの場合しか扱わないが、$`o(\textrm{Trans}(M))=0`$ のときは $`\textrm{cof}=0`$ でどちらにも当たらない。この形式化では、極小元 $`\beta`$ が $`\alpha`$ より真に大きいという仮定から $`\beta\neq0`$ が出るので $`\textrm{Trans}(M)\neq0`$ が言え、そのうえで 19 のページの $`\textrm{dom}`$ の二分類（上界 $`D_0D_\omega0`$ 未満の非零な順序数項の $`\textrm{dom}`$ は $`1`$ か $`\omega`$）を使って 2 分岐が尽くされることを示している。

- **[R]** 原文の $`\textrm{dom}(t)=\textrm{cof}(o(t))`$ は使わない

  原文は [4] の Lemma 2.3(b) と [5] の Lemma 1.6 で構文的な $`\textrm{dom}`$ を順序数の $`\textrm{cof}`$ に移し、$`\textrm{cof}`$ で場合分けする。この形式化では 後続な項の基本列 と 基本列の収束性 がどちらも構文的な $`\textrm{dom}(\textrm{Trans}(M))`$ の条件で述べられており、場合分けもそのまま $`\textrm{dom}`$ で行うので、移す一歩が要らない。原文がこの一歩のために置いた上界 $`t\lt_{\textrm{B}}D_10`$ もこの形式化には現れず、代わりに 19 のページの $`\textrm{dom}`$ の二分類が上界 $`D_0D_\omega0`$ 未満で直接 2 分岐を与える。

- **[S]** 後続な項の基本列の退化した枝も分岐として処理している

  この形式化の 後続な項の基本列 は「$`\textrm{Trans}(M)=D_00`$ かつ $`\textrm{Trans}(M[n])=0`$」または「$`\textrm{Trans}(M[n])+_{\textrm{B}}D_00=\textrm{Trans}(M)`$」という選言で、原文の等式 $`o(\textrm{Trans}(M))=o(\textrm{Trans}(M[1])+D_00)`$ にあたるのは第 2 の枝だけである。15 の証明は常に第 2 の枝を返すので第 1 の枝が渡ってくることは無いが、言明が選言である以上ここでも処理が要る。この形式化では第 1 の枝を、$`\beta=\tilde o(D_00)=1`$ と $`\alpha\lt\beta`$ から $`\alpha=0=\tilde o(0)=\tilde o(\textrm{Trans}(M[1]))`$ として潰している。結論も下流も変わらない。

- **[S]** $`o`$ の加法性の代わりに「$`s`$ と $`s+_{\textrm{B}}D_00`$ の間に項が無い」ことから $`\tilde o(s+_{\textrm{B}}D_00)=\tilde o(s)+1`$ を出している

  原文は $`o(\textrm{Trans}(M[1])+D_00)=o(\textrm{Trans}(M[1]))+o(D_00)=o(\textrm{Trans}(M[1]))+1`$ と、[4] の $`o`$ の加法性と $`o(D_00)=1`$ で計算する。主定理が使う $`\tilde o`$ は順序型として定義されていて加法性が定義から出ないので、この形式化では代わりに $`s\lt_{\textrm{B}}s+_{\textrm{B}}D_00`$（列の末尾に $`D_00`$ を足すと真に大きい）と「$`s\lt_{\textrm{B}}u\lt_{\textrm{B}}s+_{\textrm{B}}D_00`$ なる項 $`u`$ は無い」という 2 つの構文的補題を示し、初期切片への全射性と合わせて $`\tilde o(s+_{\textrm{B}}D_00)`$ が $`\tilde o(s)`$ の直後者であることを出す。得られる等式は原文と同じで、$`\tilde o(D_00)=1`$ も原文と同じ形で使う。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| 命題 (変換写像の順序数への全単射性) | `oTrans_bijOn` | `lean/Bijectivity/21-ordinal-bijectivity.lean` |
| 上界を $`\psi_0(\psi_\omega(0))`$ に置いた形 | `oTrans_bijOn_psi` | `lean/Bijectivity/PsiBridge.lean` |
| 全域性 | `oTrans_mapsTo` | `lean/Bijectivity/21-ordinal-bijectivity.lean` |
| 単射性（項の側） | `trans_injOn` | 同上 |
| 単射性（順序数の側） | `oTrans_injOn` | 同上 |
| 全射性 | `oTrans_surjOn` | 同上 |
| 非有界性 | `oTrans_unbounded` | 同上 |
| $`CT_{\textrm{PS}}`$ は基本列で閉じている | `ctps_oper` | 同上 |
| $`\textrm{Trans}(M)\in OT_{\textrm{B}}`$、$`\in OT_{\textrm{B}\omega}`$ | `OTB_Trans_of_CTPS`、`OT_Trans_of_CTPS` | 同上 |
| $`D_0D_\omega0\in OT_{\textrm{B}\omega}`$、$`D_00\in OT_{\textrm{B}}`$ | `OT_DzeroDomegaZero`、`OTB_DzeroZero`、`OT_DzeroZero` | 同上 |
| $`\tilde o(D_00)=1`$（$`D_00`$ の別表記版） | `o_DzeroZero'` | 同上 |
| $`\Omega_u`$、$`\Omega_{u+1}`$ | `Om`、`OmSucc` | `lean/Bijectivity/Psi.lean` |
| $`C_u(\alpha)`$ の 4 条件・最小性・閉包帰納法 | `IsCClosed`、`CSetOf`、`CSet`、`CSet_induction` | 同上 |
| $`\psi_u(\alpha)`$ | `psi`（`cpsi`、`cpsiStep` による同時再帰） | 同上 |
| 段階 $`C_u^n(\alpha)`$ と基数評価 | `CStage`、`CGen_stage`、`CBound`、`mk_CStage_le`、`mk_CSet_le`、`CBound_lt` | 同上 |
| $`\psi_u(\alpha)`$ の存在 | `exists_not_mem_lt_OmSucc`、`CSet_ne_univ`、`psi_not_mem`、`lt_psi_mem` | 同上 |
| $`\Omega_u\leq\psi_u(\alpha)\lt\Omega_{u+1}`$ | `Om_le_psi`、`psi_lt_OmSucc` | 同上 |
| $`\Omega`$ の単調性 | `OmSucc_le_Om`、`Om_le_Om`、`le_of_Om_lt_OmSucc` | 同上 |
| $`\psi`$ の単調性 | `CGen_mono_arg`、`psi_mono`、`psi_lt_psi` | 同上 |
| $`\psi_u(\alpha)`$ は加法的 principal・吸収律 | `add_lt_psi`、`isPrincipal_add_psi`、`add_psi_eq` | 同上 |
| [Buc1] 1.5（$`C_u(\alpha)\cap\Omega_{u+1}=\psi_u(\alpha)`$） | `mem_CSet_lt_psi`、`CSet_inter_OmSucc` | 同上 |
| [Buc1] 1.2(g) と先頭 principal | `CSet_right_summand`、`CSet_leading` | 同上 |
| [Buc1] 1.4(b)（反転）、1.4(a)（一意性） | `CSet_inversion`、`psi_inj` | 同上 |
| 逆向き橋渡し（順序数側） | `lt_of_psi_mem` | 同上 |
| [4] の評価写像 $`o`$ | `oval`、`ovalBP`、`ovalList` | 同上 |
| $`G_u`$ の元は順序数項・より軽い | `isOT_of_mem_gatherBT` 他、`weight_of_mem_gatherBT` 他 | 同上 |
| [Buc1] Lemma 2.1（順方向・iff・単射性） | `oval_lt_of_lessBT`（`oval_lt_of_lessBP`、`oval_lt_of_lessBPList` と相互再帰）、`oval_lt_iff`、`oval_injOn` | 同上 |
| $`G_u\to C_u`$ の橋渡し | `mem_CSet_of_gatherBT`、`mem_CSet_of_gatherBP`、`mem_CSet_of_gatherBPList` | 同上 |
| 構文側の逆向き橋渡し | `ovalBP_mem_of_oval_mem`、`gather_lt_BT`、`gather_lt_BP`、`gather_lt_BPList` | 同上 |
| 加法標準形への正規化 | `naddBT`、`isOT_naddBT`、`oval_naddBT`、`oval_dropWhile_lt` | 同上 |
| [Buc1] Lemma 2.2(c) | `SurjCore`、`surj_core_of_psi`、`surj_psi`、`surj_core`、`oval_image_subset`、`oval_surjOn_below` | 同上 |
| 順序型評価 $`\tilde o`$ | `o`（`tpOTB`、`oOTB` 経由） | `lean/Bijectivity/Cited.lean` |
| $`\tilde\psi`$ | `psi0psiOmega0`（$`\tilde o(D_0D_\omega0)=\tilde\psi`$ は `o_DzeroDomegaZero`） | 同上 |
| $`(OT_{\textrm{B}},\lt_{\textrm{B}})`$ が整列順序 | `rOTB` とその `IsWellFounded`／`Std.Trichotomous`／`IsTrans`／`IsWellOrder` インスタンス | 同上 |
| $`\tilde o`$ の順序保存 | `o_lt_of_lessBT` | 同上 |
| $`t\lt_{\textrm{B}}D_0D_\omega0\Rightarrow\tilde o(t)\lt\tilde\psi`$ | `o_lt_psi` | 同上 |
| 初期切片への全射性 | `o_surj_below`、`o_surj_below_psi` | 同上 |
| $`\tilde o(0)=0`$、$`\tilde o(D_00)=1`$ | `o_BZero`、`o_DzeroZero` | 同上 |
| 直後者補題と $`\tilde o(s+_{\textrm{B}}D_00)=\tilde o(s)+1`$ | `lessBT_addBT_D00_self`、`no_between_snoc_D00`、`o_addBT_DzeroZero` | 同上 |
| 上限表示 $`\tilde o(t)=\sup\{\tilde o(u)+1\}`$ | `o_eq_iSup_below` | 同上 |
| $`BT`$ 全体では $`\lt_{\textrm{B}}`$ が整礎でない証拠 | `descChain`、`descChain_lt`、`descChain_not_OT` | 同上 |
| [5] Theorem 1.4(a)（基本列の共終性） | `FseqCofinal`、`fseq_cofinal` | 同上 |
| $`\textrm{dom}(t)=1`$、$`=\omega`$ の記法 | `domIsOne`、`domIsOmega` | 同上 |
| 共終性の証明本体 | `y4_bachmann` | `lean/OTB-well-founded-syntactic/OTB-well-founded-syntactic-cofinality.lean` |
| $`(OT_{\textrm{B}},\lt_{\textrm{B}})`$ の整礎性 | `OT_B_wellFounded` | `lean/OTB-well-founded-syntactic/OTB-well-founded-syntactic-main.lean` |
| $`D_0D_\omega0`$ 未満の順序数項全体 | `Below` | `lean/Bijectivity/PsiBridge.lean` |
| $`o`$ の上限表示と $`\tilde o=o`$ | `oval_eq_iSup_below`、`o_eq_oval` | 同上 |
| $`\tilde\psi=\psi_0(\psi_\omega(0))`$ | `psi0psiOmega0_eq` | 同上 |
| 系 (ペア数列の解析)(1) を $`o`$ で書いた形 | `analysis_ordinal_oval` | 同上 |
| 項、principal 項、$`0`$、$`D_va`$、$`\lt_{\textrm{B}}`$、$`\leq_{\textrm{B}}`$ | `PSS.BT`、`PSS.BP`、`PSS.BZero`、`PSS.Dprin`、`PSS.lessBT`、`PSS.leBT` | `lean/Buchholz-1986/Buchholz-1986-2.1.lean` |
| $`\lt_{\textrm{B}}`$ の非反射性・三分律・推移律 | `lessBT_linear_irrefl`、`lessBT_linear_trichotomy`、`lessBT_linear_trans` | `lean/Buchholz-1986/Buchholz-1986-2.1-order.lean` |
| $`G_ut`$、$`T_{\textrm{B}}`$、$`OT_{\textrm{B}\omega}`$、$`OT_{\textrm{B}}`$、降順性 | `PSS.gatherBT`、`PSS.T_B`、`PSS.OT`、`PSS.OT_B`、`PSS.isOT_BT`、`PSS.descP` | `lean/Buchholz-1986/Buchholz-1986-2.2.lean` |
| $`+_{\textrm{B}}`$、$`\textrm{dom}`$ のタグ | `PSS.addBT`、`PSS.domTag` | `lean/Buchholz-1986/Buchholz-1986-3.2.lean` |
| 項の重さ | `btWeight`、`bpWeight`、`bpListWeight` | `lean/Buchholz-rel-ord/Buchholz-rel-ord-6.lean` |
| $`M\in CT_{\textrm{PS}}`$、$`M\lt_{\textrm{PS}}N`$、$`M\leq_{\textrm{PS}[]}N`$ | `CTPS`、`ltPS`、`leExpPS` | `lean/Bijectivity/Defs.lean` |
| $`\lt_{\textrm{PS}}`$ の三分律 | `ltPS_trichotomy` | `lean/Bijectivity/02-lex-linear.lean` |
| $`\leq_{\textrm{PS}[]}`$ の推移律 | `leExpPS_trans` | `lean/Bijectivity/03-exp-order-transitive.lean` |
| $`M[n]\leq_{\textrm{PS}[]}M`$ | `oper_leExpPS` | `lean/Bijectivity/09-standard-iff-exp.lean` |
| 可算な標準形の起源 | `ctps_iff_leExpPS` | `lean/Bijectivity/10-countable-standard-origin.lean` |
| 後続な項の基本列 | `successor_fseq` | `lean/Bijectivity/15-successor-fseq.lean` |
| $`\textrm{dom}(\textrm{Trans}(M))=\omega\Rightarrow1\lt\textrm{Lng}(M)`$ | `one_lt_lng_of_domIsOmega` | 同上 |
| $`D_00`$ | `DzeroZero` | 同上 |
| 基本列の収束性 | `fseq_convergence` | `lean/Bijectivity/17-fseq-convergence.lean` |
| $`\textrm{Trans}`$ が順序を保つこと | `trans_lessBT_of_ltPS` | `lean/Bijectivity/18-trans-preserves-order.lean` |
| 対応する項の上界未満の字母 | `OT_iff_OT_B_of_lt` | `lean/Bijectivity/19-alphabet-below-bound.lean` |
| $`\textrm{dom}`$ の二分類 | `domTag_cases_of_bound` | 同上 |
| 対応する項の上界 (1)、(2) | `trans_lt_bound`、`exists_trans_gt` | `lean/Bijectivity/20-term-upper-bound.lean` |
| $`D_0D_\omega0`$ | `DzeroDomegaZero`（`Psi.lean` の `DzeroDomegaZeroP` と定義上同一） | `lean/Bijectivity/Cited.lean` |
| [1] の $`\textrm{Trans}`$ が標準形を保つこと | `PSS.Trans_STPS_OT_B` | `lean/8/8.7-termination.lean` |
| [1] の 基本列の降下性 | `PSS.Trans_fseq_descend` | 同上 |
| [1] の 標準形の簡約性 | `PSS.STPS_RTPS` | `lean/6/6.7-standard-reduced.lean` |
| $`M[n]`$、$`\textrm{Lng}`$、$`ST_{\textrm{PS}}`$、$`RT_{\textrm{PS}}`$、$`\textrm{Trans}`$ | `PSS.oper`、`PSS.Lng`、`PSS.STPS`、`PSS.RTPS`、`PSS.Trans` | `lean/PSS/Defs.lean`、`lean/PSS/Standard.lean`、`lean/PSS/Red.lean`、`lean/PSS/Trans.lean` |
| 順序数の整礎性、順序型 $`\textrm{typein}`$、上限 | `wellFounded_lt`、`Ordinal.typein`、`Ordinal.iSup_le_iff`、`Ordinal.le_iSup` | なし（Mathlib） |

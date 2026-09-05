[← back](README.md)

# 16: 補題 (基本列の関係)

## 原文

### 命題

補題 (基本列の関係)

任意の$M\in ST_{\textrm{PS}}$と$m\in\mathbb{N}$に対して、$\textrm{dom}(\textrm{Trans}(M))=\omega$ならばある$n\in\mathbb{N}_+$が存在して$\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])$である。

### 証明

$\textrm{Trans}$の定義中の記号を$M$に対して定義する。  
[1]の標準形の簡約性より$M$は簡約である。  
$\textrm{dom}(0)=0\neq\omega$かつ任意の$u\in\mathbb{N}$に対して$\textrm{dom}(D_u0)=\Omega_u\neq\omega$であるから$j_1>0$である。  
$M$が単項であるとする。  
　$t_1=0$とする。  
　　$M=((0,0),(1,0))$または$M=((0,0),(1,1))$である。[1]の基本列の降下性の証明を参照。  
　　$M=((0,0),(1,0))$とする。  
　　　$\textrm{Trans}(M)=D_0D_00$かつ任意の$n\in\mathbb{N}$に対して$\textrm{Trans}(M[n])=(D_00)\times(n-1)$である。[1]の基本列の降下性の証明を参照。  
　　　$\textrm{dom}(D_00)=1$であるから$[]$の定義より任意の$n\in\mathbb{N}$に対して$(D_0D_00)[n]=(D_0(D_00[0]))\times(n+1)=(D_00)\times(n+1)$である。  
　　　よって$\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[m+2])$である。  
　　$M=((0,0),(1,1))$とする。  
　　　$\textrm{Trans}(M)=D_0D_10$かつ任意の$n\in\mathbb{N}$に対して$\textrm{Trans}(M[n])=D_0^n0$である。[1]の基本列の降下性の証明を参照。  
　　　$\textrm{dom}(D_10)=\Omega_1$であるから$[]$の定義より任意の$n\in\mathbb{N}$に対して$(D_0D_10)[n]=D_0D_0^nD_0D_00=D_0^{n+3}0$である。  
　　　よって$\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[m+3])$である。  
　$t_1\neq0$とする。  
　　$M$が条件(I)-(VI)を満たすとき、それぞれ[1]の条件(I)の下でのTransと基本列の交換関係(1)、条件(II)の下でのTransと基本列の交換関係(2)、条件(III)か(IV)の下でのTransと基本列の交換関係(3)、条件(V)の下でのTransと基本列の交換関係(3)及び条件(VI)の下でのTransと基本列の交換関係(2)よりある$n\in\mathbb{N}_+$が存在して$\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])$である。  
よって任意の$M\in PT_{\textrm{PS}}\cap ST_{\textrm{PS}}$と$m\in\mathbb{N}$に対して、$\textrm{dom}(\textrm{Trans}(M))=\omega$ならばある$n\in\mathbb{N}_+$が存在して$\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])$である。  
$M$が複項であるとする。  
　任意の$t_0,t_1\in T_{\textrm{B}}$と$m\in\textrm{dom}(t_1)$に対して$\textrm{dom}(t_0+t_1)=\textrm{dom}(t_1)$かつ$(t_0+t_1)[m]=t_0+(t_1[m])$である。  
　上より任意の$t\in T_{\textrm{B}}$に対して$\textrm{dom}(t+D_00)=\textrm{dom}(D_00)=1$であるから$P(M)_{J_1}\neq((0,0))$である。  
　仮定より$\textrm{dom}(\textrm{Trans}(P(M)_{J_1}))=\omega$である。  
　[1]の$P$の各成分の非複項性及び標準形の単項成分が標準形であることより$P(M)_{J_1}\in PT_{\textrm{PS}}\cup ST_{\textrm{PS}}$である。  
　上より任意の$m\in\mathbb{N}$に対しある$n\in\mathbb{N}_+$が存在して$\textrm{Trans}(P(M)_{J_1})[m]\leq_{\textrm{B}}\textrm{Trans}(P(M)_{J_1}[n])$である。  
　$\textrm{dom}(0)=0\neq\omega$かつ任意の$u\in\mathbb{N}$に対して$\textrm{dom}(D_u0)=\Omega_u\neq\omega$であるから$\textrm{Lng}(P(M)_{J_1})>1$である。  
　[1]の$P$と基本列の関係(2)より任意の$n\in\mathbb{N}_+$に対して$P(M[n])=(P(M)_J)_{J=0}^{J_1-1}\oplus_{T_{\textrm{PS}}}P(P(M)_{J_1}[n])$である。  
　[1]の$P$の各成分の非複項性(2)より任意の$n\in\mathbb{N}_+$に対して$M[n]$は複項である。  
　任意の$M\in T_{\textrm{PS}}$に対して、$M$が零項ならば$M^+=D_00$、$M$が零項でないならば$M^+=\textrm{Trans}(M)$とする。  
　[1]の$\textrm{Trans}$の$(\textrm{IncrFirst},\textrm{Red})$不変$P$同変性(2)、また任意の$t_0,t_1\in T_{\textrm{B}}^{<\omega}$に対して明らかに$\Sigma_{\textrm{B}}(t_0+t_1)=\Sigma_{\textrm{B}}t_0+\Sigma_{\textrm{B}}t_1$であり、任意の$n\in\mathbb{N}_+$に対して$P(M)_{J_1}$及び$P(M)_{J_1}[n]$は零項ではないから、$P(M)_{J_1}^+=\textrm{Trans}(P(M)_{J_1})$かつ$\textrm{Trans}(M)=\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1}$かつ任意の$n\in\mathbb{N}_+$に対して

$$\begin{array}{l}\textrm{Trans}(M[n])\cr =\Sigma_{\textrm{B}}(P(M[n])_J^+)_{J=0}^{\textrm{Lng}(P(M[n]))-1}\cr =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+\Sigma_{\textrm{B}}(P(P(M)_{J_1}[n])_J^+)_{J=0}^{\textrm{Lng}(P(P(M)_{J_1}[n]))-1}\cr =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+\textrm{Trans}(P(M)_{J_1}[n])\end{array}$$

である。  
　よって

$$\begin{array}{l}\textrm{Trans}(M)[m]\cr =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1}[m]\cr =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+(P(M)_{J_1}^+[m])\cr =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+(\textrm{Trans}(P(M)_{J_1})[m])\cr =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+\textrm{Trans}(P(M)_{J_1}[m])\cr =\textrm{Trans}(M[m])\cr \leq_{\textrm{B}}\textrm{Trans}(M[m])\end{array}$$

である。  
よっていずれの場合でもある$n\in\mathbb{N}_+$が存在して$\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])$である。□

## Lean

### Lean での命題

$$\forall M\in ST_{\textrm{PS}},\ \forall m\in\mathbb{N},\ \textrm{dom}(\textrm{Trans}(M))=\omega\ \Rightarrow\ \exists n\in\mathbb{N}_+,\ \textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])$$

原文の命題そのままである。$\textrm{dom}$ は Buchholz の $\textrm{dom}$ を 4 値のタグ
（$\emptyset$、$\{0\}$、$\omega$、$T_u$）として実装したもので、$\textrm{dom}(t)=\omega$ は
そのタグが $\omega$ であることを指す。$a[z]$、$\leq_{\textrm{B}}$、$+$、$\times$ も
原文（＝[1]、[4]）の $[]$、$\leq_{\textrm{B}}$、$+$、$\times$ の形式化をそのまま使う。
自然数 $m$ は Buchholz 項としては $m$ 個の $D_00$ の和で表され、$a[m]$ はその項を
$a[\cdot]$ に食わせたものである。

原文の証明が前半で示す中間結論（原文の「よって任意の$M\in PT_{\textrm{PS}}\cap ST_{\textrm{PS}}$と…」の行）は、
**単項の場合**として別の命題に切り出されている。

$$\text{（単項の場合）}\quad\forall M\in ST_{\textrm{PS}},\ M\text{ が単項},\ \textrm{Lng}(M)>1,\ \textrm{dom}(\textrm{Trans}(M))=\omega\ \Rightarrow\ \exists n\in\mathbb{N}_+,\ \textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])$$

さらに、原文が [1] から引く 5 つの交換関係のうち条件 (II) のものと、原文には無い
$[]$ の添字単調性が、それぞれ次の形の命題として切り出され、別ファイルで無条件に供給される。

$$\text{（条件 (II) の交換関係の逆向き）}\quad\forall M\in ST_{\textrm{PS}},\ M\text{ が単項},\ j_1>1,\ \text{条件 (II)}\ \Rightarrow\ \exists n\in\mathbb{N}_+,\ \textrm{Trans}(M[n])=\textrm{Trans}(M)[m]$$

$$\text{（}[]\text{ の添字単調性）}\quad\forall a\in OT_{\textrm{B}},\ \textrm{dom}(a)=\omega\land m\leq m'\ \Rightarrow\ a[m]\leq_{\textrm{B}}a[m']$$

以下、$j_1=\textrm{Lng}(M)-1$、$j_0$ は段 $0$ における $j_1$ の親、$j_{-1}=\textrm{Adm}_M(j_0)$、
$t_1=\textrm{Trans}(\textrm{Pred}(M))$、$t_2$ は $\textrm{Trans}$ の定義中の $t_2$ とする（原文の記号）。

### Lean での証明

主定理は、下の **A**（複項の場合の帰着）に **B**（単項の場合）を食わせ、
**B** にはさらに **C**（条件 (II)）と **D**（$[]$ の添字単調性）を食わせたものである。

#### A. 複項の場合（原文の後半）

**A0. $j_1>0$。** 原文の「$\textrm{dom}(0)=0\neq\omega$ かつ $\textrm{dom}(D_u0)=\Omega_u\neq\omega$ であるから $j_1>0$」に
あたる補題は、$M$ が簡約で $\textrm{dom}(\textrm{Trans}(M))=\omega$ ならば $\textrm{Lng}(M)>1$、という形で立てられている。
証明は対偶で、$\textrm{Lng}(M)=1$ すなわち $M=((c,b))$ とする。$b=0$ なら $M$ は零項なので簡約性から
$M=((0,0))$、$\textrm{Trans}(M)=0$ でタグは $\emptyset$。$b\neq0$ なら $\textrm{Trans}$ の定義の基底枝から
$\textrm{Trans}(M)=D_b0$ で、タグは $T_{b-1}$。いずれも $\omega$ でない。原文が挙げる
$\textrm{dom}(D_u0)=\Omega_u$ のうち $u=0$（タグ $\{0\}$）の場合は、簡約性で零項に落ちるのでここには現れない。

**A1. 場合分け。** $M\in ST_{\textrm{PS}}$ から [1] の標準形の簡約性で $M$ は簡約、したがって $M\in T_{\textrm{PS}}$。
A0 より $\textrm{Lng}(M)>1$。$M$ が単項なら B をそのまま適用して終わる。以下 $M$ は単項でないとする。
$\textrm{Lng}(M)>1$ より $M$ は零項でもないので、零項・単項・複項の三分から $M$ は複項である。

**A2. 最終 $P$ 成分への分解。** $A=(M_j)_{j=0}^{\textrm{Pcut}(M)-1}$、$P(M)_{J_1}=(M_j)_{j=\textrm{Pcut}(M)}^{j_1}$ と置く。
[1] の $\textrm{Trans}$ の複項枝は

$$\textrm{Trans}(M)=\begin{cases}\textrm{Trans}(A)+D_00&(P(M)_{J_1}=((0,0)))\cr  \textrm{Trans}(A)+\textrm{Trans}(P(M)_{J_1})&(\text{その他})\end{cases}$$

である（$M$ が簡約かつ複項であることだけを仮定する）。

**A3. $P(M)_{J_1}\neq((0,0))$。** 原文と同じ。$P(M)_{J_1}=((0,0))$ とすると A2 の第 1 枝で
$\textrm{Trans}(M)=\textrm{Trans}(A)+D_00$ である。$u\neq0$ ならば $\textrm{dom}(t+u)=\textrm{dom}(u)$（$+$ は
principal 項の列の連結で、$\textrm{dom}$ は末尾の principal 項だけで決まるから）を $u=D_00$ に使うと
$\textrm{dom}(\textrm{Trans}(M))=\textrm{dom}(D_00)=\{0\}$ となり、仮定 $\textrm{dom}(\textrm{Trans}(M))=\omega$ に反する。
したがって A2 の第 2 枝が成り立つ。

**A4. $P(M)_{J_1}$ の性質。** つぎの 4 つを順に出す。

1. $P(M)_{J_1}\in ST_{\textrm{PS}}$。$M\in ST_{\textrm{PS}}$ を「対角列から $n\geq1$ の基本列を $k$ 回とって得られる」という
   階層 $S_kT_{\textrm{PS}}$ に落とし、[1] の「$S_kT_{\textrm{PS}}$ の $P$ 成分はまた $S_kT_{\textrm{PS}}$」を添字
   $\textrm{Lng}(P(M))-1$ に適用し、$S_kT_{\textrm{PS}}\subseteq ST_{\textrm{PS}}$ で戻す。最終成分が
   $P(M)_{J_1}$ であることは [1] の $P$ の複項枝（$P(M)$ の最後の成分は $(M_j)_{j=\textrm{Pcut}(M)}^{j_1}$、
   残りは $P(A)$）による。これが原文の「標準形の単項成分が標準形であること」。
2. $P(M)_{J_1}$ は単項。[1] の $P$ の各成分の非複項性より、$P(M)_{J_1}$ は零項か単項である。
   零項なら、簡約な零項は $((0,0))$ に限るので A3 に反する。
3. $\textrm{Trans}(P(M)_{J_1})\neq0$。[1] の $\textrm{Trans}$ が零項性を保つこと
   （$M\in T_{\textrm{PS}}$ で「$M$ が零項 $\Leftrightarrow$ $\textrm{Trans}(M)=0$」）と 2 による。
4. $\textrm{dom}(\textrm{Trans}(P(M)_{J_1}))=\omega$ と $\textrm{Lng}(P(M)_{J_1})>1$。前者は A2 の第 2 枝と 3 に
   $\textrm{dom}(t+u)=\textrm{dom}(u)$ を使う。後者は A0 の補題を $P(M)_{J_1}$ に適用したもので、
   原文の「$\textrm{dom}(0)=0\neq\omega$ …であるから $\textrm{Lng}(P(M)_{J_1})>1$」にあたる。

**A5. 単項の場合の適用。** B を $P(M)_{J_1}$ と $m$ に適用して、$n\geq1$ と

$$\textrm{Trans}(P(M)_{J_1})[m]\leq_{\textrm{B}}\textrm{Trans}(P(M)_{J_1}[n])$$

を得る。この $n$ を結論の $n$ として取る（原文は $n=m$ とするが、B が返す $n$ は $m$ とは限らない）。

**A6. $M[n]$ の分解。** [1] の $P$ と基本列の関係 (2) を、$M\in T_{\textrm{PS}}$、$n\geq1$、
$\textrm{Lng}(P(M)_{J_1})>1$ の下で使う。得られるのは 2 つの等式

$$M[n]=\Bigl(\bigoplus_{T_{\textrm{PS}}}(P(M)_J)_{J=0}^{J_1-1}\Bigr)\oplus_{\mathbb{N}^2}P(M)_{J_1}[n]=A\oplus_{\mathbb{N}^2}P(M)_{J_1}[n],$$

$$P(M[n])=(P(M)_J)_{J=0}^{J_1-1}\oplus_{T_{\textrm{PS}}}P(P(M)_{J_1}[n])=P(A)\oplus_{T_{\textrm{PS}}}P(P(M)_{J_1}[n])$$

である。$\bigoplus_{T_{\textrm{PS}}}(P(M)_J)_{J=0}^{J_1-1}=A$ と $(P(M)_J)_{J=0}^{J_1-1}=P(A)$ は、
$P$ の連結が元の列に戻ることと A4 の 1 で述べた $P$ の複項枝による。原文は第 2 式しか書かないが、
Lean は第 1 式も使う（A7 の連結形の補題を適用するため）。

**A7. $\textrm{Trans}$ のブロック分解。** [1] の $\textrm{Trans}$ の $P$ 同変性を、$\Sigma_{\textrm{B}}$ 表示ではなく
2 ブロックの連結の形で使う。すなわち $K=A\oplus_{\mathbb{N}^2}N$、$K$ と $N$ が簡約、
$P(K)=P(A)\oplus_{T_{\textrm{PS}}}P(N)$ ならば

$$\textrm{Trans}(A\oplus_{\mathbb{N}^2}N)=\textrm{Trans}(A)+\begin{cases}D_00+\textrm{Trans}(N)&(P(N)_0=((0,0)))\cr  \textrm{Trans}(N)&(\text{その他})\end{cases}$$

である。これを $N=P(M)_{J_1}[n]$ に適用する。前提は A6 の 2 式と、$M[n]\in ST_{\textrm{PS}}$（標準形は
正の基本列で閉じる）から出る簡約性である。

**A8. 補正項の処理。** A7 の $D_00$ 補正の枝でも、補正を付けたほうが小さくならないことを示す。
すなわち $P(P(M)_{J_1}[n])_0=((0,0))$ のとき

$$\textrm{Trans}(P(M)_{J_1}[n])\leq_{\textrm{B}}D_00+\textrm{Trans}(P(M)_{J_1}[n])$$

である。$M[n]\in ST_{\textrm{PS}}$ なので [1] の $\textrm{Trans}$ が順序数項を保つことより
$\textrm{Trans}(M[n])\in OT_{\textrm{B}}$ であり、A7 よりその principal 項の列は
$(\textrm{Trans}(A)\text{ の principal 列})\ \frown\ (D_00)\ \frown\ (\textrm{Trans}(P(M)_{J_1}[n])\text{ の principal 列})$
という形をしている。$OT_{\textrm{B}}$ の条件のひとつは principal 列が広義降順であること、
また広義降順性は終切片に遺伝するので、$(D_00)\frown q$ は広義降順、
ここで $q$ は $\textrm{Trans}(P(M)_{J_1}[n])$ の principal 列である。$D_00$ は最小の principal 項
（$D_vb<_{\textrm{B}}D_00$ は $v<0$ か「$v=0$ かつ $b<_{\textrm{B}}0$」を要するがどちらも不可能）なので、
$q$ の全項が $D_00$ である。したがって principal 列の辞書式順序で $q$ と $(D_00)\frown q$ を比べると、
$q$ が空なら空列 $<$ 非空列、$q=(D_00)\frown q'$ なら先頭が等しく残りが帰納法の仮定で小さいので、
どちらの場合も $q$ は狭義に小さい。補正の枝でないときは等号なので $\leq_{\textrm{B}}$ が成り立つ。

**A9. $+$ と $[]$ の交換。** 原文の「$(t_0+t_1)[m]=t_0+(t_1[m])$」を、$m\in\textrm{dom}(t_1)$ ではなく
$t_1\neq0$ の下で、任意の $z$（自然数項に限らない）について示す。$+$ は principal 項の列の連結であり、
$a[z]$ の再帰も principal 列に対する再帰なので、項をその principal 列と同一視して、列 $a$ についての
帰納法で

$$b\neq()\ \Rightarrow\ (a\frown b)[z]=a+b[z]$$

を示せばよい。$a=()$ のときは $0+x=x$。$a=(p)$ のときは再帰の「2 要素以上の列は先頭 principal を
切り出して残りに足す」枝を 1 段展開するだけ。$a=(p)\frown a'$（$a'\neq()$）のときは同じ枝で $p$ を
切り出し、帰納法の仮定 $(a'\frown b)[z]=a'+b[z]$ を使って
$p+(a'+b[z])=(p+a')+b[z]$ と $+$ の結合則で括り直す。

**A10. 結び。** A2 の第 2 枝と A9 より

$$\textrm{Trans}(M)[m]=\bigl(\textrm{Trans}(A)+\textrm{Trans}(P(M)_{J_1})\bigr)[m]=\textrm{Trans}(A)+\bigl(\textrm{Trans}(P(M)_{J_1})[m]\bigr).$$

A5 と A8 を $\leq_{\textrm{B}}$ の推移性でつなぎ、$+$ の右引数についての単調性
（$x\leq_{\textrm{B}}y$ ならば $t+x\leq_{\textrm{B}}t+y$。狭義版は [1] が持っているので、等号の場合と場合分けする）を使うと

$$\textrm{Trans}(M)[m]=\textrm{Trans}(A)+\bigl(\textrm{Trans}(P(M)_{J_1})[m]\bigr)\leq_{\textrm{B}}\textrm{Trans}(A)+\begin{cases}D_00+\textrm{Trans}(P(M)_{J_1}[n])\cr  \textrm{Trans}(P(M)_{J_1}[n])\end{cases}=\textrm{Trans}(M[n])$$

を得る。最後の等号は A7 である。

#### B. 単項の場合（原文の前半）

$M\in ST_{\textrm{PS}}$、$M$ は単項、$\textrm{Lng}(M)>1$、$\textrm{dom}(\textrm{Trans}(M))=\omega$ とする。
以下つねに $M$ は簡約（[1] の標準形の簡約性）で $M\in T_{\textrm{PS}}$、単項性から $j_1$ は段 $0$ に
（一意な）親 $j_0$ を持ち、簡約かつ単項なので $M_{0,0}=M_{1,0}$ である。

**B0. 条件 (I)-(VI) の網羅。** 条件 (I)、(III)、(V)、(VI) のどれでもないとき、[1] の
「条件 (II) か条件 (IV)」（$M$ が簡約・単項・$\textrm{Lng}(M)>1$ の下で、
(I)(III)(V)(VI) のいずれでもなければ (II) か (IV)）を使う。よって 6 条件で尽くされる。
原文はこの網羅性を [1] に帰しているが、原文の場合分けは先に $t_1=0$ か否かで割るので、
6 条件の網羅は $t_1\neq0$ の枝の中でしか使われない。Lean は先に 6 条件で割り、
2 列（$j_1=1$）かどうかは条件 (I) と (VI) の中で割る。

**B1. 条件 (I)（$M_{1,j_1}=0$ かつ $j_0$ が $M$ 許容）。**

$j_1=1$ のとき。$u=M_{1,0}$ と置く。$M_{1,1}=0$ なので $\textrm{idx}_1(M,1)=0$ であり、
$j_1=1$ の段 $0$ の親は $0$、そこから $M_{0,1}>M_{0,0}\geq0$ なので $(M_{0,1},M_{1,1})\neq(0,0)$。
[1] の 2 列の $\textrm{Trans}$（$\textrm{Lng}(M)=2$ の簡約単項列で $\textrm{Trans}(M)=D_{M_{1,0}}D_{M_{1,1}}0$）より

$$\textrm{Trans}(M)=D_uD_00.$$

[1] の 2 列の基本列の閉形式（$\textrm{Lng}(M)=2$ のとき $M[n]=((M_{0,0}+kd_0,M_{1,0}+kd_1))_{k=0}^{n-1}$、
$d_0,d_1$ は $\textrm{idx}_1(M,1)$ で決まる差分）を使う。いまは $\textrm{idx}_1(M,1)=0$ なので $d_0=d_1=0$、
$M_{0,0}=M_{1,0}=u$ より

$$M[n]=((u,u))^n.$$

$\textrm{Trans}(M)[m]$ は $[]$ の後続枝（$D_v(t_2+D_00)$ の中身のタグが $\{0\}$ なので
$(D_v(t_2+D_00))[m]=(D_vt_2)\times(m+1)$）を $t_2=0$ で使い

$$\textrm{Trans}(M)[m]=(D_u0)\times(m+1).$$

一方 [1] の公差 $(0,0)$ の列の $\textrm{Trans}$ より

$$\textrm{Trans}(((u,u))^{k+1})=\begin{cases}(D_u0)\times k&(u=0)\cr  (D_u0)\times(k+1)&(u>0)\end{cases}$$

なので、$u=0$ のときは $n=m+2$、$u>0$ のときは $n=m+1$ を取れば等号で

$$\textrm{Trans}(M)[m]=\textrm{Trans}(M[n]).$$

$u=0$ の場合が原文の $M=((0,0),(1,0))$ であり、原文の $n=m+2$ と一致する。

$j_1>1$ のとき。[1] の条件 (I) の下での $\textrm{Trans}$ と基本列の交換関係 (1)
（$M$ が簡約・単項、$j_1>1$、条件 (I)、$n\geq1$ で $\textrm{Trans}(M[n])=\textrm{Trans}(M)[n-1]$）に
$n=m+1$ を入れて等号を得る。

**B2. 条件 (II)（$M_{1,j_1}=0$ かつ $j_0$ が $M$ 許容でない）。**

まず $j_1>1$ である。$j_1=1$ なら段 $0$ の親は $j_0=0$ だが、$0$ はつねに $M$ 許容
（非許容性の定義 $\textrm{nextR}(M,1,j-1,j)\land\textrm{nextR}(M,1,j,j+1)$ が $j=0$ では偽）なので
条件 (II) が偽になる。よって C が使えて、$n\geq1$ と $\textrm{Trans}(M[n])=\textrm{Trans}(M)[m]$ を得る。等号。

**B3. 条件 (III)/(IV)（$0<M_{1,j_1}\leq M_{1,j_0}$）。**

段 $1$ で $j_1$ が親を持つかで分ける。持たないときは、[1] の §8.4 の親無し枝の評価
（$M$ 簡約・単項、$j_1>0$、$M_{1,j_1}>0$、段 $1$ の親無しならば
$\textrm{dom}(\textrm{Trans}(M))=T_{M_{1,j_1}-1}$）より $\textrm{dom}(\textrm{Trans}(M))\neq\omega$ となり仮定に反する。

持つときは $j_1>1$ である。$j_1=1$ とすると段 $1$ の親も $0$ しかなく、親子関係から
$M_{1,0}<M_{1,1}$ が出るが、条件 (III)/(IV) は $M_{1,1}\leq M_{1,j_0}=M_{1,0}$ を言うので矛盾する。
これで [1] の条件 (III) か (IV) の下での交換関係 (3)（$n\geq1$ で
$\textrm{Trans}(M)[n-1]<_{\textrm{B}}\textrm{Trans}(M[n+1])$）が使え、$n=m+1$ として

$$\textrm{Trans}(M)[m]<_{\textrm{B}}\textrm{Trans}(M[m+2])$$

を得る。取る添字は $m+2$。

**B4. 条件 (V)（$M_{1,j_0}+1=M_{1,j_1}$ かつ $j_0+1<j_1$）。**

条件そのものから $j_1>1$ である。

$j_0$ が $M$ 許容のとき。[1] の条件 (V) の下での交換関係 (3) の許容枝の第 4 結論
（$n\geq1$ で $\textrm{Trans}(M)[n-1]<_{\textrm{B}}\textrm{Trans}(M[n+1])$）に $n=m+1$ を入れて、添字 $m+2$ を取る。

$j_0$ が $M$ 許容でないとき。[1] の非許容枝の閉形式を使う。まず条件 (V) の下では
$j_1>0$ かつ $t_1\neq0$、さらに $\textrm{Trans}(M[1])$ と $\textrm{Trans}(M)$ が共通の
$\textrm{scb}$ 分解 $s_1,b_1$（$b_1$ は右括弧のみ）を持ち、芯がそれぞれ
$D_{M_{1,j_{-1}}}t_2$ と $\textrm{Trans}$ の定義中の $c_2$ になる。この分解に対し、非許容枝の閉形式は

$$\textrm{Trans}(M[k+1])=s_1\ D_{M_{1,j_{-1}}}\bigl(\textrm{bodyM}(k)\bigr)\ b_1\quad(k\geq0),$$

$$\textrm{Trans}(M)[m']=s_1\ D_{M_{1,j_{-1}}}\bigl(\textrm{bodyO}(m')\bigr)\ b_1\quad(m'\geq1)$$

を与える。ここで $e=M_{1,j_0}$ と置き、種 $c$ の塔を
$W_c(0)=D_ec$、$W_c(k+1)=D_e(t_2+W_c(k))$ とすると

$$\textrm{bodyM}(0)=t_2,\qquad \textrm{bodyM}(j+1)=t_2+W_{t_2}(j+1),\qquad \textrm{bodyO}(m')=t_2+W_0(m').$$

[1] の条件 (V) の下での $t_2$ の非零性より $t_2\neq0$、したがって $0<_{\textrm{B}}t_2$。
塔 $W_c$ は種 $c$ について狭義単調（$k$ についての帰納法。$k=0$ は $D_e$ の中身の比較、
$k+1$ は $+$ の右単調性）なので $W_0(j+1)<_{\textrm{B}}W_{t_2}(j+1)$、$+$ の右単調性で
$\textrm{bodyO}(j+1)<_{\textrm{B}}\textrm{bodyM}(j+1)$。同じ $s_1,b_1$ の中で principal 芯だけを
取り替えた 2 項の比較（部分表現の不等式の延長性）により

$$\textrm{Trans}(M)[j+1]<_{\textrm{B}}\textrm{Trans}(M[j+2])\qquad(j\geq0).$$

$m\geq1$ なら $j=m-1$ として添字 $m+1$ を取ればよい。$m=0$ はこの形では覆えない
（閉形式が $m'\geq1$ でしか使えない）ので、D を使って

$$\textrm{Trans}(M)[0]\leq_{\textrm{B}}\textrm{Trans}(M)[1]<_{\textrm{B}}\textrm{Trans}(M[2])$$

とし、添字 $2$ を取る。D の適用には $\textrm{Trans}(M)\in OT_{\textrm{B}}$（[1] の $\textrm{Trans}$ が
順序数項を保つこと）と $\textrm{dom}(\textrm{Trans}(M))=\omega$ が要る。

**B5. 条件 (VI)（$M_{1,j_0}+1=M_{1,j_1}$ かつ $j_0+1=j_1$）。**

$j_1=1$ のとき。条件 (VI) より $j_0=0$ かつ $M_{1,1}=M_{1,0}+1$。$u=M_{1,0}$ と置く。
[1] の簡約性の条件 (A)（段 $i$ で親を持つ位置では係数が親の $+1$）を段 $0$、位置 $1$ に使うと
$M_{0,1}=M_{0,0}+1=u+1$。よって

$$M=((u,u),(u+1,u+1)).$$

$M_{1,1}>0$ なので $\textrm{idx}_1(M,1)=1$ であり、段 $1$ で $1$ が親を持つ
（持たなければ B3 と同じ親無し枝の評価で $\textrm{dom}(\textrm{Trans}(M))\neq\omega$ となる）。
2 列の $\textrm{Trans}$ より

$$\textrm{Trans}(M)=D_uD_{u+1}0,$$

2 列の基本列の閉形式（いまは $d_0=M_{0,1}-M_{0,0}=1$、$d_1=0$）より

$$M[k+1]=((u+j,u))_{j=0}^{k},$$

[1] の公差 $(1,0)$ の列の $\textrm{Trans}$（$\textrm{Trans}(((u+j,u))_{j=0}^{k})=D_u^{k+1}0$、
ただし $k=0$ かつ $u=0$ のときのみ $0$）を $M[k+2]=((u+j,u))_{j=0}^{k+1}$ に使う。添字は
$k+1\geq1$ なので例外枝には落ちず、$k\geq0$ に対して

$$\textrm{Trans}(M[k+2])=D_u^{k+2}0.$$

$\textrm{Trans}(M)[m]$ は $[]$ の第 1 種の枝で計算する。$b=D_{u+1}0$ は $b\neq0$ かつ
$\textrm{dom}(b)=T_u$ で、外側の指標 $u$ は $u\leq u$ を満たすから

$$(D_ub)[z]=D_u\bigl(b[x_{|z|}]\bigr),\qquad x_0=D_u0,\qquad x_{i+1}=D_u\bigl(b[x_i]\bigr)$$

（訂正 A23 後の読み）である。$b=D_{u+1}0$ は $u+1>0$ なので $b[y]=y$、したがって
$x_i=D_u^{i+1}0$、$\textrm{Trans}(M)[m]=D_u(x_m)=D_u^{m+2}0$。よって $n=m+2$ で

$$\textrm{Trans}(M)[m]=D_u^{m+2}0=\textrm{Trans}(M[m+2]).$$

$u=0$ の場合が原文の $M=((0,0),(1,1))$ である。

$j_1>1$ のとき。[1] の条件 (VI) の下での交換関係 (2)
（$n\geq1$ かつ「$n=1$ かつ $j_0$ が許容」でないとき
$\textrm{Trans}(M[n])=\textrm{Trans}(M)[\,j_0\text{ が許容なら }n-2\text{、さもなくば }n-1\,]$）を使う。
$j_0$ が許容なら $n=m+2$、許容でなければ $n=m+1$ を取ると等号になる。
どちらも「$n=1$ かつ $j_0$ 許容」ではない。

#### C. 条件 (II) の交換関係の供給

[1] の条件 (II) の下での交換関係 (2) は
$\textrm{Trans}(M[n])=\textrm{Trans}(M)[m_n]$、$m_n=(\text{「}P_{\textrm{B}}(t_2)_{J_1}\text{ の左端が }D_{M_{1,j_0}}\text{」なら }n-1\text{、さもなくば }n-2)$
という向きなので、目標の $m$ を与えて $n$ を逆に解く必要がある。
使えるのは条件 (II) のホストの $\textrm{scb}$ 分解の閉形式で、
$s,b$（$b$ は右括弧のみ）、$u,v\in\mathbb{N}$、$t_0,t_1\in T_{\textrm{B}}$、
$\textrm{cnt}\leq1$（$\textrm{cnt}=1$ が上の左端条件にあたる）が取れて

$$\textrm{Trans}(M)=s\ D_u\bigl(t_0+D_v(t_1+D_00)\bigr)\ b,$$

$$\textrm{Trans}(M[m'])=s\ D_u\bigl(t_0+(D_vt_1)\times(\textrm{cnt}+(m'-1))\bigr)\ b\qquad(m'\geq1)$$

となる。一方 [1] の $\textrm{scb}$ 分解と基本列の関係より、上の第 1 式の形の項は

$$\textrm{Trans}(M)[k]=s\ D_u\bigl(t_0+(D_vt_1)\times(k+1)\bigr)\ b$$

を満たす。$\textrm{cnt}+(m'-1)=k+1$ を $m'$ について解くと $m'=k+2-\textrm{cnt}$ で、
$\textrm{cnt}\leq1$ より $m'\geq k+1\geq1$。この $m'$ を $n$ として取れば両辺の平坦化列が一致するので
$\textrm{Trans}(M[n])=\textrm{Trans}(M)[k]$ が出る。閉形式の側の残差（追加ブロックの終切片の値の同定）は
[1] の §8.2 の終切片と $\textrm{Trans}$ の関係から供給される。

#### D. $[]$ の添字単調性

$a\in OT_{\textrm{B}}$ かつ $\textrm{dom}(a)=\omega$ ならば $a[m]<_{\textrm{B}}a[m+1]$、したがって
$m\leq m'$ で $a[m]\leq_{\textrm{B}}a[m']$。前者は $a$ の項の重さに関する強帰納法、後者は $m'$ に関する
帰納法で、Buchholz の基本列の側で無条件に証明されている。B4 の非許容枝が要る形に配線しただけである。
原文にはこの主張は現れない。

## 原文通りに書けなかった理由

- **[Y]** 複項の場合の末尾の等式連鎖は偽で、$\leq_{\textrm{B}}$ かつ添字は $m$ ではない（訂正 B4）

  原文の最後の連鎖は
  $\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+(\textrm{Trans}(P(M)_{J_1})[m])
  =\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}+\textrm{Trans}(P(M)_{J_1}[m])$
  という段を含むが、これは $\textrm{Trans}(P(M)_{J_1})[m]=\textrm{Trans}(P(M)_{J_1}[m])$、
  すなわち直前に示した単項の場合の結論より強い等式を使っている。単項の場合の結論は
  「ある $n\in\mathbb{N}_+$ が存在して $\textrm{Trans}(P(M)_{J_1})[m]\leq_{\textrm{B}}\textrm{Trans}(P(M)_{J_1}[n])$」
  であって、$n=m$ とは限らず等号でもない。実際、条件 (III)/(IV)/(V) では狭義の $<_{\textrm{B}}$ しか出ない。
  Lean は A5 で $n$ をそのまま受け取り、A10 で $+$ の右単調性を使って
  $\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])$ を作る。
  直しは連鎖の 4 行目以降を $\leq_{\textrm{B}}$ と $n$ に置き換えるだけで、補題の主張も下流も変わらない。

- **[Y]** 単項・$t_1=0$ の第 2 例の基本列の値が $D_0$ 1 個ぶん多い

  原文は $\textrm{dom}(D_10)=\Omega_1$ から
  $(D_0D_10)[n]=D_0D_0^nD_0D_00=D_0^{n+3}0$ とするが、正しくは $D_0^{n+2}0$ である。
  $[]$ の第 1 種の枝は $a=D_vb$、$\textrm{dom}(b)=T_u$、$v\leq u$ のとき
  $a[n]=D_v(b[x_n])$、$x_0=D_u0$、$x_{i+1}=D_u(b[x_i])$（訂正 A23 後の読み）である。
  いま $v=u=0$、$b=D_10$ で $b[y]=y$ だから $x_i=D_0^{i+1}0$、
  $a[n]=D_0(x_n)=D_0^{n+2}0$。原文の書き方 $D_0D_0^nD_0D_00$ は $x_n=D_0^{n+2}0$ に相当し、
  $x_0=D_0D_00$ と置いたことになる。訂正前の脚注の読み（$x_i=b[D_ux_{i-1}]$）でも
  $x_i=D_0^{i+1}0$ で結果は $D_0^{n+2}0$ なので、どちらの読みでも $n+3$ にはならない。
  結論 $\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[m+3])$ 自体は
  $D_0^{m+2}0\leq_{\textrm{B}}D_0^{m+3}0$ なので真のままだが、Lean は等号が立つ $n=m+2$ を取る。

- **[Y]** 単項・$t_1=0$ の第 2 例の $\textrm{Trans}(M[n])=D_0^n0$ は $n=1$ で偽

  $M=((0,0),(1,1))$ のとき $M[1]=\textrm{Pred}(M)=((0,0))$ で $\textrm{Trans}(M[1])=0$ だが、
  $D_0^10=D_00\neq0$ である。Lean が使う [1] の公差 $(1,0)$ の列の $\textrm{Trans}$ は
  この例外を明示していて、$((u+j,u))_{j=0}^{k}$ の $\textrm{Trans}$ は
  $k=0$ かつ $u=0$ のときだけ $0$、それ以外は $D_u^{k+1}0$ である。
  原文はこの $1$ 例外を書かずに「任意の $n\in\mathbb{N}$ に対して」と書いている。
  結論では $n\geq3$ しか使わないので下流は変わらない。

- **[Y]** $P(M)_{J_1}\in PT_{\textrm{PS}}\cup ST_{\textrm{PS}}$ の $\cup$ は $\cap$

  直前で示した中間結論は「任意の $M\in PT_{\textrm{PS}}\cap ST_{\textrm{PS}}$ に対して…」であり、
  その次の行でそれを $P(M)_{J_1}$ に適用するのだから、必要なのは
  $P(M)_{J_1}\in PT_{\textrm{PS}}\cap ST_{\textrm{PS}}$ である。$\cup$ では適用できない。
  引かれている 2 つの事実（[1] の $P$ の各成分の非複項性、標準形の単項成分が標準形であること）も
  それぞれ単項性と標準形性を別々に与えるので、結論は $\cap$ になる。
  Lean は A4 の 1 と 2 で標準形性と単項性を別々に立てている。

- **[W]** 2 列（$j_1=1$）で $M_0\neq(0,0)$ の場合が原文のどちらの枝にも入っていない

  原文は $t_1=0$ の枝で $M=((0,0),(1,0))$ と $M=((0,0),(1,1))$ を直接計算し、
  $t_1\neq0$ の枝を [1] の 5 つの交換関係に帰する。しかし $t_1=\textrm{Trans}(\textrm{Pred}(M))$ が
  $0$ になるのは $\textrm{Lng}(M)=2$ かつ $M_0=(0,0)$ のときだけである。
  一方 [1] の 5 つの交換関係はいずれも $j_1>1$ を仮定する
  （条件 (V) は $j_0+1<j_1$ から $j_1>1$ が自動、他の 4 つは仮定として置かれている）。
  したがって $\textrm{Lng}(M)=2$ かつ $M_0=(u,u)$、$u\geq1$ の場合はどちらの枝にも入らない。
  この場合は空虚ではない。たとえば $M=((1,1),(2,2))\in ST_{\textrm{PS}}$ は単項で
  $\textrm{Trans}(M)=D_1D_20$、$\textrm{dom}(\textrm{Trans}(M))=\omega$、$t_1=D_10\neq0$ であり、
  条件 (VI) を満たす。Lean は B1 と B5 の $j_1=1$ 枝で一般の $u$ について直接計算しており、
  $u=0$ に固定した場合が原文の 2 例にあたる。埋めるのに要るのは
  2 列の $\textrm{Trans}$、2 列の基本列の閉形式、公差 $(0,0)$ と $(1,0)$ の列の $\textrm{Trans}$、
  および $[]$ の後続枝と第 1 種の枝の計算だけで、いずれも [1] にある。

- **[W]** [1] の交換関係を引くための側条件を原文が確かめていない

  原文は 6 条件をまとめて 1 行で処理するが、そこで引く命題は追加の仮定を持ち、
  場合分けの網羅にも一歩要る。
  第一に条件 (I)、(II)、(III)/(IV)、(VI) の交換関係はいずれも $j_1>1$ を要求する。
  条件 (II) では $j_1=1$ が起こり得ないこと（$j_1=1$ なら $j_0=0$ で、$0$ はつねに $M$ 許容
  なので条件 (II) が偽）を、条件 (III)/(IV) では $j_1=1$ が段 $1$ の親の存在と
  $M_{1,j_1}\leq M_{1,j_0}$ から矛盾することを、Lean は別に示している（B2、B3）。
  条件 (I) と (VI) では $j_1=1$ が実際に起こるので、そこは前項の直接計算になる。
  第二に [1] の条件 (III) か (IV) の下での交換関係は「$j_1$ が段 $1$ に親を持つこと」を
  仮定する。この仮定は本質的で、親を持たない脚では結論が偽になる。Lean は
  [1] の親無し枝の評価から $\textrm{dom}(\textrm{Trans}(M))=T_{M_{1,j_1}-1}\neq\omega$ を出し、
  本補題の仮定 $\textrm{dom}(\textrm{Trans}(M))=\omega$ の下でその脚が起こらないことを示す（B3）。
  同じ議論は条件 (VI) の $j_1=1$ 枝でも使われる（B5）。
  第三に、原文の「$M$ が単項」「$M$ が複項」の二分は $M$ が零項でないことを前提とするが、
  それは $j_1>0$ から出る。Lean は A1 でこの一歩を明示している。

- **[W]** 条件 (V) の非許容枝では $m=0$ が [1] の交換関係で覆えない（訂正 B5）

  [1] の条件 (V) の下での交換関係 (3) は
  $\textrm{Trans}(M)[m_n]\leq_{\textrm{B}}\textrm{Trans}(M[n+1])$、
  $m_n=(j_0$ が $M$ 許容なら $n-1$、さもなくば $n)$ の形である。
  許容枝では $n=1$ で $m_n=0$ になるので $m=0$ も覆えるが、非許容枝では $n\geq1$ に対し
  $m_n=n\geq1$ なので $m=0$ に対応する $n$ が無い。Lean は D（$\textrm{dom}(a)=\omega$ なる
  $a\in OT_{\textrm{B}}$ について $a[\cdot]$ が添字に関して広義単調）を経由して
  $\textrm{Trans}(M)[0]\leq_{\textrm{B}}\textrm{Trans}(M)[1]<_{\textrm{B}}\textrm{Trans}(M[2])$ とする（B4）。
  他の 4 条件では $m=0$ も覆える（条件 (I) は $n=1$、条件 (II) は $n=1$ か $2$、
  条件 (III)/(IV) は $n=2$、条件 (VI) は $n=1$ か $2$）。

- **[W]** 複項の場合の $\Sigma_{\textrm{B}}$ 表示は先頭 $P$ 成分の非零項性を要する

  原文は [1] の $\textrm{Trans}$ の $(\textrm{IncrFirst},\textrm{Red})$ 不変 $P$ 同変性 (2) を
  $\textrm{Trans}(X)=\Sigma_{\textrm{B}}(P(X)_J^+)_{J=0}^{\textrm{Lng}(P(X))-1}$ の形で
  $X=M$ と $X=M[n]$ と $X=P(M)_{J_1}[n]$ に使う。しかしこの表示は $P(X)_0$ が零項のとき偽である
  （[1] の $\textrm{Trans}$ の再帰的定義は先頭の零項ブロックを $0$ に吸収するが、$\Sigma_{\textrm{B}}$ 表示は
  そこに $D_00$ を残す。訂正 A16）。原文が確かめているのは
  「$P(M)_{J_1}$ と $P(M)_{J_1}[n]$ が零項でない」ことであって、
  $P(M)_0$ や $P(P(M)_{J_1}[n])_0$ が零項でないことではない。
  Lean は $\Sigma_{\textrm{B}}$ 表示を使わず、$\textrm{Trans}$ の複項枝（A2）と、
  先頭ブロックが $((0,0))$ のときだけ $D_00$ を補う連結形（A7）で置き換える。
  補正が付く枝が実際に排除できるかは判定していないので、そのぶん A8 で
  $\textrm{Trans}(P(M)_{J_1}[n])\leq_{\textrm{B}}D_00+\textrm{Trans}(P(M)_{J_1}[n])$ を別に示す必要があり、
  そこで $\textrm{Trans}(M[n])\in OT_{\textrm{B}}$（[1] の $\textrm{Trans}$ が順序数項を保つこと）と
  principal 列の広義降順性を使う。原文にはこの一段が無い。
  なお Lean は連結形を使うため、[1] の $P$ と基本列の関係 (2) の 2 つの結論のうち、
  原文が引かない $M[n]=A\oplus_{\mathbb{N}^2}P(M)_{J_1}[n]$ のほうも使う。

- **[R]** $(t_0+t_1)[m]=t_0+(t_1[m])$ に $m\in\textrm{dom}(t_1)$ は要らない

  原文はこの等式を $m\in\textrm{dom}(t_1)$ の下で述べるが、Lean が示すのは
  $t_1\neq0$ ならば任意の $z$（自然数項に限らない）について $(t_0+t_1)[z]=t_0+(t_1[z])$、
  である。$+$ が principal 項の列の連結で、$a[z]$ の再帰が列の先頭から principal を
  切り出す形をしているので、$m\in\textrm{dom}(t_1)$ は使わずに済む（A9）。
  $\textrm{dom}(t_0+t_1)=\textrm{dom}(t_1)$ のほうも $t_1\neq0$ だけで出る。

- **[R]** 「任意の $n\in\mathbb{N}_+$ に対して $M[n]$ は複項である」は使わない

  原文はこの一行を [1] の $P$ の各成分の非複項性 (2) から出すが、Lean の複項の場合の証明は
  $M[n]$ の複項性をどこでも使わない。$\textrm{Trans}(M[n])$ の評価は A6 の 2 つの等式と
  A7 の連結形だけで済み、そこに必要なのは $M[n]$ と $P(M)_{J_1}[n]$ の簡約性と
  $P(M[n])=P(A)\oplus_{T_{\textrm{PS}}}P(P(M)_{J_1}[n])$ である。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| 本補題 | `fseq_relation` | `lean/Bijectivity/16-fseq-relation.lean` |
| 単項の場合（原文の中間結論） | `MonoFseqRel` | `lean/Bijectivity/16a-fseq-addBT.lean` |
| A（複項の場合の帰着） | `fseq_relation_of_mono` | 同上 |
| B（単項の場合の証明） | `mono_fseq_rel` | `lean/Bijectivity/16b-mono-fseq-rel.lean` |
| C（条件 (II) の交換関係の逆向き） | `CondIIFseqRel` / `condII_fseq_rel_holds` | `lean/Bijectivity/16b-mono-fseq-rel.lean` / `lean/Bijectivity/16d-condII-fseq-rel.lean` |
| D（$[]$ の添字単調性） | `OperBNumMono` / `operB_numBT_mono_holds` | `lean/Bijectivity/16b-mono-fseq-rel.lean` / `lean/Bijectivity/16c-operB-mono.lean` |
| $a[m]<_{\textrm{B}}a[m+1]$ | `operB_numBT_step` | `lean/Bijectivity/16c-operB-mono.lean` |
| $\textrm{Lng}(M)$ | `PSS.Lng` | `lean/PSS/Defs.lean` |
| $M_{i,j}$ | `PSS.entry` | 同上 |
| $T_{\textrm{PS}}$ | `PSS.TPS` | 同上 |
| $\textrm{Pred}(M)$ | `PSS.Pred` | 同上 |
| $M[n]$ | `PSS.oper` | 同上 |
| $\textrm{idx}_1(M,j_1)$ | `PSS.idx1` | 同上 |
| 段 $i$ の親 | `PSS.parent` / `PSS.hasParent` | 同上 |
| 零項・単項・複項 | `PSS.zeroT` / `PSS.monoT` / `PSS.multiT` | `lean/PSS/Mono.lean` |
| $P(M)$、$\textrm{Pcut}(M)$ | `PSS.P`、`PSS.Pcut` | 同上 |
| $RT_{\textrm{PS}}$ | `PSS.RTPS` | `lean/PSS/Red.lean` |
| 簡約性の条件 (A) | `PSS.RedCondA` | 同上 |
| $ST_{\textrm{PS}}$、$S_kT_{\textrm{PS}}$ | `PSS.STPS`、`PSS.SkTPS` | `lean/PSS/Standard.lean` |
| $M$ 許容 | `PSS.adm` | `lean/PSS/Adm.lean` |
| $j_{-1}=\textrm{Adm}_M(j_0)$ | `PSS.Adm` | 同上 |
| $\textrm{Trans}(M)$ | `PSS.Trans` | `lean/PSS/Trans.lean` |
| 条件 (I)-(VI) | `PSS.transCondI`-`PSS.transCondVI` | 同上 |
| $j_1$、$j_0$、$j_{-1}$、$t_1$、$t_2$、$c_2$ | `PSS.transJ1`、`transJ0`、`transJm1`、`transT1`、`transT2`、`transC2` | 同上 |
| $\textrm{scb}$ 分解、第 1 種 | `PSS.scb_decomp`、`PSS.scb_kind1` | `lean/PSS/Scb.lean` |
| $D_v a$ | `PSS.Dprin` | `lean/Buchholz-1986/Buchholz-1986-2.1.lean` |
| $<_{\textrm{B}}$、$\leq_{\textrm{B}}$ | `PSS.lessBT`、`PSS.leBT` | 同上 |
| $\Sigma_{\textrm{B}}$、$P_{\textrm{B}}$ | `PSS.SigmaB`、`PSS.PB` | 同上 |
| $T_{\textrm{B}}$ | `PSS.T_B` | `lean/Buchholz-1986/Buchholz-1986-2.2.lean` |
| principal 列の広義降順性 | `PSS.descP` | 同上 |
| $OT_{\textrm{B}}$ | `PSS.OT_B` | 同上 |
| $t_0+t_1$ | `PSS.addBT` | `lean/Buchholz-1986/Buchholz-1986-3.2.lean` |
| $a\times n$ | `PSS.multBT` | 同上 |
| 自然数項 $m$ | `PSS.numBT` | 同上 |
| $\textrm{dom}$ のタグ | `PSS.domTag` | 同上 |
| $a[z]$ | `PSS.operB` | `lean/Buchholz-rel-ord/Buchholz-rel-ord-6.lean` |
| $x_i$（訂正 A23 後） | `PSS.xseq` | 同上 |
| $\textrm{dom}(t)=\omega$ | `Bijectivity.domIsOmega` | `lean/Bijectivity/Cited.lean` |
| A0（$\textrm{dom}=\omega$ ならば $\textrm{Lng}>1$） | `Bijectivity.one_lt_lng_of_domIsOmega` | `lean/Bijectivity/15-successor-fseq.lean` |
| $\textrm{dom}(t+u)=\textrm{dom}(u)$ | `Bijectivity.domTag_addBT_right` | 同上 |
| 簡約な零項は $((0,0))$ | `Bijectivity.eq_zero_singleton_of_zeroT` | 同上 |
| $(t+u)[z]=t+(u[z])$ | `Bijectivity.operB_addBT_right` | `lean/Bijectivity/16a-fseq-addBT.lean` |
| A9 の列版 | `Bijectivity.bOperCore_list_append_fr` | 同上 |
| A8（$D_00$ 補正で小さくならない） | `Bijectivity.lessBT_addBT_D00_left` | 同上 |
| A8 の「後続はすべて $D_00$」 | `Bijectivity.descP_cons_all_D00_fr` | 同上 |
| 広義降順性の終切片への遺伝 | `Bijectivity.descP_suffix_fr` | 同上 |
| $+$ の右単調性（広義） | `Bijectivity.leBT_addBT_right_fr` | 同上 |
| $+$ の右単調性（狭義） | `PSS.addBT_lt_right_bf` | `lean/Buchholz-1986/Buchholz-1986-3.2-descent.lean` |
| $<_{\textrm{B}}$ の推移性 | `PSS.lessBT_linear_trans` | `lean/Buchholz-1986/Buchholz-1986-2.1-order.lean` |
| $ST_{\textrm{PS}}$ から $S_kT_{\textrm{PS}}$ へ | `Bijectivity.STPS_SkTPS_fr` | `lean/Bijectivity/16a-fseq-addBT.lean` |
| [1] 標準形の簡約性 | `PSS.STPS_RTPS` | `lean/6/6.7-standard-reduced.lean` |
| [1] 標準形の $P$ 成分が標準形 | `PSS.SkTPS_P_components`、`PSS.SkTPS_STPS` | `lean/6/6.7-standard-P-components.lean` |
| [1] $P$ の各成分の非複項性 | `PSS.P_components_nonmulti` | `lean/6/6.2-P-components-nonmulti.lean` |
| $P$ の連結は元の列 | `PSS.P_concat` | `lean/6/6.2-P-fseq.lean` |
| $P$ の複項枝（最終成分と残り） | `PSS.P_last_multi` | 同上 |
| 最終 $P$ 成分の位置 | `PSS.trans_multi_last_component` | `lean/7/7.3-Trans-welldefined.lean` |
| [1] $\textrm{Trans}$ の複項枝 | `PSS.Trans_Mark_multi_equations` | 同上 |
| [1] $\textrm{Trans}$ が零項性を保つこと | `PSS.Trans_preserves_zeroT` | `lean/7/7.3-Trans-preserves-zeroT.lean` |
| [1] 2 列の $\textrm{Trans}$ | `PSS.two_column_Trans` | `lean/7/7.3-two-column.lean` |
| 単項なら段 $0$ に親を持つ | `PSS.mono_hasParent_row0` | `lean/6/6.6-P-condAB.lean` |
| 簡約単項の先頭は $M_{0,0}=M_{1,0}$ | `PSS.RTPS_mono_head_eq` | `lean/6/6.6-reduced-leftend.lean` |
| 簡約性 $\Rightarrow$ 条件 (A)(B) | `PSS.RTPS_condAB` | `lean/6/6.6-reduced-iff-condAB.lean` |
| $0$ はつねに $M$ 許容 | `PSS.adm_zero` | `lean/6/6.3-admof-slice.lean` |
| 部分表現の不等式の延長性 | `PSS.scbext_lessBT` | `lean/7/7.3-Pred-Trans-descend.lean` |
| $[]$ の第 1 種の枝 | `PSS.operB_dprin_kind1` | `lean/7/7.2-scb-fseq.lean` |
| [1] $\textrm{scb}$ 分解と基本列の関係 | `PSS.scb_fseq_decomp` | 同上 |
| $[]$ の後続枝 | `PSS.operB_succ_body_ci` | `lean/8/8.1-Trans-fseq-condI.lean` |
| [1] 条件 (I) の交換関係 (1) | `PSS.condI_exchange1` | 同上 |
| [1] 条件 (III)/(IV) の交換関係 (3) | `PSS.Trans_oper_exchange` | `lean/8/8.4-Trans-fseq-condIII-IV.lean` |
| 段 $1$ の親無し枝の $\textrm{dom}$ | `PSS.Exch84_noParent_domTag_holds` | `lean/8/8.4-exch84-noparent.lean` |
| [1] 条件 (V) の交換関係 (3)（許容枝） | `PSS.Trans_oper_exchange_condV_adm_uncond_vc` | `lean/8/8.5-Trans-fseq-condV-close.lean` |
| 条件 (V) 非許容枝の閉形式 | `PSS.nf3x_vc`（`PSS.ExchV_nf3x`） | 同上 / `lean/8/8.5-Trans-fseq-condV.lean` |
| 条件 (V) の $j_1>0$ と $t_1\neq0$ | `PSS.condV_setup_holds` | `lean/8/8.5-exchV-props.lean` |
| 条件 (V) の $\textrm{scb}$ 分解 | `PSS.fseq_condV_holds` | 同上 |
| 条件 (V) の $t_2\neq0$ | `PSS.t2_nonzero_condV_holds` | 同上 |
| 塔 $W_c$ | `PSS.s85b_W`、`PSS.e5x_bodyM`、`PSS.e5x_bodyO` | `lean/8/8.5-Trans-fseq-condV.lean` |
| 塔の種についての単調性 | `Bijectivity.s85b_W_mono_seed_fr` | `lean/Bijectivity/16b-mono-fseq-rel.lean` |
| [1] 条件 (VI) の交換関係 (2) | `PSS.p_8_6_Trans_fseq_condVI_uncond` | `lean/8/8.6-Trans-fseq-condVI-close.lean` |
| [1] 条件 (II) か条件 (IV) | `PSS.condII_or_condIV` | `lean/8/8.2-subexpr-adm0-ctx.lean` |
| 条件 (II) の $\textrm{scb}$ 閉形式 | `PSS.condII_masterCF_exact_of_tailval` | `lean/8/8.3-condII-masterCF.lean` |
| [1] §8.2 終切片と $\textrm{Trans}$ の関係 | `PSS.condIIIVterminalSlice_holds` | `lean/8/8.2-condIIIV-close.lean` |
| [1] $P$ と基本列の関係 (2) | `PSS.FseqDesc_m_6_2_P_oper_2_holds` | `lean/8/8.7-fseq-descend-props.lean` |
| A7（$\textrm{Trans}$ のブロック分解） | `PSS.f7x_Trans_append_Pblocks_holds` | `lean/8/8.7-descend-last2.lean` |
| 2 列の基本列の閉形式 | `PSS.oper_len2_fd` | `lean/8/8.7-fseq-descend.lean` |
| [1] 公差 $(0,0)$ の列の $\textrm{Trans}$ | `PSS.const00_Trans` | `lean/8/8.7-const00-Trans.lean` |
| [1] 公差 $(1,0)$ の列の $\textrm{Trans}$ | `PSS.FseqDesc_m_8_6_rcseq_Trans_holds` | `lean/8/8.7-fseq-descend-props2.lean` |
| [1] $\textrm{Trans}$ が順序数項を保つこと | `PSS.Trans_STPS_OT_B` | `lean/8/8.7-termination.lean` |
| D の中身（$a[m]<_{\textrm{B}}a[m+1]$ と広義版） | `PSS.y4_N_mono`、`PSS.y4_N_mono_le` | `lean/OTB-well-founded-syntactic/OTB-well-founded-syntactic-cofinality.lean` |

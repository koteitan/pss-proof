[← back](README.md)

# 15: 命題 (後続な項の基本列)

## 原文

### 命題

命題 (後続な項の基本列)（原文の命題に通し番号は付いていない）

任意の$`M\in RT_{\textrm{PS}}`$と$`n\in\mathbb{N}_+`$に対して、$`\textrm{dom}(\textrm{Trans}(M))=1`$ならば$`(\textrm{Trans}(M),\textrm{Trans}(M[n]))=(D_00,0)`$または$`\textrm{Trans}(M[n])+D_00=\textrm{Trans}(M)`$である。

### 証明

証明

$`T_{\textrm{B}}`$上の$`\textrm{dom}`$の定義より、$`\textrm{dom}(\textrm{Trans}(M))=1`$ならば$`\textrm{Trans}(M)=D_00`$またはある$`s\in\Sigma^{\lt\omega}`$が存在して$`\underline{(}s\underline{,}D_00\underline{)}`$である。  
$`\textrm{Trans}(M)=D_00`$とする。  
　[1]の$`\textrm{Trans}`$と非可算基数の関係より$`M=((0,0),(0,0))`$である。  
　$`(\textrm{Trans}(M),\textrm{Trans}(M[n]))=(D_00,\textrm{Trans}(((0,0))))=(D_00,0)`$である。  
ある$`s\in\Sigma^{\lt\omega}`$が存在して$`\underline{(}s\underline{,}D_00\underline{)}`$であるとする。  
　$`\textrm{Trans}(M)=\underline{(}s\underline{,}D_00\underline{)}`$は複項である。  
　$`P(M)_0`$が零項でありかつ$`\textrm{Lng}(P(M))=2`$であるとすると、[1]の$`\textrm{Trans}`$が零項性を保つことより$`\textrm{Trans}(M)=\textrm{Trans}(P(M)_0)+\textrm{Trans}(P(M)_1)=0+\textrm{Trans}(P(M)_1)=\textrm{Trans}(P(M)_1)`$であり、[1]の$`P`$の各成分の非複項性、$`\textrm{Trans}`$が零項性を保つこと及び$`\textrm{Trans}`$が単項性を保つことより$`\textrm{Trans}(M)=0`$または$`\textrm{Trans}(M)`$は単項であるが、これは上と矛盾するから$`P(M)_0`$が零項でないか$`\textrm{Lng}(P(M))\neq2`$である。  
　$`\textrm{Trans}(M)=\underline{(}s\underline{,}D_00\underline{)}`$は複項であり、かつ$`P(M)_0`$が零項でないか$`\textrm{Lng}(P(M))\neq2`$であるから、[1]の$`\textrm{Trans}`$が単項性を保つことより$`M`$は複項である。  
　$`\textrm{Trans}`$の定義中の記号を$`M`$に対して定義する。  
　[1]の$`P`$の各成分の非複項性、$`\textrm{Trans}`$が零項性を保つこと、$`\textrm{Trans}`$が単項性を保つこと、$`\textrm{Trans}`$の定義及び仮定より$`P(M)_{J_1}`$は単項であり、かつ$`P(M)_{J_1}=((0,0))`$または$`\textrm{Trans}(P(M)_{J_1})=D_00`$である。  
　$`\textrm{Trans}(P(M)_{J_1})=D_00`$とすると、[1]の$`\textrm{Trans}`$と非可算基数の関係より$`P(M)_{J_1}=((0,0),(0,0))`$であり、よって$`P(M)_{J_1}`$は複項であるが、これは上と矛盾するため$`P(M)_{J_1}=((0,0))`$である。  
　[1]の$`P`$の加法性より$`P(M)=P(\textrm{Pred}(M))\oplus_{T_{\textrm{PS}}}(((0,0)))`$である。  
　$`P`$の定義より$`M=\textrm{Pred}(M)\oplus_{\mathbb{N}^2}((0,0))`$である。  
　上より$`\textrm{Trans}(M)=\textrm{Trans}((M_j)_{j_0}^{j_0-1})+D_00=\textrm{Trans}((M_j)_{j_0}^{j_1-1})+D_00=\textrm{Trans}(\textrm{Pred}(M))+D_00=\textrm{Trans}(M[n])+D_00`$である。  
よって$`(\textrm{Trans}(M),\textrm{Trans}(M[n]))=(D_00,0)`$または$`\textrm{Trans}(M[n])+D_00=\textrm{Trans}(M)`$である。□

## Lean

### Lean での命題

先に Lean 側の定義を書く。

$`T_{\textrm{B}}`$ の項は主項（$`D_va`$ の形のもの）の有限列として表す。空列が $`0`$、長さ 1 の列 $`(D_va)`$ が $`D_va`$、和 $`t+u`$ は列の連結である。順序 $`\lt_{\textrm{B}}`$ は主項列の辞書式順序で、主項どうしは $`D_ua\lt_{\textrm{B}}D_vb\iff u\lt v\lor(u=v\land a\lt_{\textrm{B}}b)`$、列としては空列が最小である。$`P_{\textrm{B}}(t)`$ は $`t`$ の主項成分の列である。

$`\textrm{dom}`$ は集合そのものではなく 4 値のタグ

```math
\varnothing,\qquad \lbrace 0\rbrace,\qquad \mathbb{N},\qquad T_v
```

（それぞれ原文の $`\textrm{dom}=0,\ 1,\ \omega,\ \Omega_{v+1}`$ に対応する）として計算する。タグの定義は主項列の長さで分かれ、空列は $`\varnothing`$、長さ $`\geq2`$ の列は末尾の主項のタグ、単一の主項 $`D_vb`$ については

```math
\textrm{dom}(D_vb)=
\begin{cases}
\lbrace 0\rbrace & b=0,\ v=0\cr
\mathbb{N} & b=0,\ v=\infty\cr
T_{v-1} & b=0,\ 0\lt v\lt\infty\cr
\mathbb{N} & b\neq0,\ \textrm{dom}(b)=\lbrace 0\rbrace\cr
\mathbb{N} & b\neq0,\ \textrm{dom}(b)=T_u,\ v\leq u\cr
T_u & b\neq0,\ \textrm{dom}(b)=T_u,\ v\gt u\cr
\textrm{dom}(b) & \text{その他}
\end{cases}
```

である。原文の $`\textrm{dom}(t)=1`$ は「$`t`$ のタグが $`\lbrace 0\rbrace`$」と読む。原文の $`\textrm{dom}(t)=\omega`$ は「タグが $`\mathbb{N}`$」である。

ペア列の側は $`\textrm{Lng}(M)`$ が長さ、$`M_{i,j}`$ が成分（範囲外は $`0`$）、$`\textrm{Pred}(M)`$ は末尾 1 列を落とす操作（$`\textrm{Lng}(M)\leq1`$ なら恒等）、$`(M_j)_{j=a}^{b}`$ は閉区間の切片、$`M[n]`$ は原文どおりの基本列である。$`RT_{\textrm{PS}}`$ は簡約なペア列（空でなく $`\textrm{Red}(M)=M`$）。$`\textrm{Trans}`$ は燃料付きの相互再帰で定義され、簡約な入力に対しては燃料 $`\textrm{Lng}(M)`$ で値が確定する。

命題は次の形である。

$`M\in RT_{\textrm{PS}}`$、$`n\in\mathbb{N}`$、$`1\leq n`$ とする。$`\textrm{dom}(\textrm{Trans}(M))=1`$ ならば

```math
\bigl(\textrm{Trans}(M)=D_00\ \land\ \textrm{Trans}(M[n])=0\bigr)\ \lor\ \textrm{Trans}(M[n])+D_00=\textrm{Trans}(M)
```

である。原文の対の等式 $`(\textrm{Trans}(M),\textrm{Trans}(M[n]))=(D_00,0)`$ は成分ごとの連言に開いてある。

### Lean での証明

証明は「前半」（$`\textrm{dom}(\textrm{Trans}(M))=1`$ から $`M`$ の最終列が $`(0,0)`$ であることを出す部分）と「後半」（そこから結論を出す部分）に分かれる。後半は原文と同じ道具で同じ筋を通る。前半は原文と筋が違う。

#### 記法についての補題

**補題A**（単一主項のタグ）: $`\textrm{dom}(D_vb)=\lbrace 0\rbrace\iff(v=0\land b=0)`$。

証明は上のタグの定義の場合分けをそのまま追う。$`b=0`$ のときは $`v=0`$ なら $`\lbrace 0\rbrace`$、$`v=\infty`$ なら $`\mathbb{N}`$、$`0\lt v\lt\infty`$ なら $`T_{v-1}`$ で、後 2 者は $`\lbrace 0\rbrace`$ でない。$`b\neq0`$ のときは $`\textrm{dom}(b)`$ が $`\lbrace 0\rbrace`$ なら $`\mathbb{N}`$、$`T_u`$ なら $`v\leq u`$ に応じて $`\mathbb{N}`$ か $`T_u`$、$`\varnothing`$ か $`\mathbb{N}`$ ならそのまま、で、どの枝も $`\lbrace 0\rbrace`$ を返さない。

**補題B**（タグは右側で決まる）: 主項列 $`as,bs`$ について $`bs\neq()`$ ならば $`\textrm{dom}(as\oplus bs)=\textrm{dom}(bs)`$。$`as`$ の長さに関する帰納で、$`as=()`$ は自明、$`as=(a)\oplus as'`$ では $`as'\oplus bs\neq()`$ だから $`(a)\oplus as'\oplus bs`$ は長さ $`\geq2`$ で、タグの定義の第 3 の場合により $`\textrm{dom}(as'\oplus bs)`$ に落ち、帰納法の仮定で $`\textrm{dom}(bs)`$ になる。これを項の言葉に直すと、$`u\neq0`$ ならば $`\textrm{dom}(t+u)=\textrm{dom}(u)`$ である。

**補題D**（$`D_00`$ の下は $`0`$ だけ）: $`t\lt_{\textrm{B}}D_00`$ ならば $`t=0`$。$`t`$ の主項列が空なら $`t=0`$。空でなく先頭が $`D_wc`$ だとすると、列の辞書式比較より $`D_wc\lt_{\textrm{B}}D_00`$ か、$`D_wc=D_00`$ かつ残りの列 $`\lt_{\textrm{B}}()`$ である。前者は $`w\lt 0`$ か（$`w=0`$ かつ $`c\lt_{\textrm{B}}0`$）だが、$`w\lt 0`$ は偽、$`c\lt_{\textrm{B}}0`$ も（空列が最小なので）偽。後者の「残りの列 $`\lt_{\textrm{B}}`$ 空列」も偽。よって矛盾。

#### 前半

**補題C**（1 列の場合）: $`M\in RT_{\textrm{PS}}`$ かつ $`\textrm{Lng}(M)=1`$ ならば $`\textrm{dom}(\textrm{Trans}(M))\neq1`$。

$`M=(p)`$ と書く。$`M`$ が簡約なので $`\textrm{Red}(M)=M`$ である。

- $`p_1=0`$ のとき。$`\textrm{Lng}(M)=1`$ かつ $`M_{1,0}=0`$ なので $`M`$ は零項、よって $`\textrm{Red}(M)=((0,0))`$、簡約性と合わせて $`M=((0,0))`$ である。[1] の $`\textrm{Trans}`$ が零項性を保つことより $`\textrm{Trans}(((0,0)))=0`$ で、$`\textrm{dom}(0)=\varnothing\neq\lbrace 0\rbrace`$。
- $`p_1\neq0`$ のとき。$`p\neq(0,0)`$ である。簡約入力では $`\textrm{Trans}`$ は燃料 $`\textrm{Lng}(M)`$ で確定し、その定義の $`j_1=0`$ の枝は「$`M_0=(0,0)`$ なら $`0`$、さもなくば $`D_{M_{1,0}}0`$」なので $`\textrm{Trans}(M)=D_{p_1}0`$。補題A よりタグが $`\lbrace 0\rbrace`$ なら $`p_1=0`$ となり矛盾。

**補題E**（単項で 2 列以上の場合）: $`M\in RT_{\textrm{PS}}`$、$`M`$ が単項、$`\textrm{Lng}(M)\gt 1`$ ならば $`\textrm{dom}(\textrm{Trans}(M))\neq1`$。

- $`\textrm{Trans}(M)=0`$ なら $`\textrm{dom}(0)=\varnothing\neq\lbrace 0\rbrace`$。
- $`\textrm{Trans}(M)\neq0`$ とする。[1] の $`\textrm{Trans}`$ が単項性を保つこと（簡約単項列の非零な $`\textrm{Trans}`$ は単一の主項）より $`\textrm{Trans}(M)=D_vb`$ と書ける。$`\textrm{dom}(\textrm{Trans}(M))=\lbrace 0\rbrace`$ を仮定すると補題A から $`v=0`$、$`b=0`$、すなわち $`\textrm{Trans}(M)=D_00`$ である。ここで $`\textrm{Trans}(\textrm{Pred}(M))`$ で場合分けする。
  - $`\textrm{Trans}(\textrm{Pred}(M))=0`$ のとき。$`\textrm{Pred}(M)`$ は簡約（[1] の $`\textrm{Pred}`$ が簡約性を保つこと）なので $`T_{\textrm{PS}}`$ に属し、$`\textrm{Trans}`$ が零項性を保つことの逆向きから $`\textrm{Pred}(M)`$ は零項、よって $`\textrm{Lng}(\textrm{Pred}(M))=1`$。$`\textrm{Lng}(\textrm{Pred}(M))=\textrm{Lng}(M)-1`$ だから $`\textrm{Lng}(M)=2`$ である。2 列の簡約単項列の $`\textrm{Trans}`$ は $`D_{M_{1,0}}(D_{M_{1,1}}0)`$（[1] の 2 列の場合の明示式）だから、$`D_00=D_{M_{1,0}}(D_{M_{1,1}}0)`$ となり、内側を比べると $`0=D_{M_{1,1}}0`$ で矛盾。
  - $`\textrm{Trans}(\textrm{Pred}(M))\neq0`$ のとき。[1] の $`\textrm{Pred}`$ による $`\textrm{Trans}`$ の狭義降下（簡約で $`\textrm{Lng}(M)\gt 1`$ なら $`\textrm{Trans}(\textrm{Pred}(M))\lt_{\textrm{B}}\textrm{Trans}(M)`$）より $`\textrm{Trans}(\textrm{Pred}(M))\lt_{\textrm{B}}D_00`$、補題D より $`\textrm{Trans}(\textrm{Pred}(M))=0`$ となり矛盾。

**補題F**（簡約な零項）: $`N\in RT_{\textrm{PS}}`$ が零項ならば $`N=((0,0))`$。$`\textrm{Red}(N)=((0,0))`$ と $`\textrm{Red}(N)=N`$ から出る。

**補題G**（非複項の $`P`$）: $`N\in T_{\textrm{PS}}`$ が複項でないならば $`P(N)=(N)`$。[1] の「複項 $`\iff\textrm{Lng}(P(N))\gt 1`$」より $`\textrm{Lng}(P(N))\leq1`$、$`P(N)\neq()`$ と合わせて $`\textrm{Lng}(P(N))=1`$、$`P(N)=(X)`$ と書ける。$`P`$ の成分の連結が $`N`$ に戻ることから $`X=N`$。

**主補題H**（前半の本体）: $`M\in RT_{\textrm{PS}}`$ かつ $`\textrm{dom}(\textrm{Trans}(M))=1`$ ならば $`1\lt\textrm{Lng}(M)`$ かつ $`M_{0,\textrm{Lng}(M)-1}=M_{1,\textrm{Lng}(M)-1}=0`$。

1. $`M\in T_{\textrm{PS}}`$ より $`\textrm{Lng}(M)\geq1`$。補題C より $`\textrm{Lng}(M)=1`$ は仮定に反するので $`1\lt\textrm{Lng}(M)`$。
2. $`\textrm{Lng}(M)\neq1`$ なので $`M`$ は零項でない。補題E より $`M`$ は単項でない。よって $`M`$ は複項である。
3. [1] の複項列の $`P`$ の末尾成分（$`M`$ 複項、$`\textrm{Lng}(M)\gt 1`$）より、$`P(M)`$ の末尾成分は $`N=(M_j)_{j=\textrm{Pcut}(M)}^{\textrm{Lng}(M)-1}`$、末尾を除いた部分は $`P(A)`$（$`A=(M_j)_{j=0}^{\textrm{Pcut}(M)-1}`$）である。空でない列は「末尾を除いた部分」と「末尾」に分かれるから $`P(M)=P(A)\oplus(N)`$ であり、$`M=A\oplus N`$ である。
4. $`N`$ は $`P(M)`$ の成分なので、[1] の $`P`$ が簡約性を保つこと（$`M`$ 簡約 $`\iff`$ $`P(M)`$ の全成分が簡約）より $`N\in RT_{\textrm{PS}}`$。また [1] の $`P`$ の各成分の非複項性より $`N`$ は零項か単項で、いずれにせよ複項でない。補題G より $`P(N)=(N)`$。
5. $`N=((0,0))`$ の場合。$`M=A\oplus((0,0))`$ なので $`M`$ の最終列は $`(0,0)`$、すなわち $`M_{0,\textrm{Lng}(M)-1}=M_{1,\textrm{Lng}(M)-1}=0`$ で結論が出る。
6. $`N\neq((0,0))`$ の場合（矛盾を導く）。
   - 補題F の対偶より $`N`$ は零項でない。$`\textrm{Trans}`$ が零項性を保つことより $`\textrm{Trans}(N)\neq0`$。
   - [1] の $`\textrm{Trans}`$ の $`P`$ ブロック分解を使う。これは「$`A\oplus N`$ が簡約、$`N`$ が簡約、$`P(A\oplus N)=P(A)\oplus P(N)`$ ならば
     ```math
     \textrm{Trans}(A\oplus N)=\textrm{Trans}(A)+\begin{cases}D_00+\textrm{Trans}(N)&P(N)_0=((0,0))\cr \textrm{Trans}(N)&\text{その他}\end{cases}
     ```
     」という形である。いまは $`P(N)_0=N\neq((0,0))`$ なので $`\textrm{Trans}(M)=\textrm{Trans}(A)+\textrm{Trans}(N)`$。
   - $`\textrm{Trans}(N)\neq0`$ だから補題B より $`\textrm{dom}(\textrm{Trans}(M))=\textrm{dom}(\textrm{Trans}(N))`$、すなわち $`\textrm{dom}(\textrm{Trans}(N))=1`$。
   - $`N`$ は零項でない非複項なので単項である。$`\textrm{Lng}(N)\gt 1`$ なら補題E に、$`\textrm{Lng}(N)=1`$ なら補題C に矛盾する。

#### 後半

**補題I**（最終列が $`(0,0)`$ なら基本列は $`\textrm{Pred}`$）: $`\textrm{Lng}(M)\gt 1`$ かつ $`M_{0,j_1}=M_{1,j_1}=0`$（$`j_1=\textrm{Lng}(M)-1`$）ならば、任意の $`n`$ に対し $`M[n]=\textrm{Pred}(M)`$。$`M[n]`$ の定義は $`j_1=0`$ / $`M_{j_1}=(0,0)`$ / 親が無い / それ以外の 4 分岐で、いまは $`j_1\neq0`$ かつ $`M_{j_1}=(0,0)`$ なので第 2 分岐に落ち、値は $`n`$ に依らず $`\textrm{Pred}(M)`$ である。

**主補題J**（後半の本体）: $`M\in RT_{\textrm{PS}}`$、$`\textrm{Lng}(M)\gt 1`$、$`M_{0,j_1}=M_{1,j_1}=0`$ ならば $`\textrm{Trans}(M[n])+D_00=\textrm{Trans}(M)`$。

1. $`M_{j_1}=(0,0)`$ から $`M`$ の $`j_1`$ 以降の部分は $`((0,0))`$、$`\textrm{Pred}(M)=(M_j)_{j=0}^{j_1-1}`$ なので $`M=\textrm{Pred}(M)\oplus((0,0))`$。
2. 切片を 2 つ確定させる。$`(M_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)`$（$`0`$ から始まる切片は先頭 $`j_1`$ 項に一致する）、$`(M_j)_{j=j_1}^{j_1}=((0,0))`$（$`M_{0,j_1}=M_{1,j_1}=0`$ から成分計算）。
3. [1] の $`P`$ の加法性を $`j_0=j_1`$ で適用する。適用条件は $`0\lt j_1`$、$`j_1\leq\textrm{Lng}(M)-1`$、および「$`\forall j\lt j_1`$ に対し $`M_{0,j_1}\leq M_{0,j}`$」の 3 つで、前 2 つは $`\textrm{Lng}(M)\gt 1`$ から、最後は $`M_{0,j_1}=0`$ から従う。結論は
   ```math
   P(M)=P\bigl((M_j)_{j=0}^{j_1-1}\bigr)\oplus P\bigl((M_j)_{j=j_1}^{j_1}\bigr)=P(\textrm{Pred}(M))\oplus P(((0,0)))
   ```
   である。
4. $`P(((0,0)))=(((0,0)))`$ なので、その第 0 成分は $`((0,0))`$ である。
5. [1] の $`\textrm{Trans}`$ の $`P`$ ブロック分解を $`A=\textrm{Pred}(M)`$、$`N=((0,0))`$ に適用する。3 つの前提（$`A\oplus N=M`$ が簡約、$`N=((0,0))`$ が簡約、$`P(A\oplus N)=P(A)\oplus P(N)`$）は 1・3 と「$`((0,0))`$ は標準形ゆえ簡約」から揃う。今度は $`P(N)_0=((0,0))`$ なので第 1 分岐に落ち、
   ```math
   \textrm{Trans}(M)=\textrm{Trans}(\textrm{Pred}(M))+\bigl(D_00+\textrm{Trans}(((0,0)))\bigr)=\textrm{Trans}(\textrm{Pred}(M))+(D_00+0)=\textrm{Trans}(\textrm{Pred}(M))+D_00
   ```
   である（最後は主項列の連結が空列を吸収することによる）。
6. 補題I より $`M[n]=\textrm{Pred}(M)`$ なので $`\textrm{Trans}(M[n])+D_00=\textrm{Trans}(M)`$。

#### 結論

$`\textrm{dom}(\textrm{Trans}(M))=1`$ から主補題H で $`1\lt\textrm{Lng}(M)`$ と $`M_{j_1}=(0,0)`$ を得、主補題J で第 2 の選言肢 $`\textrm{Trans}(M[n])+D_00=\textrm{Trans}(M)`$ を得る。第 1 の選言肢は選ばれない。

なお同じファイルには「$`M\in RT_{\textrm{PS}}`$ かつ $`\textrm{dom}(\textrm{Trans}(M))=\omega`$ ならば $`1\lt\textrm{Lng}(M)`$」も証明されているが、これは原文のこの命題ではなく後続の命題（基本列の関係・基本列の収束）で使うためのものである。証明は補題C と同じ 1 列の場合分けで、$`M=((0,0))`$ なら $`\textrm{dom}(0)=\varnothing`$、$`M=(p)`$、$`p_1\neq0`$ なら $`\textrm{dom}(D_{p_1}0)=T_{p_1-1}`$ で、どちらも $`\mathbb{N}`$ でない、というものである。

## 原文通りに書けなかった理由

- **[S]** $`\textrm{dom}(t)=1`$ を集合の等式ではなく 4 値タグの等式として書いている

  原文の $`\textrm{dom}`$ は $`T_{\textrm{B}}`$ の部分集合を値に取り、$`1=\lbrace 0\rbrace`$ である。Lean は $`\textrm{dom}`$ を $`\varnothing,\lbrace 0\rbrace,\mathbb{N},T_v`$ の 4 値タグとして計算し、集合としての $`\textrm{dom}`$ はそのタグを集合に読み替えたものとして定義する。原文の $`\textrm{dom}(t)=1`$ に当たる述語は「タグが $`\lbrace 0\rbrace`$」である。タグから集合への読み替えは単射なので両者は一致するが、その単射性は補題として立てていない。本命題も、これを使う後続の命題も一貫してタグ側で述べるので、下流の内容は変わらない。

- **[S]** 前半の場合分けを $`\textrm{Trans}(M)`$ の形ではなく $`M`$ の形で行う

  原文は $`\textrm{dom}`$ の定義から $`\textrm{Trans}(M)=D_00`$ か、末尾が $`D_00`$ の複項か、で分ける。Lean は $`\textrm{Trans}`$ の再帰の分岐に合わせて $`M`$ の側で分ける（$`\textrm{Lng}(M)=1`$／単項で $`\textrm{Lng}(M)\gt 1`$／複項）。そのため原文には無い補題 C（1 列では $`\textrm{dom}\neq1`$）と補題 E（単項で 2 列以上なら $`\textrm{dom}\neq1`$）が要る。逆に、原文の「$`\textrm{Trans}(M)`$ は複項である」という段は Lean には現れない。結論の形は同じで下流も変わらない。

- **[S]** 系（$`\textrm{Trans}`$ と非可算基数の関係）を $`\textrm{Pred}`$ による $`\textrm{Trans}`$ の狭義降下で置き換えている

  原文はこの系を 2 か所で使う。1 つは $`\textrm{Trans}(M)=D_00\Rightarrow M=((0,0),(0,0))`$、もう 1 つは $`\textrm{Trans}(P(M)_{J_1})=D_00\Rightarrow P(M)_{J_1}=((0,0),(0,0))`$ である。この系は本リポジトリに無い。第 1 の使い方は Lean では不要になり（原文が第 1 の選言肢を出す場合も第 2 の選言肢が成り立つため）、第 2 の使い方の代わりに Lean は補題 E を置く。その証明では [1] の $`\textrm{Pred}`$ による $`\textrm{Trans}`$ の狭義降下（$`\textrm{Trans}(\textrm{Pred}(M))\lt_{\textrm{B}}\textrm{Trans}(M)`$）と補題 D（$`D_00`$ 未満は $`0`$ のみ）を使う。$`\textrm{Trans}(\textrm{Pred}(M))=0`$ に落ちる縮退した場合だけは降下が使えないので、そこは $`\textrm{Lng}(M)=2`$ に持ち込んで [1] の 2 列の $`\textrm{Trans}`$ の明示式 $`D_{M_{1,0}}(D_{M_{1,1}}0)`$ で潰す。なお原文はこの系を $`P(M)_{J_1}`$ に適用するとき $`P(M)_{J_1}\in RT_{\textrm{PS}}`$ を断らないが、Lean は [1] の $`P`$ が簡約性を保つことを明示的に引いて末尾ブロックの簡約性を出してから補題 E・補題 C を適用する。

- **[R]** 「$`P(M)_0`$ が零項かつ $`\textrm{Lng}(P(M))=2`$」を排除する段落と、そこから $`M`$ が複項であることを導く段落が要らない

  原文はこの 2 段落で、$`\textrm{Trans}(M)`$ が複項であることと $`\textrm{Trans}`$ が単項性を保つことから $`M`$ が複項であることを導く。Lean は $`M`$ が複項であることを直接得る。$`\textrm{Lng}(M)\gt 1`$ から $`M`$ は零項でなく、補題 E から $`M`$ は単項でない、というだけである。

- **[⚠️Y]** 「$`P(M)_{J_1}`$ は単項であり」は「非複項であり」の誤り

  原文はここで $`P(M)_{J_1}`$ が単項であると述べ、その直後に $`P(M)_{J_1}=((0,0))`$ と結論する。$`((0,0))`$ は零項であって単項ではないので、原文の 2 文をそのまま形式化すると矛盾する。[1] の $`P`$ の各成分について言えるのは非複項性（零項または単項）であり、$`P(M)_{J_1}=((0,0))`$ を排除できるのは $`\textrm{Trans}(P(M)_{J_1})=D_00`$ を仮定した第 2 の選言肢の中だけである。「単項」を「非複項」に替えるか、「単項であり」を第 2 の選言肢の中へ移すかで直る。Lean は末尾ブロックを非複項として扱い、$`((0,0))`$ かどうかで場合分けしてから、$`((0,0))`$ でない側でのみ零項性を排除して単項に絞る。

- **[W]** 原文は $`P`$ の加法性の適用条件を確認していない

  [1] の $`P`$ の加法性は分割点 $`j_0`$ について $`0\lt j_0`$、$`j_0\leq\textrm{Lng}(M)-1`$、$`\forall j\lt j_0\ (M_{0,j_0}\leq M_{0,j})`$ の 3 条件を要求する。原文は「[1] の $`P`$ の加法性より $`P(M)=P(\textrm{Pred}(M))\oplus_{T_{\textrm{PS}}}(((0,0)))`$ である」と書くだけで、$`j_0`$ が何かも条件の確認も書かない。Lean は $`j_0=\textrm{Lng}(M)-1`$ を取り、前 2 条件を $`\textrm{Lng}(M)\gt 1`$ から、第 3 条件を $`M_{0,j_0}=0`$ から確認したうえで加法性を適用し、得られた 2 つの切片をそれぞれ $`\textrm{Pred}(M)`$ と $`((0,0))`$ に書き換える。

- **[R]** $`P`$ の連結性から $`M=\textrm{Pred}(M)\oplus((0,0))`$ を出す一歩が要らない

  原文は $`P`$ の加法性で $`P(M)=P(\textrm{Pred}(M))\oplus(((0,0)))`$ を出し、次に「$`P`$ の定義より」（$`P`$ の成分の連結が $`M`$ に戻ることより）$`M=\textrm{Pred}(M)\oplus((0,0))`$ を出す。Lean では順序が逆で、最終列が $`(0,0)`$ であることから $`M=\textrm{Pred}(M)\oplus((0,0))`$ が直ちに出る（末尾 1 列を切り離すだけ）。$`P`$ の加法性はその後、$`\textrm{Trans}`$ の $`P`$ ブロック分解の前提 $`P(M)=P(\textrm{Pred}(M))\oplus P(((0,0)))`$ を作るためだけに使う。

- **[⚠️Y]** 最後の等式の切片の添字が誤植である

  原文は $`\textrm{Trans}(M)=\textrm{Trans}((M_j)_{j_0}^{j_0-1})+D_00=\textrm{Trans}((M_j)_{j_0}^{j_1-1})+D_00`$ と書くが、原文の他の箇所では切片を $`(M_j)_{j=0}^{j_1-1}`$ のように「$`j=`$」付きで書いている。ここは $`(M_j)_{j=0}^{j_0-1}`$ と $`(M_j)_{j=0}^{j_1-1}`$ の誤植である。字義どおりに読むと最初の切片は $`j`$ が $`j_0`$ から $`j_0-1`$ までの空列になり、$`\textrm{Trans}`$ の定義の複項枝（$`\textrm{Trans}(M)=\textrm{Trans}((M_j)_{j=0}^{j_0-1})+D_00`$）とも合わない。Lean は $`(M_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)`$ の形で使う。

- **[W]** $`M[n]=\textrm{Pred}(M)`$ が原文に書かれていない

  原文の最後の等式の連鎖は $`\textrm{Trans}(\textrm{Pred}(M))+D_00=\textrm{Trans}(M[n])+D_00`$ で終わるが、$`\textrm{Trans}(\textrm{Pred}(M))=\textrm{Trans}(M[n])`$ の根拠は書かれていない。実際には $`M_{j_1}=(0,0)`$ かつ $`j_1\neq0`$ なので $`M[n]`$ の定義の第 2 分岐が選ばれ、$`n`$ に依らず $`M[n]=\textrm{Pred}(M)`$ になる。Lean はこれを補題 I として明示する。

- **[R]** 第 1 の選言肢は不要である

  Lean は常に第 2 の選言肢 $`\textrm{Trans}(M[n])+D_00=\textrm{Trans}(M)`$ を示す。原文が第 1 の選言肢を出す場合、すなわち $`M=((0,0),(0,0))`$ でも、$`M`$ の最終列は $`(0,0)`$ なので $`M=\textrm{Pred}(M)\oplus((0,0))`$ であり、$`\textrm{Trans}(M[n])+D_00=0+D_00=D_00=\textrm{Trans}(M)`$ で第 2 の選言肢が成り立つ。命題の形は原文どおり選言のまま述べてあるので、下流はそのまま両方の場合を受け取れる。

- **[R]** $`n\in\mathbb{N}_+`$ の仮定は使われない

  Lean は原文どおり $`1\leq n`$ を仮定に書くが、証明では使わない。結論に効く $`M[n]`$ の値は $`M[n]=\textrm{Pred}(M)`$ で $`n`$ に依らないからである。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| ペア列、$`\textrm{Lng}(M)`$、$`M_{i,j}`$ | `PSS.PS`, `PSS.Lng`, `PSS.entry` | `lean/PSS/Defs.lean` |
| $`T_{\textrm{PS}}`$、$`\textrm{Pred}(M)`$、$`(M_j)_{j=a}^{b}`$、$`M[n]`$ | `PSS.TPS`, `PSS.Pred`, `PSS.seg`, `PSS.oper` | 同上 |
| 零項・単項・複項、$`\textrm{Pcut}`$、$`P(M)`$ | `PSS.zeroT`, `PSS.monoT`, `PSS.multiT`, `PSS.Pcut`, `PSS.P` | `lean/PSS/Mono.lean` |
| $`\textrm{Red}`$、$`RT_{\textrm{PS}}`$、対角列 | `PSS.Red`, `PSS.RTPS`, `PSS.diagSeq` | `lean/PSS/Red.lean` |
| $`ST_{\textrm{PS}}`$ | `PSS.STPS` | `lean/PSS/Standard.lean` |
| $`T_{\textrm{B}}`$ の項、$`0`$、$`D_va`$、$`\lt_{\textrm{B}}`$、$`P_{\textrm{B}}`$ | `PSS.BT`, `PSS.BP`, `PSS.BZero`, `PSS.Dprin`, `PSS.lessBT`, `PSS.lessBP`, `PSS.lessBPList`, `PSS.PB` | `lean/Buchholz-1986/Buchholz-1986-2.1.lean` |
| $`t+u`$、$`\textrm{dom}`$ のタグと集合 | `PSS.addBT`, `PSS.BDom`, `PSS.domTag`, `PSS.domTagBP`, `PSS.domTagList`, `PSS.domB` | `lean/Buchholz-1986/Buchholz-1986-3.2.lean` |
| $`\textrm{dom}(t)=1`$、$`\textrm{dom}(t)=\omega`$ | `domIsOne`, `domIsOmega` | `lean/Bijectivity/Cited.lean` |
| $`\textrm{Trans}`$ とその燃料付き本体 | `PSS.Trans`, `PSS.TransAux` | `lean/PSS/Trans.lean` |
| 簡約入力では燃料 $`\textrm{Lng}(M)`$ で確定 | `Trans_eq_lengthAux` | `lean/7/7.3-Trans-welldefined.lean` |
| $`D_00`$ | `DzeroZero` | `lean/Bijectivity/15-successor-fseq.lean` |
| $`\textrm{Trans}(((0,0)))=0`$、$`((0,0))\in RT_{\textrm{PS}}`$ | `Trans_zero_singleton'`, `RTPS_zero_singleton` | 同上 |
| 補題A | `domTagBP_zeroOnly_iff` | 同上 |
| 補題B（列版・和版） | `domTagList_append`, `domTag_addBT_right` | 同上 |
| 補題C | `not_domIsOne_of_lng_one` | 同上 |
| $`\textrm{dom}=\omega`$ ならば $`1\lt\textrm{Lng}(M)`$ | `one_lt_lng_of_domIsOmega` | 同上 |
| 補題D | `lessBT_D00_imp_zero` | 同上 |
| 補題E | `not_domIsOne_of_monoT` | 同上 |
| 補題F | `eq_zero_singleton_of_zeroT` | 同上 |
| 補題G | `P_self_of_nonmulti` | 同上 |
| 空でない列の末尾分解 | `eq_dropLast_getLastD` | 同上 |
| 主補題H | `last_zero_of_domIsOne` | 同上 |
| 補題I | `oper_of_last_zero` | 同上 |
| 主補題J | `successor_fseq_of_last_zero` | 同上 |
| 命題（後続な項の基本列） | `successor_fseq` | 同上 |
| [1] $`\textrm{Trans}`$ が零項性を保つこと | `Trans_preserves_zeroT` | `lean/7/7.3-Trans-preserves-zeroT.lean` |
| [1] $`\textrm{Trans}`$ が単項性を保つこと | `Trans_monoT_principal` | `lean/7/7.3-Trans-preserves-monoT.lean` |
| [1] 2 列の $`\textrm{Trans}`$ の明示式 | `two_column_Trans` | `lean/7/7.3-two-column.lean` |
| [1] $`\textrm{Pred}`$ による $`\textrm{Trans}`$ の狭義降下 | `Pred_Trans_descend_RTPS` | `lean/7/7.3-Pred-Trans-descend.lean` |
| 零項の $`\textrm{Red}`$ は $`((0,0))`$ | `Red_zero_mr` | `lean/6/6.5-monoT-Red.lean` |
| $`\textrm{Pred}`$ が簡約性を保つこと、$`\textrm{Lng}(\textrm{Pred}(M))`$ | `RTPS_Pred`, `length_Pred` | `lean/6/6.5-Red-Pred-commute.lean` |
| [1] $`P`$ の加法性 | `P_additivity` | `lean/6/6.2-P-additivity.lean` |
| [1] $`P`$ の各成分の非複項性、複項 $`\iff\textrm{Lng}(P(M))\gt 1`$ | `P_components_nonmulti`, `P_components_multi_iff` | `lean/6/6.2-P-components-nonmulti.lean` |
| $`P`$ の成分の連結、$`P(M)\neq()`$、複項の $`P`$ の末尾成分 | `P_concat`, `P_nonempty`, `P_last_multi` | `lean/6/6.2-P-fseq.lean` |
| [1] $`P`$ が簡約性を保つこと | `RTPS_iff_P_components` | `lean/6/6.6-P-preserves-reduced.lean` |
| [1] $`\textrm{Trans}`$ の $`P`$ ブロック分解 | `f7x_Trans_append_Pblocks_holds`（主張は `FseqDesc_f7x_Trans_append_Pblocks`） | `lean/8/8.7-descend-last2.lean`（主張は `lean/8/8.7-fseq-descend.lean`） |
| $`RT_{\textrm{PS}}\subseteq T_{\textrm{PS}}`$ | `RTPS_TPS` | `lean/6/6.6-reduced-leftend.lean` |
| $`ST_{\textrm{PS}}\subseteq RT_{\textrm{PS}}`$ | `STPS_RTPS` | `lean/6/6.7-standard-reduced.lean` |
| $`(M_j)_{j=0}^{j}`$ が先頭切片であること | `seg_zero_eq_take` | `lean/Bijectivity/11-path-to-initial-segment.lean` |

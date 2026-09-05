[← back](README.md)

# 12: 命題 (基本列的順序が辞書式的順序を含意すること)

## 原文

### 命題

命題 (基本列的順序が辞書式的順序を含意すること)

任意の$M,N\in CT_{\textrm{PS}}$に対して、$M<_{\textrm{PS}}N$ならば$M<_{\textrm{PS}[]}N$である。

### 証明

$\textrm{operator}[]$の定義中の記号を$M$と$N$に対して定義し、それぞれ右肩に$M$と$N$を乗せて表記する。  
$j_1^M=0$とする。  
　$CT_{\textrm{PS}}$の定義より$M=((0,0))=(N_j)_{j=0}^0$である。  
　標準形の始切片への経路より$M<_{\textrm{PS}[]}N$である。  
$j_1^M>0$ならば、任意の$M',N'\in CT_{\textrm{PS}}$に対して、$\textrm{Lng}(M')<\textrm{Lng}(M)$かつ$M'<_{\textrm{PS}}N'$ならば$M'<_{\textrm{PS}[]}N'$であると仮定する。  
　$f=\min\lbrace \min(j_1^M,j_1^N)+1\rbrace \cup\lbrace j\mid j\in\mathbb{N}\land j\leq\min(j_1^M,j_1^N)\land M_j\neq N_j\rbrace$とする。  
　$f=j_1^M+1$ならば、$M=(N_j)_{j=0}^{j_1^M}$であるから標準形の始切片への経路より$M<_{\textrm{PS}[]}N$である。  
　$f\leq j_1^M$とする。  
　　$M<_{\textrm{PS}}N$であるから$f\leq j_1^N$である。  
　　$f=j_1^N$とする。  
　　　仮定より$j_1^N\leq j_1^M$である。  
　　　[1]の簡約性と係数の関係、条件(A)と(B)と係数の基本性質(1)及び(2)、標準形の簡約性及び$CT_{\textrm{PS}}$の定義より任意の$M'\in CT_{\textrm{PS}}$に対して、$\textrm{Lng}(M')=\textrm{Lng}(N)$ならば$M'_{1,j_1^N}\leq M'_{0,j_1^N}\leq j_1^N$である。  
　　　任意の$M'\in CT_{\textrm{PS}}$に対して、$\textrm{Lng}(M')=\textrm{Lng}(N)$ならば$M'=(M'_j)_{j=0}^{j_1^N-1}\oplus((M'_{0,j_1^N},M'_{1,j_1^N}))$である。  
　　　従って$\textrm{Lng}(M')=\textrm{Lng}(N)$かつ$(M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}$である$M'\in CT_{\textrm{PS}}$は高々$(j_1^N)^2$個である。  
　　　任意の$M',N'\in CT_{\textrm{PS}}$に対して、$\textrm{Lng}(M')=\textrm{Lng}(N)$かつ$N\leq_{\textrm{PS}}M'<_{\textrm{PS}}N'$ならば$M'<_{\textrm{PS}[]}N'$であると仮定する。  
　　　　可算な標準形の起源よりある$v^M,v^N\in\mathbb{N}$が存在して$M\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v^M}$かつ$N\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v^N}$である。  
　　　　$v=\max(v^M,v^N)$とする。  
　　　　標準形の始切片への経路より$((j,j))_{j=0}^{v^M}\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$かつ$((j,j))_{j=0}^{v^N}\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$である。  
　　　　基本列的順序が推移性より$M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$かつ$N\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$である。  
　　　　$\leq_{\textrm{PS}[]}$の定義よりある$a\in\mathbb{N}_+^{<\omega}$が存在して$M=((j,j))_{j=0}^v[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$である。  
　　　　辞書式的順序が基本列的順序を含意することより$N\leq_{\textrm{PS}}((j,j))_{j=0}^v$である。  
　　　　$M=((j,j))_{j=0}^v[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\leq_{\textrm{PS}}N\leq_{\textrm{PS}}((j,j))_{j=0}^v$よりある$g\in\mathbb{N}$が存在して$g\leq\textrm{Lng}(a)$かつ$((j,j))_{j=0}^v[a_0]\cdots[a_g]<_{\textrm{PS}}N$であり、そのような$g$で最小のものを$g_0$とする。  
　　　　$N'=((j,j))_{j=0}^v[a_0]\cdots[a_{g_0-1}]$とする。  
　　　　辞書式的順序の線形性及び$g_0$の定義より$N\leq_{\textrm{PS}}N'$である。  
　　　　$N<_{\textrm{PS}}N'$とする。  
　　　　　辞書式的順序が基本列的順序を含意することより$M<_{\textrm{PS}}N'[a_{g_0}]<_{\textrm{PS}}N$である。  
　　　　　$f$の定義及び仮定より$(M_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}$であるから、上より$\textrm{Lng}(N'[a_{g_0}])>j_1^N$かつ$(M_j)_{j=0}^{j_1^N-1}=(N'[a_{g_0}]_j)_{j=0}^{j_1^N-1}$である。  
　　　　　上より$(N'[a_{g_0}]_j)_{j=j_1^N}^{\textrm{Lng}(N'[a_{g_0}])-1}<_{\textrm{PS}}(N_j)_{j=j_1^N}^{j_1^N}=(N_{j_1^N})$であり、よって$(N'[a_{g_0}]_{j_1^N})<_{\textrm{PS}}(N_{j_1^N})$であるから、$(N'[a_{g_0}]_j)_{j=0}^{j_1^N}<_{\textrm{PS}}N$である。  
　　　　　任意の$n\in\mathbb{N}_+$を取る。  
　　　　　　$\textrm{Lng}(N'[n])\leq j_1^N$ならば、基本列の切片の不変性より$N'[n]=(N'[a_{g_0}]_j)_{j=0}^{\textrm{Lng}(N'[n])-1}<_{\textrm{PS}}(N'[a_{g_0}]_j)_{j=0}^{j_1^N}<_{\textrm{PS}}N$である。  
　　　　　　$\textrm{Lng}(N'[n])>j_1^N$ならば、基本列の切片の不変性より$(N'[n]_j)_{j=0}^{j_1^N}=(N'[a_{g_0}]_j)_{j=0}^{j_1^N}$であり、$(N'[a_{g_0}]_j)_{j=0}^{j_1^N}<_{\textrm{PS}}N$であるから、$<_{\textrm{PS}}$の定義より$N'[n]<_{\textrm{PS}}N$である。  
　　　　　従って任意の$n\in\mathbb{N}_+$に対して$N'[n]<_{\textrm{PS}}N$である。  
　　　　　辞書式的順序が基本列的順序を含意することより任意の$n\in\mathbb{N}_+$に対して$N<_{\textrm{PS}[]}N'[n]$ではない。  
　　　　　従って$N<_{\textrm{PS}[]}N'$ではない。  
　　　　　仮定より$N<_{\textrm{PS}[]}N'$であるが、これは上と矛盾する。  
　　　　従って$N=N'$である。  
　　　　よって$N[a_{g_0}]\cdots[a_{\textrm{Lng}(a)-1}]=M$であるから、$M<_{\textrm{PS}[]}N$である。  
　　　　仮定より任意の$N'\in CT_{\textrm{PS}}$に対して、$N<_{\textrm{PS}}N'$ならば$N<_{\textrm{PS}[]}N'$である。  
　　　　基本列的順序が推移性より、任意の$N'\in CT_{\textrm{PS}}$に対して、$N\leq_{\textrm{PS}}N'$ならば$M<_{\textrm{PS}[]}N'$である。  
　　　　ある$M'\in CT_{\textrm{PS}}$が存在して、$\textrm{Lng}(M')=\textrm{Lng}(N)$かつ$(M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}$かつ$M'<_{\textrm{PS}}N$であるならば、そのようなもののうち$<_{\textrm{PS}}$に対する最大元をとる。  
　　　　$M=M'$とした場合により、任意の$N'\in CT_{\textrm{PS}}$に対して、$N\leq_{\textrm{PS}}N'$ならば$M'<_{\textrm{PS}[]}N'$である。  
　　　　任意の$O\in CT_{\textrm{PS}}$をとり、$M'<_{\textrm{PS}}O<_{\textrm{PS}}N$とする。  
　　　　　$<_{\textrm{PS}}$の定義より$M'\leq_{\textrm{PS}}(O_j)_{j=0}^{\min(\textrm{Lng}(O)-1,j_1^N)}<_{\textrm{PS}}N$である。  
　　　　　$(M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}$であるから、$\textrm{Lng}(O)\geq\textrm{Lng}(M')$かつ$(O_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}$である。  
　　　　　[1]の標準形の始切片への遺伝性及び$CT_{\textrm{PS}}$の定義より$(O_j)_{j=0}^{j_1^N}\in CT_{\textrm{PS}}$である。  
　　　　　$M'$の最大性より、$(O_j)_{j=0}^{j_1^N}=M'$である。  
　　　　　標準形の始切片への経路より$M'=(O_j)_{j=0}^{j_1^N}\leq_{\textrm{PS}[]}O$である。  
　　　　よって任意の$N'\in CT_{\textrm{PS}}$に対して、$M'<_{\textrm{PS}}N'$ならば$M'<_{\textrm{PS}[]}N'$である。  
　　　$\textrm{Lng}(N)$及び$(N_j)_{j=0}^{j_1^N-1}$を固定したときの帰納法により、任意の$N'\in CT_{\textrm{PS}}$に対して、$N\leq_{\textrm{PS}}N'$ならば$M<_{\textrm{PS}[]}N'$である。  
　　よって$f=j_1^N$ならば、任意の$N'\in CT_{\textrm{PS}}$に対して、$N\leq_{\textrm{PS}}N'$ならば$M<_{\textrm{PS}[]}N'$である。  
　　$f\leq j_1^N$であり、$f$の定義より$N$を$(N_j)_{j=0}^f$に置き換えても$f$が不変であり、$(N_j)_{j=0}^f\leq_{\textrm{PS}}N$であるから上より$M<_{\textrm{PS}[]}N$である。  
　　よっていずれの場合でも$M<_{\textrm{PS}[]}N$である。  
　よっていずれの場合でも$M<_{\textrm{PS}[]}N$である。  
帰納法により任意の$M,N\in CT_{\textrm{PS}}$に対して、$M<_{\textrm{PS}}N$ならば$M<_{\textrm{PS}[]}N$である。□

## Lean

### Lean での命題

任意の $M,N\in CT_{\textrm{PS}}$ に対して、$M<_{\textrm{PS}}N$ ならば $M<_{\textrm{PS}[]}N$ である。

原文の命題そのままで、追加の仮定は無い。使う定義も原文どおりである。

- $CT_{\textrm{PS}}=\lbrace M\mid M\in ST_{\textrm{PS}}\land M_0=(0,0)\rbrace$。
- $<_{\textrm{PS}}$ は原文の再帰的定義。再帰の末尾に現れる空列については、$()<_{\textrm{PS}}N$ を
  $N\neq()$ と同値、$M<_{\textrm{PS}}()$ を偽、と辞書式順序の規約で補う。
- $M\leq_{\textrm{PS}[]}N$ は「ある $a\in\mathbb{N}_+^{<\omega}$ が存在して
  $M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$」、$M<_{\textrm{PS}[]}N$ はさらに $a\neq()$。
- $M_{i,j}$ は範囲外で $0$、$M_j=(M_{0,j},M_{1,j})$。

### Lean での証明

**骨格**

$L=\textrm{Lng}(M)$ と置き、$S_L=\lbrace X\mid X\in CT_{\textrm{PS}}\land\textrm{Lng}(X)\leq L\rbrace$ の上で、
$<_{\textrm{PS}}$ を逆向きにした関係についての整礎帰納法（$S_L$ の中での下降帰納法）を一つだけ回す。
示す主張は

$\Phi_L(X)$: 任意の $N\in CT_{\textrm{PS}}$ に対して、$\textrm{Lng}(N)\leq L$ かつ $X<_{\textrm{PS}}N$ ならば $X<_{\textrm{PS}[]}N$

である。原文の外側（$\textrm{Lng}(M)$ に関する）帰納法にあたるものは無い。原文の内側の帰納法に
あたるのがこの帰納法で、台が原文の
$\lbrace M'\in CT_{\textrm{PS}}\mid\textrm{Lng}(M')=\textrm{Lng}(N)\land(M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}\rbrace$
から $S_L$ に替わっている。以下 (1)(2)(3) が道具、(4) が原文の $f\leq j_1^N$ の帰着（原文の最後から
3 行目）、(5) が原文の $f=j_1^N$ の場合の主要部、(6) が帰納法本体である。

**(1) $\leq_{\textrm{PS}[]}$ まわりの小道具**

**(1-a) 混合推移性.** $X<_{\textrm{PS}[]}Y$ かつ $Y\leq_{\textrm{PS}[]}Z$ ならば $X<_{\textrm{PS}[]}Z$。
$a\neq()$ と $b$ を取って $X=Y[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$、$Y=Z[b_0]\cdots[b_{\textrm{Lng}(b)-1}]$
とすると、添字列の連結について $Z[(b\oplus_A a)_0]\cdots=X$ であり、$a\neq()$ より $b\oplus_A a\neq()$。

**(1-b) 始切片の $CT_{\textrm{PS}}$ 性.** $N\in CT_{\textrm{PS}}$、$f<\textrm{Lng}(N)$ ならば
$(N_j)_{j=0}^{f}\in CT_{\textrm{PS}}$。$ST_{\textrm{PS}}$ 性は [1] の 標準形の始切片への遺伝性、
最左列は切り落とされないので $((N_j)_{j=0}^{f})_0=N_0=(0,0)$。

**(1-c) 標準形の始切片への経路（切片形）.** $N\in CT_{\textrm{PS}}$、$f<\textrm{Lng}(N)$ ならば
$(N_j)_{j=0}^{f}\leq_{\textrm{PS}[]}N$。原文の 標準形の始切片への経路 を、閉区間の切片
$(N_j)_{j=0}^{f}$ が先頭 $f+1$ 項に等しいことで書き換えたもの。結論が $\leq_{\textrm{PS}[]}$ で
あることについては下の「原文通りに書けなかった理由」を参照。

**(1-d) 真の始切片は狭義に下.** $X,N\in CT_{\textrm{PS}}$、$\textrm{Lng}(X)<\textrm{Lng}(N)$、
$X=(N_j)_{j=0}^{\textrm{Lng}(X)-1}$ ならば $X<_{\textrm{PS}[]}N$。
$\textrm{Lng}(X)>0$ より $\textrm{Lng}(X)-1<\textrm{Lng}(N)$ なので (1-c) が使えて
$X=(N_j)_{j=0}^{\textrm{Lng}(X)-1}\leq_{\textrm{PS}[]}N$、すなわち $a$ が取れる。
$a=()$ とすると $X=N$ となり $\textrm{Lng}(X)<\textrm{Lng}(N)$ に反するので $a\neq()$。

**(2) $<_{\textrm{PS}}$ の分解（原文の $f$）**

**(2-a) 分解.** $M<_{\textrm{PS}}N$ ならば次のいずれかが成り立つ。

- (i) $\textrm{Lng}(M)<\textrm{Lng}(N)$ かつ $M=(N_j)_{j=0}^{\textrm{Lng}(M)-1}$。
- (ii) ある $f$ が存在して、$f<\textrm{Lng}(M)$、$f<\textrm{Lng}(N)$、$(M_j)_{j=0}^{f-1}=(N_j)_{j=0}^{f-1}$、
  かつ $M_{0,f}<N_{0,f}$ または（$M_{0,f}=N_{0,f}$ かつ $M_{1,f}<N_{1,f}$）。

証明は $<_{\textrm{PS}}$ の再帰的定義に沿った両列同時の帰納である。どちらかが空列の場合は
定義から直ちに (i)。先頭が異なる場合（$M_{0,0}<N_{0,0}$ または $M_{0,0}=N_{0,0}\land M_{1,0}<N_{1,0}$）は
共通接頭辞を空として (ii)。先頭が等しい場合は $M_{0,0}=N_{0,0}$ かつ $M_{1,0}=N_{1,0}$ すなわち
$M_0=N_0$ であり、尾に帰納法の仮定を使って得た分解の先頭に $M_0$ を付け直す。
これが原文の
$f=\min\lbrace \min(j_1^M,j_1^N)+1\rbrace \cup\lbrace j\mid j\in\mathbb{N}\land j\leq\min(j_1^M,j_1^N)\land M_j\neq N_j\rbrace$
による場合分けにあたる。(i) が原文の $f=j_1^M+1$、(ii) の $f$ が原文の $f\leq j_1^M$ の場合の $f$ である。
(ii) は $f<\textrm{Lng}(M)$ と $f<\textrm{Lng}(N)$ を同時に与えるので、原文の
「$M<_{\textrm{PS}}N$ であるから $f\leq j_1^N$」の一手は分解に含まれている。

**(2-b) 逆向き.** $k<\textrm{Lng}(M)$、$k<\textrm{Lng}(N)$、$(M_j)_{j=0}^{k-1}=(N_j)_{j=0}^{k-1}$、
かつ $M_k$ が $N_k$ より対の辞書式で小さいならば $M<_{\textrm{PS}}N$。
$M=(M_j)_{j=0}^{k-1}\oplus_A(M_k)\oplus_A(M_j)_{j=k+1}^{\textrm{Lng}(M)-1}$ と分解し、$N$ も同様に分解して、
共通接頭辞 $(M_j)_{j=0}^{k-1}=(N_j)_{j=0}^{k-1}$ を消去してから先頭で決める。

**(2-c) 真の始切片は小さい.** $k<\textrm{Lng}(M)$ ならば $(M_j)_{j=0}^{k-1}<_{\textrm{PS}}M$。

**(2-d) 切片が小さければ本体も小さい.** $\textrm{Lng}(N)\leq k$ かつ $(M_j)_{j=0}^{k-1}<_{\textrm{PS}}N$
ならば $M<_{\textrm{PS}}N$。(2-a) で $(M_j)_{j=0}^{k-1}<_{\textrm{PS}}N$ を分解する。(i) なら
$\min(k,\textrm{Lng}(M))=\textrm{Lng}((M_j)_{j=0}^{k-1})<\textrm{Lng}(N)\leq k$ だから
$\textrm{Lng}(M)<k$、すなわち切片は $M$ 自身なので仮定がそのまま結論である。(ii) なら相違位置 $d$ は
$d<\textrm{Lng}((M_j)_{j=0}^{k-1})\leq k$ なので $M_d=((M_j)_{j=0}^{k-1})_d$ であり、
$(M_j)_{j=0}^{d-1}=(N_j)_{j=0}^{d-1}$ と合わせて (2-b) を $M$ と $N$ に使える。

なお (2) の道具立てには、対の辞書式比較の非対称性と、接頭辞関係から $<_{\textrm{PS}}$ を出す補題も
置かれているが、以降では使っていない。

**(3) 有限性（原文の係数評価と個数評価）**

**(3-a) 係数評価.** $M\in CT_{\textrm{PS}}$、$j<\textrm{Lng}(M)$ ならば $M_{1,j}\leq M_{0,j}\leq j$。
内訳は原文が挙げる引用のとおりである。$CT_{\textrm{PS}}$ の定義より $M\in ST_{\textrm{PS}}$、
[1] の 標準形の簡約性 より $M\in RT_{\textrm{PS}}$、[1] の 簡約性と条件(A)(B) の同値より条件(A)(B)。
$M_{1,j}\leq M_{0,j}$ は [1] の 簡約性と係数の関係。$M_{0,j}\leq j$ は条件(A)と
$M_{0,0}=0$（$CT_{\textrm{PS}}$ の定義から最左列が $(0,0)$）から $j$ についての強帰納法で出る
（上段に親 $p$ があれば条件(A)より $M_{0,j}=M_{0,p}+1\leq p+1\leq j$、無ければ $M_{0,j}=0$）。
原文は $j=j_1^N$ でのみ述べるが、ここでは $\textrm{Lng}(M)$ 未満の全ての $j$ で示す。

**(3-b) 範囲外込み.** 添字が範囲外なら $M_{0,j}=M_{1,j}=0$ なので、(3-a) と合わせて全ての $j$ で
$M_{0,j}\leq j$ かつ $M_{1,j}\leq j$。

**(3-c) $S_L$ の有限性.** $M\in S_L$ に対して
$(\textrm{Lng}(M),(M_{0,j},M_{1,j})_{j=0}^{L-1})\in\lbrace 0,\ldots,L\rbrace \times(\lbrace 0,\ldots,L\rbrace ^2)^L$
を対応させる。(3-b) より各成分は $j\leq L$ で抑えられるのでこの対応は行き先の有限集合に収まり、
$M$ は長さと各成分から復元できるので単射である。よって $S_L$ は有限。

**(3-d) 下降帰納.** $<_{\textrm{PS}}$ は 辞書式的順序の線形性 より非反射的かつ推移的だから、
有限集合 $S_L$ の上でその逆関係は整礎である。よって $S_L$ の元 $X$ について、
$S_L$ の中で $X$ より $<_{\textrm{PS}}$ で真に上の元すべてで主張が成り立つと仮定してよい。

**(4) 相手の長さの帰着（原文の $N$ を $(N_j)_{j=0}^f$ に置き換える段）**

$X\in CT_{\textrm{PS}}$ とし、$\textrm{Lng}(N)\leq\textrm{Lng}(X)$ なる $N\in CT_{\textrm{PS}}$ について
$X<_{\textrm{PS}}N\Rightarrow X<_{\textrm{PS}[]}N$ が分かっているとする。このとき任意の
$N\in CT_{\textrm{PS}}$ について同じ含意が成り立つ。

$X<_{\textrm{PS}}N$ を (2-a) で分解する。(i) なら (1-d) で $X<_{\textrm{PS}[]}N$。(ii) の $f$ に対して
$\tilde N=(N_j)_{j=0}^{f}$ と置くと、

- (1-b) より $\tilde N\in CT_{\textrm{PS}}$、
- $\textrm{Lng}(\tilde N)=f+1\leq\textrm{Lng}(X)$（$f<\textrm{Lng}(X)$ より）、
- $(X_j)_{j=0}^{f-1}=(N_j)_{j=0}^{f-1}=(\tilde N_j)_{j=0}^{f-1}$ かつ $\tilde N_f=N_f$ なので (2-b) より
  $X<_{\textrm{PS}}\tilde N$。

仮定より $X<_{\textrm{PS}[]}\tilde N$、(1-c) より $\tilde N\leq_{\textrm{PS}[]}N$、(1-a) を合わせて
$X<_{\textrm{PS}[]}N$。原文はここを「$(N_j)_{j=0}^f\leq_{\textrm{PS}}N$ であるから上より」と
$\leq_{\textrm{PS}}$ で繋いでいるが、ここでは $\tilde N\leq_{\textrm{PS}[]}N$ で繋いでいる。

**(5) 主要部（原文の $f=j_1^N$ の場合）**

**主張.** $M,N\in CT_{\textrm{PS}}$、$M<_{\textrm{PS}}N$、$\textrm{Lng}(N)\leq\textrm{Lng}(M)$、
$j_1=\textrm{Lng}(N)-1$ と置いて $(M_j)_{j=0}^{j_1-1}=(N_j)_{j=0}^{j_1-1}$ とする。さらに

$\Phi(N)$: 任意の $N'\in CT_{\textrm{PS}}$ に対して $N<_{\textrm{PS}}N'$ ならば $N<_{\textrm{PS}[]}N'$

を仮定する。このとき $M<_{\textrm{PS}[]}N$。

$\Phi(N)$ が原文の内側の帰納法の仮定にあたる。原文の $f=j_1^N$ という場合分けは、この主張の
$(M_j)_{j=0}^{j_1-1}=(N_j)_{j=0}^{j_1-1}$ と $\textrm{Lng}(N)\leq\textrm{Lng}(M)$ に対応する
（$M$ と $N$ が $j_1$ で実際に相違することは使わない）。

**(5-a)** 標準形は空列でないので $\textrm{Lng}(N)=j_1+1>0$、$\textrm{Lng}(N)\leq\textrm{Lng}(M)$ より
$j_1<\textrm{Lng}(M)$。

**(5-b)** 可算な標準形の起源 より $v^M,v^N$ を取って $M\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v^M}$、
$N\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v^N}$。$v=\max(v^M,v^N)$ と置く。$u\leq v$ のとき
$((j,j))_{j=0}^{u}$ は $((j,j))_{j=0}^{v}$ の先頭 $u+1$ 項だから、標準形の始切片への経路 より
$((j,j))_{j=0}^{u}\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v}$。基本列的順序が推移性（$\leq$ 側）より
$M\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v}$ かつ $N\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v}$。

**(5-c)** $\leq_{\textrm{PS}[]}$ の定義より $a\in\mathbb{N}_+^{<\omega}$ が取れて
$M=((j,j))_{j=0}^{v}[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$。

**(5-d)** 反復展開は $\leq_{\textrm{PS}}$ を下げる（原文の 辞書式的順序が基本列的順序を含意すること の
$\leq$ 形）ので、$N\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v}$ から $N\leq_{\textrm{PS}}((j,j))_{j=0}^{v}$。

**(5-e)** $a\neq()$。もし $a=()$ なら $M=((j,j))_{j=0}^{v}$ で、(5-d) より $N\leq_{\textrm{PS}}M$、
$M<_{\textrm{PS}}N$ と合わせて $N<_{\textrm{PS}}N$ となり非反射性に反する。

**(5-f)** 条件「$((j,j))_{j=0}^{v}[a_0]\cdots[a_g]<_{\textrm{PS}}N$」は $g=\textrm{Lng}(a)-1$ で
成り立つ（そのとき左辺は $M$ で、$M<_{\textrm{PS}}N$）。この条件を満たす最小の $g$ を $g_0$ と置く。
最小性から $g_0\leq\textrm{Lng}(a)-1$、すなわち $g_0<\textrm{Lng}(a)$ なので $a_{g_0}$ が存在する。

**(5-g)** $N'=((j,j))_{j=0}^{v}[a_0]\cdots[a_{g_0-1}]$、$m=a_{g_0}\geq1$ と置く。添字列の連結より
$((j,j))_{j=0}^{v}[a_0]\cdots[a_{g_0}]=N'[m]$ であり、$g_0$ の取り方から $N'[m]<_{\textrm{PS}}N$。

**(5-h)** $N'\in CT_{\textrm{PS}}$。$N'=((j,j))_{j=0}^{v}[a_0]\cdots[a_{g_0-1}]$ すなわち
$N'\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v}$ なので、可算な標準形の起源 の逆向きによる。

**(5-i)** $N\leq_{\textrm{PS}}N'$。$g_0=0$ なら $N'=((j,j))_{j=0}^{v}$ で (5-d) そのもの。$g_0>0$ なら
$g_0$ の最小性より $\lnot(N'<_{\textrm{PS}}N)$ であり、辞書式的順序の線形性（三分律）より
$N<_{\textrm{PS}}N'$ か $N=N'$。

**(5-j)** $M\leq_{\textrm{PS}}N'[m]$。$a=(a_j)_{j=0}^{g_0}\oplus_A(a_j)_{j=g_0+1}^{\textrm{Lng}(a)-1}$ と
分けると $M=N'[m][a_{g_0+1}]\cdots[a_{\textrm{Lng}(a)-1}]$ であり、反復展開は $\leq_{\textrm{PS}}$ を下げる。

**(5-k) 挟み撃ち.** 一般に、$M\leq_{\textrm{PS}}K<_{\textrm{PS}}N$、$j_1<\textrm{Lng}(M)$、
$j_1\leq\textrm{Lng}(N)$、$(M_j)_{j=0}^{j_1-1}=(N_j)_{j=0}^{j_1-1}$ ならば
$(K_j)_{j=0}^{j_1-1}=(N_j)_{j=0}^{j_1-1}$ かつ $j_1<\textrm{Lng}(K)$。
$M=K$ なら自明。$M<_{\textrm{PS}}K$ のときは (2-a) で分解する。

- (i)（$M$ が $K$ の真の始切片）なら $\textrm{Lng}(M)<\textrm{Lng}(K)$ で $j_1<\textrm{Lng}(M)$ だから
  $j_1<\textrm{Lng}(K)$、また $(K_j)_{j=0}^{j_1-1}=(M_j)_{j=0}^{j_1-1}=(N_j)_{j=0}^{j_1-1}$。
- (ii) で相違位置 $d<j_1$ のとき: $M$ と $N$ は $j_1$ 未満で一致するから $M_d=N_d$、また
  $(N_j)_{j=0}^{d-1}=(M_j)_{j=0}^{d-1}=(K_j)_{j=0}^{d-1}$。すると (2-b) より $N<_{\textrm{PS}}K$ となり、
  $K<_{\textrm{PS}}N$ と推移性・非反射性で矛盾。
- (ii) で $d\geq j_1$ のとき: $(K_j)_{j=0}^{j_1-1}=(M_j)_{j=0}^{j_1-1}=(N_j)_{j=0}^{j_1-1}$ で、
  $j_1\leq d<\textrm{Lng}(K)$。

これを $K=N'[m]$ に適用する（(5-j) と (5-g)、(5-a)）と、$\textrm{Lng}(N'[m])>j_1$ かつ
$(N'[m]_j)_{j=0}^{j_1-1}=(N_j)_{j=0}^{j_1-1}$ を得る。原文の
「$\textrm{Lng}(N'[a_{g_0}])>j_1^N$ かつ $(M_j)_{j=0}^{j_1^N-1}=(N'[a_{g_0}]_j)_{j=0}^{j_1^N-1}$」に対応する。

**(5-l)** $(N'[m]_j)_{j=0}^{j_1}<_{\textrm{PS}}N$。$N'[m]<_{\textrm{PS}}N$ を (2-a) で分解する。
$\textrm{Lng}(N)=j_1+1\leq\textrm{Lng}(N'[m])$ なので (i) は起きない。(ii) の相違位置 $d$ は
$d<\textrm{Lng}(N)=j_1+1$ であり、$d<j_1$ なら (5-k) の一致から $N'[m]_d=N_d$ となって
「$N'[m]_d$ が $N_d$ より対の辞書式に小さい」に反するので $d=j_1$。よって $(N'[m]_j)_{j=0}^{j_1}$ と $N$ は
$j_1$ 未満で一致し $j_1$ で対の辞書式に小さいから、(2-b) より結論を得る。

**(5-m)** 任意の $n\in\mathbb{N}_+$ に対して $N'[n]<_{\textrm{PS}}N$。$\textrm{Lng}(N'[n])$ で場合分けする。

- $\textrm{Lng}(N'[n])\leq j_1$ のとき。まず $n\leq m$ である。実際 $m<n$ とすると、基本列の切片の不変性の
  基になる「$m\leq n$ なら $N'[n]$ は $N'[m]$ を接頭辞にもつ」より
  $\textrm{Lng}(N'[n])\geq\textrm{Lng}(N'[m])>j_1$ となり矛盾する。$n\leq m$ なら同じ接頭辞性より
  $N'[n]=(N'[m]_j)_{j=0}^{\textrm{Lng}(N'[n])-1}$ で、$\textrm{Lng}(N'[n])\leq j_1<j_1+1$ だからこれは
  $(N'[m]_j)_{j=0}^{j_1}$ の真の始切片である。(2-c) より
  $N'[n]<_{\textrm{PS}}(N'[m]_j)_{j=0}^{j_1}$、(5-l) と推移性で $N'[n]<_{\textrm{PS}}N$。
- $\textrm{Lng}(N'[n])>j_1$ のとき。$n,m\geq1$ で $j_1+1$ が両方の長さ以下だから、上の接頭辞性を
  $\min(n,m)$ と $\max(n,m)$ に使って $(N'[n]_j)_{j=0}^{j_1}=(N'[m]_j)_{j=0}^{j_1}$（基本列の切片の不変性）。
  (5-l) より右辺は $<_{\textrm{PS}}N$ で、$\textrm{Lng}(N)=j_1+1$ だから (2-d) より $N'[n]<_{\textrm{PS}}N$。

**(5-n)** $N=N'$。(5-i) より $N<_{\textrm{PS}}N'$ か $N=N'$ である。$N<_{\textrm{PS}}N'$ とすると、
(5-h) と $\Phi(N)$ より $N<_{\textrm{PS}[]}N'$、すなわち $c\neq()$、$c\in\mathbb{N}_+^{<\omega}$ が取れて
$N=N'[c_0]\cdots[c_{\textrm{Lng}(c)-1}]$。$c_0\geq1$ であり $N$ は $N'[c_0]$ の反復展開だから
$N\leq_{\textrm{PS}}N'[c_0]$（$\textrm{Lng}(c)=1$ のときは等号）。一方 (5-m) より
$N'[c_0]<_{\textrm{PS}}N$。合わせて $N<_{\textrm{PS}}N$ となり非反射性に反する。

**(5-o)** $M=N'[a_{g_0}]\cdots[a_{\textrm{Lng}(a)-1}]=N[a_{g_0}]\cdots[a_{\textrm{Lng}(a)-1}]$ であり、
$(a_j)_{j=g_0}^{\textrm{Lng}(a)-1}$ は (5-f) の $g_0<\textrm{Lng}(a)$ より空でなく、その各項は $1$ 以上。
よって $M<_{\textrm{PS}[]}N$。

**(6) 帰納法本体と結論**

$L$ を固定し、$S_L$ 上の下降帰納 (3-d) で $\Phi_L$ を示す。$X\in S_L$ を取り、$S_L$ の中で $X$ より
$<_{\textrm{PS}}$ で真に上の元すべてで $\Phi_L$ が成り立つと仮定する。$N\in CT_{\textrm{PS}}$、
$\textrm{Lng}(N)\leq L$、$X<_{\textrm{PS}}N$ とし、(2-a) で分解する。

- (i) なら (1-d) より $X<_{\textrm{PS}[]}N$。
- (ii) の $f$ に対して $\tilde N=(N_j)_{j=0}^{f}$ と置く。(1-b) より $\tilde N\in CT_{\textrm{PS}}$、
  $\textrm{Lng}(\tilde N)=f+1\leq\textrm{Lng}(X)\leq L$ なので $\tilde N\in S_L$、また (2-b) より
  $X<_{\textrm{PS}}\tilde N$。すなわち $\tilde N$ は $S_L$ の中で $X$ より真に上にあるから、
  帰納法の仮定が $\tilde N$ に使えて $\Phi_L(\tilde N)$ を得る。相手の長さ制限は (4) で外れて、
  $\Phi(\tilde N)$（任意の $N_3\in CT_{\textrm{PS}}$ に対して $\tilde N<_{\textrm{PS}}N_3$ ならば
  $\tilde N<_{\textrm{PS}[]}N_3$）が出る。ここで
  $\textrm{Lng}(\tilde N)-1=f$ かつ $(X_j)_{j=0}^{f-1}=(\tilde N_j)_{j=0}^{f-1}$ かつ
  $\textrm{Lng}(\tilde N)\leq\textrm{Lng}(X)$ だから、(5) の仮定がすべて揃い $X<_{\textrm{PS}[]}\tilde N$。
  (1-c) の $\tilde N\leq_{\textrm{PS}[]}N$ と (1-a) を合わせて $X<_{\textrm{PS}[]}N$。

最後に、任意の $M,N\in CT_{\textrm{PS}}$ と $M<_{\textrm{PS}}N$ に対して、$L=\textrm{Lng}(M)$ と置き、
(4) により相手を $\textrm{Lng}(N)\leq L$ の場合に帰着してから $\Phi_L(M)$ を使えば $M<_{\textrm{PS}[]}N$
を得る。$\square$

## 原文通りに書けなかった理由

- **[R]** 外側の $\textrm{Lng}(M)$ に関する帰納法が丸ごと要らない

  原文は $j_1^M=0$ を基底段階、$j_1^M>0$ を帰納段として $\textrm{Lng}(M)$ についての強帰納法を
  組んでいる（「$j_1^M>0$ ならば、任意の $M',N'\in CT_{\textrm{PS}}$ に対して
  $\textrm{Lng}(M')<\textrm{Lng}(M)$ かつ $M'<_{\textrm{PS}}N'$ ならば $M'<_{\textrm{PS}[]}N'$ であると
  仮定する」）。しかしこの帰納法の仮定は、以降の証明のどの一行でも使われていない。
  基底段階も、$j_1^M=0$ すなわち $M=((0,0))$ のときは $M$ が $N$ の真の始切片になるので、
  (2-a) の (i) の場合に吸収される。したがってこの形式化には外側の帰納法が無く、
  下降帰納 (3-d) ただ一つで証明が閉じている。

- **[W]** 標準形の始切片への経路 を狭義で使う 2 箇所で、狭義性を作り直す一手が要る

  原文は $M=(N_j)_{j=0}^{j_1^M}$ から 標準形の始切片への経路 で直ちに $M<_{\textrm{PS}[]}N$ を
  得ている。しかしこの補題の結論は $\leq_{\textrm{PS}[]}$ であって $<_{\textrm{PS}[]}$ ではない
  （$j_1'=j_1$ のとき原文の逐語形は $M<_{\textrm{PS}[]}M$ を主張してしまう）。原文自身、後の
  $((j,j))_{j=0}^{v^M}\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v}$ では $\leq$ で使っている。
  そこで (1-d) では、$\leq_{\textrm{PS}[]}$ から取った $a$ について「$a=()$ なら $X=N$ となり
  $\textrm{Lng}(X)<\textrm{Lng}(N)$ に反する」という一手を足して狭義性を回復している。

- **[Y]** 「高々 $(j_1^N)^2$ 個である」は偽

  $\textrm{Lng}(M')=\textrm{Lng}(N)$ かつ $(M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}$ である $M'$ は
  最後の対 $(M'_{0,j_1^N},M'_{1,j_1^N})$ だけで決まり、$M'_{1,j_1^N}\leq M'_{0,j_1^N}\leq j_1^N$ から
  候補は $(j_1^N+1)(j_1^N+2)/2$ 個以下である。これは $j_1^N\leq3$ では $(j_1^N)^2$ を上回る。
  実際 $j_1^N=1$（$\textrm{Lng}(N)=2$、$N_0=(0,0)$）では
  $((0,0),(0,0))$、$((0,0),(1,0))$、$((0,0),(1,1))$ の 3 個がいずれも $CT_{\textrm{PS}}$ に属し
  （$((0,0),(1,1))=((j,j))_{j=0}^{1}$、$((0,0),(1,0))=((j,j))_{j=0}^{1}[2]$、
  $((0,0),(0,0))=((j,j))_{j=0}^{1}[2][2]$）、$(j_1^N)^2=1$ を超える。
  もっとも原文がこの評価から使うのは有限性だけなので、個数を直せば下流は変わらない。
  この形式化は個数を数えず、(3-c) で $S_L$ の有限性を示している。

- **[Z]** 内側の下降帰納に基底段階が無い

  原文の内側の帰納法は、有限集合
  $S=\lbrace M'\in CT_{\textrm{PS}}\mid\textrm{Lng}(M')=\textrm{Lng}(N)\land(M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}\rbrace$
  の上での $<_{\textrm{PS}}$ に関する下降帰納である（仮定は「$N\leq_{\textrm{PS}}M'$ なる $M'$ について
  結論が既知」、段は「$S$ の中で $N$ の直下にある最大元 $M'$ について結論を導く」）。下降帰納には
  $S$ の $<_{\textrm{PS}}$-最大元 $X$ での基底段階が要るが、$X$ より上の元は $S$ に無いので帰納法の
  仮定が使えず、しかも結論「任意の $N'\in CT_{\textrm{PS}}$ に対して $X<_{\textrm{PS}}N'$ ならば
  $X<_{\textrm{PS}[]}N'$」は $N'$ が $S$ の外を動くので自明ではない。原文はこの段階を扱っていない。
  ここでは帰納の台を $S$ から $S_L=\lbrace X\in CT_{\textrm{PS}}\mid\textrm{Lng}(X)\leq L\rbrace$（$L=\textrm{Lng}(M)$）
  に取り替えた。相手 $N$ の長さは (4) の帰着で $\textrm{Lng}(X)$ 以下に落ちるので台の外に出ず、
  $S_L$ の最大元では $X<_{\textrm{PS}}N$ なる $N$ が台の中に無いので主張が空虚に成り立ち、
  基底段階が自動的に閉じる。台の有限性の根拠は原文と同じ係数評価 (3-a) である。
  この取り替えにより、原文の「$\textrm{Lng}(M')=\textrm{Lng}(N)$ かつ先頭 $j_1^N$ 項が一致」という
  台の記述と、そこに付いていた個数評価が全て置き換わっている。

- **[W]** $g_0$ の取り方の境界（$a=()$ と $g_0=0$）が確かめられていない

  原文は $M=((j,j))_{j=0}^{v}[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\leq_{\textrm{PS}}N\leq_{\textrm{PS}}((j,j))_{j=0}^{v}$
  から直ちに $g$ の存在を述べるが、$a=()$ ならそもそも $[a_g]$ が取れない。(5-e) で
  「$a=()$ なら $M=((j,j))_{j=0}^{v}$ かつ $N\leq_{\textrm{PS}}M<_{\textrm{PS}}N$ で矛盾」を補った。
  また原文は「辞書式的順序の線形性及び $g_0$ の定義より $N\leq_{\textrm{PS}}N'$」とするが、$g_0=0$ の
  ときは $g_0$ の最小性が何も言わないので、この推論は $g_0>0$ でしか通らない。(5-i) で
  $g_0=0$ の場合を分け、そこでは $N'=((j,j))_{j=0}^{v}$ なので (5-d) をそのまま使っている。

- **[W]** $N'$ と $(N_j)_{j=0}^{f}$ が $CT_{\textrm{PS}}$ に属することが確かめられていない

  原文は内側の帰納法の仮定を「任意の $M',N'\in CT_{\textrm{PS}}$ に対して」の形で置いているので、
  $N'$ に適用するには $N'\in CT_{\textrm{PS}}$ が要る。また最後の帰着で $N$ を $(N_j)_{j=0}^{f}$ に
  置き替えるときも、置き替えた列が $CT_{\textrm{PS}}$ に属していなければ前段の結論を使えない。
  原文はどちらも確かめていない（[1] の 標準形の始切片への遺伝性 を引くのは別の箇所である）。
  ここでは (5-h) で $N'\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v}$ と 可算な標準形の起源 の逆向きから
  $N'\in CT_{\textrm{PS}}$ を、(1-b) で [1] の 標準形の始切片への遺伝性 と最左列の不変性から
  $(N_j)_{j=0}^{f}\in CT_{\textrm{PS}}$ を示している。

- **[Y]** $M<_{\textrm{PS}}N'[a_{g_0}]$ は $\leq_{\textrm{PS}}$ が正しい

  $M=N'[a_{g_0}][a_{g_0+1}]\cdots[a_{\textrm{Lng}(a)-1}]$ なので、$g_0=\textrm{Lng}(a)-1$ のときは
  $M=N'[a_{g_0}]$ であり狭義にはならない。$g_0=\textrm{Lng}(a)-1$ は実際に起こりうる（$a$ の最後の
  1 手で初めて $N$ を下回る場合）。$<_{\textrm{PS}}$ を $\leq_{\textrm{PS}}$ に直せばよく、下流で
  この不等式を使うのは (5-k) の挟み撃ちだけで、そこは $\leq_{\textrm{PS}}$ で足りる。
  (5-j) では反復展開が $\leq_{\textrm{PS}}$ を下げることから $M\leq_{\textrm{PS}}N'[a_{g_0}]$ を得ている。

- **[W]** 「上より $\textrm{Lng}(N'[a_{g_0}])>j_1^N$ かつ …」の一行は場合分けを隠している

  原文はこの一行を「上より」で済ませているが、$M\leq_{\textrm{PS}}N'[a_{g_0}]<_{\textrm{PS}}N$ と
  $M$ が $N$ と $j_1^N$ 未満で一致することから $N'[a_{g_0}]$ の長さと接頭辞を読み取るには、
  $M$ と $N'[a_{g_0}]$ の関係の場合分けが要る。(5-k) では $M=N'[a_{g_0}]$、$M$ が真の始切片、
  最初の相違位置が $j_1^N$ 未満、$j_1^N$ 以上、の 4 通りに分け、3 番目は
  $N<_{\textrm{PS}}N'[a_{g_0}]<_{\textrm{PS}}N$ の矛盾で潰している。

- **[W]** $N'[n]$ が $N'[a_{g_0}]$ の始切片であるためには $n\leq a_{g_0}$ が要る

  原文は $\textrm{Lng}(N'[n])\leq j_1^N$ の場合に 基本列の切片の不変性 から
  $N'[n]=(N'[a_{g_0}]_j)_{j=0}^{\textrm{Lng}(N'[n])-1}$ としているが、この接頭辞性は
  $n\leq a_{g_0}$ のときにしか言えない。(5-m) では、$a_{g_0}<n$ なら接頭辞性から
  $\textrm{Lng}(N'[n])\geq\textrm{Lng}(N'[a_{g_0}])>j_1^N$ となって場合の仮定に反する、として
  $n\leq a_{g_0}$ を先に出している。

- **[W]** 「任意の $n$ について $N<_{\textrm{PS}[]}N'[n]$ でない、従って $N<_{\textrm{PS}[]}N'$ でない」は
  展開の長さが $1$ の場合を落としている

  $N<_{\textrm{PS}[]}N'$ とは $c\neq()$ が取れて $N=N'[c_0]\cdots[c_{\textrm{Lng}(c)-1}]$ ということだが、
  $\textrm{Lng}(c)=1$ のときは $N=N'[c_0]$ であって $N<_{\textrm{PS}[]}N'[c_0]$ ではないので、原文の
  推論はこの場合を覆わない。(5-n) では $\leq_{\textrm{PS}}$ に落として
  「$N\leq_{\textrm{PS}}N'[c_0]$ かつ $N'[c_0]<_{\textrm{PS}}N$ より $N<_{\textrm{PS}}N$」と
  非反射性で矛盾を出しており、$\textrm{Lng}(c)=1$ も含めて閉じている。

- **[R]** 結論の $\leq_{\textrm{PS}}$ 単調形への強化と、$S$ の直下の最大元へ進む段が要らない

  原文は $M<_{\textrm{PS}[]}N$ を得たあと、内側の帰納法の仮定と 基本列的順序が推移性 で
  「任意の $N'\in CT_{\textrm{PS}}$ に対して $N\leq_{\textrm{PS}}N'$ ならば $M<_{\textrm{PS}[]}N'$」と
  結論を強め、さらに $S$ の中で $N$ の直下にある最大元 $M'$ を取って、$M'<_{\textrm{PS}}O<_{\textrm{PS}}N$
  なる $O$ について $(O_j)_{j=0}^{j_1^N}=M'$（[1] の 標準形の始切片への遺伝性 と $M'$ の最大性）から
  $M'\leq_{\textrm{PS}[]}O$ を導いて、$M'$ についての主張を作っている。
  下降帰納 (3-d) は $X$ より上の元すべてについての仮定を一度に与えるので、この「直下の最大元へ
  一段進む」議論は不要であり、結論を $\leq_{\textrm{PS}}$ 単調形に強める必要も無い。
  最後の帰着 (4) では $\tilde N\leq_{\textrm{PS}}N$ ではなく $\tilde N\leq_{\textrm{PS}[]}N$ で繋ぐので、
  強化した形は使わずに済む。したがって原文のこの段（$M'$ の最大性、$O$ についての議論、
  そこでの [1] の 標準形の始切片への遺伝性 の引用）に対応する Lean の宣言は無い。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $M<_{\textrm{PS}}N$ | `ltPS` | `lean/Bijectivity/Defs.lean` |
| $M\leq_{\textrm{PS}}N$ | `lePS` | 同上 |
| $N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ | `expand` | 同上 |
| $M\leq_{\textrm{PS}[]}N$ | `leExpPS` | 同上 |
| $M<_{\textrm{PS}[]}N$ | `ltExpPS` | 同上 |
| $CT_{\textrm{PS}}$ | `CTPS` | 同上 |
| $M[n]$ | `PSS.oper` | `lean/PSS/Defs.lean` |
| $M_{i,j}$ | `PSS.entry` | 同上 |
| $(M_j)_{j=0}^{k-1}$（先頭 $k$ 項） | `List.take k M`（閉区間形 `PSS.seg` との変換は `seg_zero_eq_take`） | `lean/PSS/Defs.lean` |
| $((j,j))_{j=u}^{v}$ | `PSS.diagSeq` | `lean/PSS/Red.lean` |
| $M_j$（第 $j$ 成分の対） | `pairAt`（`pairAt_eq_getElem`, `pairAt_take`） | `lean/Bijectivity/12a-lex-toolkit.lean` |
| 対の辞書式比較 | `pairLt`（`pairLt_irrefl`） | 同上 |
| (1-a) 混合推移性 | `ltExpPS_leExpPS_trans` | `lean/Bijectivity/12-lex-implies-exp.lean` |
| (1-b) 始切片の $CT_{\textrm{PS}}$ 性 | `ctps_take` | 同上 |
| (1-c) 標準形の始切片への経路（切片形） | `take_leExpPS_of_lt` | 同上 |
| (1-d) 真の始切片は狭義に下 | `ltExpPS_of_take` | 同上 |
| (2-a) $<_{\textrm{PS}}$ の分解 | `ltPS_dest_idx`（`ltPS_dest` 経由） | `lean/Bijectivity/12a-lex-toolkit.lean` |
| (2-b) 逆向き | `ltPS_of_agree`（`ltPS_cons`） | 同上 |
| (2-c) 真の始切片は小さい | `ltPS_take` | `lean/Bijectivity/02b-lex-list-lemmas.lean` |
| (2-d) 切片が小さければ本体も小さい | `ltPS_of_take_ltPS` | `lean/Bijectivity/12a-lex-toolkit.lean` |
| 共通接頭辞の消去 | `ltPS_append_cancel` | `lean/Bijectivity/02b-lex-list-lemmas.lean` |
| 辞書式的順序の線形性 | `ltPS_irrefl`, `ltPS_trans`, `ltPS_trichotomy` | `lean/Bijectivity/02-lex-linear.lean` |
| $M_0=(0,0)$ の成分表示 | `ctps_entry_zero` | `lean/Bijectivity/12b-ctps-finite.lean` |
| (3-a) 係数評価 $M_{1,j}\leq M_{0,j}\leq j$ | `ctps_coeff` | 同上 |
| (3-b) 範囲外込みの係数評価 | `ctps_entry_le` | 同上 |
| (3-c) $S_L$ の有限性 | `ctps_finite` | 同上 |
| (3-d) 下降帰納の整礎性 | `ctps_wf` | 同上 |
| [1] 標準形の簡約性 | `PSS.STPS_RTPS` | `lean/6/6.7-standard-reduced.lean` |
| [1] 簡約性と条件(A)(B) | `PSS.RTPS_condAB` | `lean/6/6.6-reduced-iff-condAB.lean` |
| [1] 簡約性と係数の関係 | `PSS.reduced_coeff` | `lean/6/6.6-reduced-coeff.lean` |
| [1] 条件(A)からの上段の評価 | `PSS.RedCondA_row0_le_index` | `lean/6/6.6-condAB-coeff.lean` |
| [1] 標準形の始切片への遺伝性 | `PSS.STPS_prefix` | `lean/6/6.7-standard-prefix.lean` |
| 標準形が空列でないこと | `PSS.STPS_TPS` | 同上 |
| 標準形の始切片への経路（訂正形） | `seg_leExpPS`, `seg_zero_eq_take` | `lean/Bijectivity/11-path-to-initial-segment.lean` |
| 可算な標準形の起源 | `ctps_iff_leExpPS` | `lean/Bijectivity/10-countable-standard-origin.lean` |
| 基本列的順序が推移性（$\leq$ 側） | `leExpPS_trans` | `lean/Bijectivity/03-exp-order-transitive.lean` |
| 添字列の連結 | `expand_append` | 同上 |
| 反復展開は $\leq_{\textrm{PS}}$ を下げる | `expand_lePS` | `lean/Bijectivity/05-exp-implies-lex.lean` |
| 基本列の切片の不変性（接頭辞形） | `oper_prefix` | `lean/Bijectivity/06-fseq-segment-invariance.lean` |
| (4) 相手の長さの帰着 | `reduce_to_bounded` | `lean/Bijectivity/12-lex-implies-exp.lean` |
| (5) 主要部 | `big_step` | `lean/Bijectivity/12c-big-step.lean` |
| 対角列の長さと始切片 | `length_diagSeq`, `diagSeq_take` | 同上 |
| (5-b) 対角列への 標準形の始切片への経路 | `diagSeq_leExpPS` | 同上 |
| $\leq_{\textrm{PS}}$ と $<_{\textrm{PS}}$ の合成 | `lePS_ltPS_trans` | 同上 |
| (5-k) 挟み撃ち | `sandwich_agree` | 同上 |
| (5-l) $(N'[m]_j)_{j=0}^{j_1}<_{\textrm{PS}}N$ | `take_last_ltPS` | 同上 |
| (5-m) 基本列の切片の一致（切片形） | `oper_take_eq`, `oper_eq_take` | 同上 |
| (6) 下降帰納の本体 | `ltPS_ltExpPS_bounded` | `lean/Bijectivity/12-lex-implies-exp.lean` |
| 原文の命題 | `ltPS_ltExpPS` | 同上 |
| 原文の個数評価「高々 $(j_1^N)^2$ 個」 | なし | — |
| 原文の $M'$ の最大性と $O$ についての段 | なし | — |

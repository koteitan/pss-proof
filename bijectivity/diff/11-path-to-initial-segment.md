[< back](README.md)

# 11: 補題 (標準形の始切片への経路)

## 原文

### 命題

補題 (標準形の始切片への経路)

任意の $M\in ST_{\textrm{PS}}$ と $j_1'\in\mathbb{N}$ に対し、$j_1=\textrm{Lng}(M)-1$ と置くと、$j_1'\leq j_1$ ならば $(M_j)_{j=0}^{j_1'}<_{\textrm{PS}[]}M$ である。

### 証明

[1] の $\textrm{Pred}$ が $[1]$ で表されることより、帰納法により $(M_j)_{j=0}^{j_1'}=\textrm{Pred}^{j_1-j_1'}(M)=M[1]^{j_1-j_1'}<_{\textrm{PS}[]}M$ であるから、$(M_j)_{j=0}^{j_1'}<_{\textrm{PS}[]}M$ である。□

## Lean

### Lean での命題

2 つの命題が置かれている。

**(a) 逐語形の反証。**

$$\lnot\ \Bigl(\forall M\in ST_{\textrm{PS}},\ \forall j_1'\in\mathbb{N},\ j_1'\leq\textrm{Lng}(M)-1\ \Rightarrow\ (M_j)_{j=0}^{j_1'}<_{\textrm{PS}[]}M\Bigr)$$

**(b) 訂正形（結論を $\leq_{\textrm{PS}[]}$ に弱めたもの）。**

$$\forall M\in T_{\textrm{PS}},\ \forall j_1'\in\mathbb{N},\ j_1'\leq\textrm{Lng}(M)-1\ \Rightarrow\ (M_j)_{j=0}^{j_1'}\leq_{\textrm{PS}[]}M$$

ここで $\leq_{\textrm{PS}[]}$、$<_{\textrm{PS}[]}$ は原文どおり、
$M\leq_{\textrm{PS}[]}N$ を「ある $a\in\mathbb{N}_+^{<\omega}$ が存在して $M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$」、
$<_{\textrm{PS}[]}$ をさらに $a\neq()$ を課したもの、として定式化してある。
仮定は $M\in ST_{\textrm{PS}}$ ではなく $M\in T_{\textrm{PS}}$（$M\neq()$）である。

以下、$M\!\restriction\!k$ で $M$ の先頭 $k$ 項からなる列（$k>\textrm{Lng}(M)$ なら $M$ 自身）を表す。

### Lean での証明

証明は補助命題 2 つを経る。

**補助 1（始切片は先頭切片である）.**
$j+1\leq\textrm{Lng}(M)$ ならば $(M_j)_{j=0}^{j}=M\!\restriction\!(j+1)$。

長さと各成分の一致で示す。左辺は定義上 $j+1-0=j+1$ 個の添字 $0,1,\dots,j$ に
$(M_{0,j},M_{1,j})$ を対応させた列なので長さ $j+1$、右辺の長さは
$\min(j+1,\textrm{Lng}(M))=j+1$（仮定より）。
成分については、$i<j+1$ をとると仮定から $i<\textrm{Lng}(M)$ であり、
左辺の第 $i$ 項は $(M_{0,i},M_{1,i})$、右辺の第 $i$ 項は $M_i$ である。
$M_{i,j}$ の定式化は「$M$ の第 $j$ 項が存在すればその第 $i$ 成分、無ければ $0$」なので、
$i<\textrm{Lng}(M)$ の下で $(M_{0,i},M_{1,i})=M_i$ となり一致する。

**補助 2（反復 $\textrm{Pred}$ による経路）.**
任意の $k\in\mathbb{N}$ と $M\in T_{\textrm{PS}}$ に対し、$k<\textrm{Lng}(M)$ ならば
$M\!\restriction\!(\textrm{Lng}(M)-k)\leq_{\textrm{PS}[]}M$。

$k$ についての帰納法。ここが原文の「帰納法により」に対応する箇所である。

- $k=0$ のとき。$M\!\restriction\!\textrm{Lng}(M)=M$ である。添字列として $a=()$ をとれば、
  「$a$ の全成分が $1$ 以上」は空虚に真、かつ $M=M[\,]$（空の反復展開）なので
  $\leq_{\textrm{PS}[]}$ の定義を満たす。$M\in T_{\textrm{PS}}$ も $k<\textrm{Lng}(M)$ も使わない。
- $k+1$ のとき。仮定 $k+1<\textrm{Lng}(M)$ から $\textrm{Lng}(M)>1$。この下で
  1. $\textrm{Lng}(\textrm{Pred}(M))=\textrm{Lng}(M)-1$（$\textrm{Pred}$ は $\textrm{Lng}(M)>1$ のとき末尾 1 項を落とす）。
  2. $\textrm{Pred}(M)\in T_{\textrm{PS}}$。実際 $\textrm{Pred}(M)=()$ とすると
     $\textrm{Lng}(\textrm{Pred}(M))=0$ だが、1 と $k+1<\textrm{Lng}(M)$ より
     $\textrm{Lng}(\textrm{Pred}(M))=\textrm{Lng}(M)-1\geq 1$ で矛盾する。
  3. 帰納法の仮定を $k$ と $\textrm{Pred}(M)$ に適用する。適用条件
     $k<\textrm{Lng}(\textrm{Pred}(M))=\textrm{Lng}(M)-1$ は $k+1<\textrm{Lng}(M)$ から従う。得られるのは
     $$\textrm{Pred}(M)\!\restriction\!\bigl(\textrm{Lng}(\textrm{Pred}(M))-k\bigr)\ \leq_{\textrm{PS}[]}\ \textrm{Pred}(M).$$
  4. 一歩ぶんの経路 $\textrm{Pred}(M)\leq_{\textrm{PS}[]}M$ を作る。[1] の「$\textrm{Pred}$ が $[1]$ で
     表されること」（$M\in T_{\textrm{PS}}$ と $\textrm{Lng}(M)>1$ を要する）より
     $\textrm{Pred}(M)=M[1]$ であり、$n\geq1$ なら添字列 $a=(n)$ をとって
     $M[n]\leq_{\textrm{PS}[]}M$ なので、$n=1$ として $\textrm{Pred}(M)=M[1]\leq_{\textrm{PS}[]}M$。
  5. 3 の左辺を $M$ の切片に書き換える。$\textrm{Lng}(\textrm{Pred}(M))=\textrm{Lng}(M)-1$ と
     $\textrm{Pred}(M)=M\!\restriction\!(\textrm{Lng}(M)-1)$、および切片の合成則
     $(M\!\restriction\!a)\!\restriction\!b=M\!\restriction\!\min(a,b)$ より
     $$\textrm{Pred}(M)\!\restriction\!\bigl(\textrm{Lng}(M)-1-k\bigr)
       =M\!\restriction\!\min\bigl(\textrm{Lng}(M)-1-k,\ \textrm{Lng}(M)-1\bigr)
       =M\!\restriction\!\bigl(\textrm{Lng}(M)-(k+1)\bigr).$$
     最後の等号は自然数の切り算（$0$ 止まりの引き算）についての算術で、
     $\textrm{Lng}(M)-1-k\leq\textrm{Lng}(M)-1$ から $\min$ が左に決まることによる。
  6. 3 を 5 で書き換えたものと 4 を、$\leq_{\textrm{PS}[]}$ の推移性（原文の命題（基本列的順序が推移性））で
     つないで $M\!\restriction\!(\textrm{Lng}(M)-(k+1))\leq_{\textrm{PS}[]}M$ を得る。

**(b) 訂正形の証明.**
$M\in T_{\textrm{PS}}$ から $\textrm{Lng}(M)>0$（$M$ が空でないので場合分けで直ちに出る）。
仮定 $j_1'\leq\textrm{Lng}(M)-1$ と合わせて $j_1'+1\leq\textrm{Lng}(M)$。
補助 1 より $(M_j)_{j=0}^{j_1'}=M\!\restriction\!(j_1'+1)$ なので、目標は
$M\!\restriction\!(j_1'+1)\leq_{\textrm{PS}[]}M$ になる。
補助 2 を $k=\textrm{Lng}(M)-(j_1'+1)$ で使う。適用条件 $k<\textrm{Lng}(M)$ は
$\textrm{Lng}(M)>0$ から従う。得られる式の切片の長さは
$\textrm{Lng}(M)-\bigl(\textrm{Lng}(M)-(j_1'+1)\bigr)=j_1'+1$（$j_1'+1\leq\textrm{Lng}(M)$ による）なので、
そのまま目標と一致する。この $k$ が原文の $j_1-j_1'$ にあたる。

**(a) 逐語形の反証.**
まず補助として、$\textrm{Lng}(M)>1$ ならば $M<_{\textrm{PS}[]}M$ は偽であることを示す。
$M<_{\textrm{PS}[]}M$ とすると、$\textrm{Lng}(N)>1$ を補った形の命題（辞書式的順序が
基本列的順序を含意すること）、すなわち「$\textrm{Lng}(N)>1$ かつ $M<_{\textrm{PS}[]}N$ ならば
$M<_{\textrm{PS}}N$」を $N=M$ に適用して $M<_{\textrm{PS}}M$ が出るが、
これは系（辞書式的順序の線形性）の非反射性に反する。

反例は $M=((j,j))_{j=0}^{1}=((0,0),(1,1))$、$j_1'=1$ である。

- $M\in ST_{\textrm{PS}}$: $ST_{\textrm{PS}}$ の生成規則のうち「$u\leq v$ なら $((j,j))_{j=u}^{v}\in ST_{\textrm{PS}}$」を
  $u=0$、$v=1$ で使う。
- $j_1'=1\leq\textrm{Lng}(M)-1=1$: 有限計算で確かめられる。
- $(M_j)_{j=0}^{1}=M$: 有限計算で確かめられる。
- $\textrm{Lng}(M)=2>1$: 有限計算で確かめられる。

よって逐語形を $M$、$j_1'=1$ に適用すると $M<_{\textrm{PS}[]}M$ が出て、上の補助に矛盾する。

## 原文通りに書けなかった理由

- **[Y]** 逐語形の結論 $<_{\textrm{PS}[]}$ は偽であり、$\leq_{\textrm{PS}[]}$ が正しい

  仮定は $j_1'\leq j_1$ なので $j_1'=j_1$ が許される。このとき
  $(M_j)_{j=0}^{j_1'}=M$ なので、原文の結論は $M<_{\textrm{PS}[]}M$ を主張することになる。
  $<_{\textrm{PS}[]}$ は「$a\neq()$ なる $a\in\mathbb{N}_+^{<\omega}$ が存在して
  $M=M[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$」であり、$\textrm{Lng}(M)>1$ のときは
  $M[1]=\textrm{Pred}(M)\neq M$ で、以降どれだけ展開しても $M$ には戻らないので偽である。
  Lean では $M=((0,0),(1,1))\in ST_{\textrm{PS}}$、$j_1'=1$ を反例として、
  逐語形（$M\in ST_{\textrm{PS}}$ という原文どおりの仮定を付けたまま）の否定を証明してある。
  訂正は $<_{\textrm{PS}[]}$ を $\leq_{\textrm{PS}[]}$ に置き換えるだけで、証明の筋は変わらない
  （帰納法の基底が「空の添字列」になる）。下流でこの補題が狭義の $<_{\textrm{PS}[]}$ で
  使われる箇所は、$\leq_{\textrm{PS}[]}$ の形と「$<_{\textrm{PS}[]}$ と $\leq_{\textrm{PS}[]}$ の合成は
  $<_{\textrm{PS}[]}$」で置き換えられる。狭義にしたい場合は仮定を $j_1'<j_1$ とすればよい。

- **[R]** 原文の仮定 $M\in ST_{\textrm{PS}}$ は不要で、$M\in T_{\textrm{PS}}$ で足りる

  証明で使うのは $\textrm{Pred}(M)=M[1]$（$M\in T_{\textrm{PS}}$ と $\textrm{Lng}(M)>1$ のみを要する）と
  $M[n]\leq_{\textrm{PS}[]}M$、および $\leq_{\textrm{PS}[]}$ の推移性だけで、標準形性はどこにも現れない。
  Lean の訂正形は $M\neq()$ のみを仮定している。原文の題名（標準形の始切片への経路）と
  仮定の $ST_{\textrm{PS}}$ は、この補題の内容には効いていない。

- **[W]** 原文の「帰納法により」が隠している段が Lean では明示される

  原文は $(M_j)_{j=0}^{j_1'}=\textrm{Pred}^{j_1-j_1'}(M)=M[1]^{j_1-j_1'}<_{\textrm{PS}[]}M$ を
  一行で書くが、Lean では次の 3 つを分けて用意している。
  第一に、始切片 $(M_j)_{j=0}^{j_1'}$ が $M$ の先頭 $j_1'+1$ 項であること（補助 1）。
  原文は始切片と反復 $\textrm{Pred}$ の像を同一視するが、この同一視自体には
  $j_1'+1\leq\textrm{Lng}(M)$ の下での長さと成分の照合が要る。
  第二に、$\textrm{Pred}$ が先頭切片で書けること
  $\textrm{Pred}(M)=M\!\restriction\!(\textrm{Lng}(M)-1)$ と、切片の合成則
  $(M\!\restriction\!a)\!\restriction\!b=M\!\restriction\!\min(a,b)$、およびそこから出る
  $\min(\textrm{Lng}(M)-1-k,\textrm{Lng}(M)-1)=\textrm{Lng}(M)-(k+1)$ という自然数の算術。
  これが「反復 $\textrm{Pred}$ の像＝先頭切片」を帰納の各段でつなぐ。
  第三に、各段の側条件 $\textrm{Lng}(M)>1$ と $\textrm{Pred}(M)\in T_{\textrm{PS}}$ の確認。
  原文はこれらに触れないが、$\textrm{Pred}(M)=M[1]$ の適用に $\textrm{Lng}(M)>1$ が要り、
  帰納法の仮定の適用に $\textrm{Pred}(M)\neq()$ と $k<\textrm{Lng}(\textrm{Pred}(M))$ が要る。
  なお Lean は $\textrm{Pred}^{j_1-j_1'}(M)$ という項自体を作らず、
  $M[1]^{j_1-j_1'}<_{\textrm{PS}[]}M$ を長さ $j_1-j_1'$ の添字列 $(1,\dots,1)$ で一括に作る代わりに、
  一歩ずつ $\leq_{\textrm{PS}[]}$ の推移性で合成している。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $M<_{\textrm{PS}}N$ | `ltPS` | `lean/Bijectivity/Defs.lean` |
| $N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$（反復展開） | `expand` | 同上 |
| $M\leq_{\textrm{PS}[]}N$ | `leExpPS` | 同上 |
| $M<_{\textrm{PS}[]}N$ | `ltExpPS` | 同上 |
| $T_{\textrm{PS}}$ | `PSS.TPS` | `lean/PSS/Defs.lean` |
| $\textrm{Lng}(M)$ | `PSS.Lng` | 同上 |
| $M_{i,j}$ | `PSS.entry` | 同上 |
| $(M_j)_{j=a}^{b}$ | `PSS.seg` | 同上 |
| $\textrm{Pred}(M)$ | `PSS.Pred` | 同上 |
| $M[n]$ | `PSS.oper` | 同上 |
| $ST_{\textrm{PS}}$ | `PSS.STPS` | `lean/PSS/Standard.lean` |
| 対角列は標準形（$u\leq v\Rightarrow((j,j))_{j=u}^{v}\in ST_{\textrm{PS}}$） | `PSS.STPS.diag` | 同上 |
| $((j,j))_{j=a}^{b}$ | `PSS.diagSeq` | `lean/PSS/Red.lean` |
| 補助 1（始切片は先頭切片） | `seg_zero_eq_take` | `lean/Bijectivity/11-path-to-initial-segment.lean` |
| $M\!\restriction\!k$ | `List.take k M`（Mathlib） | なし（Mathlib） |
| 補助 2（反復 $\textrm{Pred}$ による経路） | `take_leExpPS` | `lean/Bijectivity/11-path-to-initial-segment.lean` |
| $\textrm{Lng}(\textrm{Pred}(M))=\textrm{Lng}(M)-1$ | `PSS.length_Pred` | `lean/6/6.5-Red-Pred-commute.lean` |
| $\textrm{Pred}(M)=M\!\restriction\!(\textrm{Lng}(M)-1)$ | `PSS.Pred_eq_take` | 同上 |
| $\textrm{Pred}(M)=M[1]$ | `PSS.pred_is_oper1` | `lean/5/5.3-pred-is-oper1.lean` |
| $M[n]\leq_{\textrm{PS}[]}M$（$n\geq1$） | `oper_leExpPS` | `lean/Bijectivity/09-standard-iff-exp.lean` |
| $\leq_{\textrm{PS}[]}$ の推移性 | `leExpPS_trans` | `lean/Bijectivity/03-exp-order-transitive.lean` |
| $(M\!\restriction\!a)\!\restriction\!b=M\!\restriction\!\min(a,b)$ | `List.take_take`（Mathlib） | なし（Mathlib） |
| $\textrm{Lng}(M)>1\Rightarrow\lnot(M<_{\textrm{PS}[]}M)$ | `ltExpPS_irrefl` | `lean/Bijectivity/11-path-to-initial-segment.lean` |
| 命題（辞書式的順序が基本列的順序を含意すること）の訂正形 | `ltExpPS_ltPS_of_lng` | `lean/Bijectivity/05-exp-implies-lex.lean` |
| $<_{\textrm{PS}}$ の非反射性 | `ltPS_irrefl` | `lean/Bijectivity/02-lex-linear.lean` |
| (a) 逐語形の反証 | `not_seg_ltExpPS` | `lean/Bijectivity/11-path-to-initial-segment.lean` |
| (b) 訂正形（本補題） | `seg_leExpPS` | 同上 |

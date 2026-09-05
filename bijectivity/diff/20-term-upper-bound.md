[< back](README.md)

# 20: 命題 (対応する項の上界)

## 原文

### 命題

命題 (対応する項の上界)（原文に番号は振られていない）

(1) 任意の$M\in CT_{\textrm{PS}}$に対して$\textrm{Trans}(M)<_{\textrm{B}}D_0D_\omega0$である。

(2) 任意の$t\in T_{\textrm{B}}$に対して、$t<_{\textrm{B}}D_0D_\omega0$ならばある$M\in CT_{\textrm{PS}}$が存在して$t<_{\textrm{B}}\textrm{Trans}(M)$である。

### 証明

  証明  
  (1) 可算な標準形の起源より任意の$M\in CT_{\textrm{PS}}$に対してある$v\in\mathbb{N}$が存在して$M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$である。  
  辞書式的順序が基本列的順序を含意することより$M\leq_{\textrm{PS}}((j,j))_{j=0}^v$である。  
  [1]の公差$(1,1)$のペア数列の$\textrm{Trans}$の基本性質より$\textrm{Trans}(((j,j))_{j=0}^v)=D_0D_v0<_{\textrm{B}}D_0D_\omega0$である。  
  $\textrm{Trans}$が順序を保つことより$\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(((j,j))_{j=0}^v)<_{\textrm{B}}D_0D_\omega0$である。□  
  (2) 任意の$t'\in T_{\textrm{B}}$をとる。  
    $t'=0$ならば$t'<_{\textrm{B}}D_00$である。  
    $t'\in PT_{\textrm{B}}$とする。  
      ある$u\in\mathbb{N}$と$a\in OT_{\textrm{B}}$が存在して$t'=D_ua$である。  
      $t'<_{\textrm{B}}D_{u+1}0$である。  
    $t'\in MT_{\textrm{B}}$とする。  
      ある$u\in\mathbb{N}$と$a\in OT_{\textrm{B}}$と$s\in\Sigma^{<\omega}$が存在して$t'=\underline{(}D_ua\underline{,}s\underline{)}$である。  
      $t'<_{\textrm{B}}D_{u+1}0$である。  
    よっていずれの場合でもある$u\in\mathbb{N}$が存在して$t'<_{\textrm{B}}D_u0$である。  
  $t=0$ならば$t<_{\textrm{B}}D_00$である。  
  $t\in PT_{\textrm{B}}$とする。  
    ある$a\in T_{\textrm{B}}$が存在して$t=D_0a$である。  
    上よりある$u\in\mathbb{N}$が存在して$a<_{\textrm{B}}D_u0$である。  
    よってある$u\in\mathbb{N}$が存在して$t<_{\textrm{B}}D_0D_u0$である。  
  $t\in MT_{\textrm{B}}$とする。  
    ある$a\in T_{\textrm{B}}$と$s\in\Sigma^{<\omega}$が存在して$t=\underline{(}D_0a\underline{,}s\underline{)}$である。  
    上よりある$u\in\mathbb{N}$が存在して$a<_{\textrm{B}}D_u0$である。  
    よってある$u\in\mathbb{N}$が存在して$D_0a<_{\textrm{B}}D_0D_u0$である。  
    よってある$u\in\mathbb{N}$が存在して$t<_{\textrm{B}}D_0D_u0$である。  
  よっていずれの場合でもある$u\in\mathbb{N}$が存在して$t<_{\textrm{B}}D_0D_u0$である。  
  [1]の公差$(1,1)$のペア数列の$\textrm{Trans}$の基本性質より$t<_{\textrm{B}}D_0D_u=0\textrm{Trans}(((j,j))_{j=0}^u)=D_0D_u0$である。□

## Lean

### Lean での命題

(1) 任意のペア数列 $M$ に対して

$$M\in CT_{\textrm{PS}}\ \Longrightarrow\ \textrm{Trans}(M)<_{\textrm{B}}D_0D_\omega0$$

(2) 任意の Buchholz 項 $t$ に対して

$$t\in T_{\textrm{B}}\ \land\ t<_{\textrm{B}}D_0D_\omega0\ \Longrightarrow\ \exists M,\ M\in CT_{\textrm{PS}}\land t<_{\textrm{B}}\textrm{Trans}(M)$$

ここで各記号は次のとおりである。

- 項は principal 項の有限列 $\underline{(}p_0\underline{,}\cdots\underline{,}p_{k-1}\underline{)}$ であり、principal 項は添字 $v\in\mathbb{N}\cup\{\omega\}$ と項 $a$ の対 $D_va$ である。$0$ は空列、$D_va$ は 1 要素の列である。$\mathbb{N}\cup\{\omega\}$ は $\omega$ を最大元として付け加えた順序であり、原文の $D_\omega$ の添字はこの最大元である。
- $<_{\textrm{B}}$ は principal 列の辞書式順序であって、次の 4 節と principal 項の比較から成る。

$$()\not<_{\textrm{B}}(),\qquad ()<_{\textrm{B}}(q\frown qs),\qquad (p\frown ps)\not<_{\textrm{B}}(),$$

$$(p\frown ps)<_{\textrm{B}}(q\frown qs):\iff p<_{\textrm{B}}q\ \lor\ (p=q\ \land\ ps<_{\textrm{B}}qs),$$

$$D_ua<_{\textrm{B}}D_vb:\iff u<v\ \lor\ (u=v\ \land\ a<_{\textrm{B}}b)$$

- $\leq_{\textrm{B}}$ は $a<_{\textrm{B}}b\lor a=b$ の略記である。
- $T_{\textrm{B}}$ は「どの深さの添字も $\omega$ でない」という再帰的な判定であり、$\underline{(}p_0\underline{,}\cdots\underline{)}\in T_{\textrm{B}}$ は各 $p_i=D_{v_i}a_i$ について $v_i\neq\omega$ かつ $a_i\in T_{\textrm{B}}$ であることと同値である。
- $D_0D_\omega0$ は 1 要素の列 $\underline{(}D_0(\underline{(}D_\omega0\underline{)})\underline{)}$ である。
- $CT_{\textrm{PS}}$、$\leq_{\textrm{PS}[]}$、$\leq_{\textrm{PS}}$、$<_{\textrm{PS}}$、対角列 $((j,j))_{j=u}^v$、反復展開 $N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ は 10 のページと同じ定義である。
- $\textrm{Trans}$ は [1] の変換写像であり、この形式化では燃料付きの再帰として全域化されている。

原文の $PT_{\textrm{B}}$、$MT_{\textrm{B}}$、$\Sigma^{<\omega}$ に対応する定義は置いていない。項が principal 列そのものなので、単項は「長さ 1 の列」、複項は「先頭 principal と残りの列」であり、場合分けは列が空か非空かだけで済む。

### Lean での証明

まず本命題のために置かれた補助補題を並べる。

**補助補題 A（空列より小さい列は無い）**: 任意の principal 項の有限列 $ps$ に対して $ps<_{\textrm{B}}()$ は偽である。

証明: 右辺が空列である節は $()<_{\textrm{B}}()$ と $(p\frown ps)<_{\textrm{B}}()$ の 2 つだけで、どちらも定義がそのまま偽を与える。$ps$ が空か非空かで場合分けすれば尽くされる。□

**補助補題 B**: 任意の $v\in\mathbb{N}$ に対して $D_0D_v0<_{\textrm{B}}D_0D_\omega0$。

証明: 両辺とも 1 要素の列だから、列の $<_{\textrm{B}}$ の第 4 節により先頭 principal の比較 $D_0(D_v0)<_{\textrm{B}}D_0(D_\omega0)$ に落ちる（第 2 の選択肢は残りの列同士の比較 $()<_{\textrm{B}}()$ が偽なので消える）。principal の比較の定義から、添字は $0=0$ で等しいので引数の比較 $D_v0<_{\textrm{B}}D_\omega0$ に落ち、同じ 2 段でさらに添字の比較 $v<\omega$ に落ちる。$\omega$ は $\mathbb{N}\cup\{\omega\}$ の最大元で $v\in\mathbb{N}$ だから $v<\omega$ である。□

**補助補題 C**: $u<v$ ならば $D_0D_u0<_{\textrm{B}}D_0D_v0$。

証明: 補助補題 B と同じ 2 段の落とし方で、外側の添字が $0=0$、内側が添字の比較 $u<v$ となり仮定そのものである。□

**補助補題 D**: $0<v$ ならば $\textrm{Trans}(((j,j))_{j=0}^v)=D_0D_v0$。

証明: [1] の公差 $(1,1)$ のペア数列の $\textrm{Trans}$ の基本性質

$$u<v\ \Longrightarrow\ \textrm{Trans}(((j,j))_{j=u}^v)=D_uD_v0$$

を $u=0$ に対して使う。差は添字 $0\in\mathbb{N}$ を $\mathbb{N}\cup\{\omega\}$ へ埋め込む変換の正規化だけである。□

**補助補題 E**: 任意の $v\in\mathbb{N}$ に対して $((j,j))_{j=0}^v\in CT_{\textrm{PS}}$。

証明: $CT_{\textrm{PS}}$ は $M\in ST_{\textrm{PS}}$ と $M_0=(0,0)$ の連言である。第 1 肢は $ST_{\textrm{PS}}$ の生成規則「$u\leq v$ ならば $((j,j))_{j=u}^v\in ST_{\textrm{PS}}$」に $u=0$ と $0\leq v$ を与える。第 2 肢は対角列の最左列（$u\leq v$ ならば $(((j,j))_{j=u}^v)_0=(u,u)$）に $0\leq v$ を与える。□

#### (1)

可算な標準形の起源

$$M\in CT_{\textrm{PS}}\iff \exists v\in\mathbb{N},\ M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$$

の $(\Rightarrow)$ を仮定 $M\in CT_{\textrm{PS}}$ に適用して $v$ と $M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$ を取る。ここまでは原文と同じである。

次に上界を 1 段持ち上げる。標準形の始切片への経路（この形式化では結論を $\leq_{\textrm{PS}[]}$ にした訂正形）を対角列に適用した形

$$u\leq v\ \Longrightarrow\ ((j,j))_{j=0}^u\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$$

を $v\leq v+1$ に対して使って $((j,j))_{j=0}^v\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v+1}$ を得、$\leq_{\textrm{PS}[]}$ の推移律と繋いで

$$M\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v+1}$$

とする。以後この $v+1$ 列の対角列を上界として使う（$v$ のままだと補助補題 D の仮定 $0<v$ が満たせない。下記の差異を参照）。補助補題 E から $((j,j))_{j=0}^{v+1}\in CT_{\textrm{PS}}$ である。

続いて

$$\textrm{Trans}(M)\leq_{\textrm{B}}\textrm{Trans}(((j,j))_{j=0}^{v+1})$$

を示す。$\leq_{\textrm{PS}[]}$ の定義から、全項が $1$ 以上の有限列 $a$ で $M=((j,j))_{j=0}^{v+1}[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ なるものを取る。反復展開の非増加性

$$(\forall i,\ 1\leq a_i)\ \Longrightarrow\ N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\leq_{\textrm{PS}}N$$

を $N=((j,j))_{j=0}^{v+1}$ に適用して $M\leq_{\textrm{PS}}((j,j))_{j=0}^{v+1}$ を得る。$\leq_{\textrm{PS}}$ は $M=N$ と $M<_{\textrm{PS}}N$ の選言なので、そこで 2 つに分ける。

- $M=((j,j))_{j=0}^{v+1}$ のとき: 両辺の $\textrm{Trans}$ が同じ項なので $\leq_{\textrm{B}}$ の反射律で済む。
- $M<_{\textrm{PS}}((j,j))_{j=0}^{v+1}$ のとき: $\textrm{Trans}$ が順序を保つこと

  $$M,N\in CT_{\textrm{PS}}\ \land\ M<_{\textrm{PS}}N\ \Longrightarrow\ \textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(N)$$

  を、仮定 $M\in CT_{\textrm{PS}}$ と補助補題 E の $((j,j))_{j=0}^{v+1}\in CT_{\textrm{PS}}$ とともに適用し、狭義の $<_{\textrm{B}}$ を得て $\leq_{\textrm{B}}$ に緩める。

最後に補助補題 D を $0<v+1$ に対して使って右辺を $D_0D_{v+1}0$ に書き換え、

$$\textrm{Trans}(M)\leq_{\textrm{B}}D_0D_{v+1}0$$

とし、補助補題 B の $D_0D_{v+1}0<_{\textrm{B}}D_0D_\omega0$ と、$\leq_{\textrm{B}}$ と $<_{\textrm{B}}$ を繋ぐ推移律（[4] の Lemma 2.1 から出る）で

$$\textrm{Trans}(M)<_{\textrm{B}}D_0D_\omega0$$

を得る。□

#### (2)

原文の $t'$ についての議論を補助主張として先に立てる。

**補助主張**: $t'\in T_{\textrm{B}}$ ならばある $u\in\mathbb{N}$ が存在して $t'<_{\textrm{B}}D_u0$。

証明: $t'$ を principal 列として場合分けする。

- $t'=()$（すなわち $t'=0$）のとき: $u=0$ と取る。$()<_{\textrm{B}}(D_00)$ は列の $<_{\textrm{B}}$ の第 2 節（空列は非空列より小さい）そのものである。
- $t'=(D_wa)\frown r$ のとき（$r$ は残りの principal 列で、$r=()$ が原文の単項、$r\neq()$ が原文の複項に当たる）: $T_{\textrm{B}}$ の判定を先頭 principal と残りの列の連言に展開し、先頭 principal の添字について $w\neq\omega$ を取り出す（$a$ と $r$ についての条件はこの補助主張では使わない）。$w\neq\omega$ より $w=u_0$ なる $u_0\in\mathbb{N}$ が取れる。$u=u_0+1$ と置く。目標 $((D_{u_0}a)\frown r)<_{\textrm{B}}(D_{u_0+1}0)$ は列の $<_{\textrm{B}}$ の第 4 節で先頭 principal の比較 $D_{u_0}a<_{\textrm{B}}D_{u_0+1}0$ に落ち、principal の比較の第 1 の選択肢である添字の比較 $u_0<u_0+1$ で成り立つ。$r$ が空か非空かは使わない。□

**主張**: $t\in T_{\textrm{B}}$ かつ $t<_{\textrm{B}}D_0D_\omega0$ ならばある $u\in\mathbb{N}$ が存在して $t<_{\textrm{B}}D_0D_u0$。

証明: $t$ を principal 列として場合分けする。

- $t=()$ のとき: $u=0$ と取る。$()<_{\textrm{B}}(D_0D_00)$ は列の $<_{\textrm{B}}$ の第 2 節そのもので、原文のように $D_00$ を経由しない。
- $t=(D_wa)\frown r$ のとき: 補助主張と同様に $T_{\textrm{B}}$ の判定を展開し、先頭 principal から $w\neq\omega$（よって $w=u_0\in\mathbb{N}$）と $a\in T_{\textrm{B}}$ を取り出す（$r$ についての条件は使わない）。

  次に先頭の添字が $0$ であることを仮定 $t<_{\textrm{B}}D_0D_\omega0$ から出す。右辺は 1 要素の列 $(D_0(D_\omega0))$ なので、列の $<_{\textrm{B}}$ の第 4 節から

  $$D_{u_0}a<_{\textrm{B}}D_0(D_\omega0)\quad\text{または}\quad\bigl(D_{u_0}a=D_0(D_\omega0)\ \land\ r<_{\textrm{B}}()\bigr)$$

  であり、後者は補助補題 A で消える。前者を principal の比較の定義で開くと

  $$u_0<0\quad\text{または}\quad\bigl(u_0=0\ \land\ a<_{\textrm{B}}D_\omega0\bigr)$$

  となる。$\mathbb{N}\cup\{\omega\}$ で $0$ は最小元だから $u_0<0$ は偽であり、よって $u_0=0$ である。同時に得られる $a<_{\textrm{B}}D_\omega0$ はこの先で使わない（原文もこれを使わない）。

  そこで補助主張を $a\in T_{\textrm{B}}$ に適用して $u\in\mathbb{N}$ と $a<_{\textrm{B}}D_u0$ を取る。目標 $((D_0a)\frown r)<_{\textrm{B}}(D_0D_u0)$ は列の $<_{\textrm{B}}$ の第 4 節で先頭 principal の比較 $D_0a<_{\textrm{B}}D_0(D_u0)$ に落ち、principal の比較の第 2 の選択肢（添字が $0=0$ で等しく引数が $a<_{\textrm{B}}D_u0$）で成り立つ。ここでも $r$ が空か非空かは使わない。□

主張で得た $u$ に対して $M=((j,j))_{j=0}^{u+1}$ と置く。補助補題 E から $M\in CT_{\textrm{PS}}$ である。補助補題 D を $0<u+1$ に対して使って $\textrm{Trans}(M)=D_0D_{u+1}0$、補助補題 C を $u<u+1$ に対して使って $D_0D_u0<_{\textrm{B}}D_0D_{u+1}0$ を得、[4] の Lemma 2.1（$<_{\textrm{B}}$ の推移律）で主張の $t<_{\textrm{B}}D_0D_u0$ と繋いで

$$t<_{\textrm{B}}\textrm{Trans}(M)$$

を得る。□

## 原文通りに書けなかった理由

- **[W]** [1] の公差 $(1,1)$ の性質は $u<v$ を要するので、原文の $v=0$（1 列の対角列）では使えない

  原文は (1) で $\textrm{Trans}(((j,j))_{j=0}^v)=D_0D_v0$、(2) の最終行で $D_0D_u0=\textrm{Trans}(((j,j))_{j=0}^u)$ と書くが、この等式の根拠である [1] の性質は $u<v$（少なくとも 2 列）を仮定しており、$v=0$ や $u=0$ では適用できない。実際 $((j,j))_{j=0}^0=((0,0))$ に対する値は $\textrm{Trans}(((0,0)))=0$ であって $D_0D_00$ ではない。この形式化では上界を 1 段持ち上げて回避する。(1) では標準形の始切片への経路を対角列に適用した形と $\leq_{\textrm{PS}[]}$ の推移律で $M\leq_{\textrm{PS}[]}((j,j))_{j=0}^{v+1}$ にしてから補助補題 D を $0<v+1$ で使い、(2) では $M=((j,j))_{j=0}^{u+1}$ を証拠に取り、原文には無い一歩 $D_0D_u0<_{\textrm{B}}D_0D_{u+1}0$（補助補題 C）を挟んで $t<_{\textrm{B}}\textrm{Trans}(M)$ に繋ぐ。

- **[W]** (1) の「辞書式的順序が基本列的順序を含意することより$M\leq_{\textrm{PS}}((j,j))_{j=0}^v$」は狭義の命題を広義の仮定に当てている

  引かれている命題は $M<_{\textrm{PS}[]}N\Rightarrow M<_{\textrm{PS}}N$ という狭義同士の主張であって、直前に得ている広義の $M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$（展開の添字列が空でもよい）には直接は当たらない。等号の場合を別に処理する一歩が要る。この形式化では代わりに広義版の補題（反復展開の非増加性 $N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\leq_{\textrm{PS}}N$）を使う。これは添字列の長さに関する帰納で無条件に成り立ち、$\textrm{Lng}(N)>1$ のような側条件を必要としない。

- **[Y]** (1) の最終行 $\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(((j,j))_{j=0}^v)$ は $M$ が対角列自身のとき偽

  直前に得られているのは広義の $M\leq_{\textrm{PS}}((j,j))_{j=0}^v$ であり、$M=((j,j))_{j=0}^v$ が排除されていない。そのとき両辺は同じ項なので $<_{\textrm{B}}$ は成り立たない（$<_{\textrm{B}}$ は非反射的）。$<_{\textrm{B}}$ を $\leq_{\textrm{B}}$ に直し、最後の $D_0D_v0<_{\textrm{B}}D_0D_\omega0$ と繋ぐところだけ狭義にすれば直る機械的な訂正なので誤記の類とみなす。この形式化では $\leq_{\textrm{PS}}$ を等号と狭義に分け、等号側は $\leq_{\textrm{B}}$ の反射律、狭義側は $\textrm{Trans}$ が順序を保つことで処理し、最後に $\leq_{\textrm{B}}$ と $<_{\textrm{B}}$ を繋ぐ推移律で結論する。

- **[Y]** (2) の $t'$ についての議論で成分を $a\in OT_{\textrm{B}}$ としているのはそのままでは偽

  そこでの仮定は $t'\in T_{\textrm{B}}$ だけであり、$t'$ が順序数項であるとは仮定されていないので、成分 $a$ が $OT_{\textrm{B}}$ に属する保証は無い。例えば $t'=D_0(\underline{(}D_00\underline{,}D_10\underline{)})$ は $\omega$ を含まない単項な項だが、成分 $\underline{(}D_00\underline{,}D_10\underline{)}$ は principal 成分が広義降順でないので順序数項ではない。原文自身、後半の $t$ についての分解では $a\in T_{\textrm{B}}$ と正しく書いている。$OT_{\textrm{B}}$ を $T_{\textrm{B}}$ に置き換えるだけの機械的な訂正で、この $a$ は $t'$ についての議論のどこでも使われないため下流も変わらない。この形式化では終始 $T_{\textrm{B}}$ で通している。

- **[R]** (2) の単項と複項の場合分けは要らなかった

  原文は $t'$ についての議論でも $t$ についての議論でも $PT_{\textrm{B}}$ と $MT_{\textrm{B}}$ を分けて同じ議論を 2 度書くが、どちらの比較も列の $<_{\textrm{B}}$ の第 4 節で先頭 principal の比較に落ちてしまい、残りの列 $r$（原文の $s$）が空か非空かは一度も使われない。この形式化では列が空か非空かだけで分け、非空の枝ひとつで単項と複項の両方を処理する。

- **[W]** (2) の「$t\in PT_{\textrm{B}}$とする。ある$a\in T_{\textrm{B}}$が存在して$t=D_0a$である」は先頭の添字が $0$ である根拠を書いていない

  $t\in T_{\textrm{B}}$ から出るのは先頭 principal の添字が $\omega$ でないこと、すなわち $t=(D_{u_0}a)\frown r$（$u_0\in\mathbb{N}$）までで、$u_0=0$ は仮定 $t<_{\textrm{B}}D_0D_\omega0$ からしか出ない。この形式化ではその導出を明示する。右辺が 1 要素の列であることから列の $<_{\textrm{B}}$ の第 4 節を開き、残りの列を比べる選択肢は補助補題 A（$r<_{\textrm{B}}()$ は偽）で潰し、先頭 principal の比較を principal の定義で開いて $u_0<0$ か $u_0=0$ に分け、$0$ が最小元であることから前者を潰す。補助補題 A はこのためだけに立てたもので、原文には対応物が無い。

- **[W]** (2) の $t=0$ の枝が出す上界 $D_00$ は結論の形 $D_0D_u0$ になっていない

  原文は「$t=0$ならば$t<_{\textrm{B}}D_00$である」と書いた直後に「よっていずれの場合でもある$u\in\mathbb{N}$が存在して$t<_{\textrm{B}}D_0D_u0$である」と結ぶが、$D_00$ は $D_0D_u0$ の形ではないので、この枝だけ $D_00<_{\textrm{B}}D_0D_00$ のような一歩が抜けている。この形式化では $u=0$ を取り、$0=()$ が非空列より小さいという列の $<_{\textrm{B}}$ の第 2 節から $t<_{\textrm{B}}D_0D_00$ を直接示して、原文の $D_00$ を経由しない。

- **[W]** (2) は $((j,j))_{j=0}^u\in CT_{\textrm{PS}}$ を確かめていない

  (2) の結論は $M\in CT_{\textrm{PS}}$ なる $M$ の存在なので、証拠として出す対角列がその元であることが要る。原文は最終行で $\textrm{Trans}(((j,j))_{j=0}^u)$ に書き換えて終わり、この確認に触れていない。この形式化では補助補題 E を立て、$ST_{\textrm{PS}}$ の生成規則（$0\leq v$ なる対角列は標準形）と対角列の最左列（$(((j,j))_{j=0}^v)_0=(0,0)$）から示している。

- **[Y]** (2) の最終行の $D_0D_u=0\textrm{Trans}(((j,j))_{j=0}^u)$ は $0$ と $=$ が入れ替わっている

  文脈から意図されているのは $D_0D_u0=\textrm{Trans}(((j,j))_{j=0}^u)$ である。字面の入れ替えを直すだけの誤記で、この形式化では（上の $u+1$ への持ち上げを別にすれば）この等式の向きどおりに補助補題 D を使っている。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| 命題 (対応する項の上界)(1) | `trans_lt_bound` | `lean/Bijectivity/20-term-upper-bound.lean` |
| 命題 (対応する項の上界)(2) | `exists_trans_gt` | 同上 |
| 補助主張（$T_{\textrm{B}}$ の項はある $D_u0$ 未満） | `exists_index_bound` | 同上 |
| 補助補題 A（空列より小さい列は無い） | `lessBPList_nil_right` | 同上 |
| 補助補題 B | `DD_lt_DDomega` | 同上 |
| 補助補題 C | `DD_mono` | 同上 |
| 補助補題 D | `Trans_diagSeq_zero` | 同上 |
| 補助補題 E | `ctps_diagSeq` | 同上 |
| 項、principal 項 | `PSS.BT`、`PSS.BP` | `lean/Buchholz-1986/Buchholz-1986-2.1.lean` |
| $0$（空列） | `PSS.BZero` | 同上 |
| $D_va$ | `PSS.Dprin v a` | 同上 |
| $<_{\textrm{B}}$（項、principal 列、principal 項） | `PSS.lessBT`、`PSS.lessBPList`、`PSS.lessBP` | 同上 |
| $\leq_{\textrm{B}}$ | `PSS.leBT` | 同上 |
| $\mathbb{N}\cup\{\omega\}$ と最大元 $\omega$ | `ℕ∞` と `⊤` | なし（Mathlib） |
| 添字が $\omega$ でないことの分解 | `WithTop.ne_top_iff_exists` | なし（Mathlib） |
| $T_{\textrm{B}}$（判定は各添字が $\omega$ でないこと） | `PSS.T_B`、`PSS.dfree_BT` | `lean/Buchholz-1986/Buchholz-1986-2.2.lean` |
| $D_0D_\omega0$ | `DzeroDomegaZero` | `lean/Bijectivity/Cited.lean` |
| [4] の Lemma 2.1（$<_{\textrm{B}}$ の推移律） | `PSS.lessBT_linear_trans` | `lean/Buchholz-1986/Buchholz-1986-2.1-order.lean` |
| $\leq_{\textrm{B}}$ の反射律 | `leBT_refl` | `lean/Bijectivity/18-trans-preserves-order.lean` |
| $\leq_{\textrm{B}}$ と $<_{\textrm{B}}$ を繋ぐ推移律 | `leBT_lessBT_trans` | 同上 |
| $\textrm{Trans}$ が順序を保つこと | `trans_lessBT_of_ltPS` | 同上 |
| $\textrm{Trans}$ | `PSS.Trans` | `lean/PSS/Trans.lean` |
| [1] の公差 $(1,1)$ のペア数列の $\textrm{Trans}$ の基本性質 | `PSS.diagSeq_Trans` | `lean/8/8.1-diagSeq-Trans.lean` |
| $M\in CT_{\textrm{PS}}$ | `CTPS M` | `lean/Bijectivity/Defs.lean` |
| $M\leq_{\textrm{PS}[]}N$ | `leExpPS M N` | 同上 |
| $M\leq_{\textrm{PS}}N$、$M<_{\textrm{PS}}N$ | `lePS M N`、`ltPS M N` | 同上 |
| $N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ | `expand N a` | 同上 |
| $((j,j))_{j=u}^v$ | `PSS.diagSeq u v` | `lean/PSS/Red.lean` |
| $M\in ST_{\textrm{PS}}$ と生成規則 | `PSS.STPS`、`PSS.STPS.diag` | `lean/PSS/Standard.lean` |
| 可算な標準形の起源 | `ctps_iff_leExpPS` | `lean/Bijectivity/10-countable-standard-origin.lean` |
| 対角列の最左列 | `headD_diagSeq` | 同上 |
| 標準形の始切片への経路を対角列に適用した形 | `diagSeq_leExpPS` | `lean/Bijectivity/12c-big-step.lean` |
| 標準形の始切片への経路（訂正形） | `seg_leExpPS` | `lean/Bijectivity/11-path-to-initial-segment.lean` |
| $\leq_{\textrm{PS}[]}$ の推移律 | `leExpPS_trans` | `lean/Bijectivity/03-exp-order-transitive.lean` |
| 反復展開の非増加性 | `expand_lePS` | `lean/Bijectivity/05-exp-implies-lex.lean` |

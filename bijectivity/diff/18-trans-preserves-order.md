[< back](README.md)

# 18: 命題 (Transが順序を保つこと)

## 原文

### 命題

命題 ($\textrm{Trans}$が順序を保つこと)

任意の $M,N\in CT_{\textrm{PS}}$ に対して、$M<_{\textrm{PS}}N$ ならば $\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(N)$ である。

### 証明

基本列的順序が辞書式的順序を含意することより $M<_{\textrm{PS}[]}N$ である。

$<_{\textrm{PS}[]}$ の定義よりある $a\in\mathbb{N}_+^{<\omega}\setminus\lbrace()\rbrace$ が存在して $M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ である。

任意の $((0,0))$ は $<_{\textrm{PS}}$ に対して $T_{\textrm{PS}}$ の最小の要素であるから、$N\neq(0,0)$ である。

上より $\textrm{Lng}(N)>1$ である。

任意の非負整数 $i<\textrm{Lng}(a)$ に対して $Q_0=N$、$Q_{i+1}=Q_i[a_i]$ とする。

[1]の基本列の降下性より $\textrm{Trans}(Q_1)=\textrm{Trans}(N[a_0])<_{\textrm{B}}\textrm{Trans}(N)$ である。

任意の非負整数 $1\leq i<\textrm{Lng}(a)$ をとり、$\textrm{Trans}(Q_i)<_{\textrm{B}}\textrm{Trans}(N)$ とすると、[1]の基本列の降下性及び[4]のLemma 2.1より $\textrm{Trans}(Q_{i+1})\leq_{\textrm{B}}\textrm{Trans}(Q_i)<_{\textrm{B}}\textrm{Trans}(N)$ である。

帰納法により任意の非負整数 $1\leq i<\textrm{Lng}(a)$ に対して $\textrm{Trans}(Q_i)<_{\textrm{B}}\textrm{Trans}(N)$ である。

よって $\textrm{Trans}(M)=\textrm{Trans}(Q_{\textrm{Lng}(a)})<_{\textrm{B}}\textrm{Trans}(N)$ である。□

## Lean

### Lean での命題

$$\forall M,N\in CT_{\textrm{PS}},\quad M<_{\textrm{PS}}N\ \Longrightarrow\ \textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(N)$$

命題そのものは原文どおりである。$CT_{\textrm{PS}}$ は原文の定義
$CT_{\textrm{PS}}=\lbrace M\mid M\in ST_{\textrm{PS}}\land M_0=(0,0)\rbrace$ をそのまま、
$<_{\textrm{PS}}$ も原文の再帰的定義をそのまま形式化したものを使う。
$\leq_{\textrm{B}}$ は $t\leq_{\textrm{B}}u\iff(t<_{\textrm{B}}u\lor t=u)$ である。

原文がこの証明で外部から引く 2 つの事実は、この形式化ではどちらも引用ではなく
証明済みの定理として使う。すなわち [1] の基本列の降下性

$$M\in ST_{\textrm{PS}},\ n\geq1,\ \textrm{Lng}(M)>1\ \Longrightarrow\ \textrm{Trans}(M[n])<_{\textrm{B}}\textrm{Trans}(M)$$

は未証明の仮定を一切含まない形で証明されており、[4] の Lemma 2.1 のうちここで使う
$<_{\textrm{B}}$ の推移律も証明されている。

### Lean での証明

証明は補助 4 つを経る。

**補助 A（$\leq_{\textrm{B}}$ の小道具、[4] の Lemma 2.1）.**
$\leq_{\textrm{B}}$ は $t\leq_{\textrm{B}}u\iff(t<_{\textrm{B}}u\lor t=u)$ と定義されているので、
次の 3 つが場合分けだけで出る。原文が「[4]のLemma 2.1より」と一言で済ませている部分にあたる。

1. 反射律: 任意の $t$ に対し $t\leq_{\textrm{B}}t$。定義の第 2 項 $t=t$ による。
2. $\leq_{\textrm{B}}$ と $<_{\textrm{B}}$ の合成: $s\leq_{\textrm{B}}t$ かつ $t<_{\textrm{B}}u$ ならば $s<_{\textrm{B}}u$。
   $s\leq_{\textrm{B}}t$ を定義で開き、$s<_{\textrm{B}}t$ の場合は [4] の Lemma 2.1（$<_{\textrm{B}}$ の推移律）を
   $s,t,u$ に適用、$s=t$ の場合は仮定 $t<_{\textrm{B}}u$ がそのまま結論。
3. $\leq_{\textrm{B}}$ の推移律: $s\leq_{\textrm{B}}t$ かつ $t\leq_{\textrm{B}}u$ ならば $s\leq_{\textrm{B}}u$。
   両方を定義で開き、$s<_{\textrm{B}}t\land t<_{\textrm{B}}u$ なら推移律で $s<_{\textrm{B}}u$、
   $s<_{\textrm{B}}t\land t=u$ なら $s<_{\textrm{B}}u$、$s=t$ なら $t\leq_{\textrm{B}}u$ がそのまま結論。

**補助 B（長さ 1 以下では基本列は恒等）.**
$\textrm{Lng}(Q)\leq1$ ならば任意の $n$ に対し $Q[n]=Q$。

基本列 $M[n]$ の定義は $j_1=\textrm{Lng}(M)-1$ を置き、場合分けの先頭で
「$j_1=0$ ならば $M[n]=M$」と定めている。$\textrm{Lng}(Q)\leq1$ なら
自然数の切り算（$0$ 止まりの引き算）で $\textrm{Lng}(Q)-1=0$ なので、この分岐が選ばれる。
Lean では反復展開版「$\textrm{Lng}(N)\leq1$ ならば任意の添字列 $a$ に対し
$N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]=N$」を長さ 1 の添字列 $(n)$ に特殊化して得ている。

**補助 C（反復展開に沿った $\textrm{Trans}$ の非増加性）.**
成分がすべて $1$ 以上の任意の添字列 $a\in\mathbb{N}_+^{<\omega}$ と任意の $Q\in ST_{\textrm{PS}}$ に対し

$$\textrm{Trans}(Q[a_0]\cdots[a_{\textrm{Lng}(a)-1}])\ \leq_{\textrm{B}}\ \textrm{Trans}(Q).$$

添字列 $a$ の構造に関する帰納。$Q$ は帰納の中で動かす（一般化する）。

- $a=()$ のとき。空の添字列に沿った反復展開は $Q$ 自身なので、目標は $\textrm{Trans}(Q)\leq_{\textrm{B}}\textrm{Trans}(Q)$
  であり、補助 A の反射律で閉じる。$Q\in ST_{\textrm{PS}}$ も成分条件も使わない。
- $a=(n)\oplus a'$ のとき。まず成分条件から $n\geq1$。
  1. 一歩ぶんの評価 $\textrm{Trans}(Q[n])\leq_{\textrm{B}}\textrm{Trans}(Q)$ を、$\textrm{Lng}(Q)$ で場合分けして作る。
     - $\textrm{Lng}(Q)>1$ のとき。[1] の基本列の降下性を $Q$ と $n$ に適用する。
       適用条件は $Q\in ST_{\textrm{PS}}$（仮定）、$n\geq1$、$\textrm{Lng}(Q)>1$ の 3 つで、
       結論は $\textrm{Trans}(Q[n])<_{\textrm{B}}\textrm{Trans}(Q)$。これから $\leq_{\textrm{B}}$ の定義の第 1 項として
       $\textrm{Trans}(Q[n])\leq_{\textrm{B}}\textrm{Trans}(Q)$ を得る。
     - $\textrm{Lng}(Q)\leq1$ のとき。補助 B より $Q[n]=Q$ なので、目標は
       $\textrm{Trans}(Q)\leq_{\textrm{B}}\textrm{Trans}(Q)$ に落ち、補助 A の反射律で閉じる。
       ここでは降下性は使えない（使えば $\textrm{Lng}(Q)>1$ が要る）。
  2. 帰納法の仮定を添字列 $a'$ と数列 $Q[n]$ に適用する。適用条件は 2 つあり、
     $Q[n]\in ST_{\textrm{PS}}$ は $ST_{\textrm{PS}}$ の生成規則「標準形の正の基本列は標準形」を
     $Q\in ST_{\textrm{PS}}$ と $n\geq1$ に使って得、$a'$ の各成分が $1$ 以上であることは
     $a'$ の成分がすべて $a$ の成分でもあることから従う。得られるのは
     $$\textrm{Trans}((Q[n])[a'_0]\cdots[a'_{\textrm{Lng}(a')-1}])\ \leq_{\textrm{B}}\ \textrm{Trans}(Q[n]).$$
  3. 反復展開の定義 $Q[a_0]\cdots[a_{\textrm{Lng}(a)-1}]=(Q[n])[a'_0]\cdots[a'_{\textrm{Lng}(a')-1}]$
     で目標の左辺を書き換え、2 と 1 を補助 A の $\leq_{\textrm{B}}$ の推移律でつなぐ。

**補助 D（$\textrm{Lng}(N)>1$）.**
$M,N\in CT_{\textrm{PS}}$ かつ $M<_{\textrm{PS}}N$ ならば $\textrm{Lng}(N)>1$。

$<_{\textrm{PS}}$ を「最初の相違位置」で分解する補題（原文の命題（基本列的順序が
辞書式的順序を含意すること）の証明が使う $f$ による場合分けを、$<_{\textrm{PS}}$ の
定義の言い換えとして切り出したもの）を $M<_{\textrm{PS}}N$ に適用すると、次のいずれかが成り立つ。

$$\textrm{Lng}(M)<\textrm{Lng}(N)\ \land\ M=(N_j)_{j=0}^{\textrm{Lng}(M)-1}$$

$$\exists k,\ k<\textrm{Lng}(M)\ \land\ k<\textrm{Lng}(N)\ \land\ (M_j)_{j=0}^{k-1}=(N_j)_{j=0}^{k-1}\ \land\ M_k<_{\textrm{lex}}N_k$$

ここで $M_k=(M_{0,k},M_{1,k})$、$p<_{\textrm{lex}}q$ は $p_0\lt q_0\lor(p_0=q_0\land p_1\lt q_1)$ である。

- 前者のとき。$M\in CT_{\textrm{PS}}$ より $M\in ST_{\textrm{PS}}$、標準形は空列でない（$M\in T_{\textrm{PS}}$）ので
  $\textrm{Lng}(M)\geq1$、よって $\textrm{Lng}(N)>\textrm{Lng}(M)\geq1$。
- 後者のとき。背理法で $\textrm{Lng}(N)\leq1$ とすると $k<\textrm{Lng}(N)\leq1$ から $k=0$。
  $N\in CT_{\textrm{PS}}$ の第 2 条件 $N_0=(0,0)$（Lean では $N$ が空列でないことから
  $N_{0,0}=0$ かつ $N_{1,0}=0$ として取り出す）より $N_k=N_0=(0,0)$ なので、
  $M_0<_{\textrm{lex}}(0,0)$ となる。しかし $p<_{\textrm{lex}}(0,0)$ は $p_0<0$ または
  ($p_0=0$ かつ $p_1<0$) であり、自然数では両方とも偽。矛盾。

**主張の証明.**

1. 原文と同じく、命題（基本列的順序が辞書式的順序を含意すること）を
   $M,N\in CT_{\textrm{PS}}$ と $M<_{\textrm{PS}}N$ に適用して $M<_{\textrm{PS}[]}N$ を得る。
   $<_{\textrm{PS}[]}$ の定義（ある添字列 $a$ が存在して $a\neq()$ かつ $a$ の各成分が $1$ 以上かつ
   $M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$）を開いて、その $a$ を取る。
2. 補助 D より $\textrm{Lng}(N)>1$。ここが原文の
   「$((0,0))$ が最小元だから $N\neq((0,0))$、上より $\textrm{Lng}(N)>1$」に対応する箇所である。
3. $a$ を先頭で分解する。$a=()$ は $a\neq()$ に反するので、$a=(n)\oplus a'$ と書ける。
   成分条件から $n\geq1$。
4. [1] の基本列の降下性を $N$ と $n$ に適用する。適用条件は $N\in ST_{\textrm{PS}}$
   （$N\in CT_{\textrm{PS}}$ の第 1 条件）、$n\geq1$（3 より）、$\textrm{Lng}(N)>1$（2 より）で、
   $$\textrm{Trans}(N[n])<_{\textrm{B}}\textrm{Trans}(N).$$
   これが原文の $\textrm{Trans}(Q_1)=\textrm{Trans}(N[a_0])<_{\textrm{B}}\textrm{Trans}(N)$ である。
5. 補助 C を添字列 $a'$ と数列 $N[n]$ に適用する。適用条件は
   $N[n]\in ST_{\textrm{PS}}$（$ST_{\textrm{PS}}$ の生成規則を $N\in ST_{\textrm{PS}}$ と $n\geq1$ に使う）と
   $a'$ の各成分が $1$ 以上であることで、
   $$\textrm{Trans}((N[n])[a'_0]\cdots[a'_{\textrm{Lng}(a')-1}])\ \leq_{\textrm{B}}\ \textrm{Trans}(N[n]).$$
   これが原文の $i$ についての帰納法にあたる部分である。
6. 1 で得た $M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ と反復展開の定義
   $N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]=(N[n])[a'_0]\cdots[a'_{\textrm{Lng}(a')-1}]$ で目標を書き換えると、
   目標は $\textrm{Trans}((N[n])[a'_0]\cdots[a'_{\textrm{Lng}(a')-1}])<_{\textrm{B}}\textrm{Trans}(N)$ になる。
   5 と 4 を補助 A の「$\leq_{\textrm{B}}$ と $<_{\textrm{B}}$ の合成」でつないで閉じる。

## 原文通りに書けなかった理由

- **[R]** 原文の「$((0,0))$ は $<_{\textrm{PS}}$ に対して $T_{\textrm{PS}}$ の最小の要素」は使っていない

  原文は $\textrm{Lng}(N)>1$ を、最小元性から $N\neq((0,0))$ を出し、$N\in CT_{\textrm{PS}}$ の
  $N_0=(0,0)$ と合わせて長さが $1$ ではないと結論する、という 2 段で得ている。
  Lean はこの最小元性の補題を持っておらず、補助 D のとおり $<_{\textrm{PS}}$ を最初の相違位置で
  分解した形から直接 $\textrm{Lng}(N)>1$ を出す。使うのは $M$ が空列でないことと
  $N_0=(0,0)$ の 2 つだけで、$T_{\textrm{PS}}$ 全体での最小元性（$M<_{\textrm{PS}}((0,0))$ が
  どんな $M$ でも偽であること、および $((0,0))\leq_{\textrm{PS}}M$）は現れない。
  結論も仮定も原文と同じなので、下流には何も影響しない。

- **[W]** 原文は各段の $\textrm{Lng}(Q_i)>1$ を確かめていない（長さ $1$ では基本列が恒等になる）

  [1] の基本列の降下性は $\textrm{Lng}(M)>1$ を前提にもつ。原文は $i=0$ の段については
  $\textrm{Lng}(N)>1$ を用意しているが、$i\geq1$ の段の $Q_i$ については何も言わずに
  「[1]の基本列の降下性及び[4]のLemma 2.1より」と書く。ところが $\textrm{Lng}(Q_i)=1$ は
  実際に起こりうる。たとえば $N=((0,0),(1,0))\in CT_{\textrm{PS}}$
  （$N=((j,j))_{j=0}^{1}[2]$ なので標準形で、先頭は $(0,0)$）に対し $N[1]=((0,0))$ であり、
  $((0,0))$ は長さ $1$ なので以後どの $n$ で展開しても $((0,0))$ のままである。
  $<_{\textrm{PS}[]}$ の witness $a$ にはこのような冗長な段が入りうるので、
  原文の $Q_i$ の列も長さ $1$ の段を含みうる。このとき降下性は適用できず、
  成り立つのは等号のほうである（原文の結論が $<_{\textrm{B}}$ ではなく $\leq_{\textrm{B}}$ になっているのは
  この場合を含むためだと読めるが、原文はその理由を書いていない）。
  Lean は補助 C の各段で $\textrm{Lng}(Q)>1$ かどうかで場合分けし、真なら降下性、
  偽なら補助 B（$\textrm{Lng}(Q)\leq1\Rightarrow Q[n]=Q$、基本列の定義の $j_1=0$ の分岐）から
  $\leq_{\textrm{B}}$ の反射律で閉じる。

- **[W]** 原文は各段の $Q_i\in ST_{\textrm{PS}}$ を確かめていない

  [1] の基本列の降下性はもう一つ $M\in ST_{\textrm{PS}}$ を前提にもつ。原文は $Q_i$ が標準形で
  あることに触れないまま各段でこれを引く。Lean は補助 C の帰納の各段で
  $ST_{\textrm{PS}}$ の生成規則「$M\in ST_{\textrm{PS}}$ かつ $n\geq1$ ならば $M[n]\in ST_{\textrm{PS}}$」を使って
  $Q\in ST_{\textrm{PS}}$ から $Q[n]\in ST_{\textrm{PS}}$ を作り、帰納の仮定へ渡している。
  $ST_{\textrm{PS}}$ の定義から一歩で出るが、原文には書かれていない段である。

- **[W]** 原文の帰納法の結論の範囲が、最後の行で使う $i=\textrm{Lng}(a)$ を含んでいない

  原文は「帰納法により任意の非負整数 $1\leq i<\textrm{Lng}(a)$ に対して
  $\textrm{Trans}(Q_i)<_{\textrm{B}}\textrm{Trans}(N)$」と書いたうえで、次の行で
  $\textrm{Trans}(M)=\textrm{Trans}(Q_{\textrm{Lng}(a)})<_{\textrm{B}}\textrm{Trans}(N)$ を結論している。
  $i=\textrm{Lng}(a)$ は範囲 $1\leq i<\textrm{Lng}(a)$ の外である。帰納の段の主張
  （$1\leq i<\textrm{Lng}(a)$ で $Q_i$ から $Q_{i+1}$ へ）自体は $i+1=\textrm{Lng}(a)$ まで届くので、
  結論の範囲を $1\leq i\leq\textrm{Lng}(a)$ に直せばよいだけである。
  Lean は添字 $i$ ではなく添字列 $a$ の構造で帰納するため、この範囲は現れない
  （補助 C は $a$ 全体に対する主張で、$a=()$ の場合も含む）。

- **[S]** 帰納法の形が違う（原文は $i$ の前進帰納、Lean は添字列の構造帰納）

  原文の帰納法は $N$ を固定し、不変量 $\textrm{Trans}(Q_i)<_{\textrm{B}}\textrm{Trans}(N)$ を
  $i$ について保つ形で、各段で「一歩ぶんの $\leq_{\textrm{B}}$」と「既に得ている $<_{\textrm{B}}\textrm{Trans}(N)$」を
  合成する。Lean の補助 C は、$Q$ を固定せず一般化した不変量
  $\textrm{Trans}(Q[a_0]\cdots[a_{\textrm{Lng}(a)-1}])\leq_{\textrm{B}}\textrm{Trans}(Q)$ を添字列の構造で示し、
  厳密不等号との合成は最後に一度だけ行う（主張の証明の 6）。
  反復展開が添字列の先頭から再帰的に定義されている
  （$N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ を $a=(n)\oplus a'$ に対し $(N[n])[a'_0]\cdots$ と読む）ため、
  この形のほうが直接書ける。証明されるのは同じ命題で、途中で使う事実も
  [1] の基本列の降下性と [4] の Lemma 2.1 の 2 つだけであり、下流は変わらない。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $M<_{\textrm{PS}}N$ | `ltPS` | `lean/Bijectivity/Defs.lean` |
| $M<_{\textrm{PS}[]}N$ | `ltExpPS` | 同上 |
| $N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$（反復展開） | `expand` | 同上 |
| $CT_{\textrm{PS}}$ | `CTPS` | 同上 |
| $T_{\textrm{PS}}$ | `PSS.TPS` | `lean/PSS/Defs.lean` |
| $\textrm{Lng}(M)$ | `PSS.Lng` | 同上 |
| $M_{i,j}$ | `PSS.entry` | 同上 |
| $M[n]$ | `PSS.oper` | 同上 |
| $ST_{\textrm{PS}}$ | `PSS.STPS` | `lean/PSS/Standard.lean` |
| $M\in ST_{\textrm{PS}}\land n\geq1\Rightarrow M[n]\in ST_{\textrm{PS}}$ | `PSS.STPS.oper` | 同上 |
| $M\in ST_{\textrm{PS}}\Rightarrow M\in T_{\textrm{PS}}$ | `PSS.STPS_TPS` | `lean/6/6.7-standard-prefix.lean` |
| $\textrm{Trans}$ | `PSS.Trans` | `lean/PSS/Trans.lean` |
| $t<_{\textrm{B}}u$ | `PSS.lessBT` | `lean/Buchholz-1986/Buchholz-1986-2.1.lean` |
| $t\leq_{\textrm{B}}u$ | `PSS.leBT` | 同上 |
| [4] の Lemma 2.1（$<_{\textrm{B}}$ の推移律） | `PSS.lessBT_linear_trans` | `lean/Buchholz-1986/Buchholz-1986-2.1-order.lean` |
| 補助 A-1（$\leq_{\textrm{B}}$ の反射律） | `leBT_refl` | `lean/Bijectivity/18-trans-preserves-order.lean` |
| 補助 A-2（$\leq_{\textrm{B}}$ と $<_{\textrm{B}}$ の合成） | `leBT_lessBT_trans` | 同上 |
| 補助 A-3（$\leq_{\textrm{B}}$ の推移律） | `leBT_trans` | 同上 |
| 補助 B（$\textrm{Lng}(Q)\leq1\Rightarrow Q[n]=Q$） | `oper_of_lng_le_one` | 同上 |
| 反復展開版（$\textrm{Lng}(N)\leq1\Rightarrow N[a_0]\cdots=N$） | `expand_of_lng_le_one` | `lean/Bijectivity/05-exp-implies-lex.lean` |
| [1] の基本列の降下性 | `PSS.Trans_fseq_descend` | `lean/8/8.7-termination.lean` |
| 補助 C（反復展開に沿った非増加性） | `trans_leBT_expand` | `lean/Bijectivity/18-trans-preserves-order.lean` |
| 命題（基本列的順序が辞書式的順序を含意すること） | `ltPS_ltExpPS` | `lean/Bijectivity/12-lex-implies-exp.lean` |
| 最初の相違位置による $<_{\textrm{PS}}$ の分解 | `ltPS_dest_idx` | `lean/Bijectivity/12a-lex-toolkit.lean` |
| $M_k=(M_{0,k},M_{1,k})$ | `pairAt` | 同上 |
| $p<_{\textrm{lex}}q$（ペアの比較） | `pairLt` | 同上 |
| $M\in CT_{\textrm{PS}}\Rightarrow M_{0,0}=M_{1,0}=0$ | `ctps_entry_zero` | `lean/Bijectivity/12b-ctps-finite.lean` |
| 補助 D（$\textrm{Lng}(N)>1$） | `one_lt_lng_of_ltPS` | `lean/Bijectivity/18-trans-preserves-order.lean` |
| 本命題 | `trans_lessBT_of_ltPS` | 同上 |

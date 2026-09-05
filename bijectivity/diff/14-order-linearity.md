[← back](README.md)

# 14: 系 (順序の線形性)

## 原文

### 命題

系 (順序の線形性)（原文の命題に通し番号は付いていない）

$\leq_{\textrm{PS}}$ 及び $\leq_{\textrm{PS}[]}$ は $CT_{\textrm{PS}}$ 上で全順序である。

ここに現れる記号は原文の「表記」節で次のように定められている。

$CT_{\textrm{PS}}=\{M\mid M\in ST_{\textrm{PS}}\land M_0=(0,0)\}$ とする。

任意の $M,N\in T_{\textrm{PS}}$ に対して $M\leq_{\textrm{PS}}N$ を $M=N\lor M<_{\textrm{PS}}N$ の略記とする。

$\leq_{\textrm{PS}[]}$ については、原文は表記節に定義を置かず、命題（基本列的順序が推移性）の証明の中で

$\leq_{\textrm{PS}[]}$ の定義より、ある $a\in\mathbb{N}_+^{<\omega}$ が存在して $M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ である。

という形で使っている。

### 証明

証明

辞書式的順序の線形性及び順序の等価性より即座に従う。□

ここで引かれている 2 つは、それぞれ次のものである。

系 (辞書式的順序の線形性): $<_{\textrm{PS}}$ は狭義全順序、$\leq_{\textrm{PS}}$ は全順序である。

系 (順序の等価性): 任意の $M,N\in CT_{\textrm{PS}}$ に対して、$M\leq_{\textrm{PS}}N$ は $M\leq_{\textrm{PS}[]}N$ と同値である。

## Lean

### Lean での命題

Lean で使う定義を先に書く。ペア列は空列を含む $\mathbb{N}^2$ の有限列で、$T_{\textrm{PS}}$ は空でないペア列全体、$ST_{\textrm{PS}}$ は対角列 $((j,j))_{j=u}^v$（$u\leq v$）を含み正の添字による基本列操作 $M\mapsto M[n]$（$n\geq1$）で閉じた最小の述語である。$CT_{\textrm{PS}}$ は原文どおり

$$CT_{\textrm{PS}}(M)\iff M\in ST_{\textrm{PS}}\ \land\ M_0=(0,0)$$

で、先頭ペア $M_0$ は空列のときの既定値を $(0,0)$ として読む。

$\leq_{\textrm{PS}[]}$ は、添字列 $a$ に沿った反復展開

$$\textrm{expand}(N,())=N,\qquad \textrm{expand}(N,n::a)=\textrm{expand}(N[n],a)$$

を使って

$$M\leq_{\textrm{PS}[]}N\iff \exists a\ \bigl((\forall n\in a,\ 1\leq n)\ \land\ M=\textrm{expand}(N,a)\bigr)$$

と定める（原文の $a\in\mathbb{N}_+^{<\omega}$ と $M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ に対応する）。$\leq_{\textrm{PS}}$ は原文どおり $M=N\lor M<_{\textrm{PS}}N$ の略記である。

Lean は原文の「全順序」を反射性・反対称性・推移性・全律の 4 条に開き、$\leq_{\textrm{PS}}$ と $\leq_{\textrm{PS}[]}$ のそれぞれについて述べる。合わせて次の 8 つである。

1. $\leq_{\textrm{PS}}$ の反射性: $M\in CT_{\textrm{PS}}$ ならば $M\leq_{\textrm{PS}}M$
2. $\leq_{\textrm{PS}}$ の反対称性: $M,N\in CT_{\textrm{PS}}$ かつ $M\leq_{\textrm{PS}}N$ かつ $N\leq_{\textrm{PS}}M$ ならば $M=N$
3. $\leq_{\textrm{PS}}$ の推移性: $M,N,O\in CT_{\textrm{PS}}$ かつ $M\leq_{\textrm{PS}}N$ かつ $N\leq_{\textrm{PS}}O$ ならば $M\leq_{\textrm{PS}}O$
4. $\leq_{\textrm{PS}}$ の全律: $M,N\in CT_{\textrm{PS}}$ ならば $M\leq_{\textrm{PS}}N\ \lor\ N\leq_{\textrm{PS}}M$
5. $\leq_{\textrm{PS}[]}$ の反射性: 任意のペア列 $M$ に対して $M\leq_{\textrm{PS}[]}M$（$CT_{\textrm{PS}}$ の仮定は付かない）
6. $\leq_{\textrm{PS}[]}$ の反対称性: $M,N\in CT_{\textrm{PS}}$ かつ $M\leq_{\textrm{PS}[]}N$ かつ $N\leq_{\textrm{PS}[]}M$ ならば $M=N$
7. $\leq_{\textrm{PS}[]}$ の推移性: $M,N,O\in CT_{\textrm{PS}}$ かつ $M\leq_{\textrm{PS}[]}N$ かつ $N\leq_{\textrm{PS}[]}O$ ならば $M\leq_{\textrm{PS}[]}O$
8. $\leq_{\textrm{PS}[]}$ の全律: $M,N\in CT_{\textrm{PS}}$ ならば $M\leq_{\textrm{PS}[]}N\ \lor\ N\leq_{\textrm{PS}[]}M$

このうち 1・3・4・7 では $CT_{\textrm{PS}}$ の仮定が主張に書かれているだけで、証明では使われない。

### Lean での証明

証明が使う 2 つの既出の結果を、Lean での形で書く。

原文の系（辞書式的順序の線形性）は、Lean では $T_{\textrm{PS}}$ への制限すら付かない形、すなわち空列を含む任意のペア列 $M,N,O$ について

- 非反射性: $\lnot\,(M<_{\textrm{PS}}M)$
- $<_{\textrm{PS}}$ の推移性: $M<_{\textrm{PS}}N$ かつ $N<_{\textrm{PS}}O$ ならば $M<_{\textrm{PS}}O$
- 三分律: $M<_{\textrm{PS}}N\ \lor\ M=N\ \lor\ N<_{\textrm{PS}}M$
- $\leq_{\textrm{PS}}$ の反射性・推移性・反対称性・全律

として与えられている。

原文の系（順序の等価性）は、$M,N\in CT_{\textrm{PS}}$ に対する

$$M\leq_{\textrm{PS}}N\iff M\leq_{\textrm{PS}[]}N$$

である。

以下、上の 8 項をこの順に示す。

#### 1. $\leq_{\textrm{PS}}$ の反射性

$CT_{\textrm{PS}}$ の仮定を捨て、全ペア列上の $\leq_{\textrm{PS}}$ の反射性をそのまま適用する。中身は $\leq_{\textrm{PS}}$ の定義の左の選言肢 $M=M$ を取ることである。

#### 2. $\leq_{\textrm{PS}}$ の反対称性

$CT_{\textrm{PS}}$ の仮定を捨て、全ペア列上の $\leq_{\textrm{PS}}$ の反対称性を仮定 $M\leq_{\textrm{PS}}N$、$N\leq_{\textrm{PS}}M$ に適用する。中身は、$M=N$ の枝は結論そのもの、$M<_{\textrm{PS}}N$ かつ $N<_{\textrm{PS}}M$ の枝は $<_{\textrm{PS}}$ の推移性で $M<_{\textrm{PS}}M$ を得て非反射性に反する、というものである。

#### 3. $\leq_{\textrm{PS}}$ の推移性

$CT_{\textrm{PS}}$ の仮定を捨て、全ペア列上の $\leq_{\textrm{PS}}$ の推移性を適用する。中身は 2 つの仮定を $=$ と $<_{\textrm{PS}}$ に分解し、等号の枝はもう一方の仮定をそのまま返し、$<_{\textrm{PS}}$ が 2 つ揃った枝で $<_{\textrm{PS}}$ の推移性を使うというものである。

#### 4. $\leq_{\textrm{PS}}$ の全律

$CT_{\textrm{PS}}$ の仮定を捨て、全ペア列上の $\leq_{\textrm{PS}}$ の全律を適用する。中身は三分律の 3 つの場合をそれぞれ $\leq_{\textrm{PS}}$ の 2 つの選言肢に振り分けることである。

#### 5. $\leq_{\textrm{PS}[]}$ の反射性

$\leq_{\textrm{PS}[]}$ の定義の存在量化子に、添字列として空列 $a=()$ を入れる。示すべき 2 条件は

- $\forall n\in(),\ 1\leq n$: 空列上の全称なので空虚に真。
- $M=\textrm{expand}(M,())$: $\textrm{expand}$ の定義の第 1 節 $\textrm{expand}(N,())=N$ そのものなので、反射律で閉じる。

よって $M\leq_{\textrm{PS}[]}M$。$M\in CT_{\textrm{PS}}$ も $M\in T_{\textrm{PS}}$ も使わない。

#### 6. $\leq_{\textrm{PS}[]}$ の反対称性

系（順序の等価性）を $(M,N)$ に適用し、その $\Leftarrow$ 向き（$\leq_{\textrm{PS}[]}$ から $\leq_{\textrm{PS}}$ へ）を仮定 $M\leq_{\textrm{PS}[]}N$ に使って $M\leq_{\textrm{PS}}N$ を得る。同じ等価性を $(N,M)$ に適用し、同じ向きを仮定 $N\leq_{\textrm{PS}[]}M$ に使って $N\leq_{\textrm{PS}}M$ を得る。この 2 つに全ペア列上の $\leq_{\textrm{PS}}$ の反対称性（上の 2 の中身）を適用して $M=N$。

#### 7. $\leq_{\textrm{PS}[]}$ の推移性

$CT_{\textrm{PS}}$ の仮定を 3 つとも捨て、原文の命題（基本列的順序が推移性）の $\leq_{\textrm{PS}[]}$ 側をそのまま適用する。その中身は次のとおりである。仮定から添字列 $a,b$ を取り出して $M=\textrm{expand}(N,a)$、$N=\textrm{expand}(O,b)$ とする。結論の証人として連結 $b\oplus a$ を取る。

- 成分条件: $n\in b\oplus a$ なら $n\in b$ または $n\in a$ であり、どちらの場合も対応する仮定から $1\leq n$。
- 等式: 添字列の連結について $\textrm{expand}(O,b\oplus a)=\textrm{expand}(\textrm{expand}(O,b),a)$ が $b$ についての帰納法で成り立つ（$b=()$ なら両辺とも $\textrm{expand}(O,a)$、$b=n::b'$ なら両辺とも $\textrm{expand}(O[n],b'\oplus a)$ と $\textrm{expand}(\textrm{expand}(O[n],b'),a)$ に落ちて帰納法の仮定）。これを右辺の $\textrm{expand}(O,b)$ に $N$ を代入した形に使って $M=\textrm{expand}(O,b\oplus a)$。

#### 8. $\leq_{\textrm{PS}[]}$ の全律

まず $CT_{\textrm{PS}}$ の仮定を使わずに、全ペア列上の $\leq_{\textrm{PS}}$ の全律（上の 4 の中身）を $M,N$ に適用して 2 つの場合に分ける。

- $M\leq_{\textrm{PS}}N$ の場合: 系（順序の等価性）を $(M,N)$ に適用し、その $\Rightarrow$ 向き（$\leq_{\textrm{PS}}$ から $\leq_{\textrm{PS}[]}$ へ）で $M\leq_{\textrm{PS}[]}N$。左の選言肢を取る。
- $N\leq_{\textrm{PS}}M$ の場合: 同じ等価性を $(N,M)$ に適用して $N\leq_{\textrm{PS}[]}M$。右の選言肢を取る。

6 は等価性の $\Leftarrow$ 向き、8 は $\Rightarrow$ 向きを使うので、この系の証明には等価性の両向きが要る。

## 原文通りに書けなかった理由

- **[R]** $\leq_{\textrm{PS}[]}$ の反射性と推移性には、原文が挙げる「順序の等価性」が要らない

  原文の証明は材料を 2 つ（辞書式的順序の線形性、順序の等価性）しか挙げておらず、$\leq_{\textrm{PS}[]}$ が全順序であることの 4 条をすべて等価性で $\leq_{\textrm{PS}}$ 側へ移して得る、と読める。Lean で等価性が要るのは反対称性と全律の 2 条だけである。反射性は $\leq_{\textrm{PS}[]}$ の定義の存在量化子に空の添字列を入れるだけで済み、推移性は原文の別の命題（基本列的順序が推移性）の $\leq_{\textrm{PS}[]}$ 側がそのまま結論になる。どちらも $CT_{\textrm{PS}}$ を使わないので、Lean の反射性は $CT_{\textrm{PS}}$ の仮定を外した形（任意のペア列について $M\leq_{\textrm{PS}[]}M$）で述べてあり、推移性は原文の形に合わせて $CT_{\textrm{PS}}$ の仮定を書いたまま証明で捨てている。いずれも原文の主張を含む形なので、下流で使うときに違いは出ない。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| ペア列 | `PSS.PS` | `lean/PSS/Defs.lean` |
| $T_{\textrm{PS}}$ | `PSS.TPS` | 同上 |
| $M[n]$ | `PSS.oper` | 同上 |
| $ST_{\textrm{PS}}$ | `PSS.STPS` | `lean/PSS/Standard.lean` |
| $CT_{\textrm{PS}}$ | `CTPS` | `lean/Bijectivity/Defs.lean` |
| $M\leq_{\textrm{PS}}N$ | `lePS` | 同上 |
| $\textrm{expand}(N,a)$ | `expand` | 同上 |
| $M\leq_{\textrm{PS}[]}N$ | `leExpPS` | 同上 |
| 1. $\leq_{\textrm{PS}}$ の反射性 | `lePS_refl_ctps` | `lean/Bijectivity/14-order-linearity.lean` |
| 2. $\leq_{\textrm{PS}}$ の反対称性 | `lePS_antisymm_ctps` | 同上 |
| 3. $\leq_{\textrm{PS}}$ の推移性 | `lePS_trans_ctps` | 同上 |
| 4. $\leq_{\textrm{PS}}$ の全律 | `lePS_total_ctps` | 同上 |
| 5. $\leq_{\textrm{PS}[]}$ の反射性 | `leExpPS_refl` | 同上 |
| 6. $\leq_{\textrm{PS}[]}$ の反対称性 | `leExpPS_antisymm_ctps` | 同上 |
| 7. $\leq_{\textrm{PS}[]}$ の推移性 | `leExpPS_trans_ctps` | 同上 |
| 8. $\leq_{\textrm{PS}[]}$ の全律 | `leExpPS_total_ctps` | 同上 |
| 系（辞書式的順序の線形性）の $\leq_{\textrm{PS}}$ 側 4 条 | `lePS_refl`, `lePS_antisymm`, `lePS_trans`, `lePS_total` | `lean/Bijectivity/02-lex-linear.lean` |
| $<_{\textrm{PS}}$ の非反射性・推移性・三分律 | `ltPS_irrefl`, `ltPS_trans`, `ltPS_trichotomy` | 同上 |
| 系（順序の等価性） | `lePS_iff_leExpPS` | `lean/Bijectivity/13-order-equivalence.lean` |
| 命題（基本列的順序が推移性）の $\leq_{\textrm{PS}[]}$ 側 | `leExpPS_trans` | `lean/Bijectivity/03-exp-order-transitive.lean` |
| 添字列の連結 | `expand_append` | 同上 |

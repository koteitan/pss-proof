[← back](README.md)

# 09: 補題 (標準形と基本列的順序の関係)

## 原文

### 命題

補題 (標準形と基本列的順序の関係)（原文の命題に番号は付いていない）

任意の $M\in T_{\textrm{PS}}$ に対して、$M\in ST_{\textrm{PS}}$ はある $u,v\in\mathbb{N}$ が存在して $u\leq v$ かつ $M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ であることと同値である。

### 証明

  (⇒) 任意の $u,v\in\mathbb{N}$ に対し、$u\leq v$ ならば $((j,j))_{j=u}^v\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ であるから、任意の $M\in S_0T_{\textrm{PS}}$ に対して、ある $u,v\in\mathbb{N}$ が存在して $u\leq v$ かつ $M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ である。

  任意の $k\in\mathbb{N}$ をとり、任意の $M\in S_kT_{\textrm{PS}}$ に対して、ある $u,v\in\mathbb{N}$ が存在して $u\leq v$ かつ $M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ であると仮定すると、任意の $M\in S_{k+1}T_{\textrm{PS}}$ に対して、ある $N\in S_kT_{\textrm{PS}}$ が存在して $M\leq_{\textrm{PS}[]}N$ であるから、基本列的順序が推移性よりある $u,v\in\mathbb{N}$ が存在して $u\leq v$ かつ $M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ である。

  帰納法により任意の $k\in\mathbb{N}$ に対して、任意の $M\in S_kT_{\textrm{PS}}$ に対して、ある $u,v\in\mathbb{N}$ が存在して $u\leq v$ かつ $M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ である。

  $ST_{\textrm{PS}}=\bigcup_{k\in\mathbb{N}}S_kT_{\textrm{PS}}$ であるから、任意の $M\in ST_{\textrm{PS}}$ に対して、ある $u,v\in\mathbb{N}$ が存在して $u\leq v$ かつ $M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ である。

  (⇐) $\leq_{\textrm{PS}[]}$ の定義よりある $a\in\mathbb{N}_+^{<\omega}$ が存在して $M=((j,j))_{j=u}^v[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ である。

  任意の非負整数 $i<\textrm{Lng}(a)$ に対して $Q_0=((j,j))_{j=u}^v$、$Q_{i+1}=Q_i[a_i]$ とする。

  $Q_0=((j,j))_{j=u}^v\in ST_{\textrm{PS}}$ である。

  任意の非負整数 $k<\textrm{Lng}(a)$ を取り、$Q_k\in ST_{\textrm{PS}}$ であると仮定すると、$Q_{k+1}=Q_k[a_{k+1}]\in ST_{\textrm{PS}}$ である。

  帰納法により任意の非負整数 $k\leq\textrm{Lng}(a)$ に対して、$Q_k\in ST_{\textrm{PS}}$ である。

  よって $M=Q_{\textrm{Lng}(a)}\in ST_{\textrm{PS}}$ である。□

## Lean

### Lean での命題

この形式化で $ST_{\textrm{PS}}$ は、次の 2 つの生成規則で閉じた最小の述語として定められている（本体側の定義を輸入している）。

- $u\leq v$ ならば $((j,j))_{j=u}^v\in ST_{\textrm{PS}}$
- $M\in ST_{\textrm{PS}}$ かつ $1\leq n$ ならば $M[n]\in ST_{\textrm{PS}}$

またこの形式化では、有限列 $a$ に沿った反復展開を $N[a]$ と書き、

$$N[()]=N,\qquad N[(n)\oplus a]=(N[n])[a]$$

で定める。$a=(a_0,\dots,a_{\textrm{Lng}(a)-1})$ に対して $N[a]=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ である。$M\leq_{\textrm{PS}[]}N$ は「ある $a\in\mathbb{N}_+^{<\omega}$（すなわち $a$ の各項が $1$ 以上の有限列）が存在して $M=N[a]$」である。

Lean の命題は次の形である。

任意の有限ペア列 $M$（$M\in T_{\textrm{PS}}$ を仮定しない。空列も含む）に対して

$$M\in ST_{\textrm{PS}}\iff \exists u,v\in\mathbb{N}\ \bigl(u\leq v\ \land\ M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v\bigr)$$

### Lean での証明

補助として 2 つの補題を置く。

**補題 A（一歩展開）**: 任意の有限ペア列 $M$ と $1\leq n$ なる $n$ に対して $M[n]\leq_{\textrm{PS}[]}M$。

証明。$\leq_{\textrm{PS}[]}$ の定義の証拠として $a=(n)$ を取る。示すべきことは 2 つ。

- $a$ の各項が $1$ 以上であること: $a$ の項は $n$ のみで、仮定が $1\leq n$ そのものである。
- $M[n]=M[a]$ であること: 反復展開の定義から $M[(n)]=(M[n])[()]=M[n]$。

**補題 B（展開閉包）**: 任意の有限列 $a$ と任意の有限ペア列 $N$ に対して、$N\in ST_{\textrm{PS}}$ かつ $a$ の各項が $1$ 以上ならば $N[a]\in ST_{\textrm{PS}}$。

証明。$a$ に関する構造帰納法。基点 $N$ は帰納法の中で動かす（$a$ ごとに全ての $N$ について主張する形で帰納する）。

- $a=()$ のとき: $N[()]=N$ であり、仮定 $N\in ST_{\textrm{PS}}$ がそのまま結論である。
- $a=(n)\oplus a'$ のとき: $n$ は $a$ の項だから仮定より $1\leq n$。よって $ST_{\textrm{PS}}$ の第 2 生成規則を $N\in ST_{\textrm{PS}}$ と $1\leq n$ に適用して $N[n]\in ST_{\textrm{PS}}$。また $a'$ の各項は $a$ の項でもあるから $1$ 以上。帰納法の仮定を列 $a'$ と基点 $N[n]$ に適用して $(N[n])[a']\in ST_{\textrm{PS}}$。反復展開の定義から $N[a]=N[(n)\oplus a']=(N[n])[a']$ なので結論を得る。

**主張の (⇒)**。$M\in ST_{\textrm{PS}}$ の生成規則に関する帰納法（$ST_{\textrm{PS}}$ が最小であることから来る帰納法原理）を使う。示すべきは各生成規則に対する場合である。

- 第 1 生成規則の場合: $M=((j,j))_{j=u}^v$ で $u\leq v$。求める $u,v$ としてこの $u,v$ をそのまま取る。$u\leq v$ は仮定そのもの。$M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ の証拠として $a=()$ を取る。空列の各項が $1$ 以上であることは空虚に真であり、$((j,j))_{j=u}^v=((j,j))_{j=u}^v[()]$ は反復展開の定義から等式として成立する。
- 第 2 生成規則の場合: $M\in ST_{\textrm{PS}}$、$1\leq n$、および帰納法の仮定「ある $u,v$ が存在して $u\leq v$ かつ $M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$」が与えられ、$M[n]$ について同じ結論を示す。帰納法の仮定から $u,v$、$u\leq v$、$M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ を取り出す。求める $u,v$ としては同じものを取る。補題 A を $M$ と $1\leq n$ に適用して $M[n]\leq_{\textrm{PS}[]}M$ を得る。既に証明済みの命題「基本列的順序が推移性」（$\leq_{\textrm{PS}[]}$ の側）をこの $M[n]\leq_{\textrm{PS}[]}M$ と $M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ に適用して $M[n]\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ を得る。

**主張の (⇐)**。仮定を分解して $u$、$v$、$u\leq v$、列 $a$、$a$ の各項が $1$ 以上であること、および等式 $M=((j,j))_{j=u}^v[a]$ を取り出す。この等式で $M$ を消去し、目標を $((j,j))_{j=u}^v[a]\in ST_{\textrm{PS}}$ に書き換える。$u\leq v$ と $ST_{\textrm{PS}}$ の第 1 生成規則から $((j,j))_{j=u}^v\in ST_{\textrm{PS}}$。補題 B を列 $a$、基点 $((j,j))_{j=u}^v$、この標準形性、および $a$ の各項が $1$ 以上であることに適用して結論を得る。

## 原文通りに書けなかった理由

- **[R]** 原文の $M\in T_{\textrm{PS}}$ という制限が要らない

  原文は「任意の $M\in T_{\textrm{PS}}$ に対して」と述べるが、Lean の命題は $M$ を有限ペア列全体で量化しており、$M\in T_{\textrm{PS}}$（この形式化では $M\neq()$）を仮定していない。証明は両方向ともこの仮定を一度も使わない。$ST_{\textrm{PS}}\subseteq T_{\textrm{PS}}$ は本体側で別途証明されているので、$M\in T_{\textrm{PS}}$ を仮定する原文の形が要るときはそこから復元でき、下流は変わらない。

- **[R]** (⇒) で $S_kT_{\textrm{PS}}$ 階層と $ST_{\textrm{PS}}=\bigcup_k S_kT_{\textrm{PS}}$ を使わない

  原文の (⇒) は、$k$ に関する帰納法で「任意の $M\in S_kT_{\textrm{PS}}$ について結論」を示し、最後に $ST_{\textrm{PS}}=\bigcup_{k\in\mathbb{N}}S_kT_{\textrm{PS}}$ で $ST_{\textrm{PS}}$ 全体へ移す、という 2 段構えである。この形式化の $ST_{\textrm{PS}}$ は 2 つの生成規則で閉じた最小の述語として定義されているので、その帰納法原理が原文の $k$ 帰納法と最後の合併の 2 段をまとめて与える。したがって $S_kT_{\textrm{PS}}$ も合併の等式も証明に現れない。なお $S_kT_{\textrm{PS}}$ とその両向きの言い換え（階層に属せば標準形／標準形なら或る階層に属す）は本体側に存在するが、本補題では引いていない。

- **[W]** 原文が根拠を書かない一歩「$M\in S_{k+1}T_{\textrm{PS}}$ なら或る $N\in S_kT_{\textrm{PS}}$ について $M\leq_{\textrm{PS}[]}N$」を補題として補っている

  原文はこの $M\leq_{\textrm{PS}[]}N$ を「であるから」と断るだけで、$\leq_{\textrm{PS}[]}$ の証拠となる列を挙げていない。Lean では補題 A として、$1\leq n$ のとき $a=(n)$ が証拠になること（$a$ の各項が $1$ 以上であること、および $M[(n)]=M[n]$ が反復展開の定義から出ること）を明示的に証明し、それを (⇒) の第 2 生成規則の場合で使っている。埋めるのに要ったのは定義の 1 回の展開だけである。

- **[S]** (⇐) の帰納法を、$Q_0$ を固定した $k$ 帰納法ではなく、基点を一般化した列の構造帰納法に組み替えている

  原文は $Q_0=((j,j))_{j=u}^v$ を固定し、$Q_{i+1}=Q_i[a_i]$ で定まる列 $(Q_k)$ について添字 $k$ の帰納法で $Q_k\in ST_{\textrm{PS}}$（$k\leq\textrm{Lng}(a)$）を示し、$M=Q_{\textrm{Lng}(a)}$ から結論する。Lean は補題 B の形、すなわち「全ての基点 $N$ について $N\in ST_{\textrm{PS}}$ ならば $N[a]\in ST_{\textrm{PS}}$」を $a$ の構造に関する帰納法で示す。原文が列の後ろに $[a_k]$ を足していくのに対し、こちらは先頭の $[a_0]$ を剥がして基点を $N[a_0]$ に移す向きに進むため、基点を全称量化しておく必要がある。証明される結論（$M=((j,j))_{j=u}^v[a]\in ST_{\textrm{PS}}$）は同じで、$(Q_k)$ という中間列は現れない。

- **[⚠️Y]** 原文 (⇐) の帰納段の添字が 1 つずれている

  原文は $Q_{i+1}=Q_i[a_i]$ と定義しておきながら、帰納段では $Q_{k+1}=Q_k[a_{k+1}]\in ST_{\textrm{PS}}$ と書いている。定義どおりなら $Q_{k+1}=Q_k[a_k]$ である。$k<\textrm{Lng}(a)$ の範囲で $k=\textrm{Lng}(a)-1$ を取ると $a_{k+1}=a_{\textrm{Lng}(a)}$ となり項が存在しないので、そのままでは形式化できない。直し方は $a_{k+1}$ を $a_k$ に替えるだけで一意であり、証明の構造は変わらない。Lean は定義どおり $N[(n)\oplus a']=(N[n])[a']$ を使っている。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $T_{\textrm{PS}}$ | `PSS.TPS`（`M ≠ []`） | `lean/PSS/Defs.lean` |
| $M[n]$ | `PSS.oper M n` | 同上 |
| $((j,j))_{j=u}^v$ | `PSS.diagSeq u v` | `lean/PSS/Red.lean` |
| $ST_{\textrm{PS}}$（2 生成規則で閉じた最小の述語） | `PSS.STPS`（生成規則 `STPS.diag`、`STPS.oper`） | `lean/PSS/Standard.lean` |
| $S_kT_{\textrm{PS}}$ | `PSS.SkTPS` | 同上 |
| 階層に属せば標準形 | `SkTPS_STPS`（本補題では未使用） | `lean/6/6.7-standard-P-components.lean` |
| 標準形なら或る階層に属す | `STPS_exists_rank_68`（本補題では未使用） | `lean/6/6.8-standard-slice-Br-descending.lean` |
| $ST_{\textrm{PS}}\subseteq T_{\textrm{PS}}$ | `STPS_TPS`（本補題では未使用） | `lean/6/6.7-standard-prefix.lean` |
| 反復展開 $N[a]$ | `expand N a` | `lean/Bijectivity/Defs.lean` |
| $M\leq_{\textrm{PS}[]}N$ | `leExpPS M N` | 同上 |
| 基本列的順序が推移性（$\leq_{\textrm{PS}[]}$ の側） | `leExpPS_trans` | `lean/Bijectivity/03-exp-order-transitive.lean` |
| 補題 A（一歩展開） | `oper_leExpPS` | `lean/Bijectivity/09-standard-iff-exp.lean` |
| 補題 B（展開閉包） | `stps_expand` | 同上 |
| 本補題 | `stps_iff_leExpPS` | 同上 |

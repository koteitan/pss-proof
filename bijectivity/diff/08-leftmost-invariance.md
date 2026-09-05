[← back](README.md)

# 08: 補題 (最左列の不変性)

## 原文

### 命題

補題 (最左列の不変性)

任意の$M,N\in T_{\textrm{PS}}$に対して、$M\leq_{\textrm{PS}[]}N$ならば$M_0=N_0$である。

### 証明

&nbsp;&nbsp;$\leq_{\textrm{PS}[]}$の定義よりある$a\in\mathbb{N}_+^{<\omega}$が存在して$M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$である。  
&nbsp;&nbsp;任意の非負整数$i<\textrm{Lng}(a)$に対して$Q_0=N$、$Q_{i+1}=Q_i[a_i]$とする。  
&nbsp;&nbsp;$(Q_0)_0=N_0$である。  
&nbsp;&nbsp;任意の非負整数$k<\textrm{Lng}(a)$を取り、$(Q_k)_0=N_0$であると仮定する。  
&nbsp;&nbsp;&nbsp;&nbsp;$\textrm{Lng}(Q_k)=1$ならば$(Q_{k+1})_0=(Q_k)_0=N_0$である。  
&nbsp;&nbsp;&nbsp;&nbsp;$\textrm{Lng}(Q_k)>1$ならば展開と$\textrm{Pred}$の関係より$(Q_{k+1})_0=\textrm{Pred}(Q_k)_0=N_0$である。  
&nbsp;&nbsp;&nbsp;&nbsp;よっていずれの場合でも$(Q_{k+1})_0=N_0$である。  
&nbsp;&nbsp;帰納法により任意の非負整数$k\leq\textrm{Lng}(a)$に対して、$(Q_k)_0=N_0$である。  
&nbsp;&nbsp;よって$M_0=(Q_{\textrm{Lng}(a)})_0=N_0$である。

## Lean

### Lean での命題

ペア数列は対 $(\mathbb{N}\times\mathbb{N})$ の有限列として表されている。最左列 $M_0$ は既定値つきの先頭要素 $\textrm{head}(M)$、すなわち $\textrm{Lng}(M)>0$ のとき $M_0$、$M=()$ のとき $(0,0)$ となるもの、で表す。$T_{\textrm{PS}}$ の元に対してはこれは原文の $M_0$ そのものである。示されている命題は

任意のペア数列 $M,N$ に対して、$M\leq_{\textrm{PS}[]}N$ ならば $\textrm{head}(M)=\textrm{head}(N)$

である（$T_{\textrm{PS}}$ への所属は仮定していない）。ここで $\leq_{\textrm{PS}[]}$ は原文どおり

$$M\leq_{\textrm{PS}[]}N\ :\Longleftrightarrow\ \exists a\in\mathbb{N}_+^{<\omega},\ M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$$

と定義されており、右辺の反復展開は列 $a$ についての再帰

$$\textrm{expand}(N,())=N,\qquad \textrm{expand}(N,(n)\oplus a)=\textrm{expand}(N[n],a)$$

で与えられている（$\mathbb{N}_+^{<\omega}$ への所属は「$a$ の各成分が $1$ 以上」という条件として持たれる）。

原文の $Q_k$ に関する帰納法にあたるものとして、次を独立の補題として立てている。

任意の列 $a$（各成分 $\geq1$）と任意のペア数列 $N$ に対して $\textrm{head}(\textrm{expand}(N,a))=\textrm{head}(N)$。

### Lean での証明

**(1) 反復展開が最左列を保つこと。** $a$ に関する構造帰納法で示す。$N$ は全称量化したまま動かす。

- $a=()$ のとき。定義より $\textrm{expand}(N,())=N$ なので、示すべき等式の両辺は同一の項であり、反射律で閉じる。

- $a=(n)\oplus a'$ のとき。定義より $\textrm{expand}(N,(n)\oplus a')=\textrm{expand}(N[n],a')$ である。$a'$ の各成分は $(n)\oplus a'$ の成分でもあるから $1$ 以上であり、帰納法の仮定を $N$ ではなく $N[n]$ に対して適用して

  $$\textrm{head}(\textrm{expand}(N[n],a'))=\textrm{head}(N[n]).$$

  よって残る目標は $\textrm{head}(N[n])=\textrm{head}(N)$ であり、$1<\textrm{Lng}(N)$ か $\textrm{Lng}(N)\leq1$ かで場合分けする。

  - $1<\textrm{Lng}(N)$ のとき。$n\in(n)\oplus a'$ から $n\geq1$ を得て、下の (2) の一歩補題をそのまま適用する。

  - $\textrm{Lng}(N)\leq1$ のとき。$j_1=\textrm{Lng}(N)-1$ は（自然数の切り捨て減算なので $\textrm{Lng}(N)=0$ でも）$0$ である。$\textrm{operator}[]$ の定義は $j_1=0$ を第 1 分岐で処理して $N[n]=N$ とするので、目標の両辺は同一の項になり閉じる。

**(2) 一歩補題（展開は最左列を保つ）。** $1<\textrm{Lng}(M)$ かつ $n\geq1$ ならば $\textrm{head}(M[n])=\textrm{head}(M)$。原文が「展開と $\textrm{Pred}$ の関係より $(Q_{k+1})_0=\textrm{Pred}(Q_k)_0=N_0$」と一行で書いた箇所にあたる。$j_1=\textrm{Lng}(M)-1$ と置くと $1<\textrm{Lng}(M)$ より $j_1>0$ であり、次の 4 つを繋ぐ。

- 命題（展開と $\textrm{Pred}$ の関係）：$1<\textrm{Lng}(M)$ かつ $n\geq1$ のとき $\textrm{Lng}(M[n])\geq j_1$ かつ $(M[n]_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)$。ここで使うのは後半の切片の等式である。

- 長さ $k>0$ の先頭切片は先頭要素を変えない：$j_1>0$ より $\textrm{head}\big((M[n]_j)_{j=0}^{j_1-1}\big)=\textrm{head}(M[n])$。

- $\textrm{Pred}$ の定義は $\textrm{Lng}(M)\leq1$ のとき恒等、そうでないとき末尾 1 項の除去なので、$1<\textrm{Lng}(M)$ から $\textrm{Pred}(M)$ は $M$ の末尾 1 項を落とした列である。

- 長さ $2$ 以上の列は末尾 1 項を落としても先頭要素が変わらない：$\textrm{head}(\textrm{Pred}(M))=\textrm{head}(M)$。

  以上より

  $$\textrm{head}(M[n])=\textrm{head}\big((M[n]_j)_{j=0}^{j_1-1}\big)=\textrm{head}(\textrm{Pred}(M))=\textrm{head}(M).$$

**(3) 本補題。** 仮定 $M\leq_{\textrm{PS}[]}N$ から、定義により各成分が $1$ 以上の列 $a$ と等式 $M=\textrm{expand}(N,a)$ を取り出し、$M$ をこの式で置き換える。(1) を $a$ と $N$ に適用して $\textrm{head}(\textrm{expand}(N,a))=\textrm{head}(N)$、すなわち $\textrm{head}(M)=\textrm{head}(N)$ を得る。□

## 原文通りに書けなかった理由

- **[R]** $M,N\in T_{\textrm{PS}}$ の仮定が要らない

  原文は $M,N\in T_{\textrm{PS}}$（空列でない）を仮定し、それに合わせて場合分けを $\textrm{Lng}(Q_k)=1$ と $\textrm{Lng}(Q_k)>1$ の 2 つで尽くしている。Lean 側は所属の仮定を置かず、空列を含む任意のペア数列に対して述べている。場合分けは $\textrm{Lng}(N)\leq1$ と $1<\textrm{Lng}(N)$ で、前者には原文が排除していた $\textrm{Lng}(N)=0$ も入るが、$j_1=\textrm{Lng}(N)-1$ が自然数の切り捨て減算で $0$ になるため $\textrm{operator}[]$ の第 1 分岐が働いて $N[n]=N$ となり、原文の $\textrm{Lng}(Q_k)=1$ の場合とまったく同じ議論で閉じる。最左列は既定値 $(0,0)$ つきの先頭要素で表しており、$T_{\textrm{PS}}$ の元に対しては原文の $M_0$ と一致するので、原文の主張はこの命題の特別な場合として得られる。

- **[S]** 帰納法を原文の $Q_k$ の前向き帰納ではなく、展開列 $a$ の構造帰納で回している

  原文は $Q_0=N$、$Q_{i+1}=Q_i[a_i]$ という列を作り、$k$ に関する帰納法で $(Q_k)_0=N_0$ を示す。この形では一歩補題は最後に行った展開 $Q_k\mapsto Q_k[a_k]$ に対して使われる。Lean は $Q_k$ の族を作らず、「任意の $N$ に対して $\textrm{head}(\textrm{expand}(N,a))=\textrm{head}(N)$」という $N$ を全称化した命題を $a$ の構造帰納で示す。この形では一歩補題は最初の展開 $N\mapsto N[a_0]$ に対して使われ、帰納法の仮定は始点を $N[a_0]$ に取り替えて適用される。すなわち始点を固定した前向き帰納から、始点を全称化した先頭剥がしの帰納への置き換えである。反復展開そのものが $\textrm{expand}(N,(n)\oplus a)=\textrm{expand}(N[n],a)$ という先頭剥がしの再帰で定義されているため、この向きのほうが定義に沿う。得られる命題は原文と同一で、この補題を $M_0=N_0$ の形でしか使わない下流には影響しない。

- **[W]** 原文の「$(Q_{k+1})_0=\textrm{Pred}(Q_k)_0=N_0$」は 3 段階を隠している

  原文は $\textrm{Lng}(Q_k)>1$ の場合を「展開と $\textrm{Pred}$ の関係より」の一言で済ませるが、その命題が与えるのは $Q_k[a_k]$ の先頭 $\textrm{Lng}(Q_k)-1$ 項が $\textrm{Pred}(Q_k)$ に等しいという切片の等式であって、先頭要素の等式ではない。Lean 側は、(i) 切片の長さ $\textrm{Lng}(Q_k)-1$ が正であること（$\textrm{Lng}(Q_k)>1$ から従う）を使って「正の長さの先頭切片は先頭要素を変えない」を挟み、(ii) $\textrm{Lng}(Q_k)>1$ のとき $\textrm{Pred}(Q_k)$ が末尾 1 項の除去であることを $\textrm{Pred}$ の定義から取り出し、(iii) 長さ $2$ 以上の列では末尾 1 項の除去が先頭要素を変えないこと（原文の 2 つ目の等号 $\textrm{Pred}(Q_k)_0=(Q_k)_0$ にあたり、原文は根拠を挙げていない）を別補題として置いている。いずれも列に関する初等的な補題で、規模は小さい。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| ペア数列 | `PSS.PS`（`List (ℕ × ℕ)`） | `lean/PSS/Defs.lean` |
| $\textrm{Lng}(M)$ | `PSS.Lng` | 同上 |
| $M[n]$、$\textrm{operator}[]$ | `PSS.oper M n` | 同上 |
| $\textrm{Pred}(M)$ | `PSS.Pred` | 同上 |
| $\textrm{head}(M)$ | `M.headD (0, 0)` | Mathlib（`List.headD`） |
| $\textrm{expand}(N,a)$ | `expand` | `lean/Bijectivity/Defs.lean` |
| $M\leq_{\textrm{PS}[]}N$ | `leExpPS M N` | 同上 |
| 反復展開が最左列を保つこと | `expand_head` | `lean/Bijectivity/08-leftmost-invariance.lean` |
| 補題 (最左列の不変性) | `leExpPS_head` | 同上 |
| 一歩補題（展開は最左列を保つ） | `oper_head` | `lean/Bijectivity/07-oper-pred.lean` |
| 命題 (展開と $\textrm{Pred}$ の関係) | `oper_take_pred` | 同上 |
| 正の長さの先頭切片は先頭要素を変えないこと | `headD_take` | 同上 |
| 長さ 2 以上の列は末尾 1 項の除去で先頭要素が変わらないこと | `headD_dropLast` | 同上 |

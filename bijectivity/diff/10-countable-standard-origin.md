[← back](README.md)

# 10: 命題 (可算な標準形の起源)

## 原文

### 命題

命題 (可算な標準形の起源)（原文に番号は振られていない）

任意の$M\in T_{\textrm{PS}}$に対して、$M\in CT_{\textrm{PS}}$はある$v\in\mathbb{N}$が存在して$M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$であることと同値である。

### 証明

  証明  
  (⇒) $ST_{\textrm{PS}}\subset CT_{\textrm{PS}}$であるから、標準形と基本列的順序の関係より、ある$u,v\in\mathbb{N}$が存在して$u\leq v$かつ$M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$である。  
  最左列の不変性より$M_0=(u,u)$である。  
  $CT_{\textrm{PS}}$の定義より$M_0=(0,0)$である。  
  従って$u=0$である。  
  よってある$v\in\mathbb{N}$が存在して$M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$である。  
  (⇐) 最左列の不変性より$M_0=(0,0)$である。  
  $M\in ST_{\textrm{PS}}$である。  
  よって$M\in CT_{\textrm{PS}}$である。□

## Lean

### Lean での命題

任意のペア数列 $M$ に対して

$$M\in CT_{\textrm{PS}}\iff \exists v\in\mathbb{N},\ M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$$

ここで各記号は次のとおりである。

- $M_0$ は先頭列であり、空列に対しては既定値 $(0,0)$ を返す全域の関数として定める。
- $CT_{\textrm{PS}}$ は原文の定義そのままの連言、すなわち $M\in CT_{\textrm{PS}}:\iff M\in ST_{\textrm{PS}}\land M_0=(0,0)$。
- $ST_{\textrm{PS}}$ は「$u\leq v$ なる対角列 $((j,j))_{j=u}^v$ を含み、正の添字による基本列 $M\mapsto M[n]$（$1\leq n$）で閉じた最小の述語」として帰納的に定める。
- $((j,j))_{j=u}^v$ は $\mathrm{range}'(u,\ v+1-u)$（$u$ から始まる長さ $v+1-u$ の連続整数列。減算は自然数の切り捨て減算）の各項 $j$ を $(j,j)$ に写した列。$v<u$ なら空列である。
- $N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ は添字列 $a$ に沿った反復展開で、$N$ に対して空列なら $N$ 自身、$a=n\frown a'$ なら $N[n]$ を $a'$ で反復展開したもの、と再帰的に定める。
- $M\leq_{\textrm{PS}[]}N:\iff$ ある有限列 $a$ が存在して $a$ の全項が $1$ 以上であり $M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$。

原文の仮定 $M\in T_{\textrm{PS}}$（この形式化では $M\neq\varnothing$）は置いていない。同値は任意のペア数列（空列を含む）について主張されている。

### Lean での証明

まず補助補題（対角列の最左列）を証明する。

補助補題: $u\leq v$ ならば $(((j,j))_{j=u}^v)_0=(u,u)$。

証明: $u\leq v$ より、自然数の切り捨て減算について $v+1-u=(v-u)+1$ である。よって $((j,j))_{j=u}^v$ の定義中の長さ $v+1-u$ は後続数の形になり、$\mathrm{range}'$ の再帰式（$\mathrm{range}'(a,0)=\varnothing$、$\mathrm{range}'(a,n+1)=a\frown\mathrm{range}'(a+1,n)$）が一段展開されて

$$\mathrm{range}'(u,\ (v-u)+1)=u\frown\mathrm{range}'(u+1,\ v-u)$$

となる。各項を $j\mapsto(j,j)$ で写すと先頭列は $(u,u)$ であり、列が空でないので既定値には落ちない。□

本命題の証明は原文と同じく両方向に分ける。

(⇒) 仮定 $M\in CT_{\textrm{PS}}$ を連言として分解し、$M\in ST_{\textrm{PS}}$ と $M_0=(0,0)$ を得る。ここで原文が $ST_{\textrm{PS}}\subset CT_{\textrm{PS}}$ と書いている包含は使わない（下記の差異を参照）。

標準形と基本列的順序の関係

$$M\in ST_{\textrm{PS}}\iff \exists u,v\in\mathbb{N},\ u\leq v\land M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$$

の (⇒) を $M\in ST_{\textrm{PS}}$ に適用し、$u,v\in\mathbb{N}$ と $u\leq v$、$M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ を取る。

最左列の不変性

$$M\leq_{\textrm{PS}[]}N\ \Longrightarrow\ M_0=N_0$$

を $N=((j,j))_{j=u}^v$ に適用して $M_0=(((j,j))_{j=u}^v)_0$、続けて補助補題を $u\leq v$ とともに適用して

$$M_0=(u,u)$$

を得る。分解で得た $M_0=(0,0)$ をこの左辺に代入すると $(0,0)=(u,u)$、すなわち対の単射性 $((a,b)=(c,d))\iff(a=c\land b=d)$ の第 1 成分から $u=0$ である。

この $u=0$ を $M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v$ に代入し、$v$ を存在の証拠として $\exists v,\ M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$ を得る。

(⇐) 仮定から $v$ と $M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$ を取る。目標 $M\in CT_{\textrm{PS}}$ は連言なので、二つの肢を別々に作る。

第 1 肢 $M\in ST_{\textrm{PS}}$: 標準形と基本列的順序の関係の (⇐) に $u=0$、$v$、$0\leq v$、および仮定 $M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$ を与える。

第 2 肢 $M_0=(0,0)$: 最左列の不変性を仮定に適用して $M_0=(((j,j))_{j=0}^v)_0$、続けて補助補題を $0\leq v$ とともに適用して $(((j,j))_{j=0}^v)_0=(0,0)$。両者を繋いで $M_0=(0,0)$ を得る。

両肢を組にして $M\in CT_{\textrm{PS}}$ である。□

## 原文通りに書けなかった理由

- **[R]** 原文の仮定 $M\in T_{\textrm{PS}}$ は使っていない

  原文は「任意の$M\in T_{\textrm{PS}}$に対して」と非空性を仮定するが、この形式化の同値は空列を含む任意のペア数列について述べられており、上の証明のどの一歩も $M\neq\varnothing$ を使わない。$M_0$ を空列に対して既定値 $(0,0)$ を返す全域関数として定めているため、空列の場合も両辺が意味を持ち、仮定なしで同値が通る。

- **[⚠️Y]** (⇒) の冒頭にある包含 $ST_{\textrm{PS}}\subset CT_{\textrm{PS}}$ は向きが逆で、そのままでは偽

  (⇒) で必要なのは $M\in CT_{\textrm{PS}}$ から $M\in ST_{\textrm{PS}}$ を出すこと、すなわち $CT_{\textrm{PS}}\subset ST_{\textrm{PS}}$ である。原文の $ST_{\textrm{PS}}\subset CT_{\textrm{PS}}$ は実際に偽であり、$u=v=1$ の対角列 $((1,1))=((j,j))_{j=1}^1\in ST_{\textrm{PS}}$ は $M_0=(1,1)\neq(0,0)$ なので $CT_{\textrm{PS}}$ に属さない。包含の向きを入れ替えるだけの機械的な訂正で、証明の構造は変わらないので誤記の類とみなす。この形式化では $CT_{\textrm{PS}}$ が連言そのものなので、正しい向きの包含は第 1 連言肢の取り出しに他ならず、補題として立てる必要もない。

- **[W]** 「最左列の不変性より$M_0=(u,u)$」は対角列の先頭列の計算を飛ばしている

  最左列の不変性が与えるのは $M_0=(((j,j))_{j=u}^v)_0$ までであり、そこから $(u,u)$ への評価は原文では暗黙である。この形式化では対角列を $\mathrm{range}'(u,\ v+1-u)$ の像として定義しており、$v<u$ のときは空列になって先頭列が既定値 $(0,0)$ になってしまうため、$u\leq v$ が本質的に効く。そこで補助補題（対角列の最左列）を別に立て、$u\leq v$ から $v+1-u=(v-u)+1$（切り捨て減算）を経て $\mathrm{range}'$ を一段展開する計算を明示した。(⇒) では標準形と基本列的順序の関係が与える $u\leq v$ を、(⇐) では $0\leq v$ を、それぞれこの補助補題に渡している。

- **[W]** (⇐) の「$M\in ST_{\textrm{PS}}$である」は根拠が書かれていない

  原文はこの一行を無条件に置くだけだが、これは標準形と基本列的順序の関係の (⇐) を $u=0$、$v$、$0\leq v$ に対して適用した結果である。この形式化ではその適用を明示し、$0\leq v$ を証拠として与えている。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $M\in CT_{\textrm{PS}}$ | `CTPS M` | `lean/Bijectivity/Defs.lean` |
| $M_0$（先頭列、空列では既定値 $(0,0)$） | `M.headD (0, 0)` | なし（Lean 標準ライブラリ） |
| $M\in ST_{\textrm{PS}}$ | `PSS.STPS M` | `lean/PSS/Standard.lean` |
| $((j,j))_{j=u}^v$ | `PSS.diagSeq u v` | `lean/PSS/Red.lean` |
| $\mathrm{range}'(a,n)$ | `List.range' a n` | なし（Lean 標準ライブラリ） |
| $N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ | `expand N a` | `lean/Bijectivity/Defs.lean` |
| $M[n]$ | `PSS.oper M n` | `lean/PSS/Defs.lean` |
| $M\leq_{\textrm{PS}[]}N$ | `leExpPS M N` | `lean/Bijectivity/Defs.lean` |
| $M\in T_{\textrm{PS}}$（本命題では未使用） | `PSS.TPS M` | `lean/PSS/Defs.lean` |
| 補助補題（対角列の最左列） | `headD_diagSeq` | `lean/Bijectivity/10-countable-standard-origin.lean` |
| 命題（可算な標準形の起源） | `ctps_iff_leExpPS` | 同上 |
| 標準形と基本列的順序の関係 | `stps_iff_leExpPS` | `lean/Bijectivity/09-standard-iff-exp.lean` |
| 最左列の不変性 | `leExpPS_head` | `lean/Bijectivity/08-leftmost-invariance.lean` |
| 対の単射性 | `Prod.mk.injEq` | なし（Lean 標準ライブラリ） |

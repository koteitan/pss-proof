[← back](README.md)

# 07: 命題 (展開とPredの関係)

## 原文

### 命題

命題 (展開と$`\textrm{Pred}`$の関係)（原文に番号は振られていない）

任意の$`M\in T_{\textrm{PS}}`$と$`n\in\mathbb{N}_+`$に対し、$`j_1=\textrm{Lng}(M)-1`$と置くと、$`\textrm{Lng}(M[n])\geq j_1`$かつ$`(M[n]_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)`$である。

### 証明

  証明  
  $`\textrm{operator}[]`$の定義中の記号を$`M`$に対して定義する。  
  $`M[n]=M`$または$`M[n]=\textrm{Pred}(M)`$ならば明らかに$`\textrm{Lng}(M[n])\geq j_1`$かつ$`(M[n]_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)`$である。  
  よって$`j_1\gt 0`$かつ$`M_{j_1}\neq(0,0)`$かつある非負整数$`j_0`$が存在して$`(i_1,j_0)\lt^\textrm{Next}_M(i_1,j_1)`$であるとする。  
    ```math
    \begin{align}\textrm{Lng}(M[n])&=\textrm{Lng}(G\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}B\right))\\&=j_0+n(j_1-j_0)\\&\geq j_1\end{align}
    ```

    である。
    [1]の$`\textrm{Pred}`$が$`[1]`$で表されること及び基本列の切片の不変性より$`(M[n]_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)`$である。  
  よっていずれの場合でも$`\textrm{Lng}(M[n])\geq j_1`$かつ$`(M[n]_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)`$である。□

## Lean

### Lean での命題

記号は次のとおり。

- ペア数列 $`M`$ は $`\mathbb{N}\times\mathbb{N}`$ の有限列、$`\textrm{Lng}(M)`$ はその長さ。$`M_j`$ は第 $`j`$ 項、$`M_{i,j}`$ はその第 $`i`$ 成分（$`j\geq\textrm{Lng}(M)`$ のときは $`0`$）。
- $`\textrm{Pred}(M)`$ は末尾の項を落とす写像（$`\textrm{Lng}(M)\leq1`$ なら恒等）。
- $`M[n]`$ は原文 [1] §5.3 の逐語形の基本列。$`j_1=\textrm{Lng}(M)-1`$ として、$`j_1=0`$ なら $`M`$、$`M_{j_1}=(0,0)`$ なら $`\textrm{Pred}(M)`$、段 $`i_1=\textrm{idx}_1(M,j_1)`$（$`M_{1,j_1}\gt 0`$ なら $`1`$、さもなくば $`0`$）に親が無ければ $`\textrm{Pred}(M)`$、さもなくば $`j_0`$ を段 $`i_1`$ における $`j_1`$ の親、$`\delta_0,\delta_1`$ を定義中の増分として $`G\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}B\right)`$。
- $`M{\restriction}k`$ で $`M`$ の先頭 $`k`$ 項を表す（$`k\geq\textrm{Lng}(M)`$ なら $`M`$ 全体）。

Lean が証明しているのは次の主張である。

任意のペア数列 $`M`$ と $`n\in\mathbb{N}`$ に対し、$`\textrm{Lng}(M)\gt 1`$ かつ $`1\leq n`$ ならば

```math
\textrm{Lng}(M)-1\leq\textrm{Lng}(M[n])\quad\land\quad (M[n]){\restriction}(\textrm{Lng}(M)-1)=\textrm{Pred}(M).
```

原文の $`j_1=\textrm{Lng}(M)-1`$ に対し、第 1 主張は $`\textrm{Lng}(M[n])\geq j_1`$ そのもの、第 2 主張は原文の $`(M[n]_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)`$ を「先頭 $`j_1`$ 項」で書いたものである。原文の $`M\in T_{\textrm{PS}}`$（空でないこと）は $`\textrm{Lng}(M)\gt 1`$ から従うので、仮定には現れない。原文の $`n\in\mathbb{N}_+`$ は $`n\in\mathbb{N}`$ と $`1\leq n`$ に分けて書いている。

このファイルには続けて系が置かれている。$`\textrm{hd}(L)`$ で $`L`$ の先頭項（空列なら $`(0,0)`$）を表すとき、

```math
\textrm{Lng}(M)\gt 1\ \land\ 1\leq n\ \Longrightarrow\ \textrm{hd}(M[n])=\textrm{hd}(M)
```

である。これは原文の次の補題（最左列の不変性）の帰納段「$`\textrm{Lng}(Q_k)\gt 1`$ ならば展開と $`\textrm{Pred}`$ の関係より $`(Q_{k+1})_0=\textrm{Pred}(Q_k)_0=N_0`$」の一歩に当たる。

### Lean での証明

以下、$`j_1=\textrm{Lng}(M)-1`$ と置く。仮定 $`\textrm{Lng}(M)\gt 1`$ より $`j_1\neq0`$ である。

**補題（先頭項の分割）.** $`j_0\leq j_1\leq\textrm{Lng}(M)`$ ならば

```math
M{\restriction}j_1=(M{\restriction}j_0)\oplus_{\mathbb{N}^2}\left((M_{0,j},M_{1,j})\right)_{j=j_0}^{j_1-1}
```

である。証明は両辺の長さと各成分の比較による。長さは、左辺が $`\min(j_1,\textrm{Lng}(M))=j_1`$、右辺が $`\min(j_0,\textrm{Lng}(M))+(j_1-j_0)=j_0+(j_1-j_0)=j_1`$ で一致する。第 $`i`$ 項（$`i\lt j_1`$、したがって $`i\lt\textrm{Lng}(M)`$）については

- $`i\lt j_0`$ のとき: 右辺の連結は左側 $`M{\restriction}j_0`$ の第 $`i`$ 項を取り、それは $`M_i`$。左辺の第 $`i`$ 項も $`M_i`$。
- $`i\geq j_0`$ のとき: 右辺の連結は右側を取り、その添字は $`i-\min(j_0,\textrm{Lng}(M))=i-j_0`$。区間 $`j_0,\dots,j_1-1`$ の第 $`i-j_0`$ 項は $`j_0+(i-j_0)=i`$ なので、値は $`(M_{0,i},M_{1,i})`$ である。$`i\lt\textrm{Lng}(M)`$ より範囲外の既定値 $`0`$ は効かず、これは $`M_i`$ に等しい。

**退化枝.** $`\textrm{Lng}(M)\gt 1`$ かつ $`M[n]=\textrm{Pred}(M)`$ のときを別に処理する。$`\textrm{Lng}(\textrm{Pred}(M))=\textrm{Lng}(M)-1=j_1`$ なので第 1 主張は等号で成り立つ。第 2 主張は、前者の先頭項表示 $`\textrm{Pred}(M)=M{\restriction}j_1`$（$`\textrm{Lng}(M)\gt 1`$ のとき）を両辺に使って

```math
(M{\restriction}j_1){\restriction}j_1=M{\restriction}\min(j_1,j_1)=M{\restriction}j_1
```

となり、$`\min(j_1,j_1)=j_1`$ で閉じる。原文の「明らか」に当たる部分はこれだけである。

**場合分け.** $`M[n]`$ の定義の分岐に沿って分ける。$`j_1\neq0`$ は既に得ているので、定義の第 1 分岐（$`M[n]=M`$）は起こらない。

1. $`M_{0,j_1}=0`$ かつ $`M_{1,j_1}=0`$（すなわち $`M_{j_1}=(0,0)`$）のとき。定義の第 2 分岐から $`M[n]=\textrm{Pred}(M)`$ なので退化枝を適用する。
2. $`M_{j_1}\neq(0,0)`$ かつ、段 $`i_1`$ における $`j_1`$ の親候補がちょうど一つではないとき（原文の「ある非負整数 $`j_0`$ が存在して $`(i_1,j_0)\lt^\textrm{Next}_M(i_1,j_1)`$」に当たる条件の否定）。定義の第 3 分岐から $`M[n]=\textrm{Pred}(M)`$ なので退化枝を適用する。
3. $`M_{j_1}\neq(0,0)`$ かつ親候補がちょうど一つのとき（主枝）。以下これを扱う。

**主枝.** $`j_0`$ を段 $`i_1`$ における $`j_1`$ の親、

```math
\delta_0=\begin{cases}M_{0,j_1}-M_{0,j_0}&(0\lt i_1)\\0&(\text{otherwise})\end{cases},\qquad
\delta_1=\begin{cases}M_{1,j_1}-M_{1,j_0}&(1\lt i_1)\\0&(\text{otherwise})\end{cases}
```

と置く（$`\textrm{operator}[]`$ の定義中の記号そのもの）。親をもつことから $`j_0\lt j_1`$ であり（親子関係 $`\lt^\textrm{Next}_M`$ が添字を真に増やすこと）、したがって $`j_0\leq\textrm{Lng}(M)`$ である。定義を展開すると

```math
M[n]=(M{\restriction}j_0)\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}(B_k)_{k=0}^{n-1}\right),\qquad
B_k=\left((M_{0,j}+k\delta_0,\ M_{1,j}+k\delta_1)\right)_{j=j_0}^{j_1-1}
```

である（$`M{\restriction}j_0`$ が原文の $`G=(M_j)_{j=0}^{j_0-1}`$）。$`1\leq n`$ より $`n=m+1`$ と書き、$`k`$ の連結を先頭の $`k=0`$ とそれ以外に分ける。$`k=0`$ では $`k\delta_0=k\delta_1=0`$ だから

```math
\bigoplus_{\mathbb{N}^2}(B_k)_{k=0}^{m}=B_0\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}(B_k)_{k=1}^{m}\right),\qquad
B_0=\left((M_{0,j},M_{1,j})\right)_{j=j_0}^{j_1-1}.
```

前半の長さは

```math
\textrm{Lng}\left((M{\restriction}j_0)\oplus_{\mathbb{N}^2}B_0\right)=\min(j_0,\textrm{Lng}(M))+(j_1-j_0)=j_0+(j_1-j_0)=j_1
```

である（$`j_0\leq\textrm{Lng}(M)`$ と $`j_0\lt j_1`$ を使う）。

第 1 主張。上の 2 つの分解と連結の結合律から $`M[n]=\left((M{\restriction}j_0)\oplus_{\mathbb{N}^2}B_0\right)\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}(B_k)_{k=1}^{m}\right)`$ なので

```math
\textrm{Lng}(M[n])=j_1+\textrm{Lng}\left(\bigoplus_{\mathbb{N}^2}(B_k)_{k=1}^{m}\right)\geq j_1
```

である。$`n`$ 個のブロックの総長は計算しない。

第 2 主張。同じ分解で前半の長さがちょうど $`j_1`$ だから、$`M[n]`$ の先頭 $`j_1`$ 項は前半そのもの

```math
(M[n]){\restriction}j_1=(M{\restriction}j_0)\oplus_{\mathbb{N}^2}B_0
```

である。一方 $`\textrm{Lng}(M)\gt 1`$ より $`\textrm{Pred}(M)=M{\restriction}j_1`$ であり、上の補題（先頭項の分割）を $`j_0\leq j_1\leq\textrm{Lng}(M)`$ に適用すると

```math
M{\restriction}j_1=(M{\restriction}j_0)\oplus_{\mathbb{N}^2}\left((M_{0,j},M_{1,j})\right)_{j=j_0}^{j_1-1}=(M{\restriction}j_0)\oplus_{\mathbb{N}^2}B_0
```

となる。両者が同じ式なので $`(M[n]){\restriction}j_1=\textrm{Pred}(M)`$ である。

**系（展開は最左列を保つ）.** 補助として次の 2 つを示す。

- $`0\lt k`$ ならば $`\textrm{hd}(L{\restriction}k)=\textrm{hd}(L)`$。$`L`$ が空列なら両辺とも既定値 $`(0,0)`$、$`L=a\frown L'`$ なら $`k=0`$ は仮定に反し、$`k\gt 0`$ のとき両辺とも $`a`$ である。
- $`\textrm{Lng}(L)\gt 1`$ のとき、$`L`$ から末尾を落としたものを $`L^-`$ と書けば $`\textrm{hd}(L^-)=\textrm{hd}(L)`$。$`L`$ を 2 項以上に分解すれば末尾落としは先頭項を残す。

これらを使う。$`\textrm{Lng}(M)\gt 1`$ より $`0\lt j_1`$ なので、第 1 の補助から $`\textrm{hd}((M[n]){\restriction}j_1)=\textrm{hd}(M[n])`$。左辺は本命題の第 2 主張により $`\textrm{hd}(\textrm{Pred}(M))`$ である。さらに $`\textrm{Lng}(M)\gt 1`$ のとき $`\textrm{Pred}(M)`$ は $`M`$ の末尾落としだから、第 2 の補助により $`\textrm{hd}(\textrm{Pred}(M))=\textrm{hd}(M)`$。よって $`\textrm{hd}(M[n])=\textrm{hd}(M)`$ である。

## 原文通りに書けなかった理由

- **[⚠️Y]** $`\textrm{Lng}(M)=1`$ のとき原文の第 2 主張は偽なので、$`\textrm{Lng}(M)\gt 1`$ を仮定に足している

  原文は任意の $`M\in T_{\textrm{PS}}`$ について主張するが、$`\textrm{Lng}(M)=1`$ すなわち $`j_1=0`$ のとき、左辺 $`(M[n]_j)_{j=0}^{j_1-1}`$ は空区間の切片、すなわち空列であり（原文が $`\lt_{\textrm{PS}}`$ の定義で使う $`(M_i)_{i=1}^{\textrm{Lng}(M)-1}`$ と同じ約束）、右辺は $`\textrm{Pred}(M)=M`$ で長さ $`1`$ なので等しくない。第 1 主張 $`\textrm{Lng}(M[n])\geq0`$ のほうはこのとき自明に成り立つ。直し方は $`\textrm{Lng}(M)\gt 1`$ を仮定に足すだけである。この命題を使う次の補題（最左列の不変性）は $`\textrm{Lng}(Q_k)=1`$ と $`\textrm{Lng}(Q_k)\gt 1`$ に場合分けし、後者でしかこの命題を引かないので、下流は変わらない。なおこの仮定により原文の場合分けのうち $`M[n]=M`$（定義の $`j_1=0`$ の分岐）は起こらなくなり、退化枝は $`M[n]=\textrm{Pred}(M)`$ だけになる。

- **[R]** $`\textrm{Lng}(M[n])=j_0+n(j_1-j_0)`$ の等式は使っていない

  原文は $`M[n]`$ の長さを $`j_0+n(j_1-j_0)`$ と厳密に計算し、そこから $`\geq j_1`$ を出す。Lean 側は $`M[n]`$ を $`\left((M{\restriction}j_0)\oplus_{\mathbb{N}^2}B_0\right)\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}(B_k)_{k=1}^{m}\right)`$ と分け、前半の長さが $`j_0+(j_1-j_0)=j_1`$ であることだけから $`\textrm{Lng}(M[n])\geq j_1`$ を得る。$`n`$ 個のブロックの総長は現れない。この分解は第 2 主張のためにどのみち必要なので、長さの等式は一度も要らない。

- **[R]** 「$`\textrm{Pred}`$ が $`[1]`$ で表されること」と「基本列の切片の不変性」を引いていない

  原文は第 2 主張を、$`\textrm{Pred}(M)=M[1]`$（原文 [1] の命題）と直前の命題（基本列の切片の不変性、$`m=1`$ と $`n`$ に対する適用）の組み合わせで得る。Lean 側は $`M[1]`$ を経由せず、上の分解の前半 $`(M{\restriction}j_0)\oplus_{\mathbb{N}^2}B_0`$ が $`M{\restriction}j_1=\textrm{Pred}(M)`$ に一致することを、先頭項の分割補題で直接示す。この 2 つの引用は本ファイルの証明には現れない（前者・後者とも Lean 側に対応する定理は存在するが、この証明では使っていない）。

- **[S]** 閉区間の切片ではなく「先頭 $`k`$ 項」で述べている

  原文の $`(M[n]_j)_{j=0}^{j_1-1}`$ は、各 $`j`$ に $`M[n]`$ の第 $`j`$ 成分を並べる切片演算（範囲外は $`0`$ で埋める）で書ける。この形式化は代わりに「先頭 $`j_1`$ 項を取る」演算 $`M{\restriction}j_1`$ で述べている。第 1 主張 $`\textrm{Lng}(M[n])\geq j_1`$ の下では両者は同じ列になるが、その一致自体はこのファイルでは示していない。下流（最左列の不変性）は先頭 $`j_1`$ 項の形しか使わないので、この言い換えで変わるものは無い。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $`\textrm{Lng}(M)`$ | `Lng` | `lean/PSS/Defs.lean` |
| $`M_{i,j}`$ | `entry M i j` | 同上 |
| $`\textrm{Pred}(M)`$ | `Pred` | 同上 |
| $`M[n]`$ | `oper M n` | 同上 |
| $`i_1=\textrm{idx}_1(M,j_1)`$ | `idx1` | 同上 |
| 段 $`i`$ における $`j_1`$ の親候補・親をもつこと・親 | `parents`, `hasParent`, `parent` | 同上 |
| $`(M_j)_{j=a}^{b}`$（閉区間の切片） | `seg` | 同上 |
| $`M{\restriction}k`$（先頭 $`k`$ 項） | `List.take` | なし（Lean 標準ライブラリ） |
| $`\textrm{hd}(L)`$（先頭項、空列なら $`(0,0)`$） | `List.headD` | なし（Lean 標準ライブラリ） |
| 先頭項の分割 | `take_split` | `lean/Bijectivity/07-oper-pred.lean` |
| 退化枝 | `oper_take_pred_of_pred` | 同上 |
| 本命題 | `oper_take_pred` | 同上 |
| 正の $`k`$ での先頭不変 | `headD_take` | 同上 |
| 末尾落としでの先頭不変 | `headD_dropLast` | 同上 |
| 系（展開は最左列を保つ） | `oper_head` | 同上 |
| $`\textrm{Pred}(M)=M{\restriction}(\textrm{Lng}(M)-1)`$ | `Pred_eq_take` | `lean/6/6.5-Red-Pred-commute.lean` |
| $`\textrm{Lng}(\textrm{Pred}(M))=\textrm{Lng}(M)-1`$ | `length_Pred` | 同上 |
| 親は真に小さい添字をもつ | `parent_lt_of_hasParent` | `lean/6/6.6-condAB-coeff.lean` |
| $`(L_1\oplus L_2){\restriction}\textrm{Lng}(L_1)=L_1`$ | `List.take_left'` | なし（Mathlib） |
| $`(L{\restriction}n){\restriction}m=L{\restriction}\min(m,n)`$ | `List.take_take` | なし（Mathlib） |
| $`\{0,\dots,m\}=\{0\}\cup\{k+1\mid k\leq m-1\}`$ | `List.range_succ_eq_map` | なし（Mathlib） |
| $`\textrm{Pred}(M)=M[1]`$（原文が引くが Lean は使わない） | `pred_is_oper1` | `lean/5/5.3-pred-is-oper1.lean` |
| 基本列の切片の不変性（原文が引くが Lean は使わない） | `oper_seg_invariance` | `lean/Bijectivity/06-fseq-segment-invariance.lean` |

[< back](README.md)

# 06: 命題 (基本列の切片の不変性)

## 原文

### 命題

命題 (基本列の切片の不変性)

任意の $M\in T_{\textrm{PS}}$ と $j_0,j_1\in\mathbb{N}$ と $m,n\in\mathbb{N}_+$ に対して、$j_0\leq j_1$ かつ $j_1<\textrm{Lng}(M[m])$ かつ $j_1<\textrm{Lng}(M[n])$ ならば $(M[m]_j)_{j=j_0}^{j_1}=(M[n]_j)_{j=j_0}^{j_1}$ である。

### 証明

$\textrm{operator}[]$ の定義中の記号を $M$ に対して定義する。

$M[m]=M[n]$ ならば明らかに $(M[m]_j)_{j=j_0}^{j_1}=(M[n]_j)_{j=j_0}^{j_1}$ である。

よって $m\neq n$ かつ $j_1>0$ かつ $M_{j_1}\neq(0,0)$ かつある非負整数 $j_0$ が存在して $(i_1,j_0)<^{\textrm{Next}}_M(i_1,j_1)$ であるとする。

　命題が $m$ と $n$ に対して対称であることから $m<n$ である場合のみ考えればいい。

$$\begin{align}(M[n]_j)_{j=0}^{\textrm{Lng}(M[m])-1}&=(G\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}B\right))_{j=0}^{\textrm{Lng}(M[m])-1}\cr &=(G\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}(B_k)_{k=0}^{m-1}\right)\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}(B_k)_{k=m}^{n-1}\right))_{j=0}^{\textrm{Lng}(M[m])-1}\cr &=(M[m]\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}(B_k)_{k=m}^{n-1}\right))_{j=0}^{\textrm{Lng}(M[m])-1}\cr &=M[m]\end{align}$$

　である。

　$j_0\leq j_1<\textrm{Lng}(M[m])$ であるから、上より $(M[n]_j)_{j=j_0}^{j_1}=(((M[n]_j)_{j=0}^{\textrm{Lng}(M[m])-1})_j)_{j=j_0}^{j_1}=(M[m]_j)_{j=j_0}^{j_1}$ である。

よっていずれの場合でも $(M[m]_j)_{j=j_0}^{j_1}=(M[n]_j)_{j=j_0}^{j_1}$ である。□

## Lean

### Lean での命題

$M$ を任意のペア数列（空列も許す）、$j_0,j_1,m,n\in\mathbb{N}$ とする。$1\leq m$ かつ $1\leq n$ かつ $j_0\leq j_1$ かつ $j_1<\textrm{Lng}(M[m])$ かつ $j_1<\textrm{Lng}(M[n])$ ならば

$$(M[m]_j)_{j=j_0}^{j_1}=(M[n]_j)_{j=j_0}^{j_1}$$

である。

ここで使う記号は次のとおり。

- $M_{i,j}$ は $M$ の第 $j$ 成分の第 $i$ 座標。$j\geq\textrm{Lng}(M)$ のときは $0$ を返す全域関数として定めてある。
- 切片 $(M_j)_{j=a}^{b}$ は、添字列 $(a,a+1,\dots,a+(b+1-a)-1)$ の各 $j$ に $(M_{0,j},M_{1,j})$ を対応させた列。長さは $b+1-a$ であり、自然数の切り捨て減算なので $a>b$ のときは空列になる。
- $M[n]$ は原文が引用する $\textrm{operator}[]$ の逐語形。親の分岐条件は定義どおり「$(i_1,j_0)<^{\textrm{Next}}_M(i_1,j_1)$ を満たす $j_0$ がちょうど 1 個であること」である。

原文の命題との違いは、$M\in T_{\textrm{PS}}$（$M\neq()$）を仮定していない点だけである。

### Lean での証明

証明は 2 つの補題を経る。

**補題 A（左接頭辞での成分不変性）**: 任意のペア数列 $A,R$ と $i,j\in\mathbb{N}$ に対し、$j<\textrm{Lng}(A)$ ならば $(A\oplus_{\mathbb{N}^2}R)_{i,j}=A_{i,j}$ である。

証明: $M_{i,j}$ は「$M$ の $j$ 番目の要素を取り、無ければ $0$、有ればその第 $i$ 座標」と定義されている。$j<\textrm{Lng}(A)$ のとき、連結列 $A\oplus_{\mathbb{N}^2}R$ の $j$ 番目の要素の取得結果は $A$ の $j$ 番目の要素の取得結果に等しい。よって両辺は同じ場合分けに落ちて一致する。

**補題 B（基本列の接頭辞性）**: 任意のペア数列 $M$ と $1\leq m\leq n$ に対し、あるペア数列 $R$ が存在して $M[n]=M[m]\oplus_{\mathbb{N}^2}R$ である。

証明: $j_1:=\textrm{Lng}(M)-1$（自然数の切り捨て減算）と置き、$\textrm{operator}[]$ の定義の分岐をそのまま追う。

(a) $\textrm{Lng}(M)\leq 1$ の場合。このとき $j_1=0$ なので、定義の「$j_1=0$ ならば $M[n]:=M$」の分岐が選ばれ、任意の $k$ に対し $M[k]=M$。よって $R=()$ が取れる。$\textrm{Lng}(M)=0$ もここに含まれる。

(b) $\textrm{Lng}(M)>1$ かつ $M_{0,j_1}=0$ かつ $M_{1,j_1}=0$、すなわち $M_{j_1}=(0,0)$ の場合。定義の「$M_{j_1}=(0,0)$ ならば $M[n]:=\textrm{Pred}(M)$」の分岐が選ばれ、任意の $k$ に対し $M[k]=\textrm{Pred}(M)$。よって $R=()$。

(c) $\textrm{Lng}(M)>1$ かつ $M_{j_1}\neq(0,0)$ かつ、$i_1$ 段で $(i_1,j_0)<^{\textrm{Next}}_M(i_1,j_1)$ を満たす $j_0$ がちょうど 1 個ではない場合。定義の「一意な親が存在しないならば $M[n]:=\textrm{Pred}(M)$」の分岐が選ばれ、任意の $k$ に対し $M[k]=\textrm{Pred}(M)$。よって $R=()$。

(d) 残る場合、すなわち $\textrm{Lng}(M)>1$ かつ $M_{j_1}\neq(0,0)$ かつ一意な親 $j_0$ が存在する場合。$j_0$ をその親とし、

$$\delta_0=\begin{cases}M_{0,j_1}-M_{0,j_0}&(0<i_1)\cr 0&(0\geq i_1)\end{cases},\qquad\delta_1=\begin{cases}M_{1,j_1}-M_{1,j_0}&(1<i_1)\cr 0&(1\geq i_1)\end{cases}$$

と置く。これは原文の $\delta_i$（$i<i_1$ なら差、$i\geq i_1$ なら $0$）を $i=0,1$ について書き下したものである。$i_1\in\lbrace 0,1\rbrace$ なので $\delta_1$ は常に $0$ になる。

まず、定義の展開だけから、任意の $k\in\mathbb{N}$（$k=0$ も含む）に対して

$$M[k]=(M_j)_{j=0}^{j_0-1}\oplus_{\mathbb{N}^2}\bigoplus_{\mathbb{N}^2}\Big(\big((M_{0,j}+c \delta_0, M_{1,j}+c \delta_1)\big)_{j=j_0}^{j_1-1}\Big)_{c=0}^{k-1}$$

が成り立つことを確かめる。右辺は原文の $G\oplus_{\mathbb{N}^2}\left(\bigoplus_{\mathbb{N}^2}B\right)$ そのものであり、この段階では $k$ について何も仮定しない。

次に $d:=n-m$ と置いて $n=m+d$ と書き直し、$B_c:=\big((M_{0,j}+c \delta_0,M_{1,j}+c \delta_1)\big)_{j=j_0}^{j_1-1}$ として

$$R:=\bigoplus_{\mathbb{N}^2}(B_c)_{c=m}^{m+d-1}$$

を取る。ここで $c$ の動く添字列は、$(0,1,\dots,d-1)$ の各元に $m$ を足して得られる列 $(m,m+1,\dots,m+d-1)$ として与える。上の表示を $k=m+d$ と $k=m$ に適用すると、示すべきは

$$G\oplus_{\mathbb{N}^2}\bigoplus_{\mathbb{N}^2}(B_c)_{c=0}^{m+d-1}=\Big(G\oplus_{\mathbb{N}^2}\bigoplus_{\mathbb{N}^2}(B_c)_{c=0}^{m-1}\Big)\oplus_{\mathbb{N}^2}\bigoplus_{\mathbb{N}^2}(B_c)_{c=m}^{m+d-1}$$

である。連結の結合律で右辺の $G$ を外に出すと、残る等式は

$$\bigoplus_{\mathbb{N}^2}(B_c)_{c=0}^{m+d-1}=\bigoplus_{\mathbb{N}^2}(B_c)_{c=0}^{m-1}\oplus_{\mathbb{N}^2}\bigoplus_{\mathbb{N}^2}(B_c)_{c=m}^{m+d-1}$$

になる。これは「添字列を連結してから各元をブロックに展開して連結する」ことと「2 つの添字列を別々に展開してから連結する」ことが一致するという一般則により、添字列そのものの等式

$$(0,1,\dots,m+d-1)=(0,1,\dots,m-1)\oplus(m,m+1,\dots,m+d-1)$$

に帰着する。右辺第 2 項は $(0,1,\dots,d-1)$ の各元に $m$ を足した列であり、この等式は自然数の区間列に関する既知の事実である。以上で補題 B が従う。

**主命題**: まず片側版を示す。

片側版: 任意の $p,q\in\mathbb{N}$ に対し、$1\leq p$ かつ $p\leq q$ かつ $j_1<\textrm{Lng}(M[p])$ ならば $(M[p]_j)_{j=j_0}^{j_1}=(M[q]_j)_{j=j_0}^{j_1}$ である。

証明: 補題 B により $M[q]=M[p]\oplus_{\mathbb{N}^2}R$ なる $R$ を取る。切片の定義を開くと、両辺は同一の添字列 $(j_0,j_0+1,\dots,j_0+(j_1+1-j_0)-1)$ 上の像なので、添字ごとの一致を示せばよい。すなわち、この添字列の各元 $j$ に対して

$$(M[p]_{0,j},M[p]_{1,j})=(M[q]_{0,j},M[q]_{1,j})$$

を示せばよい。$j$ がこの添字列の元であることから $j_0\leq j$ かつ $j<j_0+(j_1+1-j_0)$ であり、命題の仮定 $j_0\leq j_1$ と併せて $j\leq j_1$、さらに $j_1<\textrm{Lng}(M[p])$ より $j<\textrm{Lng}(M[p])$ を得る。そこで右辺の $M[q]$ を $M[p]\oplus_{\mathbb{N}^2}R$ に置き換え、補題 A を $i=0$ と $i=1$ に適用すると両成分とも $M[p]$ 側の値に等しくなり、等式が閉じる。

最後に $m\leq n$ か $n\leq m$ かで場合分けする（原文の「$m$ と $n$ に対して対称」に当たる箇所）。$m\leq n$ のときは片側版を $(p,q)=(m,n)$ と仮定 $j_1<\textrm{Lng}(M[m])$ に適用してそのまま結論を得る。$n\leq m$ のときは片側版を $(p,q)=(n,m)$ と仮定 $j_1<\textrm{Lng}(M[n])$ に適用し、得られた等式の両辺を入れ替える。□

補題 B と片側版は仮定 $1\leq p$（したがって命題の $1\leq m$、$1\leq n$）を持つが、上の証明のどこでも使っていない。$m=0$ を除外しなくても同じ議論が通る。

## 原文通りに書けなかった理由

- **[Y]** 原文の証明が、命題の $j_0,j_1$ と $\textrm{operator}[]$ の定義中の $j_0,j_1$ を同じ記号で使っている

  命題の $j_0,j_1$ は切片の端点で、仮定は $j_0\leq j_1<\textrm{Lng}(M[m])$ である。一方、証明の冒頭「$\textrm{operator}[]$ の定義中の記号を $M$ に対して定義する」により $j_1:=\textrm{Lng}(M)-1$、$j_0:=$ 一意な親、と同じ文字が再定義される。実際、証明中の「$j_1>0$ かつ $M_{j_1}\neq(0,0)$ かつある非負整数 $j_0$ が存在して $(i_1,j_0)<^{\textrm{Next}}_M(i_1,j_1)$」は後者の意味でしか読めず、最後の「$j_0\leq j_1<\textrm{Lng}(M[m])$ であるから」は前者の意味でしか読めない。後者の意味で読むと、非退化分岐では $\textrm{Lng}(M[m])=j_0+m(j_1-j_0)$ なので $m=1$ のとき $\textrm{Lng}(M[1])=j_1$ となり、$j_1<\textrm{Lng}(M[m])$ は偽になってしまう。直し方は定義側の記号を別名（たとえば $j'_0,j'_1$）にするだけなので機械的である。Lean では命題の端点と定義中の親・末尾添字を別の変数にしている。

- **[W]** 原文は退化 3 分岐で $M[m]=M[n]$ となることを確かめていない

  原文は「$M[m]=M[n]$ ならば明らかに…である。よって $m\neq n$ かつ $j_1>0$ かつ $M_{j_1}\neq(0,0)$ かつ…であるとする」と書く。この「よって」は、$\textrm{operator}[]$ の残り 3 分岐（$j_1=0$ のとき $M[k]=M$、$M_{j_1}=(0,0)$ のとき $M[k]=\textrm{Pred}(M)$、一意な親が無いとき $M[k]=\textrm{Pred}(M)$）でいずれも値が $k$ に依存しないこと、したがって $M[m]=M[n]$ となることを使っているが、原文はそれを書いていない。Lean では補題 B の証明で 3 分岐を個別に開き、それぞれ $R=()$ を与えて埋めている。

- **[W]** 原文は $\textrm{Lng}(M[m])\leq\textrm{Lng}(M[n])$ を断らずに $M[n]$ の先頭 $\textrm{Lng}(M[m])$ 項を取っている

  原文の計算は $(M[n]_j)_{j=0}^{\textrm{Lng}(M[m])-1}$ から始まるが、これが $M[n]$ の接頭辞であるためには $\textrm{Lng}(M[m])-1<\textrm{Lng}(M[n])$ が要る。非退化分岐では $\textrm{Lng}(M[k])=j_0+k(j_1-j_0)$ が $k$ について単調なのでこれは成り立つが、原文はこの単調性に触れていない。Lean はこの一段を「ある $R$ が存在して $M[n]=M[m]\oplus_{\mathbb{N}^2}R$」という接頭辞の形に置き換え、長さの比較を経由せずに済ませている。主張は原文の等式と同値であり、命題の言明も下流も変わらない。

- **[R]** 原文の $m\neq n$ の仮定は使わない

  原文は $M[m]=M[n]$ の場合を先に片付け、残りを $m\neq n$ として扱う。Lean の補題 B は $m\leq n$（$m=n$ を含む）で一様に成立するので、$m=n$ を別扱いする必要が無い。結果として場合分けは「$m\leq n$ か $n\leq m$ か」の 1 回だけになり、原文の 2 段構えの場合分けの外側が消えている。

- **[R]** 命題の仮定 $M\in T_{\textrm{PS}}$ が要らない

  Lean の命題は $M$ が空列の場合も含む形になっている。$M=()$ のときは $\textrm{Lng}(M)-1=0$（自然数の切り捨て減算）なので「$j_1=0$ ならば $M[n]:=M$」の分岐が選ばれて $M[k]=M=()$ となり、仮定 $j_1<\textrm{Lng}(M[m])=0$ が偽なので命題は空虚に成り立つ。このため補題 B の分岐 (a) は原文の「$j_1=0$」ではなく「$\textrm{Lng}(M)\leq 1$」で切ってあり、$\textrm{Lng}(M)=0$ も同じ枝で処理される。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| ペア数列 | `PSS.PS`（`List (ℕ × ℕ)`） | `lean/PSS/Defs.lean` |
| $M\in T_{\textrm{PS}}$ | なし（仮定に置いていない） | — |
| $\textrm{Lng}(M)$ | `PSS.Lng` | `lean/PSS/Defs.lean` |
| $M_{i,j}$（範囲外は $0$） | `PSS.entry` | 同上 |
| $(M_j)_{j=a}^{b}$ | `PSS.seg` | 同上 |
| $\textrm{Pred}(M)$ | `PSS.Pred` | 同上 |
| $i_1$ | `PSS.idx1` | 同上 |
| $(i,j_0)<^{\textrm{Next}}_M(i,j_1)$ | `PSS.nextR`（`PSS.nextrel0` / `PSS.nextrel1`） | 同上 |
| 一意な親の存在 | `PSS.hasParent`（`PSS.parents` の長さが 1） | 同上 |
| 一意な親 $j_0$ | `PSS.parent` | 同上 |
| $M[n]$ | `PSS.oper M n` | 同上 |
| 補題 A（左接頭辞での成分不変性） | `entry_append_left` | `lean/Bijectivity/06-fseq-segment-invariance.lean` |
| 補題 B（基本列の接頭辞性） | `oper_prefix` | 同上 |
| 補題 B の (d) での $M[k]$ の表示 | `oper_prefix` 証明中の `hop` | 同上 |
| 片側版（$p\leq q$ での切片一致） | `oper_seg_invariance` 証明中の `key` | 同上 |
| 命題（基本列の切片の不変性） | `oper_seg_invariance` | 同上 |
| 連結の左側での要素取得 | `List.getElem?_append_left` | Lean 標準ライブラリ |
| 添字ごとの写像の一致 | `List.map_congr_left` | 同上 |
| ブロック列の連結 | `List.flatMap_append` | 同上 |
| 添字列 $(0,\dots,m+d-1)$ の分解 | `List.range_add` | 同上 |
| 添字列の元の条件 | `List.mem_range'` | 同上 |

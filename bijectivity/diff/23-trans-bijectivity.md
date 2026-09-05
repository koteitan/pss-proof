[← back](README.md)

# 23: 定理 (変換写像の全単射性)

## 原文

### 命題

定理 (変換写像の全単射性)（原文に番号は振られていない）

$\textrm{Trans}$は$CT_{\textrm{PS}}\to\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}$上で全域かつ全単射であり、特に同型写像である。

### 証明

  証明  
  可算な標準形の起源及び辞書式的順序が基本列的順序を含意することより任意の$M\in CT_{\textrm{PS}}$に対してある$v\in\mathbb{N}$が存在して$M\leq_{\textrm{PS}}((j,j))_{j=0}^v<_{\textrm{PS}}((j,j))_{j=0}^{v+1}\in CT_{\textrm{PS}}$であるから、$CT_{\textrm{PS}}=\bigcup_{M\in CT_{\textrm{PS}}}\{N\mid N\in CT_{\textrm{PS}}\land N<_{\textrm{PS}}M\}$である。  
  [4]のLemma 2.1より$\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}=\bigcup_{t_0\in\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}}\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}t_0\}$である。  
  対応する項の上界(2)より$\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}=\bigcup_{M\in CT_{\textrm{PS}}}\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}\textrm{Trans}(M)\}$である。  
  ペア数列の解析(2)より従う。□

## Lean

### Lean での命題

値域を

$$R:=\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}$$

と置く。主張は次の五つである。

(全域) 任意の$M\in CT_{\textrm{PS}}$に対して$\textrm{Trans}(M)\in R$。

(単射) 任意の$M,N\in CT_{\textrm{PS}}$に対して、$\textrm{Trans}(M)=\textrm{Trans}(N)$ならば$M=N$。

(全射) 任意の$t\in R$に対して、ある$M\in CT_{\textrm{PS}}$が存在して$\textrm{Trans}(M)=t$。

(全単射) 上の三つを合わせて、$\textrm{Trans}$は$CT_{\textrm{PS}}$から$R$への全単射である。

(同型) 任意の$M,N\in CT_{\textrm{PS}}$に対して$M<_{\textrm{PS}}N\iff\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(N)$。

さらに、原文の証明に現れる二つの被覆も独立の命題として置いてある。

(定義域の被覆) 任意の$M\in CT_{\textrm{PS}}$に対して、ある$N\in CT_{\textrm{PS}}$が存在して$M<_{\textrm{PS}}N$。

(値域の被覆) 任意の$t\in R$に対して、ある$M\in CT_{\textrm{PS}}$が存在して$t<_{\textrm{B}}\textrm{Trans}(M)$。

記号は次のとおりである。

- $OT_{\textrm{B}\omega}$は$D_\omega$を許す順序数項全体、すなわち字母$D_v$の添字$v$を$\mathbb{N}\cup\{\omega\}$から取ることを許した構造判定（principal 成分がそれ自身順序数項で、かつ広義降順に並ぶこと）を満たす項全体である。$D_\omega$-free 性を課さないので、原文の$OT_{\textrm{B}\omega}$そのものにあたる。
- $T_{\textrm{B}}$は$D_\omega$をどの深さにも含まない項全体、$OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}$である。
- $D_0D_\omega0$は principal 項$D_0(D_\omega(\varnothing))$である。添字$\omega$は自然数に $\top$ を付け加えた型の$\top$として表す。
- (定義域の被覆) は原文の$CT_{\textrm{PS}}=\bigcup_{M\in CT_{\textrm{PS}}}\{N\mid N\in CT_{\textrm{PS}}\land N<_{\textrm{PS}}M\}$の非自明な向き（右辺への包含）そのものである。逆向きの包含は右辺の各集合が$CT_{\textrm{PS}}$の部分集合であることから自明なので、命題としては置いていない。(値域の被覆) も同様に、原文の$\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}=\bigcup_{M\in CT_{\textrm{PS}}}\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}\textrm{Trans}(M)\}$の非自明な向きである。

### Lean での証明

**(定義域の被覆)** $M\in CT_{\textrm{PS}}$とする。可算な標準形の起源より、ある$v\in\mathbb{N}$が存在して$M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$である。$\leq_{\textrm{PS}[]}$の定義を開いて、全項が$1$以上の有限列$a$で

$$M=((j,j))_{j=0}^v[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$$

なるものを取る。$N:=((j,j))_{j=0}^{v+1}$と置き、この$N$が求めるものであることを示す。

$N\in CT_{\textrm{PS}}$は対角列が$CT_{\textrm{PS}}$の元であること（$0\leq v+1$より$((j,j))_{j=0}^{v+1}\in ST_{\textrm{PS}}$、かつ対角列の最左列が$(0,0)$）から従う。

次に$((j,j))_{j=0}^v<_{\textrm{PS}}N$を示す。対角列の長さは$\textrm{Lng}(((j,j))_{j=u}^w)=w+1-u$（自然数の切り捨て減算）だから$\textrm{Lng}(N)=(v+1)+1-0=v+2$である。$v+1<v+2$なので、真の接頭辞の補題

$$k<\textrm{Lng}(K)\ \Longrightarrow\ (K_j)_{j=0}^{k-1}<_{\textrm{PS}}K$$

を$K=N$、$k=v+1$に適用して$(N_j)_{j=0}^{v}<_{\textrm{PS}}N$を得る。ここで対角列の始切片の等式（$u\leq w$ならば$((j,j))_{j=0}^{w}$の先頭$u+1$項は$((j,j))_{j=0}^{u}$）を$u=v$、$w=v+1$に適用すると$(N_j)_{j=0}^{v}=((j,j))_{j=0}^v$なので、書き換えて$((j,j))_{j=0}^v<_{\textrm{PS}}N$である。

続いて$M\leq_{\textrm{PS}}((j,j))_{j=0}^v$を示す。反復展開の非増大性

$$a\text{ の全項が }1\text{ 以上}\ \Longrightarrow\ K[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\leq_{\textrm{PS}}K$$

を上で取った$a$と$K=((j,j))_{j=0}^v$に適用し、$M$の表示で書き換えればよい。

最後に$\leq_{\textrm{PS}}$と$<_{\textrm{PS}}$の合成（$A\leq_{\textrm{PS}}B$かつ$B<_{\textrm{PS}}C$ならば$A<_{\textrm{PS}}C$。$A=B$なら仮定そのもの、$A<_{\textrm{PS}}B$なら$<_{\textrm{PS}}$の推移律）により$M<_{\textrm{PS}}N$。

**(値域の被覆)** $t\in R$、すなわち$t\in OT_{\textrm{B}\omega}$かつ$t<_{\textrm{B}}D_0D_\omega0$とする。対応する項の上界未満の字母

$$t<_{\textrm{B}}D_0D_\omega0\ \Longrightarrow\ (t\in OT_{\textrm{B}\omega}\iff t\in OT_{\textrm{B}})$$

を$t<_{\textrm{B}}D_0D_\omega0$に適用し、その左から右の向きに$t\in OT_{\textrm{B}\omega}$を渡して$t\in OT_{\textrm{B}}$を得る。$OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}$の第二成分を取れば$t\in T_{\textrm{B}}$である。これで対応する項の上界(2)

$$t\in T_{\textrm{B}}\land t<_{\textrm{B}}D_0D_\omega0\ \Longrightarrow\ \exists M\in CT_{\textrm{PS}},\ t<_{\textrm{B}}\textrm{Trans}(M)$$

の仮定が二つとも揃うので、これを適用して$M\in CT_{\textrm{PS}}$と$t<_{\textrm{B}}\textrm{Trans}(M)$を得る。

**(全域)** $M\in CT_{\textrm{PS}}$とする。$CT_{\textrm{PS}}$の定義は$M\in ST_{\textrm{PS}}$と$M_0=(0,0)$の連言だから、第一成分$M\in ST_{\textrm{PS}}$が取れる。[1] の Trans が標準形を保つこと（$M\in ST_{\textrm{PS}}\Rightarrow\textrm{Trans}(M)\in OT_{\textrm{B}}$）を適用し、$OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}$の第一成分を取って$\textrm{Trans}(M)\in OT_{\textrm{B}\omega}$。もう一方の$\textrm{Trans}(M)<_{\textrm{B}}D_0D_\omega0$は対応する項の上界(1)そのものである。二つを組にして$\textrm{Trans}(M)\in R$。

**(単射)** 変換写像の順序数への全単射性の単射性をそのまま用いる。すなわち$M,N\in CT_{\textrm{PS}}$で$\textrm{Trans}(M)=\textrm{Trans}(N)$とし、$<_{\textrm{PS}}$の三分律で$M<_{\textrm{PS}}N$、$M=N$、$N<_{\textrm{PS}}M$に分ける。第一の場合、Trans が順序を保つことより$\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(N)$だが、仮定の等式で書き換えると$\textrm{Trans}(N)<_{\textrm{B}}\textrm{Trans}(N)$となり$<_{\textrm{B}}$の非反射性に反する。第三の場合も$M$と$N$を入れ替えて同じ。よって$M=N$。

**(全射)** $t\in R$とする。上の (値域の被覆) より$M\in CT_{\textrm{PS}}$と$t<_{\textrm{B}}\textrm{Trans}(M)$を取る。$t\in OT_{\textrm{B}\omega}$（$t\in R$の第一成分）と合わせて

$$t\in\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}\textrm{Trans}(M)\}$$

である。ペア数列の解析(2)の全射性をこの$M$に適用すると、$N$で$N\in CT_{\textrm{PS}}$かつ$N<_{\textrm{PS}}M$かつ$\textrm{Trans}(N)=t$なるものが得られる。得られた連言のうち$N<_{\textrm{PS}}M$は捨て、$N\in CT_{\textrm{PS}}$と$\textrm{Trans}(N)=t$だけを結論に渡す。

**(全単射)** (全域)(単射)(全射) の三つを組にする。

**(同型)** ペア数列の解析(2)の順序同値部分をそのまま用いる。すなわち$M,N\in CT_{\textrm{PS}}$に対し、左から右は Trans が順序を保つことそのものである。右から左は$<_{\textrm{PS}}$の三分律で場合分けし、$M=N$なら$\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(M)$となって$<_{\textrm{B}}$の非反射性に反し、$N<_{\textrm{PS}}M$なら Trans が順序を保つことより$\textrm{Trans}(N)<_{\textrm{B}}\textrm{Trans}(M)$なので、仮定$\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(N)$と$<_{\textrm{B}}$の推移律から$\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(M)$となってやはり非反射性に反する。残るのは$M<_{\textrm{PS}}N$。

## 原文通りに書けなかった理由

- **[R]** 対角列の狭義増大$((j,j))_{j=0}^v<_{\textrm{PS}}((j,j))_{j=0}^{v+1}$に、原文が挙げる辞書式的順序が基本列的順序を含意することを使っていない

  原文は$M\leq_{\textrm{PS}}((j,j))_{j=0}^v<_{\textrm{PS}}((j,j))_{j=0}^{v+1}$の連鎖全体を、可算な標準形の起源と辞書式的順序が基本列的順序を含意することの二つから出すと書く。この形式化では前半$M\leq_{\textrm{PS}}((j,j))_{j=0}^v$にはその命題の$\leq$版（反復展開の非増大性）だけを使い、後半の狭義不等号は真の接頭辞の補題「$k<\textrm{Lng}(K)$ならば$(K_j)_{j=0}^{k-1}<_{\textrm{PS}}K$」と対角列の始切片の等式から直接出している。原文の道筋で後半を出すには、まず$((j,j))_{j=0}^v<_{\textrm{PS}[]}((j,j))_{j=0}^{v+1}$を言う必要があり、それには標準形の始切片への経路（原文はここでは引いていない）が要る。さらに辞書式的順序が基本列的順序を含意することは逐語形では偽で、$\textrm{Lng}(N)>1$（あるいは$M\neq N$）の補正が要る（項目 05 の訂正）。接頭辞の補題を使うとこの二つがどちらも不要になる。

- **[W]** 値域の元が$D_\omega$-free であることの確認が原文では埋まっていない

  対応する項の上界(2)の仮定は$t\in T_{\textrm{B}}$、すなわち$t$が$D_\omega$をどの深さにも含まないことである。ところが原文がこれを適用する相手は$OT_{\textrm{B}\omega}$の元、つまり$D_\omega$を含みうる項であり、$t\in T_{\textrm{B}}$は仮定に入っていない。この形式化では対応する項の上界未満の字母（$t<_{\textrm{B}}D_0D_\omega0$ならば$t\in OT_{\textrm{B}\omega}\iff t\in OT_{\textrm{B}}$）を一段挟み、$t\in OT_{\textrm{B}\omega}$と$t<_{\textrm{B}}D_0D_\omega0$から$t\in OT_{\textrm{B}}$を出し、その$T_{\textrm{B}}$成分を取って仮定を揃えている。原文はこの補題を対応する項の上界の周辺（変換写像の順序数への全単射性、ペア数列の解析）では引いているが、本定理の証明では言及していない。

- **[R]** [4] の Lemma 2.1 による値域の自己分解が要らなかった

  原文は値域をまず$\bigcup_{t_0\in R}\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}t_0\}$と分解し（[4] の Lemma 2.1）、その後で対応する項の上界(2)により$t_0$を$\textrm{Trans}(M)$に置き換える、という二段構えを取る。この形式化では$t\in R$に対していきなり対応する項の上界(2)を適用して$M\in CT_{\textrm{PS}}$と$t<_{\textrm{B}}\textrm{Trans}(M)$を得るので、中間の自己分解は現れず、[4] の Lemma 2.1 もこの命題では引かない。

- **[R]** 定義域側の分解$CT_{\textrm{PS}}=\bigcup_{M\in CT_{\textrm{PS}}}\{N\mid N\in CT_{\textrm{PS}}\land N<_{\textrm{PS}}M\}$が結論に使われていない

  この形式化にも原文どおり (定義域の被覆) を置いて証明してあるが、(全域)(単射)(全射) のどれもこれを経由しない。(全域) は Trans が標準形を保つことと対応する項の上界(1)から直接、(単射) は Trans が順序を保つことと$<_{\textrm{PS}}$の三分律から直接、(全射) は (値域の被覆) とペア数列の解析(2)だけから出る。原文の「ペア数列の解析(2)より従う」を、両側の分解に沿って各片の同型を貼り合わせる議論として読むと、たとえば (全域) は$M<_{\textrm{PS}}M'$なる$M'$を (定義域の被覆) で取り、ペア数列の解析(2)を$M'$に適用して$\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(M')<_{\textrm{B}}D_0D_\omega0$と繋ぐことになるが、その回り道は要らなかった。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $M<_{\textrm{PS}}N$ | `ltPS M N`（記法 `M <ₚ N`） | `lean/Bijectivity/Defs.lean` |
| $M\leq_{\textrm{PS}}N$ | `lePS M N` | 同上 |
| $M\leq_{\textrm{PS}[]}N$ | `leExpPS M N` | 同上 |
| $K[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$ | `expand K a` | 同上 |
| $M\in CT_{\textrm{PS}}$ | `CTPS M` | 同上 |
| $M[n]$ | `PSS.oper M n` | `lean/PSS/Defs.lean` |
| $M\in ST_{\textrm{PS}}$ | `PSS.STPS M` | `lean/PSS/Standard.lean` |
| $((j,j))_{j=u}^v$ | `PSS.diagSeq u v` | `lean/PSS/Red.lean` |
| $\textrm{Trans}$ | `PSS.Trans` | `lean/PSS/Trans.lean` |
| $t<_{\textrm{B}}s$ | `lessBT t s` | `lean/Buchholz-1986/Buchholz-1986-2.1.lean` |
| $D_0D_\omega0$ | `DzeroDomegaZero` | `lean/Bijectivity/Cited.lean` |
| $OT_{\textrm{B}\omega}$ | `PSS.OT` | `lean/Buchholz-1986/Buchholz-1986-2.2.lean` |
| $T_{\textrm{B}}$ | `PSS.T_B` | 同上 |
| $OT_{\textrm{B}}$ | `PSS.OT_B` | 同上 |
| 値域 $R$ | `TransRange` | `lean/Bijectivity/23-trans-bijectivity.lean` |
| 定義域の被覆 | `ctps_cover` | 同上 |
| 値域の被覆 | `transRange_cover` | 同上 |
| (全域) | `trans_mapsTo` | 同上 |
| (単射) | `trans_bij_injOn` | 同上 |
| (全射) | `trans_surjOn` | 同上 |
| (全単射) | `trans_bijOn` | 同上 |
| (同型) | `trans_order_iso` | 同上 |
| 可算な標準形の起源 | `ctps_iff_leExpPS` | `lean/Bijectivity/10-countable-standard-origin.lean` |
| 対角列の最左列 | `headD_diagSeq` | 同上 |
| 反復展開の非増大性 | `expand_lePS` | `lean/Bijectivity/05-exp-implies-lex.lean` |
| 真の接頭辞の補題 | `ltPS_take` | `lean/Bijectivity/02b-lex-list-lemmas.lean` |
| 対角列の長さ | `length_diagSeq` | `lean/Bijectivity/12c-big-step.lean` |
| 対角列の始切片 | `diagSeq_take` | 同上 |
| $\leq_{\textrm{PS}}$ と $<_{\textrm{PS}}$ の合成 | `lePS_ltPS_trans` | 同上 |
| $<_{\textrm{PS}}$ の推移律 | `ltPS_trans` | `lean/Bijectivity/02-lex-linear.lean` |
| $<_{\textrm{PS}}$ の三分律 | `ltPS_trichotomy` | 同上 |
| 対角列が $CT_{\textrm{PS}}$ の元であること | `ctps_diagSeq` | `lean/Bijectivity/20-term-upper-bound.lean` |
| 対応する項の上界(1) | `trans_lt_bound` | 同上 |
| 対応する項の上界(2) | `exists_trans_gt` | 同上 |
| 対応する項の上界未満の字母 | `OT_iff_OT_B_of_lt` | `lean/Bijectivity/19-alphabet-below-bound.lean` |
| Trans が標準形を保つこと | `Trans_STPS_OT_B` | `lean/8/8.7-termination.lean` |
| Trans が順序を保つこと | `trans_lessBT_of_ltPS` | `lean/Bijectivity/18-trans-preserves-order.lean` |
| $<_{\textrm{B}}$ の非反射性 | `lessBT_linear_irrefl` | `lean/Buchholz-1986/Buchholz-1986-2.1-order.lean` |
| $<_{\textrm{B}}$ の推移律 | `lessBT_linear_trans` | 同上 |
| 変換写像の順序数への全単射性の単射性 | `trans_injOn` | `lean/Bijectivity/21-ordinal-bijectivity.lean` |
| ペア数列の解析(2)の全射性 | `analysis_term_surjOn` | `lean/Bijectivity/22-pair-sequence-analysis.lean` |
| ペア数列の解析(2)の順序同値 | `analysis_term_lt` | 同上 |
| 標準形の始切片への経路（本証明では未使用） | `seg_leExpPS` | `lean/Bijectivity/11-path-to-initial-segment.lean` |

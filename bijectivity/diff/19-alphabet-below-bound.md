[< back](README.md)

# 19: 補題 (対応する項の上界未満の字母)

## 原文

### 命題

補題 (対応する項の上界未満の字母)（原文に番号は振られていない）

任意の$t\in T_{\textrm{B}\omega}$に対して、$t<_{\textrm{B}}D_0D_\omega0$ならば$t\in OT_{\textrm{B}\omega}$は$t\in OT_{\textrm{B}}$と同値である。

### 証明

&nbsp;&nbsp;証明  
&nbsp;&nbsp;(⇒) 任意の$t'\in OT_{\textrm{B}\omega}$をとり、$t'<_{\textrm{B}}D_\omega0$かつ$D_0t'\in OT_{\textrm{B}\omega}$とする。  
&nbsp;&nbsp;&nbsp;&nbsp;仮定及び$OT_{\textrm{B}\omega}$の定義より任意の$x\in G_0t'$に対して$x<_{\textrm{B}}D_\omega0$である。  
&nbsp;&nbsp;&nbsp;&nbsp;$t'$が字母$D_\omega$を含むとする。  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;ある$u\in\mathbb{N}\cup\{\omega\}$と$a\in OT_{\textrm{B}\omega}$が存在して$t'=D_ua$とすると、仮定より$u=\omega$またはある$b\in OT_{\textrm{B}\omega}$が存在して$D_\omega b\in G_ua\subset G_0t'$であるが、いずれも矛盾する。  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;ある$u\in(\mathbb{N}\cup\{\omega\})^{<\omega}$と$a\in OT_{\textrm{B}\omega}^{<\omega}$が存在して$\textrm{Lng}(a)=\textrm{Lng}(u)\geq2$かつ$t'=\underline{(}D_{u_0}a_0\underline{,}\cdots\underline{,}D_{\textrm{Lng}(a)-1}a_{\textrm{Lng}(a)-1}\underline{)}$とする。  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;仮定よりある非負整数$0\leq i<\textrm{Lng}(a)$が存在して$u_i=\omega$またはある$b\in OT_{\textrm{B}\omega}$が存在して$D_\omega b\in G_{u_i}a_i\subset G_0t'$である。  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$OT_{\textrm{B}\omega}$の定義より任意の非負整数$0\leq i<\textrm{Lng}(a)$に対して$D_{u_i}a_i\leq_{\textrm{B}}D_{u_0}a_0<_{\textrm{B}}t'$である。  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;ある非負整数$0\leq i<\textrm{Lng}(a)$が存在して$u_i=\omega$とすると、上が$t'<_{\textrm{B}}D_\omega0$と矛盾する。  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;ある非負整数$0\leq i<\textrm{Lng}(a)$と$b\in OT_{\textrm{B}\omega}$が存在して$D_\omega b\in G_{u_i}a_i\subset G_0t'$であるとすると、任意の$x\in G_0t'$に対して$x<_{\textrm{B}}D_\omega0$であることと矛盾する。  
&nbsp;&nbsp;&nbsp;&nbsp;いずれの場合も矛盾するため$t'$は字母$D_\omega$を含まない。  
&nbsp;&nbsp;$t=0$ならば$t\in T_{\textrm{PS}}$である。  
&nbsp;&nbsp;$t$が単項であるとする。  
&nbsp;&nbsp;&nbsp;&nbsp;$OT_{\textrm{B}\omega}$の定義及び条件よりある$a\in OT_{\textrm{B}\omega}$が存在して$t<_{\textrm{B}}D_\omega0$かつ$t=D_0a$である。  
&nbsp;&nbsp;&nbsp;&nbsp;上より$a$は字母$D_\omega$を含まないから$t\in T_{\textrm{PS}}$である。  
&nbsp;&nbsp;$t$が複項であるとする。  
&nbsp;&nbsp;&nbsp;&nbsp;$OT_{\textrm{B}}$の定義よりある$a\in OT_{\textrm{B}\omega}^{<\omega}\setminus\{()\}$が存在して$D_0a_0<_{\textrm{B}}t$かつ$t=\underline{(}D_0a_0\underline{,}\cdots\underline{,}D_0a_{\textrm{Lng}(a)-1}\underline{)}$である。  
&nbsp;&nbsp;&nbsp;&nbsp;上より任意の非負整数$0\leq i<\textrm{Lng}(a)$に対して$a_i\leq_{\textrm{B}}a_0<_{\textrm{B}}D_\omega0$である。  
&nbsp;&nbsp;&nbsp;&nbsp;上より任意の非負整数$0\leq i<\textrm{Lng}(a)$に対して$a_i$は字母$D_\omega$を含まないから$t\in T_{\textrm{PS}}$である。  
&nbsp;&nbsp;よっていずれの場合でも$t\in T_{\textrm{PS}}$である。  
&nbsp;&nbsp;よって$t\in OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{PS}}$である。  
&nbsp;&nbsp;(⇐) $OT_{\textrm{B}}\subset OT_{\textrm{B}\omega}$より即座に従う。□

## Lean

### Lean での命題

この形式化では Buchholz の項を構文木として持つ。

- 項 $t$ は主項の有限列 $t=\underline{(}p_0\underline{,}\cdots\underline{,}p_{k-1}\underline{)}$ であり、$k=0$（空列）が $0$ である。主項は $p=D_vb$ の形で、$v\in\mathbb{N}\cup\{\omega\}$、$b$ は項。$D_\omega$ を許す項全体 $T_{\textrm{B}\omega}$ は項の型そのものなので、原文の「任意の $t\in T_{\textrm{B}\omega}$」は「任意の項 $t$」になる。
- $<_{\textrm{B}}$ は主項列の辞書式順序である。$()<_{\textrm{B}}\underline{(}q\underline{,}s'\underline{)}$、$\underline{(}p\underline{,}s\underline{)}<_{\textrm{B}}()$ は偽、$\underline{(}p\underline{,}s\underline{)}<_{\textrm{B}}\underline{(}q\underline{,}s'\underline{)}$ は $p<_{\textrm{B}}q$ または（$p=q$ かつ $\underline{(}s\underline{)}<_{\textrm{B}}\underline{(}s'\underline{)}$）。主項どうしは $D_ub<_{\textrm{B}}D_vc:\iff u<v\lor(u=v\land b<_{\textrm{B}}c)$。$\leq_{\textrm{B}}$ は $<_{\textrm{B}}$ または $=$ の略記。
- $G_ut$ は有限リストとして計算する。$G_u\underline{(}p_0\underline{,}\cdots\underline{,}p_{k-1}\underline{)}=G_up_0\oplus\cdots\oplus G_up_{k-1}$、$G_u(D_vb)=(b)\oplus G_ub$（$u\leq v$ のとき）、$G_u(D_vb)=()$（$u>v$ のとき）。
- 「字母 $D_\omega$ を含まない」は構造判定で定める。$\underline{(}p_0\underline{,}\cdots\underline{)}$ が $D_\omega$-free $:\iff$ 各 $p_i$ が $D_\omega$-free、$D_vb$ が $D_\omega$-free $:\iff v\neq\omega$ かつ $b$ が $D_\omega$-free。$T_{\textrm{B}}$ はこの判定を満たす項全体。
- $OT_{\textrm{B}\omega}$ は [4] の順序数項の構造判定である。項 $\underline{(}p_0\underline{,}\cdots\underline{,}p_{k-1}\underline{)}$ が順序数項 $:\iff$ 各 $p_i$ が順序数主項であり、かつ列が広義降順（隣接して $\underline{(}p_{i+1}\underline{)}\leq_{\textrm{B}}\underline{(}p_i\underline{)}$）。主項 $D_vb$ が順序数主項 $:\iff$ $b$ が順序数項であり、かつ任意の $x\in G_vb$ に対して $x<_{\textrm{B}}b$。
- $OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}$。原文が最終行に置く等式をこちらは定義として採る。

命題は次のとおりで、原文の言明と同じである。

$$\forall t,\quad t<_{\textrm{B}}D_0D_\omega0\ \Longrightarrow\ \bigl(t\in OT_{\textrm{B}\omega}\iff t\in OT_{\textrm{B}}\bigr)$$

### Lean での証明

#### 1. 順序の分解（小道具）

**(1a) $0$ 未満の項は無い.** 任意の項 $a$ に対して $a<_{\textrm{B}}0$ は偽。辞書式順序の定義で右辺が空列になる 2 つの枝（空列対空列、非空対空列）がどちらも偽であることによる。

**(1b) 単一主項との比較.** $\underline{(}p\underline{,}s\underline{)}<_{\textrm{B}}\underline{(}q\underline{)}$ ならば $p<_{\textrm{B}}q$。辞書式順序の第 2 枝は $p=q$ かつ $\underline{(}s\underline{)}<_{\textrm{B}}()$ を要求するが、(1a) よりこれは偽だから、第 1 枝が成り立つ。

**(1c) 主項比較の分解.** $D_wa<_{\textrm{B}}D_vb$ ならば $w<v$ または（$w=v$ かつ $a<_{\textrm{B}}b$）。主項の順序の定義そのもの。

**(1d) 主項の広義比較の分解.** $\underline{(}D_wa\underline{)}\leq_{\textrm{B}}\underline{(}D_vb\underline{)}$ ならば $w<v$ または（$w=v$ かつ $a\leq_{\textrm{B}}b$）。狭義の場合は (1b) と (1c)、等号の場合は $w=v$ かつ $a=b$ なので $a\leq_{\textrm{B}}a$。

**(1e) 広義降順列の頭が上界であること.** 主項列 $\underline{(}p\underline{,}p_1\underline{,}\cdots\underline{,}p_{m}\underline{)}$ が広義降順ならば、任意の $i$ に対して $\underline{(}p_i\underline{)}\leq_{\textrm{B}}\underline{(}p\underline{)}$。列の長さに関する再帰で示す。$p_1$ については降順条件そのもの、$i\geq2$ については $\underline{(}p_1\underline{,}\cdots\underline{)}$ についての再帰の結論 $\underline{(}p_i\underline{)}\leq_{\textrm{B}}\underline{(}p_1\underline{)}$ と降順条件 $\underline{(}p_1\underline{)}\leq_{\textrm{B}}\underline{(}p\underline{)}$ を $\leq_{\textrm{B}}$ の推移性でつなぐ。

#### 2. 添字の評価

**(2a) 添字が $\omega$ でないこと.** 主項列 $(p_i)_{i=0}^{k-1}$（$p_i=D_{w_i}a_i$）が広義降順で $\underline{(}p_0\underline{,}\cdots\underline{,}p_{k-1}\underline{)}<_{\textrm{B}}\underline{(}D_\omega0\underline{)}$ ならば、すべての $i$ で $w_i\neq\omega$。

頭について (1b) と (1c) を使うと $w_0<\omega$ または（$w_0=\omega$ かつ $a_0<_{\textrm{B}}0$）であり、後者は (1a) で否定されるので $w_0<\omega$、特に $w_0\neq\omega$。$i\geq1$ については (1e) で $\underline{(}p_i\underline{)}\leq_{\textrm{B}}\underline{(}p_0\underline{)}$ を得てから (1d) を使い、$w_i<w_0<\omega$ または $w_i=w_0\neq\omega$ のいずれでも $w_i\neq\omega$ となる。これが原文の 2 行「$D_{u_i}a_i\leq_{\textrm{B}}D_{u_0}a_0$」「$u_i=\omega$ とすると $t'<_{\textrm{B}}D_\omega0$ と矛盾する」にあたる。

**(2b) 添字が $0$ であること.** 主項列 $(p_i)$ が広義降順で $\underline{(}p_0\underline{,}\cdots\underline{,}p_{k-1}\underline{)}<_{\textrm{B}}D_0D_\omega0$ ならば、すべての $i$ で $w_i=0$。頭について (1b) と (1c) より $w_0<0$（$\mathbb{N}\cup\{\omega\}$ では不可能）または $w_0=0$ かつ $a_0<_{\textrm{B}}D_\omega0$。$i\geq1$ については (1e) と (1d) より $w_i<w_0=0$（不可能）または $w_i=w_0=0$。

#### 3. $G_0$ の一段展開

$0\leq v$ は常に成り立つので $G_0(D_va)=(a)\oplus G_0a$ であり、したがって

$$G_0\underline{(}D_wa\underline{,}s\underline{)}=\bigl((a)\oplus G_0a\bigr)\oplus G_0\underline{(}s\underline{)}.$$

以下ではこの分解で $G_0$ のメンバーシップを 3 通りに分ける。

#### 4. 原文 (⇒) の内側の補助主張

原文の $t'$ についての主張を、項と主項列の相互再帰の形で置く。

**(4a) 項側.** $t\in OT_{\textrm{B}\omega}$、$t<_{\textrm{B}}D_\omega0$、かつ任意の $x\in G_0t$ に対して $x<_{\textrm{B}}D_\omega0$ ならば、$t$ は字母 $D_\omega$ を含まない。

**(4b) 主項列側.** 主項列 $(p_i)$ の各主項が順序数主項であり、すべての添字が $\omega$ と異なり、かつ任意の $x\in G_0\underline{(}p_0\underline{,}\cdots\underline{)}$ に対して $x<_{\textrm{B}}D_\omega0$ ならば、$(p_i)$ は字母 $D_\omega$ を含まない。

(4a) の証明: $t=\underline{(}p_0\underline{,}\cdots\underline{)}$ と書く。$t\in OT_{\textrm{B}\omega}$ から「各 $p_i$ が順序数主項」と「列が広義降順」を取り出す。降順と $t<_{\textrm{B}}D_\omega0$ に (2a) を適用して全添字が $\omega$ と異なることを得る。$G_0t$ は主項列としての $G_0$ の値そのものなので、有界性の仮定はそのまま (4b) に渡せる。

(4b) の証明: 空列のときは主張は空虚に成り立つ。$\underline{(}D_wa\underline{,}s\underline{)}$ のときは次の 4 つを順に作る。

1. 順序数主項の条件の第 1 連言肢から $a\in OT_{\textrm{B}\omega}$。
2. 3 の分解より $a$ は $G_0\underline{(}D_wa\underline{,}s\underline{)}$ の元なので、有界性の仮定から $a<_{\textrm{B}}D_\omega0$。
3. 同じ分解より $G_0a\subset G_0\underline{(}D_wa\underline{,}s\underline{)}$ なので、$G_0a$ の各元も $D_\omega0$ 未満。1-3 を (4a) の再帰呼び出しに渡して、$a$ が $D_\omega$-free。
4. 残りの列 $\underline{(}s\underline{)}$ については、順序数主項条件・添字条件・$G_0$ 有界性がいずれも部分列に落ちるので、(4b) の再帰呼び出しで $\underline{(}s\underline{)}$ が $D_\omega$-free。

添字条件から $w\neq\omega$ なので、$D_wa$ が $D_\omega$-free、したがって列全体も $D_\omega$-free。再帰は項と主項列の構造に沿って減少するので停止する。

原文が $t'$ に課す 3 つ目の仮定 $D_0t'\in OT_{\textrm{B}\omega}$ は、ここでは「$G_0t$ の全元が $D_\omega0$ 未満」に置き換えてある。原文はこの置き換えを (⇒) の冒頭 1 行（$D_0t'\in OT_{\textrm{B}\omega}$ と $t'<_{\textrm{B}}D_\omega0$ から $G_0t'$ の元が $D_\omega0$ 未満）で行うが、その先で内側へ降りるときに $D_0t'$ の形は復元できない。実際、主項 $D_wa$ の順序数主項条件が与えるのは「$G_wa$ の元が $a$ 未満」であって、$D_0a\in OT_{\textrm{B}\omega}$ が要求する「$G_0a$ の元が $a$ 未満」ではない（$w>0$ なら $G_wa\subsetneq G_0a$ になりうる）。$G_0$ 有界性の側は 3 の分解でそのまま内側へ落ちるので、再帰に耐えるのはこちらである。

#### 5. $G_0$ の有界性

**(5)** 主項列 $(p_i)$ の各主項が順序数主項であり、各 $p_i=D_0a_i$（添字がすべて $0$）で $a_i<_{\textrm{B}}D_\omega0$ ならば、任意の $x\in G_0\underline{(}p_0\underline{,}\cdots\underline{)}$ に対して $x<_{\textrm{B}}D_\omega0$。

頭 $D_0a_0$ の順序数主項条件は「任意の $y\in G_0a_0$ に対して $y<_{\textrm{B}}a_0$」である。添字が $0$ なので、条件に現れる $G_{v}$ がちょうど $G_0$ になる点が効いている。3 の分解で $x$ を場合分けし、

- $x=a_0$ なら仮定 $a_0<_{\textrm{B}}D_\omega0$ そのもの、
- $x\in G_0a_0$ なら $x<_{\textrm{B}}a_0$ と $a_0<_{\textrm{B}}D_\omega0$ を $<_{\textrm{B}}$ の推移性でつなぐ、
- $x\in G_0\underline{(}s\underline{)}$ なら残りの列についての再帰、

で結論する。これが原文の「仮定及び $OT_{\textrm{B}\omega}$ の定義より任意の $x\in G_0t'$ に対して $x<_{\textrm{B}}D_\omega0$ である」にあたる。ただし原文が $t'$ を $D_0$ で包んで $G_0t'$ を押さえるのに対し、こちらは $t$ の主項自身の添字が $0$ であることを使って $t$ の主項列全体について一度に押さえる。

#### 6. 主定理

**(⇒)** $t\in OT_{\textrm{B}\omega}$ と $t<_{\textrm{B}}D_0D_\omega0$ から $t\in T_{\textrm{B}}$ を示す。$t$ が空列（すなわち $0$）のときは $D_\omega$-free の判定が定義から真になる。$t=\underline{(}D_wa\underline{,}s\underline{)}$ のときは、

1. $t<_{\textrm{B}}D_0D_\omega0$ に (1b) と (1c) を使うと、$w<0$（$\mathbb{N}\cup\{\omega\}$ では不可能）または $w=0$ かつ $a<_{\textrm{B}}D_\omega0$。よって頭の添字は $0$、本体は $D_\omega0$ 未満。
2. 残りの主項 $D_{w'}a'$ については、$t\in OT_{\textrm{B}\omega}$ の降順条件に (1e) を適用して $\underline{(}D_{w'}a'\underline{)}\leq_{\textrm{B}}\underline{(}D_0a\underline{)}$ を得、(1d) で $w'<0$（不可能）または $w'=0$ かつ $a'\leq_{\textrm{B}}a$。後者と 1 の $a<_{\textrm{B}}D_\omega0$ を $\leq_{\textrm{B}}$ と $<_{\textrm{B}}$ の合成でつないで $a'<_{\textrm{B}}D_\omega0$。これが原文の $a_i\leq_{\textrm{B}}a_0<_{\textrm{B}}D_\omega0$ にあたる。
3. 1 と 2 より $t$ の全主項は添字 $0$ かつ本体 $D_\omega0$ 未満なので、(5) を適用して $G_0t$ の全元が $D_\omega0$ 未満。
4. 添字が $0$ であることから添字は $\omega$ と異なる。$t\in OT_{\textrm{B}\omega}$ の第 1 連言肢（各主項が順序数主項）と 3 と合わせて (4b) を $t$ の主項列に一度だけ適用すると、$t$ は $D_\omega$-free、すなわち $t\in T_{\textrm{B}}$。

$t\in OT_{\textrm{B}\omega}$ と $t\in T_{\textrm{B}}$ から $t\in OT_{\textrm{B}}$。

**(⇐)** $OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}$ の第 1 連言肢を取る。仮定 $t<_{\textrm{B}}D_0D_\omega0$ は使わない。

#### 7. 同ファイルに置かれた $\textrm{dom}$ の分類（本補題では使わない）

同じファイルには、後の命題（変換写像の順序数への全単射性）で後続・極限の場合分けに使う $\textrm{dom}$ の分類が置かれている。本補題の証明では使わないが、(2b) を共有している。$\textrm{dom}$ は $\varnothing$、$\{0\}$、$\mathbb{N}$、$T_u$ の 4 値をとる有限タグとして計算され、$\textrm{dom}(0)=\varnothing$、$\textrm{dom}(D_vb)$ は $b=0$ のとき $v=0$ なら $\{0\}$、$v=\omega$ なら $\mathbb{N}$、それ以外は $T_{v-1}$、$b\neq0$ のとき $\textrm{dom}(b)=\{0\}$ なら $\mathbb{N}$、$\textrm{dom}(b)=T_u$ なら $v\leq u$ のとき $\mathbb{N}$ そうでなければ $T_u$、それ以外は $\textrm{dom}(b)$ である。

- 主項列の $\textrm{dom}$ は末尾の主項の $\textrm{dom}$ に等しい（列の長さに関する再帰）。
- $D_vb$ の $\textrm{dom}$ は $\varnothing$ でない（$b=0$ の 3 分岐と $b\neq0$ の場合分けを、項側「$t\neq0$ なら $\textrm{dom}(t)\neq\varnothing$」および列側「空でない列の $\textrm{dom}$ は $\varnothing$ でない」との相互再帰で示す）。系として $\textrm{dom}(t)=\varnothing\iff t=0$。
- $t\in OT_{\textrm{B}\omega}$、$t<_{\textrm{B}}D_0D_\omega0$、$t\neq0$ ならば $\textrm{dom}(t)=\{0\}$ または $\textrm{dom}(t)=\mathbb{N}$（原文の $\textrm{dom}(t)=1$ と $\textrm{dom}(t)=\omega$）。末尾の主項 $D_vb$ の添字は (2b) より $v=0$ であり、$b=0$ なら $\{0\}$、$b\neq0$ なら $\textrm{dom}(b)\neq\varnothing$ から $\textrm{dom}(b)\in\{\{0\},\mathbb{N},T_u\}$ で、それぞれ $\mathbb{N}$、$\mathbb{N}$、$0\leq u$ より $\mathbb{N}$ になる。

## 原文通りに書けなかった理由

- **[W]** (⇒) の内側の補助主張に帰納法が無く、内側の場合の根拠が成り立たない

  原文は $t'$ が字母 $D_\omega$ を含むと仮定して、$t'$ が単項の場合と複項の場合に分けて矛盾を出す。しかし単項 $t'=D_ua$ の場合の根拠「$u=\omega$ またはある $b$ が存在して $D_\omega b\in G_ua\subset G_0t'$」は、$t'$ が $D_\omega$ を含むことからは従わない。$t'=D_0D_\omega0$ が反例で、$u=0\neq\omega$ であり $G_0(D_\omega0)=(0)$ は $D_\omega b$ の形の元を含まないのに、$t'$ は $D_\omega$ を含む。この $t'$ は $t'\in OT_{\textrm{B}\omega}$ と $t'<_{\textrm{B}}D_\omega0$ を満たすので、排除するには 3 つ目の仮定を使うほかない。正しい筋は「$a$ 自身が $G_0t'$ の元で $a<_{\textrm{B}}D_\omega0$ だから、$a$ について同じ主張を繰り返す」であって、原文にはこの繰り返し（帰納法）が無い。複項の場合も同様で、$D_\omega b\in G_{u_i}a_i$ という witness の形は保証されない。

  この形式化では 4 のとおり、項と主項列についての相互構造再帰に組み替えてある。あわせて、再帰に耐えるように仮定を $D_0t'\in OT_{\textrm{B}\omega}$ から「$G_0t$ の全元が $D_\omega0$ 未満」へ一般化した（原文の仮定はこれを含意する）。理由は 4 の末尾に書いたとおり、主項 $D_wa$ の順序数主項条件は $G_wa$ しか押さえず、$w>0$ のとき $D_0a\in OT_{\textrm{B}\omega}$ は手元に無いからである。埋めるのに要ったのは、この一般化と 4 の相互再帰（$G_0$ の一段展開 3 を含めて 50 行ほど）で、新しい数学的な着想は要らない。

- **[Y]** 証明中の $T_{\textrm{PS}}$ は $T_{\textrm{B}}$ の誤記

  原文は $t=0$ の場合、単項の場合、複項の場合、まとめの行、最終行の 5 箇所で $t\in T_{\textrm{PS}}$、$OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{PS}}$ と書くが、$t$ は Buchholz の項であって、ペア数列全体 $T_{\textrm{PS}}$ の元ではない。ここで示しているのは「$t$ が字母 $D_\omega$ を含まない」であるから、いずれも $T_{\textrm{B}}$ が正しい。$T_{\textrm{PS}}$ をそのまま形式化すると、示すべき $t\in OT_{\textrm{B}}$ が得られない。直し方は $T_{\textrm{PS}}$ を $T_{\textrm{B}}$ に置き換えるだけで一意であり、証明の構造は変わらない。この形式化は $OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}$ を定義として採っている。

- **[W]** 各場合で補助主張の適用条件が示されていない

  原文は補助主張を「$t'\in OT_{\textrm{B}\omega}$ かつ $t'<_{\textrm{B}}D_\omega0$ かつ $D_0t'\in OT_{\textrm{B}\omega}$」の下で述べておきながら、適用のたびに条件を確かめていない。

  単項の場合、原文は「ある $a\in OT_{\textrm{B}\omega}$ が存在して $t<_{\textrm{B}}D_\omega0$ かつ $t=D_0a$」と書くが、次の行で使うのは $a<_{\textrm{B}}D_\omega0$ であって $t<_{\textrm{B}}D_\omega0$ ではない（$a$ の誤記と読める）。$a<_{\textrm{B}}D_\omega0$ は仮定 $t<_{\textrm{B}}D_0D_\omega0$ から出るが、その導出は書かれていない。この形式化では 6 の 1 のとおり、(1b) で主項列の比較を主項の比較へ落とし、(1c) で $w<0$（不可能）と「$w=0$ かつ $a<_{\textrm{B}}D_\omega0$」に分けて導いている。

  複項の場合、原文は $t=\underline{(}D_0a_0\underline{,}\cdots\underline{,}D_0a_{\textrm{Lng}(a)-1}\underline{)}$ と最初から全主項の添字を $0$ と書くが、その根拠は述べられていない。この形式化では 6 の 1 と 2 のとおり、頭の添字は $t<_{\textrm{B}}D_0D_\omega0$ から、以降の添字は広義降順条件 (1e) と (1d) から得ている（一般の主項列については (2b) として独立に用意した）。また原文の $a_i\leq_{\textrm{B}}a_0$ は $D_0a_i\leq_{\textrm{B}}D_0a_0$ から添字を消して得るもので、その一歩が (1d) にあたる。さらに補助主張の 3 つ目の条件 $D_0a_i\in OT_{\textrm{B}\omega}$ は原文では確かめられていない。この形式化ではこれを (5) が代わりに担い、$t$ の各主項の順序数主項条件から $G_0t$ の有界性を直接作っている。

- **[R]** 単項と複項の場合分けは要らない

  原文は $t$ についても補助主張の $t'$ についても、単項の場合と複項の場合を分けて論じる。この形式化はどちらも「空列か、先頭主項と残りの列か」の 2 分割で通しており、単項と複項の区別は現れない。先頭主項の添字と本体は上界 $D_0D_\omega0$（補助主張の中では $D_\omega0$）との比較から、以降の主項は広義降順条件から、という同じ扱いが列の長さによらず効くためである。したがって複項の場合のために原文が置く一歩 $D_{u_0}a_0<_{\textrm{B}}t'$ も使わない。原文の $t=0$ の場合は空列の場合として残っている。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| 項 $\underline{(}p_0\underline{,}\cdots\underline{,}p_{k-1}\underline{)}$、主項 $D_vb$ | `PSS.BT`、`PSS.BP` | `lean/Buchholz-1986/Buchholz-1986-2.1.lean` |
| $0$ | `PSS.BZero` | 同上 |
| $D_va$ | `PSS.Dprin` | 同上 |
| $<_{\textrm{B}}$ | `PSS.lessBT`、`PSS.lessBP`、`PSS.lessBPList` | 同上 |
| $\leq_{\textrm{B}}$ | `PSS.leBT` | 同上 |
| $G_u$ | `PSS.gatherBT`、`PSS.gatherBP`、`PSS.gatherBPList` | `lean/Buchholz-1986/Buchholz-1986-2.2.lean` |
| 字母 $D_\omega$ を含まないこと | `PSS.dfree_BT`、`PSS.dfree_BP`、`PSS.dfree_BPList` | 同上 |
| $T_{\textrm{B}}$ | `PSS.T_B` | 同上 |
| 主項列が広義降順であること | `PSS.descP` | 同上 |
| $OT_{\textrm{B}\omega}$ | `PSS.OT`（判定は `PSS.isOT_BT`、`PSS.isOT_BP`、`PSS.isOT_BPList`） | 同上 |
| $OT_{\textrm{B}}$ | `PSS.OT_B` | 同上 |
| $\textrm{dom}$ | `PSS.domTag`、`PSS.domTagBP`、`PSS.domTagList`、`PSS.domB` | `lean/Buchholz-1986/Buchholz-1986-3.2.lean` |
| $\varnothing$、$\{0\}$、$\mathbb{N}$、$T_u$ | `PSS.BDom`、`PSS.BDom.toSet` | 同上 |
| $<_{\textrm{B}}$ の推移性 | `PSS.lessBT_linear_trans` | `lean/Buchholz-1986/Buchholz-1986-2.1-order.lean` |
| $\leq_{\textrm{B}}$ の推移性 | `Bijectivity.leBT_trans` | `lean/Bijectivity/18-trans-preserves-order.lean` |
| $\leq_{\textrm{B}}$ と $<_{\textrm{B}}$ の合成 | `Bijectivity.leBT_lessBT_trans` | 同上 |
| $\leq_{\textrm{B}}$ の反射性 | `Bijectivity.leBT_refl` | 同上 |
| $D_0D_\omega0$ | `Bijectivity.DzeroDomegaZero` | `lean/Bijectivity/Cited.lean` |
| $D_\omega0$ | `Bijectivity.DomegaZero` | `lean/Bijectivity/19-alphabet-below-bound.lean` |
| 主項の添字 $v$、本体 $b$ | `Bijectivity.dbIndex`、`Bijectivity.dbBody` | 同上 |
| (1a) $0$ 未満の項は無い | `Bijectivity.lessBT_BZero`、`Bijectivity.lessBPList_nil_right'` | 同上 |
| (1b) 単一主項との比較 | `Bijectivity.lessBPList_single_cons` | 同上 |
| (1c) 主項比較の分解 | `Bijectivity.lessBP_split` | 同上 |
| (1d) 主項の広義比較の分解 | `Bijectivity.prin_leBT_split` | 同上 |
| (1e) 広義降順列の頭が上界 | `Bijectivity.descP_head_bound` | 同上 |
| (2a) 添字が $\omega$ でないこと | `Bijectivity.index_ne_top_of_lt` | 同上 |
| (2b) 添字が $0$ であること | `Bijectivity.index_zero_of_lt_bound` | 同上 |
| 3. $G_0$ の一段展開 | `Bijectivity.gatherBP_zero` | 同上 |
| (4a)(4b) 補助主張 | `Bijectivity.dfree_of_bounded_BT`、`Bijectivity.dfree_of_bounded_BPList` | 同上 |
| (5) $G_0$ の有界性 | `Bijectivity.gather_bound_all_zero` | 同上 |
| 6. 本補題 | `Bijectivity.OT_iff_OT_B_of_lt` | 同上 |
| 7. 列の $\textrm{dom}$ は末尾で決まる | `Bijectivity.domTagList_eq_last` | 同上 |
| 7. $\textrm{dom}$ が $\varnothing$ でないこと | `Bijectivity.domTagBP_ne_empty`、`Bijectivity.domTag_ne_empty`、`Bijectivity.domTagList_ne_empty` | 同上 |
| 7. $\textrm{dom}(t)=\varnothing\iff t=0$ | `Bijectivity.domTag_empty_iff` | 同上 |
| 7. $\textrm{dom}$ の二分類 | `Bijectivity.domTag_cases_of_bound` | 同上 |

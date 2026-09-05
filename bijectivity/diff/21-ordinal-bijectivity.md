[← back](README.md)

# 21: 命題 (変換写像の順序数への全単射性)

## 原文

### 命題

原文に命題番号は無く、見出しは「命題 (変換写像の順序数への全単射性)」である。

$o\circ\textrm{Trans}$ は $CT_{\textrm{PS}}\to\psi_0\psi_\omega0$ 上で全域かつ全単射である。

### 証明

証明

対応する項の上界未満の字母、対応する項の上界(1)と(2)及び[1]の $\textrm{Trans}$ が標準形を保つことより $\lbrace\textrm{Trans}(M)\mid M\in CT_{\textrm{PS}}\rbrace$ は $\lbrace t\mid t\in OT_{\textrm{B}\omega}\land t\lt_{\textrm{B}}D_0D_\omega0\rbrace$ の $\lt_{\textrm{B}}$ に対して非有界な部分集合である。

[4]のLemma 2.2(c)より $\lbrace o(\textrm{Trans}(M))\mid M\in CT_{\textrm{PS}}\rbrace$ は $o(D_0D_\omega0)=\psi_0\psi_\omega0$ の非有界な部分集合である。

[4]のLemma 2.3(b)及び[5]のLemma 1.6より任意の $t\in\lbrace t\mid t\in OT_{\textrm{B}\omega}\land t\lt_{\textrm{B}}D_10\rbrace$ に対して $\textrm{dom}(t)=\textrm{cof}(o(t))$ である。

後続な項の基本列及び[1]の標準形の簡約性より任意の $M\in CT_{\textrm{PS}}$ に対して、$\textrm{cof}(o(\textrm{Trans}(M)))=1$ ならば $o(\textrm{Trans}(M))=o(\textrm{Trans}(M[1])+D_00)=o(\textrm{Trans}(M[1]))+o(D_00)=o(\textrm{Trans}(M[1]))+1$ である。

基本列の収束性より任意の $M\in CT_{\textrm{PS}}$ に対して、$\textrm{cof}(o(\textrm{Trans}(M)))=\omega$ ならば $o(\textrm{Trans}(M))=\sup_{n\in\mathbb{N}_+}o(\textrm{Trans}(M[n]))$ である。

[3]の命題11より $o\circ\textrm{Trans}$ は $CT_{\textrm{PS}}\to\psi_0\psi_\omega0$ 上で全射である。

$\textrm{Trans}$ が順序を保つこと、[4]のLemma 2.1及びLemma 2.2(c)より $o\circ\textrm{Trans}$ は $CT_{\textrm{PS}}\to\psi_0\psi_\omega0$ 上で単射である。

よって $o\circ\textrm{Trans}$ は $CT_{\textrm{PS}}\to\psi_0\psi_\omega0$ 上で全域かつ全単射である。□

## Lean

### Lean での命題

主定理は次の 3 つを束ねたもので、原文の「$CT_{\textrm{PS}}\to\psi_0\psi_\omega0$ 上で全域かつ全単射」に当たる。終域の順序数 $\psi_0\psi_\omega0$ は、順序数をそれ未満の順序数全体と同一視して $\lbrace\alpha\mid\alpha\lt\psi_0\psi_\omega0\rbrace$ と書く。

- 全域性: 任意の $M\in CT_{\textrm{PS}}$ に対して $o(\textrm{Trans}(M))\lt\psi_0\psi_\omega0$。
- 単射性: 任意の $M,N\in CT_{\textrm{PS}}$ に対して $o(\textrm{Trans}(M))=o(\textrm{Trans}(N))$ ならば $M=N$。
- 全射性: 任意の $\alpha\lt\psi_0\psi_\omega0$ に対してある $M\in CT_{\textrm{PS}}$ が存在して $o(\textrm{Trans}(M))=\alpha$。

同じファイルに、原文の系（ペア数列の解析）と定理（変換写像の全単射性）で使う次の命題も置かれている。

- $\textrm{Trans}$ 自身の単射性: 任意の $M,N\in CT_{\textrm{PS}}$ に対して $\textrm{Trans}(M)=\textrm{Trans}(N)$ ならば $M=N$。

ここで $o$ と $\psi_0\psi_\omega0$ は [4] からの引用（公理）ではなく、次のように構成された対象である。

- $t=D_0D_\omega0$ のとき $o(t)=\psi_0\psi_\omega0$
- $t\in OT_{\textrm{B}}$ のとき $o(t)=\textrm{otp}\lbrace u\in OT_{\textrm{B}}\mid u\lt_{\textrm{B}}t\rbrace$（$\textrm{otp}$ は順序型）
- それ以外のとき $o(t)=0$

$$\psi_0\psi_\omega0=\sup\lbrace o(t)+1\mid t\in OT_{\textrm{B}},\ t\lt_{\textrm{B}}D_0D_\omega0\rbrace$$

$OT_{\textrm{B}\omega}$（字母 $D_\omega$ を許す [4] の $OT$）に当たる集合も存在し、$OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}$ である。$D_0D_\omega0$ 自身は $D_\omega$ を含むので $OT_{\textrm{B}}$ の外にあり、そこだけ $o$ の値を定義で $\psi_0\psi_\omega0$ と与えている。

### Lean での証明

#### 0. 評価写像 $o$ の構成と、そこから取り出す性質

原文が [4] の Lemma 2.1 / 2.2(c) と加法標準形として引く事実は、この構成のもとではすべて定理になる。以下 $\textrm{otp}$ は整列順序の順序型を表す。

**$(OT_{\textrm{B}},\lt_{\textrm{B}})$ が整列順序であること。** 整礎性は別ファイルで仮定ゼロで証明された $OT_{\textrm{B}}$ 上の $\lt_{\textrm{B}}$ の整礎性をそのまま部分型へ引き戻したもの、三分律と推移律は $\lt_{\textrm{B}}$ の線形性（[4] Lemma 2.1 に当たる）から取る。なお $OT_{\textrm{B}}$ の仮定は落とせない。$x_0=D_10$、$x_{n+1}=D_0x_n$ と置いた列は $\lt_{\textrm{B}}$ について狭義降下するので、$OT_{\textrm{B}}$ を外して $o$ の単調性を述べると順序数の無限降下列ができてしまう（この列は $n\geq2$ で順序数項から外れることも機械検証されている）。

**$o$ の狭義単調性（[4] Lemma 2.2(c) の前半）。** $s,t\in OT_{\textrm{B}}$、$s\lt_{\textrm{B}}t$ ならば $o(s)\lt o(t)$。$o$ は $OT_{\textrm{B}}$ 上では順序型への順序同型なので、そのまま従う。

**$o$ の初期切片への全射性（[4] Lemma 2.2(c) の後半）。** $t_0\in OT_{\textrm{B}}$、$\alpha\lt o(t_0)$ ならば、ある $t\in OT_{\textrm{B}}$ が存在して $t\lt_{\textrm{B}}t_0$ かつ $o(t)=\alpha$。$\alpha\lt o(t_0)\lt\textrm{otp}(OT_{\textrm{B}})$ から順序型の全射性で $t$ を取り、$o(t)=\alpha\lt o(t_0)$ と単調性の逆向きで $t\lt_{\textrm{B}}t_0$ を得る。

**$\psi_0\psi_\omega0$ 未満は上界未満の項の値であること。** $\alpha\lt\psi_0\psi_\omega0$ とすると、上限の定義よりある $u\in OT_{\textrm{B}}$、$u\lt_{\textrm{B}}D_0D_\omega0$ で $\alpha\lt o(u)+1$、すなわち $\alpha\leq o(u)$。$\alpha\lt o(u)$ なら上の初期切片への全射性で $t\lt_{\textrm{B}}u$、$o(t)=\alpha$ を取り、$\lt_{\textrm{B}}$ の推移律で $t\lt_{\textrm{B}}D_0D_\omega0$。$\alpha=o(u)$ なら $u$ をそのまま使う。

**$o(0)=0$。** $0\lt o(0)$ とすると初期切片への全射性で $t\lt_{\textrm{B}}0$ なる $t$ が取れるが、$0$ 未満の項は無い。

**$o(D_00)=1$。** $0\lt_{\textrm{B}}D_00$ と単調性から $0=o(0)\lt o(D_00)$。$1\lt o(D_00)$ とすると初期切片への全射性で $t\lt_{\textrm{B}}D_00$、$o(t)=1$ が取れるが、$D_00$ 未満の項は $0$ だけ（主項列の形で場合分けして確かめる）で $o(0)=0\neq1$。

**$o(a+_{\textrm{B}}D_00)=o(a)+1$（原文が [4] の加法標準形から取る一歩）。** $a$、$a+_{\textrm{B}}D_00\in OT_{\textrm{B}}$ とする。主項列の末尾に $D_00$ を継ぎ足す操作なので $a\lt_{\textrm{B}}a+_{\textrm{B}}D_00$、よって単調性から $o(a)\lt o(a+_{\textrm{B}}D_00)$、すなわち $o(a)+1\leq o(a+_{\textrm{B}}D_00)$。逆向きは背理法で、$o(a)+1\lt o(a+_{\textrm{B}}D_00)$ とすると初期切片への全射性で $u\lt_{\textrm{B}}a+_{\textrm{B}}D_00$、$o(u)=o(a)+1\gt o(a)$ が取れ、三分律と単調性から $a\lt_{\textrm{B}}u$。ところが主項列についての帰納法で「$a\lt_{\textrm{B}}u\lt_{\textrm{B}}a+_{\textrm{B}}D_00$ なる $u$ は無い」が示せるので矛盾する。

#### 1. 順序数項であること

$M\in CT_{\textrm{PS}}$ は定義上 $M\in ST_{\textrm{PS}}$ を含むので、[1] の「$\textrm{Trans}$ が標準形を保つこと」から $\textrm{Trans}(M)\in OT_{\textrm{B}}$、したがって $\textrm{Trans}(M)\in OT_{\textrm{B}\omega}$。また $D_0D_\omega0\in OT_{\textrm{B}\omega}$ と $D_00\in OT_{\textrm{B}}$ は有限の判定式の計算で決まる。

#### 2. 全域性

$M\in CT_{\textrm{PS}}$ とする。対応する項の上界(1) より $\textrm{Trans}(M)\lt_{\textrm{B}}D_0D_\omega0$。$\psi_0\psi_\omega0$ は $t\lt_{\textrm{B}}D_0D_\omega0$ なる $t\in OT_{\textrm{B}}$ にわたる $o(t)+1$ の上限だから $o(\textrm{Trans}(M))+1\leq\psi_0\psi_\omega0$、すなわち $o(\textrm{Trans}(M))\lt\psi_0\psi_\omega0$。

#### 3. 単射性

$M,N\in CT_{\textrm{PS}}$、$o(\textrm{Trans}(M))=o(\textrm{Trans}(N))$ とする。$\lt_{\textrm{PS}}$ の三分律から $M\lt_{\textrm{PS}}N$、$M=N$、$N\lt_{\textrm{PS}}M$ のいずれか。

$M\lt_{\textrm{PS}}N$ の場合、$\textrm{Trans}$ が順序を保つことより $\textrm{Trans}(M)\lt_{\textrm{B}}\textrm{Trans}(N)$、$o$ の狭義単調性より $o(\textrm{Trans}(M))\lt o(\textrm{Trans}(N))$。仮定で右辺を左辺に書き換えると $o(\textrm{Trans}(M))\lt o(\textrm{Trans}(M))$ となり、順序数の非反射性に反する。$N\lt_{\textrm{PS}}M$ の場合も同様。よって $M=N$。

$\textrm{Trans}$ 自身の単射性も同じ形で、順序数に降ろさず項のまま行う。$\textrm{Trans}(M)=\textrm{Trans}(N)$ のとき $M\lt_{\textrm{PS}}N$ とすると $\textrm{Trans}(M)\lt_{\textrm{B}}\textrm{Trans}(N)=\textrm{Trans}(M)$ となり、$\lt_{\textrm{B}}$ の非反射性に反する。$N\lt_{\textrm{PS}}M$ も同様なので $M=N$。

#### 4. 非有界性

原文の証明の 1 行目と 2 行目（項の集合が非有界、ゆえに像も非有界）に当たる部分を、次の 1 つの主張にまとめてある。

任意の $\alpha\lt\psi_0\psi_\omega0$ に対してある $M\in CT_{\textrm{PS}}$ が存在して $\alpha\lt o(\textrm{Trans}(M))$。

証明は次の通り。$\alpha\lt\psi_0\psi_\omega0$ とすると 0. の「$\psi_0\psi_\omega0$ 未満は上界未満の項の値」から $t\in OT_{\textrm{B}}$、$t\lt_{\textrm{B}}D_0D_\omega0$、$o(t)=\alpha$ が取れる。$OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}$ の第 2 成分より $t\in T_{\textrm{B}}$ なので、対応する項の上界(2) を $t$ に適用して $M\in CT_{\textrm{PS}}$ と $t\lt_{\textrm{B}}\textrm{Trans}(M)$ を得る。$o$ の狭義単調性より $\alpha=o(t)\lt o(\textrm{Trans}(M))$。

#### 5. $CT_{\textrm{PS}}$ が基本列で閉じていること

$M\in CT_{\textrm{PS}}$、$n\geq1$ とする。可算な標準形の起源より $v\in\mathbb{N}$ が存在して $M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$。$\leq_{\textrm{PS}[]}$ の定義に添字列 $a=(n)$ を取って得られる $M[n]\leq_{\textrm{PS}[]}M$（$n\geq1$）と、$\leq_{\textrm{PS}[]}$ の推移性から $M[n]\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$、再び可算な標準形の起源（逆向き）より $M[n]\in CT_{\textrm{PS}}$。

#### 6. 全射性

$\alpha\lt\psi_0\psi_\omega0$ とする。

$$T=\lbrace\beta\mid\alpha\leq\beta\ \land\ \exists M\in CT_{\textrm{PS}},\ o(\textrm{Trans}(M))=\beta\rbrace$$

と置く。4. の非有界性で得た $M$ について $\alpha\lt o(\textrm{Trans}(M))$ なので $o(\textrm{Trans}(M))\in T$、すなわち $T\neq\varnothing$。順序数の $\lt$ の整礎性から $T$ の極小元 $\beta$ を取り、$\beta=o(\textrm{Trans}(M))$ となる $M\in CT_{\textrm{PS}}$ を固定する。$\beta$ の極小性は「$T$ の元は $\beta$ 未満にならない」の形で使う。

$\alpha\leq\beta$ なので $\alpha=\beta$ か $\alpha\lt\beta$。$\alpha=\beta$ なら $M$ が求めるものである。以下 $\alpha\lt\beta$ として矛盾を導く。

まず $\textrm{Trans}(M)\neq0$ である。もし $\textrm{Trans}(M)=0$ なら $\beta=o(0)=0$ となり $\alpha\lt0$ で矛盾する。

$\textrm{Trans}(M)\in OT_{\textrm{B}\omega}$、$\textrm{Trans}(M)\lt_{\textrm{B}}D_0D_\omega0$（対応する項の上界(1)）、$\textrm{Trans}(M)\neq0$ の 3 つを、対応する項の上界未満の字母の系である「上界 $D_0D_\omega0$ 未満の非零な順序数項の $\textrm{dom}$ は $1$ か $\omega$ のいずれか」に渡すと、$\textrm{dom}(\textrm{Trans}(M))=1$ または $\textrm{dom}(\textrm{Trans}(M))=\omega$ を得る。

**(a) $\textrm{dom}(\textrm{Trans}(M))=1$ の場合。** [1] の標準形の簡約性より $M\in RT_{\textrm{PS}}$。後続な項の基本列を $n=1$ に対して使うと

- 第 1 の枝: $(\textrm{Trans}(M),\textrm{Trans}(M[1]))=(D_00,0)$
- 第 2 の枝: $\textrm{Trans}(M[1])+_{\textrm{B}}D_00=\textrm{Trans}(M)$

である。5. より $M[1]\in CT_{\textrm{PS}}$ なので、$o(\textrm{Trans}(M[1]))$ が $T$ に属しかつ $\beta$ 未満であることを示せば極小性に反する。

$\alpha\leq o(\textrm{Trans}(M[1]))$: 第 1 の場合は $\textrm{Trans}(M[1])=0$ かつ $\beta=o(D_00)=1$ で、$\alpha\lt1$ から $\alpha=0=o(0)=o(\textrm{Trans}(M[1]))$。第 2 の場合は背理法で、$o(\textrm{Trans}(M[1]))\lt\alpha$ とすると、0. の $o(a+_{\textrm{B}}D_00)=o(a)+1$ を $a=\textrm{Trans}(M[1])$ に対して使って $\beta=o(\textrm{Trans}(M[1]))+1\leq\alpha$ となり、$\alpha\lt\beta$ に反する（$a\in OT_{\textrm{B}}$ は $M[1]\in CT_{\textrm{PS}}$ から、$a+_{\textrm{B}}D_00\in OT_{\textrm{B}}$ は上の等式で $\textrm{Trans}(M)$ に書き換えて得る）。

$o(\textrm{Trans}(M[1]))\lt\beta$: 第 1 の場合は $0\lt1$。第 2 の場合は $\beta=o(\textrm{Trans}(M[1]))+1$ より従う。

**(b) $\textrm{dom}(\textrm{Trans}(M))=\omega$ の場合。** [1] の標準形の簡約性で $M\in RT_{\textrm{PS}}$ とし、$\textrm{dom}(\textrm{Trans}(M))=\omega$ から $\textrm{Lng}(M)\gt1$ を得る（$\textrm{Lng}(M)=1$ の簡約形では $\textrm{dom}$ が $\omega$ にならない）。基本列の収束性より

$$\sup_{n\in\mathbb{N}_+}o(\textrm{Trans}(M[n]))=o(\textrm{Trans}(M))=\beta$$

である。ここで、すべての $n\in\mathbb{N}_+$ について $o(\textrm{Trans}(M[n]))\leq\alpha$ と仮定すると上限も $\alpha$ 以下、すなわち $\beta\leq\alpha$ となり $\alpha\lt\beta$ に反する。よってある $n\in\mathbb{N}_+$ が存在して $\alpha\lt o(\textrm{Trans}(M[n]))$。

この $n$ について、5. より $M[n]\in CT_{\textrm{PS}}$ であり、[1] の基本列の降下性（$M\in ST_{\textrm{PS}}$、$n\geq1$、$\textrm{Lng}(M)\gt1$）より $\textrm{Trans}(M[n])\lt_{\textrm{B}}\textrm{Trans}(M)$、$o$ の狭義単調性より $o(\textrm{Trans}(M[n]))\lt\beta$。したがって $o(\textrm{Trans}(M[n]))$ は $T$ に属し $\beta$ 未満で、極小性に反する。

以上より $\alpha=\beta=o(\textrm{Trans}(M))$ であり、全射性が従う。

#### 7. 結論

2.、3.、6. を束ねて $o\circ\textrm{Trans}$ は $\lbrace M\mid M\in CT_{\textrm{PS}}\rbrace$ から $\lbrace\alpha\mid\alpha\lt\psi_0\psi_\omega0\rbrace$ への全単射である。□

この主定理は、命題外延性・選択公理・商型の健全性という証明系の標準公理以外の公理に依存しない（依存公理の一覧を出す監査が別ファイルにあり、機械確認されている）。原文が [3][4][5] から引く事実はすべてこのリポジトリ内で証明済みだからである。

## 原文通りに書けなかった理由

- **[🌳U]** $o$ と $\psi_0\psi_\omega0$ を [4] からの引用ではなく順序型として構成している

  原文は「表記」節で $\psi_ua$、$D_ua$、$G_ua$、$o$ を [4] から引くと明記し、この命題の証明でも $o(D_0D_\omega0)=\psi_0\psi_\omega0$ を [4] の事実として使う。この形式化は $o$ を公理化せず、整列順序 $(OT_{\textrm{B}},\lt_{\textrm{B}})$ の順序型への順序同型として定め、$\psi_0\psi_\omega0$ を $\lbrace t\in OT_{\textrm{B}}\mid t\lt_{\textrm{B}}D_0D_\omega0\rbrace$ の順序型として定めている。おかげで [4] の Lemma 2.1 / 2.2(c) と加法標準形は定理になり、この命題は追加の公理を一切使わずに閉じる。代償は 2 つある。第 1 に、こうして作った $\psi_0\psi_\omega0$ が Buchholz の $\psi_0(\psi_\omega(0))$ と一致することは形式化されていない。この命題の中では $o(D_0D_\omega0)=\psi_0\psi_\omega0$ は定義であって定理ではない。第 2 に、$o$ は $OT_{\textrm{B}}$ と $D_0D_\omega0$ の外では $0$ という無意味な値を返す全域関数として定義されているので、$o$ を使うすべての一歩に $OT_{\textrm{B}}$ 所属の仮定が付く。この仮定は落とせない。$x_0=D_10$、$x_{n+1}=D_0x_n$ が $\lt_{\textrm{B}}$ について狭義降下することが機械検証されており、$OT_{\textrm{B}}$ を外すと $o$ の単調性から順序数の無限降下列が出てしまう。

- **[W]** 単射性には $\lt_{\textrm{PS}}$ の三分律が要るが、原文はそれを挙げていない

  原文は単射性の材料として「$\textrm{Trans}$ が順序を保つこと、[4]のLemma 2.1及びLemma 2.2(c)」の 3 つを挙げる。しかし $\textrm{Trans}$ が順序を保つことから単射性へ渡るには、$M\neq N$ から $M\lt_{\textrm{PS}}N$ か $N\lt_{\textrm{PS}}M$ かを取り出す一歩、すなわち始域側 $\lt_{\textrm{PS}}$ の三分律が要る。原文はこれを書いていない（系（順序の線形性）として別に用意されてはいるが、この証明では引かれていない）。この形式化は系（辞書式的順序の線形性）に当たる三分律を明示的に適用して埋めている。逆に、原文が挙げる [4] Lemma 2.1 は $o\circ\textrm{Trans}$ の単射性には現れない。順序数側の $\lt$ の非反射性で矛盾が出るためである（$\lt_{\textrm{B}}$ の非反射性を使うのは、順序数に降ろさない $\textrm{Trans}$ 自身の単射性のほうだけである）。

- **[W]** $CT_{\textrm{PS}}$ が基本列で閉じていることを補っている

  原文は $M\in CT_{\textrm{PS}}$ に対して $o(\textrm{Trans}(M[1]))$ や $o(\textrm{Trans}(M[n]))$ を像の元として扱うが、$M[n]\in CT_{\textrm{PS}}$ であることはどこにも書かれていない。この形式化では、可算な標準形の起源から $M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$ を取り、$M[n]\leq_{\textrm{PS}[]}M$ と $\leq_{\textrm{PS}[]}$ の推移性を挟んで $M[n]\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$ とし、同じ同値の逆向きで $M[n]\in CT_{\textrm{PS}}$ を出す補題を立てている。

- **[S]** [3] の命題 11 を引かず、順序数の整礎性による最小反例の議論に置き換えている

  原文は非有界性・後続の場合・極限の場合の 3 つを用意したうえで、それらを全射性へまとめる一歩を [3] の命題 11 に委ねる。この形式化は同じ 3 つを用意するところまでは原文どおりで、最後のまとめを外部から引かずにその場で行う。すなわち $\alpha$ 以上の像の値全体 $T$ の極小元 $\beta=o(\textrm{Trans}(M))$ を順序数の整礎性で取り、$\alpha\lt\beta$ を仮定して、$\textrm{dom}(\textrm{Trans}(M))$ が $1$ なら $o(\textrm{Trans}(M[1]))$ が、$\omega$ なら適当な $o(\textrm{Trans}(M[n]))$ が $T$ に属して $\beta$ より小さいことを示し、極小性に矛盾させる。証明される主張は原文と同一で、下流の系（ペア数列の解析）と定理（変換写像の全単射性）も変わらない。この置き換えのぶんだけ Lean 側の証明が原文より長い。

- **[W]** 場合分けの前に $\textrm{Trans}(M)\neq0$ を除く必要があるが、原文はそれを書いていない

  原文は $\textrm{cof}(o(\textrm{Trans}(M)))$ が $1$ か $\omega$ かで場合分けするが、$o(\textrm{Trans}(M))=0$ のときはどちらでもないので、この場合分けが尽くされていることには $\textrm{Trans}(M)\neq0$ が要る。この形式化では、$\textrm{Trans}(M)=0$ なら $\beta=o(0)=0$ となって $\alpha\lt\beta$ に反する、という一歩を明示している。

- **[R]** 原文の「$\textrm{dom}(t)=\textrm{cof}(o(t))$」は使っていない

  原文は [4] の Lemma 2.3(b) 及び [5] の Lemma 1.6 で、$t\lt_{\textrm{B}}D_10$ の範囲で構文的な $\textrm{dom}(t)$ を順序数の共終数 $\textrm{cof}(o(t))$ に翻訳し、そのうえで $\textrm{cof}=1$ と $\textrm{cof}=\omega$ に分ける。この形式化は共終数を一度も使わない。場合分けは構文的な $\textrm{dom}$ のまま行い、その尽くされていることは、対応する項の上界未満の字母から出る系「上界 $D_0D_\omega0$ 未満の非零な順序数項の $\textrm{dom}$ は $1$ か $\omega$」で与える。この系は主項列の末尾の主項の崩壊記号の水準が $0$ であること（上界未満なので）から直接出るので、$D_10$ という別の上界も要らない。原文が対応する項の上界未満の字母を引く先は非有界性の行だが、この形式化で同じ補題が効くのはこの場合分けのほうである（非有界性は対応する項の上界(2) と $o$ の初期切片への全射性だけで閉じる）。

- **[W]** 後続の場合の退化した枝 $(\textrm{Trans}(M),\textrm{Trans}(M[1]))=(D_00,0)$ の扱いが原文には無い

  後続な項の基本列は原文でも選言の形をしており、第 1 の枝は $(\textrm{Trans}(M),\textrm{Trans}(M[1]))=(D_00,0)$ である。しかしこの命題の証明で原文が書くのは第 2 の枝に当たる等式の連鎖 $o(\textrm{Trans}(M))=o(\textrm{Trans}(M[1])+D_00)=\cdots$ だけで、第 1 の枝がその連鎖を満たすこと（$0+D_00=D_00$）には触れない。この形式化では選言を消費するので両方の枝を書く必要があり、第 1 の枝は $\beta=o(D_00)=1$ と $o(\textrm{Trans}(M[1]))=o(0)=0$ から別に処理している。

- **[S]** $o$ の加法性の代わりに「$+_{\textrm{B}}D_00$ は直後者を取る操作である」という構文的な補題を使っている

  原文は $o(\textrm{Trans}(M[1])+D_00)=o(\textrm{Trans}(M[1]))+o(D_00)$ と、$o$ が加法標準形について加法的であることを [4] から引き、続けて $o(D_00)=1$ を使う。この形式化は加法性を一般には証明しておらず、必要な特殊形 $o(a+_{\textrm{B}}D_00)=o(a)+1$ だけを、$o$ の単調性と初期切片への全射性、および「主項列 $a$ と $a$ の末尾に $D_00$ を継いだ列との間に項は無い」という構文的な補題から直接示す。得られる等式は原文と同じで、下流も変わらない。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $M\in CT_{\textrm{PS}}$ | `CTPS M` | `lean/Bijectivity/Defs.lean` |
| $M\lt_{\textrm{PS}}N$ | `ltPS M N` | 同上 |
| $M\leq_{\textrm{PS}[]}N$ | `leExpPS M N` | 同上 |
| $M[n]$ | `PSS.oper M n` | `lean/PSS/Defs.lean` |
| $\textrm{Lng}(M)$ | `PSS.Lng M` | 同上 |
| $M\in ST_{\textrm{PS}}$ | `PSS.STPS M` | `lean/PSS/Standard.lean` |
| $M\in RT_{\textrm{PS}}$ | `PSS.RTPS M` | `lean/PSS/Red.lean` |
| $((j,j))_{j=0}^{v}$ | `PSS.diagSeq 0 v` | 同上 |
| $\textrm{Trans}$ | `PSS.Trans` | `lean/PSS/Trans.lean` |
| $t\in OT_{\textrm{B}\omega}$ | `t ∈ OT` | `lean/Buchholz-1986/Buchholz-1986-2.2.lean` |
| $t\in OT_{\textrm{B}}$ | `t ∈ OT_B` | 同上 |
| $t\in T_{\textrm{B}}$ | `t ∈ T_B` | 同上 |
| $\textrm{dom}(t)$ | `PSS.domTag t` | `lean/Buchholz-1986/Buchholz-1986-3.2.lean` |
| $a+_{\textrm{B}}b$ | `PSS.addBT a b` | 同上 |
| $s\lt_{\textrm{B}}t$ | `PSS.lessBT s t` | `lean/Buchholz-1986/Buchholz-1986-2.1.lean` |
| $D_0D_\omega0$ | `DzeroDomegaZero` | `lean/Bijectivity/Cited.lean` |
| $D_00$ | `DzeroZero` | `lean/Bijectivity/15-successor-fseq.lean` |
| $o$ | `o` | `lean/Bijectivity/Cited.lean` |
| $\psi_0\psi_\omega0$ | `psi0psiOmega0` | 同上 |
| $\textrm{dom}(t)=1$、$\textrm{dom}(t)=\omega$ | `domIsOne`、`domIsOmega` | 同上 |
| $OT_{\textrm{B}}$ 上の $\lt_{\textrm{B}}$ の整礎性 | `OT_B_wellFounded` | `lean/OTB-well-founded-syntactic/OTB-well-founded-syntactic-main.lean` |
| $\lt_{\textrm{B}}$ の三分律・推移律・非反射性（[4] Lemma 2.1） | `lessBT_linear_trichotomy`、`lessBT_linear_trans`、`lessBT_linear_irrefl` | `lean/Buchholz-1986/Buchholz-1986-2.1-order.lean` |
| $(OT_{\textrm{B}},\lt_{\textrm{B}})$ が整列順序であること | `instance : IsWellOrder OTBsub rOTB`（無名インスタンス、`OTBsub`／`rOTB` と組） | `lean/Bijectivity/Cited.lean` |
| $\textrm{otp}\lbrace u\in OT_{\textrm{B}}\mid u\lt_{\textrm{B}}t\rbrace$ | `tpOTB` | 同上 |
| $x_0=D_10$、$x_{n+1}=D_0x_n$ とその狭義降下性 | `descChain`、`descChain_lt`、`descChain_not_OT` | 同上 |
| $o$ の狭義単調性（[4] Lemma 2.2(c)） | `o_lt_of_lessBT` | 同上 |
| $t\lt_{\textrm{B}}D_0D_\omega0\Rightarrow o(t)\lt\psi_0\psi_\omega0$ | `o_lt_psi` | 同上 |
| $o$ の初期切片への全射性（[4] Lemma 2.2(c)） | `o_surj_below` | 同上 |
| $\psi_0\psi_\omega0$ 未満は上界未満の項の値 | `o_surj_below_psi` | 同上 |
| $o(0)=0$ | `o_BZero` | 同上 |
| $o(D_00)=1$ | `o_DzeroZero`、`o_DzeroZero'` | 同上、`lean/Bijectivity/21-ordinal-bijectivity.lean` |
| $D_00$ 未満の項は $0$ だけ | `eq_BZero_of_lessBT_DzeroZero` | `lean/Bijectivity/Cited.lean` |
| $a\lt_{\textrm{B}}a+_{\textrm{B}}D_00$ | `lessBT_addBT_D00_self` | 同上 |
| $a$ と $a+_{\textrm{B}}D_00$ の間に項が無いこと | `no_between_snoc_D00` | 同上 |
| $o(a+_{\textrm{B}}D_00)=o(a)+1$ | `o_addBT_DzeroZero` | 同上 |
| $D_0D_\omega0\in OT_{\textrm{B}\omega}$ | `OT_DzeroDomegaZero` | `lean/Bijectivity/21-ordinal-bijectivity.lean` |
| $D_00\in OT_{\textrm{B}}$ | `OTB_DzeroZero`、`OT_DzeroZero` | 同上 |
| $M\in CT_{\textrm{PS}}\Rightarrow\textrm{Trans}(M)\in OT_{\textrm{B}}$ | `OTB_Trans_of_CTPS`、`OT_Trans_of_CTPS` | 同上 |
| [1] の $\textrm{Trans}$ が標準形を保つこと | `Trans_STPS_OT_B` | `lean/8/8.7-termination.lean` |
| [1] の基本列の降下性 | `Trans_fseq_descend` | 同上 |
| [1] の標準形の簡約性 | `STPS_RTPS` | `lean/6/6.7-standard-reduced.lean` |
| 命題（対応する項の上界）(1) | `trans_lt_bound` | `lean/Bijectivity/20-term-upper-bound.lean` |
| 命題（対応する項の上界）(2) | `exists_trans_gt` | 同上 |
| 命題（$\textrm{Trans}$ が順序を保つこと） | `trans_lessBT_of_ltPS` | `lean/Bijectivity/18-trans-preserves-order.lean` |
| 補題（対応する項の上界未満の字母）（本命題では直接には未使用、下の系だけを使う） | `OT_iff_OT_B_of_lt` | `lean/Bijectivity/19-alphabet-below-bound.lean` |
| 上界未満の非零項の $\textrm{dom}$ は $1$ か $\omega$ | `domTag_cases_of_bound` | 同上 |
| 命題（後続な項の基本列） | `successor_fseq` | `lean/Bijectivity/15-successor-fseq.lean` |
| $\textrm{dom}(\textrm{Trans}(M))=\omega\Rightarrow\textrm{Lng}(M)\gt1$ | `one_lt_lng_of_domIsOmega` | 同上 |
| 命題（基本列の収束性） | `fseq_convergence` | `lean/Bijectivity/17-fseq-convergence.lean` |
| 命題（可算な標準形の起源） | `ctps_iff_leExpPS` | `lean/Bijectivity/10-countable-standard-origin.lean` |
| $M[n]\leq_{\textrm{PS}[]}M$ | `oper_leExpPS` | `lean/Bijectivity/09-standard-iff-exp.lean` |
| $\leq_{\textrm{PS}[]}$ の推移性 | `leExpPS_trans` | `lean/Bijectivity/03-exp-order-transitive.lean` |
| $\lt_{\textrm{PS}}$ の三分律 | `ltPS_trichotomy` | `lean/Bijectivity/02-lex-linear.lean` |
| $CT_{\textrm{PS}}$ が基本列で閉じていること | `ctps_oper` | `lean/Bijectivity/21-ordinal-bijectivity.lean` |
| 非有界性 | `oTrans_unbounded` | 同上 |
| 全域性 | `oTrans_mapsTo` | 同上 |
| $\textrm{Trans}$ の単射性 | `trans_injOn` | 同上 |
| $o\circ\textrm{Trans}$ の単射性 | `oTrans_injOn` | 同上 |
| 全射性 | `oTrans_surjOn` | 同上 |
| 命題（変換写像の順序数への全単射性） | `oTrans_bijOn` | 同上 |
| 順序数の $\lt$ の整礎性と極小元 | `wellFounded_lt`、`WellFounded.has_min` | なし（Lean 標準ライブラリ） |
| 公理依存の監査 | `#print axioms Bijectivity.oTrans_bijOn` | `lean/Bijectivity/Audit.lean` |

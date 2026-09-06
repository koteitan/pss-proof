[← back](README.md)

# 22: 系 (ペア数列の解析)

## 原文

### 命題

系 (ペア数列の解析)（原文の命題に番号は付いていない）

(1) 任意の $`M\in CT_{\textrm{PS}}`$ に対して、$`o\circ\textrm{Trans}`$ は同型写像 $`(\{N\mid N\in CT_{\textrm{PS}}\land N\lt_{\textrm{PS}}M\},\lt_{\textrm{PS}})\to(\{\alpha\mid\alpha\in o(\textrm{Trans}(M))\},\in)`$ である。

(2) 任意の $`M\in CT_{\textrm{PS}}`$ に対して、$`\textrm{Trans}`$ は同型写像 $`(\{N\mid N\in CT_{\textrm{PS}}\land N\lt_{\textrm{PS}}M\},\lt_{\textrm{PS}})\to(\{t\mid t\in OT_{\textrm{B}\omega}\land t\lt_{\textrm{B}}\textrm{Trans}(M)\},\lt_{\textrm{B}})`$ である。

### 証明

  (1) $`\textrm{Trans}`$ が順序を保つこと及び変換写像の順序数への全単射性より即座に従う。

  (2) 対応する項の上界(1)と(2)、対応する項の上界未満の字母、[4]のLemma 2.2(c)及びLemma 2.3(b)より $`o`$ は同型写像 $`(\{t\mid t\in OT_{\textrm{B}\omega}\land t\lt_{\textrm{B}}D_0D_\omega0\},\lt_{\textrm{B}})\to(o(D_0D_\omega0)=\psi_0\psi_\omega0,\in)`$ である。

  $`\textrm{Trans}=o^{-1}\circ o\circ\textrm{Trans}`$ であるから(1)より従う。□

## Lean

### Lean での命題

まず、この形式化での記号の対応を述べる。

- $`CT_{\textrm{PS}}`$ は原文どおり $`M\in ST_{\textrm{PS}}`$ かつ $`M`$ の先頭成分が $`(0,0)`$ であること（空列のときは先頭成分を $`(0,0)`$ と読む規約）。
- $`OT_{\textrm{B}\omega}`$ は $`D_\omega`$ を許容する Buchholz 順序数項全体、$`OT_{\textrm{B}}`$ はそのうち $`D_\omega`$ を含まないもの全体、すなわち $`OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}`$。
- $`o`$ は公理ではなく構成されている。$`(OT_{\textrm{B}},\lt_{\textrm{B}})`$ は整礎かつ三分律・推移律を満たすので整列順序であり、$`o`$ はその順序型への順序同型として定める。$`D_0D_\omega0`$ 自身は $`D_\omega`$ を含むので $`OT_{\textrm{B}}`$ の外にあり、そこだけ $`o(D_0D_\omega0)=\psi_0\psi_\omega0`$ と置く。ここで $`\psi_0\psi_\omega0=\sup\{o(t)+1\mid t\in OT_{\textrm{B}},\ t\lt_{\textrm{B}}D_0D_\omega0\}`$ である。
- 順序数の集合 $`\{\alpha\mid\alpha\in o(\textrm{Trans}(M))\}`$ は $`\{\alpha\mid\alpha\lt o(\textrm{Trans}(M))\}`$ と書く（順序数の型に $`\in`$ は無く、$`\lt`$ だけがある）。

原文の「同型写像」は、全単射性と両向きの順序保存の 2 つからなる。Lean はこの 2 つを別々の命題として述べている。

**(1)**。任意の $`M\in CT_{\textrm{PS}}`$ に対して、写像 $`N\mapsto o(\textrm{Trans}(N))`$ は

```math
\{N\mid N\in CT_{\textrm{PS}}\land N\lt_{\textrm{PS}}M\}\ \to\ \{\alpha\mid\alpha\lt o(\textrm{Trans}(M))\}
```

の全単射である。これは次の 3 本の合成として述べられている。

- 全域性: $`N\in CT_{\textrm{PS}}`$ かつ $`N\lt_{\textrm{PS}}M`$ ならば $`o(\textrm{Trans}(N))\lt o(\textrm{Trans}(M))`$。
- 単射性: $`N,N'`$ が上の左辺に属し $`o(\textrm{Trans}(N))=o(\textrm{Trans}(N'))`$ ならば $`N=N'`$（この主張は $`M\in CT_{\textrm{PS}}`$ を仮定しない）。
- 全射性: $`\alpha\lt o(\textrm{Trans}(M))`$ ならば、ある $`N`$ が存在して $`N\in CT_{\textrm{PS}}`$、$`N\lt_{\textrm{PS}}M`$、$`o(\textrm{Trans}(N))=\alpha`$。

順序を保つ部分は別に、$`M`$ に依らない形で述べられている。

- 順序同値: 任意の $`N,N'\in CT_{\textrm{PS}}`$ に対して $`N\lt_{\textrm{PS}}N'\iff o(\textrm{Trans}(N))\lt o(\textrm{Trans}(N'))`$。

**(2)**。任意の $`M\in CT_{\textrm{PS}}`$ に対して、$`\textrm{Trans}`$ は

```math
\{N\mid N\in CT_{\textrm{PS}}\land N\lt_{\textrm{PS}}M\}\ \to\ \{t\mid t\in OT_{\textrm{B}\omega}\land t\lt_{\textrm{B}}\textrm{Trans}(M)\}
```

の全単射である。やはり 3 本の合成である。

- 全域性: $`N\in CT_{\textrm{PS}}`$ かつ $`N\lt_{\textrm{PS}}M`$ ならば $`\textrm{Trans}(N)\in OT_{\textrm{B}\omega}`$ かつ $`\textrm{Trans}(N)\lt_{\textrm{B}}\textrm{Trans}(M)`$。
- 単射性: $`N,N'`$ が上の左辺に属し $`\textrm{Trans}(N)=\textrm{Trans}(N')`$ ならば $`N=N'`$（これも $`M\in CT_{\textrm{PS}}`$ を仮定しない）。
- 全射性: $`t\in OT_{\textrm{B}\omega}`$ かつ $`t\lt_{\textrm{B}}\textrm{Trans}(M)`$ ならば、ある $`N`$ が存在して $`N\in CT_{\textrm{PS}}`$、$`N\lt_{\textrm{PS}}M`$、$`\textrm{Trans}(N)=t`$。
- 順序同値: 任意の $`N,N'\in CT_{\textrm{PS}}`$ に対して $`N\lt_{\textrm{PS}}N'\iff\textrm{Trans}(N)\lt_{\textrm{B}}\textrm{Trans}(N')`$。

### Lean での証明

以下で使う既証明の道具は次のとおり。

- 命題（$`\textrm{Trans}`$ が順序を保つこと）: $`M,N\in CT_{\textrm{PS}}`$ かつ $`M\lt_{\textrm{PS}}N`$ ならば $`\textrm{Trans}(M)\lt_{\textrm{B}}\textrm{Trans}(N)`$。
- $`\textrm{Trans}`$ が標準形を保つこと（本体側 §8.7）: $`M\in ST_{\textrm{PS}}`$ ならば $`\textrm{Trans}(M)\in OT_{\textrm{B}}`$。$`M\in CT_{\textrm{PS}}`$ はその第 1 成分に $`M\in ST_{\textrm{PS}}`$ を含むので、$`M\in CT_{\textrm{PS}}`$ から $`\textrm{Trans}(M)\in OT_{\textrm{B}}`$ が出る。
- $`o`$ の単調性（[4] Lemma 2.2(c) にあたる。この形式化では順序型埋め込みの性質として証明されている）: $`s,t\in OT_{\textrm{B}}`$ かつ $`s\lt_{\textrm{B}}t`$ ならば $`o(s)\lt o(t)`$。
- 系（辞書式的順序の線形性）の三分律: 任意の有限ペア列 $`M,N`$ に対して $`M\lt_{\textrm{PS}}N`$ または $`M=N`$ または $`N\lt_{\textrm{PS}}M`$。
- $`\lt_{\textrm{B}}`$ の三分律・推移律・非反射性。
- 命題（変換写像の順序数への全単射性）の 3 本: 全域性（$`M\in CT_{\textrm{PS}}`$ ならば $`o(\textrm{Trans}(M))\lt\psi_0\psi_\omega0`$）、単射性（$`o\circ\textrm{Trans}`$ は $`CT_{\textrm{PS}}`$ 上で単射）、全射性（$`\alpha\lt\psi_0\psi_\omega0`$ ならばある $`M\in CT_{\textrm{PS}}`$ で $`o(\textrm{Trans}(M))=\alpha`$）。ここでの全域性は、命題（対応する項の上界）(1) すなわち $`\textrm{Trans}(M)\lt_{\textrm{B}}D_0D_\omega0`$ と、$`\psi_0\psi_\omega0`$ の定義（$`D_0D_\omega0`$ 未満の $`OT_{\textrm{B}}`$ の項の $`o`$ 値の上限）から出る。
- $`\textrm{Trans}`$ の $`CT_{\textrm{PS}}`$ 上の単射性（21 で $`\lt_{\textrm{PS}}`$ の三分律と順序保存と $`\lt_{\textrm{B}}`$ の非反射性から示されている）。
- 命題（対応する項の上界）(1): $`M\in CT_{\textrm{PS}}`$ ならば $`\textrm{Trans}(M)\lt_{\textrm{B}}D_0D_\omega0`$。
- 補題（対応する項の上界未満の字母）: $`t\lt_{\textrm{B}}D_0D_\omega0`$ ならば $`t\in OT_{\textrm{B}\omega}\iff t\in OT_{\textrm{B}}`$。

**(1) 全域性**。$`N`$ と、仮定 $`N\in CT_{\textrm{PS}}`$、$`N\lt_{\textrm{PS}}M`$ を取る。$`\textrm{Trans}`$ が標準形を保つことを $`N`$ と $`M`$ に適用して $`\textrm{Trans}(N)\in OT_{\textrm{B}}`$、$`\textrm{Trans}(M)\in OT_{\textrm{B}}`$。命題（$`\textrm{Trans}`$ が順序を保つこと）を $`N\lt_{\textrm{PS}}M`$ に適用して $`\textrm{Trans}(N)\lt_{\textrm{B}}\textrm{Trans}(M)`$。$`o`$ の単調性をこの 3 つに適用して $`o(\textrm{Trans}(N))\lt o(\textrm{Trans}(M))`$。ここまでは原文の「$`\textrm{Trans}`$ が順序を保つこと」から直接である。

**(1) 単射性**。$`N,N'`$ を取り、それぞれの仮定の第 1 成分 $`N\in CT_{\textrm{PS}}`$、$`N'\in CT_{\textrm{PS}}`$ だけを使う。命題（変換写像の順序数への全単射性）の単射性を $`N,N'`$ と $`o(\textrm{Trans}(N))=o(\textrm{Trans}(N'))`$ に適用して $`N=N'`$。$`N\lt_{\textrm{PS}}M`$ と $`N'\lt_{\textrm{PS}}M`$ は使わない。

**(1) 全射性**。$`\alpha`$ と仮定 $`\alpha\lt o(\textrm{Trans}(M))`$ を取る。

1. 命題（変換写像の順序数への全単射性）の全域性を $`M\in CT_{\textrm{PS}}`$ に適用して $`o(\textrm{Trans}(M))\lt\psi_0\psi_\omega0`$。順序数の $`\lt`$ の推移律と合わせて $`\alpha\lt\psi_0\psi_\omega0`$。
2. 同命題の全射性をこの $`\alpha\lt\psi_0\psi_\omega0`$ に適用して、$`N\in CT_{\textrm{PS}}`$ で $`o(\textrm{Trans}(N))=\alpha`$ なるものを得る。
3. あとは $`N\lt_{\textrm{PS}}M`$ を示せばよい。背理法で $`N\lt_{\textrm{PS}}M`$ でないと仮定し、$`\lt_{\textrm{PS}}`$ の三分律を $`N,M`$ に適用して 3 つの場合に分ける。
   - $`N\lt_{\textrm{PS}}M`$ の場合。背理法の仮定に反する。
   - $`N=M`$ の場合。$`o(\textrm{Trans}(N))=\alpha`$ の $`N`$ を $`M`$ に書き換えて $`o(\textrm{Trans}(M))=\alpha`$。これを仮定 $`\alpha\lt o(\textrm{Trans}(M))`$ に代入すると $`\alpha\lt\alpha`$ となり、$`\lt`$ の非反射性に反する。
   - $`M\lt_{\textrm{PS}}N`$ の場合。$`\textrm{Trans}`$ が標準形を保つことから $`\textrm{Trans}(M),\textrm{Trans}(N)\in OT_{\textrm{B}}`$、命題（$`\textrm{Trans}`$ が順序を保つこと）から $`\textrm{Trans}(M)\lt_{\textrm{B}}\textrm{Trans}(N)`$、$`o`$ の単調性から $`o(\textrm{Trans}(M))\lt o(\textrm{Trans}(N))=\alpha`$。仮定 $`\alpha\lt o(\textrm{Trans}(M))`$ と推移律で $`o(\textrm{Trans}(M))\lt o(\textrm{Trans}(M))`$ となり、非反射性に反する。

**(1) 順序同値**。両向きを示す。

- ($`\Rightarrow`$) $`N\lt_{\textrm{PS}}N'`$ から、全域性と同じ 3 手（標準形保存で $`OT_{\textrm{B}}`$ に入れる、順序保存で $`\lt_{\textrm{B}}`$ に移す、$`o`$ の単調性で $`\lt`$ に移す）で $`o(\textrm{Trans}(N))\lt o(\textrm{Trans}(N'))`$。
- ($`\Leftarrow`$) $`o(\textrm{Trans}(N))\lt o(\textrm{Trans}(N'))`$ を仮定し、$`\lt_{\textrm{PS}}`$ の三分律を $`N,N'`$ に適用する。$`N\lt_{\textrm{PS}}N'`$ の場合はそれが結論。$`N=N'`$ の場合は仮定が $`o(\textrm{Trans}(N))\lt o(\textrm{Trans}(N))`$ となり非反射性に反する。$`N'\lt_{\textrm{PS}}N`$ の場合は ($`\Rightarrow`$) を $`N',N`$ に適用して $`o(\textrm{Trans}(N'))\lt o(\textrm{Trans}(N))`$、仮定と推移律で $`o(\textrm{Trans}(N))\lt o(\textrm{Trans}(N))`$ となり非反射性に反する。

**(2) 全域性**。$`N`$ と仮定 $`N\in CT_{\textrm{PS}}`$、$`N\lt_{\textrm{PS}}M`$ を取る。$`\textrm{Trans}`$ が標準形を保つことを $`N`$ に適用して $`\textrm{Trans}(N)\in OT_{\textrm{B}}`$、その第 1 成分（$`OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}`$ の左側）を取って $`\textrm{Trans}(N)\in OT_{\textrm{B}\omega}`$。命題（$`\textrm{Trans}`$ が順序を保つこと）から $`\textrm{Trans}(N)\lt_{\textrm{B}}\textrm{Trans}(M)`$。この 2 つが目標の 2 成分である。

**(2) 単射性**。(1) の単射性と同じく、$`\textrm{Trans}`$ の $`CT_{\textrm{PS}}`$ 上の単射性を $`N,N'`$ の $`CT_{\textrm{PS}}`$ 成分だけに適用する。

**$`o`$ の単射性**（(2) の全射性のための補題）。$`a,b\in OT_{\textrm{B}}`$ と $`o(a)=o(b)`$ を仮定し、$`\lt_{\textrm{B}}`$ の三分律を $`a,b`$ に適用する。

- $`a\lt_{\textrm{B}}b`$ の場合。$`o`$ の単調性で $`o(a)\lt o(b)`$。$`o(a)=o(b)`$ で書き換えると $`o(b)\lt o(b)`$ となり非反射性に反する。
- $`a=b`$ の場合。それが結論。
- $`b\lt_{\textrm{B}}a`$ の場合。$`o`$ の単調性で $`o(b)\lt o(a)`$。$`o(a)=o(b)`$ で書き換えると $`o(a)\lt o(a)`$ となり非反射性に反する。

**(2) 全射性**。$`t`$ と仮定 $`t\in OT_{\textrm{B}\omega}`$、$`t\lt_{\textrm{B}}\textrm{Trans}(M)`$ を取る。

1. 命題（対応する項の上界）(1) を $`M\in CT_{\textrm{PS}}`$ に適用して $`\textrm{Trans}(M)\lt_{\textrm{B}}D_0D_\omega0`$。$`\lt_{\textrm{B}}`$ の推移律を $`t\lt_{\textrm{B}}\textrm{Trans}(M)`$ と合わせて $`t\lt_{\textrm{B}}D_0D_\omega0`$。
2. 補題（対応する項の上界未満の字母）をこの $`t\lt_{\textrm{B}}D_0D_\omega0`$ に適用すると $`t\in OT_{\textrm{B}\omega}\iff t\in OT_{\textrm{B}}`$。仮定 $`t\in OT_{\textrm{B}\omega}`$ から $`t\in OT_{\textrm{B}}`$。
3. $`\textrm{Trans}`$ が標準形を保つことから $`\textrm{Trans}(M)\in OT_{\textrm{B}}`$。$`o`$ の単調性を $`t\in OT_{\textrm{B}}`$、$`\textrm{Trans}(M)\in OT_{\textrm{B}}`$、$`t\lt_{\textrm{B}}\textrm{Trans}(M)`$ に適用して $`o(t)\lt o(\textrm{Trans}(M))`$。
4. (1) の全射性をこの $`o(t)\lt o(\textrm{Trans}(M))`$ に適用して、$`N\in CT_{\textrm{PS}}`$、$`N\lt_{\textrm{PS}}M`$、$`o(\textrm{Trans}(N))=o(t)`$ なる $`N`$ を得る。
5. $`\textrm{Trans}`$ が標準形を保つことから $`\textrm{Trans}(N)\in OT_{\textrm{B}}`$。上の $`o`$ の単射性を $`\textrm{Trans}(N)\in OT_{\textrm{B}}`$、$`t\in OT_{\textrm{B}}`$、$`o(\textrm{Trans}(N))=o(t)`$ に適用して $`\textrm{Trans}(N)=t`$。これが求める原像である。

**(2) 順序同値**。両向きを示す。

- ($`\Rightarrow`$) 命題（$`\textrm{Trans}`$ が順序を保つこと）そのもの。
- ($`\Leftarrow`$) $`\textrm{Trans}(N)\lt_{\textrm{B}}\textrm{Trans}(N')`$ を仮定し、$`\lt_{\textrm{PS}}`$ の三分律を $`N,N'`$ に適用する。$`N\lt_{\textrm{PS}}N'`$ の場合はそれが結論。$`N=N'`$ の場合は仮定が $`\textrm{Trans}(N)\lt_{\textrm{B}}\textrm{Trans}(N)`$ となり $`\lt_{\textrm{B}}`$ の非反射性に反する。$`N'\lt_{\textrm{PS}}N`$ の場合は順序保存で $`\textrm{Trans}(N')\lt_{\textrm{B}}\textrm{Trans}(N)`$、$`\lt_{\textrm{B}}`$ の推移律で $`\textrm{Trans}(N)\lt_{\textrm{B}}\textrm{Trans}(N)`$ となり非反射性に反する。

以上の 3 本ずつを組にして、(1) は写像 $`N\mapsto o(\textrm{Trans}(N))`$ の、(2) は $`\textrm{Trans}`$ の、指定した 2 つの集合の間の全単射性が得られる。

## 原文通りに書けなかった理由

- **[S]** (1) の値域の $`\alpha\in o(\textrm{Trans}(M))`$ を $`\alpha\lt o(\textrm{Trans}(M))`$ と書いている

  原文は順序数をフォン・ノイマン流の集合として扱い、値域を $`\{\alpha\mid\alpha\in o(\textrm{Trans}(M))\}`$、その順序を $`\in`$ と書く。この形式化の順序数の型には $`\in`$ が無く、順序は $`\lt`$ だけである。そこで値域を $`\{\alpha\mid\alpha\lt o(\textrm{Trans}(M))\}`$、その順序を $`\lt`$ として述べている。順序数に対して $`\alpha\in\beta`$ と $`\alpha\lt\beta`$ は同じ関係なので、集合としても順序集合としても原文と同じものであり、下流（定理（変換写像の全単射性））も変わらない。

- **[S]** 「同型写像」を、全単射性と順序同値の 2 本に分けて述べている

  原文は (1)(2) とも「同型写像である」と一言で述べる。Lean は (1)(2) それぞれについて、指定した 2 集合の間の全単射性（全域性・単射性・全射性の 3 本の組）と、順序を保つことの同値（$`N\lt_{\textrm{PS}}N'\iff\cdots`$）を別々の命題として述べており、両者を 1 つの順序同型の対象として束ねてはいない。順序同値のほうは $`\{N\in CT_{\textrm{PS}}\mid N\lt_{\textrm{PS}}M\}`$ に制限せず $`CT_{\textrm{PS}}`$ 全体で述べているので、制限すれば原文の同型写像の順序条件になる。下流の定理（変換写像の全単射性）はこの 2 本をそれぞれ別に引いており、束ねた対象を必要としない。

- **[R]** 単射性の 2 本は $`M\in CT_{\textrm{PS}}`$ を仮定しない

  原文は (1)(2) とも「任意の $`M\in CT_{\textrm{PS}}`$ に対して」で始まるが、Lean の単射性 2 本は $`M`$ を任意の有限ペア列として量化し、$`M\in CT_{\textrm{PS}}`$ を仮定していない。証明は定義域の元 $`N,N'`$ の $`CT_{\textrm{PS}}`$ 成分だけを使い、$`N\lt_{\textrm{PS}}M`$ も $`M\in CT_{\textrm{PS}}`$ も使わないためである。全単射性としてまとめる段では原文どおり $`M\in CT_{\textrm{PS}}`$ を仮定するので、下流は変わらない。

- **[W]** (1) の全射性は「即座に」出ない

  原文の (1) の証明は「$`\textrm{Trans}`$ が順序を保つこと及び変換写像の順序数への全単射性より即座に従う」だけである。全域性はたしかにこの 2 つの直接の帰結だが、全射性はそうではない。命題（変換写像の順序数への全単射性）の全射性が使えるのは $`\alpha\lt\psi_0\psi_\omega0`$ のときであり、まず同命題の全域性で $`o(\textrm{Trans}(M))\lt\psi_0\psi_\omega0`$ を出して推移律で $`\alpha`$ を $`\psi_0\psi_\omega0`$ の下へ移す必要がある。さらに、そうして得た $`N\in CT_{\textrm{PS}}`$ が $`N\lt_{\textrm{PS}}M`$ を満たすことは自動ではなく、$`\lt_{\textrm{PS}}`$ の三分律で $`N=M`$ と $`M\lt_{\textrm{PS}}N`$ を潰して初めて得られる（前者は $`\alpha\lt\alpha`$、後者は $`o(\textrm{Trans}(M))\lt\alpha\lt o(\textrm{Trans}(M))`$ で矛盾）。埋めるのに要ったのは既証明の三分律と順序数の $`\lt`$ の非反射性・推移律だけで、形式化の範疇に収まる。

  同じ形の場合分けは (2) の単射性が引く $`\textrm{Trans}`$ の $`CT_{\textrm{PS}}`$ 上の単射性にも現れるが、そちらは 21 で済んでいる。

- **[W]** 順序の反射（$`o`$ 側・項側から $`\lt_{\textrm{PS}}`$ を復元する向き）は原文が挙げる根拠からは出ない

  「同型写像」であるためには順序の両向きの同値が要るのに、原文が (1) で挙げるのは「$`\textrm{Trans}`$ が順序を保つこと」、すなわち $`N\lt_{\textrm{PS}}N'\Rightarrow\textrm{Trans}(N)\lt_{\textrm{B}}\textrm{Trans}(N')`$ の一方向だけである。逆向き（$`o(\textrm{Trans}(N))\lt o(\textrm{Trans}(N'))\Rightarrow N\lt_{\textrm{PS}}N'`$、および項側の $`\textrm{Trans}(N)\lt_{\textrm{B}}\textrm{Trans}(N')\Rightarrow N\lt_{\textrm{PS}}N'`$）は、$`\lt_{\textrm{PS}}`$ の三分律で $`N=N'`$ と $`N'\lt_{\textrm{PS}}N`$ を潰して埋めている。潰すのに使うのは順序数の $`\lt`$ と $`\lt_{\textrm{B}}`$ の非反射性・推移律だけである。

- **[R]** (2) で原文が引く「$`o`$ が同型写像であること」の全射側と、$`o^{-1}`$ の構成が要らない

  原文の (2) は、まず 対応する項の上界(1)と(2)、対応する項の上界未満の字母、[4] の Lemma 2.2(c) と Lemma 2.3(b) から「$`o`$ は $`(\{t\in OT_{\textrm{B}\omega}\mid t\lt_{\textrm{B}}D_0D_\omega0\},\lt_{\textrm{B}})\to(\psi_0\psi_\omega0,\in)`$ の同型写像である」を立て、$`\textrm{Trans}=o^{-1}\circ o\circ\textrm{Trans}`$ と書いて (1) に帰着する。Lean はこの同型写像も $`o^{-1}`$ も作らない。(2) の全射性で必要なのは、$`o(\textrm{Trans}(N))=o(t)`$ から $`\textrm{Trans}(N)=t`$ を出すこと、つまり $`o`$ の $`OT_{\textrm{B}}`$ 上の単射性だけであり、それは $`\lt_{\textrm{B}}`$ の三分律と $`o`$ の単調性から 3 行で出る。したがって $`o`$ の全射側と、そのために原文が引く 対応する項の上界(2) および [4] Lemma 2.3(b) は (2) の証明に現れない。$`o`$ を $`D_0D_\omega0`$ 未満の項の集合の順序型として構成しているので、原文が主張する $`o(D_0D_\omega0)=\psi_0\psi_\omega0`$ も引く必要がない。なお 対応する項の上界(2) と Lemma 2.3(b) に相当する共終性は、(1) が引く 命題（変換写像の順序数への全単射性）の全射性の中では使われており、間接的には効いている。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $`CT_{\textrm{PS}}`$ | `CTPS` | `lean/Bijectivity/Defs.lean` |
| $`M\lt_{\textrm{PS}}N`$ | `ltPS` | 同上 |
| $`\textrm{Trans}`$ | `PSS.Trans` | `lean/PSS/Trans.lean` |
| $`OT_{\textrm{B}\omega}`$ | `PSS.OT` | `lean/Buchholz-1986/Buchholz-1986-2.2.lean` |
| $`OT_{\textrm{B}}`$ | `PSS.OT_B` | 同上 |
| $`s\lt_{\textrm{B}}t`$ | `PSS.lessBT` | `lean/Buchholz-1986/Buchholz-1986-2.1-order.lean` |
| $`\lt_{\textrm{B}}`$ の三分律 | `PSS.lessBT_linear_trichotomy` | 同上 |
| $`\lt_{\textrm{B}}`$ の推移律 | `PSS.lessBT_linear_trans` | 同上 |
| $`\lt_{\textrm{B}}`$ の非反射性 | `PSS.lessBT_linear_irrefl` | 同上 |
| $`o`$ | `o` | `lean/Bijectivity/Cited.lean` |
| $`\psi_0\psi_\omega0`$ | `psi0psiOmega0` | 同上 |
| $`D_0D_\omega0`$ | `DzeroDomegaZero` | 同上 |
| $`o`$ の単調性（[4] Lemma 2.2(c)） | `o_lt_of_lessBT` | 同上 |
| $`s\lt_{\textrm{B}}D_0D_\omega0\Rightarrow o(s)\lt\psi_0\psi_\omega0`$ | `o_lt_psi` | 同上 |
| 系（辞書式的順序の線形性）の三分律 | `ltPS_trichotomy` | `lean/Bijectivity/02-lex-linear.lean` |
| 命題（$`\textrm{Trans}`$ が順序を保つこと） | `trans_lessBT_of_ltPS` | `lean/Bijectivity/18-trans-preserves-order.lean` |
| 補題（対応する項の上界未満の字母） | `OT_iff_OT_B_of_lt` | `lean/Bijectivity/19-alphabet-below-bound.lean` |
| 命題（対応する項の上界）(1) | `trans_lt_bound` | `lean/Bijectivity/20-term-upper-bound.lean` |
| 命題（対応する項の上界）(2)（本系では未使用） | `exists_trans_gt` | 同上 |
| $`\textrm{Trans}`$ が標準形を保つこと | `Trans_STPS_OT_B` | `lean/8/8.7-termination.lean` |
| $`M\in CT_{\textrm{PS}}\Rightarrow\textrm{Trans}(M)\in OT_{\textrm{B}}`$ | `OTB_Trans_of_CTPS` | `lean/Bijectivity/21-ordinal-bijectivity.lean` |
| 命題（変換写像の順序数への全単射性）の全域性 | `oTrans_mapsTo` | 同上 |
| 同 単射性 | `oTrans_injOn` | 同上 |
| 同 全射性 | `oTrans_surjOn` | 同上 |
| $`\textrm{Trans}`$ の $`CT_{\textrm{PS}}`$ 上の単射性 | `trans_injOn` | 同上 |
| (1) の全域性 | `analysis_ordinal_mapsTo` | `lean/Bijectivity/22-pair-sequence-analysis.lean` |
| (1) の単射性 | `analysis_ordinal_injOn` | 同上 |
| (1) の全射性 | `analysis_ordinal_surjOn` | 同上 |
| (1) の順序同値 | `analysis_ordinal_lt` | 同上 |
| 系 (1)（全単射性） | `analysis_ordinal` | 同上 |
| (2) の全域性 | `analysis_term_mapsTo` | 同上 |
| (2) の単射性 | `analysis_term_injOn` | 同上 |
| $`o`$ の $`OT_{\textrm{B}}`$ 上の単射性 | `o_injective` | 同上 |
| (2) の全射性 | `analysis_term_surjOn` | 同上 |
| (2) の順序同値 | `analysis_term_lt` | 同上 |
| 系 (2)（全単射性） | `analysis_term` | 同上 |

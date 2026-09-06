[← back](README.md)

# 01: 系 (辞書式的順序が辞書式順序であること)

## 原文

### 命題

系 (辞書式的順序が辞書式順序であること)

$`\lt_{\textrm{lex}}`$ を数列に対する辞書式順序としたとき、任意の $`M,N\in T_{\textrm{PS}}`$ に対して、$`M\lt_{\textrm{PS}}N`$ は $`\bigoplus_\mathbb{N}M\lt_{\textrm{lex}}\bigoplus_\mathbb{N}N`$ と同値である。

この系が参照する $`\lt_{\textrm{PS}}`$ は、原文の「表記」節で次のように定められている。

$`T_{\textrm{PS}}^2`$ 上の関係 $`\lt_{\textrm{PS}}`$ を以下のように再帰的に定める。

- 任意の $`M,N\in T_{\textrm{PS}}`$ に対して、$`M\lt_{\textrm{PS}}N`$ は次のいずれかが成り立つことと同値である。
  - $`M_{0,0}\lt  N_{0,0}`$ である。
  - $`M_{0,0}=N_{0,0}`$ かつ $`M_{1,0}\lt  N_{1,0}`$ である。
  - $`M_{0,0}=N_{0,0}`$ かつ $`M_{1,0}=N_{1,0}`$ かつ $`(M_i)_{i=1}^{\textrm{Lng}(M)-1}\lt_{\textrm{PS}}(N_i)_{i=1}^{\textrm{Lng}(N)-1}`$ である。

また $`\bigoplus_A a`$（配列の成分の結合）と $`M_{i,j}`$（2次元配列の要素）は [1] から引き継いだ記法で、$`M_{i,j}=(M_j)_i`$ である。$`\lt_{\textrm{lex}}`$ は原文では定義されず、「数列に対する辞書式順序」と呼ばれるだけである。

### 証明

証明

  $`\lt_{\textrm{PS}}`$ の定義から即座に従う。□

## Lean

### Lean での命題

対象はペア列全体 $`(\mathbb{N}^2)^{\lt\omega}`$、すなわち空列 $`()`$ を含む $`\mathbb{N}^2`$ 値有限列全体である（$`T_{\textrm{PS}}`$ はこのうち $`()`$ を除いたもの）。

平坦化 $`\bigoplus_\mathbb{N}`$ は列の長さに関する再帰で定める。$`p=(p_0,p_1)\in\mathbb{N}^2`$ に対し

```math
\bigoplus_\mathbb{N}() = (),\qquad \bigoplus_\mathbb{N}\bigl((p)\oplus_{\mathbb{N}^2}M\bigr) = (p_0,p_1)\oplus_\mathbb{N}\bigoplus_\mathbb{N}M .
```

展開すれば $`\bigoplus_\mathbb{N}M=(M_{0,0},M_{1,0},M_{0,1},M_{1,1},\dots,M_{0,\textrm{Lng}(M)-1},M_{1,\textrm{Lng}(M)-1})`$ であり、長さは $`2\,\textrm{Lng}(M)`$ である。

$`\lt_{\textrm{lex}}`$ は $`\mathbb{N}`$ 値有限列の対の上で、次の 4 節による再帰で定める。$`a,b\in\mathbb{N}`$、$`x,y`$ は $`\mathbb{N}`$ 値有限列とする。

1. $`() \lt_{\textrm{lex}} ()`$ は偽。
2. $`() \lt_{\textrm{lex}} (b)\oplus_\mathbb{N} y`$ は真。
3. $`(a)\oplus_\mathbb{N} x \lt_{\textrm{lex}} ()`$ は偽。
4. $`(a)\oplus_\mathbb{N} x \lt_{\textrm{lex}} (b)\oplus_\mathbb{N} y`$ は $`a\lt b \lor (a=b \land x\lt_{\textrm{lex}}y)`$ と同値。

すなわち「真の先頭部分列は小さい」という規約の辞書式順序である。

$`\lt_{\textrm{PS}}`$ も同じ形の 4 節による再帰で定める。$`p=(p_0,p_1)`$、$`q=(q_0,q_1)`$、$`M,N`$ はペア列とする。

1. $`() \lt_{\textrm{PS}} ()`$ は偽。
2. $`() \lt_{\textrm{PS}} (q)\oplus_{\mathbb{N}^2} N`$ は真。
3. $`(p)\oplus_{\mathbb{N}^2} M \lt_{\textrm{PS}} ()`$ は偽。
4. $`(p)\oplus_{\mathbb{N}^2} M \lt_{\textrm{PS}} (q)\oplus_{\mathbb{N}^2} N`$ は
   $`p_0\lt q_0 \ \lor\ (p_0=q_0 \land p_1\lt q_1) \ \lor\ (p_0=q_0 \land p_1=q_1 \land M\lt_{\textrm{PS}}N)`$
   と同値。

第 4 節の 3 つの選言肢が、原文の 3 つの場合分けにそれぞれ対応する（$`p_0=M_{0,0}`$、$`p_1=M_{1,0}`$、$`M`$ が $`(M_i)_{i=1}^{\textrm{Lng}(M)-1}`$）。第 1-3 節は原文には無く、再帰が空列に達したときのために補ったものである。

証明した命題は次である。

```math
\forall M,N\in(\mathbb{N}^2)^{\lt\omega}\ \bigl(M\lt_{\textrm{PS}}N \iff \bigoplus_\mathbb{N}M\lt_{\textrm{lex}}\bigoplus_\mathbb{N}N\bigr)
```

$`M,N\in T_{\textrm{PS}}`$ という仮定は置いていない。

### Lean での証明

$`M`$ に関する構造帰納法。$`N`$ は各段で全称のまま残すので、帰納法の仮定は

```math
\forall N\ \bigl(M'\lt_{\textrm{PS}}N \iff \bigoplus_\mathbb{N}M'\lt_{\textrm{lex}}\bigoplus_\mathbb{N}N\bigr)
```

という形（$`M'`$ は $`M`$ の尾部）で使える。

基底段階 $`M=()`$。$`N`$ で場合分けする。

- $`N=()`$ のとき。左辺は $`\lt_{\textrm{PS}}`$ の第 1 節より偽。右辺は $`\bigoplus_\mathbb{N}()=()`$ だから $`()\lt_{\textrm{lex}}()`$ で、$`\lt_{\textrm{lex}}`$ の第 1 節より偽。偽 $`\iff`$ 偽。
- $`N=(q)\oplus_{\mathbb{N}^2}N'`$ のとき。左辺は $`\lt_{\textrm{PS}}`$ の第 2 節より真。右辺は $`\bigoplus_\mathbb{N}N=(q_0,q_1)\oplus_\mathbb{N}\bigoplus_\mathbb{N}N'`$ が空でないので、$`\lt_{\textrm{lex}}`$ の第 2 節より真。真 $`\iff`$ 真。

帰納段階 $`M=(p)\oplus_{\mathbb{N}^2}M'`$。$`N`$ で場合分けする。

- $`N=()`$ のとき。左辺は $`\lt_{\textrm{PS}}`$ の第 3 節より偽。右辺は $`\bigoplus_\mathbb{N}M=(p_0,p_1)\oplus_\mathbb{N}\bigoplus_\mathbb{N}M'`$ が空でなく $`\bigoplus_\mathbb{N}()=()`$ なので、$`\lt_{\textrm{lex}}`$ の第 3 節より偽。偽 $`\iff`$ 偽。
- $`N=(q)\oplus_{\mathbb{N}^2}N'`$ のとき。左辺を $`\lt_{\textrm{PS}}`$ の第 4 節で 1 回展開し、その第 3 選言肢の中の $`M'\lt_{\textrm{PS}}N'`$ を帰納法の仮定（$`N:=N'`$）で書き換えると

  $`p_0\lt q_0 \ \lor\ (p_0=q_0 \land p_1\lt q_1) \ \lor\ \bigl(p_0=q_0 \land p_1=q_1 \land \textstyle\bigoplus_\mathbb{N}M'\lt_{\textrm{lex}}\bigoplus_\mathbb{N}N'\bigr).`$

  右辺は平坦化の定義から

  $`\bigoplus_\mathbb{N}M = (p_0)\oplus_\mathbb{N}(p_1)\oplus_\mathbb{N}\bigoplus_\mathbb{N}M', \qquad \bigoplus_\mathbb{N}N = (q_0)\oplus_\mathbb{N}(q_1)\oplus_\mathbb{N}\bigoplus_\mathbb{N}N'`$

  であり、$`\lt_{\textrm{lex}}`$ の第 4 節を先頭成分 $`p_0,q_0`$ について 1 回適用して

  $`p_0\lt q_0 \ \lor\ \Bigl(p_0=q_0 \land \bigl((p_1)\oplus_\mathbb{N}\textstyle\bigoplus_\mathbb{N}M' \lt_{\textrm{lex}} (q_1)\oplus_\mathbb{N}\bigoplus_\mathbb{N}N'\bigr)\Bigr),`$

  さらに第 4 節を第 2 成分 $`p_1,q_1`$ についてもう 1 回適用して

  $`p_0\lt q_0 \ \lor\ \Bigl(p_0=q_0 \land \bigl(p_1\lt q_1 \lor (p_1=q_1 \land \textstyle\bigoplus_\mathbb{N}M'\lt_{\textrm{lex}}\bigoplus_\mathbb{N}N')\bigr)\Bigr)`$

  となる。したがって残るのは、$`A:\ p_0\lt q_0`$、$`B:\ p_0=q_0`$、$`C:\ p_1\lt q_1`$、$`D:\ p_1=q_1`$、$`E:\ \bigoplus_\mathbb{N}M'\lt_{\textrm{lex}}\bigoplus_\mathbb{N}N'`$ と置いたときの命題論理の同値

  $`A \lor (B\land C) \lor (B\land D\land E) \iff A \lor \bigl(B \land (C \lor (D\land E))\bigr)`$

  のみである。これを両方向とも、選言肢ごとに明示的に構成する。

  - $`\Longrightarrow`$ 方向。仮定を 3 つの選言肢に分解する。$`A`$ が成り立つ場合は右辺の第 1 選言肢を取る。$`B\land C`$ が成り立つ場合は右辺の第 2 選言肢を取り、その内側では $`C\lor(D\land E)`$ の第 1 選言肢を取る。$`B\land D\land E`$ が成り立つ場合は右辺の第 2 選言肢を取り、その内側では $`D\land E`$ 側を取る。
  - $`\Longleftarrow`$ 方向。仮定を分解すると $`A`$、$`B\land C`$、$`B\land(D\land E)`$ の 3 つになる。$`A`$ の場合は左辺の第 1 選言肢、$`B\land C`$ の場合は左辺の第 2 選言肢、$`B\land(D\land E)`$ の場合は左辺の第 3 選言肢（連言を $`B\land D\land E`$ に組み替える）を取る。

以上で全ての場合が尽くされ、同値が示された。

## 原文通りに書けなかった理由

- **[W]** 原文の $`\lt_{\textrm{PS}}`$ の再帰は $`T_{\textrm{PS}}`$ の外（空列）へ出るのに、空列の場合が定義されていない

  原文は $`\lt_{\textrm{PS}}`$ を「$`T_{\textrm{PS}}^2`$ 上の関係」として 3 つの場合だけで定めるが、第 3 の場合の右辺 $`(M_i)_{i=1}^{\textrm{Lng}(M)-1}\lt_{\textrm{PS}}(N_i)_{i=1}^{\textrm{Lng}(N)-1}`$ の両辺は $`\textrm{Lng}(M)=1`$ や $`\textrm{Lng}(N)=1`$ のとき空列になり、$`T_{\textrm{PS}}`$ に属さない。したがって原文の再帰は $`T_{\textrm{PS}}^2`$ 上で閉じておらず、そのままでは $`M=((0,0))`$、$`N=((0,0),(0,0))`$ のような $`T_{\textrm{PS}}`$ の元の対ですら値が定まらない。Lean 側では空列を含む $`(\mathbb{N}^2)^{\lt\omega}`$ 上の再帰とし、$`()\lt_{\textrm{PS}}()`$ を偽、$`()\lt_{\textrm{PS}}(q)\oplus_{\mathbb{N}^2}N`$ を真、$`(p)\oplus_{\mathbb{N}^2}M\lt_{\textrm{PS}}()`$ を偽として補った。系の主張も $`T_{\textrm{PS}}`$ ではなく $`(\mathbb{N}^2)^{\lt\omega}`$ の全ての対について述べている（この一般化がないと帰納法が閉じない。また補った 3 節は原文の 3 つの場合と重ならないので、$`T_{\textrm{PS}}`$ 上での原文の主張はそのまま含まれる）。

- **[W]** 原文は $`\lt_{\textrm{lex}}`$ を定義していない

  原文は「$`\lt_{\textrm{lex}}`$ を数列に対する辞書式順序としたとき」と書くだけで、長さの異なる列をどう比べるかを述べていない。Lean 側では「真の先頭部分列は小さい」規約（$`()\lt_{\textrm{lex}}(b)\oplus_\mathbb{N}y`$ を真とする）で定義した。この系だけを見るなら規約は一意には決まらない。$`\lt_{\textrm{PS}}`$ と $`\lt_{\textrm{lex}}`$ の空列の扱いを揃えさえすれば、両辺は同時に真偽が入れ替わるので同値は保たれるからである。規約を固定しているのは下流の系（辞書式的順序の線形性）の三分律で、たとえば $`M=((0,0))`$、$`N=((0,0),(0,0))`$ は相異なるので $`M\lt_{\textrm{PS}}N`$ か $`N\lt_{\textrm{PS}}M`$ のいずれかが要り、$`()\lt_{\textrm{PS}}(q)\oplus_{\mathbb{N}^2}N`$ を偽とする規約では両方が偽になって三分律が壊れる。

- **[W]** 原文の「定義から即座に従う」は、列の長さに関する帰納法と選言の組み替えを隠している

  原文の証明は 1 行だが、$`\lt_{\textrm{PS}}`$ は再帰的定義なので、同値を示すには $`\textrm{Lng}(M)`$ に関する帰納法（$`N`$ は全称のまま一般化する）と、$`M`$ が空か否か・$`N`$ が空か否かによる 4 通りの場合分けが要る。さらに非空同士の場合、$`\lt_{\textrm{PS}}`$ の 3 選言肢は $`p_0=q_0`$ を 2 度書く平坦な形であるのに対し、$`\lt_{\textrm{lex}}`$ を 2 回展開して得られる形は $`p_0=q_0`$ を括り出した入れ子の形であり、$`A\lor(B\land C)\lor(B\land D\land E) \iff A\lor(B\land(C\lor(D\land E)))`$ という命題論理の組み替えを両方向 3 場合ずつ明示的に与えている。この組み替えが「定義から」の実体である。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| $`M\lt_{\textrm{PS}}N`$ | `ltPS` | `lean/Bijectivity/Defs.lean` |
| ペア列全体 $`(\mathbb{N}^2)^{\lt\omega}`$ | `PSS.PS` | `lean/PSS/Defs.lean` |
| $`T_{\textrm{PS}}`$ | `PSS.TPS` | 同上 |
| $`\bigoplus_\mathbb{N}M`$ | `flatten` | `lean/Bijectivity/01-lex-is-lexicographic.lean` |
| $`x\lt_{\textrm{lex}}y`$ | `ltLex` | 同上 |
| 系（辞書式的順序が辞書式順序であること） | `ltPS_iff_ltLex` | 同上 |
| 系（辞書式的順序の線形性）の三分律 | `ltPS_trichotomy` | `lean/Bijectivity/02-lex-linear.lean` |

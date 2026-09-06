[← back](README.md)

# 02: 系 (辞書式的順序の線形性)

## 原文

### 命題

系 (辞書式的順序の線形性)（原文の命題に通し番号は付いていない）

$`\lt_{\textrm{PS}}`$ は狭義全順序、$`\leq_{\textrm{PS}}`$ は全順序である。

### 証明

証明

辞書式的順序が辞書式順序であることより即座に従う。□

ここで引かれている直前の系（辞書式的順序が辞書式順序であること）は次のものである。

$`\lt_{\textrm{lex}}`$ を数列に対する辞書式順序としたとき、任意の $`M,N\in T_{\textrm{PS}}`$ に対して、$`M\lt_{\textrm{PS}}N`$ は $`\bigoplus_\mathbb{N}M\lt_{\textrm{lex}}\bigoplus_\mathbb{N}N`$ と同値である。

また原文の表記節で、$`\lt_{\textrm{PS}}`$ は $`T_{\textrm{PS}}^2`$ 上の関係として次のように再帰的に定められている。

任意の $`M,N\in T_{\textrm{PS}}`$ に対して、$`M\lt_{\textrm{PS}}N`$ は次のいずれかが成り立つことと同値である。

- $`M_{0,0}\lt  N_{0,0}`$ である。
- $`M_{0,0}=N_{0,0}`$ かつ $`M_{1,0}\lt  N_{1,0}`$ である。
- $`M_{0,0}=N_{0,0}`$ かつ $`M_{1,0}=N_{1,0}`$ かつ $`(M_i)_{i=1}^{\textrm{Lng}(M)-1}\lt_{\textrm{PS}}(N_i)_{i=1}^{\textrm{Lng}(N)-1}`$ である。

任意の $`M,N\in T_{\textrm{PS}}`$ に対して $`M\leq_{\textrm{PS}}N`$ を $`M=N\lor M\lt_{\textrm{PS}}N`$ の略記とする。

## Lean

### Lean での命題

ペア列を先頭ペアと残りに分けて $`M=p::M'`$ と書き、ペア $`p`$ の第 $`0`$ 成分・第 $`1`$ 成分を $`p_0,p_1`$ と書く（原文の $`M_{0,0},M_{1,0}`$ が $`p_0,p_1`$ にあたる）。$`\mathbb{N}`$ の有限列も同様に $`x=a::x'`$ と書く。

Lean は原文の「狭義全順序」「全順序」をその構成要素に分解し、次の 7 つを示す。$`M,N,O`$ は**空列を含む**任意のペア列であって、原文の $`M,N\in T_{\textrm{PS}}`$ という制限は付いていない。

1. 非反射性: $`\lnot\,(M\lt_{\textrm{PS}}M)`$
2. 推移性: $`M\lt_{\textrm{PS}}N`$ かつ $`N\lt_{\textrm{PS}}O`$ ならば $`M\lt_{\textrm{PS}}O`$
3. 三分律: $`M\lt_{\textrm{PS}}N\ \lor\ M=N\ \lor\ N\lt_{\textrm{PS}}M`$
4. 全律: $`M\leq_{\textrm{PS}}N\ \lor\ N\leq_{\textrm{PS}}M`$
5. 反射性: $`M\leq_{\textrm{PS}}M`$
6. $`\leq_{\textrm{PS}}`$ の推移性: $`M\leq_{\textrm{PS}}N`$ かつ $`N\leq_{\textrm{PS}}O`$ ならば $`M\leq_{\textrm{PS}}O`$
7. 反対称性: $`M\leq_{\textrm{PS}}N`$ かつ $`N\leq_{\textrm{PS}}M`$ ならば $`M=N`$

ここで $`\leq_{\textrm{PS}}`$ は原文どおり $`M=N\lor M\lt_{\textrm{PS}}N`$ の略記である。1・2・3 が「$`\lt_{\textrm{PS}}`$ は狭義全順序」、4・5・6・7 が「$`\leq_{\textrm{PS}}`$ は全順序」の中身である。

その手前に、$`\mathbb{N}`$ の有限列（空列を含む）上の $`\lt_{\textrm{lex}}`$ について同じ 3 性質を示す。

8. $`\lnot\,(x\lt_{\textrm{lex}}x)`$
9. $`x\lt_{\textrm{lex}}y`$ かつ $`y\lt_{\textrm{lex}}z`$ ならば $`x\lt_{\textrm{lex}}z`$
10. $`x\lt_{\textrm{lex}}y\ \lor\ x=y\ \lor\ y\lt_{\textrm{lex}}x`$

さらに三分律の等号の場合のために

11. 平坦化の単射性: $`\bigoplus_\mathbb{N}M=\bigoplus_\mathbb{N}N`$ ならば $`M=N`$

を示す。

同じ節にはもう 1 ファイルあり、原文に対応する記述の無い次の 2 つのリスト補題を置いている（下流の命題（基本列の辞書式的縮小性）の証明で使う）。

12. 共通接頭辞の消去: 任意のペア列 $`A,B,C`$ に対して $`(A\oplus_{\mathbb{N}^2}B)\lt_{\textrm{PS}}(A\oplus_{\mathbb{N}^2}C)`$ は $`B\lt_{\textrm{PS}}C`$ と同値である。
13. 真の接頭辞の小ささ: $`k\lt\textrm{Lng}(M)`$ ならば $`(M_j)_{j=0}^{k-1}\lt_{\textrm{PS}}M`$ である。

### Lean での証明

証明で使う定義を先に書く。$`\lt_{\textrm{PS}}`$ は原文の 3 条件を先頭ペアの比較として読み、さらに空列の場合を辞書式順序の規約で補ったもの、$`\lt_{\textrm{lex}}`$ は $`\mathbb{N}`$ の有限列の辞書式順序、$`\bigoplus_\mathbb{N}`$ は平坦化である。

```math
\lnot\bigl([]\lt_{\textrm{PS}}[]\bigr),\qquad []\lt_{\textrm{PS}}(q::N),\qquad \lnot\bigl((p::M)\lt_{\textrm{PS}}[]\bigr),
```
```math
(p::M)\lt_{\textrm{PS}}(q::N)\iff p_0\lt q_0\ \lor\ (p_0=q_0\land p_1\lt q_1)\ \lor\ (p_0=q_0\land p_1=q_1\land M\lt_{\textrm{PS}}N)
```

```math
\lnot\bigl([]\lt_{\textrm{lex}}[]\bigr),\qquad []\lt_{\textrm{lex}}(b::y),\qquad \lnot\bigl((a::x)\lt_{\textrm{lex}}[]\bigr),
```
```math
(a::x)\lt_{\textrm{lex}}(b::y)\iff a\lt b\ \lor\ (a=b\land x\lt_{\textrm{lex}}y)
```

```math
\bigoplus_\mathbb{N}[]=[],\qquad \bigoplus_\mathbb{N}(p::M)=p_0::p_1::\bigoplus_\mathbb{N}M
```

#### 8. $`\lt_{\textrm{lex}}`$ の非反射性

$`x`$ についての構造帰納法。

- $`x=[]`$ のとき、定義より $`[]\lt_{\textrm{lex}}[]`$ は偽なので、その否定が成り立つ。
- $`x=a::x'`$ のとき、示すべきは $`\lnot\,\bigl(a\lt a\lor(a=a\land x'\lt_{\textrm{lex}}x')\bigr)`$ である。ド・モルガンでこれは $`\lnot(a\lt a)`$ と $`\bigl(a=a\Rightarrow\lnot(x'\lt_{\textrm{lex}}x')\bigr)`$ の連言と同値になる。前者は $`\mathbb{N}`$ 上の $`\lt`$ の非反射性、後者は帰納法の仮定（$`a=a`$ という前提は捨てる）。

#### 9. $`\lt_{\textrm{lex}}`$ の推移性

$`x,y,z`$ の 3 つの構造についての同時再帰。場合分けは次の 6 通りである。

- $`x=[],\ y=[]`$: 仮定 $`x\lt_{\textrm{lex}}y`$ が $`[]\lt_{\textrm{lex}}[]`$、すなわち偽なので矛盾。
- $`x=[],\ y=b::y',\ z=[]`$: 仮定 $`y\lt_{\textrm{lex}}z`$ が $`(b::y')\lt_{\textrm{lex}}[]`$、すなわち偽なので矛盾。
- $`x=[],\ y=b::y',\ z=c::z'`$: 結論 $`[]\lt_{\textrm{lex}}(c::z')`$ は定義より真。
- $`x=a::x',\ y=[]`$: 仮定 $`x\lt_{\textrm{lex}}y`$ が偽なので矛盾。
- $`x=a::x',\ y=b::y',\ z=[]`$: 仮定 $`y\lt_{\textrm{lex}}z`$ が偽なので矛盾。
- $`x=a::x',\ y=b::y',\ z=c::z'`$: 定義を展開すると仮定は $`a\lt b\lor(a=b\land x'\lt_{\textrm{lex}}y')`$ と $`b\lt c\lor(b=c\land y'\lt_{\textrm{lex}}z')`$、結論は $`a\lt c\lor(a=c\land x'\lt_{\textrm{lex}}z')`$ である。4 通りに分ける。
  - $`a\lt b`$ かつ $`b\lt c`$: $`\mathbb{N}`$ 上の $`\lt`$ の推移性で $`a\lt c`$。左の選言肢を取る。
  - $`a\lt b`$ かつ $`(b=c\land\cdots)`$: $`b=c`$ を $`a\lt b`$ に代入して $`a\lt c`$。左の選言肢を取る。
  - $`(a=b\land\cdots)`$ かつ $`b\lt c`$: $`a=b`$ を $`b\lt c`$ に代入して $`a\lt c`$。左の選言肢を取る。
  - $`(a=b\land x'\lt_{\textrm{lex}}y')`$ かつ $`(b=c\land y'\lt_{\textrm{lex}}z')`$: 等号の推移性で $`a=c`$、再帰の仮定を $`x'\lt_{\textrm{lex}}y'`$ と $`y'\lt_{\textrm{lex}}z'`$ に適用して $`x'\lt_{\textrm{lex}}z'`$。右の選言肢を取る。

#### 10. $`\lt_{\textrm{lex}}`$ の三分律

$`x,y`$ の 2 つの構造についての同時再帰。場合分けは 4 通り。

- $`x=[],\ y=[]`$: 真ん中の選言肢 $`x=y`$。
- $`x=[],\ y=b::y'`$: 定義より $`[]\lt_{\textrm{lex}}(b::y')`$ は真なので左の選言肢。
- $`x=a::x',\ y=[]`$: 定義より $`[]\lt_{\textrm{lex}}(a::x')`$ は真なので右の選言肢。
- $`x=a::x',\ y=b::y'`$: $`\mathbb{N}`$ 上の $`\lt`$ の三分律で $`a\lt b`$、$`a=b`$、$`b\lt a`$ に分ける。
  - $`a\lt b`$: 定義の左の選言肢から $`x\lt_{\textrm{lex}}y`$。
  - $`a=b`$: $`b`$ を $`a`$ に置き換えたうえで、再帰の仮定を $`x',y'`$ に適用する。$`x'\lt_{\textrm{lex}}y'`$ なら定義の右の選言肢（$`a=a`$ と合わせて）から $`x\lt_{\textrm{lex}}y`$。$`x'=y'`$ なら $`x=y`$。$`y'\lt_{\textrm{lex}}x'`$ なら同様に $`y\lt_{\textrm{lex}}x`$。
  - $`b\lt a`$: $`y\lt_{\textrm{lex}}x`$。

#### 1. $`\lt_{\textrm{PS}}`$ の非反射性

原文の系（辞書式的順序が辞書式順序であること）を $`M,M`$ に適用して、$`M\lt_{\textrm{PS}}M`$ を $`\bigoplus_\mathbb{N}M\lt_{\textrm{lex}}\bigoplus_\mathbb{N}M`$ に書き換え、8 を $`x=\bigoplus_\mathbb{N}M`$ に適用する。

#### 2. $`\lt_{\textrm{PS}}`$ の推移性

同じ系を $`(M,N)`$、$`(N,O)`$、$`(M,O)`$ の 3 箇所（仮定 2 つと結論）に適用して $`\lt_{\textrm{lex}}`$ の主張に直し、9 を $`x=\bigoplus_\mathbb{N}M`$、$`y=\bigoplus_\mathbb{N}N`$、$`z=\bigoplus_\mathbb{N}O`$ に適用する。

#### 11. 平坦化の単射性

$`M,N`$ の 2 つの構造についての同時再帰。

- $`M=[],\ N=[]`$: 結論は反射律。
- $`M=[],\ N=q::N'`$: 仮定は $`[]=q_0::q_1::\bigoplus_\mathbb{N}N'`$ であり、空列と非空列の等式なので矛盾。
- $`M=p::M',\ N=[]`$: 同様に矛盾。
- $`M=p::M',\ N=q::N'`$: 仮定は $`p_0::p_1::\bigoplus_\mathbb{N}M'=q_0::q_1::\bigoplus_\mathbb{N}N'`$。cons の単射性を 2 回使って $`p_0=q_0`$、$`p_1=q_1`$、$`\bigoplus_\mathbb{N}M'=\bigoplus_\mathbb{N}N'`$ を得る。第 3 のものに再帰の仮定を適用して $`M'=N'`$、前 2 つから対の外延性で $`p=q`$。よって $`p::M'=q::N'`$。

#### 3. $`\lt_{\textrm{PS}}`$ の三分律

10 を $`x=\bigoplus_\mathbb{N}M`$、$`y=\bigoplus_\mathbb{N}N`$ に適用して 3 つの場合に分ける。

- $`\bigoplus_\mathbb{N}M\lt_{\textrm{lex}}\bigoplus_\mathbb{N}N`$: 系（辞書式的順序が辞書式順序であること）の $`\Leftarrow`$ 向きで $`M\lt_{\textrm{PS}}N`$。
- $`\bigoplus_\mathbb{N}M=\bigoplus_\mathbb{N}N`$: 11 で $`M=N`$。
- $`\bigoplus_\mathbb{N}N\lt_{\textrm{lex}}\bigoplus_\mathbb{N}M`$: 同じ系を $`(N,M)`$ に適用して $`N\lt_{\textrm{PS}}M`$。

#### 4. $`\leq_{\textrm{PS}}`$ の全律

3 の 3 つの場合に分ける。$`M\lt_{\textrm{PS}}N`$ なら $`\leq_{\textrm{PS}}`$ の定義の右の選言肢で $`M\leq_{\textrm{PS}}N`$、$`M=N`$ なら左の選言肢で $`M\leq_{\textrm{PS}}N`$、$`N\lt_{\textrm{PS}}M`$ なら右の選言肢で $`N\leq_{\textrm{PS}}M`$。

#### 5. $`\leq_{\textrm{PS}}`$ の反射性

$`\leq_{\textrm{PS}}`$ の定義の左の選言肢 $`M=M`$ を取る。

#### 6. $`\leq_{\textrm{PS}}`$ の推移性

仮定 $`M\leq_{\textrm{PS}}N`$ を分解する。$`M=N`$ なら $`N\leq_{\textrm{PS}}O`$ がそのまま結論。$`M\lt_{\textrm{PS}}N`$ のとき、さらに $`N\leq_{\textrm{PS}}O`$ を分解して、$`N=O`$ なら $`M\lt_{\textrm{PS}}O`$ が仮定そのもの、$`N\lt_{\textrm{PS}}O`$ なら 2 で $`M\lt_{\textrm{PS}}O`$。いずれも右の選言肢を取る。

#### 7. $`\leq_{\textrm{PS}}`$ の反対称性

仮定 $`M\leq_{\textrm{PS}}N`$ を分解する。$`M=N`$ なら結論そのもの。$`M\lt_{\textrm{PS}}N`$ のとき、さらに $`N\leq_{\textrm{PS}}M`$ を分解して、$`N=M`$ なら結論そのもの、$`N\lt_{\textrm{PS}}M`$ なら 2 で $`M\lt_{\textrm{PS}}M`$ を得て、1 に反する。

#### 12. 共通接頭辞の消去

$`A`$ についての構造帰納法。

- $`A=[]`$: 両辺は $`B\lt_{\textrm{PS}}C`$ そのものなので、同値は反射律。
- $`A=p::A'`$: 左辺は $`(p::(A'\oplus_{\mathbb{N}^2}B))\lt_{\textrm{PS}}(p::(A'\oplus_{\mathbb{N}^2}C))`$ で、定義を展開すると
  $`p_0\lt p_0\ \lor\ (p_0=p_0\land p_1\lt p_1)\ \lor\ (p_0=p_0\land p_1=p_1\land (A'\oplus_{\mathbb{N}^2}B)\lt_{\textrm{PS}}(A'\oplus_{\mathbb{N}^2}C))`$
  となる。$`\lt`$ の非反射性で第 1・第 2 の選言肢が偽になり、自明な等号 $`p_0=p_0,\ p_1=p_1`$ が落ちて、左辺は $`(A'\oplus_{\mathbb{N}^2}B)\lt_{\textrm{PS}}(A'\oplus_{\mathbb{N}^2}C)`$ に等しい。帰納法の仮定を $`A'`$ に適用して $`B\lt_{\textrm{PS}}C`$ と同値。

#### 13. 真の接頭辞の小ささ

$`M`$ と $`k`$ についての再帰。

- $`M=[]`$: 仮定 $`k\lt\textrm{Lng}([])=0`$ が偽なので矛盾。
- $`M=p::M',\ k=0`$: 接頭辞は空列で、$`[]\lt_{\textrm{PS}}(p::M')`$ は定義より真。
- $`M=p::M',\ k=k'+1`$: 仮定 $`k'+1\lt\textrm{Lng}(M')+1`$ から $`k'\lt\textrm{Lng}(M')`$。長さ $`k'+1`$ の接頭辞は $`p::((M'_j)_{j=0}^{k'-1})`$ なので、示すべきは
  $`(p::(M'_j)_{j=0}^{k'-1})\lt_{\textrm{PS}}(p::M')`$
  である。12 と同じく定義を展開すると、$`\lt`$ の非反射性で第 1・第 2 の選言肢が消え、自明な等号が落ちて $`(M'_j)_{j=0}^{k'-1}\lt_{\textrm{PS}}M'`$ が残る。これは再帰の仮定である。

## 原文通りに書けなかった理由

- **[W]** 原文の $`\lt_{\textrm{PS}}`$ の再帰的定義には空列の場合が無く、系の主張範囲も $`T_{\textrm{PS}}`$ に限られている

  原文は $`\lt_{\textrm{PS}}`$ を $`T_{\textrm{PS}}^2`$ 上の関係として定めるが、第 3 条件の右辺 $`(M_i)_{i=1}^{\textrm{Lng}(M)-1}\lt_{\textrm{PS}}(N_i)_{i=1}^{\textrm{Lng}(N)-1}`$ は $`\textrm{Lng}(M)=1`$ のとき空列を左辺に持つので、再帰が $`T_{\textrm{PS}}`$ の外へ出る。つまり基底の場合が書かれていない。Lean は辞書式順序の規約（$`[]\lt_{\textrm{PS}}[]`$ は偽、$`[]\lt_{\textrm{PS}}(q::N)`$ は真、$`(p::M)\lt_{\textrm{PS}}[]`$ は偽）で補い、その結果として本系の 7 つの主張も空列を含む全体で成り立つので、$`T_{\textrm{PS}}`$ への制限を付けずに述べている。原文の主張はこれを $`T_{\textrm{PS}}`$ に制限したものである。

- **[W]** 原文は「数列の辞書式順序が狭義全順序であること」自体を証明せずに使っている

  原文の証明は「辞書式的順序が辞書式順序であることより即座に従う」の一行で、$`\lt_{\textrm{PS}}`$ が $`\lt_{\textrm{lex}}`$ に移ることしか述べていない。移した先の $`\lt_{\textrm{lex}}`$ が狭義全順序であることは既知として扱われている。Lean はこれを埋め、$`\mathbb{N}`$ の有限列上の $`\lt_{\textrm{lex}}`$ について非反射性・推移性・三分律を列の構造帰納法で証明している（上の 8・9・10）。推移性は 3 本の列の同時再帰で、うち 5 通りは片方の仮定が空列がらみで偽になる退化枝である。

- **[W]** 三分律の等号の場合には平坦化の単射性が要る

  原文が引く系（辞書式的順序が辞書式順序であること）は $`M\lt_{\textrm{PS}}N\iff\bigoplus_\mathbb{N}M\lt_{\textrm{lex}}\bigoplus_\mathbb{N}N`$ という不等号だけの同値で、$`\lt_{\textrm{lex}}`$ の三分律から出てくる中央の場合 $`\bigoplus_\mathbb{N}M=\bigoplus_\mathbb{N}N`$ を $`M=N`$ に戻す手段を与えない。Lean は $`\bigoplus_\mathbb{N}`$ の単射性（上の 11）を別に証明し、cons の単射性 2 回と対の外延性で $`p=q`$ を復元している。

- **[W]** 下流の命題（基本列の辞書式的縮小性）の証明が「明らかに」で飛ばす 2 つのリスト補題を、この節で補っている

  原文の当該証明は、$`M[n]=\textrm{Pred}(M)`$ の枝を「明らかに $`M[n]\lt_{\textrm{PS}}M`$ である」で済ませ、また
  $`M[n]=(M_j)_{j=0}^{j_1-1}\oplus_{\mathbb{N}^2}\bigl(\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}\bigr)`$ の形から
  「よって $`M[n]\lt_{\textrm{PS}}M`$ は $`\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}\lt_{\textrm{PS}}(M_{j_1})`$ と同値である」と述べる。前者は真の接頭辞が $`\lt_{\textrm{PS}}`$ で小さいこと、後者は共通接頭辞 $`(M_j)_{j=0}^{j_1-1}`$ を両辺から落とせることで、どちらも根拠が書かれていない。Lean はこの 2 つを本系と同じ節に置いて証明している（上の 12・13）。どちらも $`\lt_{\textrm{PS}}`$ の定義の展開と $`\lt`$ の非反射性による選言肢の消去で、リストの構造帰納法だけで済む。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| ペア列 | `PSS.PS`（`List (ℕ × ℕ)`） | `lean/PSS/Defs.lean` |
| $`T_{\textrm{PS}}`$ | `PSS.TPS`（空でないこと） | 同上 |
| $`\textrm{Lng}(M)`$ | `PSS.Lng` | 同上 |
| $`M\lt_{\textrm{PS}}N`$ | `ltPS M N` | `lean/Bijectivity/Defs.lean` |
| $`M\leq_{\textrm{PS}}N`$ | `lePS M N` | 同上 |
| $`\bigoplus_\mathbb{N}M`$ | `flatten M` | `lean/Bijectivity/01-lex-is-lexicographic.lean` |
| $`x\lt_{\textrm{lex}}y`$ | `ltLex x y` | 同上 |
| 系（辞書式的順序が辞書式順序であること） | `ltPS_iff_ltLex` | 同上 |
| 8. $`\lt_{\textrm{lex}}`$ の非反射性 | `ltLex_irrefl` | `lean/Bijectivity/02-lex-linear.lean` |
| 9. $`\lt_{\textrm{lex}}`$ の推移性 | `ltLex_trans` | 同上 |
| 10. $`\lt_{\textrm{lex}}`$ の三分律 | `ltLex_trichotomy` | 同上 |
| 1. $`\lt_{\textrm{PS}}`$ の非反射性 | `ltPS_irrefl` | 同上 |
| 2. $`\lt_{\textrm{PS}}`$ の推移性 | `ltPS_trans` | 同上 |
| 11. 平坦化の単射性 | `flatten_inj` | 同上 |
| 3. $`\lt_{\textrm{PS}}`$ の三分律 | `ltPS_trichotomy` | 同上 |
| 4. $`\leq_{\textrm{PS}}`$ の全律 | `lePS_total` | 同上 |
| 5. $`\leq_{\textrm{PS}}`$ の反射性 | `lePS_refl` | 同上 |
| 6. $`\leq_{\textrm{PS}}`$ の推移性 | `lePS_trans` | 同上 |
| 7. $`\leq_{\textrm{PS}}`$ の反対称性 | `lePS_antisymm` | 同上 |
| 12. 共通接頭辞の消去 | `ltPS_append_cancel` | `lean/Bijectivity/02b-lex-list-lemmas.lean` |
| 13. 真の接頭辞の小ささ | `ltPS_take` | 同上 |
| 命題（基本列の辞書式的縮小性） | `oper_ltPS` | `lean/Bijectivity/04-fseq-lex-decreasing.lean` |

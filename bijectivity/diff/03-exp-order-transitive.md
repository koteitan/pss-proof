[← back](README.md)

# 03: 命題 (基本列的順序が推移性)

## 原文

### 命題

命題 (基本列的順序が推移性)

$`\lt_{\textrm{PS}[]}`$ 及び $`\leq_{\textrm{PS}[]}`$ は推移律を満たす。

### 証明

  任意の $`M,N,O\in T_{\textrm{PS}}`$ を取り、$`M\leq_{\textrm{PS}[]}N`$ かつ $`N\leq_{\textrm{PS}[]}O`$ であるとする。

  $`\leq_{\textrm{PS}[]}`$ の定義より、ある $`a,b\in\mathbb{N}_+^{\lt\omega}`$ が存在して $`M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]`$ かつ $`N=O[b_0]\cdots[b_{\textrm{Lng}(b)-1}]`$ である。

  上より $`M=O[b_0]\cdots[b_{\textrm{Lng}(b)-1}][a_0]\cdots[a_{\textrm{Lng}(a)-1}]`$ であるから $`M\leq_{\textrm{PS}[]}O`$ である。

  従って $`\leq_{\textrm{PS}[]}`$ は推移律を満たす。また $`\lt_{\textrm{PS}[]}`$ の推移性も同様に導かれる。□

## Lean

### Lean での命題

以下、$`\oplus`$ は有限列の連結、$`()`$ は空列を表す。

**反復展開.** ペア数列 $`N`$ と $`\mathbb{N}`$ の有限列 $`a`$ に対して、反復展開 $`\mathrm{Ex}(N,a)`$ を $`a`$ に関する再帰で

```math
\mathrm{Ex}(N,())=N,\qquad \mathrm{Ex}(N,(n)\oplus a')=\mathrm{Ex}(N[n],a')
```

と定める。ここで $`N[n]`$ は原文 [1] の基本列である。展開すれば $`\mathrm{Ex}(N,a)=N[a_0][a_1]\cdots[a_{\textrm{Lng}(a)-1}]`$ であり、左の添字から先に適用する点で原文の $`N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]`$ と一致する。

**基本列的順序.** 原文が定義を与えていないので（後述）、証明本文の記述をそのまま定義に採る。

```math
M\leq_{\textrm{PS}[]}N \ :\Longleftrightarrow\ \exists a\in\mathbb{N}^{\lt\omega}\ \bigl((\forall n\in a,\ 1\leq n)\ \land\ M=\mathrm{Ex}(N,a)\bigr)
```

```math
M\lt_{\textrm{PS}[]}N \ :\Longleftrightarrow\ \exists a\ \bigl(a\neq()\ \land\ (\forall n\in a,\ 1\leq n)\ \land\ M=\mathrm{Ex}(N,a)\bigr)
```

このファイルが証明するのは次の 3 つである。

**(0) 連結補題**（原文に対応物なし）。任意のペア数列 $`N`$ と任意の $`\mathbb{N}`$ の有限列 $`a,b`$ に対して

```math
\mathrm{Ex}(N,b\oplus a)=\mathrm{Ex}(\mathrm{Ex}(N,b),a).
```

ここでは $`a,b`$ の成分に正値条件を課さない。

**(1)** 任意のペア数列 $`M,N,O`$ に対して、$`M\leq_{\textrm{PS}[]}N`$ かつ $`N\leq_{\textrm{PS}[]}O`$ ならば $`M\leq_{\textrm{PS}[]}O`$。

**(2)** 任意のペア数列 $`M,N,O`$ に対して、$`M\lt_{\textrm{PS}[]}N`$ かつ $`N\lt_{\textrm{PS}[]}O`$ ならば $`M\lt_{\textrm{PS}[]}O`$。

ここで「ペア数列」は $`\mathbb{N}\times\mathbb{N}`$ の有限列すべてを走り、空列も含む。すなわち原文の $`M,N,O\in T_{\textrm{PS}}`$（$`=`$ 空列でないこと）は仮定されていない。

### Lean での証明

**(0) 連結補題.** $`b`$ に関する構造帰納法。帰納法の仮定は $`N`$ について全称化しておく（$`N`$ を固定せずに帰納する）。

- $`b=()`$ の場合。左辺は $`()\oplus a=a`$ より $`\mathrm{Ex}(N,a)`$。右辺は $`\mathrm{Ex}(N,())=N`$ より $`\mathrm{Ex}(N,a)`$。定義の第 1 式だけで両辺が一致する。
- $`b=(n)\oplus b'`$ の場合。帰納法の仮定は「任意のペア数列 $`N`$ に対して $`\mathrm{Ex}(N,b'\oplus a)=\mathrm{Ex}(\mathrm{Ex}(N,b'),a)`$」である。

  $`\mathrm{Ex}(N,((n)\oplus b')\oplus a)=\mathrm{Ex}(N,(n)\oplus(b'\oplus a))=\mathrm{Ex}(N[n],b'\oplus a)`$

  （連結の結合律と定義の第 2 式）。ここで帰納法の仮定を $`N:=N[n]`$ に適用して

  $`\mathrm{Ex}(N[n],b'\oplus a)=\mathrm{Ex}(\mathrm{Ex}(N[n],b'),a)=\mathrm{Ex}(\mathrm{Ex}(N,(n)\oplus b'),a)`$

  （最後は定義の第 2 式を内側で逆向きに使った）。これが求める右辺である。

$`N`$ を全称化しておくのが要点で、帰納法の仮定を $`N`$ ではなく $`N[n]`$ に当てるために要る。

**(1) $`\leq_{\textrm{PS}[]}`$ 側.** 原文と同じく仮定を分解するところから始める。

$`M\leq_{\textrm{PS}[]}N`$ から、$`\mathbb{N}`$ の有限列 $`a`$ で「$`a`$ の全成分が $`1`$ 以上」かつ $`M=\mathrm{Ex}(N,a)`$ なるものを得る。この等式で $`M`$ を消去する。同様に $`N\leq_{\textrm{PS}[]}O`$ から $`b`$ を得て $`N=\mathrm{Ex}(O,b)`$ で $`N`$ を消去する。残る目標は

```math
\mathrm{Ex}(\mathrm{Ex}(O,b),a)\leq_{\textrm{PS}[]}O
```

である。$`\leq_{\textrm{PS}[]}`$ の定義の存在量化子に、証人として連結列 $`b\oplus a`$ を与える。原文が $`O[b_0]\cdots[b_{\textrm{Lng}(b)-1}][a_0]\cdots[a_{\textrm{Lng}(a)-1}]`$ と並べて書いたものが、この $`b\oplus a`$ にあたる。残る義務は 2 つ。

- 正値性。$`n\in b\oplus a`$ とすると、連結の元判定より $`n\in b`$ または $`n\in a`$ である。前者なら $`b`$ についての仮定から $`1\leq n`$、後者なら $`a`$ についての仮定から $`1\leq n`$。
- 等式 $`\mathrm{Ex}(\mathrm{Ex}(O,b),a)=\mathrm{Ex}(O,b\oplus a)`$。これは (0) を $`N:=O`$ に適用した等式の左右を入れ替えたものそのものである。

以上で $`\mathrm{Ex}(\mathrm{Ex}(O,b),a)\leq_{\textrm{PS}[]}O`$、すなわち $`M\leq_{\textrm{PS}[]}O`$。

**(2) $`\lt_{\textrm{PS}[]}`$ 側.** 原文が「同様に導かれる」で済ませた側を、独立の命題として書き下している。

$`M\lt_{\textrm{PS}[]}N`$ の分解で $`a\neq()`$、$`a`$ の全成分が $`1`$ 以上、$`M=\mathrm{Ex}(N,a)`$ を得て $`M`$ を消去する。$`N\lt_{\textrm{PS}[]}O`$ の分解で $`b\neq()`$、$`b`$ の全成分が $`1`$ 以上、$`N=\mathrm{Ex}(O,b)`$ を得て $`N`$ を消去する。目標は

```math
\mathrm{Ex}(\mathrm{Ex}(O,b),a)\lt_{\textrm{PS}[]}O
```

で、証人はやはり $`b\oplus a`$。義務は (1) より 1 つ多く 3 つ。

- 非空性。$`b\neq()`$ から $`b\oplus a\neq()`$（左が空でない連結は空でない）。ここで $`a\neq()`$ は使わない。
- 正値性。(1) と同じ 2 つの場合分け。
- 等式。(1) と同じく (0) の左右を入れ替えた形。

## 原文通りに書けなかった理由

- **[W]** $`\leq_{\textrm{PS}[]}`$ と $`\lt_{\textrm{PS}[]}`$ の定義が原文に書かれていない

  原文の表記節は $`\lt_{\textrm{PS}}`$ を再帰的に定め、$`\leq_{\textrm{PS}}`$ を $`M=N\lor M\lt_{\textrm{PS}}N`$ の略記とするだけで、$`\leq_{\textrm{PS}[]}`$ と $`\lt_{\textrm{PS}[]}`$ は定義されないまま使われる。定義に相当するのは、この命題の証明中の「$`\leq_{\textrm{PS}[]}`$ の定義より、ある $`a,b\in\mathbb{N}_+^{\lt\omega}`$ が存在して $`M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]`$」という一文と、後の命題（辞書式的順序が基本列的順序を含意すること）の証明にある「$`\lt_{\textrm{PS}[]}`$ の定義よりある $`a\in\mathbb{N}_+^{\lt\omega}\setminus\{()\}`$ が存在して」という一文の 2 箇所だけである。Lean はこの 2 文から定義を復元し、$`\leq`$ 側は添字列に長さの条件を課さず、$`\lt`$ 側は $`a\neq()`$ を課す形にした。

- **[R]** 原文の $`M,N,O\in T_{\textrm{PS}}`$ という制限を使っていない

  原文は「任意の $`M,N,O\in T_{\textrm{PS}}`$ を取り」から始めるが、Lean の 2 命題は $`\mathbb{N}\times\mathbb{N}`$ の有限列すべてについて述べられており、空列を除いていない。証明は反復展開の再帰と列の連結だけで進み、基本列 $`M[n]`$ の定義を一度も開かないので、$`T_{\textrm{PS}}`$ 所属（空列でないこと）はどこでも要らない。空列でも $`\textrm{Lng}(())-1=0`$ より $`()[n]=()`$ なので、この一般化した主張も真である。

- **[W]** 原文の「上より」が指数列の連結に関する帰納法を隠している

  原文は 2 つの等式を代入して $`M=O[b_0]\cdots[b_{\textrm{Lng}(b)-1}][a_0]\cdots[a_{\textrm{Lng}(a)-1}]`$ と書き、これを直ちに「ある $`\mathbb{N}_+^{\lt\omega}`$ の元に沿った $`O`$ の反復展開」と読んで $`M\leq_{\textrm{PS}[]}O`$ を結論する。しかし反復展開を添字列に関する再帰で定めると、この読み替えは $`\mathrm{Ex}(N,b\oplus a)=\mathrm{Ex}(\mathrm{Ex}(N,b),a)`$ という別命題であり、$`b`$ に関する帰納法（帰納法の仮定を $`N[n]`$ に当てるため $`N`$ を全称化した形）が要る。Lean はこれを独立の補題 (0) として切り出しており、原文に対応する記述は無い。

- **[S]** $`\mathbb{N}_+^{\lt\omega}`$ を「$`\mathbb{N}`$ の有限列＋全成分が $`1`$ 以上」という形で符号化している

  原文の添字列は $`\mathbb{N}_+`$ 上の有限列なので、連結 $`b\oplus a`$ が再び $`\mathbb{N}_+^{\lt\omega}`$ に属することは自動である。Lean は添字列を $`\mathbb{N}`$ の有限列とし、正値性を述語として横に付けているため、証人 $`b\oplus a`$ について正値性を改めて確認する一歩（$`n\in b\oplus a`$ を $`n\in b`$ と $`n\in a`$ に分ける場合分け）が (1)(2) の両方に入る。符号化された関係は原文の $`\leq_{\textrm{PS}[]}`$、$`\lt_{\textrm{PS}[]}`$ と同じものなので、命題の内容も、この 2 命題を使う下流の議論も変わらない。

- **[W]** 原文は $`\lt_{\textrm{PS}[]}`$ 側を「同様に導かれる」で済ませている

  Lean は $`\lt`$ 側を独立の命題として全部書き下している。$`\leq`$ 側との差は、証人 $`b\oplus a`$ が空でないことを示す一歩だけで、それは $`b\neq()`$ から従う。したがって $`\lt_{\textrm{PS}[]}`$ の定義が要求する $`a\neq()`$ のほうは、$`\lt`$ 側の証明で一度も使われない。

### lean との対応

| 数式 | Lean | ファイル |
|---|---|---|
| ペア数列（$`\mathbb{N}\times\mathbb{N}`$ の有限列） | `PSS.PS` | `lean/PSS/Defs.lean` |
| $`T_{\textrm{PS}}`$ | `PSS.TPS` | 同上 |
| $`\textrm{Lng}(M)`$ | `PSS.Lng` | 同上 |
| $`M[n]`$（基本列） | `PSS.oper M n` | 同上 |
| 反復展開 $`\mathrm{Ex}(N,a)`$ | `Bijectivity.expand` | `lean/Bijectivity/Defs.lean` |
| $`M\leq_{\textrm{PS}[]}N`$ | `Bijectivity.leExpPS` | 同上 |
| $`M\lt_{\textrm{PS}[]}N`$ | `Bijectivity.ltExpPS` | 同上 |
| (0) 連結補題 $`\mathrm{Ex}(N,b\oplus a)=\mathrm{Ex}(\mathrm{Ex}(N,b),a)`$ | `expand_append` | `lean/Bijectivity/03-exp-order-transitive.lean` |
| (1) $`\leq_{\textrm{PS}[]}`$ の推移律 | `leExpPS_trans` | 同上 |
| (2) $`\lt_{\textrm{PS}[]}`$ の推移律 | `ltExpPS_trans` | 同上 |
| 連結の元判定（$`n\in b\oplus a\Rightarrow n\in b\lor n\in a`$） | `List.mem_append` | Lean 標準ライブラリ |
| 左が空でない連結は空でない | `List.append_ne_nil_of_left_ne_nil` | Lean 標準ライブラリ |

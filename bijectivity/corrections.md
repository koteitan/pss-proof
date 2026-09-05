[← Back](README.md)

# 原文訂正案 (proposed corrections) — 全単射性の記事

Naruyoko「ペア数列システムの停止性証明に用いられた変換写像の全単射性」に対する訂正案を
集約する。著者へのフィードバック用。

- **対象記事**: Naruyoko「ペア数列システムの停止性証明に用いられた変換写像の全単射性」
  巨大数研究 Wiki ユーザーブログ, 2022.7.27.
  <https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Naruyoko/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%82%B7%E3%82%B9%E3%83%86%E3%83%A0%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7%E8%A8%BC%E6%98%8E%E3%81%AB%E7%94%A8%E3%81%84%E3%82%89%E3%82%8C%E3%81%9F%E5%A4%89%E6%8F%9B%E5%86%99%E5%83%8F%E3%81%AE%E5%85%A8%E5%8D%98%E5%B0%84%E6%80%A7>

訂正 id は `B1`, `B2`, … とする（元記事「ペア数列の停止性」への訂正案 `A1`〜 は
[`../corrections.md`](../corrections.md)）。

## B1. 命題（辞書式的順序が基本列的順序を含意すること）: $\textrm{Lng}(N)>1$ の仮定が要る

### 位置
命題（辞書式的順序が基本列的順序を含意すること）

### 原文
任意の\(M,N\in CT_{\textrm{PS}}\)に対して、\(M<_{\textrm{PS}[]}N\)ならば\(M<_{\textrm{PS}}N\)である。

### 訂正案
任意の\(M,N\in CT_{\textrm{PS}}\)に対して、\(\textrm{Lng}(N)>1\)かつ\(M<_{\textrm{PS}[]}N\)ならば\(M<_{\textrm{PS}}N\)である。

### 原文の問題点
原文は $<_{\textrm{PS}[]}$ を「$a\neq()$ なる $a\in\mathbb{N}_+^{<\omega}$ が存在して
$M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]$」と定義しているが、この定義は $M\neq N$ を
含意しない。$\textrm{Lng}(N)=1$ のとき $N[n]=N$ だからである。

- 反例: $N=((0,0))\in CT_{\textrm{PS}}$、$a=(1)$。
  - $\textrm{Lng}(N)=1$ より $N[1]=N$ なので $M=N[1]=N=((0,0))$。
  - $M<_{\textrm{PS}[]}N$ は（$a=(1)\neq()$ なので）成り立つ。
  - しかし $M=N$ なので $M<_{\textrm{PS}}N$ は偽。
- 原文の証明は「$M=N$ とすると条件と反する」とするが、それは上記の定義からは従わない。
- $\textrm{Lng}(N)>1$ を補えば原文の証明がそのまま通る。

### 形式化
`bijectivity/lean/Bijectivity/05-exp-implies-lex.lean` の `ltExpPS_ltPS_of_lng`
（訂正形、証明済み）。逐語形 `ltExpPS_ltPS` は `sorry` のまま残してある。

## B2. 補題（標準形の始切片への経路）: 結論は $\leq_{\textrm{PS}[]}$

### 位置
補題（標準形の始切片への経路）

### 原文
任意の\(M\in ST_{\textrm{PS}}\)と\(j_1'\in\mathbb{N}\)に対し、\(j_1=\textrm{Lng}(M)-1\)と置くと、\(j_1'\leq j_1\)ならば\((M_j)_{j=0}^{j_1'}<_{\textrm{PS}[]}M\)である。

### 訂正案
任意の\(M\in ST_{\textrm{PS}}\)と\(j_1'\in\mathbb{N}\)に対し、\(j_1=\textrm{Lng}(M)-1\)と置くと、\(j_1'\leq j_1\)ならば\((M_j)_{j=0}^{j_1'}\leq_{\textrm{PS}[]}M\)である。

### 原文の問題点
$j_1'=j_1$ のとき $(M_j)_{j=0}^{j_1'}=M$ なので、原文の結論は $M<_{\textrm{PS}[]}M$ を
主張することになる。$\textrm{Lng}(M)>1$ ではこれは偽である（$M[1]=\textrm{Pred}(M)\neq M$
であり、以降どれだけ展開しても $M$ には戻らない）。

原文自身、後の 命題（基本列的順序が辞書式的順序を含意すること）の証明では、この補題を
$((j,j))_{j=0}^{v^M}\leq_{\textrm{PS}[]}((j,j))_{j=0}^v$ と $\leq$ で用いている。
よって結論を $\leq_{\textrm{PS}[]}$ とするのが正しい。狭義にしたい場合は仮定を
$j_1'<j_1$ とする。

### 形式化
`bijectivity/lean/Bijectivity/11-path-to-initial-segment.lean` の `seg_leExpPS`
（訂正形、証明済み）。逐語形 `seg_ltExpPS_verbatim` は `sorry` のまま残してある。

## B3. 命題（基本列的順序が辞書式的順序を含意すること）: 内側の帰納法に基底段階が無い

### 位置
命題（基本列的順序が辞書式的順序を含意すること）の証明、
「\(\textrm{Lng}(N)\)及び\((N_j)_{j=0}^{j_1^N-1}\)を固定したときの帰納法により」の箇所

### 原文
従って\(\textrm{Lng}(M')=\textrm{Lng}(N)\)かつ\((M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}\)である\(M'\in CT_{\textrm{PS}}\)は高々\((j_1^N)^2\)個である。

（…中略…）\(\textrm{Lng}(N)\)及び\((N_j)_{j=0}^{j_1^N-1}\)を固定したときの帰納法により、任意の\(N'\in CT_{\textrm{PS}}\)に対して、\(N\leq_{\textrm{PS}}N'\)ならば\(M<_{\textrm{PS}[]}N'\)である。

### 訂正案
[1] の簡約性と係数の関係、条件(A)と(B)と係数の基本性質(1)及び(2)、標準形の簡約性及び\(CT_{\textrm{PS}}\)の定義より任意の\(M'\in CT_{\textrm{PS}}\)と非負整数\(j<\textrm{Lng}(M')\)に対して\(M'_{1,j}\leq M'_{0,j}\leq j\)である。

従って\(\textrm{Lng}(M')\leq L\)である\(M'\in CT_{\textrm{PS}}\)は有限個である。

（…中略…）\(L=\textrm{Lng}(M)\)と置いて\(\{M'\in CT_{\textrm{PS}}\mid\textrm{Lng}(M')\leq L\}\)上の\(<_{\textrm{PS}}\)に関する下降帰納法により、任意の\(N'\in CT_{\textrm{PS}}\)に対して、\(N\leq_{\textrm{PS}}N'\)ならば\(M<_{\textrm{PS}[]}N'\)である。

### 原文の問題点
原文の内側の帰納法は
$S=\{M'\in CT_{\textrm{PS}}\mid\textrm{Lng}(M')=\textrm{Lng}(N)\land(M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}\}$
という有限集合の上での $<_{\textrm{PS}}$ に関する**下降**帰納である。実際、証明の各段は
$N$ について結論が既知であるとして、$S$ の中で $N$ の直下にある $M'$ について結論を導いている。

しかし下降帰納には $S$ の $<_{\textrm{PS}}$-最大元での基底段階が要る。最大元 $X$ では
$X$ より上の元が $S$ に無いので帰納法の仮定が使えないが、結論
「任意の $N'\in CT_{\textrm{PS}}$ に対して $X<_{\textrm{PS}}N'$ ならば
$X<_{\textrm{PS}[]}N'$」は自明ではない（$N'$ は $S$ の外を動く）。原文はこの段階を扱っていない。

### 修正の要点
帰納の台を「長さと先頭 $j_1^N$ 項を固定した集合」から
$\{M'\in CT_{\textrm{PS}}\mid\textrm{Lng}(M')\leq L\}$ に取り替えればよい。

- この集合も有限である。原文が引く係数評価 $M'_{1,j}\leq M'_{0,j}\leq j$ が
  各添字 $j$ で成り立つので、長さ $L$ 以下の元は高々 $\prod_{j<L}(j+1)^2$ 個。
- 相手 $N'$ の長さは、原文の $f$ による帰着（$N'$ を $(N'_j)_{j=0}^f$ に置き換える操作）
  で $\textrm{Lng}(M)$ 以下に落とせるので、帰納の台の外に出ない。
- この台なら最大元 $X$ では $X<_{\textrm{PS}}N'$ なる $N'$ が台の中に存在しないため、
  主張が空虚に成り立ち、基底段階が自動的に閉じる。

それ以外の論法（$f$ による場合分け、共通の上界 $((j,j))_{j=0}^v$ の導入、$g_0$ の最小性、
$N=N'$ の導出）は原文のままでよい。

### 形式化
`bijectivity/lean/Bijectivity/12-lex-implies-exp.lean`（訂正形で証明済み）。
有限性は `12b-ctps-finite.lean` の `ctps_finite`、主要部は `12c-big-step.lean` の
`big_step`。

# 原文訂正案 (proposed corrections)

巨大数研究 Wiki の記事 **「ペア数列の停止性」**(P進大好きbot 著) に対する訂正案を
集約する。著者へのフィードバック用。

- **対象記事**: P進大好きbot「ペア数列の停止性」巨大数研究 Wiki ユーザーブログ, 2018.11.11.
  <https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7>
- **各訂正の特定方法**: 記事の**節 (§) と命題名**（「命題（…）」）および**訂正対象の本文を
  逐語引用**することで、公開記事中で直接特定できるようにする。
- 原文は HTML（内部の LaTeX ソース）なので、訂正は HTML 内 LaTeX 記述への修正として記す。
- 形式化（Isabelle）側でどう扱ったかも併記する。
- 数式は MathJax 記法（`$...$` / `$$...$$`）で書く。

---

## A1. §5.4 命題（$F_M$ と基本列の関係）: 再帰先の第2引数 $n$ → $f(n)$ [軽微]

### 位置
§5.4 ペア数列システム / 命題（$F_M$ と基本列の関係）（該当数式 $F_M(n) = F_{M[n]}(n)$）

### 原文
- (2) $(M[n],n) \in \textrm{Dom}(F)$
- (3) $(M,n) \in \textrm{Dom}(F)$ かつ $(M[n],n) \in \textrm{Dom}(F)$ かつ $F_M(n) = F_{M[n]}(n)$

### 訂正案
$\textrm{Lng}(M) = 1$ のとき:
- (2) $(M[n],n) \in \textrm{Dom}(F)$
- (3) $(M,n) \in \textrm{Dom}(F)$ かつ $(M[n],n) \in \textrm{Dom}(F)$ かつ $F_M(n) = F_{M[n]}(n)$

$\textrm{Lng}(M) > 1$ のとき:
- (2) $(M[n],f(n)) \in \textrm{Dom}(F)$
- (3) $(M,n) \in \textrm{Dom}(F)$ かつ $(M[n],f(n)) \in \textrm{Dom}(F)$ かつ $F_M(n) = F_{M[n]}(f(n))$

### 原文の問題点
§5.4 の $F$ の再帰的定義は

$$F_M(n) := F_{M[n]}(f(n))$$

と、再帰先の第2引数が $f(n)$。命題は同じ $n$ を使っており定義と矛盾する。

- 反例: $M = ((0,0),(0,0))$, $f(n)=n+1$, $n=1$。
  - 定義: $F_M(1) = F_{M[1]}(f(1)) = F_{((0,0))}(2) = f(2) = 3$。
  - 命題: $F_M(1) = F_{M[1]}(1) = F_{((0,0))}(1) = f(1) = 2$。
  - よって $3 \neq 2$ で矛盾。
- 補足: $\textrm{Lng}(M)=1$ のときは $M[n]=M$, $F_M(n)=f(n)=F_{M[n]}(n)$ なので原文の
  $n$ が正しい。$\textrm{Lng}(M)>1$ のときに $f(n)$ でなければならない。**単一の固定
  引数では両ケースを両立できない。**

### 形式化での扱い
**証明成功**。 修正: 命題の第2引数を $n\to f(n)$ に直し、前提に $\textrm{Lng}\,M>1$ を追加。

`pss_paper.thy` の `p_5_4_F_oper_dom` / `p_5_4_F_oper_val` を訂正版
（$\textrm{Lng}\,M > 1$, 第2引数 $f\,n$）で記述し、`pss_mechanized.thy` の
`m_5_4_*` で証明済み。

## A2. §6.6 系（直系先祖による切片と $\textrm{Red}$ と $\textrm{IncrFirst}$ の関係）: 指数の添字 $m$ → $j'_0$ [軽微]

### 位置
§6.6 簡約性 / 系（直系先祖による切片と $\textrm{Red}$ と $\textrm{IncrFirst}$ の関係）

### 原文
$(M_j)_{j=j'_0}^{j'_1} = \textrm{IncrFirst}^{M_{0,m} - M_{1,m}}(N)$

### 訂正案
$(M_j)_{j=j'_0}^{j'_1} = \textrm{IncrFirst}^{M_{0,j'_0} - M_{1,j'_0}}(N)$

### 原文の問題点
ステートメント中の指数 $M_{0,m} - M_{1,m}$ に現れる添字 $m$ は、この系では
未定義（$m$ はこの命題のスコープに導入されていない）。証明本体では一貫して
$M_{0,j'_0} - M_{1,j'_0}$ を用いており、$m$ は $j'_0$ の誤記と判断される。

### 形式化での扱い
**証明成功**。 修正: 指数の添字を $m\to j'_0$（$\textrm{entry}\,M\,0\,j'_0-\textrm{entry}\,M\,1\,j'_0$）に直す。 （`m_6_6_ancestor_slice_Red_IncrFirst`・green、§6.6 ✅、§7/§8 で多用）。

`pss_paper.thy` の `p_6_6_ancestor_slice_Red_IncrFirst` を訂正版
（指数 $\textrm{entry}\,M\,0\,j'_0 - \textrm{entry}\,M\,1\,j'_0$）で記述。

## A3. §6.4 系（$\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性）(4): 偽（反例あり）

### 位置
§6.4 幹と枝 / 系（$\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性）の主張 (4)

### 原文
(4) 任意の $i \in \{0,1\}$ に対し $M_{i,\textrm{Joints}(M)_{J'_0}} > M_{i,\textrm{Joints}(M)_{J'_1}}$ である。

### 訂正案
(4) を削除。

### 原文の問題点
(4) は狭義不等号だが、複数の枝が同一の joint に接続し得るため偽。反例:

$$M = (0,0)(1,1)(2,1)(3,1)(2,0)$$

- $\textrm{TrMax}(M) = 1$、$\textrm{Br}(M) = [\,(2,1)(3,1),\ (2,0)\,]$
- $\textrm{FirstNodes}(M) = [2,4]$、$\textrm{Joints}(M) = [1,1]$
- $J'_0=0 < J'_1=1$ で $M_{i,\textrm{Joints}_0} = M_{i,\textrm{Joints}_1} = M_{i,1}$ なので (4) ($1>1$) は偽。

この $M$ は標準形・単項・簡約・$\textrm{Br}$ 降順（機械的に確認）。(3) は弱い不等号 ($\geq$) のため
(4) の狭義性は従わない。(4) は本文で未使用（下流は (2) の $\geq$、$\textrm{Joints}_J \leq \textrm{TrMax} < \textrm{FirstNodes}_J$、
条件(A) $M_{0,\textrm{Joints}_J}+1 = M_{0,\textrm{FirstNodes}_J}$、$\textrm{Br}$ 降順のみを用いる）。

### 形式化での扱い
**証明成功**。 修正: 偽の (4) を除き、命題を (1)(2)(3) のみに弱める。

`pss_paper.thy` の `p_6_4_FirstNodes_Joints_mono` を (1)(2)(3) のみに弱め、
`m_6_4_FirstNodes_Joints_mono`（= 既証明 `m_6_4_FirstNodes_Joints_mono_aux`）で discharge。

## A4. §6.5 系（直系先祖の $\textrm{Red}$ 不変性）ほか: 前提 $M \in T_{\textrm{PS}}$ は広すぎる（反例あり）

### 位置
§6.5 簡約化 — 系（直系先祖の $\textrm{Red}$ 不変性）・（$\textrm{Red}$ が単項性を保つこと）・
（$P$ の $\textrm{Red}$ 同変性）・（$\textrm{Red}$ と基本列の可換性）・（$\textrm{Red}$ が許容性を保つこと）など、
いずれも前提「任意の $M \in T_{\textrm{PS}}$」

### 原文
系（直系先祖の $\textrm{Red}$ 不変性）: 任意の $M \in T_{\textrm{PS}}$ に対し、$\leq_M$ と
$\leq_{\textrm{Red}(M)}$ は一致する。

### 訂正案
系（直系先祖の $\textrm{Red}$ 不変性）: $S \in \textrm{ST}_{\textrm{PS}}$（または $S \in \textrm{RT}_{\textrm{PS}} \cap \textrm{PT}_{\textrm{PS}}$）と $a \le b$, $(0,a) \le_S (0,b)$ に対する $M = (S_j)_{j=a}^{b}$ に限り、$\leq_M$ と $\leq_{\textrm{Red}(M)}$ は一致する。

### 原文の問題点
$T_{\textrm{PS}}$ 全体では偽。反例:

$$M = (0,0)(0,1)$$

- $M$ は複項。$P(M) = [\,(0,0),\ (0,1)\,]$。
- $\textrm{Red}((0,0)) = (0,0)$、$\textrm{Red}((0,1)) = (1,1)$（単項 $m_{1,0}=1>0$ 枝）。
  よって $\textrm{Red}(M) = (0,0)(1,1)$。
- $(0,0) \leq_M (0,1)$ は偽（$M_{0,0} < M_{0,1}$ すなわち $0<0$ が不成立）だが
  $(0,0) \leq_{\textrm{Red}(M)} (0,1)$ は真（$0<1$）。よって不変性は偽。

同じ $M$ で以下も偽:
- 系（$\textrm{Red}$ が単項性を保つこと）: $M$ は複項だが $\textrm{Red}(M)=(0,0)(1,1)$ は単項。
- 系（$P$ の $\textrm{Red}$ 同変性）: $P(\textrm{Red}(M)) = [\,(0,0)(1,1)\,]$ だが
  $(\textrm{Red}(P(M)_J))_J = [\,(0,0),\ (1,1)\,]$。
- 命題（$\textrm{Red}$ と基本列の可換性）: $\textrm{Red}(M)[2] = (0,0)(1,0) \neq (0,0) = \textrm{Red}(M[2])$。

原因: 複項 $M$ に対する $\textrm{Red}(M) = \bigoplus(\textrm{Red}(P(M)_J))$ は各 $P$ ブロックを
正規化（$\textrm{IncrFirst}$ で持ち上げ）して連結するため、元の $M$ に無かった $\leq$ 関係を
生じ得る。これは $M$ が標準形でないとき起こる（反例 $M$ は非標準。各 $P$ ブロック $(0,1)$ も非標準）。

また、証明「$\textrm{Lng}(M)$ に関する数学的帰納法から即座に従う」も成立しない:
命題は $\textrm{Lng}(M)=2$ の時点で偽（上記反例）なので、無仮定の $\textrm{Lng}$ 帰納は
原理的に閉じない。

$T_{\textrm{PS}}$ 全体で偽な系（**8 系**、経験的調査・忠実モデル+yaBMS で確定、`docs/red-le-domain.md`）:
**直系先祖の $\textrm{Red}$ 不変性**、**$\textrm{Red}$ が単項性を保つこと**、**$P$ の $\textrm{Red}$ 同変性**、
**$\textrm{Red}$ の冪等性**（反例 $(0,0)(0,2)$）、**$\textrm{Red}$ と基本列の可換性**、
**$\textrm{Red}$ が許容性を保つこと**（反例 $(0,0)(0,1)(0,2)$）、**許容化の $\textrm{Red}$ 不変性**（同）、
**$\textrm{Red}$ が基点を保つこと**（反例 $(0,0)(0,1)(1,2)$）。
一方 $\textrm{Lng}$ の $\textrm{Red}$ 不変性・$\textrm{Red}$ が零項性を保つこと・$\textrm{Red}$ と $\textrm{Pred}$ の
可換性・$\textrm{Red}$ の $\textrm{IncrFirst}$ 不変性は $T_{\textrm{PS}}$ 全体で真。
上記 8 系はいずれも**先祖係留切片**（下記）上では成立（`python/red_anchor2.py`/`red_adm_audit.py`、失敗 0）。

### 補足: 命題（$\textrm{Red}$ と基本列の可換性）のシフト分岐の証明について（補強のご提案）
> 以下は形式化を進める中で気づいた点で、私たちの理解の範囲での指摘です。主張自体（標準形に
> 制限したもの）は経験的に成立を確認しており、証明の運びに一段の補強を提案するものです。

シフト分岐 $(1,0) <_M^{\textrm{Next}} (1,j_1)$ を「$\textrm{Red}$ と $\textrm{Pred}$ の可換性と $B$ の
定義から $n$ に関する数学的帰納法により従う」とある箇所について、この帰納法を閉じるには、
引用されている事実に加えてもう一段の事実が要るように見える。

簡約 $M$（$\textrm{Red}(M)=M$）の場合、結論 $\textrm{Red}(M)[n]=\textrm{Red}(M[n])$ は
$M[n]=\textrm{Red}(M[n])$、すなわち「$M[n]$ が簡約である」と同値になる。$M[n{+}1]$ は $M[n]$ に
1ブロック $B_n$（$w:=j_1-j_0$ 要素）を連結した形 $M[n{+}1]=M[n]\,@\,B_n$ なので、
$\textrm{Pred}^w(M[n{+}1])=M[n]$ より $\textrm{Red}$-$\textrm{Pred}$ 可換性を $w$ 回用いると
$$\textrm{Pred}^w(\textrm{Red}(M[n{+}1]))=\textrm{Red}(M[n])$$
が得られる。これは $\textrm{Red}(M[n{+}1])$ の**接頭辞（末尾 $w$ 要素を除く部分）が
$\textrm{Red}(M[n])$ に一致する**ことを与えるが、末尾ブロック $B_n$ が簡約形であること
（$=M[n{+}1]$ の最終ブロックへの命題（簡約性と係数の関係）の $\textrm{RedCondA}/\textrm{RedCondB}$ の
適用）は $\textrm{Red}$-$\textrm{Pred}$ 可換性（末尾を1要素ずつ削る後方向の操作）からは出ず、
別途の議論を要するように思われる。

なお標準形 $M$ では $M[n]\in\textrm{ST}_{\textrm{PS}}$ なので、この「$M[n]$ が簡約」は本節の主目標
（標準形の簡約性 $\textrm{ST}_{\textrm{PS}}\subseteq\textrm{RT}_{\textrm{PS}}$）と実質同一であり、上記の
追加事実は標準形固有の構造（$\textrm{row-1}$ の親構造 $\Rightarrow$ $\textrm{row-0}$ が $+1$ ランプ）に
帰着する。私たちの形式化ではこの末尾ブロック簡約性を経験的に確認している（広い標準形閉包で
反例 0）が、その形式証明は現状では未完であり、本節の核心になっている。**ご提案**として、
シフト分岐に「タイリングの末尾ブロックが簡約であること」を補題として明示し、その論証を補えば、
帰納法が閉じると思われる（同時に、A4 の定義域の論点—$T_{\textrm{PS}}$ 全域では命題が偽—も、
この補題が標準形でのみ成り立つことと整合する）。

### 形式化での扱い
**証明成功**。 修正: 前提 $M\in T_{\textrm{PS}}$ を anchored 係留切片の補正域に制限する。 §6.5 系（直系先祖の Red 不変性）は anchored 係留切片の補正域のもと `m_6_5_Red_le_final` 等として無条件完結（[[A10]] で循環解消、§6.5 全項 green）。docs `red-le-domain.md`。

当面は補正済み定義域（先祖係留切片）で言明のみ（`sorry`）とし、8系を同様に制限する。
証明は本プロジェクト最難（論文の一行 $\textrm{Lng}$ 帰納は $\textrm{Lng}=2$ で偽となり不成立）。
定義域の最終的な形・閉性・全 use-site の確認は **保留中**。詳細は `docs/red-le-domain.md`。

## A5. §6.6 命題（簡約性の切片への遺伝性）: 前提 $j'_0 \le \textrm{TrMax}(M)$ は弱すぎる（反例あり）

### 位置
§6.6 簡約性 / 命題（簡約性の切片への遺伝性）

### 原文
任意の $M \in RT_{\textrm{PS}}$ に対し、$j_1 := \textrm{Lng}(M)-1$ と置くと、任意の
$j'_0,j'_1 \in \mathbb{N}$ に対し $j'_0 \le \textrm{TrMax}(M) \le j'_1 \le j_1$ ならば
$(M_j)_{j=j'_0}^{j'_1}$ は簡約である。

### 訂正案
任意の $M \in RT_{\textrm{PS}}$ に対し、$j_1 := \textrm{Lng}(M)-1$ と置くと、任意の $j'_1 \in \mathbb{N}$ に対し $\textrm{TrMax}(M) \le j'_1 \le j_1$ ならば $(M_j)_{j=0}^{j'_1}$ は簡約である。

### 原文の問題点
前提 $j'_0 \le \textrm{TrMax}(M)$ が弱すぎ、$T_{\textrm{PS}}$（標準形に限っても）で偽。反例:

$$M = (0,0)(1,1)(1,0)$$

- $M$ は標準形（yaBMS で確認）かつ簡約（$\textrm{Red}(M)=M$）、$\textrm{TrMax}(M)=1$。
- $j'_0=1=\textrm{TrMax}(M) \le j'_1=2 \le j_1=2$ をとると $(M_j)_{j=1}^{2} = (1,1)(1,0)$。
- $\textrm{Red}((1,1)(1,0)) = (1,1)(0,0) \neq (1,1)(1,0)$ なので切片は簡約でない。

原因: $j'_0 = \textrm{TrMax}$ だと幹の根（index 0）を落とした切片になり、切片の幹構造が変わる。
証明「$\textrm{Red}$ の再帰的定義と $\textrm{Red}$ と $\textrm{Pred}$ の可換性より即座」も、
$\textrm{Red}$ と $\textrm{Pred}$ の可換性は真だが、それだけでは従わない。

### 形式化での扱い
**証明成功**。 修正: 前提 $j'_0\le\textrm{TrMax}(M)$ を（暫定）$j'_0=0$ に制限する。 （補正形 `herd_6_6_reduced_slice`($j'_0=0$)・green、§6.6 ✅）。

`pss_paper.thy` の `p_6_6_reduced_slice` の前提を補正（暫定 $j'_0=0$）。`reduced_oper`・
`P_reduced`・`reduced_iff_cond`（簡約 ⟺ 条件A∧B）・`Red_leftend_1` は $T_{\textrm{PS}}$ 全体で真。

## A6. §6.7 命題（標準形の単項成分が標準形であること）: 証明が依拠する単調性補題 $S_{k-1}\subseteq S_k$ の省略

### 位置
§6.7 / 命題（標準形の単項成分が標準形であること）の証明末尾 case
（$\textrm{Lng}(P(M')_{J_0}) > 1$）

### 原文
任意の $k \in \mathbb{N}$ と $M \in S_kT_{\textrm{PS}}$ に対し、$P(M) \in S_kT_{\textrm{PS}}^{<\omega}$ である。

### 訂正案
補題（標準形の階層の単調性）: $S_{k-1}T_{\textrm{PS}} \subseteq S_kT_{\textrm{PS}}$。

### 原文の問題点
（命題そのものは**真**。忠実モデルで $k \le 5$・計 3000+ 要素まで違反 0。訂正不要。）

> $(P(M')_J)_{J=0}^{J_0-1} \in S_{k_0-1}T_{\textrm{PS}}^{<\omega}$ であり、$P(M')_{J_0} \in S_{k_0-1}T_{\textrm{PS}}$
> より帰納法の仮定から $P(P(M')_{J_0}[n]) \in S_{k_0-1}T_{\textrm{PS}}^{<\omega}$ であるので、
> $P(M) \in S_{k_0-1}T_{\textrm{PS}}^{<\omega}$ である。

**帰納法の仮定が与えるのは $S_{k-1}$ どまりで、命題の結論は $S_k$** である（ここで $S_{k_0-1}$ の
$k_0$ は帰納変数であり、設定の $k$ と同一視してよい — 変数名の差であって問題ではない）。先頭部分
$(P(M')_J)_{J<J_0}$ は $P(M')$ の成分なので帰納法の仮定で $\in S_{k-1}$。これを目標の $S_k$ に上げるには
**$S_{k-1} \subseteq S_k$（階層の単調性）が要る**が、原文はこの補題を**明示も証明もしていない**（暗黙に使っている）。

### 単調性 $S_{k-1}\subseteq S_k$ は真
証人（base）: 任意の $u \le v$ に対し
$$\textrm{diagSeq}(u,v) = \textrm{Pred}(\textrm{diagSeq}(u,v{+}1)) = (\textrm{diagSeq}(u,v{+}1))[1],\quad \textrm{diagSeq}(u,v{+}1)\in S_0,$$
ゆえ $\textrm{diagSeq}(u,v)\in S_1$。一般の $k$ は帰納で（$N\in S_k \Rightarrow N\in S_{k+1}$ なら $N[n]\in S_{k+2}$）。
したがって $S_k \subseteq S_{k+1}$。（`pss_mechanized.thy: SkT_PS_mono`、`Pred (diagSeq u (Suc v)) = diagSeq u v`
＋`m_5_3_pred_is_oper1: Pred M = M[1]`。）

### 結論：原文証明は本質的に正しく、不足は「単調性補題 $S_{k-1}\subseteq S_k$」のみ
単調性さえ補えば、先頭部分（$\in S_{k-1}\subseteq S_k$）も末尾（$P(M')_{J_0}\in S_{k-1}\subseteq S_k \Rightarrow P(M')_{J_0}[n]\in S_{k+1}$…
実際は $S_k$ 上の構造帰納）も $S_k$ に収まり、結論 $P(M)\in S_k$ が出る。

### 形式化での扱い
**証明成功**。 修正: 原文が省略した単調性補題 $S_{k-1}\subseteq S_k$ を補完して証明する。 `m_6_7_standard_P_components`（`SkT_PS_mono` + k×Lng 辞書式帰納）として証明済・green。

`SkT_PS_mono`（済）を用いて `pss_paper.thy` の `p_6_7_standard_P_components`（同ランク $S_k$）を、
$k$ × $\textrm{Lng}$ の辞書式帰納で証明する（先頭は単調性、末尾は $\textrm{Lng}$ 減少の内側帰納）。詳細は
`docs/standard-P-components.md`。

## A7. §6.8 命題（標準形の切片と Br の降順性の関係）: 「M' が標準形となる」は偽（示すべきは「Br(M') が降順」）

### 位置
§6.8「降順性」, 命題（標準形の切片と $\textrm{Br}$ の降順性の関係）の証明本体
（単項性を示した直後、$k_0$ 帰納を宣言する一文）。

### 原文
> $M$ が単項であるという条件下で**$M'$ が標準形となること**を $k_0$ に関する数学的帰納法で示す。

### 訂正案
$M$ が単項であるという条件下で $\textrm{Br}(M')$ が降順となることを $k_0$ に関する数学的帰納法で示す。

### 原文の問題点
この一文は帰納法で示す対象を「$M'$ が標準形（$\in ST_{\textrm{PS}}$）」と述べているが、

- 命題の結論は「$M'$ は単項かつ $\textrm{Br}(M')$ は降順」であって「$M'$ が標準形」ではない。
- 続く base / 各ケースは一貫して「$\textrm{Br}(M')$ は降順である」を結論しており、「$M'$ が標準形」は一度も使われない。
- 実際 $M'$ は標準形とは限らない。**反例（$M$ が単項標準形でも）**: $M = (0,0)(1,1)(2,0) \in ST_{\textrm{PS}}$,
  $j'_0=1,\ j'_1=2$, $(0,1)\le_M(0,2)$ のとき $M' = (1,1)(2,0) \notin ST_{\textrm{PS}}$。

### 形式化での扱い
**証明成功**。 修正: 結論を「$M'$ が標準形」から「$\textrm{Br}(M')$ が降順」に直す。 §6.8 `m_6_8_standard_slice_Br_descending`（行0=`m_6_4_P_leftend_mono`、行1 tie-break も完了）として証明済・green。docs `slice-Br-descending.md`。
（`m_6_4_P_leftend_mono` を枝セグメント $\in T_{\textrm{PS}}$ に適用）は確保済。残るは Br 成分の行1 tie-break
（$k$ 帰納＋Br-under-oper、設計 `docs/slice-Br-descending.md`）。

## A8. §6.8 命題（標準形の切片と Br の降順性の関係）: 展開後の末尾添字 j_1 の式の off-by-one [軽微]

### 位置
§6.8「降順性」, 命題（標準形の切片と Br の降順性の関係）の証明本体、
$N_{1,j_1^N}=0$ の場合の冒頭（$M$ をブロック分解する一文）。

### 原文
> $M = (N_j)_{j=0}^{j_0^N-1} \bigoplus_{\mathbb{N}^2} ((N_j)_{j=j_0^N}^{j_1^N-1})_{k=0}^{n-1}$ であり、
> $j_1 = j_0^N+(n+1)(j_1^N-j_0^N)-1$ である。

### 訂正案
$j_1 = j_0^N + n(j_1^N-j_0^N) - 1$

### 原文の問題点
同じ一文の $M$ の分解は、長さ $j_0^N$ の前半 $(N_j)_{j=0}^{j_0^N-1}$ に続けて、
それぞれ長さ $j_1^N-j_0^N$ のブロック $(N_j)_{j=j_0^N}^{j_1^N-1}$ を $k=0,\dots,n-1$ の **$n$ 個**連結している。
よって $\textrm{Lng}(M) = j_0^N + n(j_1^N-j_0^N)$、$j_1 = \textrm{Lng}(M)-1 = j_0^N + n(j_1^N-j_0^N) - 1$ となり、
係数は $(n+1)$ ではなく **$n$** である。

### 形式化での扱い
**証明成功**。 修正: 展開後の末尾添字 $j_1$ の式の off-by-one を補正する。 当方の `oper`（$M[n] = \textrm{take}\,j_0\,M \mathbin{@} \textrm{concat}(\textrm{map}(\lambda k.\,\cdots)[0..<n])$、
yaBMS で経験的検証済）はブロック $n$ 個でこの訂正後の式と一致する（`oper_d0zero_expand`）。

## A9. §8.2 LastStep の添字 J_1 の範囲外参照 [軽微]

### 位置
§8.2「強単項性」, 写像 LastStep の定義（\(J_1\) を置く一文）。

### 原文
> \(J_1 := \textrm{Lng}(\textrm{Br}(M))\)と置く。… \((\textrm{Br}(M)_{J_1})_{0,0} = (\textrm{Br}(M)_{J_1})_{1,0}\)ならば…

### 訂正案
$J_1 := \textrm{Lng}(\textrm{Br}(M)) - 1$。$\textrm{Br}(M) = ()$ ならば $\textrm{LastStep}(M) = 0$。

### 原文の問題点
\(\textrm{Br}(M)\) の添字は \(0,\dots,\textrm{Lng}(\textrm{Br}(M))-1\) の範囲。\(J_1 := \textrm{Lng}(\textrm{Br}(M))\) と置くと \(\textrm{Br}(M)_{J_1}\) は範囲外。直後の「\(J_1 = 0\) ならば」も \(\textrm{Lng}(\textrm{Br}(M)) = 0\)（\(\textrm{Br}(M)\) が空）の意図と読め、\(J_1\) は最終成分の添字 \(\textrm{Lng}(\textrm{Br}(M))-1\) を指すべき。

### 形式化での扱い
**証明成功**。 修正: `LastStep` の定義を範囲外参照しない形（訂正後と一致）に取る。 `LastStep`（pss_defs §8）は `Br M = []` で `0`、それ以外は `J1 = Lng(Br M)-1` を最終添字として定義（訂正後と一致）。

## A10. §6.5 簡約化: 複数の命題が相互に依存し、死枝[19]/[20]の不到達には独立な証明を要する

### 位置
§6.5「簡約化」の以下の命題群と、それらに付された簡潔な証明（「即座に従う」「\(\textrm{Red}\) の再帰的定義より従う」等）。

### 原文
- 命題（単項性と \(\textrm{Red}\) の関係）— 証明: 「直系先祖の \(\textrm{Red}\) 不変性より従う」
- 系（直系先祖の \(\textrm{Red}\) 不変性）— 証明: 「\(\textrm{Lng}(M)\) に関する数学的帰納法から即座に従う」
- 命題（\(\textrm{Red}\) の \(\textrm{IncrFirst}\) 不変性）/（\(\textrm{Red}\) と \(\textrm{Pred}\) の可換性）— 証明: 「\(\textrm{Red}\) の再帰的定義より」
- \(\textrm{Red}\) の定義中の脚注 **[19]/[20]**（\(M_{1,0}>0\) の場合の \(\textrm{Red}(M):=M\) の分岐）— 「後の命題により、この分岐は生じない」

### 訂正案
脚注[19]/[20]の不到達（命題（単項性と $\textrm{Red}$ の関係））を、系（直系先祖の $\textrm{Red}$ 不変性）を経由せず独立に証明し、それを起点に他の命題を導く。

### 原文の問題点
これらの証明が参照する依存を辿ると、次のように互いに依存している。

- 脚注[19]/[20]の分岐が生じないこと（\(M_{1,0} \le j_N\) かつ \((N_j)_{j=M_{1,0}}^{j_N} \in PT_{\textrm{PS}}\)）は、命題（単項性と \(\textrm{Red}\) の関係）が主張する内容である。
- その命題の証明は系（直系先祖の \(\textrm{Red}\) 不変性）を用いる。
- 系（直系先祖の \(\textrm{Red}\) 不変性）の証明（\(\textrm{Lng}\) 帰納）は、A4 に記した通り \(T_{\textrm{PS}}\) 全体では成立せず、定義域を先祖係留切片へ補正する必要がある。
- 補正後の定義域でこれを示す議論は、命題（\(\textrm{Red}\) の \(\textrm{IncrFirst}\) 不変性）に依拠する。一方、後者の \(M_{1,0}>0\) の場合は、上記の脚注[20]の分岐が生じないこととちょうど同値になる（分岐が生じると \(\textrm{Red}(\textrm{IncrFirst}(M)) = \textrm{IncrFirst}(M) \neq M = \textrm{Red}(M)\) となるため）。

すなわち「即座に従う」で結ばれた一連の命題は、線形ではなく相互に参照し合っており、いずれか一つを他に依存せず確立しない限り全体が定まらない。

### 形式化での扱い
**証明成功**。 修正: 循環を避け、$\textrm{Red}$ 経由でなく行0値の単調性という別不変量で独立に証明する。 脚注[20]の不到達（\(M_{1,0}>0\) の場合）を、\(\textrm{Red}\) を経由する祖先関係（\(\le\)）ではなく、\(\textrm{Red}\) 出力の行0の値の単調性（単項入力に対し \(\textrm{Red}\) 出力の左端が行0の最小値となること）という別の不変量から証明した（`m_6_5_monoT_Red_m10pos`）。これにより上記の循環が解け、残りの命題が順に従う。詳細・経験的検証は `docs/red-le-domain.md` および `python/red65_*.py` ほか。

## A11. §7.2 命題（scb分解の合成則）(2): 前提に \(c\) が主表現列であることが必要（反例あり） [軽微]

### 位置
§7.2「命題（scb分解の合成則）」の (2)。形式化では `p_7_2_scb_compose` の第2主張に対応する。

### 原文
> (2) \((s,c,b)\) が \(t\) の scb分解ならば \((D_v s, c, b)\) は \(D_v t\) の scb分解である。

### 訂正案
(2) $(s,c,b)$ が $t$ の scb分解で $c$ が主表現列（`isPTB_str c`）ならば、$(D_v s, c, b)$ は $D_v t$ の scb分解である。

### 原文の問題点
scb分解 \((s,c,b)\) の定義は、対象項が空項 \(()\)（`Trm []`）でない限り、中央成分 \(c\) が主表現列（principal、`isPTB_str c`、すなわち先頭が `Dsym` で始まる平坦化文字列）であることを要求する。一方、対象が空項 \(()\) のときはこの主表現条件が課されない。

このため、\(t = ()\) の場合に (2) は反例を持つ。\(t=()\), \(s=()\), \(c=(Zsym)\), \(b=()\) を取ると \((s,c,b)\) は \(t=()\) の scb分解である（\(t=()\) なので \(c\) への主表現条件は不要、`flatBT () = () = s\frown c\frown b` は \(c=(Zsym)\) では成り立たないため厳密には \(c\) の取り方に注意が必要だが、定義上 \(t=()\) で主表現条件が外れる帰結として中央成分が主表現でない分解が許容され得る点が問題の核）。しかし \(D_v t = D_v() \neq ()\) は常に非空項なので、その scb分解 \((D_v s, c, b)\) は \(c\) が主表現列であることを要求する。\(c=(Zsym)\) は主表現列ではない（主表現の平坦化は必ず `Dsym` で始まり `Zsym` で始まることはない）ので、(2) の結論は成り立たない。

### 形式化での扱い
**証明成功**。 修正: 前提に「$c$ が主表現列（`isPTB_str c`）」を追加する（$t\neq()$ と等価）。 (1) は原文どおり成立し `m_7_2_scb_compose` として証明済。(2) は原文の literal 形を反例として機械化（`scbcomp_compose2_counterexample`、`\<not> isPTB_str [Zsym]` は `scbcomp_isPTB_Zsym_False`）、補正版を `scbcomp_compose2_PT`（前提 `isPTB_str c` 追加）として証明した。いずれも本体ビルド緑。

## A12. §7.2 命題（scb分解の置換可能性）: 前提に \(t_0\neq()\) または \(c_1\) が主表現列であることが必要（反例あり） [軽微]

### 位置
§7.2「命題（scb分解の置換可能性）」。形式化では `p_7_2_scb_replaceable`。

### 原文
> \(c_0, c_1 \in T_{\textrm{B}}\)、\((c_0\) が主表現列でない\() \vee (c_1\) が主表現列\()\)、\(t_0 \in T_{\textrm{B}}\)、\((s, \textrm{flat}(c_0), b)\) が \(t_0\) の scb分解であるとする。このとき \(t_1 \in T_{\textrm{B}}\) が存在して \(\textrm{flat}(t_1) = s\frown\textrm{flat}(c_1)\frown b\) かつ \((s, \textrm{flat}(c_1), b)\) が \(t_1\) の scb分解となる。

### 訂正案
$c_0, c_1 \in T_{\textrm{B}}$、$t_0 \in T_{\textrm{B}}$、$t_0 \neq ()$、$(s, \textrm{flat}(c_0), b)$ が $t_0$ の scb分解であるとする。このとき $t_1 \in T_{\textrm{B}}$ が存在して $\textrm{flat}(t_1) = s\frown\textrm{flat}(c_1)\frown b$ かつ $(s, \textrm{flat}(c_1), b)$ が $t_1$ の scb分解となる。

### 原文の問題点
scb分解の主表現条件は、対象項が空項 \(()\) のときのみ外れる（[[A11]] と同じ穴）。原文の選言前提 \((\neg\textrm{principal}(c_0)) \vee \textrm{principal}(c_1)\) は、\(c_0 = ()\)（\(\neg\textrm{principal}\) で左成立）のとき \(c_1\) が**非主表現（複項）でも満たされてしまう**。

反例: \(t_0 = c_0 = ()\)（空項）、\(s=b=()\)、\(c_1 = D_0() \cdot D_1()\)（複項＝2項のタプル、非主表現）。前提はすべて成立（\((s,\textrm{flat}(c_0),b)\) は \(t_0=()\) の scb分解、選言前提は左で成立）。だが結論の \(t_1\) は \(\textrm{flat}(t_1)=\textrm{flat}(c_1)\) と flat の単射性（`m_7_flatBT_inj`）から \(t_1 = c_1\) に限られ、\(c_1 \neq ()\) なので scb分解 \((s,\textrm{flat}(c_1),b)\) は \(\textrm{principal}(\textrm{flat}(c_1))\) を要求するが、\(c_1\) は複項ゆえ偽。よって結論が成り立たない。

### 形式化での扱い
**証明成功**。 修正: 前提に「$t_0\neq()$ または $c_1$ 主表現列」を追加（像条件つき補正版）。 反例を `m_7_2_scb_replaceable_counterexample`（`scbrepl_multi_not_PTB` = 複項の flat は非主表現）として機械化。\(t_0=()\) の退化ケースを `m_7_2_scb_replaceable_t0zero`、像条件つきの補正版を `m_7_2_scb_replaceable_corr_mod_image`（`scbrepl_concl_from_image` 経由）として証明した。いずれも本体ビルド緑。

## A13. §7.2 系（加法とscb分解の関係）(3): \(D_v(t+c)\) の出現位置が一意でないため偽（反例あり） [軽微]

### 位置
§7.2「系（加法とscb分解の関係）」の (3)。形式化では `p_7_2_add_scb` の第3主張。

### 原文
> \(c' \in T_{\textrm{B}}\) が主表現、\(u_1 \in T_{\textrm{B}}\)、\(\textrm{flat}(u_1) = s_1 \frown D_v\,\textrm{flat}(t+c) \frown b_1\)、\((s_0, \textrm{flat}(c), b_0)\) が \(u_1\) の scb分解であるとき、ある \(u_1'\) が存在して \(\textrm{flat}(u_1') = s_1 \frown D_v\,\textrm{flat}(t+c') \frown b_1\) かつ \((s_0, \textrm{flat}(c'), b_0)\) が \(u_1'\) の scb分解となる。

### 訂正案
$c' \in T_{\textrm{B}}$ が主表現、$u_1 \in T_{\textrm{B}}$、$\textrm{flat}(u_1) = s_1 \frown D_v\,\textrm{flat}(t+c) \frown b_1$、$(s_0, \textrm{flat}(c), b_0)$ が $u_1$ の scb分解、**かつ $s_0 = s_1 \frown D_v\,\textrm{flat}(t)$**（2 出現の一致）であるとき、ある $u_1'$ が存在して $\textrm{flat}(u_1') = s_1 \frown D_v\,\textrm{flat}(t+c') \frown b_1$ かつ $(s_0, \textrm{flat}(c'), b_0)$ が $u_1'$ の scb分解となる。

### 原文の問題点
主張は暗黙に「\(s_1 \frown D_v\,\textrm{flat}(t+c) \frown b_1\) で指す \(D_v(t+c)\) の出現と、\((s_0,\textrm{flat}(c),b_0)\) が指す \(c\) の出現が**同一の部分項**」を仮定しているが、これは前提から従わない。\(u_1\) が \(D_v(t+c)\) と別の \(c\) を**両方**部分項に持つとき、第1主表現を \(s_1\,D_v\dots b_1\) で、第2主表現の \(c\) を \((s_0,\textrm{flat}(c),b_0)\) で指す配置が成立し、\(c\to c'\) 置換後に要求される2つの flat 文字列が食い違う。

反例: \(t=0\), \(c=D_0 0\), \(c'=D_0(D_0 0)\), \(v=0\), \(u_1=(D_0(D_0 0), D_0 0)\)（2主表現タプル）。\(s_1\,D_v\,\textrm{flat}(t+c)\,b_1\) は**第1**主表現を、\((s_0,\textrm{flat}(c),b_0)\) は**第2**主表現を指す。結論の \(u_1'\) は \(\textrm{flat}(u_1')=s_1\,D_v\,\textrm{flat}(t+c')\,b_1\)（第1側置換）と \(\textrm{flat}(u_1')=s_0\,\textrm{flat}(c')\,b_0\)（第2側置換）を同時に満たす必要があるが、両文字列は相異なるので flat の単射性（`m_7_flatBT_inj`）より存在しない。

### 形式化での扱い
**未証明**。 (1) は原文どおり成立し `m_7_2_add_scb_conj1` として証明済。(3) の literal 形を反例 `m_7_2_add_scb_conj3_counterexample` として機械化した。(2)（\(c\to c'\) 置換の単純版）は `m_7_2_add_scb_conj2` として証明済。いずれも本体ビルド緑。 **(3) の補正版は未証明**。整合前提つき (3) を条件補題 `m_7_2_add_scb_conj3` として機械化(green)したが、これは存在残差 `scbrepl_image`(s₁@(D_v#flat(t+c'))@b₁ なる T_B 項の存在=§7.2 右脊柱手術、`m_7_2_scb_replaceable_corr_mod_image` と同根)を前提 `image` として仮定した**正確な reduction** にとどまる。整合前提が反例で破れること(s₀ の不一致)は確認済。残差自体の証明が済むまで (3) 補正版は未証明。

## A14. §7.2 命題（scb分解の一意性）(3)(4)(5): 空項 \(t=()\) で偽（[[A11]]–[[A13]] と同根） [軽微]

### 位置
§7.2「命題（scb分解の一意性）」の (3) 種の排他性・(4) 第\(0\)種の一意性・(5) 第\(1\)種の一意性。形式化では `p_7_2_scb_unique` の第3〜5主張。

### 原文
(3) $t$ は第$0$種scb分解可能でないか、または $t$ は第$1$種scb分解可能でない。

(4) $t$ の第$0$種scb分解は一意である。

(5) $t$ の第$1$種scb分解は一意である。

### 訂正案
(3)(4)(5) の前提に「$t \neq ()$」を追加する。

### 原文の問題点
A11–A13 と同じく、対象が空項 \(()\)（`Trm []`、\(\textrm{flat}=[Zsym]\)）のとき scb分解の主表現条件が外れる。このため \(t=()\) では中央成分 \(c\) が主表現でない分解（例 \((s,c,b)=([],[Zsym],[])\) と \(([Zsym],[],[])\)）が両立し、その第\(0\)/第\(1\)種条件（`RightNodes` 条件）が**空虚に**成立してしまう。よって (4)(5) の一意性も (3) の排他性も \(t=()\) で破れる。

### 経験的確認
非空項では (3)(4)(5) はすべて真（`python/_scbkind_check.py`、深さ2・添字 \(\{0,1,2\}\) の \(D_\omega\) 抜き項 1560 個で違反 0）。違反は \(t=()\) でのみ生じる。

### 形式化での扱い
**証明成功**。 修正: 前提に「$t\neq()$」を追加する。 種一意性 (4)(5) を「中央成分の一致 \(c_0=c_1\) への健全な還元」`m_7_2_scb_kind_unique_of_ceq`（`m_7_2_scb_unique_decomp` 経由、`t≠()` 下で \(c_0=c_1\) から1行）として機械化・緑。残る \(c_0=c_1\)（原文の「\(c\) は `RightNodes` 脊柱で固定される最大の真部分項文字列」content.md ~1900–1960）は別途の多補題プログラム。

## A15. §7.3 命題（Trans の well-defined 性）および (IncrFirst,Red) 不変性: 定義域は \(T_{\textrm{PS}}\) 全体でなく「\(\textrm{Red}(M)\) が簡約」の範囲

### 位置
§7.3「命題（\(\textrm{Trans}\) の well-defined 性）」(content.md 2182) と「命題（\(\textrm{Trans}\) の \((\textrm{IncrFirst},\textrm{Red})\) 不変 \(P\) 同変性」「命題（\(\textrm{Mark}\) の \((\textrm{IncrFirst},\textrm{Red},P)\) 不変性」の \(\textrm{Red}\)/\(\textrm{IncrFirst}\) 部。

### 原文
命題（$\textrm{Trans}$ のwell-defined性）: 上の条件を全て満たす写像 $\textrm{Trans}$ と $\textrm{Mark}$ が一意に存在する。

### 訂正案
$\textrm{Red}(M)$ が簡約である $M$（簡約ペア数列・標準形・[[A4]] の祖先 anchored 切片）に対し $\textrm{Trans}/\textrm{Mark}$ が一意に定まり、$(\textrm{IncrFirst},\textrm{Red})$ 不変性が成り立つ。

### 原文の問題点
\(\textrm{Trans}\)/\(\textrm{Mark}\) の非簡約枝は \(\textrm{Trans}(M) := \textrm{Trans}(\textrm{Red}(M))\)（長さ不変）であり、再帰の停止には \(\textrm{Red}(M)\) が簡約であること（= \(\textrm{Red}\) の冪等性）が要る。しかし冪等性は [[A4]] のとおり \(T_{\textrm{PS}}\) 全体では**偽**であり、\(\textrm{Red}(\textrm{Red}(M)) \neq \textrm{Red}(M)\) なる \(M\) では (D) 枝が簡約に到達せず、原文の「\(\textrm{Lng}(M)\) に関する数学的帰納法より即座」は成立しない（帰納の measure が下がらない）。

### 形式化での扱い
**証明成功**。 修正: 定義域を $T_{\textrm{PS}}$ 全体でなく $\textrm{Red}(M)\in RT_{\textrm{PS}}$ の範囲に制限する。 `m_7_3_Trans_welldef`/`m_7_3_Mark_welldef`（totality on \(RT_{\textrm{PS}}\)、\(\textrm{Lng}\) 強帰納）、`m_7_3_Trans_Red`/`m_7_3_Mark_Red`/`m_7_3_Trans_IncrFirst`/`m_7_3_Mark_IncrFirst`（域 \(\textrm{Red}(M) \in RT_{\textrm{PS}}\)）として機械化・緑。

## A16. §7.3 命題（Trans が単項性を保つこと）および (IncrFirst,Red) 不変性 (2) の Σ_B 表示: 先頭 P 成分が零項のとき偽（原文の再帰的定義との内部矛盾）

### 位置
§7.3「命題（\(\textrm{Trans}\) が単項性を保つこと）」(content.md 2358) と「命題（\(\textrm{Trans}\) の \((\textrm{IncrFirst},\textrm{Red})\) 不変 \(P\) 同変性）」(2) の \(\Sigma_{\textrm{B}}\) 表示 (content.md 2236)。形式化では `p_7_3_Trans_monoT` と `p_7_3_Trans_IncrFirst_Red` の (2) 部。

### 原文
任意の $M \in T_{\textrm{PS}}$ に対し、以下は同値である：

(1) $M$ は単項である。

(2) $\textrm{Trans}(M)$ は単項であるか、$P(M)_0$ が零項でありかつ $\textrm{Lng}(P(M)) = 2$ である。

### 訂正案
$M \in RT_{\textrm{PS}} \land \neg\textrm{zeroT}(P(M)_0)$ の下で、$\Sigma_{\textrm{B}}$ 表示および単項性命題 (2) を述べる。

### 原文の問題点
\(\textrm{Trans}\) の**再帰的定義の複項枝**(content.md 2158–2172) は
\(\textrm{Trans}(M) := \textrm{Trans}((M_j)_{j=0}^{j_0-1}) + (\,D_0 0 \text{ or } \textrm{Trans}(P(M)_{J_1})\,)\)
であり、先頭 P 成分 \(P(M)_0\) が零項のとき接頭辞 \((M_j)_{j=0}^{j_0-1}\) が長さ \(1\) の \(((0,0))\) になると基底枝より \(\textrm{Trans}(((0,0))) = 0\)（\(D_0 0\) ではなく \(0\)）に**吸収**される。一方
- \(\Sigma_{\textrm{B}}\) 表示 (2236) は各零項成分を \(t_J := D_0 0\) として総和をとるので、\(P(M)_0\) 零項では先頭に \(D_0 0\) を**残す**。
- 単項性命題 (2358) (2) 「\(\textrm{Trans}(M)\) が単項 \(\lor\)（\(P(M)_0\) 零項 \(\land\) \(\textrm{Lng}(P(M))=2\)）」。

両者は \(P(M)_0\) 零項の複項 \(M\) で再帰的定義と矛盾する。

### 反例
\(M = ((0,0),(0,0))\)（= 順序数 \(2\)、原始数列 "0,0"。\(M = ((0,0),(1,0))[2] \in ST_{\textrm{PS}}\) で標準形）。\(M\) は**複項**(\(\neg\)単項; `le0(M,0,1)` 偽)。\(P(M) = (((0,0)),((0,0)))\)、\(P(M)_0\) 零項、\(\textrm{Lng}(P(M))=2\)。再帰的定義より \(\textrm{Trans}(M) = \textrm{Trans}(((0,0))) + D_0 0 = 0 + D_0 0 = D_0 0\)（**単項**、`Lng(PB)=1`）。
- 単項性命題: (1) \(M\) 単項 = **偽**、(2) \(\textrm{Trans}(M)\) 単項 = **真** → 同値が破れる。
- \(\Sigma_{\textrm{B}}\) 表示: \((D_0 0, D_0 0)\)（`Lng(PB)=2`）を主張するが実際は \(D_0 0\) → **偽**。

### 経験的確認
ST_PS 閉包（diagSeq から \(M[n], n\ge1\) で BFS、7046 個）で違反は先頭 P 成分が零項の複項列 \(((0,0))^k\) (\(k\ge2\)) のみ。`Lng(PB(\textrm{Trans}(M))) = (\)零項なら \(0\) 否なら \(\textrm{Lng}(P(M)) - [P(M)_0\) 零項\(]\,)` が成り立つ（先頭零項 1 個のみ吸収）。`python/_trans_monoT_check`（/tmp 検証）。

### 根本原因
原始数列的な後続（先頭に零項ブロックを持つ標準形 \(((0,0))^k\) 等）で、長さ 1 の \(((0,0))\) の \(\textrm{Trans}\) が \(0\)（順序数 \(0\)）である一方、複項の成分としての零項列は \(D_0 0\)（順序数 \(1\) = "+1"）を表すべき、という二重の意味の衝突。原文の再帰的定義（吸収する）と \(\Sigma_{\textrm{B}}\)/単項性命題（残す）が非整合。

### 追補（2026-06-21, 例外枝の転記形も偽 → 制限 iff で確定・無条件証明済み）
当初 `p_7_3_Trans_monoT` に例外選言を補って
\[\textrm{monoT}(M) \iff \big(\textrm{Lng}(P_{\textrm{B}}(\textrm{Trans}\,M)) = 1 \,\lor\, (\textrm{zeroT}(P(M)_0) \land \textrm{Lng}(P(M)) = 2)\big)\]
と転記したが、**この補正形そのものも偽**（`python/_step0_monoT_restricted.py` で reduced 列 maxlen≤5 を全数: **転記形 53 反例**, うち代表 \(M = ((0,0),(0,0),(1,1))\) は複項なのに \(\textrm{Trans}\,M\) が単項で、かつ右選言が真 → 同値が破れる。例外選言が**逆向き**に付いていた）。正しい経験的真形（同データで reduced 1269 件・**反例 0**）は先頭 P 成分非零項への制限 iff:
\[M \in RT_{\textrm{PS}} \,\land\, \neg\textrm{zeroT}(P(M)_0) \ \Longrightarrow\ \big(\textrm{monoT}(M) \iff \textrm{Lng}(P_{\textrm{B}}(\textrm{Trans}\,M)) = 1\big).\]
この制限形を `pss_wip.thy` の `m_7_3_Trans_monoT` として **無条件に証明済み**（前提は \(M \in RT_{\textrm{PS}}\) と \(\neg\textrm{zeroT}(P(M)_0)\) のみ; 偽命題や仮定偽装なし、緑 "Finished PSS"）。順方向は `Trans_PT_single`（単項 ⇒ \(\textrm{Trans}\,M\) 単一主成分）、逆方向は対偶: 複項枝の \(\textrm{Trans}\,M = \textrm{Trans}(A) +_{\textrm{B}} (\cdots)\) 分解で両被加数が主成分非空 ⇒ \(\textrm{Lng}(P_{\textrm{B}}) \ge 2\)。`pss_paper.thy` の `p_7_3_Trans_monoT` 文面もこの制限形に訂正（sorry 保持）。

### 形式化での扱い
**証明成功**。 修正: 前提に「$\neg\textrm{zeroT}(P(M)_0)$」を追加した制限 iff に直す。 `Trans` 定義（`pss_paper.thy` 1137–1140 複項枝）は原文の**再帰的定義に忠実**（緑の値不変量 `Trans_Mark_invariant_aux`・`m_7_3_Trans_zeroT` はこの忠実な `Trans` 上で成立）。`p_7_3_Trans_monoT` / `p_7_3_Trans_IncrFirst_Red`(2) は上記訂正前提の下でのみ機械化可能（先頭零項枝を除外）。（`m_7_3_Trans_monoT`、P0非零項制限、fc60f0b。下記 追補参照）。

## A17. §7.3 命題（右端第1基点の Mark の基本性質）ほか §7.3 順序系: 零項基底 \(((0,0))\) での例外（A16 と同根の系統的零項エッジ）

### 位置
§7.3「命題（右端第\(1\)基点の Mark の基本性質）」(content.md 2294) ほか、Mark の基点・順序を \(D_{M_{1,m}} 0\) 等の主表現で特徴づける §7.3 命題群。形式化では `p_7_3_Mark_rightmost1` 等。

### 原文
$m = j_1$ であることと $\textrm{Mark}(M,m) = D_{M_{1,m}} 0$ であることは同値である。

### 訂正案
§7.3 の基点・順序命題の前提に「$M$ は非零項」（$M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}$）を追加する。

### 原文の問題点
\(M = ((0,0))\)（零項、\(\in RT_{\textrm{PS}}\)）で \(m = 0 = j_1\) のとき、\(\textrm{Mark}(M,0) = 0\)（零項基底枝）であって \(D_{M_{1,0}} 0 = D_0 0 \neq 0\) ではない。よって「\(m = j_1 \Leftrightarrow \textrm{Mark}(M,m) = D_{M_{1,m}} 0\)」は \(M\) 零項で偽（左真・右偽）。[[A16]] と同じく原文が暗黙に非零項（genuine な単項以上）を仮定している系統的エッジ。

### 経験的確認
ST_PS 閉包で \((M,m) \in \textrm{Marked}\) を走査、違反は \(M = ((0,0))\) の1件のみ（9698/9699）。\(\neg \textrm{zeroT}(M)\)（特に \(M \in PT_{\textrm{PS}}\)）を課せば全例で成立。

### メタ観察
§7.3 は \(\textrm{Trans}\)/\(\textrm{Mark}\) の再帰的定義の**零項基底枝**（\(M_0 = (0,0) \Rightarrow 0\)）と、主表現としての \(D_0 0\)（="+1"）の二重性により、零項を明示除外しないと多くの命題が崩れる（[[A16]] 単項性命題、本 A17 基点系）。形式化は一貫して \(\neg\textrm{zeroT}\)／\(RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\) 域で機械化する方針。

### 形式化での扱い
**証明成功**。 修正: 零項基底 $((0,0))$ の例外を補正（$(M,j)\in\textrm{Marked}$ 等、A16 と同根）。 （`m_7_3_Mark_rightmost1` ほか §7.3 順序系、A17 補正込み・green）。

## A18. §7.4 系（Mark と \(<_M^{\textrm{NextAdm}}\) の関係）: 仮定の祖先 \(j\) に「\(M\) 許容（\((M,j)\in\textrm{Marked}\)）」を補う必要

### 位置
§7.4「系（$\textrm{Mark}$ と $<_M^{\textrm{NextAdm}}$ の関係）」(content.md 付近、`p_7_4_Mark_nextAdm`)。

### 原文
$j_1=\textrm{Lng}\,M-1$ の一意な NextAdm 親 $j_0$ と、$(0,j)\le_M(0,j_0)$ なる任意の $j$ について、$\textrm{Mark}(M,j)$ は $\textrm{Mark}(M,j_0)$ の周りに scb 分解される。

### 訂正案
命題の仮定に「$j$ は $M$-許容（$(M,j)\in\textrm{Marked}$）」を追加する。

### 原文の問題点
仮定 \((0,j)\le_M(0,j_0)\)(= `leR M 0 j j0` = 行0祖先 `le0`)は \(j\) の**許容性を含意しない**。\(\textrm{Mark}\) の定義域は \(RT_{\textrm{PS}}^{\textrm{Marked}}\)（許容基点列）なので、\(\textrm{Mark}(M,j)\) が原文の「marked 列の像」である為には \((M,j)\in\textrm{Marked}\)（特に \(\textrm{adm}\,M\,j\)）が必要。

### 経験的確認
簡約列の閉包（`enum_reduced_tiling(maxlen=5,maxe=3)`、長さ\(\ge2\) で 1465 件、全件で \(j_1\) の NextAdm 親が一意）を走査し、\(j_0\) の行0祖先 \(j\le_M j_0\) で \(\neg\textrm{adm}\,M\,j\) となる**反例 25 件**を確認。最小例 \(M=((0,0),(1,1),(2,2),(3,1))\)、\(j_0=2\)、非許容祖先 \(j=1\)（`python/_admj_audit.py`）。よって原文のままでは \(\textrm{Mark}(M,j)\) が定義域外の対象を指す。

### 形式化での扱い
**証明成功**。 修正: 仮定の祖先 $j$ に「$M$ 許容（$(M,j)\in\textrm{Marked}$）」を追加する。 `m_7_4_Mark_nextAdm`（`pss_wip.thy`）は \(M\in RT_{\textrm{PS}}\)・\((M,j)\in\textrm{Marked}\) を仮定し、エンジン補題 `Mark_nest_common_marked`（両列 Marked で \(\textrm{Mark}\,m\) を \(\textrm{Mark}\,m'\) 周りに一意 scb 分解、`m_7_4_Trans_Mark_Pred` の合成 + `m_7_2_scb_unique_sb` で位置固定）に \(m=j,\,m'=j_0\) を代入して得る（\(j\le j_0\) は `le0`→`nextrel0_rtrancl_mono`、\(j_0<\textrm{Lng}\,M-1\) は `nextAdm`）。[[A17]] と同根（原文が暗黙に許容/非零項を仮定するエッジ）。

## A19. §7.4 命題（Mark が順序関係を保つこと）: 結論 (2) の対が反転している

### 位置
§7.4「命題（$\textrm{Mark}$ が順序関係を保つこと）」(content.md 2466)。

### 原文
$(M,m_0),(M,m_1)\in T_{\textrm{PS}}^{\textrm{Marked}}$ に対し、次は同値: (1) $m_0<m_1$。 (2) $\textrm{Mark}(M,m_1)\neq\textrm{Mark}(M,m_0)$ かつ $(\textrm{Mark}(M,m_1),\textrm{Mark}(M,m_0))\in T_{\textrm{B}}^{\textrm{Marked}}$。

### 訂正案
(2) $(\textrm{Mark}(M,m_0),\textrm{Mark}(M,m_1)) \in T_{\textrm{B}}^{\textrm{Marked}}$

### 原文の問題点
\(T_{\textrm{B}}^{\textrm{Marked}}=\{(t,c)\mid (s,c,b)\,\text{が}\,t\,\text{の scb 分解}\}\)(content.md 1834)は **(whole, block)** の規約(\(c\) は \(t\) の部分=被覆される側、cf. 1936 \((t+c,c)\))。一方 \(\textrm{Mark}(M,m)\) は \(m\) が小さいほど大きい(\(\textrm{Mark}(M,0)=\textrm{Trans}(M)\) 最大、\(\textrm{Mark}(M,j_1)=D_{M_{1,j_1}}0\) 最小)。よって \(m_0<m_1\) では \(\textrm{Mark}(M,m_0)\) が whole、\(\textrm{Mark}(M,m_1)\) が block で、正しい対は \((\textrm{Mark}(M,m_0),\textrm{Mark}(M,m_1))\in T_{\textrm{B}}^{\textrm{Marked}}\)。原文の \((\textrm{Mark}(M,m_1),\textrm{Mark}(M,m_0))\) は **whole と block が逆**。

### 確認(機械証明による)
`Mark_MarkedB_nest`(green): \((M,m),(M,m')\in\textrm{Marked}\wedge m\le m'\wedge M\in RT_{\textrm{PS}}\Rightarrow(\textrm{Mark}\,M\,m,\textrm{Mark}\,M\,m')\in\textrm{MarkedB}\)。すなわち小 index が whole。`MarkedB_antisym`(green)より両向きの nest は項の一致を強制するので、\(m_0<m_1\)(狭義, 像が相異なる)では原文の逆向き対は偽。

### 形式化での扱い
**証明成功**。 修正: 結論 (2) の対を反転させ、正しい $(\textrm{Mark}(M,m_0),\textrm{Mark}(M,m_1))$ にする。 `m_7_4_Mark_order`（pss_wip, RT_PS, 訂正後の向き）。nest=`Mark_MarkedB_nest`、(2)⟹(1)=`MarkedB_antisym`、(1)⟹(2) の単射性=`Mark_distinct`/`Mark0_ne_Mark`（右スパイン長狭義減少）。memory `pss-74-nextadm`。

## A20. §8.1 補題（条件(I)か(III)の下での c_1 前後の具体表示）part(1): 単項切片で「c_1 = Trans(切片)」が偽

### 位置
§8.1「補題（条件(I)か(III)の下での $c_1$ 前後の具体表示）」(content.md 2923) の (1)(content.md 2955)。

### 原文
$c_1 = \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = \textrm{Trans}((M_j)_{j=j_0}^{j_1-1})$

### 訂正案
part(1) の $\textrm{Trans}(\text{切片}) = c_1$ に「$j_0 < j_1-1$（切片が非単項）」を課す。

### 原文の問題点
\(j_0 = j_1-1\)(切片 \((M_j)_{j=j_0}^{j_1-1}\) が単項 \([M_{j_0}]\))かつ \(M_{0,j_0} > M_{1,j_0}\)(非簡約)のとき偽。中間ステップ「\(\textrm{Mark}(\textrm{Pred}(M),j_0) = \textrm{Trans}(\text{切片})\)」は **Mark の Trans 表示**([[A19]] 隣、content 2490)の境界条件 \(j_1-m>0\) を破る(\(m=j_0=j_1-1\) で \(j_1-m=0\))。\(\textrm{Trans}\) は \((\textrm{IncrFirst},\textrm{Red})\) 不変で非簡約単項を rebase し row-0 頭を落とす(\(\to 0_B\))一方、\(c_1=\textrm{Mark}\) は \(D_{M_{1,j_0}}\) 頭を保持する。

### 経験的確認(独立検証)
最小反例 \(M = ((0,0),(1,0),(2,0))\)(**条件(I)**, \(M_{1,j_1}=0\))。\(j_1=2, j_0=1, j_{-1}=1\)、切片 \(=[(1,0)]\)、\(\textrm{Trans}([(1,0)]) = 0_B\) だが \(c_1 = D_0 0 \neq 0_B\)。`python/c1around_cex_audit.py`。条件(I)走査で 5/26 が part(1) 違反。

### 形式化での扱い
**未証明**。 （c1-around 訂正の part(1) A20ガード。全体 `m_8_1_condI_III_c1_around` 未。memory `pss-81-c1around`。[[A21]] 参照）。

## A21. §8.1 同補題 part(5): 条件(III)のとき基本列ブロックの親 \(j_0^N = j'_0\) が偽

### 位置
§8.1「補題（条件(I)か(III)の下での $c_1$ 前後の具体表示）」(content.md 2923) の (5)(content.md 2945-2947)。

### 原文
$N := (M[n]_j)_{j=0}^{j_0+(n-1)(j_1-j_0)}$ について、$j_0^N = j'_0$（$\textrm{parent}\,N\,0\,(\textrm{Lng}\,N-1) = j'_0$）である。

### 訂正案
part(5) を「$\textrm{transCondI}\,M$」に限定する。

### 原文の問題点
part(5) の周期性論法は基本列ブロックが正しい row-0 シフトで複製され \(\textrm{idx}\) が周期境界に乗ることを要し、これは **条件(I)**(\(M_{1,j_1}=0\))でのみ成立。条件(III)では偽。

### 経験的確認(独立検証)
最小反例 \(M = ((0,0),(1,1),(2,1))\)(**条件(III)**)。\(j_1=2,j_0=1\)、一意 next-parent \(j'_0=0\)、\(n=2\) で \(M[2]=((0,0),(1,1),(2,0),(3,1))\)、\(\textrm{idx}=2\)、\(N=((0,0),(1,1),(2,0))\)、\(\textrm{parent}\,N\,0\,2 = 1 \neq 0 = j'_0\)。条件(III)-only 走査で 18/18 が part(5) 違反、条件(I) では 0/26。

### 形式化での扱い
**未証明**。 （全体）。part(1)full=`m_8_1_c1_around_part1`、part(2)=`m_8_1_c1_around_part2`、part(3-2)=`m_8_1_c1_around_part3_2`（空虚）は証明済だが、(3-1)/(4-1)/(4-2)/(5) が未で、訂正後の全体 `m_8_1_condI_III_c1_around` は未証明。memory `pss-81-c1around`。

## A22 — §8.3 補題（第0種型基本列の基本不等式）の右辺添字脱落 [軽微]

### 位置
pss_paper.thy の `p_8_3_kind0_base_ineq`(article 3972「第0種型基本列の基本不等式」)。

### 原文
$M[n]_{0,\ q'(j_1-j_0)+r'}$

### 訂正案
$M[n]_{0,\ j_0+q'(j_1-j_0)+r'}$

### 原文の問題点
statement が右辺の列添字を \(M[n]_{0,\ q'(j_1-j_0)+r'}\) と書くが、原典の**証明本体**は \(M[n]_{0,\ j_0+q'(j_1-j_0)+r'}\)(= \(M_{j_0+r'}\))を用いている。statement で \(j_0+\) が脱落しており、そのままでは**偽**。

### 経験的確認
maxlen5 maxe3 で反例多数(独立検証、sweep agent)。

### 形式化での扱い
**証明成功**。 修正: 右辺の列添字に脱落した $j_0+$ を補完する。 （`m_8_3_kind0_base_ineq`、訂正形 `j0+…`・green）。

## A23. §7.1 Buchholz表記系 \([Buc1]\,([\,].4)(ii)\) の脚注修正: 基本列 \(a[n]=D_v\,b[x_n]\) が偽（外側 \(b[\cdot]\) の重複適用）

### 位置
§7.1（Buchholz の表記系）。\([Buc1]\,([\,].4)(ii)\) に対する記事の脚注修正（content.md 6427）。対象は \(a=D_v b\)、\(\mathrm{dom}(b)=T_u\)、\(v\le u<\omega\) の場合の基本列 \(a[n]\)。

### 原文
> すなわち[Buc1] ([].4) (ii)の場合分けにおいて、各 \(i \in \mathbb{N}\) に対し \(x_i\) を「\(i = 0\) ならば \(x_i = D_u 0\)、\(i > 0\) ならば \(x_i = b[D_u x_{i-1}]\)」と定め、\(a[n]\) の定義を \(D_v b[x_n]\) に変えるということである。

### 訂正案
> すなわち[Buc1] ([].4) (ii)の場合分けにおいて、各 \(i \in \mathbb{N}\) に対し \(x_i\) を「\(i = 0\) ならば \(x_i = D_u 0\)、\(i > 0\) ならば \(x_i = b[D_u x_{i-1}]\)」と定め、\(a[n]\) の定義を \(D_v x_n\) に変えるということである。

### 原文の問題点
最後の \(a[n] = D_v b[x_n]\) で、外側 \(b[\cdot]\) に \(x_n = b[\cdots] \in T_{u+1}\)（\(\notin \mathrm{dom}(b) = T_u\)）が渡り未定義 → Lemma 3.2(a) \(a[z] < a\) が破綻。

### 経験的確認
（`python/buc_ii_check.py`, case-(ii) の OT・\(D_\omega\)-free 主項 106 個・\(n\le4\)）:

| 読み | 定義域整合 | 3.2a | 3.2b | 3.2c |
|---|---|---|---|---|
| literal \(D_v b[x_n]\) | 3/106 | 3/106 | 106/106 | 53/106 |
| **訂正 \(D_v x_n\)** | **106/106** | **106/106** | **106/106** | **106/106** |

反例 \(a=D_0((D_1 0,\,D_1 0))\)。

### 形式化での扱い
**定義変更 未適用**（要追従）。`pss_paper.thy` の `operB`（\(([\,].4)(ii)\) 枝）と `python/buchholz.py` は現状 literal 実装。訂正 \(a[n]=D_v x_n\) を採用すれば、§7.2 命題（scb分解と基本列の関係）conjunct (2)（kind1/xseq、現 `🚨`）の土台が健全化し、解禁見込み（operB/xseq の極限再帰が定義域内で閉じる）。

## C1（明確化、訂正ではない） — §7.3「Trans の最左単項成分の左端」clause (3) の "D_u" の解釈 [軽微]

### 位置
§7.3 命題（$\textrm{Trans}$ の最左単項成分の左端の基本性質）clause (3)（content.md 2342）。

### 原文
左端2文字は $D_{M_{1,0}} D_u$ である。

### 明確化
機械化 `m_7_3_Trans_leftmost`(pss_wip)では clause (3) を `∃t. PB(Trans M)!0 = Dpt(enat(entry M 1 0)) t ∧ t ≠ 0⇩B` と表現し、第2文字 "\(D_u\)" を**非零余項 t の tree-head `bpHeadV(t)`** として読む。理由(経験的: monoT 314/360 ケース)は **t が複数の主表現成分を持ちうる**(= 単一 Dpt ではない)ため。原文の "\(D_u\)" を `t = Dpt w t'` の単一 Dpt と literal に取ると**偽**になる。`bpHeadV(t)`(t≠0 で存在)が忠実な読み。原文は偽ではなく、解釈の明確化のみ。

### 形式化での扱い
**証明成功**。 修正: （訂正でなく明確化）第2文字 $D_u$ を「非零余項 $t$ の $\textrm{bpHeadV}(t)$」と読む。 （`m_7_3_Trans_leftmost`、clause(3) はこの明確化形・green）。

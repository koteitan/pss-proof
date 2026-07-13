# 原文訂正案 (proposed corrections)

> ## 全数監査済み (2026-07-13)
>
> A1〜A46 を原文（`tmp/original.html`）と突き合わせて全数検証した。**このファイルに残る 30 件が現在の訂正案**である。
> 検証で取り下げた 16 件と、その取り下げ理由・経緯は [corrections-old.md](corrections-old.md) にある。


巨大数研究 Wiki の記事 **「ペア数列の停止性」**(P進大好きbot 著) に対する訂正案を
集約する。著者へのフィードバック用。

- **対象記事**: P進大好きbot「ペア数列の停止性」巨大数研究 Wiki ユーザーブログ, 2018.11.11.
  <https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7>
<!--
## 注意事項（GitHub 非表示）
- **各訂正の特定方法**: 記事の**節 (§) と命題名**（「命題（…）」）および**訂正対象の本文を
  逐語引用**することで、公開記事中で直接特定できるようにする。
- 原文は HTML（内部の LaTeX ソース）なので、訂正は HTML 内 LaTeX 記述への修正として記す。
- 数式は MathJax 記法（`$...$` / `$$...$$`）で書く。
- **「原文」節には論文の該当箇所を逐語引用し、「訂正案」節には、原文をそっくりそれに置き換えると論文が正しくなる、訂正後の本文そのものを書く**（原文と訂正案は平行な文章になる）。
  - **「原文」節・「訂正案」節では引用記法（`> `）を使わない**。地の文としてそのまま書く（引用の入れ子は読みにくく、平行に並べて見比べられない）。
  - 何をどう直すか、という**訂正動作**は書かない。**訂正後の本文**をそのまま書く。理由・機構は「原文の問題点」「原因」「反例」など別の見出しに書く。
  - 悪い例（訂正動作を書いている）:
    ```
    ### 訂正案
    Min を LEAST(nat 上で total、原文「最小のJ」の忠実転写)に変更する。
    ```
    → 原文をこの文章（`Min を…変更する`）にそのまま置き換えるとおかしい。
  - 良い例（A1）: 原文を訂正案にそっくり置き換えると論文が正しくなる。
    ```
    ### 原文
    - (2) $(M[n],n) \in \textrm{Dom}(F)$
    - (3) $(M,n) \in \textrm{Dom}(F)$ かつ $(M[n],n) \in \textrm{Dom}(F)$ かつ $F_M(n) = F_{M[n]}(n)$

    ### 訂正案
    $\textrm{Lng}(M) = 1$ のとき:
    - (2) $(M[n],n) \in \textrm{Dom}(F)$
    - (3) $(M,n) \in \textrm{Dom}(F)$ かつ $(M[n],n) \in \textrm{Dom}(F)$ かつ $F_M(n) = F_{M[n]}(n)$
    ```
-->

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

## A3. §6.4 系（$\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性）(4): 不等号は $>$ ではなく $\geq$（反例あり）

### 位置
§6.4 幹と枝 / 系（$\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性）の主張 (4)

### 原文
任意の\(M \in PT_{\textrm{PS}}\)と\(J'_0,J'_1 \in \mathbb{N}\)に対し、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置くと、\(J'_0 < J'_1 \leq J_1\)ならば以下が成り立つ：

(4) 任意の\(i \in \{0,1\}\)に対し\(M_{i,\textrm{Joints}(M)_{J'_0}} > M_{i,\textrm{Joints}(M)_{J'_1}}\)である。

### 訂正案
(4) 任意の\(i \in \{0,1\}\)に対し\(M_{i,\textrm{Joints}(M)_{J'_0}} \geq M_{i,\textrm{Joints}(M)_{J'_1}}\)である。更に\(\textrm{Joints}(M)_{J'_0} > \textrm{Joints}(M)_{J'_1}\)ならば\(M_{i,\textrm{Joints}(M)_{J'_0}} > M_{i,\textrm{Joints}(M)_{J'_1}}\)である。

### 原文の問題点
(2) が $\geq$（複数の枝が同一の joint に接続し得る）なので、$J'_0 < J'_1$ でも
$\textrm{Joints}(M)_{J'_0} = \textrm{Joints}(M)_{J'_1}$ となり得る。そのとき (4) の左辺と右辺は
同一の成分となり、狭義不等号は成立しない。反例:

$$M = (0,0)(1,1)(2,1)(3,1)(2,0)$$

- $\textrm{TrMax}(M) = 1$、$\textrm{Br}(M) = [\,(2,1)(3,1),\ (2,0)\,]$
- $\textrm{FirstNodes}(M) = [2,4]$、$\textrm{Joints}(M) = [1,1]$
- $J'_0=0 < J'_1=1$ だが $\textrm{Joints}(M)_{J'_0} = \textrm{Joints}(M)_{J'_1} = 1$ なので
  $M_{i,1} > M_{i,1}$ は偽。この $M$ は標準形・単項・簡約・$\textrm{Br}$ 降順（機械的に確認）。

### 経験的確認
$PT_{\textrm{PS}}$ の全数走査（$\textrm{Lng} \leq 5$、成分 $\leq 3$、該当する $(J'_0,J'_1)$ ペア 240,004 組）:

- $\geq$ 形（訂正案）の違反: **0 件**
- 狭義 $>$ の違反は、すべて $\textrm{Joints}(M)_{J'_0} = \textrm{Joints}(M)_{J'_1}$ の組で発生
- joints が相異なる 11,464 組では狭義 $>$ が **全件成立**（訂正案の第2文）

### 補足（(4) は本文で用いられている）
本文には「以下 $\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性は断りなく用いる。」という断り書きが
3 箇所（§8.1 系（強単項性の切片への遺伝性）の証明ほか）あり、この系は黙用されている。したがって
「(4) は未使用だから削除してよい」とは我々には言えず、削除ではなく $\geq$ への弱化を提案する。
我々が追えた範囲では、下流は (2) の $\geq$、$\textrm{Joints}_J \leq \textrm{TrMax} < \textrm{FirstNodes}_J$、
条件(A) $M_{0,\textrm{Joints}_J}+1 = M_{0,\textrm{FirstNodes}_J}$、$\textrm{Br}$ の降順性を用いており、(4) の
**狭義性**に依存する箇所は見つからなかったが、黙用箇所の確認をお願いしたい。

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
以下は形式化を進める中で気づいた点で、私たちの理解の範囲での指摘です。主張自体（標準形に
制限したもの）は経験的に成立を確認しており、証明の運びに一段の補強を提案するものです。

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

## A5. §6.6 命題（簡約性の切片への遺伝性）: 前提 \(j'_0 \le \textrm{TrMax}(M)\) は弱すぎる（反例あり）

### 位置
§6.6 簡約性 / 命題（簡約性の切片への遺伝性）

### 原文
任意の \(M \in RT_{\textrm{PS}}\) に対し、\(j_1 := \textrm{Lng}(M)-1\) と置くと、任意の
\(j'_0,j'_1 \in \mathbb{N}\) に対し \(j'_0 \le \textrm{TrMax}(M) \le j'_1 \le j_1\) ならば
\((M_j)_{j=j'_0}^{j'_1}\) は簡約である。

### 訂正案
任意の \(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\) に対し、\(j_1 := \textrm{Lng}(M)-1\)、
\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\) と置くと、任意の \(j'_0,j'_1 \in \mathbb{N}\) に対し
\(j'_0 \le \textrm{Joints}(M)_{J_1}\) かつ \(\textrm{TrMax}(M) \le j'_1 \le j_1\) ならば
\((M_j)_{j=j'_0}^{j'_1}\) は簡約である。

### 原文の問題点
前提 \(j'_0 \le \textrm{TrMax}(M)\) が弱すぎ、簡約（標準形に限っても）で偽。反例:

$$M = (0,0)(1,1)(1,0)$$

- \(M\) は標準形かつ簡約（\(\textrm{Red}(M)=M\)）、\(\textrm{TrMax}(M)=1\)。
- \(j'_0=1=\textrm{TrMax}(M) \le j'_1=2 \le j_1=2\) をとると \((M_j)_{j=1}^{2} = (1,1)(1,0)\)。
- \(\textrm{Red}((1,1)(1,0)) = (1,1)(0,0) \neq (1,1)(1,0)\) なので切片は簡約でない。

全数検証（\(\textrm{Lng} \le 5\)、成分 \(\le 2\)）で、原文の前提を満たす 2198 例中 **231 例が偽**。
上界を \(\textrm{Joints}(M)_{J_1}\)（\(\le \textrm{TrMax}(M)\)）に強めると **1592 例で反例 0**。

この上界は姉妹命題「単項性の切片への遺伝性」と同じ形であり、また記事自身が本命題を適用している
箇所（§8.4 の証明）でも \(j'_0 \le \textrm{Joints}(M)_{J_1} \le \textrm{TrMax}(M)\) が満たされている
ので、この強化で記事の他の議論は壊れない。

（補足：\(\textrm{TrMax}\)・\(\textrm{Br}\)・\(\textrm{Joints}\) は単項ペア数列に対して定義されるので、
\(M \in PT_{\textrm{PS}}\) も明示した。）

## A6. §6.7 命題（標準形の単項成分が標準形であること）の証明: 結論が $S_{k-1}$ どまりで、単調性 $S_{k-1}T_{\textrm{PS}} \subseteq S_kT_{\textrm{PS}}$ の補いが要る

### 位置
§6.7 / 命題（標準形の単項成分が標準形であること）**の証明**の末尾
（case $\textrm{Lng}(P(M')_{J_0}) > 1$ の最終文）。命題の主張そのものは**真**であり、訂正は不要。

### 原文
\((P(M')_J)_{J=0}^{J_0-1} \in S_{k_0-1}T_{\textrm{PS}}^{< \omega}\)であり、\(P(M')_{J_0} \in S_{k_0-1}T_{\textrm{PS}}\)より帰納法の仮定から\(P(P(M')_{J_0}[n]) \in S_{k_0-1}T_{\textrm{PS}}^{< \omega}\)であるので、\(P(M) \in S_{k_0-1}T_{\textrm{PS}}^{< \omega}\)である。□

### 訂正案
\((P(M')_J)_{J=0}^{J_0-1} \in S_{k_0-1}T_{\textrm{PS}}^{< \omega}\)であり、\(P(M')_{J_0} \in S_{k_0-1}T_{\textrm{PS}}\)より帰納法の仮定から\(P(P(M')_{J_0}[n]) \in S_{k_0-1}T_{\textrm{PS}}^{< \omega}\)であるので、\(P(M) \in S_{k_0-1}T_{\textrm{PS}}^{< \omega}\)である。ここで任意の\(k \in \mathbb{N}\)に対し\(S_kT_{\textrm{PS}} \subseteq S_{k+1}T_{\textrm{PS}}\)である。実際、任意の\(u \leq v\)に対し\(\textrm{diagSeq}(u,v) = \textrm{Pred}(\textrm{diagSeq}(u,v+1)) = \textrm{diagSeq}(u,v+1)[1]\)であるから\(S_0T_{\textrm{PS}} \subseteq S_1T_{\textrm{PS}}\)であり、一般の\(k\)については\(k\)に関する数学的帰納法から従う。従って\(S_{k_0-1}T_{\textrm{PS}}^{< \omega} \subseteq S_{k_0}T_{\textrm{PS}}^{< \omega}\)であり、\(P(M) \in S_{k_0}T_{\textrm{PS}}^{< \omega}\)である。□

### 原文の問題点
命題の主張は「任意の\(k \in \mathbb{N}\)と\(M \in S_kT_{\textrm{PS}}\)に対し、\(P(M) \in S_kT_{\textrm{PS}}^{< \omega}\)である」であるから、
示すべきは \(P(M) \in S_{k_0}T_{\textrm{PS}}^{<\omega}\) である。しかし証明の結論は \(S_{k_0-1}T_{\textrm{PS}}^{<\omega}\) で
終わっている。\(S_{k_0-1}\) から目標の \(S_{k_0}\) に上げるには階層の単調性
\(S_{k_0-1}T_{\textrm{PS}} \subseteq S_{k_0}T_{\textrm{PS}}\) が要るが、原文はこれを明示も証明もせず暗黙に用いている。

### 単調性 $S_{k}\subseteq S_{k+1}$ は真
証人（base）: 任意の $u \le v$ に対し
$$\textrm{diagSeq}(u,v) = \textrm{Pred}(\textrm{diagSeq}(u,v{+}1)) = (\textrm{diagSeq}(u,v{+}1))[1],\quad \textrm{diagSeq}(u,v{+}1)\in S_0,$$
ゆえ $\textrm{diagSeq}(u,v)\in S_1$。一般の $k$ は帰納で（$N\in S_k \Rightarrow N\in S_{k+1}$ なら $N[n]\in S_{k+2}$）。
したがって $S_k \subseteq S_{k+1}$。（`pss_mechanized.thy: SkT_PS_mono`、`Pred (diagSeq u (Suc v)) = diagSeq u v`
＋`m_5_3_pred_is_oper1: Pred M = M[1]`。）

## A7. §6.8 命題（標準形の切片と Br の降順性の関係）: 「M' が標準形となる」は偽（示すべきは「Br(M') が降順」）

### 位置
§6.8「降順性」, 命題（標準形の切片と $\textrm{Br}$ の降順性の関係）の証明本体
（単項性を示した直後、$k_0$ 帰納を宣言する一文）。

### 原文
$M$ が単項であるという条件下で**$M'$ が標準形となること**を $k_0$ に関する数学的帰納法で示す。

### 訂正案
$M$ が単項であるという条件下で $\textrm{Br}(M')$ が降順となることを $k_0$ に関する数学的帰納法で示す。

### 原文の問題点
この一文は帰納法で示す対象を「$M'$ が標準形（$\in ST_{\textrm{PS}}$）」と述べているが、

- 命題の結論は「$M'$ は単項かつ $\textrm{Br}(M')$ は降順」であって「$M'$ が標準形」ではない。
- 続く base / 各ケースは一貫して「$\textrm{Br}(M')$ は降順である」を結論しており、「$M'$ が標準形」は一度も使われない。
- 実際 $M'$ は標準形とは限らない。**反例（$M$ が単項標準形でも）**: $M = (0,0)(1,1)(2,0) \in ST_{\textrm{PS}}$,
  $j'_0=1,\ j'_1=2$, $(0,1)\le_M(0,2)$ のとき $M' = (1,1)(2,0) \notin ST_{\textrm{PS}}$。

## A8. §6.8 命題（標準形の切片と Br の降順性の関係）: 展開後の末尾添字 j_1 の式の off-by-one [軽微]

### 位置
§6.8「降順性」, 命題（標準形の切片と Br の降順性の関係）の証明本体、
$N_{1,j_1^N}=0$ の場合の冒頭（$M$ をブロック分解する一文）。

### 原文
$M = (N_j)_{j=0}^{j_0^N-1} \bigoplus_{\mathbb{N}^2} ((N_j)_{j=j_0^N}^{j_1^N-1})_{k=0}^{n-1}$ であり、
$j_1 = j_0^N+(n+1)(j_1^N-j_0^N)-1$ である。

### 訂正案
$j_1 = j_0^N + n(j_1^N-j_0^N) - 1$

### 原文の問題点
同じ一文の $M$ の分解は、長さ $j_0^N$ の前半 $(N_j)_{j=0}^{j_0^N-1}$ に続けて、
それぞれ長さ $j_1^N-j_0^N$ のブロック $(N_j)_{j=j_0^N}^{j_1^N-1}$ を $k=0,\dots,n-1$ の **$n$ 個**連結している。
よって $\textrm{Lng}(M) = j_0^N + n(j_1^N-j_0^N)$、$j_1 = \textrm{Lng}(M)-1 = j_0^N + n(j_1^N-j_0^N) - 1$ となり、
係数は $(n+1)$ ではなく **$n$** である。

## A9. §8.2 LastStep の添字 J_1 の範囲外参照 [軽微]

### 位置
§8.2「強単項性」, 写像 LastStep の定義（\(J_1\) を置く一文）。

### 原文
\(J_1 := \textrm{Lng}(\textrm{Br}(M))\)と置く。
\(J_1 = 0\)ならば\(\textrm{LastStep}(M) = 0\)である[58]。
\(J_1 > 0\)とする[59]。
\((\textrm{Br}(M)_{J_1})_{0,0} = (\textrm{Br}(M)_{J_1})_{1,0}\)ならば\(\textrm{LastStep}(M) = J_1\)である[60]。
\((\textrm{Br}(M)_{J_1})_{0,0} > (\textrm{Br}(M)_{J_1})_{1,0}\)ならば\(\textrm{LastStep}(M) := \min \{J \in \mathbb{N} \mid (\textrm{Br}(M)_{J_1})_{0,0} = (\textrm{Br}(M)_J)_{0,0} > (\textrm{Br}(M)_J)_{1,0}\}\)である[61]。

（脚注[61]: 「\(J = J_1\)が条件を満たすため\(\min\)が存在する。」）

### 訂正案
\(\textrm{Lng}(\textrm{Br}(M)) = 0\)ならば\(\textrm{LastStep}(M) = 0\)である[58]。
\(\textrm{Lng}(\textrm{Br}(M)) > 0\)とする[59]。
\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置く。
\((\textrm{Br}(M)_{J_1})_{0,0} = (\textrm{Br}(M)_{J_1})_{1,0}\)ならば\(\textrm{LastStep}(M) = J_1\)である[60]。
\((\textrm{Br}(M)_{J_1})_{0,0} > (\textrm{Br}(M)_{J_1})_{1,0}\)ならば\(\textrm{LastStep}(M) := \min \{J \in \mathbb{N} \mid J \leq J_1 \wedge (\textrm{Br}(M)_{J_1})_{0,0} = (\textrm{Br}(M)_J)_{0,0} > (\textrm{Br}(M)_J)_{1,0}\}\)である[61]。

### 原文の問題点
\(\textrm{Br}(M)\) の添字は \(0,\dots,\textrm{Lng}(\textrm{Br}(M))-1\) の範囲なので、\(J_1 := \textrm{Lng}(\textrm{Br}(M))\) と
置くと \(\textrm{Br}(M)_{J_1}\) は範囲外を参照する。著者が \(J_1\) で**最終成分の添字**を意図していることは
脚注[61]（「\(J = J_1\) が条件を満たすため \(\min\) が存在する」）からも分かる：\(J_1\) が実在する枝の添字で
なければこの脚注は意味を持たない。また「\(J_1 = 0\) ならば」の分岐は \(\textrm{Br}(M) = ()\)（枝が無い）の
意図と読めるので、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\) と置き直すなら空判定を \(\textrm{Lng}(\textrm{Br}(M)) = 0\)
に書き換える必要がある（\(\mathbb{N}\) 上の減算を避けるため）。他の箇所（例：§6.4 や §8.1）では
\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\) と置かれており、ここだけ \(-1\) が落ちている。

### 補足（else 節の \(\min\) の集合の well-formedness）
else 節の \(\min\) の内包 \(\{J \in \mathbb{N} \mid \dots\}\) には添字上界がない。\(\mathbb{N}\) の空でない
部分集合の \(\min\) は常に存在する（脚注[61]の通り \(J = J_1\) が属するので空でない）ので、**有限性は
問題ではない**。問題は集合の **well-formedness** で、\(\textrm{Br}(M)_J\) は \(J < \textrm{Lng}(\textrm{Br}(M))\) の
ときにしか定義されていないため、内包の条件は範囲外の \(J\) に対して意味を持たない。訂正案では束縛変数を
\(J \leq J_1\) に制限し、条件が定義済みの \(J\) のみを見るようにした（\(\min\) の値は変わらない：
\(J_1\) 自身が条件を満たすので、範囲外の元を除いても最小値は不変）。

#### 形式化への影響と実装（2026-07-12）
（以下は**我々の側の事情**であり、原文の欠陥ではない。）我々の Isabelle 形式化は \(\min\) を有限集合を要求する
`Min` で写していたため、範囲制限の無い内包が「（証明不能な）有限性側条件 `fin`」を §8.2 の VE カスケード全体に
引きずり、停止性の柱の残差 **FINRC**（\(\textrm{tvx\_finRc}\)）が約10ラウンド discharge 不能なまま残っていた。

`pss_defs.thy` の `LastStep_def` の \(\min\) 束縛変数に `J < Lng (Br M)` を入れる **root surgery** を実施し、全チェーン（PSS_A/B/C）を再ビルドして green を確認：

- **忠実性（機械検証）**: `ot9_LastStep_A9_faithful` — **旧定義の集合が有限だったとき（＝旧 `min` が well-defined だったとき、すなわち旧 `fin` 仮定が成り立っていた場合すべて）、新旧の \(\textrm{LastStep}\) の値は一致する**。`if` 分岐と \(\textrm{Br}(M)=()\) 分岐は不変。else 分岐では簡約形の host 上で \(J_1\) 自身が有界集合に属し、旧集合が余分に持つ元は全て範囲外（\(\ge \textrm{Lng}(\textrm{Br}(M)) > J_1 \ge \min\)）なので \(\min\) は変わらない。すなわち**値を変えない曖昧性解消**であり、既存の証明済事実は一つも無効化されない。
- **効果**: `fin` 前提は自明に証明可能になり（有界集合の部分集合）、**FINRC が無条件に discharge された**（`ot9_FINRC : "tvx_finRc K"`、仮定ゼロ）。停止性の capstone は FINRC スロットを解消（`oi8_census_FINRC`）。

## A10. §6.5 脚注[19] の死枝の不到達は、それを使って証明される系に依存している（循環）

### 位置
§6.5「簡約化」\(\textrm{Red}\) の再帰的定義（\(M\) が単項・\(M_0 \neq (0,0)\)・\(M_{1,0} > 0\) の場合）の
脚注 **[19]**、命題（単項性と \(\textrm{Red}\) の関係）、および系（直系先祖の \(\textrm{Red}\) 不変性）**の証明**。

### 原文（\(\textrm{Red}\) の定義の当該分岐）
\(M_{1,0} > 0\)とする。
\(N := \textrm{Red}(((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{IncrFirst}^{M_{1,0}}(M))\)と置く[17]。
\(j_1 := \textrm{Lng}(N) - 1\)と置く。
\(M_{1,0} \leq j_1\)かつ\((N_j)_{j=M_{1,0}}^{j_1} \in PT_{\textrm{PS}}\)ならば\(\textrm{Red}(M) := ((N_{0,j}-N_{0,M_{1,0}}+N_{1,M_{1,0}},N_{1,j}))_{j=M_{1,0}}^{j_1}\)である[18]。
\(M_{1,0} \leq j_1\)かつ\((N_j)_{j=M_{1,0}}^{j_1} \in T_{\textrm{PS}} \setminus PT_{\textrm{PS}}\)ならば\(\textrm{Red}(M) := M\)である[19]。
\(M_{1,0} > j_1\)ならば\(\textrm{Red}(M) := M\)である[20]。

### 原文（脚注[19]、それが参照する命題、および系の証明）
[19] 後で証明する単項性と\(\textrm{Red}\)の関係により、この分岐が生じないことが分かる。

命題（単項性と\(\textrm{Red}\)の関係）

任意の\(M \in PT_{\textrm{PS}}\)に対し、\(N := \textrm{Red}(((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{IncrFirst}^{M_{1,0}}(M))\)と置き\(j_1 := \textrm{Lng}(N)-1\)と置くと、\((N_j)_{j=M_{1,0}}^{j_1} \in PT_{\textrm{PS}}\)である。

証明：
\(N\)の定義より、\(\textrm{Lng}(M) = j_1 - M_{1,0} + 1\)でありかつ任意の\((i,j), (i',j') \in \mathbb{N}^2\)に対し以下は同値である：
(1) \((i,j) \leq_M (i',j')\)である。
(2) \((i,j+M_{1,0}) \leq_N (i',j'+M_{1,0})\)である。
従って直系先祖の\(\textrm{Red}\)不変性より従う。□

系（直系先祖の\(\textrm{Red}\)不変性）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\leq_M\)と\(\leq_{\textrm{Red}(M)}\)は一致する。

証明：
\(\textrm{Lng}\)の\(\textrm{Red}\)不変性と\(\textrm{Red}\)の再帰的定義により、\(\textrm{Lng}(M)\)に関する数学帰納法から即座に従う。□

### 訂正案
系（直系先祖の\(\textrm{Red}\)不変性）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\leq_M\)と\(\leq_{\textrm{Red}(M)}\)は一致する（定義域は [[A4]] の通り補正する）。

証明：
\(\textrm{Lng}\)の\(\textrm{Red}\)不変性と\(\textrm{Red}\)の再帰的定義により、\(\textrm{Red}\)の再帰の呼び出し関係に関する整礎帰納法から従う（\(\textrm{Red}\)が well-defined であることから、この呼び出し関係は整礎である）。□

### 原文の問題点（[19] のみ。[20] は循環ではない）
依存を辿ると次のようになる。

- 脚注[19] の分岐が生じないこと（\((N_j)_{j=M_{1,0}}^{j_1} \in PT_{\textrm{PS}}\)）は、命題（単項性と
  \(\textrm{Red}\) の関係）が主張する内容そのものである。
- その命題の証明は系（直系先祖の \(\textrm{Red}\) 不変性）を用いる。
- 系（直系先祖の \(\textrm{Red}\) 不変性）の証明は「\(\textrm{Lng}(M)\) に関する数学帰納法」とされるが、
  いま問題にしている分岐（\(M\) 単項・\(M_0 \neq (0,0)\)・\(M_{1,0} > 0\)）では \(\textrm{Red}\) が呼ぶ引数
  \(((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{IncrFirst}^{M_{1,0}}(M)\) の長さは
  \(M_{1,0} + \textrm{Lng}(M) > \textrm{Lng}(M)\) と**増える**ため、\(\textrm{Lng}\) に関する帰納法の仮定が
  そのままでは適用できない。この帰納法が回るには、当該分岐（＝[19] の分岐）が生じないことを
  既に知っている必要があり、それはまさに [19] が系に依拠して主張している内容である。
- 帰納の測度を \(\textrm{Lng}\) から \(\textrm{Red}\) の再帰の呼び出し関係そのものに取り替えれば、
  [19] の不到達を前提とせずに系が確立し、循環は解ける。命題（単項性と \(\textrm{Red}\) の関係）の
  証明はそのままでよい。
- なお系の主張自体、[[A4]] の通り \(T_{\textrm{PS}}\) 全体では偽である（反例 \(M = ((0,0),(0,2))\)）。

一方、**脚注[20] は循環ではない**。[20] が引く「\(\textrm{Lng}\) の \(\textrm{Red}\) 不変性」は
\(\textrm{Red}\) の全分岐（\(\textrm{Red}(M) := M\) の 2 分岐でも自明に \(\textrm{Lng}\) 不変）で成り立つので、
\(\textrm{Lng}(N) = M_{1,0} + \textrm{Lng}(M)\) すなわち \(j_1 = M_{1,0} + \textrm{Lng}(M) - 1 \geq M_{1,0}\) が
[19]/[20] の不到達を前提とせずに得られる。

## A11. §7.2 命題（scb分解の合成則）(2): 前提に \(c\) が主表現列であることが必要（反例あり） [軽微]

### 位置
§7.2「命題（scb分解の合成則）」の (2)。形式化では `p_7_2_scb_compose` の第2主張に対応する。

### 原文
命題（scb分解の合成則）

任意の\(t \in T_{\textrm{B}}\)に対し、以下が成り立つ：

(2) 任意の\(v \in \mathbb{N}\)と\(s,c,b \in \Sigma^{< \omega}\)に対し、\((s,c,b)\)が\(t\)のscb分解であるならば\((D_v s,c,b)\)は\(D_v t\)のscb分解である。

（scb分解の定義：「\((s,c,b)\)が\(t\)のscb分解であるとは、以下を満たすということである：\(t = scb\)である。**\(t \neq 0\)ならば\(c \in PT_{\textrm{B}}\)である。** \(b\)は\(\underline{)}\)のみからなる文字列である。」）

### 訂正案
(2) 任意の\(v \in \mathbb{N}\)と\(s,c,b \in \Sigma^{< \omega}\)に対し、\(c \in PT_{\textrm{B}}\)かつ\((s,c,b)\)が\(t\)のscb分解であるならば\((D_v s,c,b)\)は\(D_v t\)のscb分解である。

### 原文の問題点
scb分解の定義では、中央成分 \(c\) が主表現（\(c \in PT_{\textrm{B}}\)）であることが要求されるのは
**\(t \neq 0\) のときだけ**である。従って \(t = 0\) のとき、\((s,c,b) = ((),0,())\) は \(0\) の scb分解である
（\(0 = ()\,0\,()\)、\(b\) は空文字列、\(t = 0\) なので \(c \in PT_{\textrm{B}}\) は課されない）。
しかし \(D_v t = D_v 0 \neq 0\) なので、その scb分解には \(c \in PT_{\textrm{B}}\) が要求される。\(c = 0\) は
主表現ではない（主表現の平坦化は必ず \(D\) で始まる）ので、(2) の結論は成り立たない。すなわち
\(t = 0\)、\((s,c,b) = ((),0,())\) が反例である。

\(c \in PT_{\textrm{B}}\)（同値に \(t \neq 0\)）を前提に加えれば (2) は正しい。

### 反例（機械検証）
`pss_mechanized.thy: scbcomp_compose2_counterexample`（\((s,c,b) = ([],[\textrm{Zsym}],[])\)、\(t = 0\)）。
訂正後の形は同ファイルの `scbcomp_compose2_PT` として証明済み。

## A12. §7.2 命題（scb分解の置換可能性）: 選言前提の左側が空項で空回りする（反例あり） [軽微]

### 位置
§7.2「命題（scb分解の置換可能性）」。形式化では `p_7_2_scb_replaceable`。

### 原文
\(c_0, c_1 \in T_{\textrm{B}}\)、\((c_0\) が主表現列でない\() \vee (c_1\) が主表現列\()\)、\(t_0 \in T_{\textrm{B}}\)、\((s, \textrm{flat}(c_0), b)\) が \(t_0\) の scb分解であるとする。このとき \(t_1 \in T_{\textrm{B}}\) が存在して \(\textrm{flat}(t_1) = s\frown\textrm{flat}(c_1)\frown b\) かつ \((s, \textrm{flat}(c_1), b)\) が \(t_1\) の scb分解となる。

### 訂正案
\(c_0, c_1 \in T_{\textrm{B}}\)、\((c_1\) が主表現列\() \vee (s\frown\textrm{flat}(c_1)\frown b = \textrm{flat}(0))\)、\(t_0 \in T_{\textrm{B}}\)、\((s, \textrm{flat}(c_0), b)\) が \(t_0\) の scb分解であるとする。このとき \(t_1 \in T_{\textrm{B}}\) が存在して \(\textrm{flat}(t_1) = s\frown\textrm{flat}(c_1)\frown b\) かつ \((s, \textrm{flat}(c_1), b)\) が \(t_1\) の scb分解となる。

### 原文の問題点
scb分解の定義は「\(t \neq 0\) ならば \(c\) は主表現」なので、主表現条件は対象項が零項のときだけ外れる。
原文の選言前提 \((\neg\textrm{principal}(c_0)) \vee \textrm{principal}(c_1)\) は、\(c_0 = 0\) のとき
**左側だけで成立してしまい、\(c_1\) に何の制約も課さない**。

反例: \(t_0 = c_0 = 0\)（零項）、\(s = b = ()\)、\(c_1 = D_0 0 + D_1 0\)（複項＝非主表現）。前提はすべて成立する。
しかし結論の \(t_1\) は \(\textrm{flat}(t_1) = \textrm{flat}(c_1)\) と flat の単射性から \(t_1 = c_1 \neq 0\) に限られ、
scb分解 \((s,\textrm{flat}(c_1),b)\) は \(c_1\) が主表現であることを要求するが、\(c_1\) は複項なので偽。

訂正案の形（\(c_1\) が主表現、または結果が零項）が正しいことは形式的に確認済み
（`m_7_2_scb_replaceable_corr_mod_image`）。なお選言を落として \(t_0 \neq 0\) を課す形では、
\(c_0\) が主表現・\(c_1\) が複項という反例が残るため不十分である。

## A13. §7.2 系（加法とscb分解の関係）(3): \(D_v(t+c)\) の出現位置と \(c\) の出現位置が同一とは限らない（反例あり） [軽微]

### 位置
§7.2「系（加法とscb分解の関係）」の (3)。形式化では `p_7_2_add_scb` の第3主張。

### 原文
\(c' \in T_{\textrm{B}}\) が主表現、\(u_1 \in T_{\textrm{B}}\)、\(\textrm{flat}(u_1) = s_1 \frown D_v\,\textrm{flat}(t+c) \frown b_1\)、\((s_0, \textrm{flat}(c), b_0)\) が \(u_1\) の scb分解であるとき、ある \(u_1'\) が存在して \(\textrm{flat}(u_1') = s_1 \frown D_v\,\textrm{flat}(t+c') \frown b_1\) かつ \((s_0, \textrm{flat}(c'), b_0)\) が \(u_1'\) の scb分解となる。

### 訂正案
\(c' \in T_{\textrm{B}}\) が主表現、\(u_1 \in T_{\textrm{B}}\)、\(\textrm{flat}(u_1) = s_1 \frown D_v\,\textrm{flat}(t+c) \frown b_1\)、\((s_0, \textrm{flat}(c), b_0)\) が \(u_1\) の scb分解であり、更に \(\textrm{pre}, \textrm{post} \in \Sigma^{< \omega}\) が

- \(\textrm{flat}(t+c) = \textrm{pre} \frown \textrm{flat}(c) \frown \textrm{post}\)、
- \(\textrm{flat}(t+c') = \textrm{pre} \frown \textrm{flat}(c') \frown \textrm{post}\)、
- \(\textrm{post}\) は閉じ括弧 \(\underline{)}\) のみからなる

を満たし、\(s_0 = s_1 \frown D_v \frown \textrm{pre}\) かつ \(b_0 = \textrm{post} \frown b_1\) であるとき、ある \(u_1'\) が存在して \(\textrm{flat}(u_1') = s_1 \frown D_v\,\textrm{flat}(t+c') \frown b_1\) かつ \((s_0, \textrm{flat}(c'), b_0)\) が \(u_1'\) の scb分解となる。

### 原文の問題点
主張は暗黙に「\(s_1 \frown D_v\,\textrm{flat}(t+c) \frown b_1\) が指す \(D_v(t+c)\) の中の \(c\) と、
\((s_0,\textrm{flat}(c),b_0)\) が指す \(c\) が**同一の部分項**」を仮定しているが、これは前提から従わない。
\(u_1\) が \(c\) を複数箇所に持つとき、両者が別の出現を指す配置が成立する。

反例: \(t=0\)、\(c=D_0 0\)、\(c'=D_0(D_0 0)\)、\(v=0\)、\(u_1 = D_0(D_0 0) + D_0 0\)（2主表現）。
\(s_1 \frown D_v\,\textrm{flat}(t+c) \frown b_1\) は**第1**主表現を、\((s_0,\textrm{flat}(c),b_0)\) は**第2**主表現を指す。
結論の \(u_1'\) は \(\textrm{flat}(u_1') = s_1 D_v \textrm{flat}(t+c') b_1\)（第1側の置換）と
\(\textrm{flat}(u_1') = s_0 \textrm{flat}(c') b_0\)（第2側の置換）を同時に満たす必要があるが、
この2文字列は相異なるので flat の単射性より \(u_1'\) は存在しない。

訂正案の整合条件が正しいことは形式的に確認済み（`m_7_2_add_scb_conj3`、layerB）。なお整合条件を
\(s_0 = s_1 \frown D_v\,\textrm{flat}(t)\) と書くのでは足りない——\(t = 0\) のとき余分な \(\underline{0}\) が入り、
\(t\) が主表現や複項のときは括弧 \(\underline{(}\) と \(\underline{,}\) が抜けるため、\(\textrm{flat}\) の連結として
成立しないからである。

## A15. §7.3 命題（Trans の well-defined 性）の証明: 非簡約分岐で \(\textrm{Lng}\) 帰納の測度が下がらない

### 位置
§7.3 \(\textrm{Trans}\)/\(\textrm{Mark}\) の再帰的定義の**非簡約分岐**と、命題（\(\textrm{Trans}\) の well-defined 性）**の証明**。
命題の主張そのものは**真**であり、訂正は証明のみでよい。

### 原文
\(M\)が簡約でないとする。
\(\textrm{Trans}(M) :=　\textrm{Trans}(\textrm{Red}(M))\)である。
\(\textrm{Mark}(M,m) := \textrm{Mark}(\textrm{Red}(M),m)\)である[47]。

命題（\(\textrm{Trans}\)のwell-defined性）

上の条件を全て満たす写像\(\textrm{Trans}\)と\(\textrm{Mark}\)が一意に存在する。

証明：
\(\textrm{Lng}(M)\)に関する数学的帰納法より即座に従う。□

### 訂正案
命題（\(\textrm{Trans}\)のwell-defined性）

上の条件を全て満たす写像\(\textrm{Trans}\)と\(\textrm{Mark}\)が一意に存在する。

証明：
\(\textrm{Lng}(M)\)と\(\textrm{Red}\)の軌道の長さ（\(\textrm{Red}^k(M)\)が\(\textrm{Red}\)の不動点に到達する最小の\(k\)）の対に関する辞書式帰納法より従う。□

### 原文の問題点（証明のみ）
非簡約分岐 \(\textrm{Trans}(M) := \textrm{Trans}(\textrm{Red}(M))\) は \(\textrm{Lng}\) を保つ
（\(\textrm{Lng}\) の \(\textrm{Red}\) 不変性）ので、\(\textrm{Lng}(M)\) に関する帰納法の測度が減らない。
この分岐が 1 回で止まるためには \(\textrm{Red}(M)\) が簡約であること（\(\textrm{Red}\) の冪等性）が要るが、
それは [[A4]]・[[A41]] の通り \(T_{\textrm{PS}}\) 全体では**偽**である（反例 \(M = ((0,0),(0,2))\)）。
従って「\(\textrm{Lng}(M)\) に関する数学的帰納法より即座に従う」だけでは、この分岐で再帰が停止することが
示せていない。\(\textrm{Red}\) の軌道の停止性を測度に併用すれば埋まる。

### 経験的確認
\(\textrm{Trans}\) が \(T_{\textrm{PS}}\) 上で定義できないことの証人は無い。忠実モデルで
\(T_{\textrm{PS}}\) を全数走査（\(\textrm{Lng} \leq 4\)、成分 \(\leq 2\)、7,380 列）したところ、
\(\textrm{Red}\) の軌道は**高々 2 回**の反復で \(\textrm{Red}\) の不動点に到達し、発散は **0 件**だった。
すなわち写像 \(\textrm{Trans}/\textrm{Mark}\) は存在し、欠陥は**主張ではなく証明の測度**にある。

## A16. §7.3 命題（Trans が単項性を保つこと）および (IncrFirst,Red) 不変性 (2) の Σ_B 表示: 先頭 P 成分が零項のとき偽（原文の再帰的定義との内部矛盾）

### 位置
§7.3「命題（\(\textrm{Trans}\) が単項性を保つこと）」(content.md 2358) と「命題（\(\textrm{Trans}\) の \((\textrm{IncrFirst},\textrm{Red})\) 不変 \(P\) 同変性）」(2) の \(\Sigma_{\textrm{B}}\) 表示 (content.md 2236)。形式化では `p_7_3_Trans_monoT` と `p_7_3_Trans_IncrFirst_Red` の (2) 部。

### 原文
任意の $M \in T_{\textrm{PS}}$ に対し、以下は同値である：

(1) $M$ は単項である。

(2) $\textrm{Trans}(M)$ は単項であるか、$P(M)_0$ が零項でありかつ $\textrm{Lng}(P(M)) = 2$ である。

### 訂正案
$M \in RT_{\textrm{PS}}$ かつ $P(M)_0$ が零項でない任意の $M$ に対し、以下は同値である：

(1) $M$ は単項である。

(2) $\textrm{Trans}(M)$ は単項である（$\textrm{Lng}(P_{\textrm{B}}(\textrm{Trans}(M))) = 1$）。

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

### 例外枝を選言で補う形も偽
\(\textrm{monoT}\) の同値を
\[\textrm{monoT}(M) \iff \big(\textrm{Lng}(P_{\textrm{B}}(\textrm{Trans}\,M)) = 1 \,\lor\, (\textrm{zeroT}(P(M)_0) \land \textrm{Lng}(P(M)) = 2)\big)\]
と例外選言つきで書いても**偽**である（`python/_step0_monoT_restricted.py` で reduced 列 maxlen≤5 を全数走査:
**53 反例**。代表 \(M = ((0,0),(0,0),(1,1))\) は複項なのに \(\textrm{Trans}\,M\) が単項で、かつ右選言が真 → 同値が破れる）。
経験的に真であるのは、先頭 P 成分が零項でない場合への制限 iff である（同データで reduced 1269 件・**反例 0**）:
\[M \in RT_{\textrm{PS}} \,\land\, \neg\textrm{zeroT}(P(M)_0) \ \Longrightarrow\ \big(\textrm{monoT}(M) \iff \textrm{Lng}(P_{\textrm{B}}(\textrm{Trans}\,M)) = 1\big).\]
この制限形は `pss_wip.thy` の `m_7_3_Trans_monoT` として**無条件に証明済み**（前提は \(M \in RT_{\textrm{PS}}\) と
\(\neg\textrm{zeroT}(P(M)_0)\) のみ）。順方向は `Trans_PT_single`（単項 ⇒ \(\textrm{Trans}\,M\) 単一主成分）、
逆方向は対偶: 複項枝の \(\textrm{Trans}\,M = \textrm{Trans}(A) +_{\textrm{B}} (\cdots)\) 分解で両被加数が主成分非空
⇒ \(\textrm{Lng}(P_{\textrm{B}}) \ge 2\)。

## A17. §7.3 命題（右端第1基点の Mark の基本性質）ほか §7.3 順序系: 零項基底 \(((0,0))\) での例外（A16 と同根の系統的零項エッジ）

### 位置
§7.3「命題（右端第\(1\)基点の Mark の基本性質）」ほか、Mark の基点・順序を \(D_{M_{1,m}} 0\) 等の主表現で特徴づける §7.3 命題群。形式化では `p_7_3_Mark_rightmost1` 等。

### 原文
命題（右端第\(1\)基点のMarkの基本性質）

任意の\((M,m) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)に対し、\(j_1 := \textrm{Lng}(M) - 1\)と置くと以下は同値である：

(1) \(m = j_1\)である。
(2) \(\textrm{Mark}(M,m) = D_{M_{1,m}} 0\)である。

### 訂正案
任意の\((M,m) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)に対し、\(j_1 := \textrm{Lng}(M) - 1\)と置くと、\(M\)が零項でないならば以下は同値である：

(1) \(m = j_1\)である。
(2) \(\textrm{Mark}(M,m) = D_{M_{1,m}} 0\)である。

### 原文の問題点
\(M = ((0,0))\)（零項、\(\in RT_{\textrm{PS}}\)、\((M,0) \in T_{\textrm{PS}}^{\textrm{Marked}}\)）で \(m = 0 = j_1\)
のとき、\(\textrm{Trans}\)/\(\textrm{Mark}\) の再帰的定義の零項基底分岐（「\(M_0 = (0,0)\)とする。…
\(\textrm{Mark}(M,m) := 0\)である。」）より \(\textrm{Mark}(M,0) = 0\) であって、
\(D_{M_{1,0}} 0 = D_0 0 \neq 0\) ではない。よって (1) は真、(2) は偽となり、同値は成立しない。
\(M\) が零項でないことを課せば正しい（証明中で著者が \(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\) の場合に
帰着させているのと整合する）。

### 経験的確認
忠実モデルで \(\textrm{Mark}(((0,0)),0) = 0 \neq D_0 0\) を確認。ST_PS 閉包で
\((M,m) \in \textrm{Marked}\) を走査したところ、違反は \(M = ((0,0))\) の 1 件のみ（9698/9699 で成立）。
\(\neg\textrm{zeroT}(M)\) を課せば全例で成立。

### メタ観察
§7.3 は \(\textrm{Trans}\)/\(\textrm{Mark}\) の再帰的定義の**零項基底枝**（\(M_0 = (0,0) \Rightarrow 0\)）と、主表現としての \(D_0 0\)（="+1"）の二重性により、零項を明示除外しないと多くの命題が崩れる（[[A16]] 単項性命題、本 A17 基点系）。形式化は一貫して \(\neg\textrm{zeroT}\)／\(RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\) 域で機械化する方針。

## A18. §7.4 系（Mark と \(<_M^{\textrm{NextAdm}}\) の関係）: 仮定の祖先 \(j\) に「\(M\) 許容（\((M,j)\in\textrm{Marked}\)）」を補う必要

### 位置
§7.4「系（$\textrm{Mark}$ と $<_M^{\textrm{NextAdm}}$ の関係）」（形式化では `p_7_4_Mark_nextAdm`）。

### 原文
系（\(\textrm{Mark}\)と\(<_M^{\textrm{NextAdm}}\)の関係）

\(M \in T_{\textrm{PS}}\)とし、\(j_1 := \textrm{Lng}(M) - 1\)と置く。\((0,j_0) <_M^{\textrm{NextAdm}} (0,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在するとする。任意の\(j \in \mathbb{N}\)に対し、\((0,j) \leq_M (0,j_0)\)ならば、一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在し、以下を満たす：

(1) \((s_0,\textrm{Mark}(\textrm{Pred}(M),j_0),b_0)\)は\(\textrm{Mark}(\textrm{Pred}(M),j)\)のscb分解である。
(2) \((s_0,\textrm{Mark}(M,j_0),b_0)\)は\(\textrm{Mark}(M,j)\)のscb分解である。

### 訂正案
\(M \in T_{\textrm{PS}}\)とし、\(j_1 := \textrm{Lng}(M) - 1\)と置く。\((0,j_0) <_M^{\textrm{NextAdm}} (0,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在するとする。任意の\(j \in \mathbb{N}\)に対し、\((0,j) \leq_M (0,j_0)\)かつ\((M,j) \in T_{\textrm{PS}}^{\textrm{Marked}}\)ならば、一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在し、以下を満たす：

(1) \((s_0,\textrm{Mark}(\textrm{Pred}(M),j_0),b_0)\)は\(\textrm{Mark}(\textrm{Pred}(M),j)\)のscb分解である。
(2) \((s_0,\textrm{Mark}(M,j_0),b_0)\)は\(\textrm{Mark}(M,j)\)のscb分解である。

### 原文の問題点
仮定 \((0,j) \leq_M (0,j_0)\)（行 0 の直系先祖関係）は \(j\) の \(M\) 許容性を**含意しない**。
一方 \(\textrm{Mark}\) の定義域は \(T_{\textrm{PS}}^{\textrm{Marked}}\)（\(j\) が \(M\) 許容な対）なので、
結論に現れる \(\textrm{Mark}(M,j)\) が意味を持つためには \((M,j) \in T_{\textrm{PS}}^{\textrm{Marked}}\)
が必要である。

### 経験的確認
簡約列の閉包（`enum_reduced_tiling(maxlen=5,maxe=3)`、長さ\(\ge2\) で 1465 件、全件で \(j_1\) の NextAdm 親が一意）を走査し、\(j_0\) の行0祖先 \(j\le_M j_0\) で \(\neg\textrm{adm}\,M\,j\) となる**反例 25 件**を確認。最小例 \(M=((0,0),(1,1),(2,2),(3,1))\)、\(j_0=2\)、非許容祖先 \(j=1\)（`python/_admj_audit.py`）。よって原文のままでは \(\textrm{Mark}(M,j)\) が定義域外の対象を指す。

## A19. §7.4 命題（Mark が順序関係を保つこと）: 結論 (2) の対が反転している

### 位置
§7.4「命題（$\textrm{Mark}$ が順序関係を保つこと）」(content.md 2466)。

### 原文
$(M,m_0),(M,m_1)\in T_{\textrm{PS}}^{\textrm{Marked}}$ に対し、次は同値である：

- (1) $m_0<m_1$ である。
- (2) $\textrm{Mark}(M,m_1)\neq\textrm{Mark}(M,m_0)$ かつ $(\textrm{Mark}(M,m_1),\textrm{Mark}(M,m_0))\in T_{\textrm{B}}^{\textrm{Marked}}$ である。

### 訂正案
$(M,m_0),(M,m_1)\in T_{\textrm{PS}}^{\textrm{Marked}}$ に対し、次は同値である：

- (1) $m_0<m_1$ である。
- (2) $\textrm{Mark}(M,m_1)\neq\textrm{Mark}(M,m_0)$ かつ $(\textrm{Mark}(M,m_0),\textrm{Mark}(M,m_1))\in T_{\textrm{B}}^{\textrm{Marked}}$ である。

### 原文の問題点
\(T_{\textrm{B}}^{\textrm{Marked}}=\{(t,c)\mid (s,c,b)\,\text{が}\,t\,\text{の scb 分解}\}\)(content.md 1834)は **(whole, block)** の規約(\(c\) は \(t\) の部分=被覆される側、cf. 1936 \((t+c,c)\))。一方 \(\textrm{Mark}(M,m)\) は \(m\) が小さいほど大きい(\(\textrm{Mark}(M,0)=\textrm{Trans}(M)\) 最大、\(\textrm{Mark}(M,j_1)=D_{M_{1,j_1}}0\) 最小)。よって \(m_0<m_1\) では \(\textrm{Mark}(M,m_0)\) が whole、\(\textrm{Mark}(M,m_1)\) が block で、正しい対は \((\textrm{Mark}(M,m_0),\textrm{Mark}(M,m_1))\in T_{\textrm{B}}^{\textrm{Marked}}\)。原文の \((\textrm{Mark}(M,m_1),\textrm{Mark}(M,m_0))\) は **whole と block が逆**。

### 確認(機械証明による)
`Mark_MarkedB_nest`(green): \((M,m),(M,m')\in\textrm{Marked}\wedge m\le m'\wedge M\in RT_{\textrm{PS}}\Rightarrow(\textrm{Mark}\,M\,m,\textrm{Mark}\,M\,m')\in\textrm{MarkedB}\)。すなわち小 index が whole。`MarkedB_antisym`(green)より両向きの nest は項の一致を強制するので、\(m_0<m_1\)(狭義, 像が相異なる)では原文の逆向き対は偽。

## A20. §8.1 補題（条件(I)か(III)の下での c_1 前後の具体表示）part(1): 非簡約な単項切片で「Trans(切片) = c_1」が偽（反例あり）

### 位置
§8.1「補題（条件(I)か(III)の下での $c_1$ 前後の具体表示）」の (1)。

### 原文
補題（条件(I)か(III)の下での\(c_1\)前後の具体表示）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用いると、\(j_0\)が\(M\)許容かつ\(j_1 > 1\)かつ\(M_{1,j_0} \geq M_{1,j_1}\)ならば、以下が成り立つ：

(1) \(t_1 \neq 0\)であり\(M\)は条件(I)か(III)を満たし\(\textrm{Trans}((M_j)_{j=j_0}^{j_1-1}) = c_1 \in PT_{\textrm{B}}\)である。

### 訂正案
(1) \(t_1 \neq 0\)であり\(M\)は条件(I)か(III)を満たし\(c_1 \in PT_{\textrm{B}}\)である。更に\(j_0 < j_1-1\)または\(M_{0,j_0} = M_{1,j_0}\)（すなわち切片\((M_j)_{j=j_0}^{j_1-1}\)が簡約）ならば\(\textrm{Trans}((M_j)_{j=j_0}^{j_1-1}) = c_1\)である。

### 原文の問題点
\(j_0 = j_1-1\)（切片 \((M_j)_{j=j_0}^{j_1-1}\) が単項の \(((M_{0,j_0},M_{1,j_0}))\)）かつ
\(M_{0,j_0} \neq M_{1,j_0}\)（その 1 列切片が簡約でない）のとき、等式
\(\textrm{Trans}((M_j)_{j=j_0}^{j_1-1}) = c_1\) は成り立たない。\(\textrm{Trans}\) は
\((\textrm{IncrFirst},\textrm{Red})\) 不変なので非簡約の 1 列切片を rebase して \(0\) に潰す一方、
\(c_1 = \textrm{Mark}(\textrm{Pred}(M),j_{-1})\) は \(D_{M_{1,j_0}}\) を頭に保つためである。
（\(t_1 \neq 0\)、条件(I)か(III)、\(c_1 \in PT_{\textrm{B}}\) の部分は成立する。）

**最小反例** \(M = ((0,0),(1,0),(2,0)) \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)（条件(I)、\(M_{1,j_1}=0\)）:
\(j_1 = 2,\ j_0 = 1 = j_1-1,\ j_{-1} = 1\)、切片 \(= ((1,0))\)、
\(\textrm{Trans}(((1,0))) = 0\) だが \(c_1 = D_0 0 \neq 0\)。

### 経験的確認（独立検証）
\(RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\) を全数走査（\(\textrm{Lng} = 3..5\)、成分 \(\leq 3\)）し、補題の仮定
（\(j_0\) が \(M\) 許容、\(j_1 > 1\)、\(M_{1,j_0} \geq M_{1,j_1}\)）を満たす **1,010 例**で part(1) の等式を検査:

- 成立 **965 例** / 不成立 **45 例**
- 不成立 45 例は**すべて** \(j_0 = j_1-1\) かつ \(M_{0,j_0} \neq M_{1,j_0}\)（非簡約な 1 列切片）
- 訂正案のガード（\(j_0 < j_1-1\) または \(M_{0,j_0} = M_{1,j_0}\)）が許す例では**違反 0 件**（健全）。
  ただしガードは十分条件であって特徴付けではない：ガード外でも成立する例が 66 件ある
  （\(j_0 = j_1-1\)・非簡約切片でも \(\textrm{Trans}\) と \(c_1\) が一致する場合がある）。

## A21. §8.1 同補題 part(5): 条件(III)のとき基本列ブロックの親 \(j_0^N = j'_0\) が偽

### 位置
§8.1「補題（条件(I)か(III)の下での $c_1$ 前後の具体表示）」(content.md 2923) の (5)(content.md 2945-2947)。

### 原文
$N := (M[n]_j)_{j=0}^{j_0+(n-1)(j_1-j_0)}$ について、$j_0^N = j'_0$（$\textrm{parent}\,N\,0\,(\textrm{Lng}\,N-1) = j'_0$）である。

### 訂正案
$\textrm{transCondI}\,M$ の下で、$N := (M[n]_j)_{j=0}^{j_0+(n-1)(j_1-j_0)}$ について $j_0^N = j'_0$（$\textrm{parent}\,N\,0\,(\textrm{Lng}\,N-1) = j'_0$）である。

### 原文の問題点
part(5) の周期性論法は基本列ブロックが正しい row-0 シフトで複製され \(\textrm{idx}\) が周期境界に乗ることを要し、これは **条件(I)**(\(M_{1,j_1}=0\))でのみ成立。条件(III)では偽。

### 経験的確認(独立検証)
最小反例 \(M = ((0,0),(1,1),(2,1))\)(**条件(III)**)。\(j_1=2,j_0=1\)、一意 next-parent \(j'_0=0\)、\(n=2\) で \(M[2]=((0,0),(1,1),(2,0),(3,1))\)、\(\textrm{idx}=2\)、\(N=((0,0),(1,1),(2,0))\)、\(\textrm{parent}\,N\,0\,2 = 1 \neq 0 = j'_0\)。条件(III)-only 走査で 18/18 が part(5) 違反、条件(I) では 0/26。

## A22. §8.3 補題（第0種型基本列の基本不等式）の右辺添字脱落 [軽微]

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

## A23. §7.1 脚注（[Buc2] による \(([\ ].4)\,(\mathrm{ii})\) の差し替え）の \(x_i\) の定義で \(D_u\) と \(b[\cdot]\) が転置している [軽微]

### 位置
§7.1 Buchholzの表記系、脚注[30]（\(([\ ].4)\,(\mathrm{ii})\) を [Buc2] の規則に差し替える旨の注）。

### 原文（脚注[30]、逐語）
すなわち[Buc1] \(([\ ].4)\) (ii)の場合分けにおいて、各\(i \in \mathbb{N}\)に対し\(x_i\)を「\(i = 0\)ならば\(x_i = D_u 0\)、\(i > 0\)ならば\(x_i = b[D_u x_{i-1}]\)」と定め、\(a[n]\)の定義を\(D_v b[x_n]\)に変えるということである。

### 訂正案
すなわち[Buc1] \(([\ ].4)\) (ii)の場合分けにおいて、各\(i \in \mathbb{N}\)に対し\(x_i\)を「\(i = 0\)ならば\(x_i = D_u 0\)、\(i > 0\)ならば\(x_i = D_u b[x_{i-1}]\)」と定め、\(a[n]\)の定義を\(D_v b[x_n]\)に変えるということである。

### 原文の問題点
\(x_i\) の定義で \(D_u\) と \(b[\cdot]\) の適用順が入れ替わっている（\(b[D_u x_{i-1}]\) ではなく \(D_u b[x_{i-1}]\)）。\(a[n] = D_v b[x_n]\) の方は**印字どおりで正しい**。

印字された組み合わせ（\(x_i = b[D_u x_{i-1}]\) かつ \(a[n] = D_v b[x_n]\)）だと \(b[\cdot]\) が二重に適用され、\(x_n \notin \textrm{dom}(b) = T_u\) となって項が増大し、[Buc1] Lemma 3.2(a)（\(a[z] < a\)）が壊れる（主項 106 例中 3 例しか整合しない。反例 \(a = D_0(D_1 0 + D_1 0)\)）。

一方、訂正案の読み（\(x_i = D_u b[x_{i-1}]\)、\(a[n] = D_v b[x_n]\)）は、文献で流通する Buchholz の基本列
\(\psi_\nu(\beta)[n] = \psi_\nu(\beta[\gamma_n])\)、\(\gamma_0 = \Omega_\mu\)、\(\gamma_{n+1} = \psi_\mu(\beta[\gamma_n])\)
と完全に一致し、Lemma 3.2(a)(b)(c) をすべて満たす。

さらに、**この読みが正しいことは記事自身の記述からも裏づけられる**：

1. §7.2 命題（scb分解と基本列の関係）(2) は、この読みの下で**印字どおり 112/112 で成立**する（\(x_i = b[D_u x_{i-1}]\) と \(a[n] = D_v x_n\) の組み合わせでは非自明ケースで 0/60）。
2. §8.6 の証明が \((D_v 0)[0] = 0\) と \((D_v 0)[D_{v-1} 0] = D_{v-1} 0\) の 2 ケースを挙げているのは、\(a[0] = D_u b[x_0]\)（\(b\) に \(x_0\) を食わせる）という計算そのものである。

（この項目は転置の誤植の指摘であり、[軽微] である。）

## A29. §8.5 補題（条件(V)の下での各種scb分解）part (5) は n=1 で成立しない（証明の基底と不整合）[軽微]

### 位置
§8.5 補題（条件(V)の下での各種scb分解）(content.md 5213) part (5)、およびその証明 (content.md 5267, 5329)

### 原文
(5) \(\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n t_2 (b'_1)^n b_1\) である。

(4) の証明冒頭 (content.md 5267): \(\textrm{Trans}(L_n) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{2n} 0 (b'_1)^{2n} b_1\)

(5) の証明の \(n=1\) の場合 (content.md 5329): \((s'_1 D_{M_{1,j_0}})^{2n-2}\)

### 訂正案
(5) \(n \geq 2\) ならば \(\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n t_2 (b'_1)^n b_1\) であり、\(n = 1\) ならば \(\textrm{Trans}(M[1]) = s_1 D_{M_{1,j_{-1}}} t_2 b_1\) である。

(4) の証明冒頭: \(\textrm{Trans}(L_n) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+1} 0 (b'_1)^{n+1} b_1\)

(5) の証明の \(n=1\) の場合: \((s'_1 D_{M_{1,j_0}})^{0}\)

### 原文の問題点
主張 (5) の指数 \(n\) は \(n \geq 2\) では正しいが、\(n = 1\) では成立しない。実際、\(M[1] = \textrm{Pred}(M)\) であり、原文証明の (5) の基底 (content.md 5329) 自身が
\(\textrm{Trans}(M[1]) = t_1 = s_1 c_1 b_1 = s_1 D_{M_{1,j_{-1}}} t_2 b_1\)（＝指数 \(0\)）
を導いている。すなわち主張の指数（\(n=1\) で \(1\)）と証明の基底（\(0\)）が食い違う。\(n>1\) の場合の証明 (content.md 5337-5347) は指数 \(n\) を正しく導いており、そちらは真である。

証明中の指数の誤記も 2 箇所ある。(4) の証明冒頭の帰納法の主張の \(2n\) は \(n+1\) の誤記である
（statement (4) も証明本体 (5297, 5316) も \(n+1\)）。(5) の証明の \(n=1\) の場合の \(2n-2\) は、
\(n=1\) では値 \(0\) になるが \(n\) の式としては誤りで、単に \(0\) と書くべきである。

### 経験的確認
真正 \(ST_{\textrm{PS}}\) プール（diagSeq 種＋oper 閉包）の条件(V)かつ \(j_0\) 非許容の単項ホスト **32 個（相異なる、非空虚に条件を行使）**、正しい基本列（[[A23]] の訂正後の operB）で：

- \(n = 1\)：原文の指数 \(n\) 形 **0/32**、指数 \(0\) 形 **32/32**。
- \(n = 2,3,4\)：原文の指数 \(n\) 形 **96/96**（＝真）、指数 \(n-1\) 形 **0/96**。
- part (4) の印字（指数 \(n+1\)）は \(n \geq 1\) 全体で **63/63** で真。

（スクリプト `python/_r56_reverify.py`。）

## A30. §8.4 補題（条件(III)～(V)の下での右端の置き換えとTransの関係）part (3) の結論 scb 分解が偽

### 位置
§8.4 補題（条件(III)～(V)の下での右端の置き換えと\(\textrm{Trans}\)の関係）(content.md 4273) part (3)

### 原文
(3) \(j_{-2} < j_0\) かつ \(j_0\) 非 \(M\) 許容的のとき \((s, D_{M_{1,j_0}}(t_2 + D_{M_{1,j_0}} 0), b)\) が \(\textrm{Trans}(L')\) の scb 分解である。

### 訂正案
(3) \(j_{-2} < j_0\) かつ \(j_0\) 非 \(M\) 許容的のとき \((s, D_{M_{1,j_{-2}}} 0, b)\) が \(\textrm{Trans}(L')\) の scb 分解である。

### 原文の問題点
結論は part (2) と同一の \((s, D_{M_{1,j_{-2}}} 0, b)\)（無条件）。原文証明自身の結語（content.md 4371 / 4387）が両場合ともこの形を導いている。長さ勘定により文字どおりの part (3) は part (1) と \((s,b)\) を共有できない。

### 反例
\(M = (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(6,1)\)（\(j_1=7, j_0=5, j_{-2}=j_{-1}=4\)）: 実際の中心は \(\textrm{flat}(D_{M_{1,j_{-2}}} 0)\)。文字どおり形は条件(IV)全40例で 0/40。訂正形 40/40 + 204/204（条件III/V）。

## A31. §8.4 補題（条件(III)～(VI)の下での展開規則の基本性質）part (5-3) は zeroT(Pred N') で偽（ガード欠落）

### 位置
§8.4 補題（条件(III)～(VI)の下での展開規則の基本性質）(content.md 4407) part (5-3)

### 原文
\(\textrm{Trans}(\textrm{Pred}\,N')\) を中心とする scb 分解が存在する。

### 訂正案
\(\textrm{Pred}\,N' \neq \text{()}\)（非零項）のとき、\(\textrm{Trans}(\textrm{Pred}\,N')\) を中心とする scb 分解が存在する。

### 原文の問題点
零項のとき（条件(VI)で \(M_{1,j_{-2}} = 0\)、このとき \(j_{-2} = j_1 - 1\)、\(M[n] = L_{n-1}\)）\(\textrm{Trans}(\textrm{Pred}\,N') = 0_B\) は主項文字列でなく scb 分解の中心になれない。parts (5-1)(5-2) は同領域でも成立（642/642）。

### 反例
\(M = (0,0)(1,1)(2,0)(3,1)\)、\(n=2\): \(\textrm{Trans}(M[2]) = \textrm{flat}(D_0 D_1 D_0 D_0 0)\)、要求される中心 \(\textrm{flat}(0_B) = [Z]\) は isPTB_str を満たさない。zeroT 領域 92/92 で否定、ガード形 550/550 + 46/46。

### 原因
証明の Mark-Trans 表現ステップが印付き切片の非零を要求（`m_7_4_Mark_Trans_repr` と同一のガード）。

## A39. §8.2 写像 LastStep の定義: 最小値をとる集合 \(\{J \in \mathbb{N} \mid \cdots\}\) に添字上界 \(J \le J_1\) が無い（記事内の \(j_0\) の定義と非整合）[軽微]

### 位置
§8.2 写像 \(\textrm{LastStep}\) の定義（content.md 3312）の第3ケース（\((\textrm{Br}(M)_{J_1})_{0,0} > (\textrm{Br}(M)_{J_1})_{1,0}\) の場合）。

### 原文
\((\textrm{Br}(M)_{J_1})_{0,0} > (\textrm{Br}(M)_{J_1})_{1,0}\)ならば\(\textrm{LastStep}(M) := \min \{J \in \mathbb{N} \mid (\textrm{Br}(M)_{J_1})_{0,0} = (\textrm{Br}(M)_J)_{0,0} > (\textrm{Br}(M)_J)_{1,0}\}\)である。

### 訂正案
\((\textrm{Br}(M)_{J_1})_{0,0} > (\textrm{Br}(M)_{J_1})_{1,0}\)ならば\(\textrm{LastStep}(M) := \min \{J \in \mathbb{N} \mid J \le J_1 \wedge (\textrm{Br}(M)_{J_1})_{0,0} = (\textrm{Br}(M)_J)_{0,0} > (\textrm{Br}(M)_J)_{1,0}\}\)である。

### 原文の問題点
集合 \(\{J \in \mathbb{N} \mid \cdots\}\) の \(J\) に上界がなく、\(J > J_1 = \textrm{Lng}(\textrm{Br}(M))-1\) では \(\textrm{Br}(M)_J\) が \(\textrm{Br}(M)\) の添字範囲外を参照する。記事は \(j_0 := \min\{j \in \mathbb{N} \mid 0 < j \le j_1 \wedge (0,j) \le_M (0,j_1)\}\)（content.md 490）では上界 \(j \le j_1\) を明示しており、LastStep の \(\min\) だけ上界を欠くのは非整合。\(J \le J_1\) を補えば集合は \(\{0,\dots,J_1\}\) の部分集合として有限になり（\(J = J_1\) が条件を満たすので非空、脚注[61]）、\(\min\) が明確に存在する。

（形式化 `LastStep`(pss_defs.thy:516) はこの \(\min\) を `Min {J. …}` と転写したが、Isabelle では範囲外 \(J\) で `Br M ! J` が nth-overflow の junk を返し集合が余有限になりうるため `Min`（`Min_le`/`Min_in` が finite 要求）が未定義同然になり、`LastStep M < Lng(Br M)` が `Br M ≠ []` だけからは証明できない。上界 \(J \le J_1\) を課すか、nat 上 total な `LEAST` に替えれば解消する。）

## A40. §5.3 基本列の定義中の型主張 \(G \in T_{PS}\) が \(j_0 = 0\) のとき偽 [軽微]

### 位置
§5.3 基本列（写像 \([\ ]\)）の定義。

### 原文
\(G := (M_j)_{j=0}^{j_0-1} \in T_{\textrm{PS}}\)と置く。

### 訂正案
\(G := (M_j)_{j=0}^{j_0-1} \in T_{\textrm{PS}} \cup \{()\}\)と置く。

### 原文の問題点
\(j_0 = 0\) は実際に起こる（例 \(M = ((0,0),(1,1))\)：\(i_1 = 1\)、\(j_1 = 1\) の親として \(j_0 = 0\) が
一意に存在する）。そのとき記法の約束（\(i_0 > i_1\) のとき \((a_i)_{i=i_0}^{i_1} := ()\)）により
\(G = ()\) となるが、\(T_{\textrm{PS}}\) は空列を含まない（\(T_{\textrm{PS}} = \{M \in \Sigma^{<\omega} \mid M \neq ()\}\)）ので、
型主張 \(G \in T_{\textrm{PS}}\) はこの場合に成り立たない。値そのもの（\(M[n] = G \oplus \cdots\)）は
\(G = ()\) の読みで正しく、以降の議論も影響を受けないので、型主張を \(T_{\textrm{PS}} \cup \{()\}\) に
広げるだけでよい。

## A41. §6.6 「\(RT_{PS} = \textrm{Im}(\textrm{Red})\)」は偽（Red の冪等性が \(T_{PS}\) で偽であるため）

### 位置
§6.6 簡約性の定義直後の注（content.md 1024）。

### 原文
\(RT_{PS} = \textrm{Im}(\textrm{Red})\) である。

### 訂正案
\(RT_{PS} \subseteq \textrm{Im}(\textrm{Red})\) である。

### 原文の問題点
逆の包含 \(\textrm{Im}(\textrm{Red}) \subseteq RT_{PS}\) は \(\textrm{Red}(\textrm{Red}(M)) = \textrm{Red}(M)\)（\(\textrm{Red}\) の冪等性）と同値だが、その冪等性は [[A4]] の通り \(T_{PS}\) 上**偽**である（反例 \(M = ((0,0),(0,2))\)）。[[A4]] は §6.5 の 8 命題を列挙しているが、この無名注は含まれていない。冪等性は簡約性の定義域（標準形または簡約かつ非複項な列の先祖係留切片）に制限して初めて成立する。

## A45. §7.4 命題（$\textrm{Trans}$ と $<_M^{\textrm{NextAdm}}$ の関係）: 定義域が $T_{PS}$ では偽（$RT_{PS}$ に制限が必要）

### 位置
§7.4 許容的親子関係、命題（\(\textrm{Trans}\)と\(<_M^{\textrm{NextAdm}}\)の関係）。形式化では `p_7_4_Trans_nextAdm`。

### 原文
命題（\(\textrm{Trans}\)と\(<_M^{\textrm{NextAdm}}\)の関係）

\(M \in T_{\textrm{PS}}\)とし、\(j_1 := \textrm{Lng}(M) - 1\)と置く。\((0,j_0) <_M^{\textrm{NextAdm}} (0,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在するならば、一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在し、以下を満たす：

(1) \((s_0,\textrm{Mark}(\textrm{Pred}(M),j_0),b_0)\)は\(\textrm{Trans}(\textrm{Pred}(M))\)のscb分解である。

(2) \((s_0,\textrm{Mark}(M,j_0),b_0)\)は\(\textrm{Trans}(M)\)のscb分解である。

### 訂正案
命題（\(\textrm{Trans}\)と\(<_M^{\textrm{NextAdm}}\)の関係）

\(M \in RT_{\textrm{PS}}\)とし、\(j_1 := \textrm{Lng}(M) - 1\)と置く。\((0,j_0) <_M^{\textrm{NextAdm}} (0,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在するならば、一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在し、以下を満たす：

(1) \((s_0,\textrm{Mark}(\textrm{Pred}(M),j_0),b_0)\)は\(\textrm{Trans}(\textrm{Pred}(M))\)のscb分解である。

(2) \((s_0,\textrm{Mark}(M,j_0),b_0)\)は\(\textrm{Trans}(M)\)のscb分解である。

### 原文の問題点
\(M\) が簡約でないとき偽。反例：

$$M = (0,0)(0,1)(1,2)(1,0)$$

$M \in T_{\textrm{PS}}$ は非簡約で、$\textrm{Red}(M) = (0,0)(1,1)(2,2)(2,0) \in RT_{\textrm{PS}}$。
$m = j_0 = 1$、$j_1 = 3$ とすると、$1$ は $M$ 許容かつ $(0,1) \leq_M (0,3)$ なので $(M,1)$ は基点付きであり、
$1$ は $3$ の一意な NextAdm 親でもある（仮定はすべて成立）。しかし
$\textrm{Trans}(\textrm{Pred}(M)) = D_0 D_2 0$、$\textrm{Trans}(M) = D_0(D_2 0 + D_1(D_2 0 + D_0 0))$ であり、
結論が要求する scb 分解の組 $(s_0,b_0)$ は**存在しない**（一意性ではなく存在が破れる）。

根本原因は [[A4]] と同じである：$\textrm{Trans}(M) := \textrm{Trans}(\textrm{Red}(M))$ は簡約後の列で計算されるが、
$\leq_M$ は $\textrm{Red}$ 不変ではない。実際この $M$ では $(0,1) \leq_M (0,3)$ が成立する一方
$(0,1) \leq_{\textrm{Red}(M)} (0,3)$ は成立せず、列 $1$ は $\textrm{Red}(M)$ の基点ですらない。
原文の証明が「\(\textrm{Trans}\)の再帰的定義と直系先祖の\(\textrm{Red}\)不変性から、\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)の場合に帰着される」
としているのは、まさにこの \(\textrm{Red}\) 不変性（[[A4]] により \(T_{\textrm{PS}}\) 上偽）に依拠している。

（悉皆検査（成分 $< 3$、$\textrm{Lng} \le 4$）：反例 33 件、**すべて非簡約**。簡約な $M$ では 224/224 成立。）

## A46. §7.4 系（$\textrm{Trans}$ の $\textrm{Mark}$ と $\textrm{Pred}$ による表示）: 定義域が $T_{PS}$ では偽（$RT_{PS}$ に制限が必要）

### 位置
§7.4 許容的親子関係、系（\(\textrm{Trans}\)の\(\textrm{Mark}\)と\(\textrm{Pred}\)による表示）。形式化では `p_7_4_Trans_Mark_Pred`。

### 原文
系（\(\textrm{Trans}\)の\(\textrm{Mark}\)と\(\textrm{Pred}\)による表示）

任意の\((M,m) \in T_{\textrm{PS}}^{\textrm{Marked}}\)に対し、\(m < \textrm{Lng}(M) - 1\)ならば一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在し、以下を満たす：

(1) \((s_0,\textrm{Mark}(\textrm{Pred}(M),m),b_0)\)は\(\textrm{Trans}(\textrm{Pred}(M))\)のscb分解である。

(2) \((s_0,\textrm{Mark}(M,m),b_0)\)は\(\textrm{Trans}(M)\)のscb分解である。

### 訂正案
系（\(\textrm{Trans}\)の\(\textrm{Mark}\)と\(\textrm{Pred}\)による表示）

任意の\((M,m) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)に対し、\(m < \textrm{Lng}(M) - 1\)ならば一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在し、以下を満たす：

(1) \((s_0,\textrm{Mark}(\textrm{Pred}(M),m),b_0)\)は\(\textrm{Trans}(\textrm{Pred}(M))\)のscb分解である。

(2) \((s_0,\textrm{Mark}(M,m),b_0)\)は\(\textrm{Trans}(M)\)のscb分解である。

### 原文の問題点
[[A45]] と同一の反例 $M = (0,0)(0,1)(1,2)(1,0)$ で偽。$\textrm{Mark}(M,1) = D_0 0$、
$\textrm{Mark}(\textrm{Pred}(M),1) = D_2 0$ となり、両者を同時に scb 分解する $(s_0,b_0)$ が存在しない。
原因は [[A45]] と同じく、基点が簡約後の列から読まれる一方 $\leq_M$ が $\textrm{Red}$ 不変でないこと（[[A4]]）。
（悉皆検査：反例 33 件、すべて非簡約。簡約な $M$ では 224/224 成立。）

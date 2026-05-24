# 原文訂正案 (proposed corrections to tmp/original.html)

巨大数研究 Wiki「ペア数列の停止性」(P進大好きbot 著) の**原文 HTML**
(`tmp/original.html`) に対する訂正案を集約する。著者へのフィードバック用。

- 原文はあくまで HTML（内部の LaTeX ソース）なので、訂正は HTML 内 LaTeX 記述
  に対する修正として記す。
- 位置は `original.html` のバイト位置と、整形テキスト `tmp/content.md` の行番号で示す。
- 形式化（Isabelle）側でどう扱ったかも併記する。
- 数式は MathJax 記法（`$...$` / `$$...$$`）で書く。

---

## A1. §5.4 命題（$F_M$ と基本列の関係）: 再帰先の第2引数 $n$ → $f(n)$

**位置**
- §5.4 ペア数列システム / 命題（$F_M$ と基本列の関係）
- `original.html` byte ≈ 192272（該当数式 $F_M(n) = F_{M[n]}(n)$）
- `content.md` line 380（(2)）, line 382（(3)）

**原文**
- (2) $(M[n],n) \in \textrm{Dom}(F)$
- (3) $(M,n) \in \textrm{Dom}(F)$ かつ $(M[n],n) \in \textrm{Dom}(F)$ かつ $F_M(n) = F_{M[n]}(n)$

**問題点**

§5.4 の $F$ の再帰的定義（`content.md` line 368 = `original.html` byte ≈ 191157）は

$$F_M(n) := F_{M[n]}(f(n))$$

と、再帰先の第2引数が $f(n)$。命題は同じ $n$ を使っており定義と矛盾する。

- 反例: $M = ((0,0),(0,0))$, $f(n)=n+1$, $n=1$。
  - 定義: $F_M(1) = F_{M[1]}(f(1)) = F_{((0,0))}(2) = f(2) = 3$。
  - 命題: $F_M(1) = F_{M[1]}(1) = F_{((0,0))}(1) = f(1) = 2$。
  - よって $3 \neq 2$ で矛盾。
- 補足: $\textrm{Lng}(M)=1$ のときは $M[n]=M$, $F_M(n)=f(n)=F_{M[n]}(n)$ なので原文の
  $n$ が正しい。$\textrm{Lng}(M)>1$ のときに $f(n)$ でなければならない。**単一の固定
  引数では両ケースを両立できない。**

**訂正案**

命題を $\textrm{Lng}(M)>1$ の場合に限定し、第2引数を $f(n)$ にする:
- (2) $(M[n],f(n)) \in \textrm{Dom}(F)$
- (3) $F_M(n) = F_{M[n]}(f(n))$
- （$\textrm{Lng}(M)=1$ の場合は $M[n]=M$ で自明なので除外して差し支えない）

**形式化での扱い**

`pss_paper.thy` の `p_5_4_F_oper_dom` / `p_5_4_F_oper_val` を訂正版
（$\textrm{Lng}\,M > 1$, 第2引数 $f\,n$）で記述し、`pss_mechanized.thy` の
`m_5_4_*` で証明済み。

---

## A2. §6.6 系（直系先祖による切片と $\textrm{Red}$ と $\textrm{IncrFirst}$ の関係）: 指数の添字 $m$ → $j'_0$

**位置**
- §6.6 簡約性 / 系（直系先祖による切片と $\textrm{Red}$ と $\textrm{IncrFirst}$ の関係）
- `content.md` line 1302（命題本文）

**原文**

$(M_j)_{j=j'_0}^{j'_1} = \textrm{IncrFirst}^{M_{0,m} - M_{1,m}}(N)$

**問題点**

ステートメント中の指数 $M_{0,m} - M_{1,m}$ に現れる添字 $m$ は、この系では
未定義（$m$ はこの命題のスコープに導入されていない）。証明本体（`content.md`
line 1308–1316）では一貫して $M_{0,j'_0} - M_{1,j'_0}$ を用いており、$m$ は
$j'_0$ の誤記と判断される。

**訂正案**

$(M_j)_{j=j'_0}^{j'_1} = \textrm{IncrFirst}^{M_{0,j'_0} - M_{1,j'_0}}(N)$

**形式化での扱い**

`pss_paper.thy` の `p_6_6_ancestor_slice_Red_IncrFirst` を訂正版
（指数 $\textrm{entry}\,M\,0\,j'_0 - \textrm{entry}\,M\,1\,j'_0$）で記述。

---

## A3. §6.4 系（$\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性）(4): 偽（反例あり）

**位置**
- §6.4 幹と枝 / 系（$\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性）の主張 (4)
- `content.md` line 791（主張 (4)）、line 793（証明）

**原文**

(4) 任意の $i \in \{0,1\}$ に対し $M_{i,\textrm{Joints}(M)_{J'_0}} > M_{i,\textrm{Joints}(M)_{J'_1}}$ である。

**問題点**

(4) は狭義不等号だが、複数の枝が同一の joint に接続し得るため偽。反例:

$$M = (0,0)(1,1)(2,1)(3,1)(2,0)$$

- $\textrm{TrMax}(M) = 1$、$\textrm{Br}(M) = [\,(2,1)(3,1),\ (2,0)\,]$
- $\textrm{FirstNodes}(M) = [2,4]$、$\textrm{Joints}(M) = [1,1]$
- $J'_0=0 < J'_1=1$ で $M_{i,\textrm{Joints}_0} = M_{i,\textrm{Joints}_1} = M_{i,1}$ なので (4) ($1>1$) は偽。

この $M$ は標準形・単項・簡約・$\textrm{Br}$ 降順（機械的に確認）。(3) は弱い不等号 ($\geq$) のため
(4) の狭義性は従わない。(4) は本文で未使用（下流は (2) の $\geq$、$\textrm{Joints}_J \leq \textrm{TrMax} < \textrm{FirstNodes}_J$、
条件(A) $M_{0,\textrm{Joints}_J}+1 = M_{0,\textrm{FirstNodes}_J}$、$\textrm{Br}$ 降順のみを用いる）。

**訂正案**

(4) を削除（(1)(2)(3) のみ残す）。

**形式化での扱い**

`pss_paper.thy` の `p_6_4_FirstNodes_Joints_mono` を (1)(2)(3) のみに弱め、
`m_6_4_FirstNodes_Joints_mono`（= 既証明 `m_6_4_FirstNodes_Joints_mono_aux`）で discharge。

---

## A4. §6.5 系（直系先祖の $\textrm{Red}$ 不変性）ほか: 前提 $M \in T_{\textrm{PS}}$ は広すぎる（反例あり）

**位置**
- §6.5 簡約化 / 系（直系先祖の $\textrm{Red}$ 不変性）他
- `content.md` line 918（直系先祖の $\textrm{Red}$ 不変性）、line 926（単項性）、
  line 938（$P$ の同変性）、line 976（基本列の可換性）、line 992（許容性）など、
  いずれも前提「任意の $M \in T_{\textrm{PS}}$」

**原文**

系（直系先祖の $\textrm{Red}$ 不変性）: 任意の $M \in T_{\textrm{PS}}$ に対し、$\leq_M$ と
$\leq_{\textrm{Red}(M)}$ は一致する。

**問題点**

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

$T_{\textrm{PS}}$ 全体で偽な系（経験的調査・忠実モデル+yaBMS で確定、`docs/red-le-domain.md`）:
**直系先祖の $\textrm{Red}$ 不変性**、**$\textrm{Red}$ が単項性を保つこと**、**$P$ の $\textrm{Red}$ 同変性**、
**$\textrm{Red}$ の冪等性**（反例 $(0,0)(0,2)$）、**$\textrm{Red}$ と基本列の可換性**。
一方 $\textrm{Lng}$ の $\textrm{Red}$ 不変性・$\textrm{Red}$ が零項性を保つこと・$\textrm{Red}$ と $\textrm{Pred}$ の
可換性・$\textrm{Red}$ の $\textrm{IncrFirst}$ 不変性は $T_{\textrm{PS}}$ 全体で真。

**訂正案（定義域の特定は保留中）**

> ⚠️ 以下は経験的調査による暫定結論で、**証明・確定は保留中**（有界列挙のみ、use-site
> 監査も一部未完）。

これらの系の前提を「**標準形（または簡約かつ単項）の先祖係留切片**」に制限する。すなわち
ある $S \in \textrm{ST}_{\textrm{PS}}$（または $S \in \textrm{RT}_{\textrm{PS}} \cap \textrm{PT}_{\textrm{PS}}$）と
$a \le b$ で $(0,a) \le_S (0,b)$ なるものに対し $M = (S_j)_{j=a}^{b}$ という形に限る
（＝命題「標準形の切片と $\textrm{Br}$ の降順性の関係」(`content.md` line 1422) の前提と同型）。
- 上記5系はこの定義域上で成立（係留切片で失敗 0、`red_anchor2.py`）。
- $\textrm{ST}_{\textrm{PS}}$ への制限だけでは不適切: $\textrm{ST}_{\textrm{PS}} \subset \textrm{RT}_{\textrm{PS}}$
  （標準形は簡約済、line 1348）ゆえ標準形上では $\textrm{Red}=\mathrm{id}$ で系は自明になり、§7 が
  実際に適用する非標準の切片 $N$ を覆えない。
- §7 各使用箇所の $N$ は $(M_j)_{j=lo}^{j_1}$ 型で、$lo$ は $j_1$ の親/先祖/許容先祖
  （$<^{\textrm{NextAdm}}$ が $\le_M$ を含むことより行0係留）＝上記定義域に入る。

**形式化での扱い（保留中）**

当面は補正済み定義域（先祖係留切片）で言明のみ（`sorry`）とし、5系を同様に制限する。
証明は本プロジェクト最難（論文の一行 $\textrm{Lng}$ 帰納は $\textrm{Lng}=2$ で偽となり不成立）。
定義域の最終的な形・閉性・全 use-site の確認は **保留中**。詳細は `docs/red-le-domain.md`。

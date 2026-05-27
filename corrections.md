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

## A1. §5.4 命題（$F_M$ と基本列の関係）: 再帰先の第2引数 $n$ → $f(n)$

**位置**: §5.4 ペア数列システム / 命題（$F_M$ と基本列の関係）（該当数式 $F_M(n) = F_{M[n]}(n)$）

**原文**
- (2) $(M[n],n) \in \textrm{Dom}(F)$
- (3) $(M,n) \in \textrm{Dom}(F)$ かつ $(M[n],n) \in \textrm{Dom}(F)$ かつ $F_M(n) = F_{M[n]}(n)$

**問題点**

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

**位置**: §6.6 簡約性 / 系（直系先祖による切片と $\textrm{Red}$ と $\textrm{IncrFirst}$ の関係）

**原文**

$(M_j)_{j=j'_0}^{j'_1} = \textrm{IncrFirst}^{M_{0,m} - M_{1,m}}(N)$

**問題点**

ステートメント中の指数 $M_{0,m} - M_{1,m}$ に現れる添字 $m$ は、この系では
未定義（$m$ はこの命題のスコープに導入されていない）。証明本体では一貫して
$M_{0,j'_0} - M_{1,j'_0}$ を用いており、$m$ は $j'_0$ の誤記と判断される。

**訂正案**

$(M_j)_{j=j'_0}^{j'_1} = \textrm{IncrFirst}^{M_{0,j'_0} - M_{1,j'_0}}(N)$

**形式化での扱い**

`pss_paper.thy` の `p_6_6_ancestor_slice_Red_IncrFirst` を訂正版
（指数 $\textrm{entry}\,M\,0\,j'_0 - \textrm{entry}\,M\,1\,j'_0$）で記述。

---

## A3. §6.4 系（$\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性）(4): 偽（反例あり）

**位置**: §6.4 幹と枝 / 系（$\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性）の主張 (4)

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

**位置**: §6.5 簡約化 — 系（直系先祖の $\textrm{Red}$ 不変性）・（$\textrm{Red}$ が単項性を保つこと）・
（$P$ の $\textrm{Red}$ 同変性）・（$\textrm{Red}$ と基本列の可換性）・（$\textrm{Red}$ が許容性を保つこと）など、
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

$T_{\textrm{PS}}$ 全体で偽な系（**8 系**、経験的調査・忠実モデル+yaBMS で確定、`docs/red-le-domain.md`）:
**直系先祖の $\textrm{Red}$ 不変性**、**$\textrm{Red}$ が単項性を保つこと**、**$P$ の $\textrm{Red}$ 同変性**、
**$\textrm{Red}$ の冪等性**（反例 $(0,0)(0,2)$）、**$\textrm{Red}$ と基本列の可換性**、
**$\textrm{Red}$ が許容性を保つこと**（反例 $(0,0)(0,1)(0,2)$）、**許容化の $\textrm{Red}$ 不変性**（同）、
**$\textrm{Red}$ が基点を保つこと**（反例 $(0,0)(0,1)(1,2)$）。
一方 $\textrm{Lng}$ の $\textrm{Red}$ 不変性・$\textrm{Red}$ が零項性を保つこと・$\textrm{Red}$ と $\textrm{Pred}$ の
可換性・$\textrm{Red}$ の $\textrm{IncrFirst}$ 不変性は $T_{\textrm{PS}}$ 全体で真。
上記 8 系はいずれも**先祖係留切片**（下記）上では成立（`python/red_anchor2.py`/`red_adm_audit.py`、失敗 0）。

**訂正案（定義域の特定は保留中）**

> ⚠️ 以下は経験的調査による暫定結論で、**証明・確定は保留中**（有界列挙のみ、use-site
> 監査も一部未完）。

これらの系の前提を「**標準形（または簡約かつ単項）の先祖係留切片**」に制限する。すなわち
ある $S \in \textrm{ST}_{\textrm{PS}}$（または $S \in \textrm{RT}_{\textrm{PS}} \cap \textrm{PT}_{\textrm{PS}}$）と
$a \le b$ で $(0,a) \le_S (0,b)$ なるものに対し $M = (S_j)_{j=a}^{b}$ という形に限る
（＝命題「標準形の切片と $\textrm{Br}$ の降順性の関係」の前提と同型）。
- 上記5系はこの定義域上で成立（係留切片で失敗 0、`red_anchor2.py`）。
- $\textrm{ST}_{\textrm{PS}}$ への制限だけでは不適切: $\textrm{ST}_{\textrm{PS}} \subset \textrm{RT}_{\textrm{PS}}$
  （標準形は簡約済）ゆえ標準形上では $\textrm{Red}=\mathrm{id}$ で系は自明になり、§7 が
  実際に適用する非標準の切片 $N$ を覆えない。
- §7 各使用箇所の $N$ は $(M_j)_{j=lo}^{j_1}$ 型で、$lo$ は $j_1$ の親/先祖/許容先祖
  （$<^{\textrm{NextAdm}}$ が $\le_M$ を含むことより行0係留）＝上記定義域に入る。

**形式化での扱い（保留中）**

当面は補正済み定義域（先祖係留切片）で言明のみ（`sorry`）とし、8系を同様に制限する。
証明は本プロジェクト最難（論文の一行 $\textrm{Lng}$ 帰納は $\textrm{Lng}=2$ で偽となり不成立）。
定義域の最終的な形・閉性・全 use-site の確認は **保留中**。詳細は `docs/red-le-domain.md`。

---

## A5. §6.6 命題（簡約性の切片への遺伝性）: 前提 $j'_0 \le \textrm{TrMax}(M)$ は弱すぎる（反例あり）

**位置**: §6.6 簡約性 / 命題（簡約性の切片への遺伝性）

**原文**

任意の $M \in RT_{\textrm{PS}}$ に対し、$j_1 := \textrm{Lng}(M)-1$ と置くと、任意の
$j'_0,j'_1 \in \mathbb{N}$ に対し $j'_0 \le \textrm{TrMax}(M) \le j'_1 \le j_1$ ならば
$(M_j)_{j=j'_0}^{j'_1}$ は簡約である。

**問題点**

前提 $j'_0 \le \textrm{TrMax}(M)$ が弱すぎ、$T_{\textrm{PS}}$（標準形に限っても）で偽。反例:

$$M = (0,0)(1,1)(1,0)$$

- $M$ は標準形（yaBMS で確認）かつ簡約（$\textrm{Red}(M)=M$）、$\textrm{TrMax}(M)=1$。
- $j'_0=1=\textrm{TrMax}(M) \le j'_1=2 \le j_1=2$ をとると $(M_j)_{j=1}^{2} = (1,1)(1,0)$。
- $\textrm{Red}((1,1)(1,0)) = (1,1)(0,0) \neq (1,1)(1,0)$ なので切片は簡約でない。

原因: $j'_0 = \textrm{TrMax}$ だと幹の根（index 0）を落とした切片になり、切片の幹構造が変わる。
証明「$\textrm{Red}$ の再帰的定義と $\textrm{Red}$ と $\textrm{Pred}$ の可換性より即座」も、
$\textrm{Red}$ と $\textrm{Pred}$ の可換性は真だが、それだけでは従わない。

**訂正案（前提の特定は保留中）**

前提を $j'_0 = 0$（幹の根を含む始切片）に強める。経験的調査（忠実モデル、`python/red_66_audit.py`）:
$j'_0 = 0 \le \textrm{TrMax}(M) \le j'_1 \le j_1$ なら全数で成立（失敗0）。$j'_0 \le \textrm{TrMax}$ では
26/7380（うち標準形 11）失敗。最終的な必要十分前提は **保留中**。

**形式化での扱い（保留中）**

`pss_paper.thy` の `p_6_6_reduced_slice` の前提を補正（暫定 $j'_0=0$）。`reduced_oper`・
`P_reduced`・`reduced_iff_cond`（簡約 ⟺ 条件A∧B）・`Red_leftend_1` は $T_{\textrm{PS}}$ 全体で真。

---

## A6. §6.7 命題（標準形の単項成分が標準形であること）: 証明が依拠する単調性補題 $S_{k-1}\subseteq S_k$ の省略

**位置**: §6.7 / 命題（標準形の単項成分が標準形であること）の証明末尾 case
（$\textrm{Lng}(P(M')_{J_0}) > 1$）

**原文（命題）**

任意の $k \in \mathbb{N}$ と $M \in S_kT_{\textrm{PS}}$ に対し、$P(M) \in S_kT_{\textrm{PS}}^{<\omega}$ である。
（命題そのものは**真**。忠実モデルで $k \le 5$・計 3000+ 要素まで違反 0。訂正不要。）

**不足している点**

> $(P(M')_J)_{J=0}^{J_0-1} \in S_{k_0-1}T_{\textrm{PS}}^{<\omega}$ であり、$P(M')_{J_0} \in S_{k_0-1}T_{\textrm{PS}}$
> より帰納法の仮定から $P(P(M')_{J_0}[n]) \in S_{k_0-1}T_{\textrm{PS}}^{<\omega}$ であるので、
> $P(M) \in S_{k_0-1}T_{\textrm{PS}}^{<\omega}$ である。

**帰納法の仮定が与えるのは $S_{k-1}$ どまりで、命題の結論は $S_k$** である（ここで $S_{k_0-1}$ の
$k_0$ は帰納変数であり、設定の $k$ と同一視してよい — 変数名の差であって問題ではない）。先頭部分
$(P(M')_J)_{J<J_0}$ は $P(M')$ の成分なので帰納法の仮定で $\in S_{k-1}$。これを目標の $S_k$ に上げるには
**$S_{k-1} \subseteq S_k$（階層の単調性）が要る**が、原文はこの補題を**明示も証明もしていない**（暗黙に使っている）。

**単調性 $S_{k-1}\subseteq S_k$ は真**

証人（base）: 任意の $u \le v$ に対し
$$\textrm{diagSeq}(u,v) = \textrm{Pred}(\textrm{diagSeq}(u,v{+}1)) = (\textrm{diagSeq}(u,v{+}1))[1],\quad \textrm{diagSeq}(u,v{+}1)\in S_0,$$
ゆえ $\textrm{diagSeq}(u,v)\in S_1$。一般の $k$ は帰納で（$N\in S_k \Rightarrow N\in S_{k+1}$ なら $N[n]\in S_{k+2}$）。
したがって $S_k \subseteq S_{k+1}$。（`pss_mechanized.thy: SkT_PS_mono`、`Pred (diagSeq u (Suc v)) = diagSeq u v`
＋`m_5_3_pred_is_oper1: Pred M = M[1]`。）

**結論：原文証明は本質的に正しく、不足は「単調性補題 $S_{k-1}\subseteq S_k$」のみ**

単調性さえ補えば、先頭部分（$\in S_{k-1}\subseteq S_k$）も末尾（$P(M')_{J_0}\in S_{k-1}\subseteq S_k \Rightarrow P(M')_{J_0}[n]\in S_{k+1}$…
実際は $S_k$ 上の構造帰納）も $S_k$ に収まり、結論 $P(M)\in S_k$ が出る。

**訂正案**

「補題（標準形の階層の単調性）：$S_{k-1}T_{\textrm{PS}} \subseteq S_kT_{\textrm{PS}}$」を
§6.7 に追加（証明は上記対角列拡張）し、当該箇所で先頭部分を $S_{k-1}\subseteq S_k$ により $S_k$ とする一文を補う。
命題の主張は原文どおり（同ランク $S_k$）。

**形式化での扱い**

`SkT_PS_mono`（済）を用いて `pss_paper.thy` の `p_6_7_standard_P_components`（同ランク $S_k$）を、
$k$ × $\textrm{Lng}$ の辞書式帰納で証明する（先頭は単調性、末尾は $\textrm{Lng}$ 減少の内側帰納）。詳細は
`docs/standard-P-components.md`。


## A7. §6.8 命題（標準形の切片と Br の降順性の関係）: 「M' が標準形となる」は偽（示すべきは「Br(M') が降順」）

**所在**: §6.8「降順性」, 命題（標準形の切片と $\textrm{Br}$ の降順性の関係）の証明本体
（単項性を示した直後、$k_0$ 帰納を宣言する一文）。

> $M$ が単項であるという条件下で**$M'$ が標準形となること**を $k_0$ に関する数学的帰納法で示す。

**問題点**: この一文は帰納法で示す対象を「$M'$ が標準形（$\in ST_{\textrm{PS}}$）」と述べているが、

- 命題の結論は「$M'$ は単項かつ $\textrm{Br}(M')$ は降順」であって「$M'$ が標準形」ではない。
- 続く base / 各ケースは一貫して「$\textrm{Br}(M')$ は降順である」を結論しており、「$M'$ が標準形」は一度も使われない。
- 実際 $M'$ は標準形とは限らない。**反例（$M$ が単項標準形でも）**: $M = (0,0)(1,1)(2,0) \in ST_{\textrm{PS}}$,
  $j'_0=1,\ j'_1=2$, $(0,1)\le_M(0,2)$ のとき $M' = (1,1)(2,0) \notin ST_{\textrm{PS}}$。

**訂正案**: 「$M'$ が標準形となること」を「$\textrm{Br}(M')$ が降順となること」に修正（単項性は直前で別途証明済）。
$M'\in ST_{\textrm{PS}}$ は成り立たないので、降順性を「$M'$ が標準形」へ帰着させる経路は使えず、原文どおり
$k_0$ 帰納＋$\textrm{Br}$-under-oper 分解を要する。

**形式化での扱い**: `monoT(seg M j0' j1')`（`m_6_2_mono_ancestor_slice`）と `descending(Br ...)` の行0部
（`m_6_4_P_leftend_mono` を枝セグメント $\in T_{\textrm{PS}}$ に適用）は確保済。残るは Br 成分の行1 tie-break
（$k$ 帰納＋Br-under-oper、設計 `docs/slice-Br-descending.md`）。


## A8. §6.8 命題（標準形の切片と Br の降順性の関係）: 展開後の末尾添字 j_1 の式の off-by-one

**所在**: §6.8「降順性」, 命題（標準形の切片と Br の降順性の関係）の証明本体、
$N_{1,j_1^N}=0$ の場合の冒頭（$M$ をブロック分解する一文）。

> $M = (N_j)_{j=0}^{j_0^N-1} \bigoplus_{\mathbb{N}^2} ((N_j)_{j=j_0^N}^{j_1^N-1})_{k=0}^{n-1}$ であり、
> $j_1 = j_0^N+(n+1)(j_1^N-j_0^N)-1$ である。

**問題点**: 同じ一文の $M$ の分解は、長さ $j_0^N$ の前半 $(N_j)_{j=0}^{j_0^N-1}$ に続けて、
それぞれ長さ $j_1^N-j_0^N$ のブロック $(N_j)_{j=j_0^N}^{j_1^N-1}$ を $k=0,\dots,n-1$ の **$n$ 個**連結している。
よって $\textrm{Lng}(M) = j_0^N + n(j_1^N-j_0^N)$、$j_1 = \textrm{Lng}(M)-1 = j_0^N + n(j_1^N-j_0^N) - 1$ となり、
係数は $(n+1)$ ではなく **$n$** である。

**訂正案**: $j_1 = j_0^N + n(j_1^N-j_0^N) - 1$ に修正（係数 $(n+1)\to n$）。

**形式化での扱い**: 当方の `oper`（$M[n] = \textrm{take}\,j_0\,M \mathbin{@} \textrm{concat}(\textrm{map}(\lambda k.\,\cdots)[0..<n])$、
yaBMS で経験的検証済）はブロック $n$ 個でこの訂正後の式と一致する（`oper_d0zero_expand`）。


## A9. §8.2 LastStep の添字 J_1 の範囲外参照

**所在**: §8.2「強単項性」, 写像 LastStep の定義（\(J_1\) を置く一文）。

> \(J_1 := \textrm{Lng}(\textrm{Br}(M))\)と置く。… \((\textrm{Br}(M)_{J_1})_{0,0} = (\textrm{Br}(M)_{J_1})_{1,0}\)ならば…

**問題点**: \(\textrm{Br}(M)\) の添字は \(0,\dots,\textrm{Lng}(\textrm{Br}(M))-1\) の範囲。\(J_1 := \textrm{Lng}(\textrm{Br}(M))\) と置くと \(\textrm{Br}(M)_{J_1}\) は範囲外。直後の「\(J_1 = 0\) ならば」も \(\textrm{Lng}(\textrm{Br}(M)) = 0\)（\(\textrm{Br}(M)\) が空）の意図と読め、\(J_1\) は最終成分の添字 \(\textrm{Lng}(\textrm{Br}(M))-1\) を指すべき。

**訂正案**: \(J_1 := \textrm{Lng}(\textrm{Br}(M)) - 1\)（他の命題の \(J_1\) と同じ規約）。空の場合分けは「\(\textrm{Br}(M) = ()\) ならば \(\textrm{LastStep}(M) = 0\)」とする。

**形式化での扱い**: `LastStep`（pss_defs §8）は `Br M = []` で `0`、それ以外は `J1 = Lng(Br M)-1` を最終添字として定義（訂正後と一致）。

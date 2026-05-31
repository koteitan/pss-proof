mw-parser-output" lang="ja" dir="ltr">

## Contents

- 1 概要

- 2 序文

- 3 参考文献

- 4 記法

- 5 定式化

- 5.1 親子関係

- 5.2 前者関数

- 5.3 基本列

- 5.4 ペア数列システム

- 6 ペア数列の基本性質

- 6.1 最上行のインクリメント

- 6.2 単項性

- 6.3 許容性

- 6.4 幹と枝

- 6.5 簡約化

- 6.6 簡約性

- 6.7 標準形

- 6.8 降順性

- 7 Buchholzの表記系への翻訳

- 7.1 Buchholzの表記系

- 7.2 scb分解

- 7.3 翻訳写像

- 7.4 許容的親子関係

- 8 停止性

- 8.1 条件(I)の下での展開規則

- 8.2 強単項性

- 8.3 条件(II)の下での展開規則

- 8.4 条件(III)か(IV)の下での展開規則

- 8.5 条件(V)の下での展開規則

- 8.6 条件(VI)の下での展開規則

- 8.7 主結果

- 9 謝辞

- 10 脚注

# 概要[]

ペア数列の停止性を示す。より正確には、数あるペア数列システムのうち１つの定式化を記述し、その中で標準形という概念を定義し、標準形のペア数列システムが停止することを証明する[1]。

# 序文[]

バシク行列システムは巨大数を研究する世界中の多くの人を魅了した巨大数生成法であり様々な亜種が作られ続けているが、オリジナルのバシク行列システム自体は固定した厳密な定義を持たず、従って停止性も一切証明されていない。バシク行列システムを取り巻く歴史的背景についてはSummary on historical background of BMSを参考にすると良い。

バシク行列システムを\(1\)行の行列（つまりベクトル）だけに制限した原始数列システムに関しては先人の度重なる議論によりほぼ万人に共通の定式化が築き上げられており、単純な木構造を用いた整列順序を用いて停止性と近似的な解析がなされている[2]。一方でバシク行列システムを\(2\)行の行列までに制限したものがペア数列システムであり、その標準形と呼ばれる部分システムに関しては既に停止性の反例が挙がっているものを除いて停止性が強く信じられているだけで、その証明はもちろん知られておらず証明できたとしても順序数崩壊関数を用いた極めて非自明な議論を要することが想像に難くない。この記事の目標は、新たに標準形のペア数列システムの停止性を証明することである。

バシク行列システムに多くの亜種があることから、ペア数列システムという用語が指す具体的なアルゴリズムは一義的でない。厳密にペア数列システムの解析を行うためには、まずペア数列システムの定義を１つ固定しなければ始まらないため、2018/8/20時点でのkoteitan分類法のBM1.1, 2, 2.3, 3.1, 3.２に合わせて定式化する。

Buchholzの\(\psi\)関数はBuchholzによって性質が十分に調べられていて使いやすいのでここではBuchholzの\(\psi\)関数を用いるが、ペア数列とBuchholzの\(\psi\)関数はそこまできれいに対応しないのでかなり記述が煩雑になる点が不満である。BMSの表記に特化しているだろうBashicu's OCFやUNOCFといった順序数崩壊関数を使えばきっともっと短く解析できるのかもしれないが、Bashicu's OCFとUNOCFもオリジナルのバシク行列システム同様明示的な定義を書かれたことがないため、正確な定義を必要とする厳密な証明には用いることが出来ない。もう１つの方向性としては、Bashicu's OCFの原型とされるMadoreの\(\psi\)関数を自己流に多変数化してそれを用いることが有力だろう。ただしその場合はその新たな順序数崩壊関数の性質（特に具体的な表記がどの順序数に対応するか）を自分で調べて証明しなければ解析に用いても表記限界を既知の順序数として表せないことに変わりはないので、それだったらやはり既に基本性質が証明されているBuchholzの\(\psi\)関数を用いる方が結局手早いかもしれない。

停止性の証明の方針は以下の通りである：

- （通常の意味での標準形より広い）標準形という概念を導入し、更に広い簡約という概念を導入する。

- 簡約とは限らないペア数列に対して簡約化\(\textrm{Red}\)という操作を定義する。

- 簡約ペア数列からBuchholzの表記系への写像\(\textrm{Trans}\)を定義し、\(\textrm{Red}\)を用いて簡約とは限らないペア数列へ定義を拡張する。

- \(\textrm{Trans}\)の部分文字列の計算補助として\(\textrm{Mark}\)という写像を定義する。

- \(\textrm{Mark}\)がペア数列の部分列の\(\textrm{Trans}\)で計算できることを示す。

- これによりペア数列の\(\textrm{Trans}\)の部分文字列を元のペア数列の部分列の\(\textrm{Trans}\)を用いて計算できる。

- 簡約ペア数列の部分列は簡約とは限らないため、簡約ペア数列にしか興味がない場合でも簡約でないペア数列を用いる必要があった。

- 標準形とは限らないペア数列を標準形に置き換える操作は不明であるので、標準形にしか興味が無い場合も標準形でないペア数列を用いる必要があった。
definition nextR :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
- ペア数列の展開規則と\(\textrm{Trans}\)による像の基本列を比較する。

- これにより、標準形ペア数列の\(\textrm{Trans}\)による像がBuchholzの順序数項を定めることを示す。

- 更にBuchholzの順序数項が標準的な全順序に関して整礎であることと基本列がその順序に関して降下することから、標準形ペア数列システムの停止性が従う。

方針の概説も参考にすると良い。

なお\(n \in \mathbb{N}\)に対する命題\(P(n), Q(n)\)に対して「任意の\(n \in \mathbb{N}\)に対し\(P(n) \to Q(n)\)」を\(n\)に関する数学的帰納法で示す際に、\(P(0)\)が成り立たない場合は\(P(0) \to Q(0)\)が成り立つので「任意の\(n \in \mathbb{N}\)に対し\(P(n) \to Q(n)\)ならば\(P(n+1) \to Q(n+1)\)」を示すだけで良いのだが、読者の理解の助けになるようになるべく記事中では\(P(n_0)\)が成り立つ最小の\(n_0 \in \mathbb{N}\)を調べて\(Q(n_0)\)も示すようにする。

# 参考文献[]

- [Buc1] W. Buchholz, A new system of proof-theoretic ordinal functions, Annals of Pure and Applied Logic, Volume 32, 1986, pp. 195--207.

- [Buc2] W. Buchholz, Relating ordinals to proofs in a prespicious way, unpublished article.
`Trans` / `Mark`. The well-foundedness of `(OT_B, <)` ([Buc1] Lemma 2.2) is the
# 記法[]

\(\mathbb{N}\)で非負整数全体の集合を表し、\(\mathbb{N}_{+}\)で正整数全体の集合を表す。

クラス\(A\)に対し、集合\(a\)が\(A\)値配列であるとは、ある\(n \in \mathbb{N}\)が存在して\(a \in A^n\)ということである。このような\(n\)は\(a\)に対して一意であるので\(\textrm{Lng}(a)\)と表す。\(\textrm{Lng}(a) = 0\)の時、\(A\)に紛れのない限り\(a\)を\(()\)と表す。\(i < \textrm{Lng}(a)\)を満たす各\(i \in \mathbb{N}\)に対し、\(a\)の第\(i\)成分を\(a_i \in A\)と表す。

\(i_0 \leq i_1\)を満たす各\(i_0,i_1 \in \mathbb{N}\)と、\(\{i \in \mathbb{N} \mid i_0 \leq i \leq i_1\}\)を定義域に含む各\(A\)値関数\(f\)に対し、長さが\(i_1-i_0+1\)であって任意の\(i \in \mathbb{N}\)に対し\(i \leq i_1-i_0\)ならば第\(i\)成分が\(f(i_0+i)\)であるような\(A\)値配列を\((f(i))_{i=i_0}^{i_1}\)と表す。\(i_0 \leq i_1\)を満たさないかまたは\(\{i \in \mathbb{N} \mid i_0 \leq i \leq i_1\}\)を\(f\)が定義域に含まないような各\(i_0,i_1 \in \mathbb{N}\)と各\(A\)値関数\(f\)に対し、\((a_i)_{i=i_0}^{i_1} := ()\)と置く。
- **Lemma 2.1** (`<` strict linear order: irreflexive / transitive / trichotomous)
クラス\(A\)に対し、\(A\)値配列全体のクラスを\(A^{< \omega}\)と置き、\(A^{< \omega}\)上の二項演算
\begin{eqnarray*}
\oplus_A \colon (A^{< \omega})^2 & \to & A^{< \omega} \\
(a,b) & \mapsto & a \oplus_A b
\end{eqnarray*}
を以下のように定める：

- \(j_0 := \textrm{Lng}(a) - 1\)と置く。

- \(j_1 := j_0 + \textrm{Lng}(b)\)と置く。

- \(j \leq j_0\)を満たす各\(j \in \mathbb{N}\)に対し、\(c_j := a_j\)と置く。

- \(j_0 < j \leq j_1\)を満たす各\(j \in \mathbb{N}\)に対し、\(c_j = b_{j - j_0 - 1}\)と置く。

- \(a \oplus_A b := (c_j)_{j=0}^{j_1}\)である。

\(\oplus_A\)は結合的であるため、\(\oplus_A\)の反復的適用において省略可能なカッコは省略する。

写像
\begin{eqnarray*}
\bigoplus_A \colon (A^{< \omega})^{< \omega} & \to & A^{< \omega} \\
a & \mapsto & \bigoplus_A a
\end{eqnarray*}
を以下のように再帰的に定める：

- \(j_1 := \textrm{Lng}(a) - 1\)と置く。

- \(j_1 = -1\)ならば\(\bigoplus_A a := ()\)である。

- \(j_1 = 0\)ならば\(\bigoplus_A a := a_0\)である。

- \(j_1 > 0\)ならば\(\bigoplus_A a := \left( \bigoplus_A (a_i)_{i=0}^{j_1-1} \right) \oplus_A a_{j_1}\)である。

何らかの条件を満たす配列の一意存在性を示す際、一意性が文字列の末尾または先頭からの比較により即座に従う場合は一意性の存在を省略する。

# 定式化[]

集合\(M\)がペア数列であるとは、\(M\)が\(()\)でない\(\mathbb{N}^2\)値配列であるということである。\(i \in \{0,1\}\)と\(\textrm{Lng}(M)\)未満の\(j \in \mathbb{N}\)の組\((i,j)\)全体の集合を\(\textrm{Idx}(M)\)と置く。各\((i,j) \in \textrm{Idx}(M)\)に対し、\((M_j)_i\)を\(M_{i,j}\)と置く。

ペア数列全体の集合を\(T_{\textrm{PS}}\)と置く。

## 親子関係[]

\(M \in T_{\textrm{PS}}\)とする。\(\mathbb{Z}^2\)上の二項関係\(<_M^{\textrm{Next}}\)と\(\leq_M\)を以下のように同時に再帰的に定義する。

- \((i_0,j_0), (i_1,j_1) \in \mathbb{Z}^2\)に対し、\((i_0,j_0)  <_M^{\textrm{Next}} (i_1,j_1)\)であるとは、以下を満たすということである：

- \((i_0,j_0),(i_1,j_1) \in \textrm{Idx}(M)\)である。

- \(i_0 = i_1\)である。

- \(j_0 < j_1\)である。

- \(M_{i_0,j_0} < M_{i_1,j_1}\)である。

- \(i_0 = 0\)ならば、任意の\(j \in \mathbb{N}\)に対し、\(j_0 < j < j_1\)ならば\(M_{0,j} \geq M_{0,j_1}\)である。

- \(i_0 = 1\)ならば、\((0,j_0) \leq_M (0,j_1)\)かつ任意の\(j \in \mathbb{N}\)に対し、\(j_0 < j\)かつ\((0,j) \leq_M (0,j_1)\)ならば\(M_{1,j} \geq M_{1,j_1}\)である。

- \((i_0,j_0) \leq_M (i_1,j_1)\)であるとは、以下を満たすということである：

- \((i_0,j_0),(i_1,j_1) \in \textrm{Idx}(M)\)である。

- \(i_0 = i_1\)である。

- ある\(a \in \mathbb{N}^{< \omega}\)が存在し、\(J := \textrm{Lng}(a) - 1\)と置くと以下を満たす：

- \(a \neq ()\)である。

- \(a_0 = j_0\)である。

- 任意の\(k \in \mathbb{N}\)に対し、\(k < J\)ならば\((i_0,a_k) <_M^{\textrm{Next}}(i_1,a_{k+1})\)である。

- \(a_J = j_1\)である。

命題（親の存在の判定条件）

任意の\(M \in T_{\textrm{PS}}\)と\(j_0,j_1 \in \mathbb{N}\)に対し、\(j_0 < j_1 < \textrm{Lng}(M)\)ならば以下が成り立つ：

(1) \(M_{0,j_0} < M_{0,j_1}\)ならば、ある\(j \in \mathbb{N}\)が存在して\(j_0 \leq j < j_1\)かつ\((0,j) <_M^{\textrm{Next}} (0,j_1)\)である。

(2) \(M_{1,j_0} < M_{1,j_1}\)かつ\((0,j_0) \leq_M (0,j_1)\)ならば、ある\(j \in \mathbb{N}\)が存在して\(j_0 \leq j < j_1\)かつ\((1,j) <_M^{\textrm{Next}} (1,j_1)\)である。

(3) 条件「任意の\(j \in \mathbb{N}\)に対し\(j_0 < j \leq j_1\)ならば\(M_{0,j_0} < M_{0,j}\)である」を満たすならば、\((0,j_0) \leq_M (0,j_1)\)である。

(4) 条件「任意の\(j \in \mathbb{N}\)に対し\(j_0 < j\)かつ\((0,j) \leq_M (0,j_1)\)ならば\(M_{1,j_0} < M_{1,j}\)である」と\((0,j_0) \leq_M (0,j_1)\)を満たすならば、\((1,j_0) \leq_M (1,j_1)\)である。

証明：

(1) 仮定より\(j < j_1\)かつ\(M_{0,j} < M_{0,j_1}\)を満たす最大の\(j \in \mathbb{N}\)が存在し、その最大性から\(j_0 \leq j < j_1\)かつ\((0,j) <_M^{\textrm{Next}} (0,j_1)\)である。

(2) 仮定より\(M_{1,j} < M_{1,j_1}\)かつ\((0,j) \leq_M (0,j_1)\)を満たす最大の\(j \in \mathbb{N}\)が存在し、その最大性から\(j_0 \leq j < j_1\)かつ\((1,j) <_M^{\textrm{Next}} (1,j_1)\)である。

(3) 仮定と(1)よりある\(j \in \mathbb{N}\)が存在して\(j_0 \leq j < j_1\)かつ\((0,j) <_M^{\textrm{Next}} (0,j_1)\)である。従って\(j_1\)に関する数学的帰納法より従う。

(3) 仮定と(2)よりある\(j \in \mathbb{N}\)が存在して\(j_0 \leq j < j_1\)かつ\((1,j) <_M^{\textrm{Next}} (1,j_1)\)である。従って\(j_1\)に関する数学的帰納法より従う。□

命題（親の基本性質）

任意の\(M \in T_{\textrm{PS}}\)と\(j_0,j,j_1 \in \mathbb{N}\)に対し、\(j_0 < j \leq j_1\)ならば以下が成り立つ：

(1) \((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)ならば\(M_{0,j} \geq M_{0,j_1}\)である。

(2) \((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)かつ\((0,j) \leq_M (0,j_1)\)ならば\(M_{1,j} \geq M_{1,j_1}\)である。

証明：

(1) 成り立たないと仮定して矛盾を導く。仮定より\(j_0 < j \leq j_1\)かつ\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)かつ\(M_{0,j} < M_{0,j_1}\)を満たす\(j_0,j,j_1 \in \mathbb{N}\)が存在する。そのような\((j_0,j,j_1)\)の組み合わせにおいて\(j < \textrm{Lng}(M)\)であるため、\(j\)が最大となる組み合わせ\((j_0,j,j_1)\)が存在し、それを\((j'_0,j',j'_1)\)と置く。

\(j'\)の最大性から、任意の\(j \in \mathbb{N}\)に対し\(j' < j \leq j'_1\)ならば\(M_{0,j} \geq M_{0,j'_1}\)である。従って\((0,j') <_M^{\textrm{Next}} (0,j'_1)\)となるが、これは\(j'_0 < j'\)に反する。

(2) 成り立たないと仮定して矛盾を導く。仮定より\(j_0 < j \leq j_1\)かつ\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)かつ\((0,j) \leq_M (0,j_1)\)かつ\(M_{1,j} < M_{1,j_1}\)を満たす\(j_0,j,j_1 \in \mathbb{N}\)が存在する。そのような\((j_0,j,j_1)\)の組み合わせにおいて\(j < \textrm{Lng}(M)\)であるため、\(j\)が最大となる組み合わせ\((j_0,j,j_1)\)が存在し、それを\((j'_0,j',j'_1)\)と置く。

\(j'\)の最大性から、任意の\(j \in \mathbb{N}\)に対し\(j' < j \leq j'_1\)かつ\((0,j) \leq_M (0,j'_1)\)ならば\(M_{1,j} \geq M_{1,j'_1}\)である。従って\((1,j') <_M^{\textrm{Next}} (1,j'_1)\)となるが、これは\(j'_0 < j'\)に反する。□

系（直系先祖の基本性質）
  assumes "(M, m) \<in> Marked" "j0' \<le> m" "m \<le> j1'" "j1' \<le> Lng M - 1"
任意の\(M \in T_{\textrm{PS}}\)と\(j_0,j,j_1 \in \mathbb{N}\)に対し、\(j_0 < j \leq j_1\)ならば以下が成り立つ：

(1) \((0,j_0) \leq_M (0,j_1)\)ならば\(M_{0,j_0} < M_{0,j}\)である。

(2) \((1,j_0) \leq_M (1,j_1)\)かつ\((0,j) \leq_M (0,j_1)\)ならば\(M_{1,j_0} < M_{1,j}\)である。

証明：

親の基本性質から、\(\leq_M\)の定義における\(J\)に関する数学的帰納法より即座に従う。□

系（直系先祖の木構造）

任意の\(M \in T_{\textrm{PS}}\)と\(j'_0, j, j'_1 \in \mathbb{N}\)に対し、以下が成り立つ：

(1) \((0,j'_0) \leq_M (0,j'_1)\)かつ\(j'_0 \leq j \leq j'_1\)ならば、\((0,j'_0) \leq_M (0,j)\)である。

(2) \((1,j'_0) \leq_M (1,j'_1)\)かつ\(j'_0 \leq j\)かつ\((0,j) \leq_M (0,j'_1)\)ならば、\((1,j'_0) \leq_M (1,j)\)である。

証明：

(1) 親の存在の判定条件 (3)と直系先祖の基本性質 (1)から即座に従う。

(2) 親の存在の判定条件 (4)と直系先祖の基本性質 (2)から即座に従う。□

## 前者関数[]

写像
\begin{eqnarray*}
\textrm{Pred} \colon T_{\textrm{PS}} & \to & T_{\textrm{PS}} \\
M & \mapsto & \textrm{Pred}(M)
\end{eqnarray*}
を以下のように定める：

- \(j_1 := \textrm{Lng}(M)-1\)と置く。

- \(j_1 = 0\)ならば\(\textrm{Pred}(M) := M\)である。

- \(j_1 > 0\)ならば\(\textrm{Pred}(M) := (M_j)_{j=0}^{j_1-1}\)である。

まだ順序数表記系の構造を与えていないが、\(\textrm{Pred}\)は\(\emptyset\)に対しては\(\emptyset\)を、後続順序数に対してその最大元を取る操作に対応する。

写像
definition adm :: "pairseq \<Rightarrow> nat \<Rightarrow> bool" where
\textrm{Derp} \colon T_{\textrm{PS}} & \to & T_{\textrm{PS}} \cup \{()\} \\
M & \mapsto & \textrm{Derp}(M)
\end{eqnarray*}
を以下のように定める：
definition AdmSet :: "pairseq \<Rightarrow> nat set" where
- \(j_1 := \textrm{Lng}(M)-1\)と置く。

- \(\textrm{Derp}(M) := (M_j)_{j=1}^{j_1}\)である。

\(\textrm{Derp}\)には順序数の操作に関連する意味が特にないが、後に導入する\(\textrm{Red}\)という写像を定義するために便利なので一度だけ用いる。

## 基本列[]

写像
\begin{eqnarray*}
\textrm{operator}[] \colon T_{\textrm{PS}} \times \mathbb{N}_{+} & \to & T_{\textrm{PS}} \\
(M,n) & \mapsto & M[n]
\end{eqnarray*}
を以下のように再帰的に定める：

- \(j_1 := \textrm{Lng}(M)-1\)と置く。

- \(j_1 = 0\)ならば\(M[n] := M\)である。

- \(j_1 > 0\)とする。

- \(M_{j_1} = (0,0)\)ならば\(M[n] := \textrm{Pred}(M)\)である。

- \(M_{j_1} \neq (0,0)\)とする。

- \(i_1 := \max \{i \in \{0,1\} \mid M_{i,j_1} > 0\}\)と置く[3]。

- \((i_1,j_0) <_M^{\textrm{Next}} (i_1,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在しないならば\(M[n] := \textrm{Pred}(M)\)である。

- \((i_1,j_0) <_M^{\textrm{Next}} (i_1,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在するとする。

- \(i < i_1\)を満たす各\(i \in \mathbb{N}\)に対し、\(\delta_i := M_{i,j_1} - M_{i,j_0}\)と置く。

- \(i \geq i_1\)を満たす各\(i \in \mathbb{N}\)に対し、\(\delta_i := 0\)と置く。

- \(G := (M_j)_{j=0}^{j_0-1} \in T_{\textrm{PS}}\)と置く。

- \(B := (((M_{0,j} + k \delta_0, M_{1,j} + k \delta_1))_{j=j_0}^{j_1-1})_{k=0}^{n-1} \in T_{\textrm{PS}}^n\)と置く。

- \(M[n] := \left(G \oplus_{\mathbb{N}^2} \left( \bigoplus_{\mathbb{N}^2} B \right) \right)\)である。

まだ順序数表記系の構造を与えていないが、\(\textrm{operator}[]\)は\(\emptyset\)に対しては\(\emptyset\)を、後続順序数に関してはその最大元を、極限順序数に対してはその基本列を与える操作に対応する。

命題\(\textrm{Pred}\)が\([1]\)で表されること）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\textrm{Lng}(M) > 1\)ならば\(\textrm{Pred}(M) = M[1]\)である。

証明：

\(\textrm{operator}[]\)の定義から即座に従う。□

## ペア数列システム[]

写像\(f \colon \mathbb{N}_{+} \to \mathbb{N}_{+}\)を１つ固定する。主に\(f(n) = n+1\)か\(f(n) = n^2\)である。

\(T_{\textrm{PS}} \times \mathbb{N}_{+}\)上の部分写像
\begin{eqnarray*}
F \colon (M,n) \mapsto F_M(n)
\end{eqnarray*}
を以下ように再帰的に定める：

- \(j_1 := \textrm{Lng}(M)-1\)と置く。

- \(j_1 = 0\)ならば\(F_M(n) := f(n)\)である。

- \(j_1 > 0\)とする。

- \(M_{j_1} = (0,0)\)ならば\(F_M(n) := F_{\textrm{Pred}(M)}(f(n))\)である。

- \(M_{j_1} \neq (0,0)\)とする。

- \(i_1 := \max \{i \in \{0,1\} \mid M_{i,j_1} > 0\}\)と置く[4]。

- \((i_1,j_0) <_M^{\textrm{Next}} (i_1,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在しないならば\(F_M(n) := F_{\textrm{Pred}(M)}(f(n))\)である。

- \((i_1,j_0) <_M^{\textrm{Next}} (i_1,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在するならば\(F_M(n) := F_{M[n]}(f(n))\)である。

ペア数列自体は元々ペア数列数という１つの数として定義されているだけなのでペア数列システムという概念はバシク行列のバージョンを固定しても人によって微妙にずれがある。上記もその１つの例に過ぎないが、この記事で示すことは基本的にどのペア数列システムの解釈でも通用するので、この定式化自体に深い意味はないことに注意する。

\(F\)の定義域を\(\textrm{Dom}(F) \subset T_{\textrm{PS}} \times \mathbb{N}_{+}\)と置く。

命題（\(F_M\)と基本列の関係）

任意の\((M,n) \in T_{\textrm{PS}} \times \mathbb{N}_{+}\)に対し、以下は同値である：

(1) \((M,n) \in \textrm{Dom}(F)\)である。

(2) \((M[n],n) \in \textrm{Dom}(F)\)である。

(3) \((M,n) \in \textrm{Dom}(F)\)かつ\((M[n],n) \in \textrm{Dom}(F)\)かつ\(F_M(n) = F_{M[n]}(n)\)である。

証明：

\(\textrm{Pred}\)を用いた\(\textrm{operator}[]\)の定義と\(F\)の再帰的定義より即座に従う。□

# ペア数列の基本性質[]

後に定義する標準形のペア数列システムの停止性を証明するための準備として、ペア数列からBuchholzの表記系への翻訳写像\(\textrm{Trans}\)を定めるための準備として、ペア数列の基本操作や基本性質を調べる。

## 最上行のインクリメント[]

写像
\begin{eqnarray*}
\textrm{IncrFirst} \colon T_{\textrm{PS}} & \to & T_{\textrm{PS}} \\
M & \mapsto & \textrm{IncrFirst}(M)
\end{eqnarray*}
を以下のように定める：

- \(j_1 := \textrm{Lng}(M)-1\)と置く。

- \(\textrm{IncrFirst}(M) := ((M_{0,j}+1,M_{1,j}))_{j=0}^{j_1}\)である。

命題（\(\leq_M\)の\(\textrm{IncrFirst}\)不変性）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\leq_M\)と\(\leq_{\textrm{IncrFirst}(M)}\)は一致する。

証明：

\(\leq_M\)の定義より即座に従う。□

## 単項性[]

\(M \in T_{\textrm{PS}}\)とする。

- \(j_1 := \textrm{Lng}(M)-1\)と置く。

- \(M\)が零項であるとは、以下を満たすということである：

- \(j_1= 0\)である。

- \(M_{1,0} = 0\)である。

- \(M\)が単項であるとは、以下を満たすということである：

- \(M\)は零項でない。

- \((0,0) \leq_M (0,j_1)\)である。

- \(M\)が複項であるとは、以下を満たすということである：

- \(M\)は零項でない。

- \(M\)は単項でない

- 零項ペア数列全体の部分集合を\(ZT_{\textrm{PS}} \subset T_{\textrm{PS}}\)と置く。

- 単項ペア数列全体の部分集合を\(PT_{\textrm{PS}} \subset T_{\textrm{PS}}\)と置く。

- 複項ペア数列全体の部分集合を\(MT_{\textrm{PS}} \subset T_{\textrm{PS}}\)と置く。

命題（複項性の判定条件）
  shows "(Red M, m) \<in> Marked"
任意の\(M \in T_{\textrm{PS}}\)に対し、以下は同値である：

(1) \(M\)は複項でない。

(2) 任意の\(j \in \mathbb{N}\)に対し、\(0 < j < \textrm{Lng}(M)\)ならば\(M_{0,0} < M_{0,j}\)である。

(3) \((0,0) \leq_M (0,j_1)\)である。

証明：

(2)と(3)の同値性は親の存在の判定条件 (3)と直系先祖の基本性質 (1)より従う。

(1)が成り立つならば、\(\textrm{Lng}(M) = 1\)であるかまたは\((0,0) \leq_M (0,j_0)\)であるので、直系先祖の基本性質 (1)より(2)が成り立つ。

(2)が成り立つならば、\(\textrm{Lng}(M) = 1\)ならば\(M\)は複項でなく、\(\textrm{Lng}(M) > 1\)ならば親の存在の判定条件 (3)より\((0,0) \leq_M (0,j_1)\)であるため\(M\)は単項であるので、(1)が成り立つ。□

系（単項性の始切片への遺伝性）

任意の\(M \in PT_{\textrm{PS}}\)と\(j_0 \in \mathbb{N}\)に対し、\(0 < j_0 < \textrm{Lng}(M)\)ならば\((M_j)_{j=0}^{j_0}\)は単項である。

証明：

単項性の定義より、複項性の判定条件から即座に従う。□

命題（単項性の直系先祖による切片への遺伝性）

任意の\(M \in T_{\textrm{PS}}\)と\(j'_0,j'_1 \in \mathbb{N}\)に対し、\(j'_0 < j'_1\)かつ\((0,j'_0) \leq_M (0,j'_1)\)ならば\((M_j)_{j=j'_0}^{j'_1}\)は単項である。
  \<open>(i,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>NextAdm (i,j\<^sub>1)\<close> (§7.4): \<open>(i,j\<^sub>0) \<le>\<^sub>M (i,j\<^sub>1)\<close>, \<open>j\<^sub>0 < j\<^sub>1\<close>,
証明：

\(M' := (M_j)_{j=j'_0}^{j'_1}\)と置く。任意の\(j \in \mathbb{N}\)に対し\(0 < j \leq j'_1-j'_0\)を満たすならば、直系先祖の基本性質 (1)と\((0,j'_0) \leq_M (0,j'_1)\)より\(M'_{0,0} = M_{0,j'_0} < M_{0,j'_0+j} = M'_{0,j}\)である。従って親の存在の判定条件 (3)より\((0,0) \leq_{M'} (0,j'_1-j'_0)\)である。\(\textrm{Lng}(M') = j'_1 - j'_0 > 0\)であるので、\(M'\)は零項でない。以上より\(M'\)は単項である。□

写像
\begin{eqnarray*}
P \colon T_{\textrm{PS}} & \to & T_{\textrm{PS}}^{< \omega} \\
M & \mapsto & P(M)
補題（順序数項の共終数の遺伝性）
を以下のように再帰的に定める：

- \(M\)が零項または単項ならば\(P(M) := (M)\)である。

- \(M\)が複項とする。

- \(j_1 := \textrm{Lng}(M) - 1\)と置く。

- \(j_0 := \min \{j \in \mathbb{N} \mid 0 < j \leq j_1 \wedge (0,j) \leq_M (0,j_1)\}\)と置く[5]。

- \(P(M) := P((M_j)_{j=0}^{j_0-1}) \oplus_{T_{\textrm{PS}}} (M_j)_{j=j_0}^{j_1}\)である。

\(P\)の再帰的定義から\(P(M) \neq ()\)である。

命題（\(P\)の\(\textrm{IncrFirst}\)同変性）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(J_1 := \textrm{Lng}(P(M))-1\)と置くと、\(P(\textrm{IncrFirst}(M)) = (\textrm{IncrFirst}(P(M)_J))_{J=0}^{J_1}\)である。

証明：

\(\leq_M\)の\(\textrm{IncrFirst}\)不変性より即座に従う。□

命題（\(P\)の各成分の非複項性）

任意の\(M \in T_{\textrm{PS}}\)に対し、以下が成り立つ：

(1) \(P(M)\)の各成分は零項か単項である。

(2) \(M\)が複項である必要十分条件は\(\textrm{Lng}(P(M)) > 1\)である。

証明：

\(P\)の再帰的定義から\(\textrm{Lng}(M)\)に関する数学的帰納法より即座に従う。□

命題（\(P\)の加法性）

任意の\(M \in T_{\textrm{PS}}\)と\(j_0 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(0 < j_0 \leq j_1\)とし、任意の\(j \in \mathbb{N}\)に対し\(j < j_0\)ならば\(M_{0,j} \geq M_{0,j_0}\)であるとすると、\(P(M) = P((M_j)_{j=0}^{j_0-1}) \oplus_{T_{\textrm{PS}}} P((M_j)_{j=j_0}^{j_1})\)である。

証明：

\(j'_0 := \min \{j \in \mathbb{N} \mid (0,j) \leq_M (0,j_1)\}\)と置く[6]。

任意の\(j \in \mathbb{N}\)に対し\(j < j_0\)ならば\(M_{0,j} \geq M_{0,j_0}\)であることから、直系先祖の基本性質 (1)より\(0 < j_0 \leq j'_0\)である。従って\(P\)の定義より\(P(M) = P((M_j)_{j=0}^{j'_0-1}) \oplus_{\mathbb{N}^2} ((M_j)_{j=j'_0}^{j_1})\)かつ\(P((M_j)_{j=j'_0}^{j_1}) = ((M_j)_{j=j'_0}^{j_1})\)であるので、\(P(M) = P((M_j)_{j=0}^{j'_0-1}) \oplus_{\mathbb{N}^2} P((M_j)_{j=j'_0}^{j_1})\)となる。

\(j'_0\)の定義と親の存在の判定条件より、任意の\(j \in \mathbb{N}\)に対し、\(j < j'_0\)ならば\(M_{0,j} \geq M_{0,j'_0}\)である。

\(j'_0-j_0\)と\(j_0\)の辞書式順序に関する数学的帰納法で示す[7]。

\(j'_0-j_0 = 0\)とする。

\begin{eqnarray*}
P(M) = P((M_j)_{j=0}^{j'_0-1}) \oplus_{\mathbb{N}^2} P((M_j)_{j=j'_0}^{j_1}) = P((M_j)_{j=0}^{j_0-1}) \oplus_{\mathbb{N}^2} P((M_j)_{j=j_0}^{j_1})
\end{eqnarray*}

である。

\(j'_0-j_0 > 0\)とする。

帰納法の仮定より\(P((M_j)_{j=0}^{j'_0-1}) = P((M_j)_{j=0}^{j_0-1}) \oplus_{T_{\textrm{PS}}} P((M_j)_{j=j_0}^{j'_0-1})\)かつ\(P((M_j)_{j=j_0}^{j_1}) = P((M_j)_{j=j_0}^{j'_0-1}) \oplus_{T_{\textrm{PS}}} P((M_j)_{j=j'_0}^{j_1})\)であり、従って

\begin{eqnarray*}
& & P(M) = P((M_j)_{j=0}^{j'_0-1}) \oplus_{\mathbb{N}^2} P((M_j)_{j=j'_0}^{j_1}) = P((M_j)_{j=0}^{j_0-1}) \oplus_{T_{\textrm{PS}}} P((M_j)_{j=j_0}^{j'_0-1}) \oplus_{\mathbb{N}^2} P((M_j)_{j=j'_0}^{j_1}) \\
& = & P((M_j)_{j=0}^{j_0-1}) \oplus_{\mathbb{N}^2} P((M_j)_{j=j_0}^{j_1})
\end{eqnarray*}

である。□

命題（\(P\)と基本列の関係）

任意の\(M \in T_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(J_1 := \textrm{Lng}(P(M))-1\)と置くと以下が成り立つ：

(1) \(\textrm{Lng}(P(M)_{J_1}) = 1\)ならば\(M[n] = \textrm{Pred}(M)\)であり、更に\(J_1 = 0\)か否かに従って\(P(M[n]) = (M[n])\)または\(P(M[n]) = (P(M)_J)_{J=0}^{J_1-1}\)である。

(2) \(\textrm{Lng}(P(M)_{J_1}) > 1\)ならば\(M[n] = (\bigoplus_{\mathbb{N}^2} (P(M)_J)_{J=0}^{J_1-1}) \oplus_{\mathbb{N}^2} P(M)_{J_1}[n]\)かつ\(P(M[n]) = (P(M)_J)_{J=0}^{J_1-1} \oplus_{T_{\textrm{PS}}} P(P(M)_{J_1}[n])\)である。

証明：

(1)は\(\textrm{operator}[]\)の定義と単項性の始切片への遺伝性から即座に従う。

(2)は\((P(M)_{J_1})_0 = P(M)_{J_1}[n]_0\)より\(P\)の再帰的定義から即座に従う。□

命題（非複項性と基本列の関係）

任意の\(M \in T_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置くと、\(M\)が複項でないならば以下が成り立つ：

(1) \((0,0) <_M^{\textrm{Next}} (0,j_1)\)かつ\(M_{1,j_1} = 0\)ならば、\(P(M[n]) = (\textrm{Pred}(M))_{k=0}^{n-1}\)である。

(2) \((0,0) <_M^{\textrm{Next}} (0,j_1)\)でないまたは\(M_{1,j_1} > 0\)ならば、\(P(M[n]) = (M[n])\)である。

証明：

(1) \(M[n] = \bigoplus_{\mathbb{N}^2} (\textrm{Pred}(M))_{k=0}^{n-1}\)であり、単項性の始切片への遺伝性より\(\textrm{Pred}(M)\)は複項でない。従って\(P\)の加法性から、\(n\)に関する数学的帰納法により従う。

(2) \(M\)は複項でないので、複項性の判定条件から任意の\(j \in \mathbb{N}\)に対し\(0 < j \leq j_1\)ならば\(M[n]_{0,0} = M_{0,0} < M_{0,j}\)である、

\((0,0) <_M^{\textrm{Next}} (0,j_1)\)でなくかつ\(M_{1,j_1} = 0\)ならば、任意の\(j \in \mathbb{N}\)に対し\(0 < j < \textrm{Lng}(M[n])\)ならば\(M[n]_{0,j}\)は\((M_{0,j})_{j=1}^{j_1}\)のいずれかの成分であるので\(M[n]_{0,0} < M[n]_{0,j}\)となる。

\(M_{1,j_1} > 0\)ならば、任意の\(j \in \mathbb{N}\)に対し\(0 < j < \textrm{Lng}(M[n])\)ならば\(M[n]_{0,j}\)は\((M_{0,j})_{j=1}^{j_1}\)のいずれかの成分に\(n\)未満の自然数を足したものなので\(M[n]_{0,0} < M[n]_{0,j}\)となる。

従っていずれの場合も複項性の判定条件より\(M[n]\)は複項でなく、\(P\)の各成分の非複項性 (2)より\(P(M[n]) = (M[n])\)である。□

## 許容性[]

\(M \in T_{\textrm{PS}}\)とし、\(j \in \mathbb{N}\)とする。

- \(j_1 := \textrm{Lng}(M)\)と置く。

- \(j\)が非\(M\)許容であるとは、以下のいずれかを満たすということである：

section \<open>§7 Buchholz の表記系への翻訳\<close>

- \((1,j-1) <_M^{\textrm{Next}} (1,j) <_M^{\textrm{Next}} (1,j+1)\)である。
  The Buchholz notation system, transcribed from the cited reference
- \(j\)が\(M\)許容であるとは、\(j\)が非\(M\)許容でないということである。

- \(M\)許容である自然数全体のなす部分集合を\(\mathbb{N}_M \subset \mathbb{N}\)と置く。

命題（許容性の切片への遺伝性）

任意の\(M \in T_{\textrm{PS}}\)と\(j'_0, j_0, j'_1 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M) - 1\)と置き、\(j'_0 \leq j_0 \leq j'_1 \leq j_1\)とし\(N := (M_j)_{j=j'_0}^{j'_1}\)と置くと、以下は同値である：

(1) \(j_0\)が\(M\)許容であるまたは\(j'_0 = j_0\)または\(j_0 = j'_1\)である。

(2) \(j_0-j'_0\)が\(N\)許容である。

証明：

\(j'_0 = j'_0\)または\(j_0 = j'_1\)または\(j'_1 = j_1\)ならば、許容性の定義より従う。以下\(j'_0 < j_0 < j'_1 < j_1\)とする。

\(j'_0 < j_0 < j'_1\)より、\((1,j_0-1) <_M^{\textrm{Next}} (1,j_0) <_M^{\textrm{Next}} (1,j_0+1)\)でないことと\((1,j_0-j'_0-1) <_N^{\textrm{Next}} (1,j_0-j'_0) <_N^{\textrm{Next}} (1,j_0-j'_0+1)\)でないことは同値である。従って\(j_0\)の\(M\)許容性と\(j_0-j'_0\)の\(N\)許容性は同値である。□

\begin{eqnarray*}
\textrm{Adm}_M \colon T_{\textrm{PS}} \times \mathbb{N} & \to & \mathbb{N}_M \\
(M,j) & \mapsto & \textrm{Adm}_M(j)
\end{eqnarray*}
を以下のように定める：

- \(j\)が\(M\)許容ならば、\(\textrm{Adm}_M(j) := j\)である。

- \(j\)は非\(M\)許容ならば、\(\textrm{Adm}_M(j) := \max \{j' \in \mathbb{N}_M \mid j' < j\}\)と置く[8]。

命題（許容化の切片への遺伝性）

任意の\(M \in T_{\textrm{PS}}\)と\(j'_0,j'_1 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M) - 1\)と置き、\(j'_0 \leq \textrm{Adm}_M(j_0)\)かつ\(j_0 < j'_1 \leq j_1\)とし\(N := (M_j)_{j=j'_0}^{j'_1}\)と置くと、\(\textrm{Adm}_N(j_0-j'_0) = \textrm{Adm}_M(j_0)-j'_0\)である。

証明：

\(\textrm{Adm}_N(j_0-j'_0) \leq j_0-j'_0 < j_1-j'_0\)かつ\(j'_0 \leq \textrm{Adm}_M(j_0) \leq j_0 < j_1\)と許容性の切片への遺伝性より、\(\textrm{Adm}_N(j_0-j'_0)\)と\(\textrm{Adm}_M(j_0)-j'_0\)が\(N\)許容かつ\(\textrm{Adm}_M(j_0)\)が\(M\)許容である。従って\(\textrm{Adm}_N(j_0-j'_0)\)の最大性から\(\textrm{Adm}_N(j_0-j'_0) \geq \textrm{Adm}_M(j_0)-j'_0\)である。

\(\textrm{Adm}_M(j_0) < \textrm{Adm}_N(j_0-j'_0)+j'_0\)と仮定し矛盾を導く。

\(\textrm{Adm}_M(j_0) < \textrm{Adm}_N(j_0-j'_0)+j'_0 \leq (j_0-j'_0)+j'_0 = j_0\)より\((1,\textrm{Adm}_N(j_0-j'_0)+j'_0-1) <_M^{\textrm{Next}} (1,\textrm{Adm}_N(j_0-j'_0)+j'_0)\)であり、\(j'_0 \leq \textrm{Adm}_M(j_0) < \textrm{Adm}_N(j_0-j'_0)+j'_0\)より\((1,\textrm{Adm}_N(j_0-j'_0)-1) <_N^{\textrm{Next}} (1,\textrm{Adm}_N(j_0-j'_0))\)となる。

従って\(\textrm{Adm}_N(j_0-j'_0)\)の\(N\)許容性から\((1,\textrm{Adm}_N(j_0-j'_0)) <_N^{\textrm{Next}} (1,\textrm{Adm}_N(j_0-j'_0)+1)\)でなく、\((1,\textrm{Adm}_N(j_0-j'_0)+j'_0) <_M^{\textrm{Next}} (1,\textrm{Adm}_N(j_0-j'_0)+j'_0+1)\)でない。再度\(\textrm{Adm}_M(j_0) < \textrm{Adm}_N(j_0-j'_0)+j'_0 \leq j_0\)より\(\textrm{Adm}_N(j_0-j'_0)+j'_0 = j_0\)となる。

すると許容性の切片への遺伝性と\(j_0 < j_1\)から\(j_0\)が\(M\)許容となるので\(\textrm{Adm}_M(j_0) = j_0\)であり、これは\(\textrm{Adm}_M(j_0) < \textrm{Adm}_N(j_0-j'_0)+j'_0 \leq j_0\)に反する。

以上より\(\textrm{Adm}_M(j_0) = \textrm{Adm}_N(j_0-j'_0)+j'_0\)である。□

\((M,m) \in T_{\textrm{PS}} \times \mathbb{N}\)とする。

- \((M,m)\)が基点付きペア数列であるとは、\(j_1 := \textrm{Lng}(M)-1\)と置くと以下を満たすということである：

- \(m\)は\(M\)許容である。

- \((0,m) \leq_M (0,j_1)\)である。

- 基点付きペア数列全体の部分集合を\(T_{\textrm{PS}}^{\textrm{Marked}} \subset T_{\textrm{PS}} \times \mathbb{N}\)と置く。

- \(RT_{\textrm{PS}}^{\textrm{Marked}} := \{(M,m) \in T_{\textrm{PS}}^{\textrm{Marked}} \mid M \in RT_{\textrm{PS}}\}\)である。

命題（基点の切片への遺伝性）

任意の\((M,m) \in T_{\textrm{PS}}^{\textrm{Marked}}\)と\(j'_0,j'_1 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M) - 1\)と置くと、\(j'_0 \leq m \leq j'_1 \leq j_1\)ならば\(((M_j)_{j=j'_0}^{j'_1},m-j'_0) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。

証明：

直系先祖の木構造 (1)と許容性の切片への遺伝性から即座に従う。□

## 幹と枝[]

写像
\begin{eqnarray*}
\textrm{IdxSum} \colon T_{\textrm{PS}}^{< \omega} & \to & \mathbb{N}^{< \omega} \\
Q & \mapsto & \textrm{IdxSum}(Q)
\end{eqnarray*}
を以下のように定める：

- \(J_1 := \textrm{Lng}(Q)-1\)と置く。

- \(J \leq J_1+1\)を満たす各\(J \in \mathbb{N}\)に対し、\(j_J \in \mathbb{N}\)を以下のように再帰的に定める：

- \(J = 0\)ならば\(j_J := 0\)である。

- \(J > 0\)ならば\(j_J := j_{J-1} + \textrm{Lng}(Q_{J-1})\)である。

- \(\textrm{IdxSum}(Q) := (j_J)_{J=0}^{J_1+1}\)である。

命題（\(P\)と\(\textrm{IdxSum}\)の関係）

任意の\(M \in T_{\textrm{PS}}\)と\(J \in \mathbb{N}\)に対し、\(J_1 := \textrm{Lng}(P(M))-1\)と置くと、\(J \leq J_1\)として\(j'_0 := \textrm{IdxSum}(P(M))_J\)と置き\(j'_1 := \textrm{IdxSum}(P(M))_{J+1}\)と置くと、\(P(M)_J = (M_j)_{j=j'_0}^{j'_1-1}\)である。

証明：

\(\textrm{IdxSum}\)の定義から即座に従う。□

系（\(P\)と\(\textrm{IdxSum}\)の合成の特徴付け）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(J_1 := \textrm{Lng}(P(M))-1\)と置くと、以下が成り立つ：

(1) 任意の\(J \in \mathbb{N}\)に対し、\(J \leq J_1\)ならば、\((0,j_0) <_M^{\textrm{Next}} (0,\textrm{IdxSum}(P(M))_J)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在しない。

(2) 任意の\(j \in \mathbb{N}\)に対し、\(j \leq j_1\)かつ\((0,j_0) <_M^{\textrm{Next}} (0,j)\)を満たす一意な\(j \in \mathbb{N}\)が存在しないならば、ある\(J \in \mathbb{N}\)が存在して\(J \leq J_1\)かつ\(j = \textrm{IdxSum}(P(M))_J\)である。

subsection \<open>§7.1 Buchholz の表記系 — 基本列と \<open>dom\<close> ([Buc1] §3)\<close>

\(P\)の再帰的定義と\(P\)と\(\textrm{IdxSum}\)の関係から即座に従う。□

命題（\(P\)の各成分の左端の単調性）

任意の\(M \in T_{\textrm{PS}}\)と\(J'_0,J'_1 \in \mathbb{N}\)に対し、\(J_1 := \textrm{Lng}(P(M))-1\)と置くと、\(J'_0 \leq J'_1 \leq J_1\)ならば\((P(M)_{J'_0})_{0,0} \geq (P(M)_{J'_1})_{0,0}\)である。

証明：

\(P\)の各成分の非複項性と\(P\)と\(\textrm{IdxSum}\)の関係から、任意の\(j \in \mathbb{N}\)に対し\(j < \textrm{IdxSum}(P(M))_{J'_1}\)ならば\((0,j) \leq_M (0,j_{J'_1})\)でない。

従って親の存在の判定条件 (1)から、任意の\(j \in \mathbb{N}\)に対し\(j < j_{J'_1}\)ならば\(M_{0,j} \geq M_{0,j_{J'_1}}\)である。

\(J'_0 \leq J'_1 \leq J_1\)より\(\textrm{IdxSum}(P(M))_{J'_0} < \textrm{IdxSum}(P(M))_{J'_1}\)であるので、\((P(M)_{J'_0})_{0,0} = M_{0,j_{J'_0}} \geq M_{0,j'_{J'_1}} = (P(M)_{J'_1})_{0,0}\)である。□

命題（切片の単項成分と\(<_M^{\textrm{Next}}\)の関係）

任意の\(M \in PT_{\textrm{PS}}\)と\(j_0,J \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(0 < j_0 \leq j_1\)として\(M' := (M_j)_{j=j_0}^{j_1}\)と置き、\(J_1 := \textrm{Lng}(P(M'))-1\)と置くと、\(J \leq J_1\)ならば一意な\(j \in \mathbb{N}\)が存在して\(j < j_0\)かつ\((0,j) <_M^{\textrm{Next}} (0,j_0 + \textrm{IdxSum}(P(M'))_J)\)である。

証明：

\(j'_0 := j_0 + \textrm{IdxSum}(P(M'))_J\)と置く。

\(j'_0 \leq j_0 + (j_1-j_0) = j_1\)である。

\(M\)が単項より\((0,0) \leq_M (0,j'_0)\)であり、かつ\(j'_0 \geq j_0 > 0\)より\(M_{0,0} < M_{0,j'_0}\)である。従って親の存在の判定条件 (1)より一意な\(j \in \mathbb{N}\)が存在して\((0,j) <_M^{\textrm{Next}} (0,j'_0)\)である。

一方で\(P\)と\(\textrm{IdxSum}\)の関係と\(P\)の定義から任意の\(j \in \mathbb{N}\)に対し\(j_0 \leq j \leq j'_0\)ならば\((0,j-j_0) \leq_{M'} (0,j'_0-j_0)\)でなくすなわち\((0,j) \leq_M (0,j'_0)\)でない。以上より\(j < j_0\)である。□

写像
\begin{eqnarray*}
\textrm{TrMax} \colon PT_{\textrm{PS}} & \to & \mathbb{N} \\
M & \mapsto & \textrm{TrMax}(M)
\end{eqnarray*}
と
\begin{eqnarray*}
\textrm{Br} \colon PT_{\textrm{PS}} & \to & T_{\textrm{PS}}^{< \omega} \\
M & \mapsto & \textrm{Br}(M)
\end{eqnarray*}
と
\begin{eqnarray*}
\textrm{FirstNodes} \colon PT_{\textrm{PS}} & \to & \mathbb{N}^{< \omega} \\
M & \mapsto & \textrm{FirstNodes}(M)
\end{eqnarray*}
と
\begin{eqnarray*}
\textrm{Joints} \colon PT_{\textrm{PS}} & \to & \mathbb{N}^{< \omega} \\
M & \mapsto & \textrm{Joints}(M)
\end{eqnarray*}
と
を以下のように定める：

- \(\textrm{TrMax}(M) := \max \{j \in \mathbb{N} \mid \forall j' \in \mathbb{N}, (j' < j) \to ((1,j') <_M^{\textrm{Next}} (1,j'+1))\}\)である[9]。

- \(j_1 := \textrm{Lng}(M) - 1\)と置く。

- \(j'_1 := \textrm{TrMax}(M)\)と置く。

- \(j'_1 = j_1\)ならば\(\textrm{Br}(M) := ()\)である。

- \(j'_1 < j_1\)ならば\(\textrm{Br}(M) := P((M_j)_{j=j'_1+1}^{j_1})\)である。

- \(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置く。

- \(\textrm{FirstNodes}(M) := (\textrm{TrMax}(M) + 1 + \textrm{IdxSum}(\textrm{Br}(M))_J)_{J=0}^{J_1+1}\)である。

- \(J \leq J_1\)を満たす各\(J \in \mathbb{N}\)に対し、\((0,j) <_M^{\textrm{Next}} (0,\textrm{FirstNodes}(M)_J)\)を満たす一意な\(j \in \mathbb{N}\)を\(a_J\)と置く[10]。

- \(\textrm{Joints}(M) := (a_J)_{J=0}^{J_1}\)である。

\(\textrm{TrMax}\)の定義から\((1,\textrm{TrMax}(M)) <_M^{\textrm{Next}} (1,\textrm{TrMax}(M)+1)\)でなくかつ\(\textrm{TrMax}(M) < \textrm{Lng}(M)\)であるので、\(\textrm{TrMax}(M)\)は\(M\)許容である。また\(\textrm{FirstNodes}(M)\)の定義から、\(\textrm{Br}(M) = ((M_j)_{j = \textrm{FirstNodes}(M)_J}^{\textrm{FirstNodes}(M)_{J+1}-1})_{J=0}^{J_1}\)となる。

命題（\(\textrm{FirstNodes}\)と\(\textrm{TrMax}\)と\(\textrm{Joints}\)の関係）

任意の\(M \in PT_{\textrm{PS}}\)と\(J \in \mathbb{N}\)に対し、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置くと、\(J \leq J_1\)ならば\(\textrm{Joints}(M)_J \leq \textrm{TrMax}(M) < \textrm{FirstNodes}(M)_J\)である。

証明：

\(\textrm{TrMax}\)と\(\textrm{Br}\)と\(\textrm{FirstNodes}\)と\(\textrm{Joints}\)の定義と切片の単項成分と\(<_M^{\textrm{Next}}\)の関係から即座に従う。□

系（\(\textrm{FirstNodes}\)と\(\textrm{Joints}\)の単調性）

任意の\(M \in PT_{\textrm{PS}}\)と\(J'_0,J'_1 \in \mathbb{N}\)に対し、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置くと、\(J'_0 < J'_1 \leq J_1\)ならば以下が成り立つ：

(1) \(\textrm{FirstNodes}(M)_{J'_0} \leq \textrm{FirstNodes}(M)_{J'_1}\)である。

(2) \(\textrm{Joints}(M)_{J'_0} \geq \textrm{Joints}(M)_{J'_1}\)である。

(3) \(M_{0,\textrm{FirstNodes}(M)_{J'_0}} \geq M_{0,\textrm{FirstNodes}(M)_{J'_1}}\)である。

(4) 任意の\(i \in \{0,1\}\)に対し\(M_{i,\textrm{Joints}(M)_{J'_0}} > M_{i,\textrm{Joints}(M)_{J'_1}}\)である。

証明：

(1)と(3)は\(P\)と\(\textrm{IdxSum}\)の定義から即座に従う。

(2)と(4)は\(\textrm{FirstNodes}\)と\(\textrm{TrMax}\)と\(\textrm{Joints}\)の関係と(3)から即座に従う。□

系（単項性の切片への遺伝性）

任意の\(M \in PT_{\textrm{PS}}\)と\(j'_0,j'_1 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置き、\(j'_0 < j'_1 \leq j_1\)として\(M' := (M_j)_{j=j'_0}^{j'_1}\)と置くと、\(j'_0 \leq \textrm{Joints}(M)_{J_1}\)ならば\(M'\)は単項である。

証明：

\(j_0 := \textrm{TrMax}(M)\)と置く。

\(\textrm{TrMax}(M') = j_0-j'_0\)かつ\(\textrm{Lng}(M')-1 = j'_1-j'_0\)である。

\(\textrm{Lng}(M')-1 = j'_1-j'_0 > 0\)より、任意の\(j \in \mathbb{N}\)に対し、\(j \leq j'_1-j'_0\)ならば\((0,0) \leq_{M'} (0,j)\)となることを示せば良い。

\(j \leq \textrm{TrMax}(M')\)ならば\((1,0) \leq_{M'} (1,j)\)なので\((0,0) \leq_{M'} (0,j)\)である。

\(j > \textrm{TrMax}(M')\)とする。

\(j+j'_0 > \textrm{TrMax}(M')+j'_0 = j_0\)であるので、\(\textrm{FirstNodes}\)と\(\textrm{Joints}\)の単調性から一意な\(J \in \mathbb{N}\)が存在して\(J \leq J_1\)かつ\(\textrm{FirstNodes}(M)_J \leq j+j'_0 < \textrm{FirstNodes}(M)_{J+1}\)となる。\(P\)の各成分の非複項性より\(\textrm{Br}(M)_J\)は複項でないので、\((0,0) \leq_{\textrm{Br}(M)_J} (0,j+j'_0 - \textrm{FistNodes}(M)_J)\)すなわち\((0,\textrm{FirstNodes}(M)_J) \leq_M (0,j+j'_0)\)である。

\(\textrm{FirstNodes}\)と\(\textrm{Joints}\)の単調性と\(\textrm{FirstNodes}\)と\(\textrm{TrMax}\)と\(\textrm{Joints}\)の関係から\(j'_0 \leq \textrm{Joints}(M)_{J_1} \leq \textrm{Joints}(M)_J \leq \textrm{TrMax}(M)\)であるので、\((1,j'_0) \leq_M (1,\textrm{Joints}(M)_J)\)である。

\((1,j'_0) \leq_M (1,\textrm{Joints}(M)_J)\)かつ\((0,\textrm{Joints}(M)_J) <_M^{\textrm{Next}} (0,\textrm{FirstNodes}(M)_J)\)かつ\((0,\textrm{FirstNodes}(M)_J) \leq_M (0,j+j'_0)\)より\((0,j'_0) \leq_M (0,j+j'_0)\)すなわち\((0,0) \leq_{M'} (0,j)\)である。

以上より\(M'\)は単項である。□

## 簡約化[]

写像
\begin{eqnarray*}
\textrm{Red} \colon T_{\textrm{PS}} & \to & T_{\textrm{PS}} \\
M & \mapsto & \textrm{Red}(M)
\end{eqnarray*}
を以下のように再帰的に定める：

- \(M\)が零項ならば\(\textrm{Red}(M) := ((0,0))\)である。

- \(M\)が単項とする。

- \(j_1 := \textrm{Lng}(M) - 1\)と置く。

- \(M_0 = (0,0)\)とする[11]。

- \(j'_1 := \textrm{TrMax}(M)\)と置く。

- \(j'_1 = j_1\)ならば\(\textrm{Red}(M) := ((j,j))_{j=M_{1,0}}^{M_{1,0}+j_1}\)である。

- \(j'_1 < j_1\)とする。

- \(J_1 := \textrm{Lng}(\textrm{Br}(M)) - 1\)と置く。

- \(J \leq J_1\)を満たす各\(J \in \mathbb{N}\)に対し、\(n_J \in \mathbb{N} \cup \{-1\}\)と\(N_J \in PT_{\textrm{PS}}\)を以下のように定める：

- \((\textrm{Br}(M)_J)_{1,0} = 0\)ならば、\(n_J := -1\)である。

- \((\textrm{Br}(M)_J)_{1,0} > 0\)ならば\((1,j) <_M^{\textrm{Next}} (1,\textrm{FirstNodes}(M)_J)\)を満たす一意な\(j \in \mathbb{N}\)を\(n_J\)と置く[12]。

- \(N_J := ((M_{0,0} + \textrm{Joints}(M)_J + 1,M_{1,0} + n_J + 1)) \oplus_{\mathbb{N}^2} \textrm{Derp}(\textrm{Br}(M)_J)\)である[13]。

- \(\textrm{Red}(M) := ((j,j))_{j=0}^{j'_1} \oplus_{\textrm{N}^2} \bigoplus_{\mathbb{N}^2} (\textrm{IncrFirst}^{\textrm{Joints}(M)_J-n_J}(\textrm{Red}(N_J)))_{J=0}^{J_1}\)である[14]。

- \(M_0 \neq (0,0)\)とする。

- \(M_{1,0} = 0\)とする[15]。

- \(N := ((M_{0,j} - M_{0,0},M_{1,j}))_{j=0}^{j_1}\)と置く[16]。

- \(\textrm{Red}(M) := \textrm{Red}(N)\)である。

- \(M_{1,0} > 0\)とする。

- \(N := \textrm{Red}(((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{IncrFirst}^{M_{1,0}}(M))\)と置く[17]。

- \(j_1 := \textrm{Lng}(N) - 1\)と置く。

- \(M_{1,0} \leq j_1\)かつ\((N_j)_{j=M_{1,0}}^{j_1} \in PT_{\textrm{PS}}\)ならば\(\textrm{Red}(M) := ((N_{0,j}-N_{0,M_{1,0}}+N_{1,M_{1,0}},N_{1,j}))_{j=M_{1,0}}^{j_1}\)である[18]。

- \(M_{1,0} \leq j_1\)かつ\((N_j)_{j=M_{1,0}}^{j_1} \in T_{\textrm{PS}} \setminus PT_{\textrm{PS}}\)ならば\(\textrm{Red}(M) := M\)である[19]。

- \(M_{1,0} > j_1\)ならば\(\textrm{Red}(M) := M\)である[20]。

- \(M\)が複項とする。

- \(J_1 := \textrm{Lng}(P(M)) - 1\)と置く。

- \(\textrm{Red}(M) := \bigoplus_{\mathbb{N}^2} (\textrm{Red}(P(M)_J))_{J=0}^{J_1}\)である。

命題（\(\textrm{Red}\)のwell-defined性）

上の条件を全て満たす写像\(\textrm{Red}\)が一意に存在する。

証明：

\(\{M \in PT_{\textrm{PS}} \mid M_0 = (0,0)\}\)への制限が一意に存在することは、\(\textrm{Lng}(M) - \textrm{TrMax}(M)\)に関する数学的帰納法より従う。

\(T_{\textrm{PS}}\)への延長が一意に存在することは\(T_{\textrm{PS}} \setminus \{M \in PT_{\textrm{PS}} \mid M_0 = (0,0)\}\)における\(\textrm{Red}\)の定義より即座に従う。□

命題（\(\textrm{Red}\)の\(\textrm{IncrFirst}\)不変性）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\textrm{Red}(\textrm{IncrFirst}(M)) = \textrm{Red}(M)\)である。

証明：

\(\textrm{Red}\)の再帰的定義より即座に従う。□

命題（\(\textrm{Lng}\)の\(\textrm{Red}\)不変性）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\textrm{Lng}(\textrm{Red}(M)) = \textrm{Lng}(M)\)である。

証明：

\(\textrm{Red}\)の再帰的定義により、\(\textrm{Lng}(M)\)に関する数学帰納法から即座に従う。□

系（\(\textrm{Red}\)が零項性を保つこと）

任意の\(M \in T_{\textrm{PS}}\)に対し、以下は同値である：

(1) \(M\)は零項である。

(2) \(\textrm{Red}(M)\)は零項である。

証明：

\(\textrm{Lng}\)の\(\textrm{Red}\)不変性から\(\textrm{Lng}(M) = 1\)の場合に帰着される。\(\textrm{Lng}(M) = 1\)ならば、\(\textrm{Red}\)の再帰的定義より即座に従う。□

系（直系先祖の\(\textrm{Red}\)不変性）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\leq_M\)と\(\leq_{\textrm{Red}(M)}\)は一致する。

証明：

\(\textrm{Lng}\)の\(\textrm{Red}\)不変性と\(\textrm{Red}\)の再帰的定義により、\(\textrm{Lng}(M)\)に関する数学帰納法から即座に従う。□

系（\(\textrm{Red}\)が単項性を保つこと）

任意の\(M \in T_{\textrm{PS}}\)に対し、以下は同値である：

(1) \(M\)は単項である。

(2) \(\textrm{Red}(M)\)は単項である。

証明：

単項性の定義と直系先祖の\(\textrm{Red}\)不変性より即座に従う。□

系（\(P\)の\(\textrm{Red}\)同変性）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(J_1 := \textrm{Lng}(P(M))\)と置くと\(P(\textrm{Red}(M)) = (\textrm{Red}(P(M)_J))_{J=0}^{J_1}\)である。

証明：

\(\textrm{Red}\)の再帰的定義から、直系先祖の\(\textrm{Red}\)不変性より即座に従う。□

命題（単項性と\(\textrm{Red}\)の関係）

任意の\(M \in PT_{\textrm{PS}}\)に対し、\(N := \textrm{Red}(((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{IncrFirst}^{M_{1,0}}(M))\)と置き\(j_1 := \textrm{Lng}(N)-1\)と置くと、\((N_j)_{j=M_{1,0}}^{j_1} \in PT_{\textrm{PS}}\)である。

証明：

\(N\)の定義より、\(\textrm{Lng}(M) = j_1 - M_{1,0} + 1\)でありかつ任意の\((i,j), (i',j') \in \mathbb{N}^2\)に対し以下は同値である：

(1) \((i,j) \leq_M (i',j')\)である。

(2) \((i,j+M_{1,0}) \leq_N (i',j'+M_{1,0})\)である。

従って直系先祖の\(\textrm{Red}\)不変性より従う。□

命題（\(\textrm{Red}\)の冪等性）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\textrm{Red}^2(M) = \textrm{Red}(M)\)である。

証明：

\(\textrm{Red}\)の再帰的定義により、\(\textrm{Lng}(M)\)に関する数学帰納法から即座に従う。□

命題（\(\textrm{Red}\)と\(\textrm{Pred}\)の可換性）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\textrm{Red}(\textrm{Pred}(M)) = \textrm{Pred}(\textrm{Red}(M))\)である。

証明：

\(\textrm{Red}\)の再帰的定義から\(\textrm{Lng}(M)\)に関する数学的帰納法により即座に従う。□

命題（\(\textrm{Red}\)と基本列の可換性）

任意の\(M \in T_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Red}(M)[n] = \textrm{Red}(M[n])\)である。

証明：

\(j_1 := \textrm{Lng}(M_1)-1\)と置く。\(j_1\)に関する数学的帰納法で示す。

\(j_1 = 0\)ならば\(\textrm{Red}\)と\(\textrm{operator}[]\)の定義から即座に従う。

\(j_1 > 0\)とする。

\((1,0) <_M^{\textrm{Next}} (1,j_1)\)でないならば、\(\textrm{Red}\)と\(\textrm{operator}[]\)の再帰的定義から帰納法の仮定より従う。

\((1,0) <_M^{\textrm{Next}} (1,j_1)\)ならば、\(\textrm{Red}\)と\(\textrm{Pred}\)の可換性と\(\textrm{operator}[]\)の定義に用いた\(B\)の定義から、\(n\)に関する数学的帰納法により従う。□

命題（\(\textrm{Red}\)が許容性を保つこと）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\mathbb{N}_M = \mathbb{N}_{\textrm{Red}(M)}\)である。

証明：

直系先祖の\(\textrm{Red}\)不変性から即座に従う。□

系（許容化の\(\textrm{Red}\)不変性）

任意の\(M \in T_{\textrm{PS}}\)と\(j \in \mathbb{N}\)に対し、\(\textrm{Adm}_M(j) = \textrm{Adm}_{\textrm{Red}(M)}(j)\)である。

証明：

直系先祖の\(\textrm{Red}\)不変性と\(\textrm{Red}\)が許容性を保つことから即座に従う。□

系（\(\textrm{Red}\)が基点を保つこと）

任意の\((M,m) \in T_{\textrm{PS}}^{\textrm{Marked}}\)に対し、\((\textrm{Red}(M),m) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)である。

証明：

直系先祖の\(\textrm{Red}\)不変性と\(\textrm{Red}\)が許容性を保つことから即座に従う。□

## 簡約性[]

\(M \in T_{\textrm{PS}}\)とする。

- \(M\)が簡約であるとは、\(\textrm{Red}(M) = M\)を満たすということである。

- 簡約ペア数列全体のなす部分集合を\(RT_{\textrm{PS}} \subset T_{\textrm{PS}}\)と置く。

すなわち\(RT_{\textrm{PS}} = \textrm{Im}(\textrm{Red})\)である。\(RT_{\textrm{PS}} \subset \textrm{Im}(\textrm{Red})\)であることは簡約性の定義から従い、\(\textrm{Im}(\textrm{Red}) \subset RT_{\textrm{PS}}\)であることは\(\textrm{Red}\)の冪等性から従う。

命題（簡約性の切片への遺伝性）

任意の\(M \in RT_{\textrm{PS}}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置くと、任意の\(j'_0,j'_1 \in \mathbb{N}\)に対し\(j'_0 \leq \textrm{TrMax}(M) \leq j'_1 \leq j_1\)ならば\((M_j)_{j=j'_0}^{j'_1}\)は簡約である。

証明：

\(\textrm{Red}\)の再帰的定義と\(\textrm{Red}\)と\(\textrm{Pred}\)の可換性より即座に従う。□

命題（\(P\)が簡約性を保つこと）

任意の\(M \in T_{\textrm{PS}}\)に対し、以下は同値である：

(1) \(M\)は簡約である。

(2) \(P(M)\)の各成分は簡約である。

証明：

\(P\)の\(\textrm{Red}\)同変性より即座に従う。□

命題（簡約性が基本列で保たれること）

任意の\(M \in RT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(M[n] \in RT_{\textrm{PS}}\)である。

証明：

\(\textrm{Red}\)の冪等性と\(\textrm{Red}\)と基本列の可換性から即座に従う。□

命題（簡約性と係数の関係）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置くと\(M\)が簡約である必要十分条件は以下が成り立つことである：

(A) 任意の\(i \in \{0,1\}\)と\(j'_1 \in \mathbb{N}\)に対し、\((i,j'_0) <_M^{\textrm{Next}} (i,j'_1)\)を満たす一意な\(j'_0 \in \mathbb{N}\)が存在するならば\(M_{i,j'_0}+1 = M_{i,j'_1}\)である。

(B) 任意の\(j'_1 \in \mathbb{N}\)に対し、\((0,j'_0) <_M^{\textrm{Next}} (0,j'_1)\)を満たす一意な\(j'_0 \in \mathbb{N}\)が存在せずかつ\(j'_1 \leq j_1\)ならば、\(M_{0,j'_1} = M_{1,j'_1}\)である。

簡約性と係数の関係の証明の準備としていくつかの補題を用意する。

補題（Redと左端の関係）

任意の\(M \in T_{\textrm{PS}}\)に対し、以下が成り立つ：

(1) \(\textrm{Red}(M)_{1,0} = M_{1,0}\)である。

(2) 任意の\(u,j_0 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置くと、\(M\)が単項かつ\(j_0 \leq j_1\)かつ\((M_j)_{j=0}^{j_0} = ((j,j))_{j=u}^{j_0+u}\)ならば、\(\textrm{Red}(M)_{j_0} = (j_0+u,j_0+u)\)である。

証明：

\(\textrm{Red}\)の再帰的定義より即座に従う。□

補題（簡約性と係数の基本性質）

任意の\(M \in RT_{\textrm{PS}}\)と\(j \in \mathbb{N}\)に対し、\(j < \textrm{Lng}(M)\)ならば\(M_{0,j} \geq M_{1,j}\)である。

証明：

\(\textrm{Red}\)の再帰的定義により、\(\textrm{Lng}(M)\)に関する数学帰納法から即座に従う。□

補題（簡約性と左端の関係）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(u \in \mathbb{N}\)に対し、\(u \leq M_{1,0}\)ならば\(N := ((j,j))_{j=u}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} M\)と置くと\(N\)は簡約かつ単項である。

証明：

\(M_{1,0} = u\)ならば\(N = M\)より従う。以下\(M_{1,0} > u\)とする。

Redと左端の関係 (2)より、\(\textrm{Red}\)の定義と\(\textrm{Red}\)の冪等性から\(((j,j))_{j=0}^{u-1} \oplus_{\mathbb{N}^2} N = ((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} M = ((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{Red}(M) = \textrm{Red}(((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} M) \in RT_{\textrm{PS}}\)であり、\(((j,j))_{j=0}^{u-1} \oplus_{\mathbb{N}^2} N = \textrm{Red}(((j,j))_{j=0}^{u-1} \oplus_{\mathbb{N}^2} N) = ((j,j))_{j=0}^{u-1} \oplus_{\mathbb{N}^2} \textrm{Red}(N)\)となるので\(N = \textrm{Red}(N)\)である。従って\(N\)は簡約である。

簡約性と係数の基本性質から\(u < M_{1,0} \leq M_{0,0}\)であるので\((0,0) \leq_N (0,u+M_{1,0})\)となり、\(M\)の単項性から\(N\)は単項である。□

補題（条件(A)と(B)と係数の基本性質）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置くと、\(M_0 = (0,0)\)かつ\(M\)が条件(A)を満たすならば、以下が成り立つ：

(1) 任意の\(j \in \mathbb{N}\)に対し、\(j \leq j_1\)ならば\(M_{0,j} \leq j\)である。

(2) \(M\)が条件(B)を満たすならば、任意の\(j \in \mathbb{N}\)に対し、\(j \leq j_1\)ならば\(M_{0,j} \geq M_{1,j}\)である。

(3)  \(i \in \{0,1\}\)とし、\(i = 0\)であるか、または\(i = 1\)かつ\(M\)が条件(B)を満たすとする。任意の\(j \in \mathbb{N}\)に対し、ある\(j'_0,j'_1 \in \mathbb{N}\)が存在して\((i,j'_0) \leq_M (i,j'_1)\)でなくかつ\(j'_0 < j'_1 \leq j \leq j_1\)ならば、\(M_{i,j} < j\)である。

証明：

(1) 成り立たないと仮定して矛盾を導く。仮定から\(j \leq j_1\)かつ\(M_{0,j} > j\)を満たす\(j \in \mathbb{N}\)が存在し、その最小値を\(j_0\)と置けば、\(M_{0,0} = 0 \leq j_0 < M_{0,j_0}\)と親の存在の判定条件 (1)より\(j_0 > 0\)かつ\((0,j'_0) <_M^{\textrm{Next}} (0,j_0)\)を満たす一意な\(j'_0 \in \mathbb{N}\)が存在する。一方で\(j_0\)の最小性から\(M_{0,j'_0} \leq j'_0\)となり、\(M\)が条件(A)を満たすことから\(M_{0,j_0} = M_{0,j'_0}+1 = j'_0+1 \leq j_0\)となり矛盾する。

(2) 成り立たないと仮定して矛盾を導く。仮定から\(j \leq j_1\)かつ\(M_{0,j} < M_{1,j}\)を満たす\(j \in \mathbb{N}\)が存在する。その最小値を\(j_0\)と置けば、\(M\)が条件(B)を満たすことから\((0,j'_0) <_M^{\textrm{Next}} (0,j_0)\)を満たす一意な\(j'_0 \in \mathbb{N}\)が存在する。一方で\(j_0\)の最小性から\(M_{0,j'_0} \geq M_{1,j'_0}\)となり、\(M\)が条件(A)を満たすことから\(M_{0,j_0} = M_{0,j'_0}+1 \geq M_{1,j'_0}+1\)となる。

\((1,j'_0) <_M^{\textrm{Next}} (1,j_0)\)ならば、\(M\)が条件(A)を満たすことから\(M_{0,j_0} = M_{1,j'_0}+1 = M_{1,j_0}\)となり矛盾する。

\((1,j'_0) <_M^{\textrm{Next}} (1,j_0)\)でないならば、\(M_{1,j'_0} \geq M_{1,j_0}\)より\(M_{0,j_0} = M_{1,j'_0}+1 > M_{1,j_0}\)となり矛盾する。

(3) \(M_0 = (0,0)\)かつ\(j > 0\)より、一意な\(J_1 \in \mathbb{N}\)と\(a \in \mathbb{N}^{< \omega}\)が存在して以下を満たす：

\(\textrm{Lng}(a) = J_1+1\)である。

\((i,j'-1) <_M^{\textrm{Next}} (i,a_0)\)を満たす一意な\(j' \in \mathbb{N}\)が存在しない。

任意の\(J \in \mathbb{N}\)に対し、\(J < J_1\)ならば\((i,a_J) <_M^{\textrm{Next}} (i,a_{J+1})\)である。

\(a_{J_1} = j\)である。

\(j\)の条件から、ある\(j' \in \mathbb{N}\)が存在して\((1,j'-1) <_M^{\textrm{Next}} (1,j')\)でなくかつ\(j'_0 < j' \leq j'_1\)である。従って\(a\)は\(j'\)を成分に持たない狭義単調増大列となるので\(J_1 < j\)である。\(M_{0,0} = 0\)であることから\(a_{0,0} = 0\)であるので、\(i = 0\)ならば\(a_{i,0} = 0\)であり、\(i = 1\)かつ\(M\)が条件(B)を満たすならば(2)より\(a_{i,0} = 0\)である。従っていずれの場合も\(a_{i,0} = 0\)である。更に\(M\)が条件(A)を満たすことから\(M_{i,j} \leq a_{i,0} + J_1 < j\)である。□

それでは本題に戻る。

簡約性と係数の関係の証明：

\(j_1 = 0\)ならば条件(A)は常に成り立ちかつ条件(B)が成り立つ必要十分条件は\(M_{0,0} = M_{1,0}\)であるので、\(\textrm{Red}\)の定義より従う。

\(M\)が単項かつ\(M_{1,0} = 0\)とする。

この条件下で\(M\)の簡約性と\(M\)が条件(A)と(B)を満たすことが同値であることを\(j_1\)に関する数学的帰納法で示す。

\(j_1 = 1\)とする。

この時\((0,0) <_M^{\textrm{Next}} (0,1)\)である。

\((1,0) <_M^{\textrm{Next}} (1,1)\)ならば\(M_{1,0} < M_{1,1}\)であり、条件(A)は\(M_1 = (M_{0,0}+1,M_{1,0}+1)\)と同値であり条件(B)は\(M_{0,0} = M_{1,0}\)と同値であるので、\(\textrm{Red}\)の定義より従う。

\((1,0) <_M^{\textrm{Next}} (1,1)\)でないならば\(M_{1,0} \geq M_{1,1}\)であり、条件(A)は\(M_{0,1} = M_{0,0}+1\)と同値であり条件(B)は\(M_{0,0} = M_{1,0}\)と同値であるので、\(\textrm{Red}\)の定義より従う。

\(j_1 > 1\)とする。

まず\(M\)が簡約とする。

\(j_0 := \max \{j \in \mathbb{N} \mid j \leq j_1 \wedge \forall j' \in \mathbb{N}, (j' < j) \to ((1,j') <_M^{\textrm{Next}} (1,j'+1))\}\)と置く[21]。

\(J_1 := \textrm{Lng}(P((M_j)_{j=j_0}^{j_1}))-1\)と置く。

\(\textrm{Red}\)の再帰的定義から\(((M_j)_{j=0}^{j_0})_0 = M_0 = (0,0)\)であり、任意の\(j \in \mathbb{N}\)に対し\(j \leq j_0\)ならば\((0,0) \leq_M (0,j)\)より\((0,0) \leq_{(M_j)_{j=0}^{j_0}} (0,j)\)であるので、\((M_j)_{j=0}^{j_0}\)は単項である。更に簡約性の切片への遺伝性より\((M_j)_{j=0}^{j_0}\)は簡約であり、\(\textrm{Red}\)の定義より\((M_j)_{j=0}^{j_0} = \textrm{Red}((M_j)_{j=0}^{j_0}) = ((j,j))_{j=0}^{j_0}\)である。

\(i \in \{0,1\}\)と\(j'_1 \in \mathbb{N}\)とし、\((i,j'_0) <_M^{\textrm{Next}} (i,j'_1)\)を満たす一意な\(j'_0 \in \mathbb{N}\)が存在するとする。この時\(j'_1 > j'_0 \geq 0\)である。

\(j'_1 < j_1\)ならば、簡約性の切片への遺伝性から\(\textrm{Pred}(M)\)が簡約であるので、帰納法の仮定より\(M_{i,j'_0}+1 = \textrm{Pred}(M)_{i,j'_0}+1 = \textrm{Pred}(M)_{i,j'_1} = M_{i,j'_1}\)が成り立つ。

\(j_0 = j'_1 = j_1\)かつ\(J_1 = 0\)ならば、\(M = ((j,j))_{j=0}^{j_1}\)より\(j'_0+1 = j'_1\)であり\(M_{i,j'_0}+1 = j'_0+1 = j'_1 = M_{i,j'_1}\)である。

\(j_0 < j'_1 = j_1\)かつ\(J_1 = 0\)とする。

この時\((M_j)_{j=j_0}^{j_1}\)が単項である。

\(J_0 := \textrm{Lng}(P((M_j)_{j=j_0+1}^{j_1}))-1\)と置く。

\(m := j_1 - \textrm{Lng}(P((M_j)_{j=j_0+1}^{j_1})_{J_0}) + 1\)と置く。

\(N := ((j,j))_{j=0}^{M_{1,m}-1} \oplus_{\mathbb{N}^2} \textrm{Red}(P((M_j)_{j=j_0+1}^{j_1})_{J_0})\)と置く。

簡約性と左端の関係から\(N\)は簡約である。

\(M_{1,m}=0\)ならば、Redと左端の関係 (2)と\(\textrm{Red}\)の再帰的定義から\(N_0 = \textrm{Red}(P((M_j)_{j=j_0+1}^{j_1})_{J_0})_0 = (0,0)\)となり、\(M_{1,m} \neq 0\)ならば\(N\)の定義からやはり\(N_0 = (0,0)\)となる。従っていずれの場合も\(N_0 = (0,0)\)である。

\(\textrm{Lng}(N) - 1 = j_1 - m + M_{1,m} < j_1\)であり、\((0,m) \leq_M (0,j_1)\)より\((0,0) \leq_{P(M)_{J_1}} (0,j_1-m)\)であるので\((0,M_{1,0}) \leq_N (0,j_1-m+M_{1,m})\)である。

\(j'_0 \leq j_0 = j_1 - 1\)とする。

\((M_j)_{j=j_0}^{j_1}\)が単項であるため、\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)である。

\(M = ((j,j))_{j=0}^{j_0} \oplus_{\mathbb{N}^2} (M_{j_1})\)であり、\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)でなくかつ\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)より\(j_0 = M_{0,j_0} < M_{0,j_1}\)かつ\(j_0 = M_{1,j_0} \geq M_{1,j_1}\)である。従って\(j'_0 = M_{i,j_1}-1\)であるので\(M_{i,j'_0}+1 = j'_0+1 = M_{i,j_1}\)である。

\(j'_0 \leq j_0 < j_1 - 1\)とする。

\((M_j)_{j=j_0}^{j_1}\)が単項であるため、\((0,j_0) <_M^{\textrm{Next}} (0,j_0+1)\)である。

\((1,j_0) <_M^{\textrm{Next}} (1,j_0+1)\)でなくかつ\((0,j_0) <_M^{\textrm{Next}} (0,j_0+1)\)より\(M_{1,j_0} \geq M_{1,j_0+1}\)であり、\((i,j'_0) <_M^{\textrm{Next}} (i,j_1)\)かつ\(j'_0 < j_0+1 < j_1\)より\((1,j_0+1) \leq_M (1,j_1)\)でない。従って\((0,j_0+1) \leq_M (0,j_1)\)でない。すなわち\(J_0 > 0\)であり、\(j_0 + 1 < m\)である。\(j'_0 < j_0 + 1 < m\)かつ\((0,m) \leq_M (0,j_1)\)かつ\((i,j'_0) <_M^{\textrm{Next}} (i,j_1)\)より\(i = 1\)かつ\(j'_0 = M_{1,j'_0} < M_{1,j_1} \leq M_{1,m}\)となるので、\((1,j'_0) <_N^{\textrm{Next}} (1,j_1 - m + M_{1,m})\)から帰納法の仮定より\(M_{i,j'_0}+1 = N_{1,j'_0} + 1 = N_{1,j_1 - m + M_{1,m}} = M_{i,j'_1}\)である。

\(j_0 < j'_0\)ならば、\((i,j'_0) <_M^{\textrm{Next}} (i,j_1)\)から\(P\)の定義より\(m \leq j'_0\)となり、再び\((i,j'_0) <_M^{\textrm{Next}} (i,j_1)\)より\((i,j'_0-m+M_{1,m}) <_N^{\textrm{Next}} (i,j_1-m+M_{1,m})\)となるので、帰納法の仮定より\(M_{i,j'_0}+1 = N_{1,j'_0} + 1 = N_{1,j_1 - m + M_{1,m}} = M_{i,j'_1}\)である。

\(j'_1 = j_1\)かつ\(J_1 > 0\)とする。

\(m := j_1 - \textrm{Lng}(P(M)_{J_1}) + 1\)と置く。

\(J_1 > 0\)より\(j_0 < m\)であり、\(P\)の定義から\(M_{0,m} < j_0\)である。簡約性と係数の基本性質から\(M_{0,m}-M_{1,m} \geq 0\)であるので\(M_{1,m} \leq M_{0,m} < j_0 < m\)となる。\(P(M)_{J_1} \in PT_{\textrm{PS}}\)より\(((j,j))_{j=0}^{M_{1,m}} \oplus_{\mathbb{N}^2} (M_j)_{j=m+1}^{j_1} \in PT_{\textrm{PS}}\)となり、\(M\)の簡約性と\(\textrm{Red}\)の定義から

\begin{eqnarray*}
P(M)_{J_1} = \textrm{IncrFirst}^{M_{0,m}-M_{1,m}}(\textrm{Red}((M_{0,m},M_{1,m}) \oplus_{\mathbb{N}^2} (M_j)_{j=m+1}^{j_1})) =  \textrm{IncrFirst}^{M_{0,m}-M_{1,m}}(\textrm{Red}(P(M)_{J_1}))
\end{eqnarray*}

となる。

\(N := ((j,j))_{j=0}^{M_{1,m}-1} \oplus_{\mathbb{N}^2} \textrm{Red}(P(M)_{J_1})\)と置く。

簡約性と左端の関係から\(N\)は簡約である。

\(M_{1,m}=0\)ならば、Redと左端の関係 (2)と\(\textrm{Red}\)の再帰的定義から\(N_0 = \textrm{Red}(P(M)_{J_1})_0 = (0,0)\)となり、\(M_{1,m} \neq 0\)ならば\(N\)の定義から\(N_0 = (0,0)\)となる。従っていずれの場合も\(N_0 = (0,0)\)である。

\(\textrm{Lng}(N) - 1 = j_1 - m + M_{1,m} < j_1\)であり、\((0,m) \leq_M (0,j_1)\)より\((0,0) \leq_{P(M)_{J_1}} (0,j_1-m)\)であるので\((0,M_{1,0}) \leq_N (0,j_1-m+M_{1,m})\)である。

\(m = j_1\)ならば、\(P(M)_{J_1} = (M_m)\)であり\(P\)の定義から\(j'_0 \leq j_0\)であるので、\(M_{1,m} \leq M_{0,m} < j_0\)より\(j'_0 = M_{i,m}-1\)となるので、\(M_{i,j'_0}+1 = j'_0+1 = M_{i,m} = M_{i,j'_1}\)である。

\(m < j_1\)かつ\(j'_0 \leq j_0\)ならば、\(j'_0 < m\)かつ\((0,m) \leq_M (0,j_1)\)かつ\((i,j'_0) <_M^{\textrm{Next}} (i,j_1)\)より\(i = 1\)かつ\(j'_0 = M_{1,j'_0} < M_{1,j_1} \leq M_{1,m}\)となるので、\((1,j'_0) <_N^{\textrm{Next}} (1,j_1 - m + M_{1,m})\)から帰納法の仮定より\(M_{i,j'_0}+1 = N_{1,j'_0} + 1 = N_{1,j_1 - m + M_{1,m}} = M_{i,j'_1}\)である。

\(m < j_1\)かつ\(j_0 < j'_0\)ならば、\(P\)の定義より\(m \leq j'_0\)であり\((i,j'_0) <_M^{\textrm{Next}} (i,j_1)\)より\((i,j'_0-m+M_{1,m}) <_N^{\textrm{Next}} (i,j_1-m+M_{1,m})\)となるので、帰納法の仮定より\(M_{i,j'_0}+1 = N_{1,j'_0} + 1 = N_{1,j_1 - m + M_{1,m}} = M_{i,j'_1}\)である。

以上より、いずれの場合も条件(A)と(B)が従う。

次に\(M\)が条件(A)と(B)を満たすとする。

\(M_{1,0} = 0\)かつ\(M\)が条件(B)を満たすことから、\(M_{0,0} = 0\)である。

ここで、(＊) 任意の\(j'_0, j'_1 \in \mathbb{N}\)に対し、\((1,j'_0-1) <_M^{\textrm{Next}} (1,j'_0)\)でなくかつ\(j'_0 \leq j'_1 \leq j_1\)かつ\((M_j)_{j=j'_0}^{j'_1} \in PT_{\textrm{PS}}\)ならば、\(N' := ((M_{0,j}-M_{0,j'_0}+M_{1,j'_0},M_{1,j}))_{j=j'_0}^{j'_1}\)と置くと\(N'\)は簡約であることを示す。ただし条件(A)と(B)と係数の基本性質 (2)より\(N'\)の各成分は\(\mathbb{N}^2\)に属する。

\(N := ((j,j))_{j=0}^{M_{1,j'_0}-1} \oplus_{\mathbb{N}^2} N'\)と置く。

\(\textrm{Lng}(N)-1 = j'_1-j'_0+M_{1,j'_0}\)であり、条件(A)と(B)と係数の基本性質 (3)から\(M_{1,j'_0} < j'_0\)であるので\(\textrm{Lng}(N)-1 < j'_1 \leq j_1\)である。

\(M_{1,j'_1} = 0\)ならば\(N_0 = N'_0 = (0,0)\)であり、\(M_{1,j'_1} > 0\)ならば\(N\)の定義から\(N_0 = (0,0)\)である。

\(\textrm{IncrFirst}^{M_{0,j'_0}-M_{1,j'_0}}(N') = (M_j)_{j=j'_0}^{j'_1} \in PT_{\textrm{PS}}\)かつ\(P\)の\(\textrm{IncrFirst}\)同変性より\(N' \in PT_{\textrm{PS}}\)であり、\((0,0) \leq_N (0,M_{1,0})\)より\(N\)は単項である。更に\(N_0 = (0,0)\)であるので、\(N\)は条件(B)を満たす。

\(N\)が条件(A)を満たすことを示す。\(i \in \{0,1\}\)と\(k_0,k_1 \in \mathbb{N}^2\)とし、\((i,k_0) <_N^{\textrm{Next}} (i,k_1)\)とする。

\(M_{1,j'_0} \leq k_0\)ならば、\((i,k_0-M_{1,j'_0}) <_M^{\textrm{Next}} (i,k_1-M_{1,j'_0})\)であり\(M\)が条件(A)を満たすので、\(i=0\)ならば\(N_{i,k_0}+1 = M_{0,k_0-M_{1,j'_0}}-M_{0,j'_0}+M_{1,j'_0}+1 = M_{0,k_1-M_{i,j'_0}}-M_{0,j'_0}+M_{1,j'_0} = N_{i,k_1}\)であり、\(i=1\)ならば\(N_{i,k_0}+1 = M_{1,k_0-M_{1,j'_0}}+1 = M_{1,k_1-M_{i,j'_0}} = N_{i,k_1}\)である。

\(k_0 < M_{1,j'_0} < k_1\)ならば、\((M_j)_{j=j'_0}^{j'_1} \in PT_{\textrm{PS}}\)より\((0,j'_0) \leq_M (0,j'_0+k_1-M_{1,j'_0})\)であるので\((0,M_{1,j'_0}) \leq_N (0,k_1)\)であり、従って\((1,M_{1,j'_0}) \leq_N (1,k_1)\)でなくかつ\(i=1\)となり、条件(A)と(B)と係数の基本性質 (2)と(3)から\(N_{1,k_1} \leq N_{0,k_1}\)かつ\(N_{1,k_1} < k_1\)となる。従って\(k_0 = N_{1,k_1}-1\)となり、\(N_{i,k_0}+1 = k_0+1 = N_{i,k_1}\)である。

\(k_1 \leq M_{1,j'_0}\)ならば、\(N_{k_1} = (k_1,k_1)\)となるので\(k_0 = k_1-1\)であり\(N_{i,k_0}+1 = k_0+1 = k_1 = N_{i,k_1}\)である。

従って\(N\)は条件(A)を満たす。\(\textrm{Lng}(N)-1 < j_1\)かつ\(N_0 = (0,0)\)かつ\(N\)が条件(A)と(B)を満たすことから、帰納法の仮定より\(N\)は簡約である。

\((M_j)_{j=j'_0}^{j'_1} \in PT_{\textrm{PS}}\)より、任意の\(j \in \mathbb{N}\)に対し\(j'_0 \leq j \leq j'_1\)ならば\(M_{0,j'_0} \leq M_{0,j}\)すなわち\(M_{0,j}-M_{0,j'_0}+M_{1,j'_0} \leq M_{1,j'_0}\)となるので、一意な\(M' \in PT_{\textrm{N}}\)が存在して\(N' = \textrm{IncrFirst}^{M_{1,j'_0}}(M')\)となる。従って\(\textrm{Red}\)の\(\textrm{IncrFirst}\)不変性とRedと左端の関係 (2)と\(\textrm{Red}\)の再帰的定義から

\begin{eqnarray*}
& & ((j,j))_{j=0}^{M_{1,j'_0}-1} \oplus_{\mathbb{N}^2} N' = N = \textrm{Red}(N) \\
& = & \textrm{Red}(((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{IncrFirst}^{M_{1,j'_0}}(M')) \\
& = & \textrm{Red}(((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{IncrFirst}^{M'_{1,0}}(M')) \\
& = & ((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{Red}(M') \\
& = & ((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{Red}(\textrm{IncrFirst}^{M_{1,j'_0}}(M')) \\
& = & ((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{Red}(N')
\end{eqnarray*}

となるので\(N' = \textrm{Red}(N')\)であり、すなわち\(N'\)は簡約である。

\(\textrm{Red}\)の再帰的定義中に導入した記号を用いると、\(P\)の定義から\(\textrm{Red}(M)\)の計算に現れる\(N_J\)は全て(＊)の仮定を満たし、\(\textrm{IncrFirst}^{\textrm{Joints}(M)_J-n_J}(\textrm{Red}(N_J)) = N_J\)となる。従って\(\textrm{Red}\)の定義から\(\textrm{Red}(M) = M\)となり、すなわち\(M\)は簡約である。

\(M\)が単項かつ\(M_{1,0} > 0\)とする。

\(N := ((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} M\)と置く。

\(M\)が単項かつ\(M_{1,0} > 0\)より\(M\)は\((0,0)\)を成分に持たず、従って\(N\)は単項である。

<<<MISSING line 1265 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1266 — recover from original.html via tools/make_content.py>>>
簡約性と左端の関係から\(N\)は簡約である。更に\(N\)が単項かつ\(N_0 = (0,0)\)より、\(N\)は条件(A)と(B)を満たす。特に\(M\)は条件(A)を満たす。簡約性と係数の基本性質から\(M_{0,0} = N_{0,M_{1,0}} \geq N_{1,M_{1,0}} = M_{1,0}\)であり、よって\((0,M_{1,0}-1) <_M^{\textrm{Next}} (0,M_{1,0})\)となり\(N\)が条件(A)を満たすことから\(M_{0,0} = M_{1,0}\)となる。更に\(M\)が単項より、\(M\)は条件(B)を満たす。
<<<MISSING line 1268 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1269 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1270 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1271 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1272 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1273 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1274 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1275 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1276 — recover from original.html via tools/make_content.py>>>
\(j'_0 < M_{1,0} < j'_1\)ならば、\((0,0) \leq_M (0,j'_1-M_{1,0})\)かつ\((0,m_{1,0}) \leq_N (0,j'_1)\)であるので、\((i,j'_0) <_N^{\textrm{Next}} (i,j'_1)\)より\((1,0) \leq_M (1,j'_1-M_{1,0})\)でなくかつ\(i=1\)である。\(M\)が条件(B)を満たすので\(M_{0,j'_1} > M_{0,0} = M_{1,0} \geq M_{1,j'_1}\)となり、従って\(j'_0 = M_{1,j'_1-M_{1,0}}-1\)であり\(N_{i,j'_0}+1 = j'_0+1 = M_{1,j'_1-M_{1,0}} = N_{i,j'_1}\)である。
<<<MISSING line 1278 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1279 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1280 — recover from original.html via tools/make_content.py>>>
以上より\(N\)は条件(A)を満たす。従って\(N\)は簡約である。一方で\(M\)は条件(B)を満たすので\(M_{0,0} = M_{1,0}\)であり、\(M\)が単項であるので\(\textrm{IncrFirst}^{M_{1,0}}(M') = M\)を満たす一意な\(M' \in PT_{\textrm{PS}}\)が存在する。\(\textrm{Red}\)の\(\textrm{IncrFirst}\)不変性とRedと左端の関係 (2)と\(\textrm{Red}\)の再帰的定義から
<<<MISSING line 1282 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1283 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1284 — recover from original.html via tools/make_content.py>>>
& = & \textrm{Red}(((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{IncrFirst}^{M_{1,0}}(M')) \\
& = & \textrm{Red}(((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{IncrFirst}^{M'_{1,0}}(M')) \\
<<<MISSING line 1287 — recover from original.html via tools/make_content.py>>>
& = & ((j,j))_{j=0}^{M_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{Red}(\textrm{IncrFirst}^{M_{1,0}}(M')) \\
<<<MISSING line 1289 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1290 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1291 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1292 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1293 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1294 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1295 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1296 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1297 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1298 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1299 — recover from original.html via tools/make_content.py>>>
系（直系先祖による切片と\(\textrm{Red}\)と\(\textrm{IncrFirst}\)の関係）

任意の\(M \in RT_{\textrm{PS}}\)と\(j'_0,j'_1 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き\(j'_0 < j'_1 \leq j_1\)として\(N := \textrm{Red}((M_j)_{j=j'_0}^{j'_1})\)と置くと、\((0,j'_0) \leq_M (0,j'_1)\)ならば\(N\)は簡約かつ単項かつ\((M_j)_{j=j'_0}^{j'_1} = \textrm{IncrFirst}^{M_{0,m} - M_{1,m}}(N)\)である[22]。

証明：

\(\textrm{Red}\)を用いた\(N\)の定義から\(N\)は簡約である。

簡約性と係数の基本性質より\(M_{0,j'_0}-M_{1,j'_0} \geq 0\)である。単項性の直系先祖による切片への遺伝性より\((M_j)_{j=j'_0}^{j'_1}\)は単項であるので、任意の\(j \in \mathbb{N}\)に対し\(j'_0 \leq j \leq j'_1\)ならば\((0,j'_0) \leq_M (0,j)\)となるので\(M_{0,j}-M_{0,j_0} \geq 0\)である。

\(M' := ((M_{0,j}-M_{0,j'_0}+M_{1,j'_0},M_{1,j}))_{j=j'_0}^{j'_1}\)と置く。

\(\textrm{IncrFirst}^{M_{0,j'_0} - M_{1,j'_0}}(M') = (M_j)_{j=j'_0}^{j'_1}\)であるので、\(\leq_M\)の\(\textrm{IncrFirst}\)不変性より\(M'\)は単項である。

簡約性と係数の関係から\(M\)は条件(A)と(B)を満たす。特に\((M_j)_{j=j'_0}^{j'_1}\)は条件(A)を満たし、従って\(\leq_M\)の\(\textrm{IncrFirst}\)不変性より\(M'\)は条件(A)を満たす。また\(M'\)は単項でかつ\(M'_{0,0} = M_{1,j'_0} = M'_{1,0}\)であるので\(M'\)は条件(B)を満たす。従って簡約性と係数の関係より\(M'\)は簡約である。

\(\textrm{Red}\)の\(\textrm{IncrFirst}\)不変性より\(N = \textrm{Red}((M_j)_{j=j'_0}^{j'_1}) = \textrm{Red}(\textrm{IncrFirst}^{M_{0,j'_0} - M_{1,j'_0}}(M')) = \textrm{Red}(M') = M'\)である。従って\(\textrm{IncrFirst}^{M_{0,j'_0} - M_{1,j'_0}}(N) = \textrm{IncrFirst}^{M_{0,j'_0} - M_{1,j'_0}}(M') = (M_j)_{j=j'_0}^{j'_1}\)である。□

系（\(1\)列ペア数列の基本性質）

任意の\(M \in T_{\textrm{PS}}\)に対し、以下は同値である：

(1) \(\textrm{Lng}(M) = 1\)かつ\(M\)は簡約である。

(2) 一意な\(v \in \mathbb{N}\)が存在して\(M = ((v,v))\)である。

証明：

\(\textrm{Lng}(M) = 1\)かつ\(M\)は簡約であるとする。

簡約性と係数の関係から\(M\)は条件(A)と(B)を満たす。特に\(M\)が条件(B)を満たすので一意な\(v \in \mathbb{N}\)が存在して\(M_0 = (v,v)\)である。

\(\textrm{Lng}(M) = 1\)より、\(M = (M_0) = ((v,v))\)である。

一意な\(v \in \mathbb{N}\)が存在して\(M = ((v,v))\)であるとする。

\(M\)は条件(A)と(B)を満たすので、簡約性と係数の関係からは簡約である。また\(\textrm{Lng}(M) = 1\)である。□

## 標準形[]

部分集合\(S \subset T_{\textrm{PS}}\)であって以下を満たすもののうち最小のものを\(ST_{\textrm{PS}}\)と置く[23]：

- 任意の\(u,v \in \mathbb{N}\)に対し、\(u \leq v\)ならば\(((j,j))_{j=u}^{v} \in S\)である。

- 任意の\(M \in S\)と\(n \in \mathbb{N}_{+}\)に対し、\(M[n] \in S\)である。

ここでは\(ST_{\textrm{PS}}\)に属するペア数列のことを標準形と呼ぶ。通常は標準形ペア数列と言ったら\(3\)行バシク行列\(((0,0,0)(1,1,1))\)の展開で現れるものを指すが、それは上の条件において\(u = 0\)としたものに対応するため、ここでの流儀では標準形が通常より広い対象を指す用語となる。

命題（標準形の簡約性）

\(ST_{\textrm{PS}} \subset RT_{\textrm{PS}}\)である。

証明：

任意の\(u,v \in \mathbb{N}\)に対し、\(u \leq v\)ならば\(((j,j))_{j=u}^{v}\)は簡約である。従って簡約性が基本列で保たれることと\(ST_{\textrm{PS}}\)の定義に基づく最小性から従う。□

各\(k \in \mathbb{N}\)に対し、部分集合\(S_kT_{\textrm{PS}} \subset ST_{\textrm{PS}}\)を以下のように再帰的に定める：

- \(k = 0\)ならば\(S_kT_{\textrm{PS}} := \{((j,j))_{j=u}^{v} \mid (u,v) \in \mathbb{N}^2 \land u \leq v\}\)である。

- \(k > 0\)ならば\(S_kT_{\textrm{PS}} := \{M[n] \mid M \in S_{k-1}T_{\textrm{PS}} \wedge n \in \mathbb{N}\}\)である。

\(ST_{\textrm{PS}}\)の定義に基づく最小性より、\(ST_{\textrm{PS}} = \bigcup_{k \in \mathbb{N}} S_kT_{\textrm{PS}}\)である。

命題（標準形の単項成分が標準形であること）

任意の\(k \in \mathbb{N}\)と\(M \in S_kT_{\textrm{PS}}\)に対し、\(P(M) \in S_kT_{\textrm{PS}}^{< \omega}\)である。

証明：

\(k\)に関する数学的帰納法で示す。

\(k = 0\)ならば\(S_kT_{\textrm{PS}}\)の定義から\(M\)が零項または単項であるので従う。

\(k > 0\)とする。

\(J_1 := \textrm{Lng}(P(M))-1\)と置く。

\(S_kT_{\textrm{PS}}\)の定義から、ある\(M' \in S_{k-1}T_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)が存在して\(M = M'[n]\)である。帰納法の仮定より\(P(M') \in S_{k-1}T_{\textrm{PS}}^{< \omega}\)である。

\(J_0 := \textrm{Lng}(P(M'))-1\)と置く。

\(\textrm{Lng}(P(M')_{J_0}) = 1\)とする。

\(J_0 = 0\)ならば、\(M = M'[n] = P(M')_{J_0}[n] = P(M')_{J_0} \in S_{k-1}T_{\textrm{PS}}\)であるので帰納法の仮定より従う。

\(J_0 > 0\)ならば、\(P\)と基本列の関係 (1)より\(P(M) = (P(M')_J)_{J=0}^{J_0-1} \in S_{k_0-1}T_{\textrm{PS}}^{< \omega}\)である。

\(\textrm{Lng}(P(M')_{J_0}) > 1\)とする。

\(P\)と基本列の関係 (2)より\(P(M) = (P(M')_J)_{J=0}^{J_1} \oplus_{\mathbb{N}^2} P(P(M')_{J_0}[n])\)である。

\((P(M')_J)_{J=0}^{J_0-1} \in S_{k_0-1}T_{\textrm{PS}}^{< \omega}\)であり、\(P(M')_{J_0} \in S_{k_0-1}T_{\textrm{PS}}\)より帰納法の仮定から\(P(P(M')_{J_0}[n]) \in S_{k_0-1}T_{\textrm{PS}}^{< \omega}\)であるので、\(P(M) \in S_{k_0-1}T_{\textrm{PS}}^{< \omega}\)である。□

命題（標準形の始切片への遺伝性）

任意の\(M \in ST_{\textrm{PS}}\)と\(j'_1 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置くと、\(j'_1 \leq j_1\)ならば\((M_j)_{j=0}^{j'_1}\)は標準形である。

証明：

\(M[1] = \textrm{Pred}(M)\)であるため、\(j_1-m_1\)に関する数学的帰納法より即座に従う。

## 降順性[]

\(Q \in T_{\textrm{PS}}^{< \omega}\)とする。

- \(J_1 := \textrm{Lng}(Q)-1\)と置く。

- \(Q\)が降順であるとは、任意の\(J'_0,J'_1 \in \mathbb{N}\)に対し、\(J'_0 \leq J'_1 \leq J_1\)ならば以下が成り立つということである：

- \((Q_{J'_0})_{0,0} \geq (Q_{J'_1})_{0,0}\)である。

- \((Q_{J'_0})_{0,0} = (Q_{J'_1})_{0,0}\)ならば、\((Q_{J'_0})_{1,0} \geq (Q_{J'_1})_{1,0}\)である。

\(P\)の各成分の左端の単調性より、任意の\(M \in T_{\textrm{PS}}\)に対し以下は同値である：

(1) \(P(M)\)は降順である。

(2) 任意の\(J'_0,J'_1 \in \mathbb{N}\)に対し、\(J'_0 \leq J'_1 \leq J_1\)かつ\((P(M)_{J'_0})_{0,0} = (P(M)_{J'_1})_{0,0}\)ならば、\((P(M)_{J'_0})_{1,0} \geq (P(M)_{J'_1})_{1,0}\)である。

従って特に\(M\)が単項の時、\(j'_1 := \textrm{TrMax}(M)\)と置き、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(j'_1 < j_1\)である場合は\(\textrm{Br}(M)\)の降順性の判定には(2)を\((M_j)_{j=j'_1}^{j_1}\)に対し確認すれば良い。

命題（標準形の切片と\(\textrm{Br}\)の降順性の関係）

任意の\(M \in ST_{\textrm{PS}}\)と\(j'_0,j'_1 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(j'_0 < j'_1 \leq j_1\)として\(M' := (M_j)_{j=j'_0}^{j'_1}\)と置くと、\((0,j'_0) \leq_M (0,j'_1)\)ならば\(M'\)は単項かつ\(\textrm{Br}(M')\)は降順である。

証明：

\(M'\)の単項性は単項性の直系先祖による切片への遺伝性より従う。

\(ST_{\textrm{PS}} = \bigcup_{k \in \mathbb{N}} S_kT_{\textrm{PS}}\)より、一意な\(k_0 \in \mathbb{N}\)が存在して\(M \in S_{k_0}T_{\textrm{PS}}\)かつ任意の\(k \in \mathbb{N}\)に対し\(k < k_0\)ならば\(M \notin S_kT_{\textrm{PS}}\)である。

\((0,j'_0) \leq_M (0,j'_1)\)と\(P\)の各成分の非複項性と標準形の単項成分が標準形であることから、\(M\)は非複項であるとしてよい。\(M\)が零項であるならば、\(j'_0 = j'_1 = 0\)となり\(M' = M \in ST_{\textrm{PS}}\)である。以下では\(M\)が単項であるとする。

\(M\)が単項であるという条件下で\(M'\)が標準形となることを\(k_0\)に関する数学的帰納法で示す。

\(k_0 = 0\)ならば、\(M = ((j,j))_{j=0}^{j_1}\)であるため\(M' = ((j,j))_{j=j'_0}^{j'_1}\)であり、\(\textrm{Br}(M') = ()\)となるので\(\textrm{Br}(M')\)は降順である。

\(k_0 > 0\)とする。

\(M \in S_{k_0}T_{\textrm{PS}}\)より、ある\(N \in S_{k_0-1}T_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)が存在して\(N[n] = M\)となる。

標準形の単項成分が標準形であることから\(P(N)_0 \in S_{k_0-1}T_{\textrm{PS}}\)であるので、\(M \neq P(N)_0\)である。従って\(M\)の単項性と\(P\)と基本列の関係より、\(N\)は単項である。

\(j_1^N := \textrm{Lng}(N)-1\)と置く。

\(M' = (N_j)_{j=j'_0}^{j'_1}\)ならば、\((0,j'_0) \leq_M (0,j'_1)\)より\((0,j'_0) \leq_N (0,j'_1)\)であるので、帰納法の仮定から\(\textrm{Br}(M')\)は降順である。

\(M = \textrm{Pred}(N)\)ならば、\(j'_1 \leq j_1 = j_1^N-1 < j_1^N\)より\(M' = (N_j)_{j=j'_0}^{j'_1}\)であるので、既に示したように\(\textrm{Br}(M')\)は降順である。

\(n = 1\)ならば、\(M = N[1] = \textrm{Pred}(N)\)であるので、既に示したように\(\textrm{Br}(M')\)は降順である。

以下では\(n > 1\)とする。

\(N\)の単項性から\((0,0) \leq_N (0,j_1^N)\)かつ\(j_1^N > 0\)であるので、一意な\(j_0^N \in \mathbb{N}\)が存在して\((0,j_0^N) <_N^{\textrm{Next}} (0,j_1^N)\)となる。

\(N' := (N_j)_{j=j'_0}^{j_1^N}\)と置く。

\(J_1 := \textrm{Lng}(\textrm{Br}(N'))-1\)と置く。

\(N_{1,j_1^N} = 0\)とする。

\(M = (N_j)_{j=0}^{j_0^N-1} \bigoplus_{\mathbb{N}^2} ((N_j)_{j=j_0^N}^{j_1^N-1})_{k=0}^{n-1}\)であり、\(j_1 = j_0^N+(n+1)(j_1^N-j_0^N)-1\)である。

\(j'_1 \leq j_0^N\)ならば\(M' = (N_j)_{j=j'_0}^{j'_1}\)かつ\((0,j'_0) \leq_N (0,j'_1)\)となるので、帰納法の仮定より\(\textrm{Br}(M') = \textrm{Br}((N_j)_{j=j'_0}^{j'_1})\)は降順である。

\(j'_0 < j_0^N < j'_1\)とする。

\(j'_1-j_0^N\)を\(j_1^N-j_0^N\)で割った商と余りをそれぞれ\(q,r \in \mathbb{N}\)と置く。

\(q < n\)かつ\(r < j_1^N-j_0^N\)であり、\(j'_1 = j_0^N+q(j_1^N-j_0^N)+r\)である。

\((N[q+1]_j)_{j=j'_0}^{j'_1} = M'\)であるので、\(q = n-1\)として良い。

\((0,j_0^N) <_N^{\textrm{Next}} (0,j_1^N)\)と直系先祖の木構造 (1)より\((0,j_0^N) \leq_N (0,j_1^N-1)\)かつ\((0,j_0^N) \leq_N (0,j_0^N+r)\)すなわち\((0,j_0^N+(n-1)(j_1^N-j_0^N)) \leq_M (0,j'_1)\)である。更に\((0,j'_0) \leq_M (0,j'_1)\)かつ\(j'_0 < j_0^N \leq j_0^N+(n-1)(j_1^N-j_0^N) \leq j'_1\)であるので、\(P\)の各成分の非複項性より\((0,j'_0) \leq_M (0,j_0^N+(n-1)(j_1^N-j_0^N))\)である。

\(M_{j_0^N+(n-1)(j_1^N-j_0^N)} = M_{j_0^N} = N_{j_0^N}\)より\((M_j)_{j=0}^{j_0^N-1} \oplus_{\mathbb{N}^2} (M_{j_0^N+(n-1)(j_1^N-j_0^N)}) = (M_j)_{j=0}^{j_0^N} = (N_j)_{j=0}^{j_0^N}\)であるので、\((0,j'_0) \leq_M (0,j_0^N+(n-1)(j_1^N-j_0^N))\)より\((0,j'_0) \leq_N (0,j_0^N)\)である。以上より\((0,j'_0) \leq_N (0,j_0^N) \leq_N (0,j_1^N-1)\)かつ\((0,j'_0) \leq_N (0,j_0^N) \leq_N (0,j_1^N)\)である。

帰納法の仮定から、\(N'\)は単項かつ\(\textrm{Br}(N')\)は降順である。

\(N_{0,j_1^N} = 0\)かつ\(j_1^N-j'_0 > j_0^N-j'_0 > 0\)より、\(\textrm{TrMax}(N') < j_1^N-j'_0\)となる。従って\(J_1 \geq 0\)である。

\(j_0^N-j'_0 > 0\)であるので、\((0,j_0^N) <_N^{\textrm{Next}} (0,j_1^N)\)より\((0,j_0^N-j'_0) <_{N'}^{\textrm{Next}} (0,j_1^N-j'_0)\)である。また\(N'\)の単項性から\((0,0) \leq_{N'} (0,j_0^N-j'_0)\)であるので、一意な\(j_{-1} \in \mathbb{N}\)が存在して\((0,j_{-1}) <_{N'}^{\textrm{Next}} (0,j_0^N-j'_0)\)である。

\(j_0^N-j'_0 \leq \textrm{TrMax}(N')\)とする。

\((0,j_0^N-j'_0) <_{N'}^{\textrm{Next}} (0,j_1^N-j'_0)\)と\(P\)の各成分の非複項性より\(\textrm{FirstNodes}(N')_{J_1} = j_1^N-j'_0\)かつ\(\textrm{Br}(N')_{J_1} = (N_{j_1^N})\)であるので、\(\textrm{Br}(M') = (\textrm{Br}(N')_J)_{J=0}^{J_1-1} \oplus_{T_{\textrm{PS}}} ((N_j)_{j=j_0^N}^{j_1^N-1})_{k=1}^{n-2} \oplus_{T_{\textrm{PS}}} ((N_j)_{j=j_0^N}^{j_0^N+r})\)となる。

従って\(\textrm{Lng}(\textrm{Br}(M'))-1 = J_1+n-2\)かつ\(((\textrm{Br}(M')_J)_0)_{J=0}^{J_1+n-2} = ((\textrm{Br}(N')_J)_0)_{J=0}^{J_1-1} \oplus_{\mathbb{N}^2} (N_{j_0^N})_{k=0}^{n-1}\)となる。\(N_{0,j_0^N} < N_{0,j_1^N} = (\textrm{Br}(N')_{J_1})_{0,0}\)より、\(\textrm{Br}(M')\)は降順である。

\(j_{-1} \leq \textrm{TrMax}(N') < j_0^N-j'_1\)とする。

\((0,j_{-1}) <_{N'}^{\textrm{Next}} (0,j_0^N-j'_0)\)と\(P\)の各成分の非複項性より\(\textrm{FirstNodes}(N')_{J_1} = j_0^N-j'_0\)かつ\(\textrm{Br}(N')_{J_1} = ((N_j)_{j=j_0^N}^{j_1^N})\)であるので、\(\textrm{Br}(M') = (\textrm{Br}(N')_J)_{J=0}^{J_1-1} \oplus_{T_{\textrm{PS}}} ((N_j)_{j=j_0^N}^{j_1^N-1})_{k=0}^{n-2} \oplus_{T_{\textrm{PS}}} ((N_j)_{j=j_0^N}^{j_0^N+r})\)となる。

従って\(\textrm{Lng}(\textrm{Br}(M'))-1 = J_1+n-1\)かつ\(((\textrm{Br}(M')_J)_0)_{J=0}^{J_1+n-1} = ((\textrm{Br}(N')_J)_0)_{J=0}^{J_1-1} \oplus_{\mathbb{N}^2} (N_{j_0^N})_{k=0}^{n-1}\)となる。\(N_{j_0^N} = N_{\textrm{FirstNodes}(N')_{J_1}+j'_0} = (\textrm{Br}(N')_{J_1})_0\)より、\(\textrm{Br}(M')\)は降順である。

\(\textrm{TrMax}(N') < j_{-1}\)とする。

\(P\)の各成分の非複項性より\(\textrm{FirstNodes}(N')_{J_1} \leq j_{-1}\)であるので、\(\textrm{Br}(M') = (\textrm{Br}(N')_J)_{J=0}^{J_1-1} \oplus_{T_{\textrm{PS}}} ((M_j)_{j = \textrm{FirstNodes}(N')_{J_1}+j'_0}^{j'_1})\)となる。

従って\(\textrm{Lng}(\textrm{Br}(M'))-1 = J_1\)かつ\(((\textrm{Br}(M')_J)_0)_{J=0}^{J_1} = ((\textrm{Br}(N')_J)_0)_{J=0}^{J_1-1} \oplus_{\mathbb{N}^2} (M_{\textrm{FirstNodes}(N')_{J_1}+j'_0})\)となる。\(\textrm{FirstNodes}(N')_{J_1}+j'_0 < j_{-1}+j'_0 < j_0^N < j_1^N\)より\(M_{\textrm{FirstNodes}(N')_{J_1}+j'_0} = N_{\textrm{FirstNodes}(N')_{J_1}+j'_0} = (\textrm{Br}(N')_{J_1})_0\)より、\(\textrm{Br}(M')\)は降順である。

\(j_0^N \leq j'_0\)とする。

\(j'_0-j_0^N\)を\(j_1^N-j_0^N\)で割った商と余りをそれぞれ\(q,r \in \mathbb{N}\)と置く。

\(r' := j_1-(j_0^N+q(j_1^N-j_0^N))\)と置く。

\(q < n\)かつ\(r < j_1^N-j_0^N\)であり、\(j'_0 = j_0^N+q(j_1^N-j_0^N)+r\)かつ\(j'_0 = j_0^N+q(j_1^N-j_0^N)+r'\)である。

\((0,j'_0) \leq_M (0,j'_1)\)と\(P\)の各成分の非複項性から\(j'_1 < j_0^N+(q+1)(j_1^N-j_0^N)\)であるので、\(r \leq r' < j_1^N-j_0^N\)である。

\((0,j'_0) \leq_M (0,j'_1)\)かつ\((M_j)_{j=j_0^N+q(j_1^N-j_0^N)}^{j_0^N+(q+1)(j_1^N-j_0^N)-1} = (N_j)_{j=j_0^N}^{j_1^N-1}\)より\((0,j_0^N+r) \leq_N (0,j_0^N+r')\)である。

\(M' = (N_j)_{j=j_0^N+r}^{j_0^N+r'}\)であるので、帰納法の仮定より\(\textrm{Br}(M')\)は降順である。

\(N_{1,j_1^N} > 0\)とする。

\((1,j_{-2}^N) <_N^{\textrm{Next}} (1,j_1^N)\)を満たす一意な\(j_{-2}^N \in \mathbb{N}\)が存在しないとすると、\(M = N[n] = \textrm{Pred}(N)\)となるので、既に示したように\(\textrm{Br}(M')\)は降順である。

\((1,j_{-2}^N) <_N^{\textrm{Next}} (1,j_1^N)\)を満たす一意な\(j_{-2}^N \in \mathbb{N}\)が存在するとする。

\(\delta := N_{0,j_1^N} - N_{0,j_{-2}^N}\)と置く。

\((1,j_{-2}^N) <_N^{\textrm{Next}} (1,j_1^N)\)より\(\delta > 0\)であり、\(M = (N_j)_{j=0}^{j_{-2}^N-1} \oplus_{\mathbb{N}^2} \bigoplus_{\mathbb{N}^2} (\textrm{IncrFirst}^{k \delta}((N_j)_{j=j_{-2}^N}^{j_1^N}))_{k=0}^{n-1}\)である。

任意の\(k \in \mathbb{N}\)に対し、\(k < n-1\)ならば\((0,j_{-2}^N+k(j_1^N-j_{-2}^N)) \leq_M (0,j_{-2}^N+(k+1)(j_1^N-j_{-2}^N))\)であることを示す。

\((M_j)_{j =j_{-2}^N+k(j_1^N-j_{-2}^N)}^{j_{-2}^N+(k+1)(j_1^N-j_{-2}^N)} = \textrm{IncrFirst}^{k \delta}((N_j)_{j=j_{-2}^N}^{j_1^N-1}) \oplus_{\mathbb{N}^2} \textrm{IncrFirst}^{(k+1)\delta}((N_{j=j_{-2}^N}))\)である。更に\(M_{0,j_1^N} = M_{0,j_{-2}^N}+\delta\)より\((M_{0,j})_{j =j_{-2}^N+k(j_1^N-j_{-2}^N)}^{j_{-2}^N+(k+1)(j_1^N-j_{-2}^N)} = ((N_{0,j}+k \delta)_{j=j_{-2}^N}^{j_1^N})\)である。

\((1,j_{-2}^N) <_N^{\textrm{Next}} (1,j_1^N)\)より\((0,j_{-2}^N) \leq_M (0,j_1^N)\)であるので、\((M_{0,j})_{j =j_{-2}^N+k(j_1^N-j_{-2}^N)}^{j_{-2}^N+(k+1)(j_1^N-j_{-2}^N)} = ((N_{0,j}+k \delta)_{j=j_{-2}^N}^{j_1^N})\)より\((0,j_{-2}^N+k(j_1^N-j_{-2}^N)) \leq_M (0,j_{-2}^N+(k+1)(j_1^N-j_{-2}^N))\)である。

\((0,j_{-2}^N+(n-1)(j_1^N-j_{-2}^N)) \leq_M (0,j_1)\)であることを示す。

\((M_j)_{j =j_{-2}^N+(n-1)(j_1^N-j_{-2}^N)}^{j_1} = \textrm{IncrFirst}^{(n-1)\delta}((N_j)_{j=j_{-2}^N}^{j_1^N-1})\)であるので、\((M_{0,j})_{j =j_{-2}^N+(n-1)(j_1^N-j_{-2}^N)}^{j_1} = ((N_{0,j}+(n-1)\delta)_{j=j_{-2}^N}^{j_1^N-1})\)である。

\((1,j_{-2}^N) <_N^{\textrm{Next}} (1,j_1^N)\)より\((0,j_{-2}^N) \leq_M (0,j_1^N)\)であり、直系先祖の木構造 (1)より\((0,j_{-2}^N) \leq_M (0,j_1^N-1)\)であるので、\((M_{0,j})_{j =j_{-2}^N+(n-1)(j_1^N-j_{-2}^N)}^{j_1} = ((N_{0,j}+(n-1)\delta)_{j=j_{-2}^N}^{j_1^N-1})\)より\((0,j_{-2}^N+(n-1)(j_1^N-j_{-2}^N)) \leq_M (0,j_1)\)である。

以上より、\((0,j_{-2}^N) \leq_M (0,j_1)\)である。

\(j'_1 \leq j_{-2}^N\)ならば、\((N_j)_{j=0}^{j_{-2}^N} = (M_j)_{j=0}^{j_{-2}^N}\)であるので\(M' = (N_j)_{j=j'_0}^{j'_1}\)となり、既に示したように\(\textrm{Br}(M')\)は降順である。

\(j'_0 < j_{-2}^N < j'_1\)とする。

\(j_{-2}^N < j'_1 \leq j_1\)と\((0,j_{-2}^N) \leq_M (0,j_1)\)と直系先祖の木構造 (1)から\((0,j_{-2}^N) \leq_M (0,j'_1)\)である。更に\(j'_0 < j_{-2}^N < j'_1\)と\((0,j'_0) \leq_M (0,j'_1)\)から、\((0,j'_0) \leq_M (0,j_{-2}^N)\)すなわち\((0,j'_0) \leq_N (0,j_{-2}^N)\)である。\((0,j'_0) \leq_N (0,j_{-2}^N)\)と\((1,j_{-2}^N) <_N^{\textrm{Next}} (1,j_1^N)\)より\((0,j'_0) \leq_N (0,j_1^N)\)であるので、帰納法の仮定から\(N'\)が単項かつ\(\textrm{Br}(N')\)は降順である。

\(J_1 = -1\)とする。

\(j_{-2}^N = j_0^N = j_1^N-1\)かつ\(j'_1 = j_1\)となるので、\(M' = \textrm{Pred}(N) \oplus_{\mathbb{N}^2} ((N_{0,j_{-2}^N}+k \delta,N_{1,j_{-2}^N}))_{k=1}^{n-1}\)である。

従って\(\textrm{Lng}(\textrm{Br}(M')) = 1\)かつ\(\textrm{Br}(M') = (((N_{0,j_{-2}^N}+k \delta,N_{1,j_{-2}^N}))_{k=1}^{n-1})\)となり、\(\textrm{Br}(M')\)は降順である。

\(J_1 \geq 0\)とする。

\(\textrm{TrMax}(N') < j_1^N-j'_0\)である。

\(j_{-2}^N-j'_0 > 0\)であるので、\((1,j_{-2}^N) <_N^{\textrm{Next}} (1,j_1^N)\)より\((0,j_{-2}^N-j'_0) \leq_{N'} (0,j_1^N-j'_0)\)である。また\(N'\)の単項性より\((0,0) \leq_N (0,j_{-2}^N-j'_0)\)であり、\(j_{-2}^N-j'_0 > 0\)より\((0,j_{-3}) <_{N'}^{\textrm{Next}} (0,j_{-2}^N-j'_0)\)を満たす一意な\(j_{-3} \in \mathbb{N}\)が存在する。

\(j_{-2}^N-j'_0 \leq \textrm{TrMax}(N')\)とする。

\(j_{-1} := \textrm{FirstNodes}(N')_{J_1}\)と置く。

\((0,j_{-2}^N-j'_0) \leq_{N'} (0,j_1^N-j'_0)\)かつ\(j_{-2}^N-j'_0 \leq \textrm{TrMax}(N') < j_1^N-j'_0\)と\(P\)の各成分の非複項性より\((0,j_{-2}^N-j'_0) <_{N'}^{\textrm{Next}} (0,j_{-1})\)であるので、\(\textrm{Br}(N')_{J_1} = (N_j)_{j=j_{-1}+j'_0}^{j_1^N}\)より\(\textrm{Br}(M') = (\textrm{Br}(N')_J)_{J=0}^{J_1-1} \oplus_{T_{\textrm{PS}}} ((M_j)_{j=j_{-1}+j'_0}^{j'_1})\)となる。

従って\(\textrm{Lng}(\textrm{Br}(M'))-1 = J_1\)かつ\(((\textrm{Br}(M')_J)_0)_{J=0}^{J_1} = ((\textrm{Br}(N')_J)_0)_{J=0}^{J_1-1} \oplus_{\mathbb{N}^2} (M_{j_{-1}})\)となる。\(\textrm{FirstNodes}\)と\(\textrm{TrMax}\)と\(\textrm{Joints}\)の関係から\(j_{-1}+j'_0 = \textrm{FirstNodes}(N')_{J_1}+j'_0 \leq \textrm{TrMax}(N')+j'_0 < j_1^N\)となるので\(M_{j_{-1}} = N_{j_{-1}} = (\textrm{Br}(N')_{J_1})_0\)である。よって\(\textrm{Br}(M')\)は降順である。

\(j_{-3} \leq \textrm{TrMax}(N') < j_{-2}^N-j'_0\)とする。

\((0,j_{-3}) <_{N'}^{\textrm{Next}} (0,j_{-2}^N-j'_0)\)と\(P\)の各成分の非複項性より\(\textrm{FirstNodes}(N')_{J_1} = j_{-2}^N-j'_0\)かつ\(\textrm{Br}(N')_{J_1} = ((N_j)_{j=j_{-2}^N}^{j_1^N})\)であるので、\(\textrm{Br}(M') = (\textrm{Br}(N')_J)_{J=0}^{J_1-1} \oplus_{T_{\textrm{PS}}} ((N_j)_{j=j_0^N}^{j_1^N-1})_{k=1}^{n-2} \oplus_{T_{\textrm{PS}}} ((M_j)_{j=j_{-2}^N}^{j_1})\)となる。

従って\(\textrm{Lng}(\textrm{Br}(M'))-1 = J_1\)かつ\(((\textrm{Br}(M')_J)_0)_{J=0}^{J_1} = ((\textrm{Br}(N')_J)_0)_{J=0}^{J_1-1} \oplus_{\mathbb{N}^2} (N_{j_{-2}^N})\)となる。\(N_{j_{-2}^N} = (\textrm{Br}(N')_{J_1})_0\)より、\(\textrm{Br}(M')\)は降順である。

\(\textrm{TrMax}(N') < j_{-3}\)とする。

\(P\)の各成分の非複項性より\(\textrm{FirstNodes}(N')_{J_1} \leq j_{-3}\)であるので、\(\textrm{Br}(M') = (\textrm{Br}(N')_J)_{J=0}^{J_1-1} \oplus_{T_{\textrm{PS}}} ((M_j)_{j = \textrm{FirstNodes}(N')_{J_1}+j'_0}^{j'_1})\)となる。

従って\(\textrm{Lng}(\textrm{Br}(M'))-1 = J_1\)かつ\(((\textrm{Br}(M')_J)_0)_{J=0}^{J_1} = ((\textrm{Br}(N')_J)_0)_{J=0}^{J_1-1} \oplus_{\mathbb{N}^2} (M_{\textrm{FirstNodes}(N')_{J_1}})\)となる。\(\textrm{FirstNodes}(N')_{J_1}+j'_0 \leq j_{-3}+j'_0 \leq j_{-2}+j'_0 < j_1^N\)より\(M_{\textrm{FirstNodes}(N')_{J_1}+j'_0} = N_{\textrm{FirstNodes}(N')_{J_1}+j'_0} = (\textrm{Br}(N')_{J_1})_0\)より、\(\textrm{Br}(M')\)は降順である。

\(j_{-2}^N \leq j'_0\)とする。

\(j'_0-j_{-2}^N\)を\(j_1^N-j_{-2}^N\)で割った商と余りをそれぞれ\(q,r \in \mathbb{N}\)と置く。

\(q < n\)かつ\(r < j_1^N-j_0^N\)であり、\(j'_0 = j_0^N+q(j_1^N-j_0^N)+r\)である。

\((N[n-q]_j)_{j=j'_{-2}+r}^{j'_{-2}+(n-q)(j_1^N-j_{-2}^N)-1} = (M_j)_{j=j'_0}^{j_1}\)と\((0,j'_0) \leq_M (0,j'_1)\)より、\((0,j'_{-2}+r) \leq_{N[n-q]} (0,j'_1-q(j_1^N-j_{-2}^N))\)である。\((N[n-q]_j)_{j=j'_{-2}+r}^{j'_1-q(j_1^N-j_{-2}^N)} = M'\)より、\(q = 0\)として良い。

\(j'_1 < j_1^N\)ならば、\((M_j)_{j=0}^{j_1^N-1} = \textrm{Pred}(N)\)より\(M' = (N_j)_{j=j'_0}^{j'_1}\)であり、\((0,j'_0) \leq_M (0,j'_1)\)より\((0,j'_0) \leq_N (0,j'_1)\)となるので、帰納法の仮定より\(\textrm{Br}(M')\)は降順である。

\(j'_1 \geq j_1^N\)とする。

任意の\(k \in \mathbb{N}\)に対し\(k < n-1\)ならば\((0,j_0^N+k(j_1^N-j_0^N)) \leq_M (0,j_0^N+(k+1)(j_1^N-j_0^N))\)であり、かつ\((0,j_0^N+(n-1)(j_1^N-j_0^N)) \leq_M (0,j_1)\)であるので、\((0,j_1^N) = (0,j_0^N+(j_1^N-j_0^N)) \leq_M (0,j_1)\)である。従って直系先祖の木構造 (1)から\((0,j_1^N) \leq_M (0,j'_1)\)となる。

\((0,j'_0) \leq_M (0,j'_1)\)かつ\(j'_0 = j_0^N+r < j_1^N\)かつ\((0,j_1^N) \leq_M (0,j'_1)\)より\((0,j'_0) \leq_M (0,j_1^N)\)である。更に\((M_j)_{j=0}^{j_1^N} = (N_j)_{j=0}^{j_1^N-1} \oplus_{\mathbb{N}^2} ((N_{0,j_0^N}+\delta,N_{1,j_0^N})) = (N_j)_{j=0}^{j_1^N-1} \oplus_{\mathbb{N}^2} ((N_{0,j_1^N},N_{1,j_0^N}))\)であるので\((0,j'_0) \leq_N (0,j_1^N)\)となる。

従って帰納法の仮定から\(N'\)が単項かつ\(\textrm{Br}(N')\)は降順である。また\(j'_0 < j_1^N\)かつ\((0,j'_0) \leq_N (0,j_1^N)\)かつ\((0,j_0^N) <_N^{\textrm{Next}} (0,j_1^N)\)から\((0,j'_0) \leq_M (0,j_0^N)\)となる。

\(j_1^N-j'_0 \leq \textrm{TrMax}(N')\)とする。

\(j'_0 \leq j_0^N < j_1^N \leq \textrm{TrMax}(N')+j'_0\)より\((1,j_1^N-1) <_N^{\textrm{Next}} (1,j_1^N)\)となるので、\(j_{-2}^N = j_0^N = j_1^N-1\)である。また\(j_{-2}^N \leq j'_0 \leq j_0^N\)より\(j'_0 = j_0^N\)となる。\(M = N[n] = \textrm{Pred}(N) \oplus_{\mathbb{N}^2} ((N_{0,j_{-2}^N}+k \delta,N_{1,j_{-2}^N}))_{k=1}^{n-1}\)であるので、\(M' = ((N_{0,j_{-2}^N}+k \delta,N_{1,j_{-2}^N}))_{k=0}^{n-1}\)である。

従って\(\textrm{Lng}(\textrm{Br}(M'))-1 = 0\)かつ\(\textrm{Br}(M') = (((N_{0,j_{-2}^N}+k \delta,N_{1,j_{-2}^N}))_{k=1}^{j'_1-j'_0})\)であり、\(\textrm{Br}(M')\)は降順である。

\(j_0^N-j'_0 \leq \textrm{TrMax}(N') < j_1^N-j'_0\)とする。

\(P\)の各成分の非複項性より\(\textrm{FirstNodes}(N')_{J_1} = j_1^N-j'_0 \leq j'_1-j'_0\)である。\((M_j)_{j=0}^{j_1^N} = \textrm{Pred}(N) \oplus_{\mathbb{N}^2} ((N_{0,j_0^N}+\delta,N_{1,j_0^N})) = \textrm{Pred}(N) \oplus_{\mathbb{N}^2} ((N_{0,j_1^N},N_{1,j_{-2}^N}))\)であるので、\(\textrm{Br}(M') = (\textrm{Br}(N')_J)_{J=0}^{J_1-1} \oplus_{T_{\textrm{PS}}} ((M_j)_{j=j_1^N}^{j_1})\)である。

従って\(\textrm{Lng}(\textrm{Br}(M'))-1 = J_1\)かつ\(((\textrm{Br}(M')_J)_0)_{J=0}^{J_1} = ((\textrm{Br}(N')_J)_0)_{J=0}^{J_1-1} \oplus_{\mathbb{N}^2} (M_{j_1^N})\)となる。\(M_{0,j_1^N} = N_{0,j_1^N} = N_{0,\textrm{FirstNodes}(N')_{J_1}+j'_0} = (\textrm{Br}(N')_{J_1})_{0,0}\)かつ\(M_{1,j_1^N} = N_{1,j_{-2}^N} < N_{1,j_1^N} = N_{1,\textrm{FirstNodes}(N')_{J_1}+j'_0} = (\textrm{Br}(N')_{J_1})_{1,0}\)となるので、\(\textrm{Br}(M')\)は降順である。

\(\textrm{TrMax}(N') < j_0^N-j'_0\)とする。

\(j_{-1} := \textrm{FirstNodes}(N')_{J_1}\)と置く。

\(P\)の各成分の非複項性より\(j_{-1} \leq j_0^N-j'_0 < j_1^N-j'_0 \leq j'_1-j'_0\)である。\((M_j)_{j=0}^{j_{-1}+j'_0} = (N_j)_{j=0}^{j_{-1}+j'_0}\)であるので、\(\textrm{Br}(M') = (\textrm{Br}(N')_J)_{J=0}^{J_1-1} \oplus_{T_{\textrm{PS}}} ((M_j)_{j=j_{-1}+j'_0}^{j_1})\)である。

従って\(\textrm{Lng}(\textrm{Br}(M'))-1 = J_1\)かつ\(((\textrm{Br}(M')_J)_0)_{J=0}^{J_1} = ((\textrm{Br}(N')_J)_0)_{J=0}^{J_1-1} \oplus_{\mathbb{N}^2} (M_{j'_{-1}+j'_0})\)となる。\(\textrm{FirstNodes}\)と\(\textrm{TrMax}\)と\(\textrm{Joints}\)の関係から\(j_{-1}+j'_0 = \textrm{FirstNodes}(N')_{J_1}+j'_0 \leq \textrm{TrMax}(N')+j'_0 < j_0^N < j_1^N\)であるので、\(M_{j_{-1}+j'_0} = N_{j_{-1}+j'_0} = N_{\textrm{FirstNodes}(N')_{J_1}+j'_0} = (\textrm{Br}(N')_{J_1})_0\)である。よって\(\textrm{Br}(M')\)は降順である。□

命題（標準形の単項成分が降順であること）

任意の\(M \in ST_{\textrm{PS}}\)と\(J'_0,J'_1 \in \mathbb{N}\)に対し、\(J_1 := \textrm{Lng}(P(M))-1\)と置くと、\(J'_0 \leq J'_1 \leq J_1\)かつ\((P(M)_{J'_0})_{0,0} = (P(M)_{J'_1})_{0,0}\)ならば、\((P(M)_{J'_0})_{1,0} \geq (P(M)_{J'_1})_{1,0}\)である。

証明：

\(k_0 := \min \{k \in \mathbb{N} \mid M \in S_kT_{\textrm{PS}}\}\)と置く[24]。\(J_1 \geq J'_1 > J'_0 \geq 0\)より\(P\)の各成分の非複項性 (2)から\(M\)は複項であるので、\(k_0 > 0\)である。従ってある\(M' \in S_{k_0-1}T_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)が存在して\(M = M'[n]\)となる。

\(M\)が複項であることと非複項性と基本列の関係から、\(k_0-1 > 0\)すなわち\(k_0 > 1\)かつ\(n > 1\)である。

従ってある\(N \in S_{k_0-2}T_{\textrm{PS}}\)と\(n' \in \mathbb{N}_{+}\)が存在して\(M' = N[n']\)となる。

<<<MISSING line 1628 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1629 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1630 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1631 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1632 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1633 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1634 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1635 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1636 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1637 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1638 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1639 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1640 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1641 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1642 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1643 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1644 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1645 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1646 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1647 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1648 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1649 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1650 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1651 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1652 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1653 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1654 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1655 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1656 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1657 — recover from original.html via tools/make_content.py>>>
\(\textrm{Lng}(P(M')_{J_0}) = 1\)ならば、\(P\)と基本列の関係と\(P\)の各成分の非複項性 (2)から\(J_0 > 0\)かつ\(P(M) = (P(M')_J)_{J=0}^{J_0-1}\)であるので、帰納法の仮定から従う。
<<<MISSING line 1659 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1660 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1661 — recover from original.html via tools/make_content.py>>>
\(P\)と基本列の関係から\(P(M) = (P(M')_J)_{J=0}^{J_0-1} \oplus_{T_{\textrm{PS}}} P(P(M')_{J_0}[n])\)である。
<<<MISSING line 1663 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1664 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1665 — recover from original.html via tools/make_content.py>>>
\(P\)の各成分の非複項性 (1)から\(P(M')_{J_0}\)は複項でなく、非複項性と基本列の関係から\(((P(P(M')_{J_0}[n])_J)_{0,0})_{J=0}^{J_{-1}}\)は\((P(M')_{J_0})_{0,0}\)のみを成分に持つ。
<<<MISSING line 1667 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1668 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1669 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1670 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1671 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1672 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 1673 — recover from original.html via tools/make_content.py>>>
# Buchholzの表記系への翻訳[]
<<<MISSING line 1675 — recover from original.html via tools/make_content.py>>>
後に定義する標準形ペア数列システムの停止性を証明するための準備として、ペア数列からBuchholzの表記系への翻訳写像\(\textrm{Trans}\)を定め、その性質を調べる。
<<<MISSING line 1677 — recover from original.html via tools/make_content.py>>>
## Buchholzの表記系[]

以下では\(T_{\textrm{B}}\)は\(D_{\omega}\)を含まない項全体のなすBuchholozの表記系\(T\)[25]の部分集合を表す。\(T_{\textrm{B}}\)は順序数項[26]とは限らないことに注意する。最終的に用いるのは順序数項であるが、最初から順序数項に制限すると議論の過程で現れる各項が順序数項であるか否かを逐一判定する必要があるので非常に冗長となる。従って標準形ペアシステムの停止性を証明する直前の段階までは順序数項に制限せず議論する。

\(T_{\textrm{B}}\)の要素間の関係\(<\)は通常の強順序[27]を表し、\(T_{\textrm{B}}\)の要素間の関係\(\leq\)は「\(<\)または\(=\)」の略記を表し、\(T_{\textrm{B}}\)の要素間の演算\(+\)は加法[28]を表し、\(n \in \mathbb{N}\)に対し\(T_{\textrm{B}}\)の要素への\(\times n\)は\(n\)倍[29]を表し、\(T_{\textrm{B}}\)の要素に対する\([]\)演算子は[Buc1] pp. 203--204の\([]\)演算子の再帰的定義のうち([].4) (ii)のみ[Buc2] p. 6のDefinitionの6の規則に変えたもの[30]として得られる基本列[31]を表し、\(\textrm{dom}\)は各項ごとに\([]\)演算子の定義域[32]を表す。

\(0\)でも単項[33]でもないBuchholzの表記系の項を複項と呼ぶ。\(PT_{\textrm{B}} \subset T_{\textrm{B}}\)で\(D_{\omega}\)を含まない単項全体のなす部分集合を表し、\(MT_{\textrm{B}} \subset T_{\textrm{B}}\)で\(D_{\omega}\)を含まない複項全体のなす部分集合を表す。

\(\underline{(}\)で\(T_{\textrm{B}}\)における字母\(\textrm{(}\)を表し、\(\underline{,}\)で\(T_{\textrm{B}}\)における字母\(\textrm{,}\)を表し、\(\underline{)}\)で\(T_{\textrm{B}}\)における字母\(\textrm{)}\)を表す。\(T_{\textrm{B}}\)における字母\(\underline{(}\)と\(\underline{,}\)と\(\underline{)}\)と\(0\)と各\(u \in \omega+1\)に対する\(D_u\)全体の集合を\(\Sigma\)と置く。

\(t \in PT_{\textrm{B}}^{< \omega}\)とする。

- \(t = ()\)ならば\(t' := 0 \in \Sigma\)と置く。

- \(t \neq ()\)とする。

- \(j_1 := \textrm{Lng}(t)-1\)と置く。

- \(s_0 := \underline{(}\)と置く。

- \(0 < j < j_1\)を満たす各\(j \in \mathbb{N}\)に対して\(s_j := s_{j-1} t_{j-1} \underline{,}\)と置く。

- \(t' := s_{j_1-1} t_{j_1} \underline{)} \in \Sigma\)と置く。

\(j_1 = -1\)ならば\(t' = 0 \in T_{\textrm{B}}\)である。\(j_1 = 0\)ならば\(t' = \underline{(} t_0 \underline{)}\)より縮約規則\(\{(p) = p \mid p \in PT_{\textrm{B}}\}\)の下で\(t'\)は\(t_0 \in PT_{\textrm{B}}\)と同一視される。\(j_1 > 0\)ならば\(t' \in T_{\textrm{B}} \setminus (\{0\} \cup PT_{\textrm{B}})\)である。従っていずれの場合も\(T_{\textrm{B}}\)の項を定め、それを\(\Sigma_{\textrm{B}} t\)と表記する。

写像
\begin{eqnarray*}
P \colon T_{\textrm{B}} & \to & PT_{\textrm{B}}^{< \omega} \\
t & \mapsto & P(t)
\end{eqnarray*}
を以下のように定める：

- \(t = 0\)ならば\(P(t) := ()\)である。

- \(t \in PT_{\textrm{B}}\)ならば\(P(t) := (t)\)である。

- \(t \in MT_{\textrm{B}}\)とする。

- Buchholzの表記系の再帰的定義より、一意な\(s \in \Sigma^{<\omega}\)と\(t' \in PT_{\textrm{PS}}\)が存在して以下を満たす：

- \(t = \underline{(} s \underline{,} t' \underline{)}\)である。

- \(s \in PT_{\textrm{B}}\)または\(\underline{(} s \underline{)} \in MT_{\textrm{B}}\)である。

- \(s \in PT_{\textrm{B}}\)ならば\(P(t) := P(s) \oplus_{PT_{\textrm{B}}} (t')\)である。

- \(\underline{(} s \underline{)} \in MT_{\textrm{B}}\)ならば\(P(t) := P(\underline{(} s \underline{)}) \oplus_{PT_{\textrm{B}}} (t')\)である。

\(t \in T_{\textrm{B}}\)に対し、\(P(t)\)の各成分を\(t\)の単項成分と呼ぶ。

命題（順序数項のカッコの個数が左右で等しいこと）

任意の\(t \in T_{\textrm{B}}\)に対し、\(t\)に出現する\(\underline{(}\)の個数と\(t\)に出現する\(\underline{)}\)の個数は等しい。

証明：

Buchholzの表記系の再帰的定義より、\(\textrm{Lng}(t)\)に関する数学的帰納法から即座に従う。□

命題（順序数項の単項成分の基本性質）

任意の\(t \in T_{\textrm{B}}\)に対し、\(J_1 := \textrm{Lng}(P(t))-1\)と置くと以下が成り立つ：

(1) \(J_1 = -1\)である必要十分条件は\(t = 0\)である。

(2) \(t = \Sigma_{\textrm{B}} (P(t)_J)_{J=0}^{J_1}\)である。

証明：

\(P\)の再帰的定義より、\(\textrm{Lng}(t)\)に関する数学的帰納法から即座に従う。□

命題（部分表現の不等式の延長性）

任意の\(s,b \in \Sigma^{< \omega}\)と\(t_0, t_1 \in T_{\textrm{B}}\)に対し、\(s t_0 b \in T_{\textrm{B}}\)かつ\(s t_1 b \in T_{\textrm{B}}\)ならば、以下は同値である：

(1) \(t_0 < t_1\)である。

(2) \(s t_0 b < s t_1 b\)である。

証明：

\(<\)の再帰的定義より、\(\textrm{Lng}(s)\)に関する数学的帰納法から従う。□

## scb分解[]

写像
\begin{eqnarray*}
\textrm{RightNodes} \colon T_{\textrm{B}} & \to & \mathbb{N}^{< \omega} \\
t & \mapsto & \textrm{RightNodes}(t)
\end{eqnarray*}
を以下のように再帰的に定める：

- \(t = 0\)ならば\(\textrm{RightNodes}(t) := ()\)である。

- \(t \in PT_{\textrm{B}}\)とする。

- \(u \in \mathbb{N}\)と\(t' \in T_{\textrm{B}}\)を用いて\(t = D_u t'\)と置く。

- \(\textrm{RightNodes}(t) := (u) \oplus_{\mathbb{N}} \textrm{RightNodes}(t')\)である。

- \(t \in T_{\textrm{B}} \setminus (\{0\} \cup PT_{\textrm{B}})\)とする。

- \(J_1 := \textrm{Lng}(P(t)) - 1\)と置く。

- \(\textrm{RightNodes}(t) := \textrm{RightNodes}(P(t)_{J_1})\)である。

順序数項の不等式や加法や基本列の計算補助をするために、文字列の構文情報を与えるscb分解という概念を導入する。

\(t \in T_{\textrm{B}}\)とし、\((s,c,b) \in (\Sigma^{< \omega})^3\)とする。

- \((s,c,b)\)が\(t\)のscb分解であるとは、以下を満たすということである：

- \(t = scb\)である。

- \(t \neq 0\)ならば\(c \in PT_{\textrm{B}}\)である。

- \(b\)は\(\underline{)}\)のみからなる文字列である。

- \((s,c,b)\)が\(t\)の第\(0\)種scb分解であるとは、以下を満たすということである：

- \((s,c,b)\)は\(t\)のscb分解である。

- \(\textrm{Lng}(\textrm{RightNodes}(c)) = 2\)である。

- \(\textrm{RightNodes}(c)_1 = 0\)である。

- \((s,c,b)\)が\(t\)の第\(1\)種scb分解であるとは、以下を満たすということである：

- \((s,c,b)\)は\(t\)のscb分解である。

- \(j_1 := \textrm{Lng}(\textrm{RightNodes}(c))-1\)と置くと\(j_1 \geq 1\)である。

- \(\textrm{RightNodes}(c)_0 < \textrm{RightNodes}(c)_{j_1}\)である。

- 任意の\(j \in \mathbb{N}\)に対し、\(0 < j < j_1\)ならば\(\textrm{RightNodes}(c)_j \geq \textrm{RightNodes}(c)_{j_1}\)である。

命題（scb分解の置換可能性）

任意の\(s,b \in \Sigma^{< \omega}\)と\(c_0, c_1 \in T_{\textrm{B}}\)に対し、「\(c_0\)が単項でないまたは\(c_1\)が単項である」かつ\(s c_0 b \in T_{\textrm{B}}\)かつ\((s,c_0,b)\)が\(s c_0 b\)のscb分解であるならば、\(s c_1 b \in T_{\textrm{B}}\)かつ\((s,c_1,b)\)は\(s c_1 b\)のscb分解である。

証明：

\(s c_1 b \in T_{\textrm{B}}\)であることはBuchholzの表記系の再帰的定義から\(\textrm{Lng}(s)\)に関する数学的帰納法より即座に従う。\((s,c_1,b)\)が\(s c_1 b\)のscb分解であることはscb分解の定義より即座に従う。□

命題（scb分解の合成則）

任意の\(t \in T_{\textrm{B}}\)に対し、以下が成り立つ：

(1) 任意の\(c_0 \in PT_{\textrm{B}}\)と\(s_0,s_1,c_1,b_1,b_0 \in \Sigma^{< \omega}\)に対し、\((s_0,c_0,b_0)\)が\(t\)のscb分解でかつ\((s_1,c_1,b_1)\)が\(c_0\)のscb分解ならば、\((s_0 s_1,c_1,b_1 b_0)\)は\(t\)のscb分解である。

(2) 任意の\(v \in \mathbb{N}\)と\(s,c,b \in \Sigma^{< \omega}\)に対し、\((s,c,b)\)が\(t\)のscb分解であるならば\((D_v s,c,b)\)は\(D_v t\)のscb分解である。

証明：

scb分解の定義より即座に従う。□

\((s,c,b)\)が\(t\)のscb分解となるような\((s,b) \in (\Sigma^{< \omega})\)が存在する\((t,c) \in T_{\textrm{B}}^2\)全体のなす部分集合を\(T_{\textrm{B}}^{\textrm{Marked}} \subset T_{\textrm{B}}^2\)と置く。

命題（scb分解の自明性の判定条件）

任意の\((t,c) \in T_{\textrm{B}}^{\textrm{Marked}}\)に対し、以下が同値である：

(1) \(t = c\)である。

(2) 任意の\((s,b) \in (\Sigma^{< \omega})^2\)に対し、\((s,c,b)\)が\(t\)のscb分解であるならば\(s = ()\)かつ\(b = ()\)である。

(3) ある\(b \in \Sigma^{< \omega}\)が存在し、\(((),c,b)\)が\(t\)のscb分解である。

証明：

(1)が成り立つならば、\(\textrm{Lng}(s) + \textrm{Lng}(b) = (\textrm{Lng}(s) + \textrm{Lng}(c) + \textrm{Lng}(b)) - \textrm{Lng}(b) = \textrm{Lng}(t) - \textrm{Lng}(c) = 0\)より\(s = ()\)かつ\(b = ()\)となり、(2)が成り立つ。

(2)が成り立つならば、\((t,c) \in T_{\textrm{B}}^{\textrm{Marked}}\)より\((s,c,b)\)が\(t\)のscb分解となる\((s,b) \in (\Sigma^{< \omega})^2\)が存在し、(2)より\(s = ()\)かつ\(b = ()\)となるので\(t = scb = c\)であり、(1)と(3)が成り立つ。

(3)が成り立つならば、順序数項のカッコの個数が左右で等しいことと\(t = cb\)から\(b = ()\)となるので\(t = c\)であり、(1)が成り立つ。□

\(t \in T_{\textrm{B}}\)とする。

- \(t\)が第\(0\)種scb分解可能であるとは、\(t\)の第\(0\)種scb分解が存在するということである。

- \(t\)が第\(1\)種scb分解可能であるとは、\(t\)の第\(1\)種scb分解が存在するということである。

命題（scb分解の一意性）

任意の\(t \in T_{\textrm{B}}\)に対し、以下が成り立つ：

(1) 任意の\((s_0,s_1,c,b_0,b_1) \in (\Sigma^{< \omega})^5\)に対し、\((s_0,c,b_0)\)と\((s_1,c,b_1)\)が\(t\)のscb分解であるならば、\(s_0 = s_1\)かつ\(b_0 = b_1\)である。

(2) \(\textrm{dom}(t) = \mathbb{N}\)である必要十分条件は、\(t\)が第\(0\)種scb分解可能または第\(1\)種scb分解可能であることである。

(3) \(t\)は第\(0\)種scb分解可能でないかまたは\(t\)は第\(1\)種scb分解可能でない。

(4) \(t\)の第\(0\)種scb分解は一意である。

(5) \(t\)の第\(1\)種scb分解は一意である。

証明：

(1)は\(c\)が単項であり単項は\(\underline{)}\)以外の文字を含むことから即座に従う。

(2)は\(t\)が\(D_{\omega}\)を含まないことから\(\textrm{dom}\)の再帰的定義より即座に従う。

(4)を示す。

\((s_0,c_0,b_0)\)と\((s_1,c_1,b_1)\)が\(t\)の第\(0\)種scb分解であると仮定する。

\(j_1 := \textrm{Lng}(\textrm{Rightnodes}(t))-1\)と置く。仮定から\(t\)はscb分解可能であるため、\(t \neq 0\)であり\(j_1 \geq 0\)である。

\(u := \textrm{RightNodes}(t)_{j_1}\)と置く。\(\textrm{RightNodes}\)の再帰的定義から、\(t\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字は\(D_u 0\)である。

\(i \in \{0,1\}\)とする。\(j_{1,i} := \textrm{Lng}(\textrm{RightNodes}(c_i))-1\)と置く。scb分解の定義から、\(j_{1,i} \geq 1\)である。

\(u_i := \textrm{RightNodes}(c_i)_{j_{1,i}}\)と置く。\(\textrm{RightNodes}\)の再帰的定義から、\(c_i\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字は\(D_{u_i} 0\)である。

\(b_i\)は\(\underline{)}\)のみからなる文字列であるため、\(t\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字と\(c_i\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字は等しく、\(u = u_i\)である。従って\(u_0 = u_1\)である。

\(v_i := \textrm{RightNodes}(c_i)_0\)と置く。\(b_i\)は\(\underline{)}\)のみからなる文字列でありかつ\(c_i\)は\(t\)に含まれる項であるため、\(j_{1,i} \leq j_1\)かつ\(\textrm{RightNodes}(c_i) = (\textrm{RightNodes}(t)_j)_{j=j_1-j_{1,i}}^{j_1}\)である。従って\(v_i = \textrm{RightNodes}(t)_{j_1-j_{1,i}} < u\)かつ任意の\(j \in \mathbb{N}\)に対して\(j_1-j_{1,i} < j < j_1\)ならば\(\textrm{RightNodes}(t)_j \geq u\)である。以上より\(j_1-j_{1,0} = j_1-j_{1,1}\)かつ\(v_0 = v_1\)である。

\(j_0 := j_1 - j_{1,0}\)と置く。\(\textrm{RightNodes}(t)_{j_0} = v_0\)より、\(t\)は\(D_{v_0}\)を含む。\(t\)に出現する\(D_{v_0}\)のうちもっとも末尾に近いものより左側の文字列を\(s\)と置くと、\(c_i\)の先頭が\(D_{v_0}\)でかつ\(\textrm{RightNodes}(c_i) = (\textrm{RightNodes}(t)_j)_{j=j_0}^{j_1}\)であることから\(s = s_i\)である。従って\(s_0 = s_1\)である。

\(c_i\)が項であることから、\(c_i\)の末尾に\(1\)個以上の\(\underline{)}\)を結合した文字列は項でない。更に\(b_i\)が\(\underline{)}\)のみからなることから、\(t\)の先頭から\(s\)を除いた文字列の部分文字列であって項であるもののうち最大のものが\(c_i\)である。従って\(c_0 = c_1\)かつ\(b_0 = b_1\)である。

以上より\((s_0,c_0,b_0) = (s_1,c_1,b_1)\)である。

(5)を示す。

\((s_0,c_0,b_0)\)と\((s_1,c_1,b_1)\)が\(t\)の第\(1\)種scb分解であると仮定する。

\(j_1 := \textrm{Lng}(\textrm{Rightnodes}(t))-1\)と置く。仮定から\(t\)はscb分解可能であるため、\(t \neq 0\)であり\(j_1 \geq 0\)である。

\(u := \textrm{RightNodes}(t)_{j_1}\)と置く。\(\textrm{RightNodes}\)の再帰的定義から、\(t\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字は\(D_u 0\)である。

\(i \in \{0,1\}\)とする。\(j_{1,i} := \textrm{Lng}(\textrm{RightNodes}(c_i))-1\)と置く。scb分解の定義から、\(j_{1,i} \geq 1\)である。

\(u_i := \textrm{RightNodes}(c_i)_{j_{1,i}}\)と置く。\(\textrm{RightNodes}\)の再帰的定義から、\(c_i\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字は\(D_{u_i} 0\)である。

\(b_i\)は\(\underline{)}\)のみからなる文字列であるため、\(t\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字と\(c_i\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字は等しく、\(u = u_i\)である。従って\(u_0 = u_1\)である。

\(v_i := \textrm{RightNodes}(c_i)_0\)と置く。\(b_i\)は\(\underline{)}\)のみからなる文字列でありかつ\(c_i\)は\(t\)に含まれる項であるため、\(j_{1,i} \leq j_1\)かつ\(\textrm{RightNodes}(c_i) = (\textrm{RightNodes}(t)_j)_{j=j_1-j_{1,i}}^{j_1}\)である。従って\(v_i = \textrm{RightNodes}(t)_{j_1-j_{1,i}} < u\)かつ任意の\(j \in \mathbb{N}\)に対して\(j_1-j_{1,i} < j < j_1\)ならば\(\textrm{RightNodes}(t)_j \geq u\)である。以上より\(j_1-j_{1,0} = j_1-j_{1,1}\)かつ\(v_0 = v_1\)である。

\(j_0 := j_1 - j_{1,0}\)と置く。\(\textrm{RightNodes}(t)_{j_0} = v_0\)より、\(t\)は\(D_{v_0}\)を含む。\(t\)に出現する\(D_{v_0}\)のうちもっとも末尾に近いものより左側の文字列を\(s\)と置くと、\(c_i\)の先頭が\(D_{v_0}\)でかつ\(\textrm{RightNodes}(c_i) = (\textrm{RightNodes}(t)_j)_{j=j_0}^{j_1}\)であることから\(s = s_i\)である。従って\(s_0 = s_1\)である。

\(c_i\)が項であることから、\(c_i\)の末尾に\(1\)個以上の\(\underline{)}\)を結合した文字列は項でない。更に\(b_i\)が\(\underline{)}\)のみからなることから、\(t\)の先頭から\(s\)を除いた文字列の部分文字列であって項であるもののうち最大のものが\(c_i\)である。従って\(c_0 = c_1\)かつ\(b_0 = b_1\)である。

以上より\((s_0,c_0,b_0) = (s_1,c_1,b_1)\)である。

(3)を示す。

(4)の証明から、\(t\)の第\(0\)種scb\((s_0,c_0,b_0)\)が存在するならば\(t\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字は\(c_0\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字と一致し、\(D_0 0\)となる。

(5)の証明から、\(t\)の第\(1\)種scb\((s_1,c_1,b_1)\)が存在するならば\(t\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字は\(c_1\)から\(\underline{)}\)を除いた文字列の末尾\(2\)文字と一致し、それはある\(u \in \mathbb{N}\)を用いて\(D_u 0\)と表せる。一方で\(c_1\)の先頭は\(v < u\)を満たすある\(v \in \mathbb{N}\)を用いて\(D_v\)と表せるので、特に\(u > 0\)である。

以上より、\(t\)が第\(0\)種scb分解可能ならば\(t\)は第\(1\)種scb分解可能でない。□

系（加法とscb分解の関係）

任意の\(t \in T_{\textrm{B}}\)と\(c \in PT_{\textrm{B}}\)に対し、以下が成り立つ：

(1) \((t+c,c) \in T_{\textrm{B}}^{\textrm{Marked}}\)である。

(2) 任意の\((s,b) \in (\Sigma^{< \omega})^2\)と\(c' \in PT_{\textrm{B}}\)に対し、\((s,c,b)\)が\(t+c\)のscb分解であるならば\((s,c',b)\)は\(t+c'\)のscb分解でである。

(3) 任意の\(v \in \mathbb{N}\)と\(s_0,s_1,b_0,b_1 \in \Sigma^{< \omega}\)と\(c' \in PT_{\textrm{B}}\)に対し、\(s_1 D_v(t+c) b_1 \in T_{\textrm{B}}\)かつ\((s_0,c,b_0)\)が\(s_1 D_v(t+c) b_1\)のscb分解であるならば、\(s_1 D_v(t+c') b_1 \in T_{\textrm{B}}\)かつ\((s_0,c',b_0)\)は\(s_1 D_v(t+c') b_1\)のscb分解である。

証明：

(1),(2)を示す。

\(t = 0\)とする。

\(t+c = c\)より\(((),c,())\)が\(t+c\)のscb分解をなすので\((t+c,c) \in T_{\textrm{B}}^{\textrm{Marked}}\)である。scb分解の一意性より\(s = ()\)かつ\(b = ()\)であり、\((s,c',b) = ((),c',())\)は\(t+c' = c'\)のscb分解である。

\(t \in PT_{\textrm{B}}\)とする。

\(t+c = \underline{(} t \underline{,} c \underline{)}\)より\((\underline{(} t \underline{,},c,\underline{)})\)が\(t+c\)のscb分解をなすので\((t+c,c) \in T_{\textrm{B}}^{\textrm{Marked}}\)である。scb分解の一意性より\(s = \underline{(} t \underline{,}\)かつ\(b = \underline{)}\)であり、\((s,c',b) = (\underline{(} t \underline{,},c',\underline{)})\)は\(t+c' = \underline{(} t \underline{,} c' \underline{)}\)のscb分解である。

\(t \in MT_{\textrm{B}}\)とする。

\(s' \in \Sigma^{< \omega}\)を用いて\(t = \underline{(} s \underline{)}\)と置くと\(t+c = \underline{(} s' \underline{,} c \underline{)}\)より\((\underline{(} s' \underline{,},c,\underline{)})\)が\(t+c\)のscb分解をなすので\((t+c,c) \in T_{\textrm{B}}^{\textrm{Marked}}\)である。scb分解の一意性より\(s = \underline{(} s' \underline{,}\)かつ\(b = \underline{)}\)であり、\((s,c',b) = (\underline{(} s' \underline{,},c',\underline{)})\)は\(t+c' = \underline{(} s' \underline{,} c' \underline{)}\)のscb分解である。

(3)を示す。

\(t = 0\)とする。

\(s_1 D_v c b_1 = s_1 D_v(t+c) b_1 \in T_{\textrm{B}}\)よりscb分解の置換可能性から\(s_1 D_v(t+c') b_1 = s_1 D_v c' b_1 \in T_{\textrm{B}}\)である。

\(s_0 c b_0 = s_1 D_v(t+c) b_1 = s_1 D_v c b_1\)より、scb分解の一意性 (1)から\(s_0 = s_1 D_v\)かつ\(b_0 = b_1\)である。従って\(s_0 c' b_0 = s_1 D_v c' b_1 = s_1 D_v(t+c') b_1\)となるので\((s_0,c',b_0)\)は\(s_1 D_v(t+c') b_1\)のscb分解である。

\(t \in PT_{\textrm{B}}\)とする。

\(s_1 D_v \underline{(} t \underline{,} c \underline{)} b_1 = s_1 D_v(t+c) b_1 \in T_{\textrm{B}}\)よりscb分解の置換可能性から\(s_1 D_v(t+c') b_1 = s_1 D_v \underline{(} t \underline{,} c' \underline{)} b_1 \in T_{\textrm{B}}\)である。

\(s_0 c b_0 = s_1 D_v(t+c) b_1 = s_1 D_v \underline{(} t \underline{,} c \underline{)} b_1\)より、scb分解の一意性 (1)から\(s_0 = s_1 D_v \underline{(} t \underline{,}\)かつ\(b_0 = \underline{)} b_1\)である。従って\(s_0 c' b_0 = s_1 D_v \underline{(} t \underline{,} c' \underline{)} b_1 = s_1 D_v(t+c') b_1\)となるので\((s_0,c',b_0)\)は\(s_1 D_v(t+c') b_1\)のscb分解である。

\(t \in MT_{\textrm{B}}\)とする。

\(s' \in \Sigma^{< \omega}\)を用いて\(t = \underline{(} s' \underline{)}\)と置くと\(s_1 D_v \underline{(} s' \underline{,} c \underline{)} b_1 = s_1 D_v(t+c) b_1 \in T_{\textrm{B}}\)よりscb分解の置換可能性から\(s_1 D_v(t+c') b_1 = s_1 D_v \underline{(} s' \underline{,} c' \underline{)} b_1 \in T_{\textrm{B}}\)である。

\(s_0 c b_0 = s_1 D_v(t+c) b_1 = s_1 D_v \underline{(} s' \underline{,} c \underline{)} b_1\)より、scb分解の一意性 (1)から\(s_0 = s_1 D_v \underline{(} s' \underline{,}\)かつ\(b_0 = \underline{)} b_1\)である。従って\(s_0 c' b_0 = s_1 D_v \underline{(} s' \underline{,} c' \underline{)} b_1 = s_1 D_v(t+c') b_1\)となるので\((s_0,c',b_0)\)は\(s_1 D_v(t+c') b_1\)のscb分解である。□

命題（scb分解と基本列の関係）

任意の\(v,n \in \mathbb{N}\)に対し、以下が成り立つ：

(1) 任意の\(t'_0,t'_1 \in T_{\textrm{B}}\)に対し以下が成り立つ。

(1-1) \(t'_0 + D_v(t'_1 + D_0 0)[n] = t'_0 + (D_v t'_1) \times (n+1)\)である。

(1-2) 任意の\(t \in T_{\textrm{B}}\)と\(u \in \mathbb{N}\)と\((s,b) \in (\Sigma^{< \omega})^2\)に対し、\((s,D_u(t'_0 + D_v(t'_1+D_0 0)),b)\)が\(t\)のscb分解ならば、\((s,D_u(t'_0 + (D_v t'_1) \times (n+1)),b)\)は\(t[n]\)のscb分解である。

(2) 任意の\(t \in T_{\textrm{B}}\)と\(u \in \mathbb{N}\)と\((s_0,s_1,c_2,b_0,b_1) \in (\Sigma^{< \omega})^5\)に対し、\((s_1,c_2,b_1)\)が\(t\)の第\(1\)種scb分解でありかつ\((D_u s_0,D_v 0,b_0)\)が\(c_2\)のscb分解であるならば、\(v > u\)かつ\(t[n] = s_1 D_u (s_0 D_{v-1})^{n+1} 0 b_0^{n+1}b_1\)である。

証明：

Buchholzの表記系における基本列と共終数の再帰的定義から、\([n]\)を取る項の長さに関する数学的帰納法により即座に従う。□

命題（\(\textrm{RightNodes}\)と部分表現の関係）

任意の\(s,b \in \Sigma^{< \omega}\)と\(v \in \mathbb{N}\)\(t \in PT_{\textrm{B}}\)に対し、\(b\)が\(\underline{)}\)のみからなりかつ\(s D_v 0 b \in T_{\textrm{B}}\)ならば、\(s D_v t b \in T_{\textrm{B}}\)かつ\(\textrm{Lng}(P(s D_v t b)) = \textrm{Lng}(P(s D_v 0 b))\)であり一意な\(a_0, a_1 \in \mathbb{N}^{< \omega}\)が存在して以下を満たす：

(1) \(\textrm{RightNodes}(s D_v t b) = a_0 \oplus_{\mathbb{N}} (v) \oplus_{\mathbb{N}} a_1\)である。

(2) \(\textrm{RightNodes}(s D_v 0 b) = a_0 \oplus_{\mathbb{N}} (v)\)である。

(3) \(\textrm{RightNodes}(D_v t) = (v) \oplus_{\mathbb{N}} a_1\)である。

証明：

\(s D_v t b \in T_{\textrm{B}}\)であることはscb分解の置換可能性から従い、\(\textrm{Lng}(P(s D_v t b)) = \textrm{Lng}(P(s D_v 0 b))\)であることは\(P\)の再帰的定義から\(\textrm{Lng}(s)\)に関する数学的帰納法より即座に従う。

\(a_1 := \textrm{RightNodes}(t)\)と置く。

\(\textrm{RightNodes}\)の定義より、\(\textrm{RightNodes}(D_v t) = (v) \oplus_{\mathbb{N}} a_1\)である。

ある\(a_0 \in \mathbb{N}^{< \omega}\)が存在して\(\textrm{RightNodes}(s D_v t b) = a_0 \oplus_{\mathbb{N}} (v) \oplus_{\mathbb{N}} a_1\)かつ\(\textrm{RightNodes}(s D_v 0 b) = a_0 \oplus_{\mathbb{N}} (v)\)となることを\(\textrm{Lng}(s)\)に関する数学的帰納法で示す。

\(\textrm{Lng}(s) = 0\)ならば、\(b = 0\)となるので\(a_0 = ()\)とすれば良い。

\(\textrm{Lng}(s) > 0\)とする。

\(s D_v 0 b \in PT_{\textrm{B}}\)とする。

\(u \in \mathbb{N}\)と\(s' \in \Sigma^{< \omega}\)を用いて\(s = D_u s'\)と置く。

\(T_{\textrm{B}}\)の再帰的定義から\(s' D_v 0 b \in T_{\textrm{B}}\)である。従って\(s' D_v t b \in T_{\textrm{B}}\)である。

\(\textrm{Lng}(s') = \textrm{Lng}(s)-1 < \textrm{Lng}(s)\)であるので、帰納法の仮定からある\(a'_0 \in \mathbb{N}^{< \omega}\)が存在して\(\textrm{RightNodes}(s' D_v t b) = a'_0 \oplus_{\mathbb{N}} (v) \oplus_{\mathbb{N}} a_1\)かつ\(\textrm{RightNodes}(s' D_v 0 b) = a'_0 \oplus_{\mathbb{N}} (v)\)となる。

\(a_0 := (u) \oplus_{\mathbb{N}} a'_0\)と置くと、\(T_{\textrm{B}}\)の再帰的定義から\(\textrm{RightNodes}(s D_v t b) = (u) \oplus_{\mathbb{N}} \textrm{RightNodes}(s' D_v t b) = (u) \oplus_{\mathbb{N}} a'_0 \oplus_{\mathbb{N}} (v) \oplus_{\mathbb{N}} a_1 = a_0 \oplus_{\mathbb{N}} (v) \oplus_{\mathbb{N}} a_1\)かつ\(\textrm{RightNodes}(s D_v 0 b) = (u) \oplus_{\mathbb{N}} \textrm{RightNodes}(s' D_v 0 b) = (u) \oplus_{\mathbb{N}} a'_0 \oplus_{\mathbb{N}} (v) = a_0 \oplus_{\mathbb{N}} (v)\)である。

\(s D_v 0 b \in MT_{\textrm{B}}\)とする。

\(J_1 := \textrm{Lng}(P(s D_v 0 b))\)と置く。

\(\Sigma_{\textrm{B}}\)の定義から、\(\underline{)}\)のみからなるある\(b'_1 \in \Sigma^{< \omega}\)が存在して\(\underline{,} P(s D_v 0 b)_{J_1} b'_1\)が\(s D_v 0 b\)の末尾に現れる。\(\underline{)}\)のみからなる\(b'_0 \in \Sigma^{< \omega}\)を用いて\(b = b'_0 b'_1\)と置く。

\(s D_v 0 b\)の末尾に\(D_v 0 b = D_v 0 b'_0 b'_1\)が現れ、\(P(s D_v 0 b)_{J_1}\)の末尾に\(b'_0\)が現れ、そして\(P(s D_v 0 b)_{J_1}\)は単項であるので\(0\)でも\(\underline{)}\)でもない文字を含むため、\(P(s D_v 0 b)_{J_1}\)の末尾に\(D_v 0 b'_0\)が現れる。\(s'_0 \in \Sigma^{< \omega}\)を用いて\(P(s D_v 0 b)_{J_1} = s'_0 D_v 0 b'_0\)と置く。

\(s D_v 0 b\)の末尾に\(\underline{,} P(s D_v 0 b)_{J_1} b'_1 = \underline{,} s'_0 D_v 0 b'_0 b'_1 = \underline{,} s'_0 D_v 0 b\)が現れることから、\(s\)の末尾に\(\underline{,} s'_0\)が現れる。\(s'_1 \in \Sigma^{< \omega}\)を用いて\(s = s'_1 \underline{,} s'_0\)と置く。

\(s'_0 D_v 0 b'_0 = P(s D_v b)_{J_1} \in T_{\textrm{B}}\)より\(s'_0 D_v t b'_0 \in T_{\textrm{B}}\)であり、\(s D_v 0 b = s'_1 \underline{,} s'_0 D_v 0 b'_0 b'_1 = s'_1 \underline{,} P(s D_v b)_{J_1} b'_1\)である。\(s D_v 0 b\)の末尾\(P(s D_v 0 b)_{J_1} b'_1\)を\(P(s D_v t b)_{J_1} b'_1\)に置き換えたものは\(s D_v t b\)であり、かつ\(s D_v 0 b\)の末尾\(P(s D_v 0 b)_{J_1} b'_1 = s'_0 D_v 0 b'_0 b'_1\)を\(s'_0 D_v t b'_1\)に置き換えたものも\(s D_v t b\)であるので、\(P(s D_v t b)_{J_1} = s'_0 D_v t b'_0\)である。

\(\textrm{Lng}(s') = \textrm{s} - \textrm{Lng}(s'_1) + 1 < \textrm{Lng}(s)\)であるので、帰納法の仮定からある\(a_0 \in \mathbb{N}^{< \omega}\)が存在して\(\textrm{RightNodes}(s'_0 D_v t b'_0) = a_0 \oplus_{\mathbb{N}} (v) \oplus_{\mathbb{N}} a_1\)かつ\(\textrm{RightNodes}(s'_0 D_v 0 b'_0) = a_0 \oplus_{\mathbb{N}} (v)\)となる。

\(\textrm{RightNodes}\)の再帰的定義から\(\textrm{RightNodes}(s D_v t b) = \textrm{RightNodes}(P(s D_v t b)_{J_1}) = \textrm{RightNodes}(s'_0 D_v t b'_0) = a_0 \oplus_{\mathbb{N}} (v) \oplus_{\mathbb{N}} a_1\)であり、\(\textrm{RightNodes}(s D_v 0 b) = \textrm{RightNodes}(P(s D_v 0 b)_{J_1}) = \textrm{RightNodes}(s'_0 D_v 0 b'_0) = a_0 \oplus_{\mathbb{N}} (v)\)である。□

## 翻訳写像[]

\((\textrm{Trans}(M),\textrm{Mark}(M,m)) \in T_{\textrm{B}}^{\textrm{Marked}}\)を満たす写像
\begin{eqnarray*}
\textrm{Trans} \colon T_{\textrm{PS}} & \to & T_{\textrm{B}} \\
M & \mapsto & \textrm{Trans}(M)
\end{eqnarray*}
と
\begin{eqnarray*}
\textrm{Mark} \colon T_{\textrm{PS}}^{\textrm{Marked}} & \to & T_{\textrm{B}} \\
(M,m) & \mapsto & \textrm{Mark}(M,m)
\end{eqnarray*}
を以下のように再帰的に定める：

- \(j_1 := \textrm{Lng}(M) - 1\)と置く。

- \(M \in RT_{\textrm{PS}}\)かつ\(j_1 = 0\)とする。

- \(M_0 = (0,0)\)とする。

- \(\textrm{Trans}(M) := 0\)である。

- \(\textrm{Mark}(M,m) := 0\)である。

- \(M_0 \neq (0,0)\)とする。

- \(\textrm{Trans}(M) := D_{M_{1,0}} 0\)である。

- \(\textrm{Mark}(M,m) := D_{M_{1,0}} 0\)である。

- \(M\)が簡約かつ単項かつ\(j_1 > 0\)とする。

- \(t_1 := \textrm{Trans}(\textrm{Pred}(M))\)と置く。

- \(t_1 = 0\)とする[34]。

- \(\textrm{Trans}(M) := D_0 D_{M_{1,j_1}} 0\)である。

- \(m = 0\)ならば\(\textrm{Mark}(M,m) := D_0 D_{M_{1,j_1}} 0\)である。

- \(m > 0\)ならば\(\textrm{Mark}(M,m) := D_{M_{1,j_1}} 0\)である。

- \(t_1 \neq 0\)とする。

- \(i_1 := \max \{i \in \{0,1\} \mid M_{i,j_1} > 0\}\)と置く[35]。

- \(j_0 := \max \{j \in \mathbb{N} \mid j < j_1 \wedge (0,j) \leq_M (0,j_1)\}\)と置く[36]。

- \(j_{-1} := \textrm{Adm}_M(j_0)\)と置く。

- 互いに背反な条件(I)～(VI)を以下のように定める：

- 条件(I)は「\(M_{1,j_1} = 0\)かつ\(j_0\)は\(M\)許容」である。

- 条件(II)は「\(M_{1,j_1} = 0\)かつ\(j_0\)は非\(M\)許容」である。

- 条件(III)は「\(M_{1,j_1} > 0\)かつ\(M_{1,j_0} \geq M_{1,j_1}\)かつ\(j_0\)は\(M\)許容」である。

- 条件(IV)は「\(M_{1,j_1} > 0\)かつ\(M_{1,j_0} \geq M_{1,j_1}\)かつ\(j_0\)は非\(M\)許容」である。

- 条件(V)は「\(M_{1,j_1} > 0\)かつ\(M_{1,j_0}+1 = M_{1,j_1}\)かつ\(j_0+1 < j_1\)」である。

- 条件(VI)は「\(M_{1,j_1} > 0\)かつ\(M_{1,j_0}+1 = M_{1,j_1}\)かつ\(j_0+1 = j_1\)」である。

- \(c_1 := \textrm{Mark}(\textrm{Pred}(M),j_{-1})\)と置く[37]。

- \((t_1,c_1) \in T_{\textrm{B}}^\textrm{Marked}\)かつ\(t_1 \neq 0\)より、\(c_1 \in PT_{\textrm{B}}\)でありscb分解の一意性 (1)より一意な\((s_1,b_1) \in (\Sigma^{< \omega})^2\)が存在して\((s_1,c_1,b_1)\)は\(t_1\)のscb分解をなす。

- \(v \in \mathbb{N}\)と\(t_2 \in T_{\textrm{B}}\)を用いて\(c_1 = D_v t_2\)と置く。

- \(J_1 := \textrm{Lng}(P(t_2))-1\)と置く。

- 条件(I)か(III)か(V)を満たすならば\(c_2 := D_v(t_2 + D_{M_{1,j_1}} 0)\)と置く。

- 条件(II)か(IV)を満たすとする。

- \(t_2 = 0\)ならば[38]、\(c_2 := D_v D_{M_{1,j_0}} D_{M_{1,j_1}} 0\)と置く。

- \(t_2 \neq 0\)とする。

- \(P(t_2)_{J_1}\)の左端が\(D_{M_{1,j_0}}\)であるとする。

- \(t_3 := \Sigma_{\textrm{B}} (P(t_2)_J)_{J=0}^{J_1-1}\)と置く。

- \(t_4 \in T_{\textrm{PS}}\)を用いて\(P(t_2)_{J_1} = D_{M_{1,j_0}} t_4\)と置く。

- \(P(t_2)_{J_1}\)の左端が\(D_{M_{1,j_0}}\)でないとする。

- \(t_3 := t_2\)と置く。

- \(t_4 := t_2\)と置く。

- \(c_2 := D_v (t_3 + D_{M_{1,j_0}}(t_4 + D_{M_{1,j_1}} 0))\)と置く。

- 条件(VI)を満たすならば\(c_2 := D_v D_{M_{1,j_1}} 0\)と置く。

- \(\textrm{Trans}(M) := s_1 c_2 b_1\)である[39]。

- \(m < j_1\)とする。

- \(c_0 := \textrm{Mark}(\textrm{Pred}(M),m)\)と置く[40]。

- \((c_0,c_1) \in T_{\textrm{B}}^{\textrm{Marked}}\)とする。

- \((t_1,c_0) \in T_{\textrm{B}}^{\textrm{Marked}}\)より、scb分解の一意性 (1)から一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在して\((s_0,c_0,b_0)\)は\(t_1\)のscb分解である。

- \((c_0,c_1) \in T_{\textrm{B}}^\textrm{Marked}\)より、scb分解の一意性 (1)から一意な\((s_{-1},b_{-1}) \in (\Sigma^{< \omega})^2\)が存在して\((s_{-1},c_1,b_{-1})\)は\(c_0\)のscb分解である[41]。

- \(\textrm{Mark}(M,m) := s_{-1} c_2 b_{-1}\)である[42]。

- \((c_0,c_1) \in T_{\textrm{B}}^{\textrm{Marked}}\)でないならば[43]、\(\textrm{Mark}(M,m) := D_{M_{1,j_1}} 0\)である[44]。

- \(m = j_1\)ならば\(\textrm{Mark}(M,m) := D_{M_{1,j_1}} 0\)である[45]。

- \(M\)が簡約かつ複項とする。

- \(J_1 := \textrm{Lng}(P(M))-1\)と置く。

- \(j_0 := j_1 - \textrm{Lng}(P(M)_{J_1}) + 1\)と置く。

- \(P(M)_{J_1} = ((0,0))\)とする。

- \(\textrm{Trans}(M) := \textrm{Trans}((M_j)_{j=0}^{j_0-1}) + D_0 0\)である。

- \(\textrm{Mark}(M,m) := D_0 0\)である。

- \(P(M)_{J_1} \neq ((0,0))\)とする。

- \(\textrm{Trans}(M) := \textrm{Trans}((M_j)_{j=0}^{j_0-1}) + \textrm{Trans}(P(M)_{J_1})\)である。

- \(\textrm{Mark}(M,m) := \textrm{Mark}(P(M)_{J_1},m-j_0)\)である[46]。

- \(M\)が簡約でないとする。

- \(\textrm{Trans}(M) :=　\textrm{Trans}(\textrm{Red}(M))\)である。

- \(\textrm{Mark}(M,m) := \textrm{Mark}(\textrm{Red}(M),m)\)である[47]。

命題（\(\textrm{Trans}\)のwell-defined性）

上の条件を全て満たす写像\(\textrm{Trans}\)と\(\textrm{Mark}\)が一意に存在する。

証明：

\(\textrm{Lng}(M)\)に関する数学的帰納法より即座に従う。□

命題（\(2\)列ペア数列の基本性質）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)に対し、\(\textrm{Lng}(M) = 2\)ならば以下が成り立つ：

(1) \(\textrm{Trans}(M) = D_{M_{1,0}} D_{M_{1,1}} 0\)である。

(2) \((M,0),(M,1) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。

(3) \(\textrm{Mark}(M,0) = D_{M_{1,0}} D_{M_{1,1}} 0\)かつ\(\textrm{Mark}(M,1) = D_{M_{1,1}} 0\)である。

証明：

\(m \in \{0,1\}\)とし、\(\textrm{Trans}\)と\(\textrm{Mark}\)の再帰的定義中に導入した記号を用いる。

\(M\)の簡約性と簡約性と係数の関係から\(M\)は条件(A)と(B)を満たす。

\(j_1 = 1\)であり、\(M\)は単項より\((0,0) <_M^{\textrm{Next}} (0,1) = (0,j_1)\)なので\(j_0 = 0\)である。特に\(j_0\)は\(M\)許容であり、\(j_{-1} = j_0 = 0\)である。

\(m=0\)ならば、\(M\)は単項なので\((0,m) = (0,0) <_M^{\textrm{Next}} (0,1) = (0,j_1)\)となり、\(m = 0\)は\(M\)許容であるので\((M,m) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。

\(m=1\)ならば、\((0,m) = (0,1) \leq_M^{\textrm{Next}} (0,1) = (0,j_1)\)となり、\(m = 1 = j_1\)は\(M\)許容であるので\((M,m) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。

\(D_v t_2 = c_1 = \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = \textrm{Mark}(((M_{1,0},M_{1,0})),0) = D_{M_{1,0}} 0\)より\(v = M_{1,0}\)かつ\(t_2 = 0\)である。

\(j_0\)の\(M\)許容性と\(j_0+1 = 1 = j_1\)から\(M\)は条件(I)か(III)か(VI)を満たす。

条件(I)か(III)を満たすならば\(c_2 = D_v(t_2 + D_{M_{1,j_1}} 0) = D_{M_{1,0}}(0 + D_{M_{1,j_1}}) 0 = D_{M_{1,0}} D_{M_{1,1}} 0\)である。

条件(VI)を満たすならば\(c_2 = D_v D_{M_{1,j_1}} 0 = D_{M_{1,0}} D_{M_{1,j_1}} 0\)である。

従っていずれの場合も\(c_2 = D_{M_{1,m}} D_{M_{1,j_1}} 0\)である。

\(m=0\)ならば、\(m = j_{-1}\)より\(s_{-1} c_1 b_{-1} = c_0 = \textrm{Mark}(\textrm{Pred}(M),m) = \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = c_1\)となるので\(s_{-1} = ()\)かつ\(b_{-1} = ()\)であり、\(\textrm{Mark}(M,m) = s_{-1} c_2 b_{-1} = D_{M_{1,m}} D_{M_{1,j_1}} 0\)である。

\(m=1\)ならば、\(m = j_1\)より\(\textrm{Mark}(M,m) = D_{M_{1,j_1}} 0\)である。

\(M_{1,0} = 0\)ならば、\(t_1 = \textrm{Trans}(\textrm{Pred}(M)) = \textrm{Trans}((M_{1,0},M_{1,0})) = 0\)であるので、\(\textrm{Trans}(M) = D_0 D_{M_{1,1}} 0 = D_{M_{1,0}} D_{M_{1,1}} 0\)である。

\(M_{1,0} > 0\)ならば、\(t_1 = \textrm{Trans}(\textrm{Pred}(N)) = \textrm{Trans}((M_{1,0},M_{1,0})) = D_{M_{1,0}} 0 \neq 0\)であり、\(s_1 D_{M_{1,0}} 0 b_1 = s_1 c_1 b_1 = t_1 = D_{M_{1,m}} 0\)より\(s_1 = ()\)かつ\(b_1 = ()\)であるので、\(\textrm{Trans}(M) = s_1 c_2 b_1 = D_{M_{1,0}} D_{M_{1,j_1}} 0\)である。□

命題（\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性）

任意の\(M \in T_{\textrm{PS}}\)に対し以下が成り立つ：

(1) \(\textrm{Trans}(M) = \textrm{Trans}(\textrm{Red}(M)) = \textrm{Trans}(\textrm{IncrFirst}(M))\)である。

(2) \(M\)が複項とする。\(J_1 := \textrm{Lng}(P(M))\)と置く。\(J \leq J_1\)を満たす各\(J \in \mathbb{N}\)に対し、\(P(M)_J\)が零項ならば\(t_J : = D_0 0\)と置き\(P(M)_J\)が零項でないならば\(t_J := \textrm{Trans}(P(M)_J)\)と置く。この時\(\textrm{Trans}(M) = \Sigma_{\textrm{B}} (t_J)_{J=0}^{J_1}\)である。

証明：

\(\textrm{Red}\)の冪等性と\(\textrm{Trans}\)と\(\textrm{Red}\)の再帰的定義より即座に従う。□

命題（\(\textrm{Mark}\)の\((\textrm{IncrFirst},\textrm{Red},P)\)不変性）

任意の\((M,m) \in T_{\textrm{PS}}^{\textrm{Marked}}\)に対し以下が成り立つ：

(1) \(\textrm{Mark}(M,m) = \textrm{Mark}(\textrm{Red}(M),m) = \textrm{Mark}(\textrm{IncrFirst}(M),m)\)である。

(2) \(M\)が複項とする。\(J_1 := \textrm{Lng}(P(M))\)と置き、\(j_0 := \textrm{Lng}(M) - \textrm{Lng}(P(M)_{J_1}) - 1\)と置く。\(P(M)_{J_1}\)が零項ならば\(\textrm{Mark}(M,m) = D_0 0\)であり、\(P(M)_{J_1}\)が零項でないならば\(\textrm{Mark}(M,m) = \textrm{Mark}(P(M)_{J_1},m-j_0)\)である。

証明：

\(\textrm{Red}\)の冪等性と\(\textrm{Mark}\)と\(\textrm{Red}\)の再帰的定義より即座に従う。□

命題（\(\textrm{Trans}\)が零項性を保つこと）

任意の\(M \in T_{\textrm{PS}}\)に対し、以下は同値である：

(1) \(M\)は零項である。

(2) \(\textrm{Trans}(M) = 0\)である。

証明：

\(\textrm{Red}\)が零項性を保つことと\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性より\(M\)が簡約の場合に帰着される。

\(M\)が簡約ならば、\(\textrm{Trans}\)の再帰的定義から、\(\textrm{Lng}(M)\)に関する数学的帰納法より即座に従う。□

命題（\(c_1\)と\(c_2\)の大小関係）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用いると、\(j_1 > 0\)かつ\(t_1 \neq 0\)ならば、\(c_1\)と\(c_2\)は単項でありかつ\(c_1 < c_2\)である。

証明：

\(c_1\)と\(c_2\)の定義より即座に従う。□

命題（\(\textrm{Pred}\)の\(\textrm{Trans}\)に関する降下性）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\textrm{Lng}(M) > 1\)ならば\(\textrm{Trans}(\textrm{Pred}(M)) < \textrm{Trans}(M)\)である。

証明：

\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と\(\textrm{Red}\)と\(\textrm{Pred}\)の可換性から、\(M \in RT_{\textrm{PS}} \setminus \textrm{ZT}_{\textrm{PS}}\)の場合に帰着される。

\(J_1 := \textrm{Lng}(J_1)\)とする。

\(\textrm{Lng}(P(M)_{J_1}) = 1\)ならば、\(\textrm{Trans}\)の再帰的定義より\(0 < D_0 0\)と部分表現の不等式の延長性から従う。

\(\textrm{Lng}(P(M)_{J_1}) > 1\)とする。

\(P\)が簡約性を保つことから\(P(M)_{J_1} \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)である。\(\textrm{Trans}\)の定義と\(c_1\)と\(c_2\)の大小関係より、部分表現の不等式の延長性から\(\textrm{Trans}(\textrm{Pred}(P(M)_{J_1})) < \textrm{Trans}(P(M)_{J_1})\)である。

\(\textrm{Lng}(P(M)_{J_1}) > 1\)より\(P(\textrm{Pred}(M)) = (P(M)_J)_{J=0}^{J_1-1} \oplus_{T_{\textrm{PS}}} \textrm{Pred}(P(M)_{J_1})\)であるので、\(\textrm{Trans}\)の定義より部分表現の不等式の延長性から\(\textrm{Trans}(\textrm{Pred}(M)) < \textrm{Trans}(M)\)である。□

命題（右端第\(1\)基点のMarkの基本性質）

任意の\((M,m) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)に対し、\(j_1 := \textrm{Lng}(M) - 1\)と置くと以下は同値である：

(1) \(m = j_1\)である。

(2) \(\textrm{Mark}(M,m) = D_{M_{1,m}} 0\)である。

<<<MISSING line 2302 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2303 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2304 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2305 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2306 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2307 — recover from original.html via tools/make_content.py>>>
\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)ならば、\(\textrm{Lng}(c_2) > 2\)から\(\textrm{Mark}\)の定義より即座に従う。□
<<<MISSING line 2309 — recover from original.html via tools/make_content.py>>>
系（\(\textrm{Mark}\)の左端の基本性質）
<<<MISSING line 2311 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2312 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2313 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2314 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2315 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2316 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2317 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2318 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2319 — recover from original.html via tools/make_content.py>>>
系（条件(II)か(IV)の下で\(t_2\)が\(0\)でないこと）
<<<MISSING line 2321 — recover from original.html via tools/make_content.py>>>
任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用いると、\(t_1 \neq 0\)かつ\(M\)が条件(II)か(IV)を満たすならば、\(t_2 \neq 0\)である。
<<<MISSING line 2323 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2324 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2325 — recover from original.html via tools/make_content.py>>>
\(M\)が条件(II)を満たすならば、\((1,j_0) <_M^{\textrm{Next}} (1,j_0+1)\)より\(M_{1,j_0+1} > 0\)であるので、\(i_1 = 0\)より\(j_0+1 < j_1\)である。
<<<MISSING line 2327 — recover from original.html via tools/make_content.py>>>
\(M\)が条件(IV)を満たすならば、\((1,j_0) \leq_M (1,j_1)\)でないので\(j_0\)の非\(M\)許容性から\(j_0+1 < j_1\)である。
<<<MISSING line 2329 — recover from original.html via tools/make_content.py>>>
従っていずれの場合も\(j_{-1} \leq j_0 < j_1-1\)であり、右端第\(1\)基点のMarkの基本性質より\(D_v t_2 = c_1 \neq D_{M_{1,j_{-1}}} 0\)である。また\(\textrm{Mark}\)の左端の基本性質より\(v = M_{1,j_{-1}}\)であるので、\(t_2 \neq 0\)となる。□
<<<MISSING line 2331 — recover from original.html via tools/make_content.py>>>
命題（右端第\(2\)基点のMarkの基本性質）
<<<MISSING line 2333 — recover from original.html via tools/make_content.py>>>
\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)とし、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用いると、\(j_1 > 0\)かつ\(t_1 \neq 0\)ならば、\(\textrm{Mark}(M,j_{-1}) = c_2\)である。
<<<MISSING line 2335 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2336 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2337 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2338 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2339 — recover from original.html via tools/make_content.py>>>
\(s_{-1} c_0 b_{-1} = c_1 = \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = \textrm{Mark}(\textrm{Pred}(M),m) = c_0\)より\(s_{-1} = ()\)かつ\(b_{-1} = ()\)である。従って\(\textrm{Mark}(M,j_{-1}) = \textrm{Mark}(M,m) = s_{-1} c_2 b_{-1} = c_2\)である。□
<<<MISSING line 2341 — recover from original.html via tools/make_content.py>>>
命題（\(\textrm{Trans}\)の最左単項成分の左端の基本性質）
<<<MISSING line 2343 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2344 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2345 — recover from original.html via tools/make_content.py>>>
(1) \(P(M)_0 = ((0,0))\)かつ\(\textrm{Lng}(P(M)) > 1\)ならば\(\textrm{Trans}(M)\)の最左単項成分の左端は\(D_{M_{1,1}}\)である。
<<<MISSING line 2347 — recover from original.html via tools/make_content.py>>>
(2) \(P(M)_0 \neq ((0,0))\)ならば\(\textrm{Trans}(M)\)の最左単項成分は\(\textrm{Trans}(P(M)_0)\)でありその左端は\(D_{M_{1,0}}\)である。
<<<MISSING line 2349 — recover from original.html via tools/make_content.py>>>
(3) \((1,0) <_M^{\textrm{Next}} (1,1)\)ならば\(\textrm{Trans}(M)\)の最左単項成分の左端\(2\)文字はある\(u \in \mathbb{N}\)を用いて\(D_{M_{1,0}} D_u\)と表せる。
<<<MISSING line 2351 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2352 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2353 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2354 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2355 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2356 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2357 — recover from original.html via tools/make_content.py>>>
命題（\(\textrm{Trans}\)が単項性を保つこと）

任意の\(M \in T_{\textrm{PS}}\)に対し、以下は同値である：

(1) \(M\)は単項である。

(2) \(\textrm{Trans}(M)\)は単項であるか、\(P(M)_0\)が零項でありかつ\(\textrm{Lng}(P(M)) = 2\)である。

証明：

\(\textrm{Red}\)が単項性を保つことと\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と\(\textrm{Trans}\)の最左単項成分の左端の基本性質より\(M\)が簡約の場合に帰着される。

\(M\)が簡約ならば、\(\textrm{Trans}\)の再帰的定義から、\(\textrm{Lng}(M)\)に関する数学的帰納法より即座に従う。□

系（\(\textrm{Trans}\)と非可算基数の関係）

任意の\(M \in RT_{\textrm{PS}}\)と\(v \in \mathbb{N}\)に対し、以下は同値である：

(1) \(\textrm{Trans}(M) = D_v 0\)である。

<<<MISSING line 2378 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2379 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2380 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2381 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2382 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2383 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2384 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2385 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2386 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2387 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2388 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2389 — recover from original.html via tools/make_content.py>>>
\(M_{1,0} > 0\)と仮定すると、\(\textrm{Trans}\)の最左単項成分の左端の基本性質 (2)から\(\textrm{Trans}(M)\)の最左単項成分の左端は\(D_{M_{1,0}} \neq D_0 = D_v\)となり矛盾する。従って\(M_{1,0} = 0\)である。
<<<MISSING line 2391 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2392 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2393 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2394 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2395 — recover from original.html via tools/make_content.py>>>
\(\textrm{Lng}(M') = 2\)より\(M'\)は零項でない。\(M'\)が単項ならば、\(2\)列ペア数列の基本性質と\(\textrm{Pred}\)の\(\textrm{Trans}\)に関する降下性から\(D_0 0 = D_v 0 = \textrm{Trans}(M) \geq \textrm{Trans}(M') = D_0 D_{M_{1,1}} 0 > D_0 0\)となり矛盾する。従って\(M'\)は複項であり、\(M_{0,1} \leq M_{0,0} = 0\)すなわち\(M_{0,1} = 0\)となる。
<<<MISSING line 2397 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2398 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2399 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2400 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2401 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2402 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2403 — recover from original.html via tools/make_content.py>>>
\(P(M)_0\)が零項であると仮定すると、\(M_0 = (0,0)\)であり\(P\)の定義より\(M_{0,1} = 0\)となり、\(M\)が条件(B)を満たすことから\(M_{1,1} = M_{0,1} = 0\)となるが、\(\textrm{Trans}\)の最左単項成分の左端の基本性質より\(D_v 0 = \textrm{Trans}(M)\)の唯一の単項成分\(D_v 0\)の左端が\(D_{M_{1,1}} = D_0 \neq D_v\)となり矛盾する。従って\(P(M)_0\)は零項でない。
<<<MISSING line 2405 — recover from original.html via tools/make_content.py>>>
\(P(M)_0\)が零項でないことと\(\textrm{Trans}\)が単項性を保つことから\(M\)は単項であり、\(\textrm{Trans}\)の最左単項成分の左端の基本性質から\(\textrm{Trans}(M)\)の左端は\(D_{M_{1,0}}\)となるので、\(M_{1,0} = v > 0\)である。
<<<MISSING line 2407 — recover from original.html via tools/make_content.py>>>
\(\textrm{Trans}((M_0)) = D_{M_{1,0}} 0 = D_v 0 = \textrm{Trans}(M)\)となるので、\(\textrm{Pred}\)の\(\textrm{Trans}\)に関する降下性より\(M = (M_0) = ((M_{1,0},M_{1,0})) = ((v,v))\)である。□
<<<MISSING line 2409 — recover from original.html via tools/make_content.py>>>
系（左端第\(1\)基点のMarkの基本性質）
<<<MISSING line 2411 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2412 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2413 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2414 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2415 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2416 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2417 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2418 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2419 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2420 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2421 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2422 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2423 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2424 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2425 — recover from original.html via tools/make_content.py>>>
\(2\)列ペア数列の基本性質より\((M,0) \in T_{\textrm{PS}}^{\textrm{Marked}}\)かつ\(\textrm{Mark}(M,0) = D_{M_{1,0}} D_{M_{1,1}} 0 = \textrm{Trans}(M)\)である。
<<<MISSING line 2427 — recover from original.html via tools/make_content.py>>>
\(m \neq 0\)ならば\(m = 1\)であり、\(2\)列ペア数列の基本性質より\(\textrm{Mark}(M,m) = D_{M_{1,m}} 0 = D_{M_{1,1}} 0 \neq D_{M_{1,0}} D_{M_{1,1}} 0 = \textrm{Trans}(M)\)である。
<<<MISSING line 2429 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2430 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2431 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2432 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2433 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2434 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2435 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2436 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2437 — recover from original.html via tools/make_content.py>>>
\(\textrm{Lng}(\textrm{Pred}(M)) = j_1 > 1\)より\(\textrm{Pred}(M)\)は零項でなく、\(\textrm{Trans}\)が零項性を保つことより\(t_1 \neq 0\)である。
<<<MISSING line 2439 — recover from original.html via tools/make_content.py>>>
簡約性の切片への遺伝性と単項性の始切片への遺伝性から\(\textrm{Pred}(M)\)は簡約かつ単項であり、帰納法の仮定から\((\textrm{Pred}(M),0) \in T_{\textrm{PS}}^{\textrm{Marked}}\)かつ、\(c_0 = \textrm{Mark}(\textrm{Pred}(M),m)\)が\(t_1 = \textrm{Trans}(\textrm{Pred}(M))\)と一致する必要十分条件は\(m = 0\)である。
<<<MISSING line 2441 — recover from original.html via tools/make_content.py>>>
\(m = 0\)ならば\(s_0 c_0 b_0 = t_1 = c_0\)より\(s_0 = ()\)かつ\(b_0 = ()\)であり、\(s_1 = s_0 s_{-1} = s_{-1}\)かつ\(b_1 = b_{-1} b_0 = b_{-1}\)となるので\(\textrm{Mark}(M,0) = \textrm{Mark}(M,m) = s_{-1} c_2 b_{-1} = s_1 c_2 b_1 = \textrm{Trans}(M)\)である。
<<<MISSING line 2443 — recover from original.html via tools/make_content.py>>>
\(m \neq 0\)ならば\(s_0 c_0 b_0 = t_1 \neq c_0\)より\(s_0 \neq ()\)または\(b_0 \neq ()\)であり、\(\textrm{Mark}(M,m) = s_{-1} c_2 b_{-1} \neq s_0 s_{-1} c_2 b_{-1} b_0 = s_1 c_2 b_1 = \textrm{Trans}(M)\)である。□
<<<MISSING line 2445 — recover from original.html via tools/make_content.py>>>
系（\(s_1\)と\(b_1\)の空性と基点の関係）
<<<MISSING line 2447 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2448 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2449 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2450 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2451 — recover from original.html via tools/make_content.py>>>
(2) \(s_1 = ()\)かつ\(c_1 = t_1\)かつ\(b_1 = ()\)である。
<<<MISSING line 2453 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2454 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2455 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2456 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2457 — recover from original.html via tools/make_content.py>>>
(1)が成り立つならば、左端第\(1\)基点のMarkの基本性質 (2)より\(c_1 = \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = \textrm{Trans}(\textrm{Pred}(M)) = t_1\)となり、scb分解の自明性の判定条件より\(s_1 = ()\)かつ\(b_1 = ()\)となり、従って\(c_1 = s_1 c_1 b_1 = t_1\)である。
<<<MISSING line 2459 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2460 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2461 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2462 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2463 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2464 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2465 — recover from original.html via tools/make_content.py>>>
命題（\(\textrm{Mark}\)が順序関係を保つこと）
<<<MISSING line 2467 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2468 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2469 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2470 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2471 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2472 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2473 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2474 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2475 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2476 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2477 — recover from original.html via tools/make_content.py>>>
系（\(s_{-1}\)と\(b_{-1}\)の空性と基点の関係）
<<<MISSING line 2479 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2480 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2481 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2482 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2483 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2484 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2485 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2486 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2487 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2488 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2489 — recover from original.html via tools/make_content.py>>>
命題（\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示）
<<<MISSING line 2491 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2492 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2493 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2494 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2495 — recover from original.html via tools/make_content.py>>>
\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と\(\textrm{Mark}\)の\((\textrm{IncrFirst},\textrm{Red},P)\)不変性と\(\textrm{Red}\)が許容性を保つことより\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)の場合に帰着される。以下\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)とし、\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(M\)に対して定義し、\(M\)に対しての適用であることを明示するために右肩に\(M\)を乗せて表記する。
<<<MISSING line 2497 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2498 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2499 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2500 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2501 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2502 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2503 — recover from original.html via tools/make_content.py>>>
\(\textrm{Lng}\)の\(\textrm{Red}\)不変性より\(j_1^N = \textrm{Lng}(N)-1 = \textrm{Lng}((M_j)_{j=m}^{j_1})-1 = j_1-m\)である。\((0,j_0^M) <_M^{\textrm{Next}} (0,j_1)\)かつ\((0,m) \leq_M (0,j_1)\)より\(m \leq j_0^M\)かつ\((0,j_0^M-m) <_N^{\textrm{Next}} (0,j_1^M-m) = (0,j_1-m) = (0,j_1^N)\)であるので、\(j_0^N = j_0^M-m\)である。\(N\)は簡約であるので簡約性と係数の関係より\(M\)と\(N\)は条件(A)と(B)を満たす。直系先祖による切片と\(\textrm{Red}\)と\(\textrm{IncrFirst}\)の関係より\(N\)は単項かつ\(\textrm{IncrFirst}^{M_{0,m}-M_{1,m}}(N) = (M_j)_{j=m}^{j_1}\)であり、すなわち\(N = ((M_{0,j}-M_{0,0}+M_{1,0},M_{1,j}))_{j=m}^{j_1}\)である。
<<<MISSING line 2505 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2506 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2507 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2508 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2509 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2510 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2511 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2512 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2513 — recover from original.html via tools/make_content.py>>>
\(D_{v^N} t_2^N = c_1^N = \textrm{Mark}(\textrm{Pred}(N),j_{-1}^N) = \textrm{Mark}(((M_{1,m},M_{1,m})),0) = D_{M_{1,m}} 0\)より\(v^N = M_{1,m}\)かつ\(t_2^N = 0\)である。
<<<MISSING line 2515 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2516 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2517 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2518 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2519 — recover from original.html via tools/make_content.py>>>
\(m\)の\(M\)許容性と\(j_0^M+1 = m+1 = j_1 = j_1^M\)から\(M\)は条件(I)か(III)か(VI)を満たす。条件(I)か(III)を満たすならば\(c_2^M = D_{v^M}(t_2^M + D_{M_{1,j_1}} 0) = D_{M_{1,m}} D_{M_{1,j_1}} 0\)であり、条件(VI)を満たすならば\(c_2^M = D_{v^M} D_{M_{1,j_1}} 0 = D_{M_{1,m}} D_{M_{1,j_1}} 0\)であるので、いずれの場合も\(c_2^M = D_{M_{1,m}} D_{M_{1,j_1}} 0\)であり、\(\textrm{Mark}(M,m) = s_{-1}^M c_2^M b_{-1}^M = D_{M_{1,m}} D_{M_{1,j_1}} 0\)である。
<<<MISSING line 2521 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2522 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2523 — recover from original.html via tools/make_content.py>>>
\(t_1^N = \textrm{Trans}(\textrm{Pred}(N)) = \textrm{Trans}((M_{1,m},M_{1,m})) = 0\)である。
<<<MISSING line 2525 — recover from original.html via tools/make_content.py>>>
従って\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と\(\textrm{Trans}\)の定義から\(\textrm{Trans}((M_j)_{j=m}^{j_1}) = \textrm{Trans}(N) = D_0 D_{N_{1,1}} 0 = D_{M_{1,m}} D_{M_{1,j_1}} 0\)である。
<<<MISSING line 2527 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2528 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2529 — recover from original.html via tools/make_content.py>>>
\(t_1^N = \textrm{Trans}(\textrm{Pred}(N)) = \textrm{Trans}((M_{1,m},M_{1,m})) = D_{M_{1,m}} 0 \neq 0\)であるので、\(N\)に対し条件(I)～(VI)が意味を持つ。
<<<MISSING line 2531 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2532 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2533 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2534 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2535 — recover from original.html via tools/make_content.py>>>
\(N_{1,j_1^N} = N_{1,1} = M_{1,j_1} > M_{1,m} > 0\)である。\((0,0) <_N^{\textrm{Next}} (0,1)\)かつ\(N_{1,0} = M_{1,m} < M_{1,j_1} = N_{1,1}\)より\((1,0) <_N^{\textrm{Next}} (1,1)\)であり、\(j_0^N+1 = 1 = j_1^N\)と\(N\)が条件(B)を満たすことから\(N_{1,j_0^N}+1 = N_{1,j_1^N}\)である。従って\(N\)は条件(VI)を満たす。
<<<MISSING line 2537 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2538 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2539 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2540 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2541 — recover from original.html via tools/make_content.py>>>
\(j_0^N\)が\(N\)許容かつ\(N_{1,j_0^N} = M_{1,m} \geq M_{1,j_1} = N_{1,j_1^N}\)より、\(N\)は条件(I)か(III)を満たす。
<<<MISSING line 2543 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2544 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2545 — recover from original.html via tools/make_content.py>>>
従っていずれの場合も\(\textrm{Trans}(N) = s_1^N c_2^N b_1^N = D_{M_{1,m}} D_{M_{1,j_1}} 0\)であり、\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性から\(\textrm{Trans}((M_j)_{j=m}^{j_1}) = \textrm{Trans}(N) = D_{M_{1,m}} D_{M_{1,j_1}} 0 = \textrm{Mark}(M,m)\)である。
<<<MISSING line 2547 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2548 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2549 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2550 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2551 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2552 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2553 — recover from original.html via tools/make_content.py>>>
\(\textrm{Red}(R)\)が簡約かつ単項であり、 \(\textrm{Lng}(N)-1 = j_1-m > 1\)と\(\textrm{Trans}\)が零項性を保つことより\(t_1^N \neq 0\)であるので、\(\textrm{Red}(N)\)に対して条件(I)～(VI)が意味を持つ。
<<<MISSING line 2555 — recover from original.html via tools/make_content.py>>>
基点の切片への遺伝性より\((\textrm{Pred}(M),m) \in T_{\textrm{PS}}^{\textrm{Marked}}\)であり\(\textrm{Lng}(\textrm{Pred}(M))-1 = j_1-1 < j_1\)であるので、\(\textrm{Red}\)と\(\textrm{Pred}\)の可換性と帰納法の仮定より
<<<MISSING line 2557 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2558 — recover from original.html via tools/make_content.py>>>
c_0^M & = & \textrm{Mark}(\textrm{Pred}(M),m) = \textrm{Trans}((\textrm{Pred}(M)_j)_{j=m}^{j_1-1}) = \textrm{Trans}((M_j)_{j=m}^{j_1-1}) = \textrm{Trans}((M_{0,j}-M_{0,m}+M_{1,m},M_{1,j})_{j=m}^{j_1-1}) = \textrm{Trans}(\textrm{Pred}(N)) = t_1^N \\
c_1^M & = & \textrm{Mark}(\textrm{Pred}(M),j_{-1}^M) = \textrm{Trans}((M_j)_{j=j_{-1}^M}^{j_1-1})
<<<MISSING line 2561 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2562 — recover from original.html via tools/make_content.py>>>
である。また\(N\)が単項より\((N,0) \in T_{\textrm{PS}}^{\textrm{Marked}}\)であり、基点の切片への遺伝性より\((\textrm{Pred}(N),0) \in T_{\textrm{PS}}^{\textrm{Marked}}\)となる。\(\textrm{Lng}(\textrm{Pred}(N))-1 = j_1^N-1 = j_1-m-1 < j_1\)であるので、\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と帰納法の仮定より
<<<MISSING line 2564 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2565 — recover from original.html via tools/make_content.py>>>
c_0^N & = & \textrm{Mark}(\textrm{Pred}(N),0) = \textrm{Trans}(\textrm{Pred}(N)) = \textrm{Trans}((M_{0,j}-M_{0,m}+M_{1,m},M_{1,j})_{j=m}^{j_1-1}) = \textrm{Trans}((M_j)_{j=m}^{j_1-1}) = c_0^M \\
c_1^N & = & \textrm{Mark}(\textrm{Pred}(N),j_{-1}^N) = \textrm{Trans}((\textrm{Pred}(N)_j)_{j=j_{-1}^N}^{j_1^N-1}) = \textrm{Trans}((M_{0,j}-M_{0,m}+M_{1,m},M_{1,j})_{j=j_{-1}^M}^{j_1-1}) = \textrm{Trans}((M_j)_{j=j_{-1}^M}^{j_1-1}) = c_1^M
<<<MISSING line 2568 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2569 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2570 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2571 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2572 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2573 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2574 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2575 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2576 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 2577 — recover from original.html via tools/make_content.py>>>
## 許容的親子関係[]

\(M \in T_{\textrm{PS}}\)とする。\(\mathbb{Z}^2\)上の二項関係\(<_M^{\textrm{NextAdm}}\)を以下のように定める：

- \((i_0,j_0), (i_1,j_1) \in \mathbb{Z}^2\)に対し、\((i_0,j_0)  <_M^{\textrm{NextAdm}} (i_1,j_1)\)であるとは、以下を満たすということである：

- \((i_0,j_0) \leq_M (i_1,j_1)\)である。

- \(j_0 < j_1\)である。

- \(j_0\)は\(M\)許容である。

- 任意の\(j \in \mathbb{N}\)に対し、\(j_0 < j < j_1\)ならば以下のいずれかを満たす：

- \((i_0,j) \leq_M (i_1,j_1)\)でない。

- \(j\)は非\(M\)許容である。

命題（\(\textrm{Adm}_M\)と\(<_M^{\textrm{NextAdm}}\)の関係）

\(M \in T_{\textrm{PS}}\)とし、\(j_1 := \textrm{Lng}(M) - 1\)と置く。任意の\(i \in \{0,1\}\)に対し、\((i,j_0) <_M^{\textrm{Next}} (i,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在するならば。\(j_{-1} := \textrm{Adm}_M(j_0)\)と置くと\((i,j_{-1}) <_M^{\textrm{NextAdm}} (i,j_1)\)である。

証明：

\((1,j_{-1}) \leq_M (1,j_0)\)かつ\((i,j_0) <_M^{\textrm{Next}} (i,j_1)\)より\((i,j_{-1}) \leq_M (i,j_1)\)である。更に\(j_{-1}\)は\(M\)許容である。

\(j \in \mathbb{N}\)とし、\(j_{-1} < j < j_1\)とする。\((i,j) \leq_M (i,j_1)\)ならば、\((i,j_0) <_M^{\textrm{Next}} (i,j_1)\)より\(j \leq j_0\)であり、従って\(\textrm{Adm}_M(j) \leq j_{-1} < j\)となるので\(j\)は\(M\)許容でない。

以上より、\((i,j_{-1}) <_M^{\textrm{NextAdm}} (i,j_1)\)である。□

命題（\(\textrm{Trans}\)と\(<_M^{\textrm{NextAdm}}\)の関係）

\(M \in T_{\textrm{PS}}\)とし、\(j_1 := \textrm{Lng}(M) - 1\)と置く。\((0,j_0) <_M^{\textrm{NextAdm}} (0,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在するならば、一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在し、以下を満たす：

(1) \((s_0,\textrm{Mark}(\textrm{Pred}(M),j_0),b_0)\)は\(\textrm{Trans}(\textrm{Pred}(M))\)のscb分解である。

(2) \((s_0,\textrm{Mark}(M,j_0),b_0)\)は\(\textrm{Trans}(M)\)のscb分解である。

証明：

\(\textrm{Trans}\)の再帰的定義と直系先祖の\(\textrm{Red}\)不変性から、\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)の場合に帰着される。

\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)ならば\(\textrm{Trans}\)の定義と直系先祖の\(\textrm{Red}\)不変性から即座に従う。□

系（\(\textrm{Mark}\)と\(<_M^{\textrm{NextAdm}}\)の関係）

\(M \in T_{\textrm{PS}}\)とし、\(j_1 := \textrm{Lng}(M) - 1\)と置く。\((0,j_0) <_M^{\textrm{NextAdm}} (0,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在するとする。任意の\(j \in \mathbb{N}\)に対し、\((0,j) \leq_M (0,j_0)\)ならば、一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在し、以下を満たす：

(1) \((s_0,\textrm{Mark}(\textrm{Pred}(M),j_0),b_0)\)は\(\textrm{Mark}(\textrm{Pred}(M),j)\)のscb分解である。

(2) \((s_0,\textrm{Mark}(M,j_0),b_0)\)は\(\textrm{Mark}(M,j)\)のscb分解である。

証明：

\(\textrm{Trans}\)と\(<_M^{\textrm{NextAdm}}\)の関係と\(\textrm{Mark}\)が順序関係を保つことから即座に従う。□

系（\(\textrm{Trans}\)の\(\textrm{Mark}\)と\(\textrm{Pred}\)による表示）

任意の\((M,m) \in T_{\textrm{PS}}^{\textrm{Marked}}\)に対し、\(m < \textrm{Lng}(M) - 1\)ならば一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在し、以下を満たす：

(1) \((s_0,\textrm{Mark}(\textrm{Pred}(M),m),b_0)\)は\(\textrm{Trans}(\textrm{Pred}(M))\)のscb分解である。

(2) \((s_0,\textrm{Mark}(M,m),b_0)\)は\(\textrm{Trans}(M)\)のscb分解である。

証明：

\(\textrm{Trans}\)と\(<_M^{\textrm{NextAdm}}\)の関係と\(\textrm{Mark}\)と\(<_M^{\textrm{NextAdm}}\)の関係から即座に従う。□

系（\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示）

任意の\((M,m) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)に対し、\(0 < m < \textrm{Lng}(M) - 1\)ならば一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在し、以下を満たす：

(1) \((s_0,D_{M_{1,m}} 0,b_0)\)は\(\textrm{Trans}((M_j)_{j=0}^{m})\)のscb分解である。

(2) \((s_0,\textrm{Mark}(M,m),b_0)\)は\(\textrm{Trans}(M)\)のscb分解である。

証明：

\(j_1 := \textrm{Lng}(M) - 1\)と置く。

\(\textrm{Trans}\)の再帰的定義と直系先祖の\(\textrm{Red}\)不変性から、\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)の場合に帰着される。以下\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)として、\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(M\)に対して定義し、\(M\)に対しての適用であることを明示するために右肩に\(M\)を乗せて表記する[48]。

\(j_1-m\)に関する数学的帰納法で示す。

\(j_1-m = 0\)ならば右端第\(1\)基点のMarkの基本性質より従う。

\(j_1-m = 1\)とする。

\(s_0 := s_1^M\)と置く。

\(b_0 := b_1^M\)と置く。

\((0,m) \leq_M (0,j_1) = (0,j_1^M)\)かつ\(m+1 = j_1 = j_1^M\)より\(j_0^M = m\)であり、\(m\)が\(M\)許容であることから\(j_{-1}^M = j_0^M = m\)である。従って\(s_{-1}\)と\(b_{-1}\)の空性と基点の関係より\(s_{-1}^M = ()\)かつ\(b_{-1}^M = ()\)である。

右端第\(1\)基点のMarkの基本性質より\(c_1^M = \textrm{Mark}(\textrm{Pred}(M),j_{-1}^M) = \textrm{Mark}(\textrm{Pred}(M),j_1-1) = D_{M_{1,m}} 0\)であるので、\(\textrm{Trans}((M_j)_{j=0}^{m}) = \textrm{Trans}(\textrm{Pred}(M)) = t_1^M = s_1^M c_1^M b_1^M = s_0 D_{M_{1,m}} b_0\)である。

\(\textrm{Trans}(M) = s_1^M c_2^M b_1^M = s_1^M s_{-1}^M c_2^M b_{-1}^M b_1^M = s_0 \textrm{Mark}(M,m) b_0\)である。

\(j_1-m > 1\)とする。

簡約性の切片への遺伝性より\(\textrm{Pred}(M)\)は簡約であり、\(0 < j_1-m-1 \leq j_1-1 < j_1\)かつ単項性の始切片への遺伝性より\(\textrm{Pred}(M)\)は単項であり、\(m < j_1 - 1\)かつ基点の切片への遺伝性より\((\textrm{Pred}(M),m) \in T_{\textrm{PS}}^{\textrm{Mark}}\)である。

従って帰納法の仮定から、一意な\((s_0,b_0) \in (\Sigma^{< \omega})^2\)が存在し、以下を満たす：

(1) \(b_0\)は\(\underline{)}\)のみからなる。

(2) \(\textrm{Trans}((\textrm{Pred}(M)_j)_{j=0}^{m}) = s_0 D_{\textrm{Pred}(M)_{1,m}} 0 b_0 = s_0 D_{M_{1,m}} 0 b_0\)である。

(3) \(\textrm{Trans}(\textrm{Pred}(M)) = s_0 \textrm{Mark}(\textrm{Pred}(M),m) b_0 = s_0 c_0^M b_0\)である。

\(\textrm{Trans}\)の\(\textrm{Mark}\)と\(\textrm{Pred}\)による表示から\(\textrm{Trans}(M) = s_0 \textrm{Mark}(M,m) b_0\)である。更に\(m \leq j_1-1\)より\((M_j)_{j=0}^{m} = (\textrm{Pred}(M)_j)_{j=0}^{m}\)であるので、\(\textrm{Trans}((M_j)_{j=0}^{m}) = \textrm{Trans}((\textrm{Pred}(M)_j)_{j=0}^{m}) = s_0 D_{M_{1,m}} 0 b_0\)である。□

系（\(\textrm{RightNodes}\)と\(\textrm{Mark}\)の関係）

任意の\((M,m) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)に対し、\(0 < m < \textrm{Lng}(M) - 1\)ならば、ある\(a_0, a_1 \in \mathbb{N}^{< \omega}\)が存在して以下を満たす：

(1) \(\textrm{RightNode}(\textrm{Trans}(M)) = a_0 \oplus_{\mathbb{N}} (M_{1,m}) \oplus_{\mathbb{N}} a_1\)である。

(2) \(\textrm{RightNode}(\textrm{Trans}((M_j)_{j=0}^{m})) = a_0 \oplus_{\mathbb{N}} (M_{1,m})\)である。

(3) \(\textrm{RightNode}(\textrm{Mark}(M,m)) = (M_{1,m}) \oplus_{\mathbb{N}} a_1\)である。

証明：

単項性の直系先祖による切片への遺伝性と\(\textrm{Mark}\)の左端の基本性質と\(\textrm{RightNodes}\)と部分表現の関係から即座に従う。□

写像
\begin{eqnarray*}
\textrm{RightAnces} \colon T_{\textrm{PS}} & \to & \mathbb{N}^{< \omega} \\
M & \mapsto & \textrm{RightAnces}(M)
\end{eqnarray*}
を以下のように定義する：

- \(\textrm{Trans}\)の再帰的定義中に導入した記号を用いる。

- \(M\)が簡約かつ\(j_1 = 0\)とする。

- \(M_0 = (0,0)\)ならば\(\textrm{RightAnces}(M) := ()\)である。

- \(M_0 \neq (0,0)\)ならば\(\textrm{RightAnces}(M) := (M_{1,0})\)である。

- \(M\)が簡約かつ\(j_1 > 0\)かつ単項とする。

- \(\textrm{Pred}(M)\)が零項ならば\(\textrm{RightAnces}(M) := (0,M_{1,j_1})\)である。

- \(\textrm{Pred}(M)\)が零項でないとする[49]。

- \((M_j)_{j=0}^{j_{-1}}\)が零項ならば\(a := (0)\)と置く。

- \((M_j)_{j=0}^{j_{-1}}\)が零項でないならば\(a := \textrm{RightAnces}((M_j)_{j=0}^{j_{-1}})\)と置く。

- \(M\)が条件(I)か(III)か(V)か(VI)を満たすならば\(\textrm{RightAnces}(M) := a \oplus_{\mathbb{N}} (M_{1,j_1})\)である。

- \(M\)が条件(II)か(IV)を満たすならば\(\textrm{RightAnces}(M) := a \oplus_{\mathbb{N}} (M_{1,j_0},M_{1,j_1})\)である。

- \(M\)が簡約かつ複項とする。

- \(J_1 := \textrm{Lng}(P(M))-1\)と置く。

- \(P(M)_{J_1} = ((0,0))\)ならば\(\textrm{RightAnces}(M) := (0)\)である。

- \(P(M)_{J_1} \neq ((0,0))\)ならば\(\textrm{RightAnces}(M) := \textrm{RightAnces}(P(M)_{J_1})\)である。

- \(M\)が簡約でないならば\(\textrm{RightAnces}(M) := \textrm{RightAnces}(\textrm{Red}(M))\)である。

命題（\(\textrm{RightNodes}\)と\(\textrm{RightAnces}\)の関係）

任意の\(M \in T_{\textrm{PS}}\)に対し、\(\textrm{RightAnces}(M) = \textrm{RightNodes}(\textrm{Trans}(M))\)である。

証明：

\(\textrm{RightNodes}\)と\(\textrm{Trans}\)と\(\textrm{RightAnces}\)の再帰的定義から、\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)である場合に帰着される。以下\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)とし、\(\textrm{RightNodes}\)の再帰的定義中に導入した記号と\(\textrm{Trans}\)の再帰的定義中に導入した記号を用いる。

\(M\)が単項より\(j_1 > 0\)である。また\(M\)が簡約より簡約性と係数の関係から\(M\)は条件(A)と(B)を満たす。

\(\textrm{RightAnces}(M) = \textrm{RightNodes}(\textrm{Trans}(M))\)であることを\(j_1\)に関する数学的帰納法で示す。

\(j_1 = 1\)とする。

\(2\)列ペア数列の基本性質 (1)より\(\textrm{Trans}(M) = D_{M_{1,0}} D_{M_{1,1}} 0\)であり、\(\textrm{RightNodes}(\textrm{Trans}(M)) = \textrm{RightNodes}(D_{M_{1,0}} D_{M_{1,1}} 0) = (M_{1,0},M_{1,1})\)である。

\(M\)が単項より\((0,0) <_M^{\textrm{Next}} (0,1) = (0,j_1)\)であるので\(j_0 = 0\)である。従って\(j_0\)は\(M\)許容であり\(j_{-1} = j_0 = 0\)である。

\(M_{1,0} = 0\)ならば、\(\textrm{Pred}(M) = ((M_{0,0},0))\)であるので\(\textrm{Pred}(M)\)は零項であり\(\textrm{RightAnces}(M) = (0,M_{1,j_1}) = (M_{1,0},M_{1,1})\)である。

\(M_{1,0} > 0\)とする。

\(\textrm{Pred}(M) = ((M_{0,0},M_{1,0}))\)より\(\textrm{Pred}(M)\)は零項でなく、\(a = \textrm{RightAnces}((M_j)_{j=0}^{j_{-1}}) = \textrm{RightAnces}((M_{0,0},M_{1,0})) = (M_{1,0})\)である。

\(j_0\)が\(M\)許容であり\(j_0+1 = 1 = j_1\)であるので、\(M\)は条件(I)か(III)か(VI)を満たす。従って\(\textrm{RightAnces}(M) = a \oplus_{\mathbb{N}} (M_{1,j_1}) = (M_{0,1},M_{1,1})\)である。

以上よりいずれの場合も\(\textrm{RightAnces}(M) = \textrm{RightNodes}(\textrm{Trans}(M))\)である。

\(j_1 > 1\)とする[50]。

\(\textrm{Mark}\)の左端の基本性質より\(v = M_{1,0}\)である。

\((M_j)_{j=0}^{j_{-1}}\)が零項であるとする。

この時\(a = (0)\)かつ\(j_{-1} = 0\)かつ\(v = M_{1,0} = 0\)であり、\(s_1\)と\(b_1\)の空性と基点の関係より\(s_1 = ()\)かつ\(b_1 = ()\)である。従って\(\textrm{Trans}(M) = s_1 c_2 b_1 = c_2\)である。

\(M\)が条件(I)か(III)か(V)か(VI)を満たすとする。

\(\textrm{RightAnces}(M) = a \oplus_{\mathbb{N}} (M_{1,j_1}) = (0,M_{1,j_1})\)である。

\(M\)が条件(VI)を満たすか否かに従って\(c_2 = D_v D_{M_{1,j_1}} 0 = D_0 D_{M_{1,j_1}} 0\)または\(c_2 = D_v(t_2 + D_{M_{1,j_1}} 0) = D_0(t_2 + D_{M_{1,j_1}} 0)\)となるので、いずれの場合も\(\textrm{RightNodes}(\textrm{Trans}(M)) = (0,M_{1,j_1}) = \textrm{RightAnces}(M)\)である。

\(M\)が条件(II)か(IV)を満たすならば、\(\textrm{RightAnces}(M) = a \oplus_{\mathbb{N}} (M_{1,j_0},M_{1,j_1}) = (0,M_{1,j_0},M_{1,j_1})\)であり、\(c_2 = D_v(t_3 + D_{M_{1,j_0}}(t_4 + D_{M_{1,j_1}} 0)) = D_0(t_3 + D_{M_{1,j_0}}(t_4 + D_{M_{1,j_1}} 0))\)より\(\textrm{RightNodes}(M) = (0,M_{1,j_0},M_{1,j_1}) = \textrm{RightAnces}(M)\)である。

\((M_j)_{j=0}^{j_{-1}}\)が零項であるとする。

\(N := (M_j)_{j=0}^{j_{-1}}\)と置く。

\(\textrm{Lng}(N)-1 = j_{-1} \leq j_0 < j_1\)であるので、帰納法の仮定より\(\textrm{RightAnces}(N) = \textrm{RightNodes}(N)\)である。

右端第\(2\)基点のMarkの基本性質より\(\textrm{Mark}(M,j_{-1}) = c_2\)であるので\(\textrm{Trans}(M) = s_1 c_2 b_1 = s_1 \textrm{Mark}(M,j_{-1}) b_1\)であり、\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より\(\textrm{Trans}(N) = s_1 D_{M_{1,j_{-1}}} b_1\)である。

\(M\)が条件(I)か(III)か(V)か(VI)を満たすとする。

\(\textrm{RightAnces}(M) = a \oplus_{\mathbb{N}} (M_{1,j_1}) = \textrm{RightAnces}(N) \oplus_{\mathbb{N}} (M_{1,j_1})\)である。

\(M\)が条件(VI)を満たすか否かに従って\(c_2 = D_v D_{M_{1,j_1}} 0 \)または\(c_2 = D_v(t_2 + D_{M_{1,j_1}} 0)\)であるので、いずれの場合も\(\textrm{RightNodes}(\textrm{Mark}(M,j_1)) = \textrm{RightNodes}(c_2) = (v,M_{1,j_1})\)である。従って\(\textrm{RightNodes}\)と\(\textrm{Mark}\)の関係から\(\textrm{RightNodes}(\textrm{Trans}(M)) = \textrm{RightNodes}(\textrm{Trans}(N)) \oplus_{\mathbb{N}} (M_{1,j_1}) = \textrm{RightAnsces}(N) \oplus_{\mathbb{N}} (M_{1,j_1})\)となる。

\(M\)が条件(II)か(IV)を満たすとする。

\(\textrm{RightAnces}(M) = a \oplus_{\mathbb{N}} (M_{1,j_0},M_{1,j_1}) = \textrm{RightAnces}(N) \oplus_{\mathbb{N}} (M_{1,j_0},M_{1,j_1})\)である。

\(c_2 = D_v(t_3 + D_{M_{1,j_0}}(t_4 + D_{M_{1,j_1}} 0))\)であるので、\(\textrm{RightNodes}(\textrm{Mark}(M,j_1)) = \textrm{RightNodes}(c_2) = (v,M_{1,j_0},M_{1,j_1})\)である。従って\(\textrm{RightNodes}\)と\(\textrm{Mark}\)の関係から\(\textrm{RightNodes}(\textrm{Trans}(M)) = \textrm{RightNodes}(\textrm{Trans}(N)) \oplus_{\mathbb{N}} (M_{1,j_0}M_{1,j_1}) = \textrm{RightAnsces}(N) \oplus_{\mathbb{N}} (M_{1,j_0},M_{1,j_1})\)となる。

以上より、いずれの場合も\(\textrm{RightAnces}(M) = \textrm{RightNodes}(\textrm{Trans}(M))\)である。□

系（非零項の\(\textrm{RightAnces}\)が非空であること）

任意の\(M \in T_{\textrm{PS}}\)に対し、以下は同値である：

(1) \(M\)は零項である。

(2) \(\textrm{RightAnces}(M) = ()\)である。

証明：

\(\textrm{Trans}\)が零項性を保つことと\(\textrm{RightNodes}\)と\(\textrm{RightAnces}\)の関係から即座に従う。□

# 停止性[]

まずは単項な標準形ペア数列に対し条件(I)～(VI)のそれぞれの下での展開規則を調べ、それによりBuchholzの表記系における展開規則との比較を行い、標準形ペア数列に伴う計算可能関数の全域性（すなわち計算規則の停止性）を証明する。

## 条件(I)の下での展開規則[]

命題（条件(I)の下での\(\textrm{Trans}\)と基本列の交換関係）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用いると、\(j_1 > 1\)かつ\(M\)が条件(I)を満たすならば[51]、以下が成り立つ：

(1) \(\textrm{Trans}(M[n]) = \textrm{Trans}(M)[n-1]\)である。

(2) \(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

条件(I)の下での\(\textrm{Trans}\)と基本列の交換関係を証明するための準備としていくつかの補題を示す。

補題（公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質）

任意の\(u,v \in \mathbb{N}\)に対し、\(u < v\)ならば\(M = ((j,j))_{j=u}^{v}\)と置くと\(\textrm{Trans}(M) = D_u D_v 0\)である。

証明：

\(M\)は単項であり、また条件(A)と(B)を満たすので簡約性と係数の関係から\(M\)は簡約である。\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(M\)に対して定義し、\(M\)に対しての適用であることを明示するために右肩に\(M\)を乗せて表記する[52]。

\(j_1^M = v-u\)かつ\(j_0^M = j_1^M-1 = v-u-1\)かつ\(j_{-1}^M = 0\)である。\(M_{v-u-1} = (v-1,v-1)\)かつ\(M_{v-u} = (v,v)\)より\((1,j_0^M) = (1,v-u-1) <_M^{\textrm{Next}} (1,v-u) = (1,j_1^M)\)である。

\(v-u\)に関する数学的帰納法で示す。

\(v-u = 1\)とする。

\(j_1^M = v-u = 1\)かつ\(j_0^M = v-u-1 = 0\)より\(j_{-1}^M = 0 = j_0\)となるので、\(j_0^M\)は\(M\)許容である。

\(u = 0\)ならば、\(t_1^M = \textrm{Trans}(\textrm{Pred}(M)) = \textrm{Trans}((0,0)) = 0\)であるので\(\textrm{Trans}(M) = D_0 D_v 0 = D_u D_v 0\)である。

\(u > 0\)とする。

\(t_1^M = \textrm{Trans}(\textrm{Pred}(M)) = \textrm{Trans}((u,u)) = D_u 0 \neq 0\)であるので\(M\)に対し条件(I)～(VI)が意味を持つ。

\(j_{-1}^M = 0\)と\(s_1\)と\(b_1\)の空性と基点の関係から\(s_1^M = ()\)かつ\(b_1^M = ()\)である。従って\(D_{v^M} t_2^M = c_1^M = s_1^M c_1^M b_1^M = t_1^M = D_u 0\)より\(v^M = u\)かつ\(t_2^M = 0\)である。

\(M_{1,j_1} = v = u+1 = M_{1,j_0}+1 > 0\)かつ\(j_0+1 = 1 = j_1\)であるので\(M\)は条件(VI)を満たす。従って\(c_2^M = D_{v^M} D_{M_{1,j_1^M}} 0 = D_u D_v 0\)であり、\(\textrm{Trans}(M) = s_1^M c_2^M b_1^M = D_u D_v 0\)である。

lemma idxsum_leftend_lmin:

\(\textrm{Pred}(M) = ((j,j))_{j=u}^{v-1}\)であるので、帰納法の仮定から\(t_1^M = \textrm{Trans}(\textrm{Pred}(M)) = D_u D_{v-1} 0 \neq 0\)であるので\(M\)に対し条件(I)～(VI)が意味を持つ。

\(j_{-1}^M = 0\)と\(s_1\)と\(b_1\)の空性と基点の関係から\(s_1^M = ()\)かつ\(b_1^M = ()\)であり、\(D_{v^M} t_2^M = c_1^M = D_u D_{v-1} 0\)より\(v^M = u\)かつ\(t_2^M = D_{v-1} 0\)である。

\(M_{1,j_1} = v = u+1 = M_{1,j_0}+1 > 0\)かつ\(j_0+1 = 1 = j_1\)であるので\(M\)は条件(VI)を満たす。従って\(c_2^M = D_{v^M} D_{M_{1,j_1^M}} 0 = D_u D_v 0\)であり、\(\textrm{Trans}(M) = s_1^M c_2^M b_1^M = D_u D_v 0\)である。□

系（\(\textrm{Pred}\)が公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質）

任意の\(u,v,w,w' \in \mathbb{N}\)に対し、\(u < v\)ならば\(M := ((j,j))_{j=u}^{v} \oplus_{\mathbb{N}^2} (w',w)\)と置くと以下が成り立つ：

(1) \(w' = v+1\)かつ\(u < w \leq v\)ならば\(\textrm{Trans}(M) = D_u D_v D_w 0\)である。

(2) \(u < w' \leq v\)かつ\(w = w'\)ならば\(\textrm{Trans}(M) = D_u \underline{(} D_v 0 \underline{,} D_w 0 \underline{)}\)である。

(3) \(u+1 < w' \leq v\)かつ\(w < w'\)ならば\(\textrm{Trans}(M) = D_u \underline{(} D_v 0 \underline{,} D_{w'-1} \underline{(} D_v 0 \underline{,} D_w 0 \underline{)} \underline{)}\)である。

(4) \(u+1 = w'\)かつ\(w < w'\)ならば\(\textrm{Trans}(M) = D_u \underline{(} D_v 0 \underline{,} D_w 0 \underline{)}\)である。

証明：

いずれの場合も\(M\)は単項であり、また条件(A)と(B)を満たすので簡約性と係数の関係から\(M\)は簡約である。\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(M\)に対して定義し、\(M\)に対しての適用であることを明示するために右肩に\(M\)を乗せて表記する[53]。

\(\textrm{Pred}(M) = ((j,j))_{j=u}^{v}\)であり、公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質より\(t_1^M = \textrm{Trans}(\textrm{Pred}(M)) = D_u D_v 0 \neq 0\)であるので、\(M\)に対して条件(I)～(VI)が意味を持つ。

\(j_1^M = v-u+1\)である。左端第\(1\)基点のMarkの基本性質より\(\textrm{Mark}(\textrm{Pred}(M),0) = t_1^M = D_u D_v 0\)であり、右端第\(1\)基点のMarkの基本性質より\(\textrm{Mark}(\textrm{Pred}(M),j_1^M-1) = D_{\textrm{Pred}(M)_{1,j_1^M-1}} 0 = D_v 0\)である。

\(w' = v+1\)かつ\(u < w \leq v\)とする。

\(j_0^M = j_1^M-1 = v-u\)であり、\(M_{1,j_0^M} = M_{1,v-u} = v\)かつ\(M_{1,j_1^M} = M_{1,v-u+1} = w \leq v = M_{1,j_0^M}\)より\((1,j_0^M) <_M^{\textrm{Next}} (1,j_1^M)\)でなく、\(j_0^M\)は\(M\)許容であるので\(j_{-1}^M = j_0^M = j_1^M-1\)である。従って\(M\)は条件(I)か(III)を満たす。

\(c_1^M = \textrm{Mark}(\textrm{Pred}(M),j_{-1}^M) = \textrm{Mark}(\textrm{Pred}(M),j_1^M-1) = D_v 0\)であり、\(s_1^M D_v 0 b_1^M = s_1^M c_1^M b_1^M = t_1^M = D_u D_v 0\)より\(s_1^M = D_u\)かつ\(b_1^M = ()\)である。また\(D_{v^M} t_2^M = c_1^M = D_v 0\)より\(v^M = v\)かつ\(t_2^M = 0\)であるので\(c_2^M = D_{v^M}(t_2^M + D_{M_{1,j_1^M}} 0) = D_v(0 + D_w 0) = D_v D_w 0\)である。

以上より\(\textrm{Trans}(M) = s_1^M c_2^M b_1^M = D_u D_v D_w 0\)である。

\(u < w' \leq v\)かつ\(w = w'\)とする。

\(j_0^M = w'-u-1\)であり、\(M_{1,j_0^M} = M_{1,w'-u-1} = w'-1\)かつ\(M_{1,j_1^M} = M_{1,v-u+1} = w = M_{1,j_0^M}+1\)より\((1,j_0^M) <_M^{\textrm{Next}} (1,j_1^M)\)であり、\(j_0^M\)は非\(M\)許容であるので\(j_{-1}^M = 0\)である。従って\(M\)は条件(V)を満たす。

\(c_1^M = \textrm{Mark}(\textrm{Pred}(M),j_{-1}^M) = \textrm{Mark}(\textrm{Pred}(M),0) = D_u D_v 0\)であり、\(j_{-1}^M = 0\)と\(s_1\)と\(b_1\)の空性と基点の関係から\(s_1^M = ()\)かつ\(b_1^M = ()\)である。また\(D_{v^M} t_2^M = c_1^M = D_u D_v 0\)より\(v^M = u\)かつ\(t_2^M = D_v 0\)であるので\(c_2^M = D_{v^M}(t_2^M + D_{M_{1,j_1^M}} 0) = D_u(D_v 0 + D_w 0) = D_u \underline{(} D_v 0 \underline{,} D_w 0 \underline{)}\)である。

以上より\(\textrm{Trans}(M) = s_1^M c_2^M b_1^M = D_u \underline{(} D_v 0 \underline{,} D_w 0 \underline{)}\)である。

\(u+1 < w' \leq v\)かつ\(w < w'\)とする。

\(j_0^M = w'-u-1 > 0\)であり、\(M_{1,j_0^M} = M_{1,w'-u-1} = w'-1\)かつ\(M_{1,j_1^M} = M_{1,v-u+1} = w \leq w'-1 = M_{1,j_0^M}\)より\((1,j_0^M) <_M^{\textrm{Next}} (1,j_1^M)\)でなく、\(j_0^M\)は非\(M\)許容であるので\(j_{-1}^M = 0\)である。従って\(M\)は条件(IV)を満たす。

\(c_1^M = \textrm{Mark}(\textrm{Pred}(M),j_{-1}^M) = \textrm{Mark}(\textrm{Pred}(M),0) = D_u D_v 0\)であり、\(j_{-1}^M = 0\)と\(s_1\)と\(b_1\)の空性と基点の関係から\(s_1^M = ()\)かつ\(b_1^M = ()\)である。また\(D_{v^M} t_2^M = c_1^M = D_u D_v 0\)より\(v^M = u\)かつ\(t_2^M = D_v 0\)であり、\(v \geq w' > w'-1\)より\(t_2^M\)の唯一の単項成分\(D_v 0\)の左端は\(D_v \neq D_{w'-1} = D_{M_{1,j_0^M}}\)であるので\(t_3^M = t_2^M = D_v  0\)かつ\(t_4^M = t_2^M = D_v 0\)となる。従って\(c_2^M = D_{v^M}(t_3^M + D_{M_{1,j_0^M}}(t_4^M + D_{M_{1,j_1^M}} 0)) = D_u(D_v 0 + D_{w'-1}(D_v 0 + D_w 0)) = D_u \underline{(} D_v 0 \underline{,} D_{w'-1} \underline{(} D_v 0 \underline{,} D_w 0 \underline{)} \underline{)}\)である。

以上より\(\textrm{Trans}(M) = s_1^M c_2^M b_1^M = D_u \underline{(} D_v 0 \underline{,} D_{w'-1} \underline{(} D_v 0 \underline{,} D_w 0 \underline{)} \underline{)}\)である。

\(u+1 = w'\)かつ\(w < w'\)とする。

\(j_0^M = 0\)であり、\(M_{1,j_0^M} = M_{1,0} = u\)かつ\(M_{1,j_1^M} = M_{1,v-u+1} = w \leq w'-1 = u = M_{1,j_0^M}\)より\((1,j_0^M) <_M^{\textrm{Next}} (1,j_1^M)\)でなく、\(j_0^M\)は\(M\)許容であるので\(j_{-1}^M = j_0^M = 0\)である。従って\(M\)は条件(I)か(III)を満たす。

\(c_1^M = \textrm{Mark}(\textrm{Pred}(M),j_{-1}^M) = \textrm{Mark}(\textrm{Pred}(M),0) = D_u D_v 0\)であり、\(j_{-1}^M = 0\)と\(s_1\)と\(b_1\)の空性と基点の関係から\(s_1^M = ()\)かつ\(b_1^M = ()\)である。また\(D_{v^M} t_2^M = c_1^M = D_u D_v 0\)より\(v^M = u\)かつ\(t_2^M = D_v 0\)であるので\(c_2^M = D_{v^M}(t_2^M + D_{M_{1,j_1^M}} 0) = D_u(D_v 0 + D_w 0) = D_u \underline{(} D_v 0 \underline{,} D_w 0 \underline{)}\)である。

以上より\(\textrm{Trans}(M) = s_1^M c_2^M b_1^M = D_u \underline{(} D_v 0 \underline{,} D_w 0 \underline{)}\)である。□

補題（条件(I)か(III)の下での\(c_1\)前後の具体表示）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用いると、\(j_0\)が\(M\)許容かつ\(j_1 > 1\)かつ\(M_{1,j_0} \geq M_{1,j_1}\)ならば、以下が成り立つ：

(1) \(t_1 \neq 0\)であり\(M\)は条件(I)か(III)を満たし\(\textrm{Trans}((M_j)_{j=j_0}^{j_1-1}) = c_1 \in PT_{\textrm{B}}\)である。

更に\((0,j'_0) <_M^{\textrm{Next}} (0,j_0)\)を満たす一意な\(j'_0 \in \mathbb{N}\)が存在するとし、\(j'_{-1} := \textrm{Adm}_M(j'_0)\)と置く。

(2) \(j'_0 \leq j_1-2\)かつ\((\textrm{Pred}(M),j'_{-1}) \in T_{\textrm{PS}}^{\textrm{Marked}}\)かつ\(((M_j)_{j=j'_{-1}}^{j_1-1},j_0-j'_{-1}) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。

(3) \(j'_0+1 = j_0\)ならば以下が成り立つ：

(3-1) \(j'_{-1} = j'_0\)または\(M_{1,j'_0}+1 = M_{1,j_0}\)ならば、\(\textrm{Mark}(\textrm{Pred}(M),j'_{-1}) = D_{M_{1,j'_{-1}}} c_1\)である。

(3-2) \(j'_{-1} < j'_0\)かつ\(M_{1,j'_0} \geq M_{1,j_0}\)ならば、\(\textrm{Mark}(\textrm{Pred}(M),j'_{-1}) = D_{M_{1,j'_{-1}}} D_{M_{1,j'_0}} c_1\)である。

(4) \(j'_0+1 < j_0\)ならば以下が成り立つ：

(4-1) \(j'_{-1} = j'_0\)または\(M_{1,j'_0}+1 = M_{1,j_0}\)ならば、一意な\(t'_2 \in T_{\textrm{B}}^2\)が存在して\(\textrm{Mark}(\textrm{Pred}(M),j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_2+c_1)\)である。

(4-2) \(j'_{-1} < j'_0\)かつ\(M_{1,j'_0} \geq M_{1,j_0}\)ならば、一意な\((t'_3,t'_4) \in T_{\textrm{B}}^2\)が存在して\(\textrm{Mark}(\textrm{Pred}(M),j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4+c_1))\)である。

更に任意の\(n \in \mathbb{N}_+\)に対し、\(n > 1\)とし、\(N := (M[n]_j)_{j=0}^{j_0+(n-1)(j_1-j_0)}\)と置き\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(N\)に対して定め\(N\)に対する適用であることを明示するために右肩に\(N\)を乗せて表記する。

(5) \((M[n],j_0+(n-1)(j_1-j_0)) \in T_{\textrm{B}}^{\textrm{Marked}}\)かつ\((0,j'_0) <_{M[n]}^{\textrm{Next}} (0,j_0+(n-1)(j_1-j_0))\)であり、\(j_1^N = j_0+(n-1)(j_1-j_0)\)かつ\(j_0^N = j'_0\)かつ\(j_{-1}^N = j'_{-1}\)かつ\(t_1^N \neq 0\)であり、\(N\)は条件(VI)を満たさない。

証明：

(1)が成り立つことを示す。

\(\textrm{Lng}(\textrm{Pred}(M))-1 = j_1 > 1\)より\(\textrm{Pred}(M)\)は零項でなく、従って\(\textrm{Trans}\)が零項性を保つことから\(t_1 \neq 0\)である。\(M_{1,j_0} \geq M_{1,j_1}\)かつ\(j_0\)が\(M\)許容より\(j_0 = j_{-1}\)であり\(M\)は条件(I)か(III)を満たす。

\(j_0\)が\(M\)許容より\(j_{-1} = j_0\)である。従って\(c_1 = \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = \textrm{Trans}((\textrm{Pred}(M)_j)_{j=j_{-1}}^{j_1-1}) = \textrm{Trans}((M_j)_{j=j_0}^{j_1-1})\)である。また\(t_1 \neq 0\)かつ\((t_1,c_1) \in T_{\textrm{B}}^{\textrm{Marked}}\)から\(c_1 \in PT_{\textrm{B}}\)である。

(2)が成り立つことを示す。
lemma idxsum_lmin_leftend:
\(j'_{-1} \leq j'_0 < j_0 < j_1\)より\(j'_{-1} \leq j_1-2\)である。\((0,j'_{-1}) \leq_M (0,j'_0) <_M^{\textrm{Next}} (0,j_0) <_M^{\textrm{Next}} (0,j_1)\)より\((M,j'_{-1}) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。従って基点の切片への遺伝性より\((\textrm{Pred}(M),j'_{-1}) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。\((M,j_0) \in T_{\textrm{PS}}^{\textrm{Marked}}\)と基点の切片への遺伝性より\(((M_j)_{j=j'_{-1}}^{j_1-1},j_0-j'_{-1}) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。

(3), (4)が成り立つことを示す。

\(N := (M_j)_{j=j'_{-1}}^{j_0}\)と置く。\(\textrm{Red}(N)\)は簡約であるので簡約性と係数の関係より\(M\)と\(\textrm{Red}(N)\)は条件(A)と(B)を満たす。\(\textrm{Red}(N)\)が条件(A)と(B)を満たすことと直系先祖による切片と\(\textrm{Red}\)と\(\textrm{IncrFirst}\)の関係より

\begin{eqnarray*}
N & = & \textrm{IncrFirst}^{M_{0,j'_{-1}}-M_{1,j'_{-1}}}(\textrm{Red}(N)) \\
\textrm{Red}(N) & = & ((j,j))_{j=M_{1,j'_{-1}}}^{M_{1,j'_0}} \oplus_{\mathbb{N}^2} ((M_{0,j}-M_{0,j'_{-1}}+M_{1,j'_{-1}},M_{1,j}))_{j=j'_0+1}^{j_0-1} \oplus_{\mathbb{N}^2} ((M_{1,j'_0}+1,M_{1,j_0}))
\end{eqnarray*}

となる。従って\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性より

\begin{eqnarray*}
\textrm{Trans}(N) & = & \textrm{Trans}(\textrm{Red}(N)) \\
& = & \textrm{Trans}(((j,j))_{j=M_{1,j'_{-1}}}^{M_{1,j'_0}} \oplus_{\mathbb{N}^2} ((M_{0,j}-M_{0,j'_{-1}}+M_{1,j'_{-1}},M_{1,j}))_{j=j'_0+1}^{j_0-1} \oplus_{\mathbb{N}^2} ((M_{1,j'_0}+1,M_{1,j_0})))
\end{eqnarray*}

である。

\(j'_0+1 = j_0\)とする。

\begin{eqnarray*}
\textrm{Trans}(N) = \textrm{Trans}(\textrm{Red}(N)) = \textrm{Trans}(((j,j))_{j=M_{1,j'_{-1}}}^{M_{1,j'_0}} \oplus_{\mathbb{N}^2} ((M_{0,j}-M_{0,j'_{-1}}+M_{1,j'_{-1}},M_{1,j}))_{j=j'_0+1}^{j_0-1} \oplus_{\mathbb{N}^2} ((M_{1,j'_0}+1,M_{1,j_0}))) = \textrm{Trans}(((j,j))_{j=M_{1,j'_{-1}}}^{M_{1,j'_0}} \oplus_{\mathbb{N}^2} (M_{1,j'_0}+1,M_{1,j_0}))
\end{eqnarray*}

である。\(M_{1,j'_0}+1 = M_{1,j_0}\)ならば公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質より

\begin{eqnarray*}
\textrm{Trans}(N) = \textrm{Trans}(((j,j))_{j=M_{1,j'_{-1}}}^{M_{1,j'_0}} \oplus_{\mathbb{N}^2} (M_{1,j'_0}+1,M_{1,j_0})) = D_{M_{1,j'_{-1}}} D_{M_{1,j_0}} 0
\end{eqnarray*}

であり、\(j'_{-1} = j'_0\)かつ\(M_{1,j'_0} \geq M_{1,j_0}\)ならば\(2\)列ペア数列の基本性質より

\begin{eqnarray*}
\textrm{Trans}(N) = \textrm{Trans}(((j,j))_{j=M_{1,j'_{-1}}}^{M_{1,j'_0}} \oplus_{\mathbb{N}^2} (M_{1,j'_0}+1,M_{1,j_0})) = D_{M_{1,j'_{-1}}} D_{M_{1,j_0}} 0
\end{eqnarray*}

であり、\(j'_{-1} < j'_0\)かつ\(M_{1,j'_0} \geq M_{1,j_0}\)ならば\(\textrm{Pred}\)が公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質 (1)より

\begin{eqnarray*}
\textrm{Trans}(N) = \textrm{Trans}(((j,j))_{j=M_{1,j'_{-1}}}^{M_{1,j'_0}} \oplus_{\mathbb{N}^2} (M_{1,j'_0}+1,M_{1,j_0})) = D_{M_{1,j'_{-1}}} D_{M_{1,j'_0}} D_{M_{1,j_0}} 0
\end{eqnarray*}

である。従って\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示と\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より、\(j'_{-1} = j'_0\)または\(M_{1,j'_0}+1 = M_{1,j_0}\)ならば、

\begin{eqnarray*}
\textrm{Mark}(\textrm{Pred}(M),j'_{-1}) & = & \textrm{Trans}((M_j)_{j=j'_{-1}}^{j_1-1}) = D_{M_{1,j'_{-1}}} \textrm{Trans}((M_j)_{j=j_0}^{j_1-1}) \\
& = & D_{M_{1,j'_{-1}}} \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = D_{M_{1,j'_{-1}}} c_1
\end{eqnarray*}

であり、\(j'_{-1} < j'_0\)かつ\(M_{1,j'_0}+1 = M_{1,j_0}\)ならば

\begin{eqnarray*}
\textrm{Mark}(\textrm{Pred}(M),j'_{-1}) & = & \textrm{Trans}((M_j)_{j=j'_{-1}}^{j_1-1}) = D_{M_{1,j'_{-1}}} D_{M_{1,j'_0}} \textrm{Trans}((M_j)_{j=j_0}^{j_1-1}) \\
& = & D_{M_{1,j'_{-1}}} \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = D_{M_{1,j'_{-1}}} D_{M_{1,j'_0}} c_1
\end{eqnarray*}

である。

\(j'_0+1 < j_0\)とする。

\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(N\)に対して定め、\(N\)に対する適用であることを明示するために右肩に\(N\)を乗せて表記する。

\(j_1^N = j_0-j'_{-1}\)かつ\(j_0^N = j'_0-j'_{-1}\)であり、許容化の切片への遺伝性より\(j_{-1}^N = \textrm{Adm}_N(j_0^N) = \textrm{Adm}_M(j'_0)-j'_{-1} = 0\)である。従って\(s_1\)と\(b_1\)の空性と基点の関係から\(s_1^N = ()\)かつ\(b_1^N = ()\)であり、

\(j'_{-1} \leq j'_0 < j'_0+1 < j_0\)より\(j_1^N = j_0-j'_{-1} > 2\)であるので\(\textrm{Pred}(N)\)は零項でなく、\(\textrm{Trans}\)が零項性を保つことから\(t_1^N \neq 0\)である。従って\(N\)に対し条件(I)～(VI)が意味を持つ。

\(j_0^N+1 = j'_0+1-j'_{-1} < j_0-j'_{-1} = j_1^N\)より\(N\)は条件(VI)を満たさない。\(\textrm{Trans}\)の最左単項成分の左端の基本性質より\(v^N = N_{1,0} = M_{1,j'_{-1}}\)である。

\(j'_{-1} = j'_0\)または\(M_{1,j'_0}+1 = M_{1,j_0}\)とする。

\(t'_2 := t_2^N\)と置く。

\(j'_{-1} = j'_0\)ならば、\(j_{-1}^N = 0 = j'_0-j'_{-1} = j_0^N\)より\(j_0^N\)は\(N\)許容となり条件(I)か(III)を満たす。

\(M_{1,j'_0}+1 = M_{1,j_0}\)ならば、\(N\)が条件(VI)を満たさないことから\(N\)は条件(V)を満たす。

いずれの場合も

\begin{eqnarray*}
c_2^N & = & D_{v^N}(t_2^N + D_{N_{1,j_1^N}} 0) = D_{M_{1,j'_{-1}}}(t'_2+D_{M_{1,j_0}} 0) \\
\textrm{Trans}(N) & = & s_1^N c_2^N b_1^N = D_{M_{1,j'_{-1}}}(t'_2+D_{M_{1,j_0}} 0)
\end{eqnarray*}

である。従って加法とscb分解の関係と\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示と\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より

\begin{eqnarray*}
\textrm{Mark}(\textrm{Pred}(M),j'_{-1}) & = & \textrm{Trans}((M_j)_{j=j'_{-1}}^{j_1-1}) = D_{M_{1,j'_{-1}}}(t'_2 + \textrm{Trans}((M_j)_{j=j_0}^{j_1-1})) \\
& = & D_{M_{1,j'_{-1}}}(t'_2 + \textrm{Mark}(\textrm{Pred}(M),j_{-1})) = D_{M_{1,j'_{-1}}}(t'_2+c_1)
\end{eqnarray*}

である。

\(j'_{-1} < j'_0\)かつ\(M_{1,j'_0} \geq M_{1,j_0}\)とする。

\(j_{-1}^N = 0 < j'_0-j'_{-1} = j_0^N\)より\(j_0^N\)は非\(N\)許容となり、\(N_{1,j_0^N} = M_{1,j'_0} \geq M_{1,j_0} = N_{1,j_1^N}\)より\(N\)は条件(II)か(IV)を満たす。

\(t'_3 := t_3^N\)と置く。

\(t'_4 := t_4^N \)と置く。

\begin{eqnarray*}
c_2^N & = & D_{v^N}(t_3^N + D_{N_{1,j_0^N}}(t_4^N + D_{N_{1,j_1^N}} 0)) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + D_{M_{1,j_0}} 0)) \\
\textrm{Trans}(N) & = & s_1^N c_2^N b_1^N = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + D_{M_{1,j_0}} 0))
\end{eqnarray*}

である。従って加法とscb分解の関係と\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示と\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より

\begin{eqnarray*}
\textrm{Mark}(\textrm{Pred}(M),j'_{-1}) & = & \textrm{Trans}((M_j)_{j=j'_{-1}}^{j_1-1}) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + \textrm{Trans}((M_j)_{j=j_0}^{j_1-1}))) \\
& = & D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + \textrm{Mark}(\textrm{Pred}(M),j_{-1}))) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4+c_1))
\end{eqnarray*}

である。

(5)が成り立つことを示す。

\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)と親の基本性質 (1)より、任意の\(j \in \mathbb{N}\)に対し\(j_0 < j \leq j_1\)ならば\(M_{0,j} \geq M_{0,j_1} > M_{0,j_0}\)である。従って親の存在の判定条件 (3)より\((0,j_0) \leq_M (0,j_1-1)\)である。更に\((M_j)_{j=j_0}^{j_1-1} = (M[n]_j)_{j=j_0+(n-1)(j_1-j_0)}^{j_0+n(j_1-j_0)-1}\)であるので、\((0,j_0+(n-1)(j_1-j_0)) \leq_{M[n]} (0,j_0+n(j_1-j_0)-1)\)である。

\(n > 1\)より\(M[n]_{0,j_0+(n-1)(j_1-j_0)-1} = M_{0,j_1-1} > M_{0,j_0} = M[n]_{0,j_0+(n-1)(j_1-j_0)}\)となるので、\((0,j_0+(n-1)(j_1-j_0)-1) <_{M[n]}^{\textrm{Next}} (0,j_0+(n-1)(j_1-j_0))\)でない。従って\(j_0+(n-1)(j_1-j_0)\)は\(M[n]\)許容である。以上より\((M[n],j_0+(n-1)(j_1-j_0)) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。

任意の\(j \in \mathbb{N}\)に対し、\(j_0 \leq j < j_0+(n-1)(j_1-j_0)\)ならば、\(j-j_0\)を\(j_1-j_0 > 0\)で割った余りを\(r \in \mathbb{N}\)と置くと\(r < j_1-j_0\)であり、\(r = 0\)ならば\(M[n]_{0,j} = M_{0,j_0+r} = M_{0,j_0} = M[n]_{0,j_0+(n-1)(j_1-j_0)}\)となり\(r > 0\)ならば\(M[n]_{0,j} = M_{0,j_0+r} \geq M_{0,j_1} > M_{0,j_0} = M[n]_{0,j_0+(n-1)(j_1-j_0)}\)であるのでいずれの場合も\((0,j) \leq_{M[n]} (0,j_0+(n-1)(j_1-j_0))\)でない。

また任意の\(j \in \mathbb{N}\)に対し、\(j'_0 < j < j_0\)ならば、\((0,j'_0) <_M^{\textrm{Next}} (0,j_0)\)と親の基本性質 (1)より\(M[n]_{0,j} = M_{0,j} \geq M_{0,j_0} = M[n]_{0,j_0+(n-1)(j_1-j_0)}\)であるので\((0,j) \leq_{M[n]} (0,j_0+(n-1)(j_1-j_0))\)でない。

更に\((0,j'_0) <_M^{\textrm{Next}} (0,j_0)\)より\(M[n]_{0,j'_0} = M_{0,j'_0} < M_{0,j_0} = M[n]_{0,j_0+(n-1)(j_1-j_0)}\)であるので、以上より\((0,j'_0) <_{M[n]}^{\textrm{Next}} (0,j_0+(n-1)(j_1-j_0))\)である。

\(\textrm{Lng}(N) = j_0+(n-1)(j_1-j_0)+1\)より\(j_1^N = j_0+(n-1)(j_1-j_0) \geq j_0 + (j_1-j_0) \geq j_0+1 > 1\)であるので\(\textrm{Pred}(N)\)は零項でなく、\(\textrm{Trans}\)が零項性を保つことより\(t_1^N \neq 0\)である。従って\(N\)に対して条件(I)～(VI)が意味を持つ。

\((0,j'_0) <_{M[n]}^{\textrm{Next}} (0,j_0+(n-1)(j_1-j_0))\)より\((0,j'_0) <_N^{\textrm{Next}} (0,j_0+(n-1)(j_1-j_0)) = (0,j_1^N)\)であるので\(j_0^N = j'_0\)であり、\(\textrm{Pred}(N) = (M[n]_j)_{j=0}^{j_0+(n-1)(j_1-j_0)-1} = M[n-1]\)である。従って\(t_1^N = \textrm{Trans}(\textrm{Pred}(N)) = \textrm{Trans}(M[n-1]) = \textrm{Trans}(M)[n-2]\)である。
  @{thm [source] p_6_4_P_IdxSum_char_2}.\<close>
\(j'_0 < j_0 \leq j_1-1\)と許容化の切片への遺伝性より\(\textrm{Adm}_N(j'_0) = \textrm{Adm}_{\textrm{Pred}(M)}(j'_0) = j'_{-1}\)である。従って\(j_{-1}^N = \textrm{Adm}_N(j_0^N) = \textrm{Adm}_N(j'_0) = j'_{-1}\)である。

\(j_0^N+1 = j'_0+1 \leq j_0 < j_1 \leq j_0+(n-1)(j_1-j_0) = j_1^N\)より、\(N\)は条件(VI)を満たさない。□

それでは本題に戻る。

条件(I)の下での\(\textrm{Trans}\)と基本列の交換関係の証明：

\(M\)は単項であるので\(\textrm{Trans}\)が零項性を保つことから\(\textrm{Trans}(M) \neq 0\)である。

(2)は(1)と\(\textrm{Trans}(M) \neq 0\)と[Buc1] Lemma 3.2 (a)より即座に従う。以下では(1)を示す。

\(j_1 > 0\)より\(\textrm{Pred}(M)\)は零項でないので\(\textrm{Trans}\)が零項性を保つことから\(t_1 \neq 0\)である。また\((t_1,c_1) \in T_{\textrm{B}}^{\textrm{Marked}}\)であるので\(c_1 \in PT_{\textrm{B}}\)である。

\(M\)は簡約であるので、簡約性と係数の関係から条件(A)と(B)を満たす。\(M\)の単項性と条件(B)から\(M_{0,0} = M_{1,0}\)である。簡約性が基本列で保たれることから\(M[n]\)も簡約である。

\(j_0\)が\(M\)許容より\(j_{-1} = j_0\)である。\(\textrm{Mark}\)の左端の基本性質より\(v = M_{1,j_{-1}} = M_{1,j_0}\)である。

\(\textrm{Trans}\)の定義より\((s_1,c_2,b_1) = (s_1,D_{M_{1,j_0}}(t_2 + D_0 0), b_1)\)は\(\textrm{Trans}(M)\)の第\(0\)種scb分解である。

\(n = 1\)ならば\(M[n] = \textrm{Pred}(M)\)より\(\textrm{Trans}(M[n]) = t_1 = s_1 c_1 b_1\)である。

\(j_0 = 0\)とする。

非複項性と基本列の関係 (1)より\(P(M[n]) = (\textrm{Pred}(M))_{k=0}^{n-1}\)である。

\(j_0\)は\(M\)許容であるので\(j_{-1} = j_0 = 0\)である。従って\(s_1\)と\(b_1\)の空性と基点の関係より\(s_1 = ()\)かつ\(b_1 = ()\)であり、scb分解と基本列の関係 (1-1)より\(\textrm{Trans}(M)[n-1] = D_{M_{1,j_0}}(t_2 + D_0 0)[n-1] = (D_{M_{1,j_0}} t_2) \times n  = c_1 \times n\)である。

\(\textrm{Trans}(M[n]) = \textrm{Trans}(M)[n-1]\)となることを\(n\)に関する数学的帰納法で示す。

\(n = 1\)ならば\(\textrm{Trans}(M[n]) = s_1 c_1 b_1 =  c_1 = \textrm{Trans}(M)[n-1]\)である。
  @{thm [source] p_6_4_P_leftend_mono}.\<close>
\(n > 1\)ならば、帰納法の仮定より\(\textrm{Trans}(M[n-1]) = \textrm{Trans}(M)[n-2]\)であり、\(\textrm{Lng}(\textrm{Pred}(M)) = j_1 > 1\)より\(\textrm{Pred}(M) \neq (0,0)\)であるので\(\textrm{Trans}\)の再帰的定義より
lemma m_6_4_P_leftend_mono:
\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & \textrm{Trans}(\bigoplus_{\mathbb{N}^2} (\textrm{Pred}(M))_{k=0}^{n-2}) + \textrm{Trans}(\textrm{Pred}(M)) = \textrm{Trans}(M[n-1]) + t_1 = \textrm{Trans}(M)[n-2] + s_1 c_1 b_1 = c_1 \times (n-1) + c_1 \\
& = & c_1 \times n = \textrm{Trans}(M)[n-1]
\end{eqnarray*}

である。

\(j_0 > 0\)とする。

\(M\)が条件(I)を満たすことから、\(j_0\)が\(M\)許容かつ\(M_{1,j_0} \geq 0 = M_{1,j_1}\)である。従って\(M\)は条件(I)か(III)の下での\(c_1\)前後の具体表示の仮定を満たす。

\(M\)が単項であることから\((0,0) \leq_M (0,j_1)\)であるので\(M_{0,0} < M_{0,j_1}\)となり、\(0 < j_0\)であるので親の存在の判定条件 (1)から\((0,j'_0) <_M^{\textrm{Next}} (0,j_0)\)を満たす一意な\(j'_0 \in \mathbb{N}\)が存在する。

条件(I)か(III)の下での\(c_1\)前後の具体表示で導入した記号を用いる。

\((t_1,\textrm{Mark}(\textrm{Pred}(M),j'_{-1})) \in T_{\textrm{B}}^{\textrm{Marked}}\)より、一意な\((s'_{-1},b'_{-1}) \in (\Sigma^{< \omega})^2\)が存在して\((s'_{-1},\textrm{Mark}(\textrm{Pred}(M),j'_{-1}),b'_{-1})\)は\(t_1\)のscb分解をなす。特に\(\textrm{Trans}(\textrm{Pred}(M)) = t_1 = s'_{-1} \textrm{Mark}(\textrm{Pred}(M),j'_{-1}) b'_{-1}\)である。

\(j_{-1} = j_0 > 0\)と\(s_1\)と\(b_1\)の空性と基点の関係とscb分解の自明性の判定条件より、\(s_1 \neq ()\)である。

\(j'_{-1} = j'_0\)または\(M_{1,j'_0}+1 = M_{1,j_0}\)とする。

\(j'_0+1 = j_0\)とする。

\(t'_2 := 0\)と置く。

条件(I)か(III)の下での\(c_1\)前後の具体表示 (3-1)より\(s_1 c_1 b_1 = \textrm{Trans}(\textrm{Pred}(M)) = s'_{-1} \textrm{Mark}(\textrm{Pred}(M),j'_{-1}) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}} c_1 b'_{-1}\)である。従ってscb分解の一意性 (1)より\(s_1 = s'_{-1} D_{M_{1,j'_{-1}}}\)かつ\(b_1 = b'_{-1}\)である。

scb分解と基本列の関係 (1-2)より\(\textrm{Trans}(M)[n-1] = s'_{-1} D_{M_{1,j'_{-1}}}((D_{M_{1,j_0}} t_2) \times n) b_1 = s'_{-1} D_{M_{1,j'_{-1}}}(c_1 \times n) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times n) b'_{-1}\)である。

\(j'_0+1 < j_0\)とする。

条件(I)か(III)の下での\(c_1\)前後の具体表示 (4-1)より一意な\(t'_2 \in T_{\textrm{B}}\)が存在して\(\textrm{Mark}(\textrm{Pred}(M),j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_2+c_1)\)である。

\begin{eqnarray*}
s_1 c_1 b_1 = t_1 = \textrm{Trans}(\textrm{Pred}(M)) = s'_{-1} \textrm{Mark}(\textrm{Pred}(M),j'_{-1}) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}(t'_2+c_1) b'_{-1}
\end{eqnarray*}

であるので、加法とscb分解の関係とscb分解の合成則 (2)を反復して適用することで[54]

    by (rule idxsum_leftend_lmin[OF assms(1) J1L])
\textrm{Trans}(M) = s_1 c_2 b_1 = s'_{-1} D_{M_{1,j'_{-1}}}(t'_2+c_2) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}(t'_2 + D_{M_{1,j_0}}(t_2 + D_0 0)) b'_{-1}
\end{eqnarray*}

となる。従ってscb分解と基本列の関係 (1-2)より\(\textrm{Trans}(M)[n-1] = s'_{-1} D_{M_{1,j'_{-1}}}(t'_2 + (D_{M_{1,j_0}} t_2) \times n) b'_1 = s'_{-1} D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times n) b'_{-1}\)である。

以上より、いずれの場合も\(\textrm{Trans}(M)[n-1] = s'_{-1} D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times n) b'_{-1}\)である。

\(\textrm{Mark}(M[n],j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times n)\)かつ\(\textrm{Trans}(M[n]) = s'_{-1} \textrm{Mark}(M[n],j'_{-1}) b'_{-1}\)となることを\(n\)に関する数学的帰納法で示す。

\(n = 1\)ならば\(\textrm{Mark}(M[n],j'_{-1}) = \textrm{Mark}(\textrm{Pred}(M),j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_2+c_1) = D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times n)\)かつ\(\textrm{Trans}(M[n]) = \textrm{Trans}(\textrm{Pred}(M)) = s'_{-1} \textrm{Mark}(\textrm{Pred}(M),j'_{-1}) b'_{-1} = s'_{-1} \textrm{Mark}(M[n],j'_{-1}) b'_{-1}\)である。

\(n > 1\)とする。

条件(I)か(III)の下での\(c_1\)前後の具体表示 (5)より\(j_1^N = j_0+(n-1)(j_1-j_0)\)かつ\(j_0^N = j'_0\)かつ\(j_{-1}^N = j'_{-1}\)かつ\(t_1^N \neq 0\)であり、\(N\)は条件(VI)を満たさない。

帰納法の仮定より\(c_1^N = \textrm{Mark}(M[n-1],j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times (n-1))\)かつ\(s_1^N c_1^N b_1^N = t_1^N = \textrm{Trans}(M[n-1]) = s'_{-1} \textrm{Mark}(M[n-1],j'_{-1}) b'_{-1} = s'_{-1} c_1^N b'_{-1}\)である。従ってscb分解の一意性 (1)より\(s_1^N = s'_{-1}\)かつ\(b_1^N = b'_{-1}\)である。また\(D_{v^N} t_2^N = c_1^N = D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times (n-1))\)より\(v^N = M_{1,j'_{-1}}\)かつ\(t_2^N = t'_2 + c_1 \times (n-1)\)である。

\(j'_{-1} = j'_0\)ならば\(j_{-1}^N = j'_{-1} = j'_0 = j_0^N\)より\(N\)は条件(I)か(III)を満たす。

\(M_{1,j'_0}+1 = M_{1,j_0}\)ならば、\(N\)が条件(VI)を満たないことと\(N_{1,j_0^N}+1 = M_{1,j'_0}+1 = M_{1,j_0} = N_{1,j_1^N}\)より、\(N\)は条件(V)を満たす。

従っていずれの場合\(N\)は条件(I)か(III)か(V)を満たし、\(c_2^N = D_{v^N}(t_2^N + D_{N_{1,j_1^N}} 0) = D_{M_{1,j'_{-1}}}((t'_2 + c_1 \times (n-1)) + D_{M_{1,j_0}} 0)\)となるので\(\textrm{Trans}(N) = s_1^N c_2^N b_1^N = s'_{-1} D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times (n-1) + D_{M_{1,j_0}} 0) b'_{-1}\)である。

加法とscb分解の関係とscb分解の合成則 (2) より\((D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times (n-1) + D_{M_{1,j_0}} 0),D_{M_{1,j_0}} 0) \in T_{\textrm{B}}^{\textrm{Marked}}\)である。また\(\textrm{Mark}\)の定義より\((\textrm{Trans}(N),D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times (n-1) + D_{M_{1,j_0}} 0)) \in T_{\textrm{B}}^{\textrm{Marked}}\)である。

更にscb分解の合成則 (1)とscb分解の置換可能性を反復して適用することで[55]\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & s'_{-1} D_{M_{1,j'_{-1}}}((t'_2 + c_1 \times (n-1)) + \textrm{Mark}(M[n],j_0+(n-1)(j_1-j_0))) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}((t'_2 + c_1 \times (n-1)) + \textrm{Mark}(\textrm{Pred}(M),j_{-1})) b'_{-1} \\
& = & s'_{-1} D_{M_{1,j'_{-1}}}((c_1 \times (n-1)) + c_1) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times n) b'_{-1}
\end{eqnarray*}

となり、更に\(\textrm{Trans}(N) = s'_{-1} \textrm{Mark}(N,j'_{-1}) b'_{-1}\)より

\begin{eqnarray*}
s'_{-1} \textrm{Mark}(M[n],j'_{-1}) b'_{-1} & = & \textrm{Trans}(M[n]) = s'_{-1} D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times n) b'_{-1}
\end{eqnarray*}

となるので\(\textrm{Mark}(M[n],j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times n)\)かつ\(\textrm{Trans}(M[n]) = s'_{-1} \textrm{Mark}(M[n],j'_{-1}) b'_{-1}\)である。

以上より

\begin{eqnarray*}
\textrm{Trans}(M[n]) = s'_{-1} \textrm{Mark}(M[n],j'_{-1}) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}(t'_2 + c_1 \times n) b'_{-1} = \textrm{Trans}(M)[n-1]
\end{eqnarray*}

である。

\(j'_{-1} < j'_0\)かつ\(M_{1,j'_0} \geq M_{1,j_0}\)とする。

\(j'_0+1 = j_0\)とする。

\(t'_3 := 0\)と置く。

\(t'_4 := 0\)と置く。

条件(I)か(III)の下での\(c_1\)前後の具体表示 (3-2)より\(s_1 c_1 b_1 = \textrm{Trans}(\textrm{Pred}(M)) = s'_{-1} \textrm{Mark}(\textrm{Pred}(M),j'_{-1}) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}} D_{M_{1,j'_0}} c_1 b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4+c_1)) b'_{-1}\)である。従ってscb分解の一意性 (1)より\(s_1 = s'_{-1} D_{M_{1,j'_{-1}}} D_{M_{1,j'_0}}\)かつ\(b_1 = b'_{-1}\)である。

scb分解と基本列の関係 (1-2)より\(\textrm{Trans}(M)[n-1] = s'_{-1} D_{M_{1,j'_{-1}}} D_{M_{1,j'_0}}((D_{M_{1,j_0}} t_2) \times n) b_1 = s'_{-1} D_{M_{1,j'_{-1}}} D_{M_{1,j'_0}}(c_1 \times n) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times n)) b'_{-1}\)である。

\(j'_0+1 < j_0\)とする。

条件(I)か(III)の下での\(c_1\)前後の具体表示 (4-2)より一意な\((t'_3,t'_4) \in T_{\textrm{B}}^2\)が存在して\(\textrm{Mark}(\textrm{Pred}(M),j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4+c_1))\)であり、\(s_1 c_1 b_1 = t_1 = \textrm{Trans}(\textrm{Pred}(M)) = s'_{-1} \textrm{Mark}(\textrm{Pred}(M),j'_{-1}) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4+c_1)) b'_{-1}\)である。

よって加法とscb分解の関係とscb分解の合成則 (2)を反復して適用することで\((D_{M_{1,j'_0}}(t'_4+c_1),c_1), (D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4+c_1)),D_{M_{1,j'_0}}(t'_4+c_1)) \in T_{\textrm{B}}^{\textrm{Marked}}\)が従う。また\(\textrm{Mark}\)の定義より\((s_1 c_1 b_1,D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4+c_1))), (s_1 c_1 b_1,c_1) \in T_{\textrm{B}}^{\textrm{Marked}}\)である。

更にscb分解の合成則 (1)とscb分解の置換可能性を反復して適用することで[56]\(\textrm{Trans}(M) = s_1 c_2 b_1 = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + D_{M_{1,j_0}}(t_2 + D_0 0))) b'_{-1}\)が従う。scb分解と基本列の関係 (1-2)より\(\textrm{Trans}(M)[n-1] = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + (D_{M_{1,j_0}} t_2) \times n)) b'_1 = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times n)) b'_{-1}\)である。

従っていずれの場合も\(\textrm{Mark}(\textrm{Pred}(M),j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4+c_1))\)かつ\(\textrm{Trans}(M)[n-1] = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times n)) b'_{-1}\)である。

\(\textrm{Mark}(M[n],j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times n))\)かつ\(\textrm{Trans}(M[n]) = s'_{-1} \textrm{Mark}(M[n],j'_{-1}) b'_{-1}\)となることを\(n\)に関する数学的帰納法で示す。

\(n = 1\)ならば\(\textrm{Mark}(M[n],j'_{-1}) = \textrm{Mark}(\textrm{Pred}(M),j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1)) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times n))\)かつ\(\textrm{Trans}(M[n]) = \textrm{Trans}(\textrm{Pred}(M)) = s'_{-1} \textrm{Mark}(\textrm{Pred}(M),j'_{-1}) c_1 b'_{-1} = s'_{-1} \textrm{Mark}(M[n],j'_{-1}) b'_{-1}\)である。

\(n > 1\)とする。

条件(I)か(III)の下での\(c_1\)前後の具体表示 (5)より\(j_1^N = j_0+(n-1)(j_1-j_0)\)かつ\(j_0^N = j'_0\)かつ\(j_{-1}^N = j'_{-1}\)かつ\(t_1^N \neq 0\)であり、\(N\)は条件(VI)を満たさない。

帰納法の仮定より\(c_1^N = \textrm{Mark}(M[n-1],j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1)))\)かつ\(s_1^N c_1^N b_1^N = t_1^N = \textrm{Trans}(M[n-1]) = s'_{-1} \textrm{Mark}(M[n-1],j'_{-1}) b'_{-1} = s'_{-1} c_1^N b'_{-1}\)である。従ってscb分解の一意性 (1)より\(s_1^N = s'_{-1}\)かつ\(b_1^N = b'_{-1}\)である。また\(D_{v^N} t_2^N = c_1^N = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1)))\)より\(v^N = M_{1,j'_{-1}}\)かつ\(t_2^N = t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1))\)である。

\(j_{-1}^N = j'_{-1} < j'_0 = j_0^N\)より\(j_0^N\)は非\(N\)許容であるので\(N\)は条件(I)や(III)は満たさず、\(N_{1,j_0^N}+1 = M_{1,j'_0}+1 \geq M_{1,j_0} = N_{1,j_1^N}\)より\(N\)は条件(II)か(IV)を満たす。\(t_2^N\)の最右単項成分\(D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1))\)の左端は\(D_{M_{1,j'_0}} = D_{N_{1,j_0^N}}\)であるので、\(t_3^N = t'_3\)かつ\(D_{N_{1,j_0^N}} t_4^N = t_2^N = D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1))\)すなわち\(t_4^N = t'_4 + c_1 \times (n-1)\)である。

従って\(c_2^N = D_{v^N}(t_3^N + D_{N_{1,j_0^N}}(t_4^N + D_{N_{1,j_1^N}} 0)) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1) + D_{M_{1,j_0}} 0)) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1) + D_{M_{1,j_0}} 0))\)となるので\(\textrm{Trans}(N) = s_1^N c_2^N b_1^N = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 +  D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1) + D_{M_{1,j_0}} 0)) b'_{-1}\)である。

加法とscb分解の関係とscb分解の合成則 (2)を反復して適用することで\((D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1) + D_{M_{1,j_0}} 0),D_{M_{1,j_0}} 0), (D_{M_{1,j'_{-1}}}(t'_3 +  D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1) + D_{M_{1,j_0}} 0)),D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1) + D_{M_{1,j_0}} 0)) \in T_{\textrm{B}}^{\textrm{Marked}}\)が従う。また\(\textrm{Mark}\)の定義より\((\textrm{Trans}(N),D_{M_{1,j'_{-1}}}(t'_3 +  D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1) + D_{M_{1,j_0}} 0))) \in T_{\textrm{B}}^{\textrm{Marked}}\)である。

更にscb分解の合成則 (1)とscb分解の置換可能性を反復して適用することで[57]\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1) + \textrm{Mark}(M[n],j_0+(n-1)(j_1-j_0)))) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1) + \textrm{Mark}(\textrm{Pred}(M),j_{-1}))) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times (n-1) + c_1)) b'_{-1} \\
& = & s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times n)) b'_{-1}
\end{eqnarray*}

となり、更に\(\textrm{Trans}(N) = s'_{-1} \textrm{Mark}(N,j'_{-1}) b'_{-1}\)より

\begin{eqnarray*}
s'_{-1} \textrm{Mark}(M[n],j'_{-1}) b'_{-1} & = & \textrm{Trans}(M[n]) = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times n)) b'_{-1}
\end{eqnarray*}

となるので\(\textrm{Mark}(M[n],j'_{-1}) = D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times n))\)かつ\(\textrm{Trans}(M[n]) = s'_{-1} \textrm{Mark}(M[n],j'_{-1}) b'_{-1}\)である。

以上より

\begin{eqnarray*}
\textrm{Trans}(M[n]) = s'_{-1} \textrm{Mark}(M[n],j'_{-1}) b'_{-1} = s'_{-1} D_{M_{1,j'_{-1}}}(t'_3 + D_{M_{1,j'_0}}(t'_4 + c_1 \times n)) b'_{-1} = \textrm{Trans}(M)[n-1]\end{eqnarray*}

である。□

## 強単項性[]

条件(II)の下での展開規則を調べるために、強単項性という概念を導入する。

\(M \in \textrm{T}_{\textrm{PS}}\)とする。

- \(M\)が強単項であるとは、\(M\)が簡約かつ単項かつ\(\textrm{Br}(M)\)が降順であるということである。

- 強単項ペア数列全体のなす部分集合を\(DT_{\textrm{PS}} \subset T_{\textrm{PS}}\)と置く。

命題（標準形の直系先祖による切片の簡約化の強単項性）

任意の\(M \in ST_{\textrm{PS}}\)と\(j'_0,j'_1 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(j'_0 < j'_1 \leq j_1\)とし\(M' := (M_j)_{j=j'_0}^{j'_1} \)と置くと、\((0,j'_0) \leq_M (0,j'_1)\)ならば\(\textrm{Red}(M')\)は強単項である。

証明：

標準形の切片と\(\textrm{Br}\)の降順性の関係より、\(M'\)は単項かつ\(\textrm{Br}(M')\)は降順である。従って\(\textrm{Red}\)が単項性を保つことより\(\textrm{Red}(M')\)は単項である。

\(J_1 := \textrm{Lng}(\textrm{Br}(\textrm{Red}(M')))-1\)と置く。

直系先祖による切片と\(\textrm{Red}\)と\(\textrm{IncrFirst}\)の関係より\(M' = \textrm{IncrFirst}^{M_{0,j'_0}-M_{1,j'_0}}(\textrm{Red}(M'))\)であるので、\(\leq_M\)の\(\textrm{IncrFirst}\)不変性から\(\textrm{Br}(M') = (\textrm{IncrFirst}^{M_{0,j'_0}-M_{1,j'_0}}(\textrm{Br}(\textrm{Red}(M'))_J))_{J=0}^{J_1}\)である。

従って\(\textrm{Br}(M')\)の降順性から\(\textrm{Br}(\textrm{Red}(M'))\)は降順である。以上より\(\textrm{Red}(M')\)は強単項である。□

写像
\begin{eqnarray*}
\textrm{LastStep} \colon DT_{\textrm{PS}} & \to & \mathbb{N} \\
M & \mapsto & \textrm{LastStep}(M)
\end{eqnarray*}
を以下のように定める：

- \(J_1 := \textrm{Lng}(\textrm{Br}(M))\)と置く。

- \(J_1 = 0\)ならば\(\textrm{LastStep}(M) = 0\)である[58]。

- \(J_1 > 0\)とする[59]。

- \((\textrm{Br}(M)_{J_1})_{0,0} = (\textrm{Br}(M)_{J_1})_{1,0}\)ならば\(\textrm{LastStep}(M) = J_1\)である[60]。

- \((\textrm{Br}(M)_{J_1})_{0,0} > (\textrm{Br}(M)_{J_1})_{1,0}\)ならば\(\textrm{LastStep}(M) := \min \{J \in \mathbb{N} \mid (\textrm{Br}(M)_{J_1})_{0,0} = (\textrm{Br}(M)_J)_{0,0} > (\textrm{Br}(M)_J)_{1,0}\}\)である[61]。

命題（条件(II)か(IV)の下での終切片と\(\textrm{Trans}\)の関係）

任意の\(M \in DT_{\textrm{PS}}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置き、\(J_1 \geq 0\)として\(j'_0 := \textrm{Joints}(M)_{J_1}\)と置き、 \(j'_1 := \textrm{FirstNodes}(M)_{J_1}\)と置き、\(J_0 := \textrm{LastStep}(M)\)と置き、\(m_1 := \textrm{FirstNodes}(M)_{J_0}-1\)と置き、\(N := (M_j)_{j=0}^{m_1}\)と置き、\(N' := (M_j)_{j=j'_0}^{m_1}\)と置き[62]、\(M' := (M_j)_{j=j'_0}^{j_1}\)と置くと、\(0 < j'_0 < \textrm{TrMax}(M)\)かつ\(M_{0,j'_1} > M_{1,j'_1}\)ならば一意な\(t_1,t_2 \in T_{\textrm{B}}\)が存在して以下を満たす：

(1) \(\textrm{Trans}(N) = D_{M_{1,0}} t_1\)である。

(2) \(\textrm{Trans}(N') = D_{M_{1,j'_0}} t_1\)である。

(3) \(\textrm{Trans}(M') = D_{M_{1,j'_0}}(t_1 + t_2)\)かつ\(t_2 \neq 0\)である。

(4) \(\textrm{Trans}(M) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_0}}(t_1 + t_2))\)である。

条件(II)か(IV)の下での終切片と\(\textrm{Trans}\)の関係を証明するための準備としていくつかの補題を示す。

補題（強単項性の切片への遺伝性）

任意の\(M \in DT_{\textrm{PS}}\)と\(j'_0,j'_1 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置き、\(j'_0 < j'_1 \leq j_1\)とし\(M' := (M_j)_{j=j'_0}^{j'_1} \)と置くと、\(j'_0 \leq \textrm{Joints}(M)_{J_1}\)ならば\(M'\)は強単項である。

証明：

簡約性と係数の関係より\(M\)は条件(A)と(B)を満たす。従って任意の\(j \in \mathbb{N}\)に対し\(j \leq \textrm{TrMax}(M)\)ならば\(M_j = (M_{1,0}+j,M_{1,0}+j)\)である。

\(\textrm{FirstNodes}\)と\(\textrm{TrMax}\)と\(\textrm{Joints}\)の関係より\(j'_0 \leq \textrm{Joints}(M)_{J_1} \leq \textrm{TrMax}(M)\)である。従って簡約性の切片への遺伝性から\(M'\)は簡約である。

\(j_0 := \textrm{TrMax}(M)\)と置く。

\(\textrm{TrMax}(M') = j_0-j'_0\)かつ\(\textrm{Lng}(M')-1 = j'_1-j'_0\)である。

任意の\(j \in \mathbb{N}\)に対し、\(j \leq j'_1-j'_0\)ならば\((0,0) \leq_M (0,j)\)となることを示す。

\(j \leq \textrm{TrMax}(M')\)ならば\((1,0) \leq_{M'} (1,j)\)なので\((0,0) \leq_{M'} (0,j)\)である。

\(j > \textrm{TrMax}(M')\)とする。

\(j+j'_0 > \textrm{TrMax}(M')+j'_0 = j_0\)であるので、一意な\(J \in \mathbb{N}\)が存在して\(J \leq J_1\)かつ\(\textrm{FirstNodes}(M)_J \leq j+j'_0 < \textrm{FirstNodes}(M)_{J+1}\)となる。\(P\)の各成分の非複項性より\(\textrm{Br}(M)_J\)は複項でないので、\((0,0) \leq_{\textrm{Br}(M)_J} (0,j+j'_0 - \textrm{FistNodes}(M)_J)\)すなわち\((0,\textrm{FirstNodes}(M)_J) \leq_M (0,j+j'_0)\)である。

\(\textrm{Br}(M)\)の降順性から\(M_{0,\textrm{FirstNodes}(M)_J} \geq M_{0,\textrm{FirstNodes}(M)_{J_1}}\)であり、\(M\)が条件(A)を満たすことから\(M_{0,\textrm{Joints}(M)_J}+1 = M_{0,\textrm{FirstNodes}(M)_J}\)かつ\(M_{0,\textrm{Joints}(M)_{J_1}}+1 = M_{0,\textrm{FirstNodes}(M)_{J_1}}\)である。従って\(j'_0 \leq \textrm{Joints}(M)_{J_1} = M_{0,\textrm{Joints}(M)_{J_1}}-M_{1,0} = M_{0,\textrm{FirstNodes}(M)_{J_1}}-1-M_{1,0} \leq M_{0,\textrm{FirstNodes}(M)_J}-1-M_{1,0} = M_{0,\textrm{Joints}(M)_J}-M_{1,0} = \textrm{Joints}(M)_J\)である。

\(\textrm{FirstNodes}\)と\(\textrm{TrMax}\)と\(\textrm{Joints}\)の関係より\(j'_0 \leq \textrm{Joint}(M)_J \leq \textrm{TrMax}(M)\)であるので\((1,j'_0) \leq_M (1,\textrm{Joints}(M)_J)\)である。更に\((0,\textrm{Joints}(M)_J) <_M^{\textrm{Next}} (0,\textrm{FirstNodes}(M))\)かつ\((0,\textrm{FirstNodes}(M)_J) \leq_M (0,j+j'_0)\)より、\((0,j'_0) \leq_M (0,j+j'_0)\)すなわち\((0,0) \leq_{M'} (0,j)\)である。

以上より\(M'\)は単項である。

\(J_0 := \textrm{Lng}(\textrm{Br}(M'))-1\)と置く。

\(P\)と\(\textrm{IdxSum}\)の合成の特徴付けより、\(J_0 \leq J_1\)かつ\(\textrm{FirstNodes}(M') = (\textrm{FirstNodes}(M)_J-j'_0)_{J=0}^{J_0}\)である。従って\(\textrm{Br}(M')\)は降順である。□

補題（部分表現の単項成分と\(\textrm{Pred}\)の関係）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置き、\(J_1 \geq 0\)として\(j'_0 := \textrm{Joints}(M)_{J_1}\)と置き、\(j'_1 := \textrm{FirstNodes}(M)_{J_1}\)と置くと、\(j_1 > 1\)ならば以下のいずれかが成り立つ：

(1) \(j'_1 = j_1\)であり、\(\textrm{TrMax}(M) = 0\)または\(j'_0 < \textrm{TrMax}(M)\)であり、\(M_{0,j'_1} = M_{1,j'_1}\)または\(j'_0\)が\(M\)許容であり、一意な\(t_1 \in T_{\textrm{B}}\)が存在して\(\textrm{Trans}(\textrm{Pred}(M)) = D_{M_{1,0}} t_1\)かつ\(\textrm{Trans}(M) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_1}} 0)\)である。

(2) \(j'_1 = j_1\)であり、\(M_{0,j'_1} > M_{1,j'_1}\)かつ\(j'_0\)が非\(M\)許容であり、一意な\((t_1,t_2) \in T_{\textrm{B}}^2\)が存在して\(\textrm{Trans}(\textrm{Pred}(M)) = D_{M_{1,0}} t_1\)かつ\(\textrm{Trans}(M) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_0}} t_2)\)である。

(3) 一意な\((t_1,t_2,t_3) \in T_{\textrm{B}}^2\)が存在して\(\textrm{Trans}(\textrm{Pred}(M)) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_1}} t_2)\)かつ\(\textrm{Trans}(M) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_1}} t_3)\)である。

(4) 一意な\((t_1,t_2,t_3) \in T_{\textrm{B}}^2\)が存在して\(\textrm{Trans}(\textrm{Pred}(M)) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_0}} t_2)\)かつ\(\textrm{Trans}(M) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_0}} t_3)\)である。

証明：

簡約性と係数の関係から\(M\)は条件(A)と(B)を満たす。\(M\)が条件(A)と(B)を満たすことから任意の\(j \in \mathbb{N}\)に対し\(j \leq \textrm{TrMax}(M)\)ならば\(M_j = (M_{1,0} + j, M_{1,0} + j)\)である。また\(M\)が条件(A)を満たすことから\(M_{0,j'_0}+1 = M_{0,j'_1}\)である。

\(j_1 > 1\)より\(\textrm{Pred}(M)\)は零項でなく、\(\textrm{Trans}\)が零項性を保つことから\(\textrm{Trans}(\textrm{Pred}(M)) \neq 0\)である。従って\(M\)に対し条件(I)～(VI)が意味を持つ。

\(J_1 \geq 0\)より\(\textrm{TrMax}(M) < j_1\)である。また\(M\)の単項性から\((0,0) \leq_M (0,j_1)\)であり、\(j_1 > 1 > 0\)より\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在する。

<<<MISSING line 3380 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3381 — recover from original.html via tools/make_content.py>>>
\((0,j'_0) <_M^{\textrm{Next}} (0,j'_1) = (0,j_1)\)より\(j_0 = j'_0\)である。また\(\textrm{FirstNodes}\)と\(\textrm{TrMax}\)と\(\textrm{Joints}\)の関係より\(j'_0 \leq \textrm{TrMax}(M)\)である。
<<<MISSING line 3383 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3384 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3385 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3386 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3387 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3388 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3389 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3390 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3391 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3392 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3393 — recover from original.html via tools/make_content.py>>>
\(\textrm{Pred}(M) = (M_{1,0}+j,M_{1,0}+j)_{j=0}^{j'_1-1}\)であり\(j'_1-1 = j_1-1 > 0\)であるので、公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質より\(\textrm{Trans}(\textrm{Pred}(M)) = D_{M_{1,0}} D_{M_{1,j'_1-1}} 0\)である。
<<<MISSING line 3395 — recover from original.html via tools/make_content.py>>>
\(M\)が条件(VI)を満たさないことから、\(M\)は\(\textrm{Pred}\)が公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質 (1)～(4)のいずれかの条件を満たす。
<<<MISSING line 3397 — recover from original.html via tools/make_content.py>>>
\(M\)が\(\textrm{Pred}\)が公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質 (1)の条件を満たすならば、\(j_0+1 = j_1\)となるので\(j'_0 = j_0 = j_1-1 = j'_1-1\)であり、従って\((t_1,t_2,t_3) := (0,0,D_{M_{1,j'_1}} 0)\)と置くと\(\textrm{Trans}(\textrm{Pred}(M)) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_1-1}} t_2) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_0}} t_2)\)かつ\(\textrm{Trans}(M) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_1-1}} t_3) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_0}} t_3)\)となるので、(4)が成り立つ。
<<<MISSING line 3399 — recover from original.html via tools/make_content.py>>>
\(M\)が\(\textrm{Pred}\)が公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質 (2)の条件を満たすならば、\(M_{0,j'_1} = M_{1,j'_1}\)であり、\((t_1,t_2) := (D_{M_{1,j'_1-1}} 0, 0)\)と置くと\(\textrm{Trans}(\textrm{Pred}(M)) = D_{M_{1,0}} t_1\)かつ\(\textrm{Trans}(M) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_1}} t_2)\)となるので、(1)が成り立つ。
<<<MISSING line 3401 — recover from original.html via tools/make_content.py>>>
\(M\)が\(\textrm{Pred}\)が公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質 (3)の条件を満たすならば、\(M_{0,j'_1} > M_{1,j'_1}\)であり、\(j'_0 = M_{0,j'_1}-1-M_{1,0}\)かつ\(M_{1,0}+1 < M_{0,j'_1} \leq M_{0,j'_1-1}\)より\(0 < j'_0 \leq \textrm{TrMax}(M)-1\)となるので\(j'_0\)は非\(M\)許容であり、\((t_1,t_2) := (D_{M_{1,j'_1-1}} 0, \underline{(} D_{M_{1,j'_1-1}} 0 \underline{,} D_{M_{1,j'_0}} 0 \underline{)})\)と置くと\(\textrm{Trans}(\textrm{Pred}(M)) = D_{M_{1,0}} t_1\)かつ\(\textrm{Trans}(M) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_0}} t_2)\)となるので、(2)が成り立つ。
<<<MISSING line 3403 — recover from original.html via tools/make_content.py>>>
\(M\)が\(\textrm{Pred}\)が公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質 (4)の条件を満たすならば、\(j'_0 = M_{0,j'_1}-1-M_{1,0} = 0\)となるので\(j'_0 = 0\)となり\(j'_0\)は\(M\)許容であり、\((t_1,t_2) := (D_{M_{1,j'_1-1}} 0, 0)\)と置くと\(\textrm{Trans}(\textrm{Pred}(M)) = D_{M_{1,0}} t_1\)かつ\(\textrm{Trans}(M) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_1}} t_2)\)となるので、(1)が成り立つ。
<<<MISSING line 3405 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3406 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3407 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3408 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3409 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3410 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3411 — recover from original.html via tools/make_content.py>>>
簡約性の切片への遺伝性と単項性の始切片への遺伝性から\(\textrm{Pred}(M)\)は簡約かつ単項である。\(j_1 \geq j_1 - \textrm{TrMax}(M) > 1\)より\(\textrm{Lng}(\textrm{Pred}(M))-1 = j_1 > 1\)である。
<<<MISSING line 3413 — recover from original.html via tools/make_content.py>>>
\(J'_1 := \textrm{Lng}(\textrm{Br}(\textrm{Pred}(M)))-1\)と置く。
<<<MISSING line 3415 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3416 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3417 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3418 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3419 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3420 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3421 — recover from original.html via tools/make_content.py>>>
\(\textrm{Lng}(\textrm{Pred}(M))-1 = j_1-1\)かつ\(\textrm{TrMax}(\textrm{Pred}(M')) = \textrm{TrMax}(M)\)より\((\textrm{Lng}(\textrm{Pred}(M))-1) - \textrm{TrMax}(\textrm{Pred}(M')) = j_1-1 - \textrm{TrMax}(M) < j_1 - \textrm{TrMax}(M)\)であるので、帰納法の仮定から[63]、一意な\(i \in \{0,1\}\)と\((t_1,t_2) \in T_{\textrm{B}}^2\)が存在して\(\textrm{Trans}(\textrm{Pred}(M)) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_i}} t_2)\)となる。
<<<MISSING line 3423 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3424 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3425 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3426 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3427 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3428 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3429 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3430 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3431 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3432 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3433 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3434 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3435 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3436 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3437 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3438 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3439 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3440 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3441 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3442 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3443 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3444 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3445 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3446 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3447 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3448 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3449 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3450 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3451 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3452 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3453 — recover from original.html via tools/make_content.py>>>
補題（強単項性の下での部分表現の単項成分の基本性質）

任意の\(M \in DT_{\textrm{PS}}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置き、\(J_1 \geq 0\)として\(j'_0 := \textrm{Joints}(M)_{J_1}\)と置き、\(j'_1 := \textrm{FirstNodes}(M)_{J_1}\)と置くと、一意な\(t' \in T_{\textrm{B}}\)が存在して以下を満たす：

(1) \(\textrm{Trans}(M) = D_{M_{1,0}} t'\)である。

(2) \(j'_0 = 0\)または\(M_{0,j'_1} = M_{1,j'_1}\)ならば、\(t'\)の各単項成分は\(D_{M_{1,j'_1}} 0\)以上である。

(3) \(0 < j'_0 < \textrm{TrMax}(M)\)かつ\(M_{0,j'_1} > M_{1,j'_1}\)ならば、\(t'\)の各単項成分は\(D_{M_{1,j'_0}} 0\)以上である。

(4) \(0 < j'_0 = \textrm{TrMax}(M)\)ならば、\(t'\)の各単項成分は\(D_{M_{1,\textrm{TrMax}(M)}} 0\)以上である。

証明：

以下\(\textrm{FirstNodes}\)と\(\textrm{Joints}\)の単調性は断りなく用いる。

\(\textrm{Trans}\)が単項性を保つことから\(\textrm{Trans}(M)\)は単項であり、\(P\)の各成分の非複項性と\(\textrm{Trans}\)の最左単項成分の左端の基本性質より一意な\(t' \in T_{\textrm{B}}\)が存在して\(\textrm{Trans}(M) = D_{M_{1,0}} t'\)である。

\(\textrm{FirstNodes}\)と\(\textrm{TrMax}\)と\(\textrm{Joints}\)の関係より、任意の\(J \in \mathbb{N}\)に対し\(J \leq J_1\)ならば\(\textrm{Joints}(M)_J \leq \textrm{TrMax}(M) < \textrm{FirstNodes}(M)_J\)である。特に\(j'_0 \leq\textrm{TrMax}(M) < j'_1\)である。また\(j_1 \geq j'_1 > j'_0 \geq 0\)より\(j_1 > 0\)である。

\(\textrm{TrMax}\)の定義から\(\textrm{TrMax}(M)\)は\(M\)許容である。従って\((1,\textrm{TrMax}(M)) <_M^{\textrm{Next}} (1,\textrm{TrMax}(M)+1) = (1,\textrm{FirstNodes}(M)_0)\)でなく、すなわち\(M_{1,\textrm{TrMax}(M)} \geq M_{1,\textrm{FirstNodes}(M)_0}\)である。

簡約性と係数の関係から\(M\)は条件(A)と(B)を満たす。\(M\)が条件(A)と(B)を満たすことから任意の\(j \in \mathbb{N}\)に対し\(j \leq \textrm{TrMax}(M)\)ならば\(M_j = (M_{1,0} + j, M_{1,0} + j)\)である。特に\(M_{1,\textrm{TrMax}(M)} = M_{1,0} + \textrm{TrMax}(M) \geq M_{1,0} + j'_0 = M_{1,j'_0}\)である。また\(M\)が条件(A)を満たすことから\(M_{1,j'_0} = M_{0,j'_0} = M_{0,j'_1}-1\)である。

(2)と(3)と(4)が成り立つことを\(j_1 - \textrm{TrMax}(M)\)に関する数学的帰納法で示す。

\(j_1 - \textrm{TrMax}(M) = 1\)とする。

\(\textrm{TrMax}(M) < j'_1 \leq j_1\)より\(j'_1 = j_1\)である。\(\textrm{TrMax}(M)\)の\(M\)許容性から\((1,j'_0) = (1,\textrm{TrMax}(M)) <_M^{\textrm{Next}} (1,\textrm{TrMax}(M)+1) = (1,j_1)\)でないので、\(M_{1,j'_0} \geq M_{1,j'_1}\)である。従って\(M_{0,j'_1} = M_{0,j'_0}+1 = M_{1,j'_0}+1 \geq M_{1,j'_1}+1 > M_{1,j'_1}\)である。

\(j_1 = 1\)とする。

\(\textrm{TrMax}(M) = j_1-1 = 0\)である。\(j'_0 \leq \textrm{TrMax}(M) = 0\)より\(j'_0 = 0 = \textrm{TrMax}(M)\)である。

\(2\)列ペア数列の基本性質より\(t' = D_{M_{1,j_1}} 0\)であり、その唯一の単項成分は\(D_{M_{1,j_1}} 0 = D_{M_{1,j'_1}} 0\)である。

\(j_1 > 1\)とする。

\(j'_0 = 0\)ならば、\(\textrm{Pred}\)が公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質 (4)から\(t' = \underline{(} D_{M_{1,\textrm{TrMax}(M)}} 0 \underline{,} D_{M_{1,j_1}} 0 \underline{)}\)であり、\(D_{M_{1,\textrm{TrMax}(M)}} 0 \geq D_{M_{1,j'_0}} 0 \geq D_{M_{1,j'_1}} 0\)かつ\(D_{M_{1,j_1}} 0 = D_{M_{1,j'_1}} 0\)である。

\(0 < j'_0 < \textrm{TrMax}(M)\)ならば、\(\textrm{TrMax}\)の定義から\(j'_0\)は\(M\)許容でなく、\(\textrm{Pred}\)が公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質 (3)から\(t' = \underline{(} D_{M_{1,\textrm{TrMax}(M)}} 0 \underline{,} D_{M_{0,j'_1}-1} \underline{(} D_{M_{1,\textrm{TrMax}(M)}} 0 \underline{,} D_{M_{1,j_1}} 0 \underline{)} \underline{)}\)であり、\(D_{M_{1,\textrm{TrMax}(M)}} 0 \geq D_{M_{1,j'_0}} 0\)かつ\(D_{M_{0,j'_1}-1} \underline{(} D_{M_{1,\textrm{TrMax}(M)}} 0 \underline{,} D_{M_{1,j_1}} 0 \underline{)} = D_{M_{1,j'_0}} \underline{(} D_{M_{1,\textrm{TrMax}(M)}} 0 \underline{,} D_{M_{1,j_1}} 0 \underline{)} \geq D_{M_{1,j'_0}} 0\)である。

\(0 < j'_0 = \textrm{TrMax}(M)\)ならば、\(\textrm{Pred}\)が公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質 (1)から\(t' = D_{M_{1,\textrm{TrMax}(M)}} D_{M_{1,j_1}} 0\)である。

\(j_1 - \textrm{TrMax}(M) > 1\)とする。

簡約性の切片への遺伝性と単項性の始切片への遺伝性から\(\textrm{Pred}(M)\)は簡約かつ単項である。\(j_1 \geq j_1 - \textrm{TrMax}(M) > 1\)より\(\textrm{Lng}(\textrm{Pred}(M))-1 = j_1 > 1\)である。

\(J'_1 := \textrm{Lng}(\textrm{Br}(\textrm{Pred}(M)))-1\)と置く。

\(j'_1 = j_1\)ならば、\(j_1 - \textrm{TrMax}(M) > 1\)より\(J_1 > 0\)であり、\(P\)と\(\textrm{IdxSum}\)の合成の特徴付けから、\(J'_1 = J_1-1 \geq 0\)である。

\(j'_1 < j_1\)ならば、\(P\)と\(\textrm{IdxSum}\)の合成の特徴付けから、\(J'_1 = J_1 \geq 0\)である。

以上よりいずれの場合も\(\textrm{Lng}(J'_1) \geq 0\)である。

\(\textrm{Lng}(\textrm{Pred}(M))-1 = j_1-1\)かつ\(\textrm{TrMax}(\textrm{Pred}(M')) = \textrm{TrMax}(M)\)より\((\textrm{Lng}(\textrm{Pred}(M))-1) - \textrm{TrMax}(\textrm{Pred}(M')) = j_1-1 - \textrm{TrMax}(M) < j_1 - \textrm{TrMax}(M)\)であるので、帰納法の仮定から[64]、一意な\(t \in T_{\textrm{B}}\)が存在して以下を満たす[65]：

(1) \(\textrm{Trans}(\textrm{Pred}(M)) = D_{M_{1,0}} t\)である。

(2) \(\textrm{Joints}(M)_{J'_1} = 0\)または\(M_{0,\textrm{FirstNodes}(M)_{J'_1}} = M_{1,\textrm{FirstNodes}(M)_{J'_1}}\)ならば、\(t\)の各単項成分は\(D_{M_{1,\textrm{FirstNodes}(M)_{J'_1}}} 0\)以上である。

(3) \(0 < \textrm{Joints}(M)_{J'_1} < \textrm{TrMax}(M)\)かつ\(M_{0,\textrm{FirstNodes}(M)_{J'_1}} > M_{1,\textrm{FirstNodes}(M)_{J'_1}}\)ならば、\(t\)の各単項成分は\(D_{M_{1,\textrm{Joints}(M)_{J'_1}}} 0\)以上である。

(4) \(0 < \textrm{Joints}(M)_{J'_1} = \textrm{TrMax}(M)\)ならば、\(t\)の各単項成分は\(D_{M_{1,\textrm{TrMax}(M)_{J'_1}}} 0\)以上である。

\(\textrm{Joints}(M)_{J'_1} = M_{0,\textrm{Joints}(M)_{J'_1}}-M_{1,0} = M_{0,\textrm{FirstNodes}(M)_{J'_1}}-1-M_{1,0} \geq M_{0,j'_1}-1-M_{1,0} = M_{0,j'_0}-M_{1,0} = j'_0\)である。また簡約性と係数の基本性質から\(M_{0,j'_1} \geq M_{1,j'_1}\)である。

\(j'_0 = 0\)または\(M_{0,j'_1} = M_{1,j'_1}\)とする。

(2) \(\textrm{Joints}(M)_{J'_1} = 0\)または\(M_{0,\textrm{FirstNodes}(M)_{J'_1}} = M_{1,\textrm{FirstNodes}(M)_{J'_1}}\)とする。

\(t\)の各単項成分は\(D_{M_{1,\textrm{FirstNodes}(M)_{J'_1}}} 0\)以上である。

\(\textrm{Joints}(M)_{J'_1} = 0\)とする。

\(j'_1 \leq \textrm{Joints}(M)_{J'_1} = 0\)より\(j'_0 = 0 = \textrm{Joints}(M)_{J'_1}\)である。

\(M_{0,\textrm{FirstNodes}(M)_{J'_1}} = M_{0,\textrm{Joints}(M)_{J'_1}}+1 = M_{0,j'_0}+1 = M_{0,j'_1}\)であるので、\(M\)の強許容性から\(M_{1,\textrm{FirstNodes}(M)_{J'_1}} \geq M_{1,j'_1}\)である。

\(M_{0,\textrm{FirstNodes}(M)_{J'_1}} = M_{1,\textrm{FirstNodes}(M)_{J'_1}}\)ならば、\(M_{1,\textrm{FirstNodes}(M)_{J'_1}} \geq M_{0,\textrm{FirstNodes}(M)_{J'_1}} \geq M_{0,j'_1} \geq M_{1,j'_1}\)である。

以上より、いずれの場合も\(M_{1,\textrm{FirstNodes}(M)_{J'_1}} \geq M_{1,j'_1}\)である。

\(M_{0,\textrm{FirstNodes}(M)_{J'_1}} = M_{1,\textrm{FirstNodes}(M)_{J'_1}}\)ならば、\(P\)の定義から\(M_{1,\textrm{FirstNodes}(M)_{J'_1}} = M_{0,\textrm{FirstNodes}(M)_{J'_1}} \geq M_{0,j'_1} \geq M_{1,J'_1}\)である。

以上より、いずれの場合も\(t\)の各単項成分は\(D_{M_{1,j'_1}} 0\)以上である。

(3) \(0 < \textrm{Joints}(M)_{J'_1} < \textrm{TrMax}(M)\)かつ\(M_{0,\textrm{FirstNodes}(M)_{J'_1}} > M_{1,\textrm{FirstNodes}(M)_{J'_1}}\)ならば、\(t\)の各単項成分は\(D_{M_{0,\textrm{Joints}(M)_{J'_1}}} 0\)以上であり、\(M_{0,\textrm{FirstNodes}(M)_{J'_1}} \geq M_{0,j'_1} \geq M_{1,j'_1}\)であるので、\(t\)の各単項成分は\(D_{M_{1,j'_1}} 0\)以上である。

(4) \(0 < \textrm{Joints}(M)_{J'_1} = \textrm{TrMax}(M)\)とする。
<<<MISSING line 3545 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3546 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3547 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3548 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3549 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3550 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3551 — recover from original.html via tools/make_content.py>>>
\(M_{0,j'_1} \leq M_{0,\textrm{FirstNodes}(M)_0} = M_{0,\textrm{Joints}(M)_0}+1 \leq M_{0,\textrm{TrMax}(M)}+1 = M_{0,j'_1}\)より\(M_{0,\textrm{FirstNodes}(M)_0} = M_{0,\textrm{TrMax}(M)}+1 = M_{0,j'_1}\)であり、\(M\)の強許容性から\(M_{1,\textrm{FirstNodes}(M)_0} \geq M_{1,j'_1} = M_{1,\textrm{TrMax}(M)}+1\)である。
<<<MISSING line 3553 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3554 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3555 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3556 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3557 — recover from original.html via tools/make_content.py>>>
\(M_{1,\textrm{TrMax}(M)} = M_{0,\textrm{TrMax}(M)} \geq M_{0,j'_0}+1 = M_{0,j'_1} \geq M_{1,j'_1}\)となるので、\(t\)の各単項成分は\(D_{M_{1,j'_1}} 0\)以上である。
<<<MISSING line 3559 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3560 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3561 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3562 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3563 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3564 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3565 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3566 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3567 — recover from original.html via tools/make_content.py>>>
\(\textrm{Joints}(M)_{J'_1} \geq j'_0 > 0\)である。
<<<MISSING line 3569 — recover from original.html via tools/make_content.py>>>
(2) \(M_{0,\textrm{FirstNodes}(\textrm{Pred}(M))_{J'_1}} = M_{1,\textrm{FirstNodes}(M)_{J'_1}}\)ならば、\(t\)の各単項成分は\(D_{M_{1,\textrm{FirstNodes}(M)_{J'_1}}} 0\)以上であり、\(P\)の定義から\(M_{1,\textrm{FirstNodes}(M)_{J'_1}} = M_{0,\textrm{FirstNodes}(M)_{J'_1}} \geq M_{0,j'_0} = M_{1,j'_0}\)であるので、\(t\)の各単項成分は\(D_{M_{1,j'_0}} 0\)以上である。
<<<MISSING line 3571 — recover from original.html via tools/make_content.py>>>
(3) \(0 < \textrm{Joints}(M)_{J'_1} < \textrm{TrMax}(M)\)かつ\(M_{0,\textrm{FirstNodes}(M)_{J'_1}} > M_{1,\textrm{FirstNodes}(M)_{J'_1}}\)とする。
<<<MISSING line 3573 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3574 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3575 — recover from original.html via tools/make_content.py>>>
\(j'_0 = \textrm{Joints}(M)_{J'_1}\)ならば\(M\)の強許容性から\(M_{1,\textrm{Joints}(M)_{J'_1}} \geq M_{1,j'_0}\)である。
<<<MISSING line 3577 — recover from original.html via tools/make_content.py>>>
\(j'_0 < \textrm{Joints}(M)_{J'_1}\)ならば簡約性と係数の基本性質から\(M_{1,\textrm{Joints}(M)_{J'_1}} = M_{0,\textrm{Joints}(M)_{J'_1}} > M_{0,j'_0} = M_{1,j'_0}\)である。
<<<MISSING line 3579 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3580 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3581 — recover from original.html via tools/make_content.py>>>
(4) \(0 < \textrm{Joints}(M)_{J'_1} = \textrm{TrMax}(M)\)ならば、\(t\)の各単項成分は\(D_{M_{1,\textrm{TrMax}(M)}} 0\)以上であり、\(M_{1,\textrm{TrMax}(M)} = M_{0,\textrm{TrMax}(M)} > M_{0,j'_0} = M_{1,j'_0}\)であるので、\(t\)の各単項成分は\(D_{M_{1,j'_0}} 0\)以上である。
<<<MISSING line 3583 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3584 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3585 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3586 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3587 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3588 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3589 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3590 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3591 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3592 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3593 — recover from original.html via tools/make_content.py>>>
(4) \(0 < \textrm{Joints}(M)_{J'_1} = \textrm{TrMax}(M)\)であるので、\(t\)の各単項成分は\(D_{M_{1,\textrm{TrMax}(M)}} 0\)以上であり、\(M_{1,\textrm{TrMax}(M)} = M_{1,j'_0}\)である。
<<<MISSING line 3595 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3596 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3597 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3598 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3599 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3600 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3601 — recover from original.html via tools/make_content.py>>>
補題（条件(V)の下での右端の親の基本性質）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(m \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置き、\(J_1 \geq 0\)として\(j'_0 := \textrm{Joints}(M)_{J_1}\)と置き、\(j'_1 := \textrm{FirstNodes}(M)_{J_1}\)と置き、\(M' := (M_j)_{j=m}^{j_1}\)と置くと、「\(m < j'_0\)」または「\(m = j'_0\)かつ\(M_{0,j'_1} = M_{1,j'_1}\)かつ\(\textrm{Br}(M)\)が降順」ならば、一意な\(j_0 \in \mathbb{N}\)が存在して以下を満たす：

  @{thm [source] p_6_4_mono_slice_next}.\<close>

(2) \(j'_0 \leq j_0\)である。

(3) \(m < j_0\)または\(M_{0,j_1} = M_{1,j_1}\)である。

(4) \(m = j_0\)ならば\(j_0 < \textrm{TrMax}(M)\)である。

証明：

\(j'_1 = j_1\)とする。

\(j_0 := j'_0\)と置く。

\(m < j'_0\)ならば、\(m < j'_0 = j_0\)である。

\(m = j'_0\)ならば、仮定より\(M_{0,j_1} = M_{0,j'_1} = M_{0,j'_0}+1 = M_{1,j'_0}+1 = M_{1,j'_1} = M_{1,j_1}\)である。

以上より、いずれの場合も\(m < j_0\)または\(M_{0,j_1} = M_{1,j_1}\)である。

\(j'_1 < j_1\)とする。

\(P\)の各成分の非複項性より\(\textrm{Br}(M)_{J_1}\)は複項でないので\((0,0) \leq_{\textrm{Br}(M)_{J_1}} (0,j_1-j'_1)\)すなわち\((0,j'_1) \leq_M (0,j_1)\)である。\(j'_1 < j_1\)より一意な\(j_0 \in \mathbb{N}\)が存在して\(j'_1 \leq j_0\)かつ\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)すなわち\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)である。

\(m \leq j'_0 < j'_1 \leq j_0\)であるので、\(j'_0 < j_0\)かつ\(m < j_0\)である。

\(m \leq j_0\)かつ\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)より、\((0,j_0-m) <_{M'}^{\textrm{Next}} (0,j_1-m)\)である。

\(\textrm{TrMax}(M)+1 = \textrm{FirstNodes}(M)_0\)であり、\(\textrm{TrMax}\)の定義より\((1,\textrm{TrMax}(M)) <_M^{\textrm{Next}} (1,\textrm{FirstNodes}(M)_0)\)でない。

\(m = j_0\)ならば\(j_0 < \textrm{TrMax}(M)\)であることを示す。

\(m < j_0\)または\(M_{0,j_1} = M_{1,j_1}\)であるので、\(m = j_0\)より\(M_{0,j_1} = M_{1,j_1}\)である。

簡約性と係数の基本性質より\(M_{1,j_0} \leq M_{0,j_0} = M_{0,j_1}-1 = M_{1,j_1}-1 < M_{1,j_1}\)である。

\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)かつ\(M_{1,j_0} < M_{1,j_1}\)より\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)となる。

\(m \leq j'_0 \leq j_0\)より\(m = j'_0\)である。従って\(M_{0,j'_1} = M_{1,j'_1}\)かつ\(\textrm{Br}(M)\)が降順である。

\((1,\textrm{TrMax}(M)) <_M^{\textrm{Next}} (1,\textrm{FirstNodes}(M)_0)\)でないので、\(M_{0,\textrm{TrMax}(M)} \geq M_{0,\textrm{FirstNodes}(M)_0}\)または\(M_{1,\textrm{TrMax}(M)} \geq M_{1,\textrm{FirstNodes}(M)_0}\)である。

\(M_{0,\textrm{TrMax}(M)} \geq M_{0,\textrm{FirstNodes}(M)_0}\)とする。

\(P\)の各成分の左端の単調性より\(M_{0,\textrm{TrMax}(M)} \geq M_{0,\textrm{FirstNodes}(M)_0} \geq M_{0,j'_1}\)であるので、\((0,\textrm{TrMax}(M)) \leq_M (0,j'_1)\)でなく、従って\(j'_0 < \textrm{TrMax}(M)\)である。

\(M_{0,\textrm{TrMax}(M)} = M_{0,\textrm{FirstNodes}(M)_0}\)かつ\(M_{1,\textrm{TrMax}(M)} \geq M_{1,\textrm{FirstNodes}(M)_0}\)とする。

\(\textrm{Br}(M)\)の降順性から、\(M_{0,\textrm{FirstNodes}(M)_0} > M_{0,j'_1}\)または\(M_{1,\textrm{FirstNodes}(M)_0} \geq M_{1,j'_1}\)である。

\(M_{0,\textrm{FirstNodes}(M)_0} > M_{0,j'_1}\)ならば\(M_{0,\textrm{TrMax}(M)} = M_{0,\textrm{FirstNodes}(M)_0} > M_{0,j'_1}\)であるので\((0,\textrm{TrMax}(M)) \leq_M (0,j'_1)\)でなく、従って\(j'_0 < \textrm{TrMax}(M)\)である。

\(M_{1,\textrm{FirstNodes}(M)_0} \geq M_{1,j'_1}\)ならば\(M_{1,\textrm{TrMax}(M)} \geq M_{1,\textrm{FirstNodes}(M)_0} \geq M_{1,j'_1}\)であるので\((1,\textrm{TrMax}(M)) \leq_M (1,j'_1)\)でなく、従って\(j'_0 < \textrm{TrMax}(M)\)である。

以上より、いずれの場合も\(j'_0 < \textrm{TrMax}(M)\)である。

以上より、いずれの場合も\(j_0 = j'_0 < \textrm{TrMax}(M)\)である。□

補題（条件(V)の下での終切片と\(\textrm{Trans}\)の関係）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(m \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置き、\(J_1 \geq 0\)として\(j'_0 := \textrm{Joints}(M)_{J_1}\)と置き、\(j'_1 := \textrm{FirstNodes}(M)_{J_1}\)と置き、\(M' := (M_j)_{j=m}^{j_1}\)と置くと、「\(m < j'_0\)」または「\(m = j'_0\)かつ\(M_{0,j'_1} = M_{1,j'_1}\)かつ\(\textrm{Br}(M)\)が降順」ならば、一意な\(t_1 \in T_{\textrm{B}}\)が存在して以下を満たす：

(1) \(\textrm{Trans}(M) = D_{M_{1,0}} t_1\)である。

(2) \(\textrm{Trans}(M') = D_{M_{1,m}} t_1\)である。

証明：

以下\(\textrm{FirstNodes}\)と\(\textrm{Joints}\)の単調性は断りなく用いる。

簡約性の切片への遺伝性と単項性の切片への遺伝性より\(M'\)は簡約かつ単項であり、\(\textrm{Trans}\)が単項性を保つことから\(\textrm{Trans}(M)\)と\(\textrm{Trans}(M')\)は単項である。

\(\textrm{Trans}\)の最左単項成分の左端の基本性質から一意な\(t_1 \in T_{\textrm{PS}}\)が存在して\(\textrm{Trans}(M) = D_{M_{1,0}} t_1\)となる。
<<<MISSING line 3679 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3680 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3681 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3682 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3683 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3684 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3685 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3686 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3687 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3688 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3689 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3690 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3691 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3692 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3693 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3694 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3695 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3696 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3697 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3698 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3699 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3700 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3701 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3702 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3703 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3704 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3705 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3706 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3707 — recover from original.html via tools/make_content.py>>>
簡約性と係数の基本性質より\(M_{1,j_0} \leq M_{0,j_0} = M_{0,j_1}-1 = M_{1,j_1}-1 < M_{1,j_1}\)より\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)となり、\((1,\textrm{TrMax}(M)) <_M^{\textrm{Next}} (1,j_1)\)でないので\(j_0 < \textrm{TrMax}(M)\)である。
<<<MISSING line 3709 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3710 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3711 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3712 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3713 — recover from original.html via tools/make_content.py>>>
  @{thm [source] p_6_4_FirstNodes_TrMax_Joints} (statement rendered with
<<<MISSING line 3715 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3716 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3717 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3718 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3719 — recover from original.html via tools/make_content.py>>>
\(j_1^M \geq j_1^{M'} = j_1-m > \textrm{TrMax}(M)+1-m \geq 1\)より\(\textrm{Pred}(M)\)と\(\textrm{Pred}(M')\)はいずれも零項でなく、\(\textrm{Trans}\)が零項性を保つことから\(t_1^M = \textrm{Trans}(\textrm{Pred}(M)) \neq 0\)かつ\(t_1^{M'} = \textrm{Trans}(\textrm{Pred}(M')) \neq 0\)である。従って\(M\)と\(M'\)に対し条件(I)～(VI)が意味を持つ。
<<<MISSING line 3721 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3722 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3723 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3724 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3725 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3726 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3727 — recover from original.html via tools/make_content.py>>>
\(J_0 := \textrm{Lng}(\textrm{Br}(\textrm{Pred}(M)))\)と置く。
<<<MISSING line 3729 — recover from original.html via tools/make_content.py>>>
簡約性の切片への遺伝性と単項性の始切片への遺伝性より\(\textrm{Pred}(M)\)は簡約かつ単項である。
<<<MISSING line 3731 — recover from original.html via tools/make_content.py>>>
\(\textrm{TrMax}(M) < j_1-1 = j'_1-1\)から\(\textrm{Lng}(\textrm{Pred}(M))-1 = j_1-1 > \textrm{TrMax}(M) = \textrm{TrMax}(\textrm{Pred}(M))\)であるので\(J_0 \geq 0\)である。
<<<MISSING line 3733 — recover from original.html via tools/make_content.py>>>
\(j'_1 = j_1\)ならば、\(\textrm{Br}(\textrm{Pred}(M)) = (\textrm{Br}(M)_J)_{J=0}^{J_1-1}\)であり、特に\(J_0 = J_1-1\)である。
<<<MISSING line 3735 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3736 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3737 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3738 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3739 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3740 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3741 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3742 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3743 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3744 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3745 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3746 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3747 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3748 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3749 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3750 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3751 — recover from original.html via tools/make_content.py>>>
\(M\)が条件(A)を満たすことから\(M_{0,\textrm{FristNodes}(M)_{J_0}} = M_{0,\textrm{Joints}(M)_{J_0}}+1 = M_{0,j'_0}+1 = M_{0,j'_1}\)である。従って\(\textrm{Br}(M)\)の降順性から\(M_{0,\textrm{FirstNodes}(M)_{J_0}} \leq M_{0,j'_1} = M_{1,j'_1} \leq M_{1,\textrm{FirstNodes}(M)_{J_0}}\)である。一方で簡約性と係数の基本性質より\(M_{0,\textrm{FirstNodes}(M)_{J_0}} \geq M_{1,\textrm{FirstNodes}(M)_{J_0}}\)である。
<<<MISSING line 3753 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3754 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3755 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3756 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3757 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3758 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3759 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3760 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3761 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3762 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3763 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3764 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3765 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3766 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3767 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3768 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3769 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3770 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3771 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3772 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3773 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3774 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3775 — recover from original.html via tools/make_content.py>>>
以下\(\textrm{FirstNodes}\)と\(\textrm{Joints}\)の単調性は断りなく用いる。
<<<MISSING line 3777 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3778 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3779 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3780 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3781 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3782 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3783 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3784 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3785 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3786 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3787 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3788 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3789 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3790 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3791 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3792 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3793 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3794 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3795 — recover from original.html via tools/make_content.py>>>
\(\textrm{TrMax}(M) > j'_0\)より\(M_{1,\textrm{TrMax}(M)} > M_{1,j'_0}\)であるので、\(t_1 = D_{M_{1,\textrm{TrMax}(M)}} 0\)の唯一の単項成分\(D_{M_{1,\textrm{TrMax}(M)}} 0\)は\(D_{M_{1,j'_0}+1} 0\)以上である。
<<<MISSING line 3797 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3798 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3799 — recover from original.html via tools/make_content.py>>>
\(J_0 > 0\)であり、\(\textrm{Joints}(M)_{J_0-1} \geq j'_0 > 0\)と\(N\)が強許容であることから、強単項性の下での部分表現の単項成分の基本性質より以下が成り立つ[67]：
<<<MISSING line 3801 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3802 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3803 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3804 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3805 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3806 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3807 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3808 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3809 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3810 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3811 — recover from original.html via tools/make_content.py>>>
簡約性と係数の基本性質より\(M_{1,\textrm{FirstNodes}(M)_{J_0-1}} = M_{0,\textrm{FirstNodes}(M)_{J_0-1}} \geq M_{0,j'_1} = M_{0,j'_0}+1\)であるので\(t_1\)の各単項成分は\(D_{M_{1,j'_0}+1} 0\)以上である。
<<<MISSING line 3813 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3814 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3815 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3816 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3817 — recover from original.html via tools/make_content.py>>>
\(\textrm{LastStep}\)の定義から、\(M_{0,\textrm{FirstNodes}(M)_{J_0-1}} > M_{1,\textrm{FirstNodes}(M)_{J_0-1}}\)より\(M_{0,\textrm{FirstNodes}(M)_{J_0-1}} > M_{0,j'_1}\)である。従って\(M_{1,\textrm{Joints}(M)_{J_0-1}} = M_{0,\textrm{Joints}(M)_{J_0-1}} = M_{0,\textrm{FirstNodes}(M)_{J_0-1}}-1 \geq M_{0,j'_1} = M_{0,j'_0}+1\)であるので\(t_1\)の各単項成分は\(D_{M_{1,j'_0}+1} 0\)以上である。
<<<MISSING line 3819 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3820 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3821 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3822 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3823 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3824 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3825 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3826 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3827 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3828 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3829 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3830 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3831 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3832 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3833 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3834 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3835 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3836 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3837 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3838 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3839 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3840 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3841 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3842 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3843 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3844 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3845 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3846 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3847 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3848 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3849 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3850 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3851 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3852 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3853 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3854 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3855 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3856 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3857 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3858 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3859 — recover from original.html via tools/make_content.py>>>
\(j_1^M = j_1 = j'_1\)である。\((0,j'_0) <_M^{\textrm{Next}} (0,j'_1) = (0,j_1^M)\)より\(j_0^M = j'_0\)であり、更に\(0 < j'_0 < \textrm{TrMax}(M)\)より\(\textrm{TrMax}\)の定義から\(j_0^M\)は非\(M\)許容かつ\(j_{-1}^M = 0\)となる。また\(M_{0,j'_1} > M_{1,j'_1}\)から\(M_{1,j_0^M} = M_{1,j'_0} = M_{0,j'_0} = M_{0,j'_1}-1 \geq M_{1,j'_1} = M_{1,j_1^M}\)である。
<<<MISSING line 3861 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3862 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3863 — recover from original.html via tools/make_content.py>>>
\(j_1^{M'} = j_1-j'_0 = j'_1-j'_0\)かつ\(j_0^{M'} = j_0^M-j'_0 = 0\)である。従って\(j_0^{M'}\)は\(M'\)許容かつ\(j_{-1}^{M'} = j_0^{M'} = 0\)となる。また\(M_{0,j'_1} > M_{1,j'_1}\)から\(M'_{1,j_0^{M'}} = M'_{1,0} = M_{1,j'_0} = M_{0,j'_0} = M_{0,j'_1}-1 \geq M_{1,j'_1} = M_{1,j_1} = M'_{1,j'_1-j'_0} = M'_{1,j_1^{M'}}\)である。
<<<MISSING line 3865 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3866 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3867 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3868 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3869 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3870 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3871 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3872 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3873 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3874 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3875 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3876 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3877 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3878 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3879 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3880 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3881 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3882 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3883 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3884 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3885 — recover from original.html via tools/make_content.py>>>
強単項性の切片への遺伝性より\(M'\)は強許容であり、\(\textrm{Lng}(M')-1 = m_1 \geq \textrm{TrMax}(M) > j'_0 > 0\)より\(\textrm{Lng}(M')-1 > 1\)であるので、\(M'\)に対し部分表現の単項成分と\(\textrm{Pred}\)の関係 (1)～(4)のいずれかが成り立つ。
<<<MISSING line 3887 — recover from original.html via tools/make_content.py>>>
\(\textrm{Joints}(M')_{J_1} = \textrm{Joints}(M)_{J_1}-j'_0 = 0\)であるので\(\textrm{Joints}(M')_{J_1}\)は\(M'\)許容であり、従って\(M'\)に対し部分表現の単項成分と\(\textrm{Pred}\)の関係 (2)は成り立たない。
<<<MISSING line 3889 — recover from original.html via tools/make_content.py>>>
\(M_{0,j'_0}+1 > M_{0,j'_0} \geq M_{1,j'_0}\)かつ\(M_{0,j'_0}+1 = M_{0,j'_1} > M_{1,j'_1}\)であるので、\(t_1\)の各単項成分が\(D_{M_{0,j'_0}+1} 0\)以上かつ\(\textrm{Trans}(\textrm{Pred}(M')) = D_{M_{1,j'_0}} t_1\)であることから、\(M'\)に対し部分表現の単項成分と\(\textrm{Pred}\)の関係 (3)と(4)はいずれも成り立たない。
<<<MISSING line 3891 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3892 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3893 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3894 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3895 — recover from original.html via tools/make_content.py>>>
\(D_{v^M} t_2^M = t_1^M = \textrm{Trans}(\textrm{Pred}(M)) = \textrm{Trans}(N) = D_{M_{1,0}} t_1\)より\(v^M = M_{1,0}\)かつ\(t_2^M = t_1\)となる。\(M_{1,j_0^M} = M_{1,j'_0} = M_{0,j'_0}\)であり\(t_2^M = t_1\)の各単項成分が\(D_{M_{0,j'_0}+1}\)以上であることから、\(t_2^M\)の最右単項成分の左端は\(D_{M_{1,j_0^M}}\)でない。従って\(t_3^M = t_2^M = t_1\)かつ\(t_4^M = t_2^M = t_1\)である。
<<<MISSING line 3897 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3898 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3899 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3900 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3901 — recover from original.html via tools/make_content.py>>>
強単項性の切片への遺伝性より\(\textrm{Pred}(M)\)は強単項である。
<<<MISSING line 3903 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3904 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3905 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3906 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3907 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3908 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3909 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3910 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3911 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3912 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3913 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3914 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3915 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3916 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3917 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3918 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3919 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3920 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3921 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3922 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3923 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3924 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3925 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3926 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3927 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3928 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3929 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3930 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3931 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3932 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3933 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3934 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3935 — recover from original.html via tools/make_content.py>>>
\(D_{v^M} t_2^M = t_1^M = D_{M_{1,0}}(t_1 + D_{M_{1,j'_0}}(t_1 + t'_2))\)より\(v^M = M_{1,0}\)かつ\(t_2^M = t_1 + D_{M_{1,j'_0}}(t_1 + t'_2)\)であり、\(t_2^M\)の最右単項成分\(D_{M_{1,j'_0}}(t_1 + t'_2)\)の左端は\(D_{M_{1,j'_0}} = D_{M_{1,j_0^M}}\)となる。従って\(t_3^M = t_1\)かつ\(t_4^M = t_1 + t'_2\)かつ\(c_2^M = D_{v^M}(t_3^M + D_{M_{1,j_0^M}}(t_4^M + D_{M_{1,j_1^M}} 0)) = D_{M_{1,0}}(t_1 + D_{M_{1,j'_0}}(t_1 + t'_2 + D_{M_{1,j_1}} 0))\)である。
<<<MISSING line 3937 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3938 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3939 — recover from original.html via tools/make_content.py>>>
\(D_{v^{M'}} t_2^{M'} = t_1^{M'} = D_{M_{1,j'_0}}(t_1 + t'_2)\)より\(v^{M'} = M_{1,j'_0}\)かつ\(t_2^{M'} = t_1 + t'_2\)であり、\(t_2^{M'}\)の最右単項成分\(D_{M_{1,j'_0}}(t_1 + t'_2)\)の左端は\(D_{M_{1,j'_0}} = D_{M_{1,j_0^M}}\)となる。従って\(c_2^{M'} = D_{v^{M'}}(t_2^{M'} + D_{M'_{1,j_1^{M'}}} 0) = D_{M_{1,j'_0}}(t_1 + t'_2 + D_{M_{1,j_1}} 0)\)である。
<<<MISSING line 3941 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3942 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3943 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3944 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3945 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3946 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3947 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3948 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3949 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3950 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3951 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3952 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3953 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3954 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 3955 — recover from original.html via tools/make_content.py>>>
## 条件(II)の下での展開規則[]

命題（条件(II)の下での\(\textrm{Trans}\)と基本列の交換関係）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\(L := \textrm{Red}((M_j)_{j=j_{-1}}^{j_1})\)と置くと、\(j_1 > 1\)かつ\(M\)が条件(II)を満たすならば[71]、\(P(t_2)_{J_1}\)の左端が\(D_{M_{1,j_0}}\)であるか否かに従って\(m_n := n-1\)または\(m_n := n-2\)と置くと、以下が成り立つ：

(1) \(m_n = -1\)ならば\(\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}} t_2 b_1\)である。

(2) \(m_n \geq 0\)ならば\(\textrm{Trans}(M[n]) = \textrm{Trans}(M)[m_n]\)である。

(3) \(\textrm{Mark}(M[n],j_{-1}) = D_{M_{1,j_{-1}}} (t_3 + (D_{M_{1,j_0}} t_4) \times (m_n+1))\)である。

(4) \(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

条件(II)の下での\(\textrm{Trans}\)と基本列の交換関係を証明するための準備としていくつかの補題を示す。

補題（第\(0\)種型基本列の基本不等式）

任意の\(M in T_{\textrm{PS}}\)と\(n,r' \in \mathbb{N}_{+}\)と\(q,q' \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置くと、\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在し\(M_{1,j_1} = 0\)かつ\(q,q' \leq n-1\)かつ\(r' \in j_1-j_0\)ならば、\(M[n]_{0,j_0+q(j_1-j_0)} < M[n]_{0,q'(j_1-j_0)+r'}\)である。

証明：

\(M_{1,j_1} = 0\)より\(M[n] = (M_j)_{j=0}^{j_0-1} \oplus \bigoplus_{\mathbb{N}^2} ((M_j)_{j=j_0}^{j_1-1})_{k=0}^{n-1}\)である。

\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)より、任意の\(j \in \mathbb{N}\)に対し\(j_0 < j < j_1\)ならば\(M_{0,j} \geq M_{0,j_1} > M_{0,j_0}\)である。

\(j_0 < j_0+r' < j_1\)より\(M_{0,j_0} < M_{0,j_0+r'}\)であり、\(M[n]_{j_0+q(j_1-j_0)} = M_{j_0}\)かつ\(M[n]_{j_0+q'(j_1-j_0)+r'} = M_{j_0+r'}\)より\(M[n]_{0,j_0+q(j_1-j_0)} < M[n]_{0,j_0+q'(j_1-j_0)+r'}\)となる。□

補題（第\(0\)種型基本列の基本分岐規則）

任意の\(M \in RT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)と\(q \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在するとし、\(M_{1,j_1} = 0\)かつ\(q \leq n-1\)かつ\(j_0\)が非\(M\)許容ならば、\((0,j_0-1) <_{M[n]}^{\textrm{Next}} (0,j_0+q(j_1-j_0))\)かつ\((1,j_0-1) <_{M[n]}^{\textrm{Next}} (1,j_0+q(j_1-j_0))\)である。

証明：

\(j_{-1} := \textrm{Adm}_M(j_0)\)と置く。

\(j_0\)が非\(M\)許容であることから\(j_{-1} < j_0\)であり、任意の\(j'_0 \in \mathbb{N}\)に対し\(j_{-1} < j'_0 \leq j_0\)ならば\((1,j'_0-1) <_M^{\textrm{Next}} (1,j'_0)\)である。特に\((1,j_0-1) <_M^{\textrm{Next}} (1,j_0)\)となり、簡約性と係数の関係より\(M\)は条件(A)と(B)を満たすことから、\(M_{0,j_0-1}+1 = M_{0,j_0}\)かつ\(M_{1,j_0-1}+1 = M_{1,j_0}\)である。

更に \(M_{1,j_1} = 0\)より\(M[n] = (M_j)_{j=0}^{j_0-1} \oplus \bigoplus_{\mathbb{N}^2} ((M_j)_{j=j_0}^{j_1-1})_{k=0}^{n-1}\)であるので\(M[n]_{j_0-1} = M_{j_0-1}\)かつ\(M[n]_{j_0+q(j_1-j_0)} = M_{j_0}\)であることから、\(M[n]_{0,j_0-1} = M[n]_{0,j_0+q(j_1-j_0)}-1 < M[n]_{0,j_0+q(j_1-j_0)}\)かつ\(M[n]_{1,j_0-1} = M[n]_{1,j_0+q(j_1-j_0)}-1 < M[n]_{1,j_0+q(j_1-j_0)}\)である。

一方で任意の\(j'_0 \in \mathbb{N}\)に対し、\(j_0-1 < j'_0 < j_0+q(j_1-j_0)\)ならば第\(0\)種型基本列の基本不等式より\(M[n]_{j'_0} \geq M[n]_{j_0+q(j_1-j_0)}\)である。以上より、\((0,j_0-1) <_{M[n]}^{\textrm{Next}} (0,j_0+q(j_1-j_0))\)かつ\((1,j_0-1) <_{M[n]}^{\textrm{Next}} (1,j_0+q(j_1-j_0))\)である。□

補題（第\(0\)種型基本列の基本基点関係）

任意の\(M \in RT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在するとし\(j_{-1} := \textrm{Adm}_M(j_0)\)と置くと、\(M_{1,j_1} = 0\)ならば以下が成り立つ：

(1) \(n > 1\)ならば\((M[n],j_0+(n-1)(j_1-j_0)) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)である。

(2) \(j_0\)が非\(M\)許容ならば\((M[n],j_{-1}) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)である。

証明：

簡約性が基本列で保たれることから\(M[n]\)は簡約である。

\(M_{1,j_1} = 0\)より\((M[n]_j)_{j=j_0+(n-1)(j_1-j_0)}^{j_0+n(j_1-j_0)-1} = (M_j)_{j=j_0}^{j_1-1}\)である。

(1) 第\(0\)種型基本列の基本不等式より\((0,j_0) \leq_M (0,j_1-1)\)であるので、\((0,j_0+(n-1)(j_1-j_0)) \leq_{M[n]} (0,j_0+(n-1)(j_1-j_0)+(j_1-j_0-1)) = (0,j_0+n(j_1-j_0)-1)\)である。

第\(0\)種型基本列の基本分岐規則より\((1,j_0-1) <_{M[n]}^{\textrm{Next}} (1,j_0+(n-1)(j_1-j_0))\)であり、\(n > 1\)より\(j_0+(n-1)(j_1-j_0)-1 > j_0-1\)であるので\((1,j_0+(n-1)(j_1-j_0)-1) \leq_{M[n]} (1,j_0+(n-1)(j_1-j_0))\)でない。従って\(j_0+(n-1)(j_1-j_0)\)は\(M[n]\)許容であり、\((M[n],j_0+(n-1)(j_1-j_0)) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)である。

(2) \(j_0\)の非\(M\)許容性より\((0,j_{-1}) \leq_M (0,j_0-1)\)であるので\((0,j_{-1}) \leq_{M[n]} (0,j_0-1)\)であり、第\(0\)種型基本列の基本分岐規則より\((0,j_0-1) <_{M[n]}^{\textrm{Next}} (0,j_0+(n-1)(j_1-j_0))\)であり、(1)より\((0,j_0+(n-1)(j_1-j_0)) \leq_{M[n]} (0,j_0+n(j_1-j_0)-1)\)であるので、\((0,j_{-1}) \leq_{M[n]} (0,j_0+n(j_1-j_0)-1)\)である。

許容性の切片への遺伝性より\(j_{-1}\)は\(\textrm{Pred}(M)\)許容である。\(j_0\)の非\(M\)許容性より\(j_{-1} < j_0 \leq j_1-1\)であり、\((M[n]_j)_{j=0}^{j_1-1} = \textrm{Pred}(M)\)であるので、再び許容性の切片への遺伝性より\(j_{-1}\)は\(M[n]\)許容である。以上より、\((M[n],j_{-1}) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)である。□

それでは本題に戻る。

条件(II)の下での\(\textrm{Trans}\)と基本列の交換関係の証明：

標準形の簡約性から\(M\)は簡約であり、簡約性と係数の関係より\(M\)は条件(A)と(B)を満たす。

\(M\)が条件(II)を満たすことから、\(M_{1,j_0} \geq M_{1,j_1}\)かつ\(j_0\)が非\(M\)許容すなわち\(j_{-1} < j_0\)である。

\(\textrm{Mark}\)の左端の基本性質より\(v = M_{1,j_{-1}}\)である。scb分解の置換可能性より\((s_1,c_2,b_1) = (s_1,D_{M_{1,j_{-1}}}(t_3 + D_{M_{1,j_0}}(t_4 + D_0 0)),b_1)\)は\(\textrm{Trans}(M)\)のscb分解であり、scb分解と基本列の関係 (1-2)より

\begin{eqnarray*}
\textrm{Trans}(M)[n] = s_1 D_{M_{1,j_{-1}}}(t_3 + (D_{M_{1,j_0}} t_4) \times (n+1)) b_1
\end{eqnarray*}

である。特に\(\textrm{Trans}(M) \neq 0\)である。

(1)～(4)を\(n \in \mathbb{N}_{+}\)に関する数学的帰納法で示す。

\(n=1\)とする。

\(M[n] = \textrm{Pred}(M)\)より\(\textrm{Trans}(M[n]) = \textrm{Trans}(\textrm{Pred}(M)) = t_1\)かつ\(\textrm{Mark}(M[n],j_{-1}) = \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = c_1\)である。

\(P(t_2)_{J_1}\)の左端が\(D_{M_{1,j_0}}\)であるとする。

\(m_n = n-1 = 0\)であり、

\begin{eqnarray*}
t_3 & = & \Sigma_{\textrm{B}} (P(t_2)_J)_{J=0}^{J_1-1} \\
c_1 & = & D_v t_2 = D_{M_{1,j_{-1}}} (\Sigma_{\textrm{B}} (P(t_2)_J)_{J=0}^{J_1-1} + P(t_2)_{J_1}) = D_{M_{1,j_{-1}}} (t_3 + D_{M_{1,j_0}} t_4)
\end{eqnarray*}

であるので\(\textrm{Mark}(M[n],j_{-1}) = c_1 = D_{M_{1,j_{-1}}} (t_3 + (D_{M_{1,j_0}} t_4) \times (m_n+1))\)であり、

\begin{eqnarray*}
\textrm{Trans}(M[n]) = t_1 = s_1 c_1 b_1 = s_1 D_{M_{1,j_{-1}}} (t_3 + (D_{M_{1,j_0}} t_4)) b_1 = \textrm{Trans}(M)[n-1]
\end{eqnarray*}

である。従って\(\textrm{Trans}(M) \neq 0\)と[Buc1] Lemma 3.2より\(\textrm{Trans}(M[n]) = \textrm{Trans}(M)[n-1] < \textrm{Trans}(M)\)である。

\(P(t_2)_{J_1}\)の左端が\(D_{M_{1,j_0}}\)でないとする。

\begin{eqnarray*}
c_1 & = & D_v t_2 = D_{M_{1,j_{-1}}} t_2 \\
c_2 & = & D_v(t_2 + D_{M_{1,j_0}} 0) = D_{M_{1,j_{-1}}}(t_2 + D_{M_{1,j_0}} 0)
\end{eqnarray*}

であるので\(\textrm{Mark}(M[n],j_{-1}) = c_1 = D_{M_{1,j_{-1}}} t_2\)であり、

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & t_1 = s_1 c_1 b_1 = s_1 D_{M_{1,j_{-1}}} t_2 b_1 \\
\textrm{Trans}(M) & = & s_1 c_2 b_1 = s_1 D_{M_{1,j_{-1}}}(t_2 + D_{M_{1,j_0}} 0) b_1
\end{eqnarray*}

である。従って部分表現の不等式の延長性より、\(t_2 < t_2 + D_{M_{1,j_0}} 0\)から\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

\(n > 1\)とする。

\(N := (M[n]_j)_{j=0}^{j_0+(n-1)(j_1-j_0)}\)と置く。

\(M\)の単項性より\((0,0) \leq_M (0,j_0-1)\)であるので\((0,0) \leq_N (0,j_0-1)\)であり、第\(0\)種型基本列の基本分岐規則より\((0,j_0-1) <_{M[n]}^{\textrm{Next}} (0,j_0+(n-1)(j_1-j_0))\)であり\((0,j_0-1) <_N^{\textrm{Next}} (0,j_0+(n-1)(j_1-j_0))\)となるので、\(N\)は単項である。\(M\)が条件(B)を満たすことから\(N_{0,0} = M_{0,0} = M_{1,0} = N_{1,0}\)となる。\(N\)の単項性と\(N_{0,0} = N_{1,0}\)より、\(N\)は条件(B)を満たす。

\(N\)が条件(A)を満たすことを示す。

\(i \in \{0,1\}\)と\(j'_0,j'_1 \in \mathbb{N}\)とし、\((i,j'_0) <_N^{\textrm{Next}} (i,j'_1)\)とする。

\(j'_1 \leq j_0\)ならば、\((i,j'_0) <_M^{\textrm{Next}} (i,j'_1)\)かつ\(M\)が条件(A)を満たすことから\(N_{i,j'_0}+1 = M_{i,j'_0}+1 = M_{i,j'_1} = N_{i,j'_1}\)である。

\(j'_0 < j_0 < j'_1\)とする。

\(j'_1-j_0\)を\(j_1-j_0\)で割った商と余りを\(q_1,r_1 \in \mathbb{N}\)と置く。

\(q_1 \leq n-1\)かつ\(r_1 < j_1-j_0\)である。

第\(0\)種型基本列の基本分岐規則と第\(0\)種型基本列の基本不等式より\((0,j_0-1) <_N^{\textrm{Next}} (0,j_0+q_1(j_1-j_0)) \leq_N (0,j_0+q_1(j_1-j_0)+r_1) = (0,j'_1)\)であるので、\((0,j_0-1) \leq_N (0,j_1)\)である。更に\(j'_0 < j_0\)かつ\((i,j'_0) <_N^{\textrm{Next}} (i,j'_1)\)より\((0,j'_0) \leq_N (0,j_0-1)\)となるので、\((0,j'_0) \leq_M (0,j_0-1)\)となる。

任意の\(j \in \mathbb{N}\)に対し、\((0,j'_0) \leq_M (0,j) \leq_M (0,j_0+r)\)ならば\((i,j) \leq_M (i,j_0+r_1)\)でないことを示す。

\(j \leq j_0-1\)ならば、\((0,j'_0) \leq_M (0,j) \leq_M (0,j_0+r)\)かつ\((0,j'_0) \leq_M (0,j_0-1)\)より\((0,j) \leq_M (0,j_0-1)\)でありすなわち\((0,j) \leq_N (0,j_0-1) \leq_N (0,j'_1)\)となるので、\((i,j'_0) <_N^{\textrm{Next}} (i,j'_1)\)と親の基本性質から\(M_{i,j} = N_{i,j} \geq N_{i,j'_1} = M_{i,j_0+r_1}\)となる。

\(j > j_0-1\)ならば、\((0,j) \leq_M (0,j_0+r)\)より\((0,j+q_1(j_1-j_0)) \leq_N (0,j_0+q_1(j_1-j_0)+r) = (0,j'_1)\)となり、\((i,j'_0) <_N^{\textrm{Next}} (i,j'_1)\)と親の基本性質から\(M_{i,j} = N_{i,j+q_1(j_1-j_0)} \geq N_{i,j'_1} = M_{i,j_0+r_1}\)となる。

以上より、いずれの場合も\(M_{i,j} \geq M_{i,j_0+r}\)であり、特に\((i,j) \leq_M (i,j_0+r_1)\)でない。

従って\((i,j'_0) <_M^{\textrm{Next}} (i,j_0+r_1)\)であり、\(M\)が条件(A)を満たすことから\(N_{i,j'_0}+1 = M_{i,j'_0}+1 = M_{i,j_0+r_1} = N_{i,j'_1}\)である。

\(j_0 \leq j'_0\)とする。

\(j'_1-j_0\)を\(j_1-j_0\)で割った商と余りを\(q_1,r_1 \in \mathbb{N}\)と置く。

\(q_1 \leq n-1\)かつ\(r_1 < j_1-j_0\)である。

第\(0\)種型基本列の基本分岐規則と第\(0\)種型基本列の基本不等式より\((0,j_0-1) <_N^{\textrm{Next}} (0,j_0+q_1(j_1-j_0)) \leq_N (0,j_0+q_1(j_1-j_0)+r_1) = (0,j'_1)\)であるので、\(j_0-1 < j_0 \leq j'_0\)かつ\((i,j'_0) <_N^{\textrm{Next}} (i,j'_1)\)より\(j_0+q_1(j_1-j_0) \leq j'_0 < j'_1\)である。

更に\((N_j)_{j=j_0+q_1(j_1-j_0)}^{j'_1} = (M_j)_{j=j_0}^{j_0+r_1}\)であるので、\((i,j'_0-q_1(j_1-j_0)) <_M^{\textrm{Next}} (i,j_0+r_1)\)である。\(M\)が条件(A)を満たすことから\(N_{i,j'_0}+1 = M_{i,j'_0-q_1(j_1-j_0)}+1 = M_{i,j_0+r_1} = N_{i,j'_1}\)となる。

以上よりいずれの場合も\(N_{i,j'_0}+1 = N_{i,j'_1}\)である。従って\(N\)は条件(A)を満たす。

\(N\)が条件(A)と(B)を満たすことから、簡約性と係数の関係より\(N\)は簡約である。

\(L' := \textrm{Red}((M[n]_j)_{j=j_0+(n-1)(j_1-j_0)}^{j_0+n(j_1-j_0)-1})\)と置く。

\(\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}}(t_3 + (D_{M_{1,j_0}} t_4) \times m_n + \textrm{Trans}(L')) b_1\)となることを示す。

\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(N\)に対して定義し、\(N\)に対しての適用であることを明示するために右肩に\(N\)を乗せて表記する。

\(j_{-1} < j_0 < j_1\)より\(j_1^N = \textrm{Lng}(N)-1 = j_0+(n-1)(j_1-j_0) > j_{-1} + (j_1-j_0) \geq 1\)となるので\(\textrm{Pred}(N)\)は零項であり、\(\textrm{Trans}\)が零項性を保つことから\(t_1^N = \textrm{Trans}(\textrm{Pred}(N)) \neq 0\)である。\(N\)が単項であることと合わせ、\(N\)に対して条件(I)～(VI)が意味を持つ。

第\(0\)種型基本列の基本分岐規則より\((0,j_0-1) <_N^{\textrm{Next}} (0,j_0+(n-1)(j_1-j_0))\)であり、\(j_0\)が非\(M\)許容かつ\(M\)が条件(A)を満たすことから\(N_{1,j_0-1}+1 = M_{1,j_0-1}+1 = M_{1,j_0} = N_{1,j_0+(n-1)(j_1-j_0)} > 0\)であり、かつ\((j_0-1)+1 = j_0 < j_0+(n-1)(j_1-j_0)\)であることから、\(N\)は条件(V)を満たす。

\(j_1^N = j_0+(n-1)(j_1-j_0)\)であり、第\(0\)種型基本列の基本分岐規則より\((0,j_0-1) <_N^{\textrm{Next}} (0,j_0+(n-1)(j_1-j_0))\)であるので、\(j_0^N = j_0-1\)である。\(j_0\)が非\(M\)許容であるので\(j_{-1} = \textrm{Adm}_M(j_0-1) = \textrm{Adm}_N(j_0-1) = \textrm{Adm}_N(j_0^N)\)となる。\(\textrm{Mark}\)の左端の基本性質より\(v^N = N_{1,\textrm{Adm}_N(j_0^N)} = N_{1,j_{-1}} = M_{1,j_{-1}}\)である。

\(\textrm{Pred}(N) = (M[n]_j)_{j=0}^{j_0+(n-1)(j_1-j_0)-1} = M[n-1]\)であるので\(c_1^N = \textrm{Mark}(\textrm{Pred}(N),\textrm{Adm}_N(j_0^N)) = \textrm{Mark}(M[n-1],j_{-1})\)であり、帰納法の仮定より

\begin{eqnarray*}
D_{v^N} t_2^N = c_1^N = \textrm{Mark}(M[n-1],j_{-1}) = D_{M_{1,j_{-1}}}(t_3 + (D_{M_{1,j_0}} t_4) \times m_n)
\end{eqnarray*}

かつ

\begin{eqnarray*}
& & s_1^N c_1^N b_1^N = t_1^N = \textrm{Trans}(\textrm{Pred}(N)) = \textrm{Trans}(M[n-1]) \\
& = & \left\{ \begin{array}{ll} \textrm{Trans}(M)[m_{n-1}] & (m_{n-1} \geq 0) \\ s_1 D_{M_{1,j_{-1}}}(t_2) & (m_{n-1} = -1) \end{array} \right. \\
& = & \left\{ \begin{array}{ll} s_1 D_{M_{1,j_{-1}}} (t_3 + (D_{M_{1,j_0}} t_4) \times m_n) b_1 & (m_n \geq 1) \\ s_1 D_{M_{1,j_{-1}}}(t_2) & (m_n = 0) \end{array} \right. \\
& = & s_1 D_{M_{1,j_{-1}}} (t_3 + (D_{M_{1,j_0}} t_4) \times m_n) b_1
\end{eqnarray*}

となる。従って\(t_2^N = t_3 + (D_{M_{1,j_0}} t_4) \times m_n\)かつ\(s_1^N = s_1\)かつ\(b_1^N = b_1\)である。\(N\)が条件(V)を満たすことから

\begin{eqnarray*}
c_2^N = D_{v^N}(t_2^N + D_{N_{1,j_1^N}} 0) = D_{M_{1,j_{-1}}}(t_3 + (D_{M_{1,j_0}} t_4) \times m_n + D_{M_{1,j_0}} 0)
\end{eqnarray*}

となるので

\begin{eqnarray*}
\textrm{Trans}(N) = s_1^N c_2^N b_1^N = s_1 D_{M_{1,j_{-1}}}(t_3 + (D_{M_{1,j_0}} t_4) \times m_n + D_{M_{1,j_0}} 0) b_1
\end{eqnarray*}

である。更に第\(0\)種型基本列の基本基点関係 (1)より\((M[n],j_0+(n-1)(j_1-j_0)) \in RT_{\textrm{PS}}^{\textrm{Marked}}\)であり、\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より

\begin{eqnarray*}
\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}}(t_3 + (D_{M_{1,j_0}} t_4) \times m_n + \textrm{Mark}(M[n],j_0+(n-1)(j_1-j_0))) b_1
\end{eqnarray*}

である。

\(j_0\)が非\(M\)許容であることから\((1,j_0) <_M^{\textrm{Next}} (1,j_0+1)\)であり、\(M\)が条件(II)を満たすことから\(M_{1,j_0} \geq 0 = M_{1,j_1}\)であるので、\(j_1 > j_0+1\)であり、よって\(\textrm{Lng}(L')-1 = j_1-j_0-1 > 0\)である。

直系先祖による切片と\(\textrm{Red}\)と\(\textrm{IncrFirst}\)の関係より

\begin{eqnarray*}
& & (M_j)_{j=j_0}^{j_1-1} = (M[n]_j)_{j=j_0+(n-1)(j_1-j_0)}^{j_0+n(j_1-j_0)-1} = \textrm{IncrFirst}^{M[n]_{0,j_0+(n-1)(j_1-j_0)}-M[n]_{1,j_0+(n-1)(j_1-j_0)}}(L') \\
& = & \textrm{IncrFirst}^{M_{0,j_0}-M_{1,j_0}}(L')
\end{eqnarray*}

となり、\(\textrm{Red}\)の\(\textrm{IncrFirst}\)不変性と\(L'\)が簡約であることから\(\textrm{Red}((M_j)_{j=j_0}^{j_1-1}) = L'\)である。\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示と\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性より

\begin{eqnarray*}
& & \textrm{Mark}(M[n],j_0+(n-1)(j_1-j_0)) = \textrm{Trans}((M[n]_j)_{j=j_0+(n-1)(j_1-j_0)}^{j_0+n(j_1-j_0)-1}) = \textrm{Trans}((M_j)_{j=j_0}^{j_1-1}) \\
& = & \textrm{Trans}(L')
\end{eqnarray*}

となる。従って

\begin{eqnarray*}
\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}}(t_3 + (D_{M_{1,j_0}} t_4) \times m_n + \textrm{Trans}(L')) b_1
\end{eqnarray*}

となる。

\(\textrm{Trans}(L') = D_{M_{1,j_0}} t_4\)であることを示す。

\(L := \textrm{Red}((M_j)_{j=j_{-1}}^{j_1-1})\)と置く。

\((0,j_{-1}) \leq_M (0,j_0) <_M^{\textrm{Next}} (0,j_1)\)と直系先祖の木構造 (1)から\((0,j_{-1}) \leq_M (0,j_1-1)\)である。従って標準形の直系先祖による切片の簡約化の強単項性より\(L\)は強単項である。

\(j_{-1} < j_0\)と許容性の切片への遺伝性から\(j_0-j_{-1}\)は非\(L\)許容であり、許容化の切片への遺伝性から\(\textrm{Adm}_L(j_0-j_{-1}) = j_{-1}-j_{-1} = 0\)である。従って\(\textrm{TrMax}\)の定義より\(0 < j_0-j_{-1} < \textrm{TrMax}(L)\)である。

\(\textrm{Lng}(L)-1 = j_1-j_{-1}\)であり、\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)より\((0,j_0-j_{-1}) <_L^{\textrm{Next}} (0,j_1-j_{-1})\)であり、\(L_{1,j_0-j_{-1}} = M_{1,j_0} \geq M_{1,j_1} = L_{1,j_1-j'_0}\)である。従って\(\textrm{TrMax}\)の定義より\(\textrm{TrMax}(L) < j_1-j'_0\)となるので、\(\textrm{Lng}(\textrm{Br}(L)) \geq 0\)である。

簡約性と係数の関係より\(L\)は条件(A)と(B)を満たす。\(L\)が条件(A)と(B)を満たすことから\(L_{0,j_1-j_{-1}} = L_{0,j_1-j_{-1}}+1 = L_{1,j_1-j_{-1}}+1 \geq L_{0,j_1-j_{-1}}+1 > L_{0,j_1-j_{-1}}\)である。

従って条件(II)か(IV)の下での終切片と\(\textrm{Trans}\)の関係から、ある\((t'_1,t'_2) \in T_{\textrm{B}}^2\)が存在して以下を満たす：

(1) \(\textrm{Trans}(L') = D_{L_{1,j_0-j_{-1}}}(t'_1 + t'_2)\)かつ\(t'_2\)である。

(2) \(\textrm{Trans}(L) = D_{L_{1,0}}(t'_1 + D_{L_{1,j_0-j_{-1}}}(t'_1 + t'_2))\)である。

右端第\(2\)基点のMarkの基本性質と\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示と\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示より

\begin{eqnarray*}
& & D_{L_{1,0}}(t'_1 + D_{L_{1,j_0-j_{-1}}}(t'_1 + t'_2)) = \textrm{Trans}(L) = \textrm{Trans}((M_j)_{j=j_{-1}}^{j_1}) = \textrm{Mark}(M,j_{-1}) = c_2  \\
& = & D_{M_{1,j_{-1}}}(t_3 + D_{M_{1,j_0}} t_4)
\end{eqnarray*}

であるので\(D_{L_{1,j_0-j_{-1}}}(t'_1 + t'_2)\)は\(t_3 + D_{M_{1,j_0}} t_4\)の最右単項成分\(D_{M_{1,j_0}} t_4\)に等しく、以上より

\begin{eqnarray*}
\textrm{Trans}(L') = D_{L_{1,j_0-j_{-1}}}(t'_1 + t'_2) = D_{M_{1,j_0}} t_4
\end{eqnarray*}

である。

以上より、

\begin{eqnarray*}
& & \textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}}(t_3 + (D_{M_{1,j_0}} t_4) \times m_n + \textrm{Trans}(L')) b_1 \\
& = & s_1 D_{M_{1,j_{-1}}}(t_3 + (D_{M_{1,j_0}} t_4) \times m_n + D_{M_{1,j_0}} t_4) b_1 \\
& = & s_1 D_{M_{1,j_{-1}}}(t_3 + (D_{M_{1,j_0}} t_4) \times (m_n+1)) b_1 = \textrm{Trans}(M)[m_n]
\end{eqnarray*}

である。□

## 条件(III)か(IV)の下での展開規則[]

命題（条件(III)か(IV)の下での\(\textrm{Trans}\)と基本列の交換関係）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)を満たす一意な\(j_{-2} \in \mathbb{N}\)が存在するとし\(j_{-3} := \textrm{Adm}_M(j_{-2})\)と置くと、\(j_1 > 1\)かつ\(M\)が条件(III)か(IV)を満たすならば[72]、以下が成り立つ：

(1) \(\textrm{Trans}(M[n]) \leq \textrm{Trans}(M)[n-1]\)である。

(2) \(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

(3) \(\textrm{Trans}(M)[n-1] < \textrm{Trans}(M[n+1])\)である。

条件(III)か(IV)の下での\(\textrm{Trans}\)と基本列の交換関係を証明するための準備としていくつかの補題を示す。

補題（右端の非許容直系先祖の基本性質）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(m_0,m_1 \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(m_{-1} := \textrm{Adm}_M(m_0)\)と置き、\(N := (M_j)_{j=m_{-1}}^{j_1}\)と置き、\((0,m_0) <_M^{\textrm{Next}} (0,m_1) \leq_M (0,j_1)\)として\(N' := (M_j)_{j=m_0}^{j_1}\)と置き、\(J_1 := \textrm{Lng}(\textrm{Br}(\textrm{Red}(N)))-1\)と置くと、\((1,m_1-1) <_M^{\textrm{Next}} (1,m_1)\)でなくかつ\(m_0\)が非\(M\)許容ならば、\(J_1 \geq 0\)かつ\(0 < m_0-m_{-1} < \textrm{TrMax}(\textrm{Red}(N))\)かつ\(m_0-m_{-1} = \textrm{Joints}(\textrm{Red}(N))_{J_1}\)かつ\(\textrm{FirstNodes}(\textrm{Red}(N))_{J_1} = m_1-m_{-1}\)である。

証明：

\(m_0\)が非\(M\)許容より\(m_{-1} < m_0\)であるので、\(m_{-1}-m_0 > 0\)である。

任意の\(j \in \mathbb{N}\)に対し、\(0 < j \leq \textrm{TrMax}(\textrm{Red}(N))\)ならば、\((1,j-1) <_{\textrm{Red}(N)}^{\textrm{Next}} (1,j)\)であり直系先祖の\(\textrm{Red}\)不変性より\((1,j-1) <_{N}^{\textrm{Next}} (1,j)\)すなわち\((1,j+m_{-1}-1) <_M^{\textrm{Next}} (1,j+m_{-1})\)である。従って\((1,m_1-1) <_M^{\textrm{Next}} (1,m_1)\)でないことから\(\textrm{TrMax}(\textrm{Red}(N)) < m_1-m_{-1}\)である。

\((0,m_0) <_M^{\textrm{Next}} (0,m_1) \leq_M (0,j_1)\)より\((0,m_0-m_{-1}) <_N^{\textrm{Next}} (0,m_1-m_{-1}) \leq_N (0,j_1-m_{-1})\)であり、直系先祖の\(\textrm{Red}\)不変性より\((0,m_0-m_{-1}) <_{\textrm{Red}(N)}^{\textrm{Next}} (0,m_1-m_{-1}) \leq_{\textrm{Red}(N)} (0,j_1-m_{-1})\)である。

許容化の切片への遺伝性より\(\textrm{Adm}_N(m_0-m_{-1}) = \textrm{Adm}_M(m_0)-m_{-1} = 0\)であり、許容化の\(\textrm{Red}\)不変性から\(\textrm{Adm}_{\textrm{Red}(N)}(m_0-m_{-1}) = 0\)である。従って\(m_0-m_{-1} \leq \textrm{TrMax}(\textrm{Red}(N))\)である。

\(0 < m_0-m_{-1} \leq \textrm{TrMax}(\textrm{Red}(N))\)より\(\textrm{TrMax}(\textrm{Red}(N)) > 0\)である。\(\textrm{TrMax}\)の定義より\(\textrm{TrMax}(\textrm{Red}(N))\)は\(\textrm{Red}(N)\)許容であるので、\(\textrm{Adm}_{\textrm{Red}(N)}(\textrm{TrMax}(\textrm{Red}(N))) = \textrm{TrMax}(\textrm{Red}(N)) > 0 = \textrm{Adm}_{\textrm{Red}(N)}(m_0-m_{-1})\)である。従って\(m_0-m_{-1} < \textrm{TrMax}(\textrm{Red}(N))\)となる。

\(m_0-m_{-1} \leq \textrm{TrMax}(\textrm{Red}(N)) < m_1-m_{-1}\)と\((0,m_0-m_{-1}) <_{\textrm{Red}(N)}^{\textrm{Next}} (0,m_1-m_{-1}) \leq_{\textrm{Red}(N)} (0,j_1-m_{-1})\)と\(P\)の各成分の非複項性より\(\textrm{FirstNodes}(\textrm{Red}(N))_{J_1} = m_1-m_{-1}\)かつ\(m_0-m_{-1} = \textrm{Joints}(\textrm{Red}(N))_{J_1}\)である。□

補題（条件(III)～(V)の下での右端の置き換えと\(\textrm{Trans}\)の関係）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)を満たす一意な\(j_{-2} \in \mathbb{N}\)が存在するとして\(N' := (M_j)_{j=j_{-2}}^{j_1}\)と置き、\(L' := (M_j)_{j=j_{-2}}^{j_1-1} \oplus_{\mathbb{N}^2}((M_{0,j_1},M_{1,j_{-2}}))\)と置くと、\(j_{-2} < j_1-1\)ならば一意な\((s,b) \in (\Sigma^{< \omega})^2\)が存在して以下を満たす：

(1) \((s,D_{M_{1,j_1}} 0,b)\)は\(\textrm{Trans}(N')\)のscb分解である。

(2) \(j_{-2} = j_0\)または\(j_0\)が\(M\)許容であるならば、\((s,D_{M_{1,j_{-2}}} 0,b)\)は\(\textrm{Trans}(L')\)のscb分解である。

(3) \(j_{-2} < j_0\)かつ\(j_0\)が非\(M\)許容であるならば、\((s,D_{M_{1,j_0}}(t_2 + D_{M_{1,j_0}} 0),b)\)は\(\textrm{Trans}(L')\)のscb分解である。

証明：

\(j_{-3} := \textrm{Adm}_M(j_{-2})\)と置く。

\(N := (M_j)_{j=j_{-3}}^{j_1}\)と置く。

\((1,j_{-3}) \leq_M (1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)より\((0,j_{-3}) \leq_M (0,j_{-2}) \leq_M (0,j_1)\)であるので、標準形の直系先祖による切片の簡約化の強単項性より\(\textrm{Red}(N)\)と\(\textrm{Red}(N')\)は強単項であり、特に簡約かつ単項である。

\((N'_{0,j})_{j=0}^{j_1-j_{-2}} = (L'_{0,j})_{j=0}^{j_1-j_{-2}}\)と直系先祖の\(\textrm{Red}\)不変性から\(L'\)は単項であり、再び\(\textrm{Red}\)が単項性を保つことから\(\textrm{Red}(L')\)は簡約かつ単項である。

\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(\textrm{Red}(N)\)と\(\textrm{Red}(N')\)と\(\textrm{Red}(L')\)に対して定め、\(\textrm{Red}(N)\)と\(\textrm{Red}(N')\)と\(\textrm{Red}(L')\)に対する適用であることを明示するために右肩にそれぞれ\(N\)と\(N'\)と\(L'\)を載せて表記する。

\(j_1^N = j_1-j_{-3}\)かつ\(j_1^{N'} = j_1^{L'} = j_1-j_{-2}\)であり、直系先祖の\(\textrm{Red}\)不変性から\(j_0^N = j_0-j_{-3}\)かつ\(j_0^{N'} = j_0^{L'} = j_0-j_{-2}\)かつ\((1,0) \leq_{\textrm{Red}(N)} (1,j_{-2}-j_{-3}) <_{\textrm{Red}(N)}^{\textrm{Next}} (1,j_1-j_{-3}) = (1,j_1^N)\)かつ\((1,0) <_{\textrm{Red}(N')}^{\textrm{Next}} (1,j_1-j_{-2}) = (1,j_1^{N'})\)である。従って\(\textrm{Red}(N')_{1,0} <_{\textrm{Red}(N')}^{\textrm{Next}} \textrm{Red}(N')_{1,j_1^{N'}}\)である。

簡約性と係数の関係から\(M\)と\(\textrm{Red}(N')\)は条件(A)と(B)を満たす。\(M\)が条件(A)を満たすことと\(j_{-3} = \textrm{Adm}_M(j_{-2})\)より、\((N_j)_{j=0}^{j_{-2}-j_{-3}} = \textrm{IncrFirst}^{N_{0,0}-N_{1,0}}(((j,j))_{j=N_{1,0}}^{N_{1,j_{-2}-j_{-3}}})\)かつ\(N_{0,0}-N_{1,0} = M_{0,j_{-3}}-M_{1,j_{-3}} = M_{0,j_{-2}}-M_{1,j_{-2}} = N'_{0,0}-N'_{0,1}\)である。

直系先祖による切片と\(\textrm{Red}\)と\(\textrm{IncrFirst}\)の関係より\(\textrm{IncrFirst}^{N'_{0,0}-N'_{1,0}}(\textrm{Red}(N)) = \textrm{IncrFirst}^{N_{0,0}-N_{1,0}}(\textrm{Red}(N)) = N\)かつ\(\textrm{IncrFirst}^{N'_{0,0}-N'_{1,0}}(\textrm{Red}(N')) = N'\)である。

従って

\begin{eqnarray*}
\textrm{Red}(N) & = & (N_{0,j}-N'_{0,0}+N'_{1,0},N_{1,j})_{j=0}^{j_1^{N'}} = ((j,j))_{j=N_{1,0}}^{N'_{1,0}-1} \oplus_{\mathbb{N}^2} (N'_{0,j}-N'_{0,0}+N'_{1,0},N'_{1,j})_{j=0}^{j_1^{N'}} \\
\textrm{Red}(N') & = & (N'_{0,j}-N'_{0,0}+N'_{1,0},N'_{1,j})_{j=0}^{j_1^{N'}}
\end{eqnarray*}

となるので、\(\textrm{Red}(N) = ((j,j))_{j=N_{1,0}}^{N'_{1,0}-1} \oplus_{\mathbb{N}^2} \textrm{Red}(N')\)である。特に\(\textrm{Br}(\textrm{Red}(N)) = \textrm{Br}(\textrm{Red}(N'))\)である。

\(J_1 := \textrm{Lng}(\textrm{Br}(\textrm{Red}(N')))-1\)と置く。

\(\textrm{Red}(N')_{1,0} <_{\textrm{Red}(N')}^{\textrm{Next}} \textrm{Red}(N')_{1,j_1^{N'}}\)かつ\(0 < j_1-1-j_{-2} < j_1^{N'}-1\)より\(\textrm{Red}(N')_{1,j_1^{N'}-1} <_{\textrm{Red}(N')}^{\textrm{Next}} \textrm{Red}(N')_{1,j_1^{N'}}\)でない。従って\(\textrm{TrMax}(\textrm{Red}(N')) < j_1^{N'}\)であり、\(J_1 \geq 0\)である。

\(R := \textrm{Pred}(\textrm{Red}(N')) \oplus_{\mathbb{N}^2} (N'_{0,j_1^{N'}}-N'_{0,0}+N'_{1,0},N'_{1,0})\)と置く。

\(R\)が簡約であることを示す。

\(R\)の定義から\(\leq_{\textrm{Red}(N')}\)と\(\leq_R\)は\((\{0,1\} \times \mathbb{N}) \setminus \{(1,j_1^{N'})\}\)上で一致する。特に\(\textrm{Red}(N')\)の単項性から\(R\)は単項である。

\((1,0) <_{\textrm{Red}(N')}^{\textrm{Next}} (1,j_1^{N'})\)と親の基本性質 (2)より、\(\textrm{Red}(N')_{1,0} < \textrm{Red}(N')_{1,j_1^{N'}}\)かつ任意の\(j \in \mathbb{N}\)に対し\(0 < j < j_1^{N'}\)かつ\((0,j) \leq_{\textrm{Red}(N')} (0,j_1^{N'})\)ならば\(R_{1,j} = N'_{1,j} = \textrm{Red}(N')_{1,j} \geq \textrm{Red}(N')_{1,j_1^{N'}} > \textrm{Red}(N')_{1,0} = N'_{1,0} = R_{1,j_1^{N'}}\)である。

従って、任意の\(j \in \mathbb{N}\)に対し\(0 < j < j_1^{N'}\)ならば\((1,j) \leq_R (1,j_1^{N'})\)でない。更に\(R_{1,0} = N'_{1,0} = R_{1,j_1^{N'}}\)であるので\((1,0) \leq_R (1,j_1^{N'})\)でない。すなわち\((1,j) <_R^{\textrm{Next}} (1,j_1^{N'})\)を満たす一意な\(j \in \mathbb{N}\)は存在しない。

以上より、任意の\(i \in \{0,1\}\)と\(j'_1,j'_2 \in \mathbb{N}\)に対し、\((i,j'_1) <_R^{\textrm{Next}} (i,j'_1)\)である必要十分条件は\((i,j'_1) <_{\textrm{Red}(N')}^{\textrm{Next}} (i,j'_2) \neq (1,j_1^{N'})\)である。更に\(\textrm{Red}(N')\)が条件(A)を満たすことと\(R = \textrm{Pred}(\textrm{Red}(N')) \oplus_{\mathbb{N}^2} (\textrm{Red}(N')_{0,j_1^{N'}},N'_{1,0})\)であることから、\(R\)は条件(A)を満たす。

\(R\)の単項性と\(R_{0,0} = \textrm{Pred}(\textrm{Red}(N'))_{0,0} = N'_{1,0}\)から、\(R\)は条件(B)を満たす。従って簡約性と係数の関係から\(R\)は簡約である。

また\(\textrm{IncrFirst}^{N'_{0,0}-N'_{1,0}}(R) = L'\)より、\(\textrm{Red}\)の\(\textrm{IncrFirst}\)不変性から\(\textrm{Red}(L') = \textrm{Red}(R) = R\)である。

\(\textrm{Pred}(N') = \textrm{Pred}(L')\)より\(t_1^{N'} = t_1^{L'}\)であり、\(\textrm{Red}(N')\)の単項性と\(\textrm{Trans}\)が零項性を保つことから\(t_1^{N'} \neq 0\)である。従って\(\textrm{Red}(N')\)と\(\textrm{Red}(L')\)に対し条件(I)～(VI)が意味を持つ。

\(\textrm{Pred}(N') = \textrm{Pred}(L')\)かつ\(j_0^{N'} = j_0^{L'} < j_1^{L'}\)より\(j_{-1}^{N'} = j_{-1}^{L'}\)である。従って\(c_1^{N'} = c_1^{L'}\)であり、\(D_{v^{N'}} t_2^{N'} = c_1^{N'} = c_1^{L'} = D_{v^{L'}} t_2^{L'}\)であるので\(v^{N'} = v^{L'}\)かつ\(t_2^{N'} = t_2^{L'}\)である。また\(t_1^{N'} = t_1^{L'}\)と\(c_1^{N'} = c_1^{L'}\)とscb分解の一意性より\(s_1^{N'} = s_1^{L'}\)かつ\(b_1^{N'} = b_1^{L'}\)である。

\((1,0) <_{\textrm{Red}(N')}^{\textrm{Next}} (1,j_1-j_{-2}) = (1,j_1^{N'})\)より\(\textrm{Red}(N')_{1,j_1^{N'}} > \textrm{Red}(N')_{1,0} \geq 0\)であり、\((1,0) <_{\textrm{Red}(N')}^{\textrm{Next}} (1,j_1^{N'})\)かつ\(0 < j_1-1-j_{-2} = j_1^{N'}-1\)であるので、\(\textrm{Red}(N')\)は条件(III)か(IV)か(V)を満たす。

\(\textrm{Red}(N')\)が条件(A)を満たすことと\(\textrm{Red}(N')_{1,0} <_{\textrm{Red}(N')}^{\textrm{Next}} \textrm{Red}(N')_{1,j_1^{N'}}\)より\(\textrm{Red}(N')_{1,0} = \textrm{Red}(N')_{1,j_1^{N'}}-1\)であるので、

\begin{eqnarray*}
& & \textrm{Red}(L')_{1,j_0^{L'}} - \textrm{Red}(L')_{1,j_1^{L'}} = R_{1,j_0^{N'}} - R_{1,j_1^{N'}} = \textrm{Red}(N')_{1,j_0^{N'}} - N'_{1,0} \\
& = & \textrm{Red}(N')_{1,j_0^{N'}} - \textrm{Red}(N')_{1,0} = \textrm{Red}(N')_{1,j_0^{N'}} - \textrm{Red}(N')_{1,j_1^{N'}} + 1 > \textrm{Red}(N')_{1,j_0^{N'}} - \textrm{Red}(N')_{1,j_1^{N'}}
\end{eqnarray*}

である。従って\(\textrm{Red}(N')\)が条件(III)か(IV)を満たすならば、\(\textrm{Red}(N')_{1,j_0^{N'}} - \textrm{Red}(N')_{1,j_1^{N'}} \geq 0\)であるので\(\textrm{Red}(L')_{1,j_0^{L'}} - \textrm{Red}(L')_{1,j_1^{L'}} > 0\)となり、\(\textrm{Red}(L')\)は条件(V)と(VI)のいずれも満たさない。\(\textrm{Red}(N')\)が条件(V)を満たすならば、\(\textrm{Red}(N')_{1,j_0^{N'}}+1 = \textrm{Red}(N')_{1,j_1^{N'}}\)より\(\textrm{Red}(L')_{1,j_0^{L'}} - \textrm{Red}(L')_{1,j_1^{L'}} = 0\)となるので\(\textrm{Red}(L')\)は条件(V)と(VI)のいずれも満たさない。

以上より、いずれの場合も\(\textrm{Red}(L')\)は条件(V)と(VI)のいずれも満たさない。

許容性の切片への遺伝性より以下が同値である：

(1) \(j_0^{N'}\)が\(N'\)許容である。

(2) \(j_0^{L'}\)が\(L'\)許容である。

(3) \(j_{-2} = j_0\)または\(j_0\)が\(M\)許容である。

従って\(\textrm{Red}\)が許容性を保つことから以下が同値である：

(1) \(j_0^{N'}\)が\(\textrm{Red}(N')\)許容である。

(2) \(j_0^{L'}\)が\(\textrm{Red}(L')\)許容である。

(3) \(j_{-2} = j_0\)または\(j_0\)が\(M\)許容である。

\(j_{-2} = j_0\)または\(j_0\)が\(M\)許容ならば\(\textrm{Red}(L')\)は条件(I)か(III)を満たし、\(j_{-2} < j_0\)かつ\(j_0\)が非\(M\)許容ならば\(\textrm{Red}(L')\)は条件(II)か(IV)を満たす。

\(j_{-2} = j_0\)または\(j_0\)が\(M\)許容であるとする。

\(\textrm{Red}(N')\)は条件(III)か(V)を満たし、\(\textrm{Red}(L')\)は条件(I)か(III)を満たす。

\(t_2^{N'} = t_2^{L'}\)と\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性より

\begin{eqnarray*}
\textrm{Trans}(N') & = & \textrm{Trans}(\textrm{Red}(N')) = s_1^{N'} c_2^{N'} b_1^{N'} = s_1^{N'} D_{v^{N'}}(t_2^{N'} + D_{\textrm{Red}(N')_{1.j_1^{N'}}} 0) b_1^{N'} \\
& = & s_1^{N'} D_{v^{N'}}(t_2^{N'} + D_{N'_{1,j_1^{N'}}} 0) b_1^{N'} = s_1^{N'} D_{v^{N'}}(t_2^{N'} + D_{M_{1,j_1}} 0) b_1^{N'} \\
\textrm{Trans}(L') & = & \textrm{Trans}(\textrm{Red}(L')) = s_1^{L'} c_2^{L'} b_1^{L'} = s_1^{L'} D_{v^{L'}}(t_2^{L'} + D_{\textrm{Red}(L')_{1,j_1^{L'}}} 0) b_1^{L'} \\
& = & s_1^{N'} D_{v^{N'}}(t_2^{N'} + D_{L'_{1,j_1^{N'}}} 0) b_1^{N'} = s_1^{N'} D_{v^{N'}}(t_2^{N'} + D_{N'_{1,0}} 0) b_1^{N'} \\
& = & s_1^{N'} D_{v^{N'}}(t_2^{N'} + D_{M_{1,j_{-2}}} 0) b_1^{N'} \\
\end{eqnarray*}

であるので、scb分解の合成則と加法とscb分解の関係より一意な\((s,b) \in (\Sigma^{< \omega})^2\)が存在して\((s,D_{M_{1,j_1}} 0,b)\)と\((s,D_{M_{1,j_{-2}}} 0,b)\)はそれぞれ\(\textrm{Trans}(N')\)と\(\textrm{Trans}(L')\)のscb分解である。□

\(j_{-2} < j_0\)かつ\(j_0\)が非\(M\)許容であるとする。

\(\textrm{Red}(N')\)は条件(IV)を満たし、\(\textrm{Red}(L')\)は条件(II)か(IV)を満たす。

\(t_2^{N'} = t_2^{L'}\)かつ\(\textrm{Red}(N')_{1,j_0^{N'}} = R_{1,j_0^{N'}} = \textrm{Red}(L')_{1,j_0^{L'}}\)より\(t_3^{N'} = t_3^{L'}\)かつ\(t_4^{N'} = t_4^{L'}\)であるので、\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性より

\begin{eqnarray*}
\textrm{Trans}(N') & = & \textrm{Trans}(\textrm{Red}(N')) = s_1^{N'} c_2^{N'} b_1^{N'} = s_1^{N'} D_{v^{N'}}(t_3^{N'} + D_{\textrm{Red}(N')_{1,j_0^{N'}}}(t_4^{N'} + D_{\textrm{Red}(N')_{1.j_1^{N'}}} 0)) b_1^{N'} \\
& = & s_1^{N'} D_{v^{N'}}(t_3^{N'} + D_{R_{1,j_0^{N'}}}(t_4^{N'} + D_{N'_{1,j_1^{N'}}} 0)) b_1^{N'} = s_1^{N'} D_{v^{N'}}(t_3^{N'} + D_{R_{1,j_0^{N'}}}(t_4^{N'} + D_{M_{1,j_1}} 0)) b_1^{N'} \\
\textrm{Trans}(L') & = & \textrm{Trans}(\textrm{Red}(L')) = s_1^{L'} c_2^{L'} b_1^{L'} = s_1^{L'} D_{v^{L'}}(t_3^{L'} + D_{\textrm{Red}(L')_{1,j_0^{L'}}}(t_4^{L'} + D_{\textrm{Red}(L')_{1,j_1^{L'}}} 0)) b_1^{L'} \\
& = & s_1^{N'} D_{v^{N'}}(t_3^{N'} + D_{R_{1,j_0^{N'}}}(t_4^{N'} + D_{L'_{1,j_1^{N'}}} 0)) b_1^{N'} = s_1^{N'} D_{v^{N'}}(t_3^{N'} + D_{R_{1,j_0^{N'}}}(t_4^{N'} + D_{N'_{1,0}} 0)) b_1^{N'} \\
& = & s_1^{N'} D_{v^{N'}}(t_3^{N'} + D_{R_{1,j_0^{N'}}}(t_4^{N'} + D_{M_{1,j_{-2}}} 0)) b_1^{N'} \\
\end{eqnarray*}

であるので、scb分解の合成則と加法とscb分解の関係より一意な\((s,b) \in (\Sigma^{< \omega})^2\)が存在して\((s,D_{M_{1,j_1}} 0,b)\)と\((s,D_{M_{1,j_{-2}}} 0,b)\)はそれぞれ\(\textrm{Trans}(N')\)と\(\textrm{Trans}(L')\)のscb分解である。□

補題（条件(III)～(VI)の下での展開規則の基本性質）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)を満たす一意な\(j_{-2} \in \mathbb{N}\)が存在するとし\(N' := (M_j)_{j=j_{-2}}^{j_1}\)と置き、\(L' := (M'_j)_{j=j_{-2}}^{j_1}\)と置き、各\(n \in \mathbb{N}_{+}\)に対し\(L_n := M[n] \oplus_{\mathbb{N}^2} ((M_{0,j_{-2}}+n(M_{0,j_1}-M_{0,j_{-2}}),M_{1,j_{-2}}))\)と置くと[73]、\(j_1 > 1\)[74]ならば以下が成り立つ：

(1) \(M\)が条件(III)か(IV)を満たすならば\(j_{-2} < j_0\)であり、\(M\)が条件(V)か(VI)を満たすならば\(j_{-2} = j_0\)である。

(2) 任意の\(n \in \mathbb{N}_{+}\)に対し、\(L_n\)は簡約かつ単項である。

(3) \(\leq_M\)と\(\leq_{L_1}\)の\((\{0,1\} \times \mathbb{N}) \setminus \{(1,j_1)\}\)への制限は一致する。

(4) 「\(M\)が(VI)を満たすかまたは\(j_0\)が\(M\)許容である」ならば\(L_1\)は条件(I)か(III)を満たし、「\(M\)が(VI)を満たさずかつ\(j_0\)が非\(M\)許容である」ならば\(L_1\)は条件(II)か(IV)を満たす[75]。

(5) 任意の\(n \in \mathbb{N}_{+}\)に対し、\(n > 1\)ならば一意な\((s',b') \in (\Sigma^{< \omega})^2\)が存在して以下を満たす：

(5-1) \((s',D_{M_{1,j_{-2}}} 0,b')\)は\(\textrm{Trans}(L_{n-1})\)のscb分解である。

(5-2) \((s',\textrm{Trans}(L'),b')\)は\(\textrm{Trans}(L_n)\)のscb分解である。

(5-3) \((s',\textrm{Trans}(\textrm{Pred}(N')),b')\)は\(\textrm{Trans}(M[n])\)のscb分解である。

証明：

(1)

\(M\)が条件(III)か(IV)を満たすならば、\(M_{1,j_0} \geq M_{1,j_1}\)であるので\((1,j_0) \leq_M (1,j_1)\)でなく、従って\(j_{-2} < j_0\)である。

\(M\)が条件(V)か(VI)を満たすならば、\(M_{1,j_0} < M_{1,j_1}\)であるので\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)であり、従って\(j_{-2} = j_0\)である。

(2)

標準形の簡約性より\(M\)は簡約であり、簡約性が基本列で保たれることから\(M[n+1]\)は簡約である。\(M_{1,j_1} > M_{1,j_{-2}} > 0\)と非複項性と基本列の関係 (2)より\(M[n+1]\)は単項である。更に

\begin{eqnarray*}
L_n = M[n] \oplus_{\mathbb{N}^2} ((M_{0,j_1},M_{1,j_{-2}})) = M[n] \oplus_{\mathbb{N}^2} ((M_{0,j_1},M_{1,j_1}-1)) = (M[n+1]_j)_{j=0}^{j_{-2}+n(j_1-j_{-2})}
\end{eqnarray*}

であるので、簡約性の切片への遺伝性と単項性の始切片への遺伝性より\(L_n\)は簡約かつ単項である。

(3)

\(L_1 = M[1] \oplus_{\mathbb{N}^2} (M_{0,j_1},M_{0,j_{-2}}) = \textrm{Pred}(M) \oplus_{\mathbb{N}^2} (M_{0,j_1},M_{0,j_{-2}})\)であるので、\(\leq_M\)と\(\leq_{L_1}\)の\((\{0,1\} \times \mathbb{N}) \setminus \{(1,j_1)\}\)への制限は一致する。特に\((0,j_0) <_{L_1}^{\textrm{Next}} (0,j_1)\)である。

\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(L_1\)に対しても定め、\(L_1\)に対する適用であることを明示するために右肩に\(L_1\)を乗せて表記する。

\(\textrm{Pred}(L_1) = \textrm{Pred}(M)\)より\(t_1^{L_1} = t_1 \neq 0\)であるので\(L_1\)に対して条件(I)～(VI)が意味を持つ。

\((0,j_0) <_{L_1}^{\textrm{Next}} (0,j_1)\)かつ\(L_{1,j_0} = M_{1,j_0} = L_{1,j_1}\)より\(L_1\)は条件(V)と(VI)のいずれも満たさない。

\(M\)が条件(VI)を満たすとする。

\(j_0+1 = j_1\)である。\(L_{1,j_0} = L_{1,j_1} = L_{1,j_0+1}\)であるので\((1,j_0) <_{L_1}^{\textrm{Next}} (1,j_0+1)\)でない。従って\(j_0\)は\(L_1\)許容である。

以上より、\(L_1\)は条件(I)か(III)を満たす。

\(j_0\)が\(M\)許容であるとする。

\(j_0\)が\(M\)許容であることから、\((0,j_0) <_M^{\textrm{Next}} (0,j_0+1)\)でないかまたは\(M_{1,j_0} \geq M_{1,j_0+1}\)である。

\((0,j_0) <_M^{\textrm{Next}} (0,j_0+1)\)でないならば、\((0,j_0) <_{L_1}^{\textrm{Next}} (0,j_0+1)\)でないので\(j_0\)は\(L_1\)許容である。

\(M_{1,j_0} \geq M_{1,j_0+1}\)ならば、\(j_0 < j_1\)より\(L_{1,j_0} = M_{1,j_0} \geq M_{1,j_1} \geq L_{1,j_1}\)であるので\(j_0\)は\(L_1\)許容である。

従っていずれの場合も\(j_0\)は\(L_1\)許容である。

以上より、\(L_1\)は条件(I)か(III)を満たす。

\(M\)が(VI)を満たさずかつ\(j_0\)が非\(M\)許容であるとする。

\(j_0\)が非\(M\)許容であることから\((1,j_0-1) <_M^{\textrm{Next}} (1,j_0) <_M^{\textrm{Next}} (1,j_0+1)\)である。

\(M_{1,j_1} > M_{1,j_{-2}} \geq 0\)より\(M\)は条件(I)と(II)のいずれも満たさない。従って\(M\)は条件(IV)か(V)を満たすので\(M_{1,j_0}+1 \geq M_{1,j_1}\)となり、\(L_{1,j_0} = M_{1,j_0} \geq M_{1,j_1}-1 = L_{1,j_1}\)となる。

\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)でない。従って\(j_0+1 < j_1\)となるので、\((1,j_0-1) <_{L_1}^{\textrm{Next}} (1,j_0) <_{L_1}^{\textrm{Next}} (1,j_0+1)\)である。従って\(j_0\)は非\(L_1\)許容である。

以上より\(L_1\)は条件(II)か(IV)を満たす。□

(5)

\(\textrm{Lng}(L_n)-1 = j_{-2}+n(j_1-j_{-2})\)である。

\(j_{-2}+(n-1)(j_1-j_{-2})\)が非\(L_n\)許容であると仮定し矛盾を導く。

\(j_{-2}+(n-1)(j_1-j_{-2})\)が非\(L_n\)許容より\((1,j_{-2}+(n-1)(j_1-j_{-2})-1) <_{L_n}^{\textrm{Next}} (1,j_{-2}+(n-1)(j_1-j_{-2}))\)であるので、

\begin{eqnarray*}
& & M_{0,j_1-1} = (L_n)_{0,j_{-2}+(n-1)(j_1-j_{-2})-1}-(n-2)(M_{0,j_1}-M_{0,j_{-2}}) \\
& < & (L_n)_{0,j_{-2}+(n-1)(j_1-j_{-2})}-(n-2)(M_{0,j_1}-M_{0,j_{-2}}) \\
& = & (M_{0,j_{-2}}+(n-1)(M_{0,j_1}-M_{0,j_{-2}}))-(n-2)(M_{0,j_1}-M_{0,j_{-2}}) = M_{0,j_1}
\end{eqnarray*}

かつ\(M_{1,j_1-1} = (L_n)_{1,j_{-2}+(n-1)(j_1-j_{-2})-1} < (L_n)_{1,j_{-2}+(n-1)(j_1-j_{-2})} = M_{1,j_{-2}} < M_{1,j_1}\)である。

\(M_{0,j_1-1} < M_{0,j_1}\)かつ\(M_{1,j_1-1} < M_{1,j_{-2}} < M_{1,j_1}\)より\((1,j_1-1) <_M^{\textrm{Next}} (1,j_1)\)すなわち\(j_{-2} = j_1-1\)となるが、これは\(M_{1,j_1-1} < M_{1,j_{-2}}\)に矛盾する。

以上より、\(j_{-2}+(n-1)(j_1-j_{-2})\)は\(L_n\)許容である。更に\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)より\((0,j_{-2}) \leq_M (0,j_1)\)であるので、\((0,j_{-2}+(n-1)(j_1-j_{-2})) \leq_{L_n} (0,j_{-2}+n(j_1-j_{-2}))\)である。従って\((L_n,j_{-2}+(n-1)(j_1-j_{-2})) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。

\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示より

\begin{eqnarray*}
\textrm{Mark}(L_n,j_{-2}+(n-1)(j_1-j_{-2})) = \textrm{Trans}(((L_n)_j)_{j=j_{-2}+(n-1)(j_1-j_{-2})}^{j_{-2}+n(j_1-j_{-2})}) = \textrm{Trans}(L')
\end{eqnarray*}

であるので、\(((L_n)_j)_{j=0}^{j_{-2}+(n-1)(j_1-j_{-2})} = L_{n-1}\)と\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より一意な\((s',b') \in (\Sigma^{< \omega})^2\)が存在して以下を満たす：

(1) \((s',D_{M_{1,j_{-2}}} 0,b')\)は\(\textrm{Trans}(L_{n-1})\)のscb分解である。

(2) \((s',\textrm{Trans}(L'),b')\)は\(\textrm{Trans}(L_n)\)のscb分解である。

\(j_{-2}+(n-1)(j_1-j_{-2})\)が\(L_n\)許容であり\(j_{-2}+(n-1)(j_1-j_{-2}) < j_{-2}+n(j_1-j_{-2})\)かつ\(M[n] = \textrm{Pred}(L_n)\)であることから、基点の切片への遺伝性より\((M[n],j_{-2}+(n-1)(j_1-j_{-2})) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。

簡約性が基本列で保たれることから\(M[n]\)は簡約であるので、\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示より

\begin{eqnarray*}
\textrm{Mark}(M[n],j_{-2}+(n-1)(j_1-j_{-2})) = \textrm{Trans}(((M[n])_j)_{j=j_{-2}+(n-1)(j_1-j_{-2})}^{j_{-2}+n(j_1-j_{-2})}) = \textrm{Trans}(\textrm{Pred}(N'))
\end{eqnarray*}

である。従って\(((M[n])_j)_{j=0}^{j_{-2}+(n-1)(j_1-j_{-2})} = L_{n-1}\)と\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より、\((s',\textrm{Trans}(\textrm{Pred}(N')),b')\)は\(\textrm{Trans}(M[n])\)のscb分解である。□

補題（条件(III)～(VI)の下での\(\textrm{Trans}\)とscb分解の関係）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置いて\(j_1 > 1\)とし、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)を満たす一意な\(j_{-2} \in \mathbb{N}\)が存在するとし、\(j_{-3} := \textrm{Adm}_M(j_{-2})\)と置き、\(N := (M_j)_{j=j_{-3}}^{j_1}\)と置くと、一意な\((s',b') \in (\Sigma^{< \omega})^2\)が存在して\((s',\textrm{Trans}(N),b')\)は\(\textrm{Trans}(M)\)の第\(1\)種scb分解である。

証明：

\((0,j_{-3}) \leq_M (0,j_{-2}) \leq_M (0,j_1)\)かつ\(j_{-3}\)は\(M\)許容であるので、\((M,j_{-3}) \in T_{\textrm{PS}}^{\textrm{Marked}}\)である。

\(N := (M_j)_{j=j_{-3}}^{j_1}\)と置く。

\((0,j_{-3}) \leq_M (0,j_{-2})\)かつ\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)より\(j_{-3} < j_1\)かつ\((0,j_{-3}) \leq_M (0,j_{-2}) \leq_M (0,j_1)\)である。

\((M,j_{-3}) \in T_{\textrm{PS}}^{\textrm{Marked}}\)より、一意な\((s',b') \in (\Sigma^{< \omega})^2\)が存在して\((s',\textrm{Mark}(M,j'_{-2}),b')\)は\(\textrm{Trans}(M)\)のscb分解である。

\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示より\((s',\textrm{Trans}(N),b')\)は\(\textrm{Trans}(M)\)のscb分解である。

\((0,j'_{-2}) \leq_M (0,j_1)\)と単項性の直系先祖による切片への遺伝性から、\(N\)は単項である。従って\(\textrm{Red}\)が単項性を保つことより\(\textrm{Red}(N)\)は簡約かつ単項である。

\((0,j'_{-2}) \leq_M (0,j_1)\)より\((0,0) \leq_N (0,j_1-j'_{-2})\)であり、直系先祖の\(\textrm{Red}\)不変性より\((0,0) \leq_{\textrm{Red}(N)} (0,j_1-j'_{-2})\)である。

\((0,0) \leq_{\textrm{Red}(N)} (0,j_1-j'_{-2})\)かつ\(0\)が\(\textrm{Red}(N)\)許容であることから、一意な\(J_1 \in \mathbb{N}\)と\(n \in \mathbb{N}_M^{< \omega}\)が存在して以下を満たす：

\(\textrm{Lng}(n) = J_1+1\)である。

\(n_0 = 0\)である。

<<<MISSING line 4533 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4534 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4535 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4536 — recover from original.html via tools/make_content.py>>>
任意の\(J \in \mathbb{N}\)に対し、\(0 < J < J_1\)ならば、\(n_J+j'_{-2} > n_0+j'_{-2} = j'_{-2} \geq j_{-2}\)であり、\((0,n_J) \leq_{\textrm{Red}(N)} (0,n_{J_1}) = (0,j_1-j'_{-2})\)と直系先祖の\(\textrm{Red}\)不変性より\((0,n_J) \leq_N (0,j_1-j'_{-2})\)すなわち\((0,n_J+j'_{-2}) \leq_M (0,j_1)\)であるので、\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)と親の基本性質 (2)より\(M_{1,n_J+j'_{-2}} \geq M_{1,j_1}\)である。
<<<MISSING line 4538 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4539 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4540 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4541 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4542 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4543 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4544 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4545 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4546 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4547 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4548 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4549 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4550 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4551 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4552 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4553 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4554 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4555 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4556 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4557 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4558 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4559 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4560 — recover from original.html via tools/make_content.py>>>
直系先祖による切片と\(\textrm{Red}\)と\(\textrm{IncrFirst}\)の関係より\(\textrm{IncrFirst}^{N_{0,0}-N_{1,0}}(\textrm{Red}(N)) = N\)であるので、特に任意の\(j \in \mathbb{N}\)に対し\(j \leq j_1-j_{-3}\)ならば\(\textrm{Red}_{1,j} = N_{1,j} = M_{1,j+j_{-3}}\)である。
<<<MISSING line 4562 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4563 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4564 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4565 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4566 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4567 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4568 — recover from original.html via tools/make_content.py>>>
\((0,n'_{J'}) <_{\textrm{Red}(N)}^{\textrm{Next}} (0,n_J)\)と直系先祖の\(\textrm{Red}\)不変性より\(n'_{J'} < n_J\)かつ\((0,n'_{J'}) <_N^{\textrm{Next}} (0,n_J)\)すなわち\((0,n'_{J'}+j_{-3}) <_M^{\textrm{Next}} (0,n_J+j_{-3}) \leq_M (0,j_1)\)である。
<<<MISSING line 4570 — recover from original.html via tools/make_content.py>>>
\((0,j_{-2}) \leq_M (0,j_1)\)より\((0,j_{-2}-j_{-3}) \leq_N (0,j_1-j_{-3})\)であり、直系先祖の\(\textrm{Red}\)不変性より\((0,j_{-2}-j_{-3}) \leq_{\textrm{Red}(N)} (0,j_1-j_{-3})\)である。
<<<MISSING line 4572 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4573 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4574 — recover from original.html via tools/make_content.py>>>
\((0,n'_{J'}) <_{\textrm{Red}(N)}^{\textrm{Next}} (0,n_J) \leq_{\textrm{Red}(N)} (0,n_{J_1}) = (0,j_1-j_{-3})\)と直系先祖の\(\textrm{Red}\)不変性より\((0,n'_{J'}) <_N^{\textrm{Next}} (0,n_J) \leq_N (0,j_1-j_{-3})\)すなわち\((0,n'_{J'}+j_{-3}) <_M^{\textrm{Next}} (0,n_J+j_{-3}) \leq_M (0,j_1)\)である。
<<<MISSING line 4576 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4577 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4578 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4579 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4580 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4581 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4582 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4583 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4584 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4585 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4586 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4587 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4588 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4589 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4590 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4591 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4592 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4593 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4594 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4595 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4596 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4597 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4598 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4599 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4600 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4601 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4602 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4603 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4604 — recover from original.html via tools/make_content.py>>>
補題（条件(III)～(V)の下での切片のscb分解）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)を満たす一意な\(j_{-2} \in \mathbb{N}\)が存在するとし\(N' := (M_j)_{j=j_{-2}}^{j_1}\)と置くと、\(M\)が条件(VI)を満たさずかつ\(\textrm{Adm}_M(j_{-2}) = j_{-1}\)ならば、一意な\((s'_1,b'_1) \in (\Sigma^{< \omega})^2\)が存在して以下を満たす：

(1) \((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(c_2\)のscb分解である。

(2) \((D_{M_{1,j_{-2}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(\textrm{Trans}(N')\)のscb分解である。

(3) \(\textrm{Trans}(\textrm{Pred}(N')) = D_{M_{1,j_{-2}}} t_2\)である。

証明：

以下では条件(III)～(VI)の下での展開規則の基本性質を断りなく用いる。

(1)

標準形の簡約性より\(M\)は簡約である。

右端第\(1\)基点のMarkの基本性質から\(\textrm{Mark}(M,j_1) = D_{M_{1,j_1}} 0\)であり、右端第\(2\)基点のMarkの基本性質から\(\textrm{Mark}(M,j_{-1}) = c_2\)である。

従って\(j_{-1} \leq j_0 < j_1\)とscb分解の自明性の判定条件と\(\textrm{Trans}\)の最左単項成分の左端の基本性質と\(\textrm{Mark}\)が順序関係を保つことから一意な\((s'_1,b'_1) \in (\Sigma^{< \omega})^2\)が存在して\((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(c_2\)のscb分解である。

(2)

\(N := (M_j)_{j=j_{-1}}^{j_1}\)と置く。

\((0,j_{-1}) \leq_M (0,j_0) <_M^{\textrm{Next}} (0,j_1)\)と標準形の直系先祖による切片の簡約化の強単項性から\(\textrm{Red}(N)\)は強単項である。

\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示から\(\textrm{Trans}(\textrm{Red}(N)) = \textrm{Trans}(N) = \textrm{Mark}(M,j_{-1}) = c_2\)である。

\(j_{-1} = \textrm{Adm}_M(j_{-2}) \leq j_{-2} \leq j_0\)である。許容化の切片への遺伝性より\(\textrm{Adm}_N(j_{-2}-j_{-1}) = \textrm{Adm}_M(j_{-2})-j_{-1} = 0\)かつ\(\textrm{Adm}_N(j_0-j_{-1}) = \textrm{Adm}_M(j_0)-j_{-1} = 0\)であり、許容化の\(\textrm{Red}\)不変性から\(\textrm{Adm}_{\textrm{Red}(N)}(j_{-2}-j_{-1}) = 0\)かつ\(\textrm{Adm}_{\textrm{Red}(N)}(j_0-j_{-1}) = 0\)である。従って\(j_{-2}-j_{-1} \leq j_0-j_{-1} \leq \textrm{TrMax}(\textrm{Red}(N))\)である。

\(M\)が条件(III)か(IV)を満たすならば、\(M_{1,j_0} \geq M_{1,j_1}\)より\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)でなく、従って\(j_{-2} < j_0 < j_1\)となるので\(j_{-2} < j_1-1\)であり、特に\((1,j_1-1) <_M^{\textrm{Next}} (1,j_1)\)でない。

\(M\)が条件(V)を満たすならば、\(j_0 < j_1-1\)より\((0,j_1-1) <_M^{\textrm{Next}} (0,j_1)\)でなく、特に\((1,j_1-1) <_M^{\textrm{Next}} (1,j_1)\)でない。

従って、いずれの場合も\((1,j_1-1) <_M^{\textrm{Next}} (1,j_1)\)でない。

\(J_1 := \textrm{Lng}(\textrm{Br}(\textrm{Red}(N)))\)と置く。

\((1,j_1-1) \leq_M (1,j_1)\)でないので、\((1,j_1-1-j_{-1}) \leq_N (1,j_1-j_{-1})\)でない。直系先祖の\(\textrm{Red}\)不変性より\((1,j_1-1-j_{-1}) \leq_{\textrm{Red}(N)} (1,j_1-j_{-1})\)でないので、\(\textrm{TrMax}(\textrm{Red}(N)) < j_1-j_{-1}\)である。従って\(J_1 \geq 0\)である。

\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)より\((0,j_0-j_{-1}) <_N^{\textrm{Next}} (0,j_1-j_{-1})\)であり、直系先祖の\(\textrm{Red}\)不変性より\((0,j_0-j_{-1}) <_{\textrm{Red}(N)}^{\textrm{Next}} (0,j_1-j_{-1})\)である。

\((0,j_0-j_{-1}) <_{\textrm{Red}(N)}^{\textrm{Next}} (0,j_1-j_{-1})\)かつ\(j_0-j_{-1} \leq \textrm{TrMax}(\textrm{Red}(N)) < j_1-j_{-1}\)より、\(P\)の各成分の非複項性から\(\textrm{FirstNodes}(\textrm{Red}(N))_{J_1} = j_1-j_{-1}\)かつ\(\textrm{Joints}(\textrm{Red}(N))_{J_1} = j_0-j_{-1}\)となる。

\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)より\((1,j_{-2}-j_{-1}) <_N^{\textrm{Next}} (1,j_1-j_{-1})\)であり、直系先祖の\(\textrm{Red}\)不変性より\((1,j_{-2}-j_{-1}) <_{\textrm{Red}(N)}^{\textrm{Next}} (1,j_1-j_{-1})\)である。

\(M\)が条件(III)か(IV)を満たすならば、\(j_{-2} < j_0\)より\(j_{-2}-j_{-1} < j_0-j_{-1} = \textrm{Joints}(\textrm{Red}(N))_{J_1}\)である。

\(M\)が条件(V)を満たすとする。

\(M_{1,j_0} < M_{1,j_0}+1 = M_{1,j_1}\)より\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)であるので\(j_{-2} = j_0\)である。特に\(\textrm{FirstNodes}\)と\(\textrm{TrMax}\)と\(\textrm{Joints}\)の関係から\(j_{-2}-j_{-1} = j_0-j_{-1} = \textrm{Joints}(\textrm{Red}(N))_{J_1} \leq \textrm{TrMax}(\textrm{Red}(N))\)である。

簡約性と係数の関係から\(\textrm{Red}(N)\)は条件(A)と(B)を満たす。\(\textrm{Red}(N)\)が条件(A)と(B)を満たすことと\(j_{-2}-j_1  \leq \textrm{TrMax}(\textrm{Red}(N))\)から\(\textrm{Red}(N)_{0,j_{-2}-j_{-1}} = \textrm{Red}(N)_{1,j_{-2}-j_{-1}}\)である。\(\textrm{Red}(N)\)が条件(A)を満たすことと\((1,j_{-2}-j_{-1}) <_{\textrm{Red}(N)}^{\textrm{Next}} (1,j_1-j_{-1})\)より\(\textrm{Red}(N)_{0,j_1-j_{-1}} = \textrm{Red}(N)_{0,j_{-2}-j_{-1}}+1 = \textrm{Red}(N)_{1,j_{-2}-j_{-1}}+1 = \textrm{Red}(N)_{1,j_1-j_{-1}}\)である。

\(\textrm{Red}(N)\)が強単項であることから、\(\textrm{Br}(\textrm{Red}(N))\)は降順である。

以上より、「\(j_{-2}-j_{-1} < \textrm{Joints}(\textrm{Red}(N))_{J_1}\)」または「\(j_{-2}-j_{-1} = \textrm{Joints}(\textrm{Red}(N))_{J_1}\)かつ\(\textrm{Red}(N)_{0,j_1-j_{-1}} = \textrm{Red}(N)_{1,j_1-j_{-1}}\)かつ\(\textrm{Br}(\textrm{Red}(N))\)が降順」である。

従って\((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)が\(\textrm{Trans}(\textrm{Red}(N)) = c_2\)のscb分解であることと\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と条件(V)の下での終切片と\(\textrm{Trans}\)の関係から\((D_{M_{1,j_{-2}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(\textrm{Trans}(N')\)のscb分解である。

(3)

簡約性の切片への遺伝性と単項性の始切片への遺伝性より\(\textrm{Pred}(\textrm{Red}(N))\)は簡約かつ単項である。また\(\textrm{Red}\)と\(\textrm{Pred}\)の可換性より\(\textrm{Red}(\textrm{Pred}(N)) = \textrm{Pred}(\textrm{Red}(N))\)である。

\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示から

\begin{eqnarray*}
\textrm{Trans}(\textrm{Pred}(\textrm{Red}(N))) & = & \textrm{Trans}(\textrm{Red}(\textrm{Pred}(N))) = \textrm{Trans}(\textrm{Pred}(N)) \\
& = & \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = c_1 = D_{M_{1,j_{-1}}} t_2
\end{eqnarray*}

である。

簡約性と係数の関係より\(M\)は条件(A)と(B)を満たすので、\(j_{-2}-j_{-1} < j_0-j_{-1} \leq \textrm{TrMax}(\textrm{Red}(N)) = \textrm{TrMax}(N)\)より\(N_{0,0}-N_{1,0} = N_{0,j_{-2}-j_{-1}}-N_{1,j_{-2}-j_{-1}} = N'_{0,0}-N'_{1,0}\)である。

直系先祖による切片と\(\textrm{Red}\)と\(\textrm{IncrFirst}\)の関係より\(\textrm{IncrFirst}^{N_{0,0}-N_{1,0}}(\textrm{Red}(\textrm{Pred}(N))) = \textrm{Pred}(N)\)かつ\(\textrm{IncrFirst}^{N'_{0,0}-N'_{1,0}}(\textrm{Red}(\textrm{Pred}(N'))) = \textrm{Pred}(N')\)であるので、\((\textrm{Pred}(N)_j)_{j=j_{-2}-j_{-1}}^{j_1-1-j_{-1}} = \textrm{Pred}(N')\)より\((\textrm{Red}(\textrm{Pred}(N))_j)_{j=j_{-2}-j_{-1}}^{j_1-1-j_{-1}} = \textrm{Red}(\textrm{Pred}(N'))\)である。

\(J_0 := \textrm{Lng}(\textrm{Br}(\textrm{Pred}(\textrm{Red}(N))))\)と置く。

\(\textrm{TrMax}(\textrm{Red}(N)) < j_1-1-j_{-1}\)とする。

\(\textrm{TrMax}(\textrm{Red}(N)) < j_1-1-j_{-1}\)より\(\textrm{TrMax}(\textrm{Pred}(\textrm{Red}(N))) = \textrm{TrMax}(\textrm{Red}(N))\)であるので、特に\(j_{-2}-j_{-1} < j_0-j_{-1} \leq \textrm{TrMax}(\textrm{Pred}(\textrm{Red}(N))) < j_1-j_{-1}\)である。従って\(J_0 \geq 0\)である。\(\textrm{Pred}\)が\([1]\)で表されることと\(P\)と基本列の関係から\(J_1-1 \leq J_0 \leq J_1\)である。

\((1,j_{-2}-j_{-1}) <_{\textrm{Red}(N)}^{\textrm{Next}} (1,j_1-j_{-1})\)と\((0,j_0-j_{-1}) <_{\textrm{Red}(N)}^{\textrm{Next}} (0,j_1-j_{-1})\)と直系先祖の木構造 (1)より\((0,j_{-2}-j_{-1}) \leq_{\textrm{Red}(N)} (0,j_0-j_{-1}) \leq_{\textrm{Red}(N)} (0,j_1-1-j_{-1})\)であるので、\((0,j_{-2}-j_{-1}) \leq_{\textrm{Pred}(\textrm{Red}(N))} (0,j_0-j_{-1}) \leq_{\textrm{Pred}(\textrm{Red}(N))} (0,j_1-1-j_{-1})\)である。

\((0,j_0-j_{-1}) \leq_{\textrm{Pred}(\textrm{Red}(N))} (0,j_1-1-j_{-1})\)かつ\(j_0-j_{-1} \leq \textrm{TrMax}(\textrm{Pred}(\textrm{Red}(N))) < j_1-1-j_{-1}\)より、\(P\)の各成分の非複項性から\(j_0-j_{-1} \leq \textrm{Joints}(\textrm{Pred}(\textrm{Red}(N)))_{J_0}\)である。特に\(j_{-2}-j_{-1} < j_0-j_{-1} \leq \textrm{Joints}(\textrm{Pred}(\textrm{Red}(N)))_{J_0}\)である。

従って\(\textrm{Trans}(\textrm{Red}(\textrm{Pred}(N))) = \textrm{Trans}(\textrm{Pred}(\textrm{Red}(N))) = D_{M_{1,j_{-1}}} t_2\)かつ\((\textrm{Red}(\textrm{Pred}(N))_j)_{j=j_{-2}-j_{-1}}^{j_1-1-j_{-1}} = \textrm{Red}(\textrm{Pred}(N'))\)であることと\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と条件(V)の下での終切片と\(\textrm{Trans}\)の関係から\(\textrm{Trans}(\textrm{Pred}(N')) = \textrm{Trans}(\textrm{Red}(\textrm{Pred}(N'))) = D_{M_{1,j_{-2}}} t_2\)である。

\(\textrm{TrMax}(\textrm{Red}(N)) = j_1-1-j_{-1}\)とする。

\(\textrm{TrMax}(\textrm{Red}(\textrm{Pred}(N))) = \textrm{TrMax}(\textrm{Pred}(\textrm{Red}(N))) = \textrm{TrMax}(\textrm{Red}(N)) = j_1-1-j_{-1}\)である。

従って\(\textrm{Trans}(\textrm{Red}(\textrm{Pred}(N))) = D_{M_{1,j_{-1}}} t_2\)かつ\((\textrm{Red}(\textrm{Pred}(N))_j)_{j=j_{-2}-j_{-1}}^{j_1-1-j_{-1}} = \textrm{Red}(\textrm{Pred}(N'))\)かつ\(j_{-2}-j_{-1} < j_0-j_{-1} \leq j_1-1-j_{-1}\)であることと\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質から\(\textrm{Trans}(\textrm{Pred}(N')) = \textrm{Trans}(\textrm{Red}(\textrm{Pred}(N'))) = D_{M_{1,j_{-2}}} t_2\)である。

補題（条件(III)～(V)の下での各種scb分解）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)を満たす一意な\(j_{-2} \in \mathbb{N}\)が存在するとし\(N' := (M_j)_{j=j_{-2}}^{j_1}\)と置き、\(L' := (M_j)_{j=j_{-2}}^{j_1-1} \oplus_{\mathbb{N}^2} ((M_{0,j_1},M_{1,j_{-2}}))\)と置き、\(L_n := M[n] \oplus_{\mathbb{N}^2} ((M_{0,j_{-2}}+n(M_{0,j_1}-M_{0,j_{-2}}),M_{1,j_{-2}}))\)と置くと[77]、\(M\)が条件(VI)を満たさずかつ「\(j_{-2} < j_0\)または\(j_0\)が\(M\)許容」かつ\(\textrm{Adm}_M(j_{-2}) = j_{-1}\)ならば、一意な\((s'_1,b'_1) \in (\Sigma^{< \omega})^2\)が存在して以下を満たす：

(1) \((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(c_2\)のscb分解である。

(2) \((D_{M_{1,j_{-2}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)と\((D_{M_{1,j_{-2}}} s'_1,D_{M_{1,j_{-2}}} 0,b'_1)\)はそれぞれ\(\textrm{Trans}(N')\)と\(\textrm{Trans}(L')\)のscb分解である。

(3) \(\textrm{Trans}(\textrm{Pred}(N')) = D_{M_{1,j_{-2}}} t_2\)である。

(4) \(\textrm{Trans}(L_n) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_{-2}}})^n 0 (b'_1)^n b_1\)である。

(5) \(\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_{-2}}})^{n-1} t_2 (b'_1)^{n-1} b_1\)である。

証明：

以下では条件(III)～(VI)の下での展開規則の基本性質を断りなく用いる。

条件(III)～(V)の下での切片のscb分解より一意な\((s'_1,b'_1) \in (\Sigma^{< \omega})^2\)が存在して以下を満たす：

(1) \((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(c_2\)のscb分解である。

(2) \((D_{M_{1,j_{-2}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(\textrm{Trans}(N')\)のscb分解である。
<<<MISSING line 4725 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4726 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4727 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4728 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4729 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4730 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4731 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4732 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4733 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4734 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4735 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4736 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4737 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4738 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4739 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4740 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4741 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4742 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4743 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4744 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4745 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4746 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4747 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4748 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4749 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4750 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4751 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4752 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4753 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4754 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4755 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4756 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4757 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4758 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4759 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4760 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4761 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4762 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4763 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4764 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4765 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4766 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4767 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4768 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4769 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4770 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4771 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4772 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4773 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4774 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4775 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4776 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4777 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4778 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4779 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4780 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4781 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4782 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4783 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4784 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4785 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4786 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4787 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4788 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4789 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4790 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4791 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4792 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4793 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4794 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4795 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4796 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4797 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4798 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4799 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4800 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4801 — recover from original.html via tools/make_content.py>>>
補題（条件(III)か(IV)の下での各種scb分解）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)を満たす一意な\(j_{-2} \in \mathbb{N}\)が存在するとし\(j_{-3} := \textrm{Adm}_M(j_{-2})\)と置き、\(N := (M_j)_{j=j_{-3}}^{j_1}\)と置き、\(N' := (M_j)_{j=j_{-2}}^{j_1}\)と置き、\(L' := (M_j)_{j=j_{-2}}^{j_1-1} \oplus_{\mathbb{N}^2} ((M_{0,j_1},M_{1,j_{-2}}))\)と置き、\(L_n := M[n] \oplus_{\mathbb{N}^2} ((M_{0,j_{-2}}+n(M_{0,j_1}-M_{0,j_{-2}}),M_{1,j_{-2}}))\)と置くと[78]、\(j_1 > 1\)かつ\(M\)が条件(III)か(IV)を満たし[79]かつ\(j_{-3} < j_{-1}\)ならば、一意な\((s'_0,s'_1,s'_2,b'_2,b'_1,b'_0) \in (\Sigma^{< \omega})^6\)が存在して以下を満たす：

(1) \((s'_0,\textrm{Trans}(N),b'_0)\)は\(\textrm{Trans}(M)\)のscb分解である。

(2) \((D_{M_{1,j_{-3}}} s'_1,c_1,b'_1)\)と\((D_{M_{1,j_{-3}}} s'_1,c_2,b'_1)\)はそれぞれ\(\textrm{Trans}(\textrm{Pred}(N))\)と\(\textrm{Trans}(N)\)のscb分解である。

(3) \((s'_2,D_{M_{1,j_1}} 0,b'_2)\)は\(c_2\)のscb分解である。

(4) \((D_{M_{1,j_{-2}}} s'_1,c_1,b'_1)\)と\((D_{M_{1,j_{-2}}} s'_1,c_2,b'_1)\)と\((D_{M_{1,j_{-2}}} s'_1 s'_2,D_{M_{1,j_{-2}}} 0,b'_2 b'_1)\)はそれぞれ\(\textrm{Trans}(\textrm{Pred}(N'))\)と\(\textrm{Trans}(N')\)と\(\textrm{Trans}(L')\)のscb分解である。

(5) \(\textrm{Trans}(L_n) = s'_0 D_{M_{1,j_{-3}}} (s'_1 s'_2 D_{M_{1,j_{-2}}})^n 0 (b'_2 b'_1)^n b'_0\)である。

(6) \(\textrm{Trans}(M[n]) = s'_0 D_{M_{1,j_{-3}}} (s'_1 s'_2 D_{M_{1,j_{-2}}})^{n-1} s'_1 c_1 b'_1 (b'_2 b'_1)^{n-1} b'_0\)である。

証明：

以下では条件(III)～(VI)の下での展開規則の基本性質を断りなく用いる。

(1)

\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示から\(\textrm{Trans}(N) = \textrm{Mark}(M,j_{-3})\)であるので、一意な\((s'_0,b'_0) \in (\Sigma^{< \omega})^2\)が存在して\((s'_0,\textrm{Trans}(N),b'_0)\)は\(\textrm{Trans}(M)\)のscb分解である。

(2)

標準形の簡約性より\(M\)は簡約である。

\(j_{-3} < j_{-1}\)とscb分解の自明性の判定条件と\(\textrm{Trans}\)の最左単項成分の左端の基本性質と\(\textrm{Mark}\)が順序関係を保つことから一意な\((s'_1,b'_1) \in (\Sigma^{< \omega})^2\)が存在して\((D_{M_{1,j_{-3}}} s'_1,c_2,b'_1)\)は\(\textrm{Trans}(N)\)のscb分解である。

\(\textrm{Trans}\)の\(\textrm{Mark}\)と\(\textrm{Pred}\)による表示より\((D_{M_{1,j_{-3}}} s'_1,c_1,b'_1)\)は\(\textrm{Trans}(\textrm{Pred}(N))\)のscb分解である。

(3)

右端第\(1\)基点のMarkの基本性質と\(\textrm{Mark}\)が順序関係を保つことから一意な\((s'_2,b'_2) \in (\Sigma^{< \omega})^2\)が存在して\((s'_2,D_{M_{1,j_1}} 0,b'_2) = (s'_2,\textrm{Mark}(M,j_1),b'_2)\)は\(c_2\)のscb分解である。

(4)

\((1,j_{-3}) \leq_M (1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)と標準形の直系先祖による切片の簡約化の強単項性から\(\textrm{Red}(N)\)は強単項である。簡約性と係数の関係より\(\textrm{Red}(N)\)は条件(A)と(B)を満たす。

<<<MISSING line 4842 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4843 — recover from original.html via tools/make_content.py>>>
\(M\)が条件(III)か(IV)を満たすことから\(M_{1,j_0} \geq M_{1,j_1}\)であり、従って\((1,j_0) \leq_M (1,j_1)\)でなくすなわち\((1,j_0-j_{-3}) \leq_N (1,j_1-j_{-3})\)でない。直系先祖の\(\textrm{Red}\)不変性より\((1,j_0-j_{-3}) \leq_{\textrm{Red}(N)} (1,j_1-j_{-3})\)でないので、\(\textrm{TrMax}(\textrm{Red}(N)) < j_1-j_{-3}\)である。従って\(J_1 \geq 0\)である。
<<<MISSING line 4845 — recover from original.html via tools/make_content.py>>>
\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)かつ\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)より\((1,j_{-2}-j_{-3}) <_N^{\textrm{Next}} (1,j_1-j_{-3})\)かつ\((0,j_0-j_{-3}) <_N^{\textrm{Next}} (0,j_1-j_{-3})\)であり、直系先祖の\(\textrm{Red}\)不変性より\((1,j_{-2}-j_{-3}) <_{\textrm{Red}(N)}^{\textrm{Next}} (1,j_1-j_{-3})\)かつ\((0,j_0-j_{-3}) <_{\textrm{Red}(N)}^{\textrm{Next}} (0,j_1-j_{-3})\)である。
<<<MISSING line 4847 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4848 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4849 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4850 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4851 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4852 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4853 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4854 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4855 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4856 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4857 — recover from original.html via tools/make_content.py>>>
\(j_{-2}-j_{-3} = m_0\)ならば、\(\textrm{Red}(N)_{0,m_1} = \textrm{Red}(N)_{1,m_1}\)かつ\(\textrm{Br}(\textrm{Red}(N))\)が降順であることを示す。
<<<MISSING line 4859 — recover from original.html via tools/make_content.py>>>
\(\textrm{Red}(N)\)が強単項であるので、\(\textrm{Br}(\textrm{Red}(N))\)は降順である。
<<<MISSING line 4861 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4862 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4863 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4864 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4865 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4866 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4867 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4868 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4869 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4870 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4871 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4872 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4873 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4874 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4875 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4876 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4877 — recover from original.html via tools/make_content.py>>>
\((1,j_0) \leq_M (1,j_1)\)でなくかつ\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)かつ\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)より\(j_{-2} < j_0 < j_1\)である。従って\(j_1-1-j_{-3} \geq j_0-j_{-3} > j_{-2}-j_{-3} \geq 0\)であるので、\(\textrm{Red}(N)\)の強単項性と強単項性の切片への遺伝性より\(\textrm{Pred}(\textrm{Red}(N))\)は強単項である。
<<<MISSING line 4879 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4880 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4881 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4882 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4883 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4884 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4885 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4886 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4887 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4888 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4889 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4890 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4891 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4892 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4893 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4894 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4895 — recover from original.html via tools/make_content.py>>>
\(m'_0 := \textrm{Joints}(\textrm{Pred}(\textrm{Red}(N)))_{J_0}\)と置く。
<<<MISSING line 4897 — recover from original.html via tools/make_content.py>>>
\(m'_1 := \textrm{FirstNodes}(\textrm{Pred}(\textrm{Red}(N)))_{J_0}\)と置く。
<<<MISSING line 4899 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4900 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4901 — recover from original.html via tools/make_content.py>>>
\(j_{-2}-j_{-3} = m'_0\)ならば、\(\textrm{Pred}(\textrm{Red}(N))_{0,m'_1} = \textrm{Pred}(\textrm{Red}(N))_{1,m'_1}\)かつ\(\textrm{Br}(\textrm{Pred}(\textrm{Red}(N)))\)が降順であることを示す。
<<<MISSING line 4903 — recover from original.html via tools/make_content.py>>>
\(\textrm{Pred}(\textrm{Red}(N))\)が強単項であるので、\(\textrm{Br}(\textrm{Pred}(\textrm{Red}(N)))\)は降順である。
<<<MISSING line 4905 — recover from original.html via tools/make_content.py>>>
\(\textrm{Pred}\)が\([1]\)で表されることと\(P\)と基本列の関係から\(J_1-1 \leq J_0 \leq J_1\)であるので、\(\textrm{FirstNodes}\)と\(\textrm{Joints}\)の単調性より
<<<MISSING line 4907 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4908 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4909 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4910 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4911 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4912 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4913 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4914 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4915 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4916 — recover from original.html via tools/make_content.py>>>
\(m'_1 \leq m_1\)と\(\textrm{Red}(N)_{0,m'_1} = \textrm{Red}(N)_{0,m_1}\)より、\(\textrm{Br}(\textrm{Red}(N))\)が降順であることから\(\textrm{Red}(N)_{1,m'_1} \geq \textrm{Red}(N)_{1,m_1} = \textrm{Red}(N)_{0,m_1} = \textrm{Red}(N)_{0,m'_1}\)である。一方で簡約性と係数の基本性質より\(\textrm{Red}(N)_{0,m'_1} \geq \textrm{Red}(N)_{1,m'_1}\)であるので、\(\textrm{Red}(N)_{0,m'_1} = \textrm{Red}(N)_{1,m'_1}\)すなわち\(\textrm{Pred}(\textrm{Red}(N))(N)_{0,m'_1} = \textrm{Pred}(\textrm{Red}(N))_{1,m'_1}\)である。
<<<MISSING line 4918 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4919 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4920 — recover from original.html via tools/make_content.py>>>
従って\((D_{M_{1,j_{-3}}} s'_1,c_1,b'_1)\)が\(\textrm{Trans}(\textrm{Pred}(N))\)のscb分解であることと\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と\(\textrm{Red}\)と\(\textrm{Pred}\)の可換性と条件(V)の下での終切片と\(\textrm{Trans}\)の関係から\((D_{M_{1,j_{-2}}} s'_1,c_1,b'_1)\)は\(\textrm{Trans}(\textrm{Pred}(N'))\)のscb分解である。
<<<MISSING line 4922 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4923 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4924 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4925 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4926 — recover from original.html via tools/make_content.py>>>
従って\((D_{M_{1,j_{-3}}} s'_1,c_1,b'_1)\)が\(\textrm{Trans}(\textrm{Pred}(N))\)のscb分解であることと\(\textrm{Red}\)と\(\textrm{Pred}\)の可換性と\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質から\((D_{M_{1,j_{-2}}} s'_1,c_1,b'_1)\)は\(\textrm{Trans}(\textrm{Pred}(N'))\)のscb分解である。
<<<MISSING line 4928 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4929 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4930 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4931 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4932 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4933 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4934 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4935 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4936 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4937 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4938 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4939 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4940 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4941 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4942 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4943 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4944 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4945 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4946 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4947 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4948 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4949 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4950 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4951 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4952 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4953 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4954 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4955 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4956 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4957 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4958 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4959 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4960 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4961 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4962 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4963 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4964 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4965 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4966 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4967 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4968 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4969 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4970 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4971 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4972 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4973 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4974 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4975 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4976 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4977 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4978 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4979 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4980 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4981 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4982 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4983 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4984 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4985 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4986 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4987 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4988 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4989 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4990 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4991 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4992 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4993 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4994 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4995 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4996 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4997 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4998 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 4999 — recover from original.html via tools/make_content.py>>>
補題（条件(III)か(IV)の下での基本列の基本性質）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)を満たす一意な\(j_{-2} \in \mathbb{N}\)が存在するとすると、\(j_1 > 1\)かつ\(M\)が条件(III)か(IV)を満たすならば[80]、以下が成り立つ：

(1) \(M[n] = M[n+1][1]^{j_1-j_{-2}}\)である。

(2) \(\textrm{Trans}(M)[n-1] = \textrm{Trans}(M[n+1][1]^{j_1-1-j_{-2}})\)である。

(3) ある\((s',c'_1,c'_2,b') \in (\Sigma^{< \omega})^4\)が存在し、以下を満たす；

(3-1) \(c'_1\)と\(c'_2\)は\(c'_1 < c'_2\)を満たす単項である。

(3-2) \((s',c'_1,b')\)は\(\textrm{Trans}(M[n])\)のscb分解である。

(3-2) \((s',c'_2,b')\)は\(\textrm{Trans}(M)[n]\)のscb分解である。

証明：

簡約性と係数の関係より\(M\)は条件(A)と(B)を満たす。\(M\)が条件(A)を満たすことから、\(M_{1,j_{-2}} = M_{1,j_1}-1\)である。

\(M\)が条件(III)か(IV)を満たすことから\(M_{1,j_0} \geq M_{1,j_1}\)であるので\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)でなく、従って\(j_{-2} < j_0\)である。

\(j_{-3} := \textrm{Adm}_M(j_{-2})\)と置く。

\(N := (M_j)_{j=j_{-3}}^{j_1}\)と置く。

\(N' := (M_j)_{j=j_{-2}}^{j_1}\)と置く。

\(L' := (M_j)_{j=j_{-2}}^{j_1-1} \oplus_{\mathbb{N}^2} ((M_{0,j_1},M_{1,j_{-2}}))\)と置く。

\(L_n := M[n] \oplus_{\mathbb{N}^2} ((M_{0,j_{-2}}+n(M_{0,j_1}-M_{0,j_{-2}}),M_{1,j_{-2}}))\)と置く[81]。

\(\textrm{Pred}\)が\([1]\)で表されることから、

\begin{eqnarray*}
<<<MISSING line 5035 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5036 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5037 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5038 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5039 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5040 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5041 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5042 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5043 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5044 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5045 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5046 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5047 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5048 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5049 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5050 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5051 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5052 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5053 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5054 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5055 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5056 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5057 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5058 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5059 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5060 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5061 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5062 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5063 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5064 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5065 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5066 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5067 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5068 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5069 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5070 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5071 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5072 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5073 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5074 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5075 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5076 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5077 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5078 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5079 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5080 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5081 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5082 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5083 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5084 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5085 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5086 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5087 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5088 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5089 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5090 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5091 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5092 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5093 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5094 — recover from original.html via tools/make_content.py>>>
定義から\((s',c'_1,b')\)と\((s',c'_2,b)\)はそれぞれ\(\textrm{Trans}(M[n])\)と\(\textrm{Trans}(L_n)\)のscb分解である。
<<<MISSING line 5096 — recover from original.html via tools/make_content.py>>>
\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示より\(\textrm{Trans}((M_j)_{j=j_{-1}}^{j_1}) = c_2 = D_{M_{1,j_{-1}}} s'_1 D_{M_{1,j_1}} 0 b'_1\)であるので、条件(III)～(VI)の下での\(\textrm{Trans}\)とscb分解の関係より\((s_1,D_{M_{1,j_{-1}}} s'_1 D_{M_{1,j_1}} 0 b'_1,b_1)\)は\(\textrm{Trans}(M)\)の第\(1\)種scb分解である。従ってscb分解と基本列の関係 (2)より
<<<MISSING line 5098 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5099 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5100 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5101 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5102 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5103 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5104 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5105 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5106 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5107 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5108 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5109 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5110 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5111 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5112 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5113 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5114 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5115 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5116 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5117 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5118 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5119 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5120 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5121 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5122 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5123 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5124 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5125 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5126 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5127 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5128 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5129 — recover from original.html via tools/make_content.py>>>
定義から\((s',c'_1,b')\)と\((s',c'_2,b')\)はそれぞれ\(\textrm{Trans}(M[n])\)と\(\textrm{Trans}(L_n)\)のscb分解である。
<<<MISSING line 5131 — recover from original.html via tools/make_content.py>>>
条件(III)～(VI)の下での\(\textrm{Trans}\)とscb分解の関係より\((s'_0,\textrm{Trans}((M_j)_{j=j_{-3}}^{j_1}),b'_0) = (s'_0,D_{M_{1,j_{-3}}} s'_1 s'_2 D_{M_{1,j_1}} 0 b'_2 b'_1,b'_0)\)は\(\textrm{Trans}(M)\)の第\(1\)種scb分解である。従ってscb分解と基本列の関係 (2)より
<<<MISSING line 5133 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5134 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5135 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5136 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5137 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5138 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5139 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5140 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5141 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5142 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5143 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5144 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5145 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5146 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5147 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5148 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5149 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 5150 — recover from original.html via tools/make_content.py>>>
## 条件(V)の下での展開規則[]

命題（条件(V)の下での\(\textrm{Trans}\)と基本列の交換関係）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\(j_0\)が\(M\)許容ならば\(m_n := n-1\)と置き、\(j_0\)が非\(M\)許容ならば\(m_n := n\)と置くと、\(j_1 > 1\)かつ\(M\)が条件(V)を満たすならば[82]、以下が成り立つ：

(1) \(\textrm{Trans}(M[n]) \leq \textrm{Trans}(M)[m_n]\)である。

(2) \(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

(3) \(\textrm{Trans}(M)[m_n] \leq \textrm{Trans}(M[n+1])\)である。

条件(V)の下での\(\textrm{Trans}\)と基本列の交換関係を証明するための準備としていくつかの補題を示す。

補題（条件(V)の下での\(\textrm{Joints}\)と\(\textrm{FirstNodes}\)と\(t_2\)の基本性質）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\(N := (M_j)_{j=j_{-1}}^{j_1}\)と置き、\(J_1 := \textrm{Lng}(\textrm{Br}(\textrm{Red}(N)))-1\)と置くと、\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)かつ\(j_0\)が非\(M\)許容でありかつ\(j_0 < j_1-1\)ならば以下が成り立つ：

(1) \(J_1 \geq 0\)かつ\(j_0-j_{-1} = \textrm{Joints}(\textrm{Red}(N))_{J_1}\)かつ\(\textrm{FirstNodes}(\textrm{Red}(N))_{J_1} = j_1-j_{-1}\)である。

(2) \(\textrm{Red}(N)_{0,j_1-j_{-1}} = \textrm{Red}(N)_{1,j_1-j_{-1}}\)である。

(3) \(t_2\)の各単項成分は\(D_{M_{1,j_1}} 0\)以上である。

証明：

標準形の簡約性より\(M\)は簡約である。\(j_0 < j_1-1\)より\(j_1 > j_0+1 \geq 1\)であるので\(\textrm{Pred}(M)\)は零項でない。特に\(\textrm{Trans}\)が零項性を保つことから\(t_1 \neq 0\)である。

従って\(M\)に対し条件(I)～(VI)が意味を持つ。

簡約性と係数の関係より\(M\)は条件(A)と(B)を満たす。\(M\)が条件(A)を満たしかつ\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)かつ\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)であることから\(M_{0,j_0} = M_{0,j_1}-1\)かつ\(M_{1,j_0} = M_{1,j_1}-1\)である。従って\(M\)は条件(V)を満たす。

\(N := (M_j)_{j=j_{-1}}^{j_1}\)と置く。

標準形の直系先祖による切片の簡約化の強単項性より\(\textrm{Red}(N)\)は強単項である。

\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と右端第\(2\)基点のMarkの基本性質と\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示から

\begin{eqnarray*}
D_v(t_2 + D_{M_{1,j_1}} 0) = c_2 = \textrm{Mark}(M,j_{-1}) = \textrm{Trans}(N) = \textrm{Trans}(\textrm{Red}(N))
\end{eqnarray*}

である。

\(J_1 := \textrm{Lng}(\textrm{Br}(\textrm{Red}(N)))-1\)と置く。

\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)かつ\(j_0 < j_1-1\)であるので\((1,j_1-1) <_M (1,j_1)\)でない。従って右端の非許容直系先祖の基本性質より\(J_1 \geq 0\)かつ\(0 < j_0-j_{-1} < \textrm{TrMax}(\textrm{Br}(\textrm{Red}(N)))\)かつ\(j_0-j_{-1} = \textrm{Joints}(\textrm{Red}(N))_{J_1}\)かつ\(\textrm{FirstNodes}(\textrm{Red}(N)) = j_1-j_{-1}\)である。

任意の\(i \in {0,1}\)に対し、\((i,j_0) <_M^{\textrm{Next}} (i,j_1)\)より\((i,j_0-j_{-1}) <_N^{\textrm{Next}} (i,j_1-j_{-1})\)であり、直系先祖の\(\textrm{Red}\)不変性から\((i,j_0-j_{-1}) <_{\textrm{Red}(N)}^{\textrm{Next}} (i,j_1-j_{-1})\)である。

簡約性と係数の関係より\(\textrm{Red}(N)\)は条件(A)と(B)を満たす。\(\textrm{Red}(N)\)が条件(A)と(B)を満たしかつ\(j_0-j_{-1} < \textrm{TrMax}(\textrm{Br}(\textrm{Red}(N)))\)であることから\(\textrm{Red}(N)_{0,j_0-j_{-1}} = \textrm{Red}(N)_{1,j_0-j_{-1}}\)であり、\(\textrm{Red}(N)\)が条件(A)を満たしかつ\((0,j_0-j_{-1}) <_{\textrm{Red}(N)}^{\textrm{Next}} (0,j_1-j_{-1})\)かつ\((1,j_0-j_{-1}) <_{\textrm{Red}(N)}^{\textrm{Next}} (1,j_1-j_{-1})\)であることから、

\begin{eqnarray*}
\textrm{Red}(N)_{0,j_1-j_{-1}} = \textrm{Red}(N)_{0,j_0-j_{-1}}+1 = \textrm{Red}(N)_{1,j_0-j_{-1}}+1 = \textrm{Red}(N)_{1,j_1-j_{-1}}
\end{eqnarray*}

である。

\(0 < j_0-j_{-1} < \textrm{TrMax}(\textrm{Br}(\textrm{Red}(N)))\)かつ\(\textrm{Red}(N)_{0,j_1-j_{-1}} = \textrm{Red}(N)_{1,j_1-j_{-1}}\)であるので、\(\textrm{Trans}(\textrm{Red}(N)) = D_v(t_2 + D_{M_{1,j_1}} 0)\)と強単項性の下での部分表現の単項成分の基本性質より\(t_2 + D_{M_{1,j_1}} 0\)の各単項成分は\(D_{\textrm{Red}(N)_{1,j_1-j_{-1}}} 0\)以上である。

直系先祖による切片と\(\textrm{Red}\)と\(\textrm{IncrFirst}\)の関係より\(\textrm{Red}(N)_{1,j_1} = M_{1,j_1}\)であるので、\(t_2\)の各単項成分は\(D_{M_{1,j_1}} 0\)以上である。□

補題（条件(V)の下での各種scb分解）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\(N' := (M_j)_{j=j_0}^{j_1}\)と置き、\(L' := (M_j)_{j=j_0}^{j_1-1} \oplus_{\mathbb{N}^2} ((M_{0,j_1},M_{1,j_0}))\)と置き、\(L_n := M[n] \oplus_{\mathbb{N}^2} ((M_{0,j_0}+n(M_{0,j_1}-M_{0,j_0}),M_{1,j_0}))\)と置くと[83]、\(j_1 > 1\)かつ\(M\)が条件(V)を満たし[84]かつ\(j_0\)が非\(M\)許容であるならば、一意な\((s'_1,b'_1) \in (\Sigma^{< \omega})^2\)が存在して以下を満たす：

(1) \((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(c_2\)のscb分解である。

(2) \((D_{M_{1,j_0}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)と\((D_{M_{1,j_0}} s'_1,D_{M_{1,j_0}} 0,b'_1)\)はそれぞれ\(\textrm{Trans}(N')\)と\(\textrm{Trans}(L')\)のscb分解である。

(3) \(\textrm{Trans}(\textrm{Pred}(N')) = D_{M_{1,j_0}} t_2\)である。

(4) \(\textrm{Trans}(L_n) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+1} 0 (b'_1)^{n+1} b_1\)である。

(5) \(\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n t_2 (b'_1)^n b_1\)である。

証明：

以下では条件(III)～(VI)の下での展開規則の基本性質を断りなく用いる。

\(M\)が条件(V)を満たすので\(M_{1,j_0} < M_{1,j_0}+1 = M_{1,j_1}\)である。従って\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)である。

条件(III)～(V)の下での切片のscb分解より一意な\((s'_1,b'_1) \in (\Sigma^{< \omega})^2\)が存在して以下を満たす：

(1) \((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(c_2\)のscb分解である。

(2) \((D_{M_{1,j_0}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(\textrm{Trans}(N')\)のscb分解である。

(3) \(\textrm{Trans}(\textrm{Pred}(N')) = D_{M_{1,j_0}} t_2\)である。

以上より(1)と(3)が従う。

(2)

\(N := (M_j)_{j=j_{-1}}^{j_1}\)と置く。

標準形の直系先祖による切片の簡約化の強単項性より\(\textrm{Red}(N)\)は強単項であるので、\(\textrm{Br}(\textrm{Red}(N))\)は降順である。

右端第\(2\)基点のMarkの基本性質と\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示から\(\textrm{Trans}(N) = \textrm{Mark}(M,j_{-1}) = c_2\)であるので、\((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(\textrm{Trans}(N)\)のscb分解である。

\(J_1 := \textrm{Lng}(\textrm{Br}(\textrm{Red}(N)))-1\)と置く。

\(M\)が条件(V)を満たすことから\(j_0+1 < j_1\)すなわち\(j_0 < j_1-1\)である。従って条件(V)の下での\(\textrm{Joints}\)と\(\textrm{FirstNodes}\)と\(t_2\)の基本性質より以下が成り立つ：

(1) \(J_1 \geq 0\)かつ\(j_0-j_{-1} = \textrm{Joints}(\textrm{Red}(N))_{J_1}\)かつ\(\textrm{FirstNodes}(\textrm{Red}(N))_{J_1} = j_1-j_{-1}\)である。

(2) \(\textrm{Red}(N)_{0,j_1-j_{-1}} = \textrm{Red}(N)_{1,j_1-j_{-1}}\)である。

\(\textrm{Red}(N)_{0,j_1-j_{-1}} = \textrm{Red}(N)_{1,j_1-j_{-1}}\)かつ\(\textrm{Br}(\textrm{Red}(N))\)が降順であるので、\((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(\textrm{Trans}(N)\)のscb分解であることと条件(V)の下での終切片と\(\textrm{Trans}\)の関係より\((D_{M_{1,j_0}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(\textrm{Trans}(N')\)のscb分解である。

\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)かつ\(L'_{j_1-j_0} = (M_{0,j_1},M_{1,j_0}) = (N'_{0,j_1-j_0},N'_{1,0})\)であることから、\((D_{M_{1,j_0}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)が\(\textrm{Trans}(N')\)のscb分解であることと条件(III)～(V)の下での右端の置き換えと\(\textrm{Trans}\)の関係より\((D_{M_{1,j_0}} s'_1,D_{M_{1,j_0}} 0,b'_1)\)は\(\textrm{Trans}(L')\)のscb分解である。

(4)

標準形の簡約性より\(M\)は簡約である。簡約性と係数の関係より\(M\)は条件(A)と(B)を満たす。\(M\)が条件(A)を満たしかつ\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)かつ\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)であることから\(M_{0,j_0} = M_{0,j_1}-1\)かつ\(M_{1,j_0} = M_{1,j_1}-1\)である。

\(\textrm{Trans}(L_n) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{2n} 0 (b'_1)^{2n} b_1\)であることを\(n\)に関する数学的帰納法で示す。

\(n = 1\)とする。

\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(L_1\)に対しても定め、\(L_1\)に対する適用であることを明示するために右肩に\(L_1\)を乗せて表記する。

\(L_1\)の定義から\(\leq_{L_1}\)と\(\leq_M\)の\((\{0,1\} \times \mathbb{N}) \setminus \{(1,j_1)\}\)への制限は一致する。\(j_1^{J_1} = j_1\)であり、\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)より\((0,j_0) <_{L_1}^{\textrm{Next}} (0,j_1) = (0,j_1^{L_1})\)であるので、\(j_0^{L_1} = j_0\)かつ\((L_1)_{1,j_0^{L_1}} = (L_1)_{1,j_0} = M_{1,j_0} = (L_1)_{1,j_1} = (L_1)_{1,j_1^{L_1}}\)である。

\(j_{-1}^{L_1} = j_{-1}\)であり、\(j_0\)が非\(M\)許容であることから\(j_0^{L_1} = j_0 > j_{-1} = j_{-1}^{L_1}\)となるので、\(j_0^{L_1}\)は非\(L_1\)許容である。

\(\textrm{Pred}(L_1) = \textrm{Pred}(M)\)より\(t_1^{L_1} = t_1 \neq 0\)かつ\(c_1^{L_1} = c_1\)かつ\(t_2^{L_1} = t_2\)かつ\(s_1^{L_1} = s_1\)かつ\(b_1^{L_1} = b_1\)である。\(t_1^{L_1} \neq 0\)より\(L_1\)に対して条件(I)～(VI)が意味を持つ。

\(M\)が条件(VI)を満たさずかつ\(j_0\)が非\(M\)許容であることから、\(L_1\)は条件(II)か(IV)を満たす。

\(\textrm{Mark}\)の左端の基本性質より\(v^{L_1} = (L_1)_{1,j_{-1}^{L_1}} = M_{1,j_{-1}}\)である。

\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)かつ\(j_0\)が非\(M\)許容かつ\(j_0 < j_1-1\)より、条件(V)の下での\(\textrm{Joints}\)と\(\textrm{FirstNodes}\)と\(t_2\)の基本性質から\(t_2\)の各単項成分は\(D_{M_{1,j_1}} 0\)以上である。更に\((L_1)_{1,j_0^{L_1}} = M_{1,j_0} = M_{1,j_1}-1 < M_{1,j_1}\)より、\(t_2^{L_1} = t_2\)の右端単項成分の左端は\(D_{(L_1)_{1,j_0^{L_1}}}\)でない。

従って\(t_3^{L_1} = t_2^{L_1} = t_2\)かつ\(t_4^{L_1} = t_2^{L_1} = t_2\)であり、

\begin{eqnarray*}
c_2^{L_1} = D_{v^{L_1}}(t_3^{L_1} + D_{(L_1)_{1,j_0^{L_1}}}(t_4^{L_1} + D_{(L_1)_{1,j_1^{L_1}}} 0)) = D_{M_{1,j_{-1}}}(t_2 + D_{M_{1,j_0}}(t_2 + D_{M_{1,j_0}} 0))
\end{eqnarray*}

\((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)が\(c_2= D_v(t_2 + D_{M_{1,j_1}} 0)\)のscb分解であることから\((D_{M_{1,j_0}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(D_{M_{1,j_0}}(t_2 + D_{M_{1,j_1}} 0)\)のscb分解であり、加法とscb分解の関係より\((D_{M_{1,j_0}} s'_1,D_{M_{1,j_0}} 0,b'_1)\)は\(D_{M_{1,j_0}}(t_2 + D_{M_{1,j_0}} 0)\)のscb分解であり、\((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_0}} s'_1 D_{M_{1,j_0}} 0 b'_1,b'_1)\)は\(c_2^{L_1} = D_{M_{1,j_{-1}}}(t_2 + D_{M_{1,j_0}}(t_2 + D_{M_{1,j_0}} 0))\)のscb分解である。

以上より

\begin{eqnarray*}
\textrm{Trans}(L_n) = \textrm{Trans}(L_1) = s_1^{L_1} c_2^{L_1} b_1^{L_1} = s_1 D_{M_{1,j_{-1}}} s'_1 D_{M_{1,j_0}} s'_1 D_{M_{1,j_0}} 0 b'_1 b'_1 b_1 \\
& = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+1} 0 (b'_1)^{n+1} b_1
\end{eqnarray*}

である。

\(n > 1\)とする。

帰納法の仮定から

\begin{eqnarray*}
\textrm{Trans}(L_{n-1}) & = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n 0 (b'_1)^n b_1 \\
& = & (s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n-1} s'_1) D_{M_{1,j_0}} 0 ((b'_1)^n b_1)
\end{eqnarray*}

であるので、

\begin{eqnarray*}
\textrm{Trans}(L_n) & = & (s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n-1} s'_1) \textrm{Trans}(L') ((b'_1)^n b_1) \\
& = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n-1} s'_1 D_{M_{1,j_0}} s'_1 D_{M_{1,j_0}} 0 b'_1 (b'_1)^n b_1 \\
& = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+1} 0 (b'_1)^{n+1} b_1
\end{eqnarray*}

である。

(5)

\(n=1\)とする。

\(M[n] = \textrm{Pred}(M)\)より

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & t_1 = s_1 c_1 b_2 = s_1 D_{M_{1,j_{-1}}} t_2 b_1 \\
& = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{2n-2} t_2 (b'_1)^{2n-2} b_1
\end{eqnarray*}

である。

\(n > 1\)とする。

\begin{eqnarray*}
\textrm{Trans}(L_n) & = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+1} 0 (b'_1)^{n+1} b_1 \\
& = & (s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n-1} s'_1) D_{M_{1,j_0}} s'_1 D_{M_{1,j_0}} 0 b'_1 ((b'_1)^n b_1) \\
& = & (s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n-1} s'_1) \textrm{Trans}(L') ((b'_1)^n b_1)
\end{eqnarray*}

より

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & (s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n-1} s'_1) \textrm{Trans}(\textrm{Pred}(N')) ((b'_1)^n b_1) \\
& = & (s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n-1} s'_1) D_{M_{1,j_0}} t_2 ((b'_1)^n b_1) \\
& = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n t_2 (b'_1)^n b_1
\end{eqnarray*}

である。□

補題（条件(V)の下での基本列のscb分解）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\(j_0\)が\(M\)許容ならば\(m_n := n-1\)と置き、\(j_0\)が非\(M\)許容ならば\(m_n := n\)と置くと、\(j_1 > 1\)かつ\(M\)が条件(V)を満たすならば[85]、一意な\(u \in \mathbb{N}\)と\((s'_0,b'_0) \in (\Sigma^{< \omega})^2\)と\(t' \in T_{\textrm{B}}\)が存在して以下を満たす：

(1) \((s'_0,D_u t_2,b'_0)\)は\(\textrm{Trans}(M[n])\)のscb分解である。

(2) \((s'_0,D_u(t_2 + D_{M_{1,j_0}} 0),b'_0)\)は\(\textrm{Trans}(M)[m_n]\)のscb分解である。

(3) \((s'_0,D_u(t_2 + D_{M_{1,j_0}} t'),b'_0)\)は\(\textrm{Trans}(M[n+1])\)のscb分解である。

証明：

\(M\)が条件(V)を満たすので\(M_{1,j_0} < M_{1,j_0}+1 = M_{1,j_1}\)である。従って\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)である。

任意の\((s'_1,b'_1) \in (\Sigma^{< \omega})^2\)に対し、\((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)が\(c_2\)のscb分解であるならば\(\textrm{Trans}(M)[m_n] = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{m_n+1} 0 (b'_1)^{m_n+1} b_1\)かつ任意の\(t' \in T_{\textrm{B}}\)に対し\(s'_1 D_{M_{1,j_0}} t' b'_1 = t_2 + D_{M_{1,j_0}} t'\)であることを示す。

条件(III)～(VI)の下での\(\textrm{Trans}\)とscb分解の関係より\((s_1,c_2,b_1) = (s_1,D_{M_{1,j_{-1}}} s'_1 D_{M_{1,j_1}} 0 b'_1,b_1)\)は\(\textrm{Trans}(M)\)の第\(1\)種scb分解であり、scb分解と基本列の関係 (2)より

\begin{eqnarray*}
\textrm{Trans}(M)[m_n] = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_1}}-1)^{m_n+1} 0 (b'_1)^{m_n+1} b_1 = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{m_n+1} 0 (b'_1)^{m_n+1} b_1
\end{eqnarray*}

である。\(D_{M_{1,j_{-1}}} s'_1 D_{M_{1,j_1}} 0 b'_1 = c_2 = D_v(t_2 + D_{M_{1,j_1}} 0)\)より\(s'_1 D_{M_{1,j_1}} 0 b'_1 = t_2 + D_{M_{1,j_1}} 0\)である。従って加法とscb分解の関係より\(t_2 + D_{M_{1,j_0}} t' = s'_1 D_{M_{1,j_0}} t' b'_1\)である。

\(j_0\)が\(M\)許容であるとする。

条件(III)～(V)の下での各種scb分解より、一意な\((s'_1,b'_1) \in (\Sigma^{< \omega})^2\)が存在して以下を満たす：

(1) \((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(c_2\)のscb分解である。

(5) \(\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n-1} t_2 (b'_1)^{n-1} b_1\)である。

(5)' \(\textrm{Trans}(M[n+1]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n t_2 (b'_1)^n b_1\)である。

\(n = 1\)とする。

\(u := M_{1,j_{-1}}\)と置く。

\(s'_0 := s_1\)と置く。

\(n > 1\)とする。

\(u := M_{1,j_0}\)と置く。

\(s'_0 := s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n-2} s'_1\)と置く。

\(b'_0 := (b'_1)^{n-1} b_1\)と置く。

\(t' := t_2\)と置く。

既に示したように、\(\textrm{Trans}(M)[m_n] = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{m_n+1} 0 (b'_1)^{m_n+1} b_1\)かつ\(s'_1 D_{M_{1,j_0}} 0 b'_1 = t_2 + D_{M_{1,j_0}} 0\)かつ\(s'_1 D_{M_{1,j_0}} t' b'_1 = t_2 + D_{M_{1,j_0}} t'\)である。従って

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n-1} t_2 (b'_1)^{n-1} b_1 = s'_0 D_u t_2 b'_0 \\
\textrm{Trans}(M)[m_n] & = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n 0 (b'_1)^n b_1 = s'_0 D_u(t_2 + D_{M_{1,j_0}} 0) b'_0 \\
\textrm{Trans}(M[n+1]) & = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n t_2 (b'_1)^n b_1 = s'_0 D_u(t_2 + D_{M_{1,j_0}} t') b'_0
\end{eqnarray*}

である。

\(j_0\)が非\(M\)許容であるとする。

条件(V)の下での各種scb分解より、一意な\((s'_1,b'_1) \in (\Sigma^{< \omega})^2\)が存在して以下を満たす：

(1) \((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(c_2\)のscb分解である。

(5) \(\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n t_2 (b'_1)^n b_1\)である。

(5)' \(\textrm{Trans}(M[n+1]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+1} t_2 (b'_1)^{n+1} b_1\)である。

\(u := M_{1,j_0}\)と置く。

\(s'_0 := s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n-1} s'_1\)と置く。

\(b'_0 := (b'_1)^n b_1\)と置く。

\(t'_0 := t_2 + D_{M_{1,j_0}} t_2\)と置く。

既に示したように、\(\textrm{Trans}(M)[m_n] = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{m_n+1} 0 (b'_1)^{m_n+1} b_1\)かつ\(s'_1 D_{M_{1,j_0}} 0 b'_1 = t_2 + D_{M_{1,j_0}} 0\)かつ\(s'_1 D_{M_{1,j_0}} t_2 b'_1 = t_2 + D_{M_{1,j_0}} t_2 = t'\)である。従って

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n t_2 (b'_1)^n b_1 = s'_0 D_u t_2 b'_0 \\
\textrm{Trans}(M)[m_n] & = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+1} 0 (b'_1)^{n+1} b_1 = s'_0 D_{M_{1,j_0}}(t_2 + D_{M_{1,j_0}} 0) b'_0 \\
\textrm{Trans}(M[n+1]) & = & s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+2} t_2 (b'_1)^{n+2} b_1 = s'_0 D_{M_{1,j_0}}(t_2 + D_{M_{1,j_0}} t'_0) b'_0
\end{eqnarray*}

である。□

それでは本題に戻る。

条件(V)の下での\(\textrm{Trans}\)と基本列の交換関係の証明：

\(M\)は単項であるので\(\textrm{Trans}\)が零項性を保つことから\(\textrm{Trans}(M) \neq 0\)である。従って(2)は(1)と[Buc1] Lemma 3.2より即座に従う。以下では(1)と(3)を示す。

条件(V)の下での基本列のscb分解より、一意な\(u \in \mathbb{N}\)と\((s'_0,b'_0) \in (\Sigma^{< \omega})^2\)と\(t' \in T_{\textrm{B}}\)が存在して以下を満たす：

(1) \((s'_0,D_u t_2,b'_0)\)は\(\textrm{Trans}(M[n])\)のscb分解である。

(2) \((s'_0,D_u(t_2 + D_{M_{1,j_0}} 0),b'_0)\)は\(\textrm{Trans}(M)[m_n]\)のscb分解である。

(3) \((s'_0,D_u(t_2 + D_{M_{1,j_0}} t'),b'_0)\)は\(\textrm{Trans}(M[n+1])\)のscb分解である。

\(t_2 < t_2 + D_{M_{1,j_0}} 0 \leq t_2 + D_{M_{1,j_0}} t'\)であるので、部分表現の不等式の延長性から\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)[m_n] \leq \textrm{Trans}(M[n+1])\)である。□

\(j_0\)が非\(M\)許容であるとする。

条件(V)の下での各種scb分解より、一意な\((s'_1,b'_1) \in (\Sigma^{< \omega})^2\)が存在して以下を満たす：

(1) \((D_{M_{1,j_{-1}}} s'_1,D_{M_{1,j_1}} 0,b'_1)\)は\(c_2\)のscb分解である。

(5) \(\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n t_2 (b'_1)^n b_1\)である。

(5)' \(\textrm{Trans}(M[n+1]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+1} t_2 (b'_1)^{n+1} b_1\)である。

\begin{eqnarray*}
\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n t_2 (b'_1)^n b_1 \\
\textrm{Trans}(M)[m_n] = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+1} 0 (b'_1)^{n+1} b_1 = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^n s'_1 D_{M_{1,j_0}} 0 b'_1 (b'_1)^n b_1
\end{eqnarray*}

かつ\(t_2 < s'_1 D_{M_{1,j_0}} 0 b'_1\)より、部分表現の不等式の延長性から\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)[m_n]\)である。

\(s'_1 D_{M_{1,j_0}} 0 b'_1 \in T_{\textrm{B}}\)とscb分解の置換可能性より\(s'_1 D_{M_{1,j_0}} t_2 b'_1 \in T_{\textrm{B}}\)であり、

\begin{eqnarray*}
\textrm{Trans}(M)[m_n] = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+1} 0 (b'_1)^{n+1} b_1 \\
\textrm{Trans}(M[n+1]) = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+2} t_2 (b'_1)^{n+2} b_1 = s_1 D_{M_{1,j_{-1}}} (s'_1 D_{M_{1,j_0}})^{n+1} s'_1 D_{M_{1,j_0}} t_2 b'_1 (b'_1)^{n+1} b_1
\end{eqnarray*}

かつ\(0 \leq s'_1 D_{M_{1,j_0}} t_2 b'_1\)より、部分表現の不等式の延長性から\(\textrm{Trans}(M)[m_n] \leq \textrm{Trans}(M[n+1])\)である。□

## 条件(VI)の下での展開規則[]

命題（条件(VI)の下での\(\textrm{Trans}\)と基本列の交換関係）

任意の\(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用い、\(j_0\)が\(M\)許容ならば\(m_n := n-2\)と置き、\(j_0\)が非\(M\)許容ならば\(m_n := n-1\)と置くと、\(j_1 > 1\)かつ\(M\)が条件(VI)を満たすならば[86]、以下が成り立つ：

(1) \(m_n = -1\)ならば、ある\(k \in \mathbb{N}\)が存在して\(1 < k \leq M_{1,j_1}+1\)かつ\(\textrm{Trans}(M[n]) = \textrm{Trans}(M)[0]^k\)である。

(2) \(m_n \geq 0\)ならば、\(\textrm{Trans}(M[n]) = \textrm{Trans}(M)[m_n]\)である。

(3) \(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

条件(VI)の下での\(\textrm{Trans}\)と基本列の交換関係を証明するための準備としていくつかの補題を示す。

補題（公差\((1,0)\)のペア数列の\(\textrm{Trans}\)の基本性質）

任意の\(u,m,j_1 \in \mathbb{N}\)に対し、\(M := ((m+j,u))_{j=0}^{j_1} \in T_{\textrm{PS}}\)と置くと
\begin{eqnarray*}
\textrm{Trans}(M) & = & \left\{ \begin{array}{ll} 0 & (j_1 = 0 \wedge u = 0) \\ D_u^{j_1+1} 0 & (j_1 > 0 \vee u > 0) \end{array} \right.
\end{eqnarray*}
となる。

証明：

\(((u+j,u))_{j=0}^{j_1}\)は条件(A)と(B)を満たすので、簡約性と係数の関係より簡約である。従って\(\textrm{Red}\)の\(\textrm{IncrFirst}\)不変性より

\begin{eqnarray*}
\textrm{Red}(M) = \textrm{Red}(\textrm{IncrFirst}^u(M)) = \textrm{Red}(\textrm{IncrFirst}^m(((u+j,u))_{j=0}^{j_1})) = \textrm{Red}(((u+j,u))_{j=0}^{j_1}) = ((u+j,u))_{j=0}^{j_1}
\end{eqnarray*}

である。

\(j_1\)に関する数学的帰納法で示す。

\(j_1 = 0\)とする。

\(\textrm{Trans}\)の再帰的定義より

\begin{eqnarray*}
\textrm{Trans}(M) & = & \textrm{Trans}((m,u)) = \textrm{Trans}(\textrm{Red}((m,u))) = \textrm{Trans}((u,u)) \\
& = & \left\{ \begin{array}{ll} 0 & (u = 0) \\ D_u 0 & (u > 1) \end{array} \right.
\end{eqnarray*}

である。

\(j_1 = 1\)とする。

\(2\)列ペア数列の基本性質と\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性より

\begin{eqnarray*}
\textrm{Trans}(M) = \textrm{Trans}((m,u),(m+1,u)) = \textrm{Trans}(\textrm{Red}((m,u),(m+1,u))) = \textrm{Trans}((u,u),(u+1,u)) = D_u D_u 0 = D_u^{j_1+1} 0
\end{eqnarray*}

である。

\(j_1 > 1\)とする。

\(\textrm{Red}(M) = ((j,u))_{j=0}^{j_1}\)は簡約かつ単項である。

\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(\textrm{Red}(M)\)に対して定める[87]。

帰納法の仮定より\(\textrm{Trans}(\textrm{Pred}(M)) = D_u^{j_1} 0\)である。

\(\textrm{Red}\)と\(\textrm{Pred}\)の可換性と\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性より

\begin{eqnarray*}
t_1 = \textrm{Trans}(\textrm{Pred}(\textrm{Red}(M))) = \textrm{Trans}(\textrm{Red}(\textrm{Pred}(M))) = \textrm{Trans}(\textrm{Pred}(M)) = D_u^{j_1} 0 \neq 0
\end{eqnarray*}

である。従って\(\textrm{Red}(M)\)に対して条件(I)～(VI)が意味を持つ。

\(j_0 = j_1-1\)であり\(j_{-1} = j_0\)である。

\(u = 0\)ならば\(M\)は条件(I)を満たす。

\(u > 0\)ならば\(M\)は条件(III)を満たす。

従っていずれの場合も\(M\)は条件(I)か(III)を満たす。

簡約性の切片への遺伝性より\(\textrm{Pred}(\textrm{Red}(M))\)は簡約であるので、右端第\(1\)基点のMarkの基本性質より\(c_1 = \textrm{Mark}(\textrm{Pred}(\textrm{Red}(M)),j_{-1}) = \textrm{Mark}(\textrm{Pred}(\textrm{Red}(M)),j_1-1) = D_u 0\)である。

\(t_1 = D_u^{j_1} 0\)かつ\(c_1 = D_u 0\)より、\(s_1 = D_u^{j_1-1}\)かつ\(b_1 = ()\)である。

\(D_v t_2 = c_1 = D_u 0\)より、\(v = u\)かつ\(t_2 = 0\)である。

\(M\)は条件(I)か(III)を満たすことから\(c_2 = D_v(t_2 + D_u 0) = D_u D_u 0 = D_u^2 0\)である。従って\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性より

\begin{eqnarray*}
\textrm{Trans}(M) & = & \textrm{Trans}(\textrm{Red}(M)) = s_1 c_2 b_1 = D_u^{j_1-1} D_u^2 0 = D_u^{j_1+1} 0
\end{eqnarray*}

である。□

補題（公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の展開規則）

任意の\(u,j_1 \in \mathbb{N}\)と\(n \in \mathbb{N}_{+}\)に対し、\(M := ((u+j,u+j))_{j=0}^{j_1} \in T_{\textrm{PS}}\)と置くと、\(j_1 > 1\)ならば\(\textrm{Trans}(M[n]) = D_u D_{u+j_1-1}^n 0\)である。

証明：

\(M\)は条件(A)と(B)を満たすので、簡約性と係数の関係より\(M\)は簡約である。簡約性が基本列で保たれることより\(M[n]\)は簡約である。

\((1,j_1-1) <_M^{\textrm{Next}} (1,j_1)\)より

\begin{eqnarray*}
M[n] & = & (M_j)_{j=0}^{j_1-1} \oplus_{\mathbb{N}^2} ((M_{0,j_1-1}+j,M_{1,j_1-1}))_{j=1}^{n-1} = (M_j)_{j=0}^{j_1-1} \oplus_{\mathbb{N}^2} ((u+j_1-1+j,u+j_1-1))_{j=1}^{n-1}
\end{eqnarray*}

であり、\(\textrm{Lng}(M[n])-1 = j_1-2+n\)である。

\(n = 1\)ならば、\(j_1-1 = \textrm{Lng}(M[n])-1\)であるので\(j_1-1\)は\(M[n]\)許容である。

\(n > 1\)ならば、\(j_1-1 < \textrm{Lng}(M[n])-1\)かつ\(M[n]_{1,j_1-1} = M_{1,j_1-1} = M[n]_{1,j_1}\)であるので\((1,j_1-1) <_{M[n]}^{\textrm{Next}} (1,j_1)\)でなく、従って\(j_1-1\)は\(M[n]\)許容である。

以上より、いずれの場合も\(j_1-1\)は\(M[n]\)許容である。

\((M[n]_j)_{j=0}^{j_1-1} = (M_j)_{j=0}^{j_1-1} = ((u+j,u+j))_{j=0}^{j_1-1}\)であるので、\(j_1 > 1\)と公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質より

\begin{eqnarray*}
\textrm{Trans}((M[n]_j)_{j=0}^{j_1-1}) = D_u D_{u+j_1-1} 0
\end{eqnarray*}

である。

\((M[n]_j)_{j=j_1-1}^{j_1-2+n} = ((u+j_1-1+j,u+j_1-1))_{j=1}^{n-1}\)であるので、\(j_1 > 1\)と公差\((1,0)\)のペア数列の\(\textrm{Trans}\)の基本性質より\(\textrm{Trans}((M[n]_j)_{j=j_1-1}^{j_1-2+n}) = D_{u+j_1-1}^n 0\)である。従って\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示より

\begin{eqnarray*}
\textrm{Mark}(M[n],j_1-1) = \textrm{Trans}((M[n]_j)_{j=j_1-1}^{j_1-2+n}) = D_{u+j_1-1}^n 0
\end{eqnarray*}

である。

以上より、\(j_1-1 > 0\)と\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示から

\begin{eqnarray*}
\textrm{Trans}(M[n]) = D_u \textrm{Mark}(M[n],j_1-1) = D_u D_{u+j_1-1}^n 0
\end{eqnarray*}

である。□

補題（順序数項の末尾単項の零化可能性）

任意の\(t,t' \in T_{\textrm{B}}\)と\(s,b \in \Sigma^{< \omega}\)と\(u,v \in \mathbb{N}\)に対し、\((s,D_u(t' + D_v 0),b\))が\(t\)のscb分解であるならば、ある\(k \in \mathbb{N}\)が存在して\(0 < k \leq v+1\)かつ\((s,D_u t',b)\)が\(t[0]^k\)のscb分解である。
となる。

証明：

\(v\)についての数学的帰納法で示す。

\(v = 0\)とする。

\(k := 1\)と置く。

\(0 < k = 1 = v+1\)である。

順序数項の基本列の再帰的定義より

\begin{eqnarray*}
(s,(D_u(t' + D_0 0))[0],b) = (s,D_u((t' + D_0 0)[0]),b) = (s,D_u(t' + (D_0 0)[0]),b)= (s,D_u(t' + 0),b) = (s,D_u t',b)
\end{eqnarray*}

が\(t[0]^k = t[0]\)のscb分解である。

\(v > 0\)とする。

\((D_v 0)[0] = 0\)かつ\((D_v 0)[D_{v-1} 0] = D_{v-1} 0\)であるので、順序数項の基本列の再帰的定義とscb分解の置換可能性より\((s,D_u t',b)\)または\((s,D_u(t' + D_{v-1} 0),b)\)が\(t[0]\)のscb分解である。

\((s,D_u t',b)\)が\(t[0]\)のscb分解であるとする。

\(k := 1\)と置く。

\(0 < k = 1 < v+1\)である。

\((s,D_u t',b)\)は\(t[0]^k = t[0]\)のscb分解である。

\((s,D_u(t' + D_{v-1} 0),b)\)が\(t[0]\)のscb分解であるとする。

帰納法の仮定より、ある\(k' \in \mathbb{N}\)が存在して\(0 < k' \leq v\)かつ\(t[0][0]^{k'}\)が\((s,D_u t',b)\)のscb分解である。

\(k := k'+1\)と置く。

\(0 < 1 < k \leq v+1\)である。

\(t[0]^k = t[0][0]^{k'}\)は\((s,D_u t',b)\)のscb分解である。□

それでは本題に戻る。

条件(VI)の下での\(\textrm{Trans}\)と基本列の交換関係の証明：

\(M\)は単項であるので\(\textrm{Trans}\)が零項性を保つことから\(\textrm{Trans}(M) \neq 0\)である。従って(3)は(1)と(2)と[Buc1] Lemma 3.2より即座に従う。

\(M_{1,j_0} < M_{1,j_0}+1 = M_{1,j_1}\)より\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)である。

\(j_0+1 = j_1\)かつ\(M_{1,j_0}+1 = M_{1,j_1}\)より

\begin{eqnarray*}
M[n] & = & (M_j)_{j=0}^{j_1-1} \oplus_{\mathbb{N}^2} ((M_{0,j_0}+j,M_{1,j_0}))_{j=1}^{n-1}
\end{eqnarray*}

であり、\(\textrm{Lng}(M[n])-1 = j_1-2+n\)である。

\(n = 1\)ならば、\(j_0 = \textrm{Lng}(M[n])-1\)であるので\(j_0\)は\(M[n]\)許容である。

\(n > 1\)ならば、\(j_0 < \textrm{Lng}(M[n])-1\)かつ\(M[n]_{1,j_0} = M_{1,j_0} = M[n]_{1,j_0+1}\)であるので\((1,j_0) <_{M[n]}^{\textrm{Next}} (1,j_0+1)\)でなく、従って\(j_0\)は\(M[n]\)許容である。

従っていずれの場合も\(j_0\)は\(M[n]\)許容である。

\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)より\((1,j_{-1}) <_M^{\textrm{Next}} (1,j_{-1}+1)\)であり、\(j_{-1}\)は\(M\)許容であるので\((1,j_{-1}-1) <_M^{\textrm{Next}} (1,j_{-1})\)でない。更に\((M[n]_j)_{j=0}^{j_{-1}} = (M_j)_{j=0}^{j_{-1}}\)であるので、\((1,j_{-1}-1) <_{M[n]}^{\textrm{Next}} (1,j_{-1})\)でない。以上より\(j_{-1}\)は\(M[n]\)許容である。

右端第\(2\)基点のMarkの基本性質より\(\textrm{Trans}(M) = s_1 c_2 b_1 = s_1 \textrm{Mark}(M,j_{-1}) b_1\)であるので、\(j_{-1} > 0\)ならば\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より

\begin{eqnarray*}
\textrm{Trans}((M[n]_j)_{j=0}^{j_{-1}}) = \textrm{Trans}((M_j)_{j=0}^{j_{-1}}) = s_1 D_{M_{1,j_{-1}}} b_1
\end{eqnarray*}

である。

\(N := (M_j)_{j=j_{-1}}^{j_1}\)と置く。

標準形の直系先祖による切片の簡約化の強単項性より\(\textrm{Red}(N)\)は強単項である。簡約性と係数の関係より\(\textrm{Red}(N)\)は条件(A)と(B)を満たす。直系先祖による切片と\(\textrm{Red}\)と\(\textrm{IncrFirst}\)の関係より\(\textrm{IncrFirst}^{N_{0,0}-N_{1,0}}(\textrm{Red}(N)) = N\)すなわち\(\textrm{Red}(N) = ((M_{1,j}-M_{0,j_{-1}}+M_{1,j_{-1}},M_{1,j}))_{j=j_{-1}}^{j_1}\)である。

\(M_{1,j_0} < M_{1,j_0}+1 = M_{1,j_1}\)より\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)であるので\((1,j_0) <_N^{\textrm{Next}} (1,j_1)\)であり、直系先祖の\(\textrm{Red}\)不変性より\((1,j_0) <_{\textrm{Red}(N)}^{\textrm{Next}} (1,j_1)\)である。

許容化の切片への遺伝性より\(\textrm{Adm}_N(j_0-j_{-1}) = 0\)であり、許容化の\(\textrm{Red}\)不変性より\(\textrm{Adm}_{\textrm{Red}(N)}(j_0-j_{-1}) = 0\)である。

\((1,j_0) <_{\textrm{Red}(N)}^{\textrm{Next}} (1,j_1)\)かつ\(\textrm{Adm}_{\textrm{Red}(N)}(j_0-j_{-1}) = 0\)より\(\textrm{TrMax}(\textrm{Red}(N)) = j_1-j_{-1}\)である。更に\(\textrm{Red}(N)\)が条件(A)と(B)を満たし\(\textrm{Red}(N)_{1,0} = M_{1,j_{-1}}\)かつ\(\textrm{Red}(N)_{1,j_1} = M_{1,j_1}\)であることから、\(\textrm{Red}(N) = ((j,j))_{j=M_{1,j_{-1}}}^{M_{1,j_1}}\)である。

\(j_1-j_{-1} \geq j_1-j_0 > 0\)と公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質より、\(\textrm{Trans}(\textrm{Red}(N)) = D_{M_{1,j_{-1}}} D_{M_{1,j_1}} 0\)である。従って\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示より

\begin{eqnarray*}
c_2 & = & \textrm{Mark}(M,j_{-1}) = \textrm{Trans}(N) = \textrm{Trans}(\textrm{Red}(N)) = D_{M_{1,j_{-1}}} D_{M_{1,j_1}} 0
\end{eqnarray*}

である。条件(III)～(VI)の下での\(\textrm{Trans}\)とscb分解の関係より\((s_1,c_2,b_1) = (s_1,D_{M_{1,j_{-1}}} D_{M_{1,j_1}} 0,b_1) = (s_1,\textrm{Trans}(N),b_1)\)は\(\textrm{Trans}(M)\)の第\(1\)種scb分解であり、scb分解と基本列の関係より任意の\(m \in \mathbb{N}\)に対し

\begin{eqnarray*}
\textrm{Trans}(M)[m] & = & s_1 D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1}^{m+1} 0 b_1
\end{eqnarray*}

である。

\(\textrm{Red}\)と\(\textrm{Pred}\)の可換性より\(\textrm{Red}(\textrm{Pred}(N)) = \textrm{Pred}(\textrm{Red}(N)) = ((j,j))_{j=M_{1,j_{-1}}}^{M_{1,j_1}-1}\)である。

\(j_1-j_{-1} = 1\)とする。

\(j_{-1} \leq j_0 < j_1 = j_{-1}+1\)より\(j_0 = j_{-1}\)である。従って\(j_0\)は\(M\)許容であり、\(m_n = n-2\)である。

\(\textrm{Pred}(M)_{1,j_1-1} = M_{1,j_1-1} = M_{1,j_{-1}}\)と右端第\(1\)基点のMarkの基本性質より

\begin{eqnarray*}
c_1 = \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = \textrm{Mark}(\textrm{Pred}(M),j_1-1) = D_{M_{1,j_{-1}}} 0
\end{eqnarray*}

である。

\(n = 1\)とする。

\(m_n = -1\)である。

\(M[n] = \textrm{Pred}(M)\)より

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & s_1 c_1 b_1 = s_1 D_{M_{1,j_{-1}}} 0 b_1 \\
\textrm{Trans}(M)[0] & = & s_1 D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1} 0 b_1
\end{eqnarray*}

であるので、順序数項の末尾単項の零化可能性よりある\(k' \in \mathbb{N}\)が存在して\(0 < k' \leq M_{1,j_1}\)かつ\(\textrm{Trans}(M[n])  = \textrm{Trans}(M)[0][0]^{k'} = \textrm{Trans}(M)[0]^{k+1}\)である。

\(k := k'+1\)と置く。

\(1 < k \leq M_{1,j_1}+1\)である。

\(\textrm{Trans}(M[n]) = \textrm{Trans}(M)[0][0]^{k'} = \textrm{Trans}(M)[0]^k\)である。

\(n > 1\)とする。

\(m_n \geq 0\)である。

\((M[n]_j)_{j=j_{-1}}^{j_1-2+n} = ((M_{0,j_0}+j,M_{1,j_0}))_{j=０}^{n-1}\)であるので、\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示と公差\((1,0)\)のペア数列の\(\textrm{Trans}\)の基本性質から

\begin{eqnarray*}
\textrm{Mark}(M[n],j_{-1}) = \textrm{Trans}((M[n]_j)_{j=j_{-1}}^{j_1-2+n}) = D_{M_{1,j_0}}^n 0
\end{eqnarray*}

である。

\(j_{-1} = 0\)とする。

\(s_1\)と\(b_1\)の空性と基点の関係より\(s_1 = ()\)かつ\(b_1 = ()\)である。

\(M[n] = ((M_{0,j_0}+j,M_{1,j_0}))_{j=０}^{n-1}\)であるので、従って公差\((1,0)\)のペア数列の\(\textrm{Trans}\)の基本性質

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & D_{M_{1,j_{-1}}}^n 0 = D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1}^{n-1} 0 \\
\textrm{Trans}(M)[m_n] & = & s_1 D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1}^{n-1} 0 b_1 = D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1}^{n-1} 0
\end{eqnarray*}

となる。すなわち\(\textrm{Trans}(M[n])  = \textrm{Trans}(M)[m_n]\)である。

\(j_{-1} > 0\)とする。

\(\textrm{Trans}((M[n]_j)_{j=0}^{j_{-1}}) = s_1 D_{M_{1,j_{-1}}} 0 b_1\)と\(\textrm{Mark}(M[n],j_{-1}) = D_{M_{1,j_0}}^n 0\)から、\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & s_1 D_{M_{1,j_0}}^n 0 b_1 \\
\textrm{Trans}(M)[m_n] & = & s_1 D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1}^{n-1} 0 b_1 = s_1 D_{M_{1,j_0}}^n 0 b_1
\end{eqnarray*}

となる。すなわち\(\textrm{Trans}(M[n])  = \textrm{Trans}(M)[m_n]\)である。

\(j_1-j_{-1} > 1\)とする。

\(j_{-1} < j_1-1 = j_0\)である。従って\(j_0\)は非\(M\)許容であり、\(m_n = n-1 \geq 0\)である。

公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質より\(\textrm{Trans}(\textrm{Red}(\textrm{Pred}(N))) = D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1} 0\)である。従って\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示より

\begin{eqnarray*}
c_1 = \textrm{Mark}(\textrm{Pred}(M),j_{-1}) = \textrm{Trans}(\textrm{Pred}(N)) = \textrm{Trans}(\textrm{Red}(\textrm{Pred}(N))) = D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1} 0
\end{eqnarray*}

である。

\(n = 1\)とする。

\(M[n] = \textrm{Pred}(M)\)より

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & s_1 c_1 b_1 = s_1 D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1} 0 b_1 \\
\textrm{Trans}(M)[m_n] & = & s_1 D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1} 0 b_1
\end{eqnarray*}

である。すなわち\(\textrm{Trans}(M[n]) = \textrm{Trans}(M)[m_n]\)である。

\(n > 1\)とする。

\((M[n]_j)_{j=j_{-1}}^{j_1-2+n} = (M_j)_{j=j_{-1}}^{j_1-1} \oplus_{\mathbb{N}^2} ((M_{0,j_0}+j,M_{1,j_0}))_{j=1}^{n-1} = N[n]\)であるので、\(\textrm{Red}\)と基本列の可換性と\(\textrm{Trans}\)の\((\textrm{IncrFirst},\textrm{Red})\)不変\(P\)同変性と\(\textrm{Mark}\)の\(\textrm{Trans}\)による表示と公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の展開規則より

\begin{eqnarray*}
\textrm{Mark}(M[n],j_{-1}) & = & \textrm{Trans}((M[n]_j)_{j=j_{-1}}^{j_1-2+n}) = \textrm{Trans}(N[n]) = \textrm{Trans}(\textrm{Red}(N[n])) \\
& = & \textrm{Trans}(\textrm{Red}(N)[n]) = \textrm{Trans}(((j,j))_{j=M_{1,j_{-1}}}^{M_{1,j_1}}[n]) = D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1}^n 0
\end{eqnarray*}

である。

\(j_{-1} = 0\)とする。

\(s_1\)と\(b_1\)の空性と基点の関係より\(s_1 = ()\)かつ\(b_1 = ()\)である。

\(M[n] = (M[n]_j)_{j=j_{-1}}^{j_1-2+n}\)であるので、

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & \textrm{Trans}((M[n]_j)_{j=j_{-1}}^{j_1-2+n}) = D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1}^n 0 \\
\textrm{Trans}(M)[m_n] & = & s_1 D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1}^n 0 b_1 = D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1}^n 0
\end{eqnarray*}

となる。すなわち\(\textrm{Trans}(M[n])  = \textrm{Trans}(M)[m_n]\)である。

\(j_{-1} > 0\)とする。

\(\textrm{Trans}((M[n]_j)_{j=0}^{j_{-1}}) = s_1 D_{M_{1,j_{-1}}} 0 b_1\)と\(\textrm{Trans}\)の\(\textrm{Mark}\)と切片による表示より

\begin{eqnarray*}
\textrm{Trans}(M[n]) & = & s_1 \textrm{Mark}(M[n],j_{-1}) b_1 = s_1 D_{M_{1,j_{-1}}} D_{M_{1,j_0}}^n 0 b_1 \\
\textrm{Trans}(M)[m_n] & = & s_1 D_{M_{1,j_{-1}}} D_{M_{1,j_1}-1}^n 0 b_1 = s_1 D_{M_{1,j_{-1}}} D_{M_{1,j_0}}^n 0 b_1
\end{eqnarray*}

となる。すなわち\(\textrm{Trans}(M[n])  = \textrm{Trans}(M)[m_n]\)である。□

## 主結果[]

定理（標準形ペア数列システムの停止性）

\(ST_{\textrm{PS}} \times \mathbb{N}_{+} \subset \textrm{Dom}(F)\)である。

標準形ペア数列システムの停止性を証明するための準備としていくつかの補題を示す。

補題（公差\((0,0)\)のペア数列の\(\textrm{Trans}\)の基本性質）

任意の\(u,j_1 \in \mathbb{N}\)に対し、\(M := ((u,u))_{j=0}^{j_1}\)と置くと、
\begin{eqnarray*}
\textrm{Trans}(M) = \left\{ \begin{array}{ll} (D_0 0) \times j_1 & (u = 0) \\ (D_u 0) \times (j_1+1) & (u > 0) \end{array} \right.
\end{eqnarray*}
である。

証明：

\(\textrm{Trans}\)の再帰的定義から、\(j_1\)に関する数学的帰納法により即座に従う。□

補題（基本列の降下性）

任意の\(M \in ST_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)に対し、\(\textrm{Lng}(M) > 1\)ならば\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

証明：

標準形の簡約性から\(M\)は簡約である。簡約性と係数の関係から\(M\)は条件(A)と(B)を満たす。

\(\textrm{Trans}\)の再帰的定義中に導入した記号を用いる。

\(J'_1 := \textrm{Lng}(P(M))-1\)と置く。

\(M[n] = \textrm{Pred}(M)\)ならば\(\textrm{Pred}\)の\(\textrm{Trans}\)に関する降下性より従う。以下では\(M[n] \neq \textrm{Pred}(M)\)とする。

\(M[n] \neq \textrm{Pred}(M)\)より、\(n > 1\)かつ\((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)を満たす一意な\(j_0 \in \mathbb{N}\)が存在する。特に\(j_1 > j_0 \geq 0\)であり、\(\textrm{Lng}(P(M)_{J'_1}) \geq j_1-j_0 > 0\)である。すなわち\(P(M)_{J'_1} \neq ((0,0))\)である。

\(P(M)_{J'_1} \neq ((0,0))\)と\(\textrm{Trans}\)の再帰的定義と標準形の単項成分が標準形であることから、\(M\)を\(P(M)_{J_1}\)に置き換えることで\(M\)が単項である場合に帰着される。以下では\(M\)が単項であるとする。

\(t_1 = 0\)とする。

\(\textrm{Trans}\)が零項性を保つことより\(\textrm{Pred}(M)\)は零項である。従って\(j_1 = 1\)かつ\(M_{1,0} = 0\)である。\(M\)が単項でかつ条件(A)と(B)を満たすことから、\(M = ((0,0),(1,0))\)または\(M = ((0,0),(1,1))\)である。

\(M = ((0,0),(1,0))\)とする。

公差\((1,0)\)のペア数列の\(\textrm{Trans}\)の基本性質から\(\textrm{Trans}(M) = D_0 D_0 0\)である。

\(M[n] = ((0,0))_{j=0}^{n-1}\)であるので、公差\((0,0)\)のペア数列の\(\textrm{Trans}\)の基本性質から\(\textrm{Trans}(M[n]) = (D_0 0) \times (n-1)\)である。

\(0 < D_0 0\)より\((D_0 0) \times (n-1) < D_0 D_0 0\)であるので、\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

\(M = ((0,0),(1,1))\)とする。

公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質から\(\textrm{Trans}(M) = D_0 D_1 0\)である。

\(M[n] = ((j,0))_{j=0}^{n-1}\)であるので、\(n > 1\)と公差\((1,0)\)のペア数列の\(\textrm{Trans}\)の基本性質から\(\textrm{Trans}(M[n]) = D_0^n 0\)である。

\(D_0^{n-1} 0 < D_1 0\)より\(D_0^n 0 < D_0 D_1 0\)であるので、\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

\(t_1 \neq 0\)とする[88]。

\(\textrm{Trans}\)が零項性を保つことより\(\textrm{Pred}(M)\)は零項でない。

\(M\)が条件(I)を満たすとする。

\(j_1 = 1\)とする。

\(\textrm{Pred}(M)\)は零項でなくかつ\(M\)が条件(A)と(B)を満たすことから、一意な\(u \in \mathbb{N}\)が存在して\(u > 0\)かつ\(M = ((u,u),(u+1,0))\)である。

\(2\)列ペア数列の基本性質 (1)より\(\textrm{Trans}(M) = D_u D_0 0\)である。

\(M[n] = ((u,u))_{j=0}^{n-1}\)であるので、公差\((0,0)\)のペア数列の\(\textrm{Trans}\)の基本性質から\(\textrm{Trans}(M[n]) = (D_u 0) \times n\)である。

\(0 < D_0 0\)より\(D_u 0 < D_u D_0 0\)であるので、\((D_u 0) \times n < D_u D_0 0\)すなわち\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

\(j_1 > 1\)ならば、条件(I)の下での\(\textrm{Trans}\)と基本列の交換関係 (2)より\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

\(M\)が条件(II)を満たすとする。

\(M\)が単項であるので\((0,0) \leq_M (0,j_1)\)であるが、\(0\)は\(M\)許容であるため\((0,0) <_M^{\textrm{Next}} (0,j_1)\)でない。従って\(j_1 > 1\)であり、条件(II)の下での\(\textrm{Trans}\)と基本列の交換関係 (4)より\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

\(M\)が条件(III)か(IV)を満たすとする。

\(M[n] \neq \textrm{Pred}(M)\)より、\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\)を満たす一意な\(j_{-2} \in \mathbb{N}\)が存在する。\(M_{1,j_0} \geq M_{1,j_1}\)より\((1,j_0) <_M^{\textrm{Next}} (1,j_1)\)でないので、\(j_{-2} < j_0 < j_1\)である。従って\(j_1 > 1\)であり、条件(III)か(IV)の下での\(\textrm{Trans}\)と基本列の交換関係 (2)より\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

\(M\)が条件(V)を満たすとする。

\(j_1 > j_0+1 \geq 1\)であるので条件(V)の下での\(\textrm{Trans}\)と基本列の交換関係 (2)より\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

\(M\)が条件(VI)を満たすとする。

\(j_1 = 1\)とする。

\(\textrm{Pred}(M)\)は零項でなくかつ\(M\)が条件(A)と(B)を満たすことから、一意な\(u \in \mathbb{N}\)が存在して\(u > 0\)かつ\(M = ((u,u),(u+1,u+1))\)である。

\(2\)列ペア数列の基本性質 (1)より\(\textrm{Trans}(M) = D_u D_{u+1} 0\)である。

\(M[n] = ((u+j,u))_{j=0}^{n-1}\)であるので、公差\((1,0)\)のペア数列の\(\textrm{Trans}\)の基本性質から\(\textrm{Trans}(M[n]) = D_u^n 0\)である。

\(D_u^{n-1} 0 < D_{u+1} 0\)より\(D_u^n 0 < D_u D_{u+1} 0\)であるので、\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。

\(j_1 > 1\)ならば、条件(VI)の下での\(\textrm{Trans}\)と基本列の交換関係 (3)より\(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)である。□

以下、[Buc1]における\(OT\)と\(T_{\textrm{B}}\)の共通部分を\(OT_{\textrm{B}}\)と置く。

補題（順序数項の再帰構造）

任意の\(t \in OT_{\textrm{B}}\)と\(c \in T_{\textrm{B}}\)と\(s,b \in \Sigma^{< \omega}\)に対し、\((s,c,b\))が\(t\)のscb分解であるならば、\(c\)は順序数項である。
となる。

証明：

scb分解の自明性の判定条件と順序数項の再帰的定義から、\(\textrm{Lng}(s)\)に関する数学的帰納法より即座に従う。□

補題（順序数項の共終数の遺伝性）

任意の\(t,t' \in T_{\textrm{B}}\)と\(s,b \in \Sigma^{< \omega}\)に対し、\(\textrm{dom}(t') = \mathbb{N}\)かつ\((s,t',b\))が\(t\)のscb分解であるならば、\(\textrm{dom}(t) = \mathbb{N}\)である。
となる。

証明：

scb分解の自明性の判定条件と\(\textrm{dom}\)の再帰的定義[Buc1] p. 204 ([].4) (iii)と([].5)から、\(\textrm{Lng}(s)\)に関する数学的帰納法より即座に従う。□

補題（順序数項の末尾項の零化可能性）

任意の\(t \in OT_{\textrm{B}}\)と\(t' \in T_{\textrm{B}}\)と\(s,b \in \Sigma^{< \omega}\)と\(u \in \mathbb{N}\)に対し、\((s,D_u t',b\))が\(t\)のscb分解であるならば、ある\(k \in \mathbb{N}\)が存在して\((s,D_u 0,b)\)が\(t[0]^k\)のscb分解である。
となる。

証明：

[Buc1] Lemma 2.2より\((OT_{\textrm{B}},<)\)は整礎である。従って\((OT_{\textrm{B}},<)\)に対して数学的帰納法が適用可能である。

\(t = s D_u t' b\)より\((s D_u,t',b\))は\(t\)のscb分解であるので、順序数項の再帰構造より\(t'\)は順序数項である。

ある\(k \in \mathbb{N}\)が存在して\((s,D_u 0,b)\)が\(t[0]^k\)のscb分解となることを\(t'\)に関する数学的帰納法で示す。

\(t' = 0\)とする。

\(k := 0\)と置く。

\((s,D_u 0,b) = (s,D_u t',b)\)は\(t[0]^k = t\)のscb分解である。

\(t' > 0\)とする。

\(t' \neq 0\)であるので、\(t'\)は単項または複項である。従ってある\(\tau \in T_{\textrm{B}}\)と\(\tau' \in PT_{\textrm{B}}\)が存在して\(t' = \tau + \tau'\)である。

\(\tau'\)は単項であるので\(0 < \tau'\)であり、従って\(0 \geq \tau < \tau + \tau' = t'\)である。

\(\textrm{dom}(\tau') = \{0\}\)とする。

\(\textrm{dom}(t') = \textrm{dom}(\tau') = \{0\}\)より\(\textrm{dom}(D_u t') = \mathbb{N}\)であるので、順序数項の共終数の遺伝性から\(\textrm{dom}(t) = \mathbb{N}\)である。

基本列の再帰的定義[Buc1] p. 204 ([].4) (i)より\((D_u t')[0] = (D_u \tau) \times (0+1) = D_u \tau \in PT_{\textrm{B}}\)であるので、scb分解の置換可能性と\([]\)の再帰的定義から\((s,D_u \tau,b)\)は\(t[0]\)のscb分解となる。

\(\tau < t'\)と\((s,D_u \tau,b)\)が\(t[0]\)のscb分解であることから、帰納法の仮定よりある\(k' \in \mathbb{N}\)が存在して\((s,D_u 0,b)\)が\(t[0][0]^{k'}\)のscb分解となる。

\(\textrm{dom}(\tau') \neq \{0\}\)とする。

基本列の再帰的定義[Buc1] p. 204 ([].4) (ii)と(iii)と([].5)と[Buc2] p. 6のDefinitionの6から、ある\(n \in \textrm{dom}(t') \cup \mathbb{N}\)が存在して\((s,D_u(t'[n]),b)\)が\(t[0]\)のscb分解となる。

\(t' > 0\)と[Buc1] Lemma 3.2 (a)より\(t'[n] < t'\)である。\(t'[n] < t'\)と\((s,D_u(t'[n]),b)\)が\(t[0]\)のscb分解であることから、帰納法の仮定よりある\(k' \in \mathbb{N}\)が存在して\((s,D_u 0,b)\)が\(t[0][0]^{k'}\)のscb分解となる。
<<<MISSING line 6009 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6010 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6011 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6012 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6013 — recover from original.html via tools/make_content.py>>>
補題（\(\textrm{Pred}\)と\([0]\)の関係）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{B}}\)に対し、\(\textrm{Trans}\)の再帰的定義中に導入した記号を用いると、\(j_1 > 1\)かつ\(M\)が条件(VI)を満たさず[89]かつ\(\textrm{Trans}(M)\)が順序数項であるならば、ある\(k \in \mathbb{N}\)が存在して\(\textrm{Trans}(M)[0]^k = t_1\)である。

証明：

簡約性と係数の関係から\(M\)は条件(A)と(B)を満たす。

\(j_1 > 1\)より\(t_1 \neq 0\)であるので、\((s_1,D_v t_2,b_1) = (s_1,c_1,b_1)\)が\(t_1\)のscb分解をなしかつ\(M\)に対し条件(I)～(VI)が意味を持つ。

\(M\)が条件(I)か(III)か(V)を満たすとする。

\((s_1,D_v(t_2 + D_{M_{1,j_1}} 0),b_1) = (s_1,c_2,b_1)\)が\(\textrm{Trans}(M)\)のscb分解である。

\((s_1,D_v t_2,b_1)\)と\((s_1,D_v(t_2 + D_{M_{1,j_1}} 0),b_1)\)がそれぞれ\(t_1\)と\(\textrm{Trans}(M)\)のscb分解であることから、順序数項の末尾単項の零化可能性よりある\(k \in \mathbb{N}\)が存在して\(t_1 = \textrm{Trans}(M)[0]^k\)となる。

\(M\)が条件(II)か(IV)を満たすとする。

\(P(t_2)_{J_1}\)の左端が\(D_{M_{1,j_0}}\)であるとする。

\(t_2 = t_3 + D_{M_{1,j_0}} t_4\)である。従って\((s_1,D_v(t_3 + D_{M_{1,j_0}} t_4),b_1) = (s_1,c_1,b_1)\)と\((s_1,D_v(t_3 + D_{M_{1,j_0}}(t_4 +D_{M_{1,j_1}} 0)),b_1) = (s_1,c_2,b_1)\)はそれぞれ\(t_1\)と\(\textrm{Trans}(M)\)のscb分解である。

更にscb分解の合成則と加法とscb分解の関係よりある\((s',b') \in (\Sigma^{< \omega})^2\)が存在して\((s',D_{M_{1,j_0}} t_4,b')\)と\((s',D_{M_{1,j_0}}(t_4 + D_{M_{1,j_1}} 0),b')\)がそれぞれ\(t_1\)と\(\textrm{Trans}(M)\)のscb分解となる。

順序数項の末尾単項の零化可能性より、ある\(k \in \mathbb{N}\)が存在して\((s',D_{M_{1,j_0}} t_4,b')\)は\(\textrm{Trans}(M)[0]^k\)のscb分解である。従って

\begin{eqnarray*}
t_1 = s_1 D_{M_{1,j_{-1}}} t_2 b_1 = \textrm{Trans}(M)[0]^k
\end{eqnarray*}

である。

\(P(t_2)_{J_1}\)の左端が\(D_{M_{1,j_0}}\)でないとする。

\(t_3 = t_2\)かつ\(t_4 = t_2\)かつ\(c_2 = D_v(t_3 + D_{M_{1,j_0}}(t_4 + D_{M_{1,j_1}} 0)) = D_v(t_2 + D_{M_{1,j_0}}(t_2 + D_{M_{1,j_1}} 0))\)である。従って\((s_1,D_v(t_2 + D_{M_{1,j_0}}(t_2 + D_{M_{1,j_1}} 0)),b_1) = (s_1,c_2,b_1)\)は\(\textrm{Trans}(M)\)のscb分解である。

更にscb分解の合成則と加法とscb分解の関係よりある\((s',b') \in (\Sigma^{< \omega})^2\)が存在して\((s',D_{M_{1,j_0}}(t_2 + D_{M_{1,j_1}} 0),b')\)が\(\textrm{Trans}(M)\)のscb分解となる。

\(\textrm{Trans}(M)\)が順序数項であることと順序数項の末尾項の零化可能性よりある\(k'_0 \in \mathbb{N}\)が存在して\((s',D_{M_{1,j_0}} 0,b')\)は\(\textrm{Trans}(M)[0]^{k'_0}\)のscb分解となる。

\((s_1,D_{M_{1,j_{-1}}}(t_2 + D_{M_{1,j_0}}(t_2 + D_{M_{1,j_1}} 0)),b_1)\)と\((s',D_{M_{1,j_0}}(t_2 + D_{M_{1,j_1}} 0),b')\)がいずれも\(\textrm{Trans}(M)\)のscb分解でありかつ\((s',D_{M_{1,j_0}} 0,b')\)が\(\textrm{Trans}(M)[0]^{k'_0}\)のscb分解であることから、加法とscb分解の関係 (3)より\((s_1,D_{M_{1,j_{-1}}}(t_2 + D_{M_{1,j_0}} 0),b_1)\)は\(\textrm{Trans}(M)[0]^{k'_0}\)のscb分解である。

従って順序数項の末尾単項の零化可能性より、ある\(k'_1 \in \mathbb{N}\)が存在して\((s_1,D_{M_{1,j_{-1}}} t_2,b_1)\)は\(\textrm{Trans}(M)[0]^{k'_0}[0]^{k'_1}\)のscb分解である。

\(k := k'_0 + k'_1\)と置く。

\begin{eqnarray*}
t_1 = s_1 D_{M_{1,j_{-1}}} t_2 b_1 = \textrm{Trans}(M)[0]^{k'_0}[0]^{k'_1} = \textrm{Trans}(M)[0]^k
\end{eqnarray*}

である。□

補題（順序数項の基本例）

(1) 任意の\(u \in \mathbb{N}\)に対し、\(D_u 0 \in OT_{\textrm{B}}\)である。

(2) 任意の\(u,v \in \mathbb{N}\)に対し、\(D_u D_v 0 \in OT_{\textrm{B}}\)である。

(3) 任意の\(u \in \mathbb{N}\)と\(n \in \mathbb{N}_{+}\)に対し、\((D_u 0) \times (n-1) \in OT_{\textrm{B}}\)である。

(4) 任意の\(u \in \mathbb{N}\)と\(n \in \mathbb{N}\)に対し、\(D_u^n 0 \in OT_{\textrm{B}}\)である。

証明：

以下では\(2^{T_{\textrm{B}}}\)で\(T_{\textrm{B}}\)の部分集合全体の集合を表し、\(G\)で[Buc1] p. 201のフィルトレーションの\(\mathbb{N} \times T_{\textrm{B}}\)への制限

\begin{eqnarray*}
G \colon \mathbb{N} \times T_{\textrm{B}} & \to & 2^{T_{\textrm{B}}} \\
(u,t) & \mapsto & G_u t
\end{eqnarray*}

を表す。[Buc1] p.201の方法で\(<\)を\(T_{\textrm{B}} \cup 2^{T_{\textrm{B}}}\)へ拡張する。

(1) \(0 \in OT_{\textrm{B}}\)と\(G_u 0 = \emptyset < D_u 0\)と[Buc1] p.201 (OT3)より即座に従う。

(2) \(D_v 0 \in OT_{\textrm{B}}\)と

\begin{eqnarray*}
G_u D_v 0 & = & \left\{ \begin{array}{ll} \{0\} \cup G_u 0 & (u \leq v) \\ \emptyset & (u > v) \end{array} \right. \\
& = & \left\{ \begin{array}{ll} \{0\} \cup \emptyset & (u \leq v) \\ \emptyset & (u > v) \end{array} \right. \\
& = & \left\{ \begin{array}{ll} \{0\} & (u \leq v) \\ \emptyset & (u > v) \end{array} \right. \\
& < & D_v 0
\end{eqnarray*}

と[Buc1] p.201 (OT3)より即座に従う。

(3) \(0, D_u 0 \in OT_{\textrm{B}}\)と[Buc1] p.201 (OT2)より即座に従う。

(4) 任意の\(m \in \mathbb{N}\)に対し\(m < n\)ならば\(D_u^m 0 < D_u^n 0\)であることを\(m\)に関する数学的帰納法で示す。

\(m = 0\)ならば、\(D_u^m 0 = 0 < D_u^n 0\)である。

\(m > 0\)ならば、帰納法の仮定より\(D_u^{m-1} 0 < D_u^{n-1} 0\)であるので\(D_u^m 0 = D_u D_u^{m-1} 0 < D_u D_u^{n-1} 0 = D_u^n 0\)である。

特に\(\{D_u^m 0 \mid m \in \mathbb{N} \wedge m < n\} < D_u^n 0\)である。

\(G_u D_u^n 0 = \{D_u^m 0 \mid m \in \mathbb{N} \wedge m < n\}\)かつ\(D_u^n 0 \in OT_{\textrm{B}}\)であることを\(n\)に関する数学的帰納法で示す。

\(n = 0\)ならば、\(G_u D_u^n 0 = G_u 0 = \emptyset = \{D_u^m 0 \mid m \in \mathbb{N} \wedge m < n\}\)かつ\(D_u^n 0 = 0 \in OT_{\textrm{B}}\)である。

\(n > 0\)とする。

帰納法の仮定より\(G_u D_u^{n-1} 0 = \{D_u^m 0 \mid m \in \mathbb{N} \wedge m < n-1\}\)かつ\(D_u^{n-1} 0 \in OT_{\textrm{B}}\)である。

\(G_u D_u^n 0 = \{D_u^{n-1} 0\} \cup G_u D_u^{n-1} 0 = \{D_u^m 0 \mid m \in \mathbb{N} \wedge m < n\}\)である。

\(D_u^{n-1} 0 \in OT_{\textrm{B}}\)と\(G_u D_u^{n-1} 0 = \{D_u^m 0 \mid m \in \mathbb{N} \wedge m < n-1\} < D_u^{n-1} 0\)と[Buc1] p.201 (OT3)より\(D_u^n 0 \in OT_{\textrm{B}}\)である。□

補題（\(\textrm{Trans}\)が標準形を保つこと）

任意の\(M \in ST_{\textrm{PS}}\)に対し、\(\textrm{Trans}(M) \in OT_{\textrm{B}}\)である。

証明：

以下では順序数項の基本例を断りなく用いる。

\(k_0 := \min \{k \in \mathbb{N} \mid M \in S_kT_{\textrm{PS}}\}\)と置く[90]。

\(k_0\)に関する数学的帰納法で示す。

\(k_0 = 0\)とする。

一意な\((u,v) \in \mathbb{N}^2\)が存在して\(u \leq v\)かつ\(M = ((j,j))_{j=u}^{v}\)である。

\(u = v = 0\)ならば、\(\textrm{Trans}\)の定義より\(\textrm{Trans}(M) = 0 \in OT_{\textrm{B}}\)である。

\(u = v > 0\)ならば、\(\textrm{Trans}\)の定義より\(\textrm{Trans}(M) = D_u 0 \in OT_{\textrm{B}}\)である。

\(u < v\)ならば、公差\((1,1)\)のペア数列の\(\textrm{Trans}\)の基本性質から\(\textrm{Trans}(M[n]) = D_u D_v 0 \in OT_{\textrm{B}}\)である。

\(k_0 > 0\)とする。

\(N \in S_{k_0-1}T_{\textrm{PS}}\)と\(n \in \mathbb{N}_{+}\)を用いて\(M = N[n]\)と置く。

帰納法の仮定より\(\textrm{Trans}(N) \in OT_{\textrm{B}}\)である。

[Buc1] Lemma 3.3より、任意の\(m \in \mathbb{N}\)に対し\(\textrm{Trans}(N)[m]\)と\(\textrm{Trans}(N)[0]^m\)はいずれも順序数項である。

\(\textrm{Pred}(N) = M\)ならば、\(\textrm{Pred}\)と\([0]\)の関係よりある\(k \in \mathbb{N}\)が存在して\(\textrm{Trans}(M) = \textrm{Trans}(N)[0]^k\)となるので、\(\textrm{Trans}(M)\)は順序数項である。以下では\(\textrm{Pred}(N) \neq M\)とする。

\(N[1] = \textrm{Pred}(N) \neq M = N[n]\)より特に\(n > 1\)である。

標準形の簡約性から\(N\)は簡約である。簡約性と係数の関係から\(N\)は条件(A)と(B)を満たす。

\(((0,0))[n] = ((0,0)) \in S_0T_{\textrm{B}}\)かつ\(k_0 > 0\)であるので、\(N \neq ((0,0))\)である。従って\(N\)は単項または複項である。

\(N\)が単項であるとする。

\(\textrm{Trans}\)の再帰的定義中に導入した記号を\(N\)に対して定める。

\(t_1 = 0\)とする。

\(\textrm{Trans}\)が零項性を保つことより\(\textrm{Pred}(N)\)は零項である。従って\(j_1 = 1\)かつ\(N_{1,0} = 0\)である。\(N\)が単項でかつ条件(A)と(B)を満たすことから、\(N = ((0,0),(1,0))\)または\(N = ((0,0),(1,1))\)である。

\(N = ((0,0),(1,0))\)ならば、\(M = N[n] = ((0,0))_{j=0}^{n-1}\)であるので、公差\((0,0)\)のペア数列の\(\textrm{Trans}\)の基本性質から\(\textrm{Trans}(M) = (D_0 0) \times (n-1) \in OT_{\textrm{B}}\)である。

<<<MISSING line 6170 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6171 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6172 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6173 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6174 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6175 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6176 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6177 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6178 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6179 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6180 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6181 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6182 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6183 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6184 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6185 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6186 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6187 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6188 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6189 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6190 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6191 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6192 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6193 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6194 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6195 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6196 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6197 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6198 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6199 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6200 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6201 — recover from original.html via tools/make_content.py>>>
特に\(\textrm{Pred}(N[n+1][1]^{j_1-1-j_{-2}}) = M\)かつ\(\textrm{Trans}(N[n+1][1]^{j_1-1-j_{-2}})\)が順序数項であるので、\(\textrm{Pred}\)と\([0]\)の関係よりある\(k \in \mathbb{N}\)が存在して\(\textrm{Trans}(M) = \textrm{Trans}(N[n+1][1]^{j_1-1-j_{-2}})[0]^k = \textrm{Trans}(N)[n-1][0]^k\)となる。従って[Buc1] Lemma 3.3より\(\textrm{Trans}(M)\)は順序数項である。
<<<MISSING line 6203 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6204 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6205 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6206 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6207 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6208 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6209 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6210 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6211 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6212 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6213 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6214 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6215 — recover from original.html via tools/make_content.py>>>
従って順序数項の末尾単項の零化可能性よりある\(k \in \mathbb{N}\)が存在して\(\textrm{Trans}(M)  = \textrm{Trans}(N[n]) = \textrm{Trans}(N)[m_n][0]^k\)であるので、[Buc1] Lemma 3.3より\(\textrm{Trans}(M)\)は順序数項である。
<<<MISSING line 6217 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6218 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6219 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6220 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6221 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6222 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6223 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6224 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6225 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6226 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6227 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6228 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6229 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6230 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6231 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6232 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6233 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6234 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6235 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6236 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6237 — recover from original.html via tools/make_content.py>>>
\(P\)の各成分の非複項性から\(J_1 > 0\)である。\(\textrm{Pred}(N) \neq M = N[n]\)より\(\textrm{Lng}(P(N)_{J_1}) > 1\)である。従って\(P\)と基本列の関係 (2)から\(P(M) = P(N[n]) = (P(N)_J)_{J=0}^{J_1-1} \oplus_{T_{\textrm{PS}}} P(P(N)_{J_1}[n])\)である。
<<<MISSING line 6239 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6240 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6241 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6242 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6243 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6244 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6245 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6246 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6247 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6248 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6249 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6250 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6251 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6252 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6253 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6254 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6255 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6256 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6257 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6258 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6259 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6260 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6261 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6262 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6263 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6264 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6265 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6266 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6267 — recover from original.html via tools/make_content.py>>>
text \<open>m: 命題（Lng の Red 不変性） — discharges p_6_5_Lng_Red.\<close>
<<<MISSING line 6269 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6270 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6271 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6272 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6273 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6274 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6275 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6276 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6277 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6278 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6279 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6280 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6281 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6282 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6283 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6284 — recover from original.html via tools/make_content.py>>>
標準形の単項成分が標準形であることから\(P(N)_{J_1} \in S_{k_0-1}T_{\textrm{PS}}\)であるので、\(P(N)_{J_1}[n] \in S_{k_0}T_{\textrm{PS}}\)である。
<<<MISSING line 6286 — recover from original.html via tools/make_content.py>>>
\(\textrm{Lng}(P(N)_{J_1}) > 1\)かつ標準形であることから、基本列の降下性より\(\Sigma_{\textrm{B}} a_2 = \textrm{Trans}(P(N)_{J_1}[n]) < \textrm{Trans}(P(N)_{J_1})\)である。従って\(a_2\)の各成分は\(\textrm{Trans}(P(N)_{J_1})\)未満である。
<<<MISSING line 6288 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6289 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6290 — recover from original.html via tools/make_content.py>>>
\(P(N)_{J_1}[n] \in S_{k_0-1}T_{\textrm{PS}}\)でないならば、\(k_0 = \min \{k \in \mathbb{N} \mid P(N)_{J_1} \in S_kT_{\textrm{PS}}\}\)であるので\(P(N)_{J_1}\)が単項であることから\(\textrm{Trans}(P(N)_{J_1}[n])\)は順序数項である[92]。
<<<MISSING line 6292 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6293 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6294 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6295 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6296 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6297 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6298 — recover from original.html via tools/make_content.py>>>
\(a_0 \oplus_{T_{\textrm{B}}} a_1\)の成分から\(0\)を除いた\(PT_{\textrm{B}}\)値配列が降順であることを示す。。
<<<MISSING line 6300 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6301 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6302 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6303 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6304 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6305 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6306 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6307 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6308 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6309 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6310 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6311 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6312 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6313 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6314 — recover from original.html via tools/make_content.py>>>
\(P(N)_{J_1}\)の単項性と非複項性と基本列の関係から\(P(P(N)_{J_1}[n])\)の各成分は等しく零項となる。従って\(a_1 = (D_0 0)_{J=0}^{J_2}\)かつ\(a_2 = (0) \oplus_{T_{\textrm{B}}} (D_0 0)_{J=1}^{J_2}\)である。
<<<MISSING line 6316 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6317 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6318 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6319 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6320 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6321 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6322 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6323 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6324 — recover from original.html via tools/make_content.py>>>
以上より、\(\textrm{Trans}(M) = \Sigma_{\textrm{B}} (a_0 \oplus_{T_{\textrm{B}}} a_1)\)は順序数項の降順の和である。従って順序数項の再帰的定義[Buc1] p. 201 (OT2)から\(\textrm{Trans}(M)\)は順序数項である。□
<<<MISSING line 6326 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6327 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6328 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6329 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6330 — recover from original.html via tools/make_content.py>>>
[Buc1] Lemma 2.2より\((OT_{\textrm{B}},<)\)は整礎である。従って\((OT_{\textrm{B}},<)\)に対して数学的帰納法が適用可能である。
<<<MISSING line 6332 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6333 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6334 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6335 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6336 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6337 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6338 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6339 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6340 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6341 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6342 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6343 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6344 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6345 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6346 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6347 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6348 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6349 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6350 — recover from original.html via tools/make_content.py>>>
基本列の降下性より\(\textrm{Trans}(M[n]) < \textrm{Trans}(M) = t\)である。\(M\)が標準形であることと標準形の再帰的定義から\(M[n]\)も標準形であるので、\(\textrm{Trans}\)が標準形を保つことより\(\textrm{Trans}(M[n])\)は順序数項である。従って帰納法の仮定より、\((M[n],n) \in \textrm{Dom}(F)\)である。
<<<MISSING line 6352 — recover from original.html via tools/make_content.py>>>
\(F_M\)と基本列の関係より\((M,n) \in \textrm{Dom}(F)\)である。□
<<<MISSING line 6354 — recover from original.html via tools/make_content.py>>>
# 謝辞[]
<<<MISSING line 6356 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6357 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6358 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6359 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6360 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6361 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6362 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6363 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6364 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6365 — recover from original.html via tools/make_content.py>>>
<<<MISSING line 6366 — recover from original.html via tools/make_content.py>>>
# 脚注[]

- ↑ 当初の予定ではペア数列の解析、すなわちペア数列システムに伴う順序数表記系の限界を決定するつもりだったが、停止性の証明までを書き切るだけで大変疲れてしまった上に需要もさほどないと思うため、停止性までに留めた。

- ↑ その証明を厳密に記述した記事は知らないが、初等的であるためわざわざ書くほどでもないのだろう。

- ↑ \(M_{j_1} \neq (0,0)\)より\(\max\)は存在する。

- ↑ \(M_{j_1} \neq (0,0)\)より\(\max\)は存在する。

- ↑ \(M\)が複項より\(0 < j_1\)であり、かつ\((0,j_1) \leq_M (0,j_1)\)であるので\(\min\)は存在する。

- ↑ \(j = j_1\)が条件を満たすため、\(\min\)は存在する。

- ↑ \(j'_0-j_0\)と\(j_0\)の辞書式順序の順序型は\(\omega \times \omega\)であるため整礎であり、数学的帰納法が適用可能である。

- ↑ \(0\)は\(M\)許容であり、かつ\(j\)は非\(M\)許容より\(j > 0\)であるので、\(\max\)は存在する。

- ↑ \(j = 0\)が条件を満たし、かつ条件を満たす\(j\)は\(\textrm{Lng}(M)\)未満であるため、最大値が存在する。

- ↑ \(M\)の単項性から\((0,0) \leq_M (0,\textrm{FirstNodes}(M)_J)\)であり、\(\textrm{FirstNodes}(M)_J > j'_1 \geq 0\)より\(j\)は存在する。

- ↑ \(M\)は零項でないので、この時\(j_1 > 0\)である。

- ↑ \(M\)が単項より\((0,0) \leq_M (0,\textrm{FirstNodes}(M)_J)\)であり、\(M_{0,0} = 0 < (\textrm{Br}(M)_J)_{1,0} = M_{1,\textrm{FirstNode}(M)_J}\)と親の存在の判定条件 (2)から\(j\)は存在する。

- ↑ \(\textrm{FirstNodes}\)と\(\textrm{TrMax}\)と\(\textrm{Joints}\)の関係より\(\textrm{Joints}(M)_J \leq \textrm{TrMax}(M)\)なので\(M_{0,0} + \textrm{Joints}(M)_J \leq M_{0,\textrm{Joints}(M)}\)であり、\((0,\textrm{Joints}(M)_J) <_M^{\textrm{Next}} (0,\textrm{FirstNodes}(M)_J)\)より\(M_{0,\textrm{Joints}(M)_J} < M_{0,\textrm{FirstNodes}(M)_J}\)であるので\(M_{0,0} + \textrm{Joints}(M)_J + 1 \leq M_{0,\textrm{FirstNodes}(M)_J}\)となり、\(\textrm{Br}(M)_J\)が非複項であったので\(N_J\)も非複項となる。

- ↑ \(\textrm{Joints}(M)_J\)と\(n_J\)の定義より\(\textrm{Joints}(M)_J \geq n_J\)なので\(\textrm{IncrFirst}^{\textrm{Joints}(M)_J-n_J}\)は意味を持つ。

- ↑ \(M\)は零項でないので、この時\(j_1 > 0\)である。

- ↑ \(N_0 = (0,0)\)であり、\(M\)が単項より直系先祖の基本性質 (1)から任意の\(j \in \mathbb{N}\)に対し\(0 < j \leq j_1\)ならば\(M_{0,0} < M_{0,j}\)であるので\(N_j \in \mathbb{N}^2\)となり、\(\leq_M\)と\(\leq_N\)は等しいので\(N\)は単項である。

- ↑ \(N_0 = (0,0)\)であり、任意の\(j \in \mathbb{N}\)に対し\(j < M_{1,0} + \textrm{Lng}(M)\)ならば\(N_{1,j} > 0\)なので\(N\)は単項である。

- ↑ \((N_j)_{j=M_{1,0}}^{j_1} \in PT_{\textrm{PS}}\)より任意の\(j \in \mathbb{N}\)に対し\(M_{1,0} < j \leq j_1\)ならば\(N_{0,M_{1,0}} < N_{0,j}\)であるので\((N_{0,j}-N_{0,M_{1,0}}+N_{1,M_{1,0}},N_{1,j}) \in \mathbb{N}^2\)である。

- ↑ 後で証明する単項性と\(\textrm{Red}\)の関係により、この分岐が生じないことが分かる。

- ↑ 後で証明する\(\textrm{Lng}\)の\(\textrm{Red}\)不変性により、この分岐が生じないことが分かる。

- ↑ \(j = 0\)が条件を満たすため\(\max\)は存在する。

- ↑ 簡約性と係数の関係より\(M_{0,j'_0} - M_{1,j'_0} \geq 0\)であるので\(\textrm{IncrFirst}^{M_{0,j'_0} - M_{1,j'_0}}\)は意味を持つ。

- ↑ \(S = T_{\textrm{PS}}\)が条件を満たし、条件を満たす\(S\)全体の共通部分もまた条件を満たすため、最小の\(S\)が存在する。

- ↑ \(ST_{\textrm{PS}} = \bigcup_{k \in \mathbb{N}} S_kT_{\textrm{PS}}\)より\(\min\)は存在する。

- ↑ [Buc1] p. 200参照。

- ↑ [Buc1] p. 201参照。

- ↑ [Buc1] p. 200参照。

- ↑ [Buc1] p. 203参照。

- ↑ [Buc1] p. 203参照。

- ↑ すなわち[Buc1] ([].4) (ii)の場合分けにおいて、各\(i \in \mathbb{N}\)に対し\(x_i\)を「\(i = 0\)ならば\(x_i = D_u 0\)、\(i > 0\)ならば\(x_i = b[D_u x_{i-1}]\)」と定め、\(a[n]\)の定義を\(D_v b[x_n]\)に変えるということである。

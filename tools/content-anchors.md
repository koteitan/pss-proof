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

- ペア数列の展開規則と\(\textrm{Trans}\)による像の基本列を比較する。

- これにより、標準形ペア数列の\(\textrm{Trans}\)による像がBuchholzの順序数項を定めることを示す。

- 更にBuchholzの順序数項が標準的な全順序に関して整礎であることと基本列がその順序に関して降下することから、標準形ペア数列システムの停止性が従う。

方針の概説も参考にすると良い。

なお\(n \in \mathbb{N}\)に対する命題\(P(n), Q(n)\)に対して「任意の\(n \in \mathbb{N}\)に対し\(P(n) \to Q(n)\)」を\(n\)に関する数学的帰納法で示す際に、\(P(0)\)が成り立たない場合は\(P(0) \to Q(0)\)が成り立つので「任意の\(n \in \mathbb{N}\)に対し\(P(n) \to Q(n)\)ならば\(P(n+1) \to Q(n+1)\)」を示すだけで良いのだが、読者の理解の助けになるようになるべく記事中では\(P(n_0)\)が成り立つ最小の\(n_0 \in \mathbb{N}\)を調べて\(Q(n_0)\)も示すようにする。

# 参考文献[]

- [Buc1] W. Buchholz, A new system of proof-theoretic ordinal functions, Annals of Pure and Applied Logic, Volume 32, 1986, pp. 195--207.

- [Buc2] W. Buchholz, Relating ordinals to proofs in a prespicious way, unpublished article.

# 記法[]

\(\mathbb{N}\)で非負整数全体の集合を表し、\(\mathbb{N}_{+}\)で正整数全体の集合を表す。

クラス\(A\)に対し、集合\(a\)が\(A\)値配列であるとは、ある\(n \in \mathbb{N}\)が存在して\(a \in A^n\)ということである。このような\(n\)は\(a\)に対して一意であるので\(\textrm{Lng}(a)\)と表す。\(\textrm{Lng}(a) = 0\)の時、\(A\)に紛れのない限り\(a\)を\(()\)と表す。\(i < \textrm{Lng}(a)\)を満たす各\(i \in \mathbb{N}\)に対し、\(a\)の第\(i\)成分を\(a_i \in A\)と表す。

\(i_0 \leq i_1\)を満たす各\(i_0,i_1 \in \mathbb{N}\)と、\(\{i \in \mathbb{N} \mid i_0 \leq i \leq i_1\}\)を定義域に含む各\(A\)値関数\(f\)に対し、長さが\(i_1-i_0+1\)であって任意の\(i \in \mathbb{N}\)に対し\(i \leq i_1-i_0\)ならば第\(i\)成分が\(f(i_0+i)\)であるような\(A\)値配列を\((f(i))_{i=i_0}^{i_1}\)と表す。\(i_0 \leq i_1\)を満たさないかまたは\(\{i \in \mathbb{N} \mid i_0 \leq i \leq i_1\}\)を\(f\)が定義域に含まないような各\(i_0,i_1 \in \mathbb{N}\)と各\(A\)値関数\(f\)に対し、\((a_i)_{i=i_0}^{i_1} := ()\)と置く。

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
\begin{eqnarray*}
\textrm{Derp} \colon T_{\textrm{PS}} & \to & T_{\textrm{PS}} \cup \{()\} \\
M & \mapsto & \textrm{Derp}(M)
\end{eqnarray*}
を以下のように定める：

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

証明：

\(M' := (M_j)_{j=j'_0}^{j'_1}\)と置く。任意の\(j \in \mathbb{N}\)に対し\(0 < j \leq j'_1-j'_0\)を満たすならば、直系先祖の基本性質 (1)と\((0,j'_0) \leq_M (0,j'_1)\)より\(M'_{0,0} = M_{0,j'_0} < M_{0,j'_0+j} = M'_{0,j}\)である。従って親の存在の判定条件 (3)より\((0,0) \leq_{M'} (0,j'_1-j'_0)\)である。\(\textrm{Lng}(M') = j'_1 - j'_0 > 0\)であるので、\(M'\)は零項でない。以上より\(M'\)は単項である。□

写像
\begin{eqnarray*}
P \colon T_{\textrm{PS}} & \to & T_{\textrm{PS}}^{< \omega} \\
M & \mapsto & P(M)
\end{eqnarray*}
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

- \(j > j_1\)である。

- \((1,j-1) <_M^{\textrm{Next}} (1,j) <_M^{\textrm{Next}} (1,j+1)\)である。

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

証明：

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

<<<MISSING line 1265 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1266 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1267 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1268 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1269 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1270 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1271 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1272 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1273 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1274 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1275 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1276 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1277 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1278 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1279 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1280 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1281 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1282 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1283 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1284 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1285 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1286 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1287 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1288 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1289 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1290 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1291 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1292 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1293 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1294 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1295 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1296 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1297 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1298 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1299 — recover from Googology Wiki article 'ペア数列の停止性'>>>
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

<<<MISSING line 1628 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1629 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1630 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1631 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1632 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1633 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1634 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1635 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1636 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1637 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1638 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1639 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1640 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1641 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1642 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1643 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1644 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1645 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1646 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1647 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1648 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1649 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1650 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1651 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1652 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1653 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1654 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1655 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1656 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1657 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1658 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1659 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1660 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1661 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1662 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1663 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1664 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1665 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1666 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1667 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1668 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1669 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1670 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1671 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1672 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1673 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1674 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1675 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1676 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1677 — recover from Googology Wiki article 'ペア数列の停止性'>>>
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

<<<MISSING line 1836 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1837 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1838 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1839 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1840 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1841 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1842 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1843 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1844 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1845 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1846 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1847 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1848 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1849 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1850 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1851 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1852 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1853 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1854 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1855 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1856 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1857 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1858 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1859 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1860 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1861 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1862 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1863 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1864 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1865 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1866 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1867 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1868 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1869 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1870 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1871 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1872 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1873 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1874 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1875 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1876 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1877 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1878 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1879 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1880 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1881 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1882 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1883 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1884 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1885 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1886 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1887 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1888 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1889 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1890 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1891 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1892 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1893 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1894 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1895 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1896 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1897 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1898 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1899 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1900 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1901 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1902 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1903 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1904 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1905 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1906 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1907 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1908 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1909 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1910 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1911 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1912 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1913 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1914 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1915 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1916 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1917 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1918 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1919 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1920 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1921 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1922 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1923 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1924 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1925 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1926 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1927 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1928 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1929 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1930 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1931 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1932 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1933 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1934 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1935 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1936 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1937 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1938 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1939 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1940 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1941 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1942 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1943 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1944 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1945 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1946 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1947 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1948 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1949 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1950 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1951 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1952 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1953 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1954 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1955 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1956 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1957 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1958 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1959 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1960 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1961 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1962 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1963 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1964 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1965 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1966 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1967 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1968 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1969 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1970 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1971 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1972 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1973 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1974 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1975 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1976 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1977 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1978 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1979 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1980 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1981 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1982 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1983 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1984 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1985 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1986 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1987 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1988 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1989 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1990 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1991 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1992 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1993 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1994 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1995 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1996 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1997 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1998 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 1999 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2000 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2001 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2002 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2003 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2004 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2005 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2006 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2007 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2008 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2009 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2010 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2011 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2012 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2013 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2014 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2015 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2016 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2017 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2018 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2019 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2020 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2021 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2022 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2023 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2024 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2025 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2026 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2027 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2028 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2029 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2030 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2031 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2032 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2033 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2034 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2035 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2036 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2037 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2038 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2039 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2040 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2041 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2042 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2043 — recover from Googology Wiki article 'ペア数列の停止性'>>>
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

<<<MISSING line 2302 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2303 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2304 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2305 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2306 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2307 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2308 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2309 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2310 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2311 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2312 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2313 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2314 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2315 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2316 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2317 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2318 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2319 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2320 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2321 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2322 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2323 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2324 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2325 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2326 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2327 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2328 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2329 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2330 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2331 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2332 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2333 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2334 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2335 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2336 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2337 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2338 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2339 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2340 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2341 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2342 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2343 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2344 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2345 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2346 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2347 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2348 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2349 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2350 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2351 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2352 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2353 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2354 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2355 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2356 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2357 — recover from Googology Wiki article 'ペア数列の停止性'>>>
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

<<<MISSING line 2378 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2379 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2380 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2381 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2382 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2383 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2384 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2385 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2386 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2387 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2388 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2389 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2390 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2391 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2392 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2393 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2394 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2395 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2396 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2397 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2398 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2399 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2400 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2401 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2402 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2403 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2404 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2405 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2406 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2407 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2408 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2409 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2410 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2411 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2412 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2413 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2414 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2415 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2416 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2417 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2418 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2419 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2420 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2421 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2422 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2423 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2424 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2425 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2426 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2427 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2428 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2429 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2430 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2431 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2432 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2433 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2434 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2435 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2436 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2437 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2438 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2439 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2440 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2441 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2442 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2443 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2444 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2445 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2446 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2447 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2448 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2449 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2450 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2451 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2452 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2453 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2454 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2455 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2456 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2457 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2458 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2459 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2460 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2461 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2462 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2463 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2464 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2465 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2466 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2467 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2468 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2469 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2470 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2471 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2472 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2473 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2474 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2475 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2476 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2477 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2478 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2479 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2480 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2481 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2482 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2483 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2484 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2485 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2486 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2487 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2488 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2489 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2490 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2491 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2492 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2493 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2494 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2495 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2496 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2497 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2498 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2499 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2500 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2501 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2502 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2503 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2504 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2505 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2506 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2507 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2508 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2509 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2510 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2511 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2512 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2513 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2514 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2515 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2516 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2517 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2518 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2519 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2520 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2521 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2522 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2523 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2524 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2525 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2526 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2527 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2528 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2529 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2530 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2531 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2532 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2533 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2534 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2535 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2536 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2537 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2538 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2539 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2540 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2541 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2542 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2543 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2544 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2545 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2546 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2547 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2548 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2549 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2550 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2551 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2552 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2553 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2554 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2555 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2556 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2557 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2558 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2559 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2560 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2561 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2562 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2563 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2564 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2565 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2566 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2567 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2568 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2569 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2570 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2571 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2572 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2573 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2574 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2575 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2576 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2577 — recover from Googology Wiki article 'ペア数列の停止性'>>>
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

<<<MISSING line 2638 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2639 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2640 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2641 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2642 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2643 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2644 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2645 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2646 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2647 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2648 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2649 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2650 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2651 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2652 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2653 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2654 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2655 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2656 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2657 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2658 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2659 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2660 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2661 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2662 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2663 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2664 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2665 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2666 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2667 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2668 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2669 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2670 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2671 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2672 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2673 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2674 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2675 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2676 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2677 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2678 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2679 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2680 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2681 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2682 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2683 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2684 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2685 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2686 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2687 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2688 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2689 — recover from Googology Wiki article 'ペア数列の停止性'>>>
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
<<<MISSING line 2750 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2751 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2752 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2753 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2754 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2755 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2756 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2757 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2758 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2759 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2760 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2761 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2762 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2763 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2764 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2765 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2766 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2767 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2768 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2769 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2770 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2771 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2772 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2773 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2774 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2775 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2776 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2777 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2778 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2779 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2780 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2781 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2782 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2783 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2784 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2785 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2786 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2787 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2788 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2789 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2790 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2791 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2792 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2793 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2794 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2795 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2796 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2797 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2798 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2799 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2800 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2801 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2802 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2803 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2804 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2805 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2806 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2807 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2808 — recover from Googology Wiki article 'ペア数列の停止性'>>>
系（非零項の\(\textrm{RightAnces}\)が非空であること）

任意の\(M \in T_{\textrm{PS}}\)に対し、以下は同値である：

(1) \(M\)は零項である。

(2) \(\textrm{RightAnces}(M) = ()\)である。

証明：

\(\textrm{Trans}\)が零項性を保つことと\(\textrm{RightNodes}\)と\(\textrm{RightAnces}\)の関係から即座に従う。□

# 停止性[]

まずは単項な標準形ペア数列に対し条件(I)～(VI)のそれぞれの下での展開規則を調べ、それによりBuchholzの表記系における展開規則との比較を行い、標準形ペア数列に伴う計算可能関数の全域性（すなわち計算規則の停止性）を証明する。

<<<MISSING line 2825 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2826 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2827 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2828 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2829 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2830 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2831 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2832 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2833 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2834 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2835 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2836 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2837 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2838 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2839 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2840 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2841 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2842 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2843 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2844 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2845 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2846 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2847 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2848 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2849 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2850 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2851 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2852 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2853 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2854 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2855 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2856 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2857 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2858 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2859 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2860 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2861 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2862 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2863 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2864 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2865 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2866 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2867 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2868 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2869 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2870 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2871 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2872 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2873 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2874 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2875 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2876 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2877 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2878 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2879 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2880 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2881 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2882 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2883 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2884 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2885 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2886 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2887 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2888 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2889 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2890 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2891 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2892 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2893 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2894 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2895 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2896 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2897 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2898 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2899 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2900 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2901 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2902 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2903 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2904 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2905 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2906 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2907 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2908 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2909 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2910 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2911 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2912 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2913 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2914 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2915 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2916 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2917 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2918 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2919 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2920 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2921 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2922 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2923 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2924 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2925 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2926 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2927 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2928 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2929 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2930 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2931 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2932 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2933 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2934 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2935 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2936 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2937 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2938 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2939 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2940 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2941 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2942 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2943 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2944 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2945 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2946 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2947 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2948 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2949 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2950 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2951 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2952 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2953 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2954 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2955 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2956 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2957 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2958 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2959 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2960 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2961 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2962 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2963 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2964 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2965 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2966 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2967 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2968 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2969 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2970 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2971 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2972 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2973 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2974 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2975 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2976 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2977 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2978 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2979 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2980 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2981 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2982 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2983 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2984 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2985 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2986 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2987 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2988 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2989 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2990 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2991 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2992 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2993 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2994 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2995 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2996 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2997 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2998 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 2999 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3000 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3001 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3002 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3003 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3004 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3005 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3006 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3007 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3008 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3009 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3010 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3011 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3012 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3013 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3014 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3015 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3016 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3017 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3018 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3019 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3020 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3021 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3022 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3023 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3024 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3025 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3026 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3027 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3028 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3029 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3030 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3031 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3032 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3033 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3034 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3035 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3036 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3037 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3038 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3039 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3040 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3041 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3042 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3043 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3044 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3045 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3046 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3047 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3048 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3049 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3050 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3051 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3052 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3053 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3054 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3055 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3056 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3057 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3058 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3059 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3060 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3061 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3062 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3063 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3064 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3065 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3066 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3067 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3068 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3069 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3070 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3071 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3072 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3073 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3074 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3075 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3076 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3077 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3078 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3079 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3080 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3081 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3082 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3083 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3084 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3085 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3086 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3087 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3088 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3089 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3090 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3091 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3092 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3093 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3094 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3095 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3096 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3097 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3098 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3099 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3100 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3101 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3102 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3103 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3104 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3105 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3106 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3107 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3108 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3109 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3110 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3111 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3112 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3113 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3114 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3115 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3116 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3117 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3118 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3119 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3120 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3121 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3122 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3123 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3124 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3125 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3126 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3127 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3128 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3129 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3130 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3131 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3132 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3133 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3134 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3135 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3136 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3137 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3138 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3139 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3140 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3141 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3142 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3143 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3144 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3145 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3146 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3147 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3148 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3149 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3150 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3151 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3152 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3153 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3154 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3155 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3156 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3157 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3158 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3159 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3160 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3161 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3162 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3163 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3164 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3165 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3166 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3167 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3168 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3169 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3170 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3171 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3172 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3173 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3174 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3175 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3176 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3177 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3178 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3179 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3180 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3181 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3182 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3183 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3184 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3185 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3186 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3187 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3188 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3189 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3190 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3191 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3192 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3193 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3194 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3195 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3196 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3197 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3198 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3199 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3200 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3201 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3202 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3203 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3204 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3205 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3206 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3207 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3208 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3209 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3210 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3211 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3212 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3213 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3214 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3215 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3216 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3217 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3218 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3219 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3220 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3221 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3222 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3223 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3224 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3225 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3226 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3227 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3228 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3229 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3230 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3231 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3232 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3233 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3234 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3235 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3236 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3237 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3238 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3239 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3240 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3241 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3242 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3243 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3244 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3245 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3246 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3247 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3248 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3249 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3250 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3251 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3252 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3253 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3254 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3255 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3256 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3257 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3258 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3259 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3260 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3261 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3262 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3263 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3264 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3265 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3266 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3267 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3268 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3269 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3270 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3271 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3272 — recover from Googology Wiki article 'ペア数列の停止性'>>>
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

<<<MISSING line 3380 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3381 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3382 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3383 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3384 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3385 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3386 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3387 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3388 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3389 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3390 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3391 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3392 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3393 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3394 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3395 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3396 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3397 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3398 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3399 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3400 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3401 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3402 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3403 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3404 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3405 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3406 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3407 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3408 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3409 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3410 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3411 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3412 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3413 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3414 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3415 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3416 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3417 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3418 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3419 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3420 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3421 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3422 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3423 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3424 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3425 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3426 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3427 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3428 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3429 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3430 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3431 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3432 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3433 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3434 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3435 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3436 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3437 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3438 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3439 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3440 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3441 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3442 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3443 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3444 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3445 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3446 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3447 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3448 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3449 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3450 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3451 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3452 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3453 — recover from Googology Wiki article 'ペア数列の停止性'>>>
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

<<<MISSING line 3544 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3545 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3546 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3547 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3548 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3549 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3550 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3551 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3552 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3553 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3554 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3555 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3556 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3557 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3558 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3559 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3560 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3561 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3562 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3563 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3564 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3565 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3566 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3567 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3568 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3569 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3570 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3571 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3572 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3573 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3574 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3575 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3576 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3577 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3578 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3579 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3580 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3581 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3582 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3583 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3584 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3585 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3586 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3587 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3588 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3589 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3590 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3591 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3592 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3593 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3594 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3595 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3596 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3597 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3598 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3599 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3600 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3601 — recover from Googology Wiki article 'ペア数列の停止性'>>>
補題（条件(V)の下での右端の親の基本性質）

任意の\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)と\(m \in \mathbb{N}\)に対し、\(j_1 := \textrm{Lng}(M)-1\)と置き、\(J_1 := \textrm{Lng}(\textrm{Br}(M))-1\)と置き、\(J_1 \geq 0\)として\(j'_0 := \textrm{Joints}(M)_{J_1}\)と置き、\(j'_1 := \textrm{FirstNodes}(M)_{J_1}\)と置き、\(M' := (M_j)_{j=m}^{j_1}\)と置くと、「\(m < j'_0\)」または「\(m = j'_0\)かつ\(M_{0,j'_1} = M_{1,j'_1}\)かつ\(\textrm{Br}(M)\)が降順」ならば、一意な\(j_0 \in \mathbb{N}\)が存在して以下を満たす：

(1) \((0,j_0) <_M^{\textrm{Next}} (0,j_1)\)である。

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
<<<MISSING line 3679 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3680 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3681 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3682 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3683 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3684 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3685 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3686 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3687 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3688 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3689 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3690 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3691 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3692 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3693 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3694 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3695 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3696 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3697 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3698 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3699 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3700 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3701 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3702 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3703 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3704 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3705 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3706 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3707 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3708 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3709 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3710 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3711 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3712 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3713 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3714 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3715 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3716 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3717 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3718 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3719 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3720 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3721 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3722 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3723 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3724 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3725 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3726 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3727 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3728 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3729 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3730 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3731 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3732 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3733 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3734 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3735 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3736 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3737 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3738 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3739 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3740 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3741 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3742 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3743 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3744 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3745 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3746 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3747 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3748 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3749 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3750 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3751 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3752 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3753 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3754 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3755 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3756 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3757 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3758 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3759 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3760 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3761 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3762 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3763 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3764 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3765 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3766 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3767 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3768 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3769 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3770 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3771 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3772 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3773 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3774 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3775 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3776 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3777 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3778 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3779 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3780 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3781 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3782 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3783 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3784 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3785 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3786 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3787 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3788 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3789 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3790 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3791 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3792 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3793 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3794 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3795 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3796 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3797 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3798 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3799 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3800 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3801 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3802 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3803 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3804 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3805 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3806 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3807 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3808 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3809 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3810 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3811 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3812 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3813 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3814 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3815 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3816 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3817 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3818 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3819 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3820 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3821 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3822 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3823 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3824 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3825 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3826 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3827 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3828 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3829 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3830 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3831 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3832 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3833 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3834 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3835 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3836 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3837 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3838 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3839 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3840 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3841 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3842 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3843 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3844 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3845 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3846 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3847 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3848 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3849 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3850 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3851 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3852 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3853 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3854 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3855 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3856 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3857 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3858 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3859 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3860 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3861 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3862 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3863 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3864 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3865 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3866 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3867 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3868 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3869 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3870 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3871 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3872 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3873 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3874 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3875 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3876 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3877 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3878 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3879 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3880 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3881 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3882 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3883 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3884 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3885 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3886 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3887 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3888 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3889 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3890 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3891 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3892 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3893 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3894 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3895 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3896 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3897 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3898 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3899 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3900 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3901 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3902 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3903 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3904 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3905 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3906 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3907 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3908 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3909 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3910 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3911 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3912 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3913 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3914 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3915 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3916 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3917 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3918 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3919 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3920 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3921 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3922 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3923 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3924 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3925 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3926 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3927 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3928 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3929 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3930 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3931 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3932 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3933 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3934 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3935 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3936 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3937 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3938 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3939 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3940 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3941 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3942 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3943 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3944 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3945 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3946 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3947 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3948 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3949 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3950 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3951 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3952 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3953 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3954 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3955 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3956 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3957 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3958 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3959 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3960 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3961 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3962 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3963 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3964 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3965 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3966 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3967 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3968 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3969 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3970 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3971 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3972 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3973 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3974 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3975 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3976 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3977 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3978 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3979 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3980 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3981 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3982 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3983 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3984 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3985 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3986 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3987 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3988 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3989 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3990 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3991 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3992 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3993 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3994 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3995 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3996 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3997 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3998 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 3999 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4000 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4001 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4002 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4003 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4004 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4005 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4006 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4007 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4008 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4009 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4010 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4011 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4012 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4013 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4014 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4015 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4016 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4017 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4018 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4019 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4020 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4021 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4022 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4023 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4024 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4025 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4026 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4027 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4028 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4029 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4030 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4031 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4032 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4033 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4034 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4035 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4036 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4037 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4038 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4039 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4040 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4041 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4042 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4043 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4044 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4045 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4046 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4047 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4048 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4049 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4050 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4051 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4052 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4053 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4054 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4055 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4056 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4057 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4058 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4059 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4060 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4061 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4062 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4063 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4064 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4065 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4066 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4067 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4068 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4069 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4070 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4071 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4072 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4073 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4074 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4075 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4076 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4077 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4078 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4079 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4080 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4081 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4082 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4083 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4084 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4085 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4086 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4087 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4088 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4089 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4090 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4091 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4092 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4093 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4094 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4095 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4096 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4097 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4098 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4099 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4100 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4101 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4102 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4103 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4104 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4105 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4106 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4107 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4108 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4109 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4110 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4111 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4112 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4113 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4114 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4115 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4116 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4117 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4118 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4119 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4120 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4121 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4122 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4123 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4124 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4125 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4126 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4127 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4128 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4129 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4130 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4131 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4132 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4133 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4134 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4135 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4136 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4137 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4138 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4139 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4140 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4141 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4142 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4143 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4144 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4145 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4146 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4147 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4148 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4149 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4150 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4151 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4152 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4153 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4154 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4155 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4156 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4157 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4158 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4159 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4160 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4161 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4162 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4163 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4164 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4165 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4166 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4167 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4168 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4169 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4170 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4171 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4172 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4173 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4174 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4175 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4176 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4177 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4178 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4179 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4180 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4181 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4182 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4183 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4184 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4185 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4186 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4187 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4188 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4189 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4190 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4191 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4192 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4193 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4194 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4195 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4196 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4197 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4198 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4199 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4200 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4201 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4202 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4203 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4204 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4205 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4206 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4207 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4208 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4209 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4210 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4211 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4212 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4213 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4214 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4215 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4216 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4217 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4218 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4219 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4220 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4221 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4222 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4223 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4224 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4225 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4226 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4227 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4228 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4229 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4230 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4231 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4232 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4233 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4234 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4235 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4236 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4237 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4238 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4239 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4240 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4241 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4242 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4243 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4244 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4245 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4246 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4247 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4248 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4249 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4250 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4251 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4252 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4253 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4254 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4255 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4256 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4257 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4258 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4259 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4260 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4261 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4262 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4263 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4264 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4265 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4266 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4267 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4268 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4269 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4270 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4271 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4272 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4273 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4274 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4275 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4276 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4277 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4278 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4279 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4280 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4281 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4282 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4283 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4284 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4285 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4286 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4287 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4288 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4289 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4290 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4291 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4292 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4293 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4294 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4295 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4296 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4297 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4298 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4299 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4300 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4301 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4302 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4303 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4304 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4305 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4306 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4307 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4308 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4309 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4310 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4311 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4312 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4313 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4314 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4315 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4316 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4317 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4318 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4319 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4320 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4321 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4322 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4323 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4324 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4325 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4326 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4327 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4328 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4329 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4330 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4331 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4332 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4333 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4334 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4335 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4336 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4337 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4338 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4339 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4340 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4341 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4342 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4343 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4344 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4345 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4346 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4347 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4348 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4349 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4350 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4351 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4352 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4353 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4354 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4355 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4356 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4357 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4358 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4359 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4360 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4361 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4362 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4363 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4364 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4365 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4366 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4367 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4368 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4369 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4370 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4371 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4372 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4373 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4374 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4375 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4376 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4377 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4378 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4379 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4380 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4381 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4382 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4383 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4384 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4385 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4386 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4387 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4388 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4389 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4390 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4391 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4392 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4393 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4394 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4395 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4396 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4397 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4398 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4399 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4400 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4401 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4402 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4403 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4404 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4405 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4406 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4407 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4408 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4409 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4410 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4411 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4412 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4413 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4414 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4415 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4416 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4417 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4418 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4419 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4420 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4421 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4422 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4423 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4424 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4425 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4426 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4427 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4428 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4429 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4430 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4431 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4432 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4433 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4434 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4435 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4436 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4437 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4438 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4439 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4440 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4441 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4442 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4443 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4444 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4445 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4446 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4447 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4448 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4449 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4450 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4451 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4452 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4453 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4454 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4455 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4456 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4457 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4458 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4459 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4460 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4461 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4462 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4463 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4464 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4465 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4466 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4467 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4468 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4469 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4470 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4471 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4472 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4473 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4474 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4475 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4476 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4477 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4478 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4479 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4480 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4481 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4482 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4483 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4484 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4485 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4486 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4487 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4488 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4489 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4490 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4491 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4492 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4493 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4494 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4495 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4496 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4497 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4498 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4499 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4500 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4501 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4502 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4503 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4504 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4505 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4506 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4507 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4508 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4509 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4510 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4511 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4512 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4513 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4514 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4515 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4516 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4517 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4518 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4519 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4520 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4521 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4522 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4523 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4524 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4525 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4526 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4527 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4528 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4529 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4530 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4531 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4532 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4533 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4534 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4535 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4536 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4537 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4538 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4539 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4540 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4541 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4542 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4543 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4544 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4545 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4546 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4547 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4548 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4549 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4550 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4551 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4552 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4553 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4554 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4555 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4556 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4557 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4558 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4559 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4560 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4561 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4562 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4563 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4564 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4565 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4566 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4567 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4568 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4569 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4570 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4571 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4572 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4573 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4574 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4575 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4576 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4577 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4578 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4579 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4580 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4581 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4582 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4583 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4584 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4585 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4586 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4587 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4588 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4589 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4590 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4591 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4592 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4593 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4594 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4595 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4596 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4597 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4598 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4599 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4600 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4601 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4602 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4603 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4604 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4605 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4606 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4607 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4608 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4609 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4610 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4611 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4612 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4613 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4614 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4615 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4616 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4617 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4618 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4619 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4620 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4621 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4622 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4623 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4624 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4625 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4626 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4627 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4628 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4629 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4630 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4631 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4632 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4633 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4634 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4635 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4636 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4637 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4638 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4639 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4640 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4641 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4642 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4643 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4644 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4645 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4646 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4647 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4648 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4649 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4650 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4651 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4652 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4653 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4654 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4655 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4656 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4657 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4658 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4659 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4660 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4661 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4662 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4663 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4664 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4665 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4666 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4667 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4668 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4669 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4670 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4671 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4672 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4673 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4674 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4675 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4676 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4677 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4678 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4679 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4680 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4681 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4682 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4683 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4684 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4685 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4686 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4687 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4688 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4689 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4690 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4691 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4692 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4693 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4694 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4695 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4696 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4697 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4698 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4699 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4700 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4701 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4702 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4703 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4704 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4705 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4706 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4707 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4708 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4709 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4710 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4711 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4712 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4713 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4714 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4715 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4716 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4717 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4718 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4719 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4720 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4721 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4722 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4723 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4724 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4725 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4726 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4727 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4728 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4729 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4730 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4731 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4732 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4733 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4734 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4735 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4736 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4737 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4738 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4739 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4740 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4741 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4742 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4743 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4744 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4745 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4746 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4747 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4748 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4749 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4750 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4751 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4752 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4753 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4754 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4755 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4756 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4757 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4758 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4759 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4760 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4761 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4762 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4763 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4764 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4765 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4766 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4767 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4768 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4769 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4770 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4771 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4772 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4773 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4774 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4775 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4776 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4777 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4778 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4779 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4780 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4781 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4782 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4783 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4784 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4785 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4786 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4787 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4788 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4789 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4790 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4791 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4792 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4793 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4794 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4795 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4796 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4797 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4798 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4799 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4800 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4801 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4802 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4803 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4804 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4805 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4806 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4807 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4808 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4809 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4810 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4811 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4812 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4813 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4814 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4815 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4816 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4817 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4818 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4819 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4820 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4821 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4822 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4823 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4824 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4825 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4826 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4827 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4828 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4829 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4830 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4831 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4832 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4833 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4834 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4835 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4836 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4837 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4838 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4839 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4840 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4841 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4842 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4843 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4844 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4845 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4846 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4847 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4848 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4849 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4850 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4851 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4852 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4853 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4854 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4855 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4856 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4857 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4858 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4859 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4860 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4861 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4862 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4863 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4864 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4865 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4866 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4867 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4868 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4869 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4870 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4871 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4872 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4873 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4874 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4875 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4876 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4877 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4878 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4879 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4880 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4881 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4882 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4883 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4884 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4885 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4886 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4887 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4888 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4889 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4890 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4891 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4892 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4893 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4894 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4895 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4896 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4897 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4898 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4899 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4900 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4901 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4902 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4903 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4904 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4905 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4906 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4907 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4908 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4909 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4910 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4911 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4912 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4913 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4914 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4915 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4916 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4917 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4918 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4919 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4920 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4921 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4922 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4923 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4924 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4925 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4926 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4927 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4928 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4929 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4930 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4931 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4932 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4933 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4934 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4935 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4936 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4937 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4938 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4939 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4940 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4941 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4942 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4943 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4944 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4945 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4946 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4947 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4948 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4949 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4950 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4951 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4952 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4953 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4954 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4955 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4956 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4957 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4958 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4959 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4960 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4961 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4962 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4963 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4964 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4965 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4966 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4967 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4968 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4969 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4970 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4971 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4972 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4973 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4974 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4975 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4976 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4977 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4978 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4979 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4980 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4981 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4982 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4983 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4984 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4985 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4986 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4987 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4988 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4989 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4990 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4991 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4992 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4993 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4994 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4995 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4996 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4997 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4998 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 4999 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5000 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5001 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5002 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5003 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5004 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5005 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5006 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5007 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5008 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5009 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5010 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5011 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5012 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5013 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5014 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5015 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5016 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5017 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5018 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5019 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5020 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5021 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5022 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5023 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5024 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5025 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5026 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5027 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5028 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5029 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5030 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5031 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5032 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5033 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5034 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5035 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5036 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5037 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5038 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5039 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5040 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5041 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5042 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5043 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5044 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5045 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5046 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5047 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5048 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5049 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5050 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5051 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5052 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5053 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5054 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5055 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5056 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5057 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5058 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5059 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5060 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5061 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5062 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5063 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5064 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5065 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5066 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5067 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5068 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5069 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5070 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5071 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5072 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5073 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5074 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5075 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5076 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5077 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5078 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5079 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5080 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5081 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5082 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5083 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5084 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5085 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5086 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5087 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5088 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5089 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5090 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5091 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5092 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5093 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5094 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5095 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5096 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5097 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5098 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5099 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5100 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5101 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5102 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5103 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5104 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5105 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5106 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5107 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5108 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5109 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5110 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5111 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5112 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5113 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5114 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5115 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5116 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5117 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5118 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5119 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5120 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5121 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5122 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5123 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5124 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5125 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5126 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5127 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5128 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5129 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5130 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5131 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5132 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5133 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5134 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5135 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5136 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5137 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5138 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5139 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5140 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5141 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5142 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5143 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5144 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5145 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5146 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5147 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5148 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5149 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5150 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5151 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5152 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5153 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5154 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5155 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5156 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5157 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5158 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5159 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5160 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5161 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5162 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5163 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5164 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5165 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5166 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5167 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5168 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5169 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5170 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5171 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5172 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5173 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5174 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5175 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5176 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5177 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5178 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5179 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5180 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5181 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5182 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5183 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5184 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5185 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5186 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5187 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5188 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5189 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5190 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5191 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5192 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5193 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5194 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5195 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5196 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5197 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5198 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5199 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5200 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5201 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5202 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5203 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5204 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5205 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5206 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5207 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5208 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5209 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5210 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5211 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5212 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5213 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5214 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5215 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5216 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5217 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5218 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5219 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5220 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5221 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5222 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5223 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5224 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5225 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5226 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5227 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5228 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5229 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5230 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5231 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5232 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5233 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5234 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5235 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5236 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5237 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5238 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5239 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5240 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5241 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5242 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5243 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5244 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5245 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5246 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5247 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5248 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5249 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5250 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5251 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5252 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5253 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5254 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5255 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5256 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5257 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5258 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5259 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5260 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5261 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5262 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5263 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5264 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5265 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5266 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5267 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5268 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5269 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5270 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5271 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5272 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5273 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5274 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5275 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5276 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5277 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5278 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5279 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5280 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5281 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5282 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5283 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5284 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5285 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5286 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5287 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5288 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5289 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5290 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5291 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5292 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5293 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5294 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5295 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5296 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5297 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5298 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5299 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5300 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5301 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5302 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5303 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5304 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5305 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5306 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5307 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5308 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5309 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5310 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5311 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5312 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5313 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5314 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5315 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5316 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5317 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5318 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5319 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5320 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5321 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5322 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5323 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5324 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5325 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5326 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5327 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5328 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5329 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5330 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5331 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5332 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5333 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5334 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5335 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5336 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5337 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5338 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5339 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5340 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5341 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5342 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5343 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5344 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5345 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5346 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5347 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5348 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5349 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5350 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5351 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5352 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5353 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5354 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5355 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5356 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5357 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5358 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5359 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5360 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5361 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5362 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5363 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5364 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5365 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5366 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5367 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5368 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5369 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5370 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5371 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5372 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5373 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5374 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5375 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5376 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5377 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5378 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5379 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5380 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5381 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5382 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5383 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5384 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5385 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5386 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5387 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5388 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5389 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5390 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5391 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5392 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5393 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5394 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5395 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5396 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5397 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5398 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5399 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5400 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5401 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5402 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5403 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5404 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5405 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5406 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5407 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5408 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5409 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5410 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5411 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5412 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5413 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5414 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5415 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5416 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5417 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5418 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5419 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5420 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5421 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5422 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5423 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5424 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5425 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5426 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5427 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5428 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5429 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5430 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5431 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5432 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5433 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5434 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5435 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5436 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5437 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5438 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5439 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5440 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5441 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5442 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5443 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5444 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5445 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5446 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5447 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5448 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5449 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5450 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5451 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5452 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5453 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5454 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5455 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5456 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5457 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5458 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5459 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5460 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5461 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5462 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5463 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5464 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5465 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5466 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5467 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5468 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5469 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5470 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5471 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5472 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5473 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5474 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5475 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5476 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5477 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5478 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5479 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5480 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5481 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5482 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5483 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5484 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5485 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5486 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5487 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5488 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5489 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5490 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5491 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5492 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5493 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5494 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5495 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5496 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5497 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5498 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5499 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5500 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5501 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5502 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5503 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5504 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5505 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5506 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5507 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5508 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5509 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5510 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5511 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5512 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5513 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5514 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5515 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5516 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5517 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5518 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5519 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5520 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5521 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5522 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5523 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5524 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5525 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5526 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5527 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5528 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5529 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5530 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5531 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5532 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5533 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5534 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5535 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5536 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5537 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5538 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5539 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5540 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5541 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5542 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5543 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5544 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5545 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5546 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5547 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5548 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5549 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5550 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5551 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5552 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5553 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5554 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5555 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5556 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5557 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5558 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5559 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5560 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5561 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5562 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5563 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5564 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5565 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5566 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5567 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5568 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5569 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5570 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5571 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5572 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5573 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5574 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5575 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5576 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5577 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5578 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5579 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5580 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5581 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5582 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5583 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5584 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5585 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5586 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5587 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5588 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5589 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5590 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5591 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5592 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5593 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5594 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5595 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5596 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5597 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5598 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5599 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5600 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5601 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5602 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5603 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5604 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5605 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5606 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5607 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5608 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5609 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5610 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5611 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5612 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5613 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5614 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5615 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5616 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5617 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5618 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5619 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5620 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5621 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5622 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5623 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5624 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5625 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5626 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5627 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5628 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5629 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5630 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5631 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5632 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5633 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5634 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5635 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5636 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5637 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5638 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5639 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5640 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5641 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5642 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5643 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5644 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5645 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5646 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5647 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5648 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5649 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5650 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5651 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5652 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5653 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5654 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5655 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5656 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5657 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5658 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5659 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5660 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5661 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5662 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5663 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5664 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5665 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5666 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5667 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5668 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5669 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5670 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5671 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5672 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5673 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5674 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5675 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5676 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5677 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5678 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5679 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5680 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5681 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5682 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5683 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5684 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5685 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5686 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5687 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5688 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5689 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5690 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5691 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5692 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5693 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5694 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5695 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5696 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5697 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5698 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5699 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5700 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5701 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5702 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5703 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5704 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5705 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5706 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5707 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5708 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5709 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5710 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5711 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5712 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5713 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5714 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5715 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5716 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5717 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5718 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5719 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5720 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5721 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5722 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5723 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5724 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5725 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5726 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5727 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5728 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5729 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5730 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5731 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5732 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5733 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5734 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5735 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5736 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5737 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5738 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5739 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5740 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5741 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5742 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5743 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5744 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5745 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5746 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5747 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5748 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5749 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5750 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5751 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5752 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5753 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5754 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5755 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5756 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5757 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5758 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5759 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5760 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5761 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5762 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5763 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5764 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5765 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5766 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5767 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5768 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5769 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5770 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5771 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5772 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5773 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5774 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5775 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5776 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5777 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5778 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5779 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5780 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5781 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5782 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5783 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5784 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5785 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5786 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5787 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5788 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5789 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5790 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5791 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5792 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5793 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5794 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5795 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5796 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5797 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5798 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5799 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5800 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5801 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5802 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5803 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5804 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5805 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5806 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5807 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5808 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5809 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5810 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5811 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5812 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5813 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5814 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5815 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5816 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5817 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5818 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5819 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5820 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5821 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5822 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5823 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5824 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5825 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5826 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5827 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5828 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5829 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5830 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5831 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5832 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5833 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5834 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5835 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5836 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5837 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5838 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5839 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5840 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5841 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5842 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5843 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5844 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5845 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5846 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5847 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 5848 — recover from Googology Wiki article 'ペア数列の停止性'>>>
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
<<<MISSING line 6009 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6010 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6011 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6012 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6013 — recover from Googology Wiki article 'ペア数列の停止性'>>>
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

<<<MISSING line 6134 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6135 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6136 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6137 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6138 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6139 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6140 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6141 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6142 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6143 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6144 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6145 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6146 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6147 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6148 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6149 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6150 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6151 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6152 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6153 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6154 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6155 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6156 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6157 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6158 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6159 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6160 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6161 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6162 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6163 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6164 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6165 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6166 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6167 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6168 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6169 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6170 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6171 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6172 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6173 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6174 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6175 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6176 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6177 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6178 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6179 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6180 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6181 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6182 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6183 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6184 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6185 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6186 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6187 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6188 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6189 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6190 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6191 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6192 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6193 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6194 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6195 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6196 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6197 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6198 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6199 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6200 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6201 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6202 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6203 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6204 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6205 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6206 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6207 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6208 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6209 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6210 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6211 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6212 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6213 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6214 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6215 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6216 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6217 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6218 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6219 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6220 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6221 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6222 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6223 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6224 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6225 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6226 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6227 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6228 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6229 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6230 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6231 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6232 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6233 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6234 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6235 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6236 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6237 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6238 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6239 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6240 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6241 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6242 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6243 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6244 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6245 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6246 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6247 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6248 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6249 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6250 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6251 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6252 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6253 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6254 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6255 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6256 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6257 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6258 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6259 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6260 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6261 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6262 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6263 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6264 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6265 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6266 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6267 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6268 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6269 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6270 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6271 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6272 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6273 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6274 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6275 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6276 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6277 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6278 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6279 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6280 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6281 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6282 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6283 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6284 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6285 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6286 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6287 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6288 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6289 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6290 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6291 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6292 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6293 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6294 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6295 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6296 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6297 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6298 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6299 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6300 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6301 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6302 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6303 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6304 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6305 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6306 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6307 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6308 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6309 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6310 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6311 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6312 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6313 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6314 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6315 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6316 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6317 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6318 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6319 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6320 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6321 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6322 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6323 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6324 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6325 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6326 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6327 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6328 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6329 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6330 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6331 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6332 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6333 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6334 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6335 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6336 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6337 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6338 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6339 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6340 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6341 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6342 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6343 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6344 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6345 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6346 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6347 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6348 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6349 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6350 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6351 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6352 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6353 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6354 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6355 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6356 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6357 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6358 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6359 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6360 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6361 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6362 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6363 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6364 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6365 — recover from Googology Wiki article 'ペア数列の停止性'>>>
<<<MISSING line 6366 — recover from Googology Wiki article 'ペア数列の停止性'>>>
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


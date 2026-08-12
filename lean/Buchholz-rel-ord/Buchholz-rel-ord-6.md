[← Back](README.md)

# Buchholz [Buc2] p.6 Definition 6 — 基本列の塔

出典：W. Buchholz, *Relating ordinals to proofs in a prespicious way*,
unpublished article, p.6, Definition 6.

原稿そのものは現存資料から確認できないため、ここでは引用文に記録された規則を
採用する。Buchholz (1986) の \(([\ ].4)(ii)\) を次の規則で置き換える。

## 定義

\(\operatorname{dom}(b)=T_u\) かつ \(v\leq u\) とする。補助列
\((x_i)_{i\in\mathbb N}\) を

\[
x_0=D_u0,\qquad
x_{i+1}=D_u\bigl(b[x_i]\bigr)
\]

で定め、

\[
(D_vb)[n]=D_v\bigl(b[x_n]\bigr)
\]

とする。

ここで括弧は重要である。再帰段階は

\[
D_u\bigl(b[x_i]\bigr)
\]

であって \(b[D_ux_i]\) ではない。後者を用いると \(b[\cdot]\) の適用位置が
一段ずれ、基本列の降下性が壊れる。

## 再帰の正当性

基本列 \(a[z]\) と補助列 \(x_i\) を同時に定める。項の構造的大きさを
\(|a|\) とし、呼出し状態に三成分の測度

\[
\mu=(\text{項の大きさ},\ \text{状態種別},\ \text{反復回数})
\]

を辞書式順序で割り当てる。

通常の基本列から部分項の基本列へ進むと第一成分が減少する。
\(x_{i+1}\) を計算するとき、同じ \(b\) に対する基本列計算へ移る箇所では
第二成分が減少し、\(x_i\) を求める再帰では第三成分が減少する。
したがって全ての再帰呼出しで \(\mu\) が狭義に減少し、定義は一意に定まる。

その他の分岐は Buchholz (1986) の \(([\ ].0)\)–\(([\ ].5)\) に従う。

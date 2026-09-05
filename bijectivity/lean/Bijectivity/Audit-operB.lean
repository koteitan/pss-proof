import Bijectivity.Cited
import «Buchholz-1986».«Buchholz-1986-3.3»

/-!
# 監査 — 基本列の共終性（`o_iSup_operB` の経験的検証）

`Cited.lean` の `FseqCofinal`（[Buc2] Theorem 1.4(a)）の**独立な数値検証**。
この主張自体は `OTB-well-founded-syntactic-cofinality.lean` の `y4_bachmann` で
**証明済み**（仮定ゼロ・`sorry` ゼロ）なので、本ファイルは公理の裏付けではなく
**独立二重チェック**として残す。その主張は

\[
t\in OT_{\textrm{B}},\ \textrm{dom}(t)=\omega,\ u\in OT_{\textrm{B}},\ u<_{\textrm{B}}t
\;\Longrightarrow\; \exists m,\ u\leq_{\textrm{B}}t[m]
\]

＝「基本列 \(t[0],t[1],\dots\) が \(\{u\in OT_{\textrm{B}}\mid u<_{\textrm{B}}t\}\)
で共終」であり、**順序数を含まない純粋に構文的な主張**なので、下の `coversBelow` は
`FseqCofinal` の内側をそのまま `pool` に制限したものになっている。
（原文の \(\sup_m o(t[m])=o(t)\) はここから `17-fseq-convergence` の
`o_iSup_operB` として導かれる。）

しかも本リポジトリの `operB` は [Buc2] の定義そのものではなく、**訂正 A23** を
当てた形（`x₀ = D_u0`、`x_{i+1} = D_u(b[x_i])`、`(D_vb)[n] = D_v(b[x_n])`,
`Buchholz-rel-ord-6.lean` 参照）である。したがって共終性は「引用すれば済む」
ものではなく、**この定義に対して**確かめる価値がある。

本ファイルは小さな \(OT_{\textrm{B}}\) 項のプールを全数列挙し、
\(\textrm{dom}(t)=\omega\) なる各 \(t\) について上の主張を \(m\leq B\) の範囲で
`#guard` で検査する。反例が出ればビルドが落ちる。

## 結果

| 指標の範囲 | \(t\) の深さ | プール | \(\textrm{dom}=\omega\) の項 | 反例 |
|---|---|---|---|---|
| \(\{0,1\}\) | 2 | 91 | 64 | **0** |
| \(\{0,1,2\}\) | 2 | 496 | 361 | **0** |
| \(\{0,1,2,3\}\) | 2 | 1891 | 1355 | **0** |
| \(\{0,1,2\}\) | 3（非対称版） | 496 | 1071 | **0** |
| \(\{0,1,2,3,4\}\) | 2 | 5671 | 3964 | **0**（ビルド時間の都合で `#guard` にはしていない） |

非対称版は \(t\) を 1 段深くして（深さ 3 の単項）、比較相手 \(u\) は深さ 2 の
プールのままにしたもの。`operB` の A23 分岐（`xseq` の塔）は
\(t=D_v(D_w\cdots)\) で \(v\leq w-1\) のときに走るので、深さ 2 で既に踏んでいるが、
入れ子の塔も見ておくためのもの。

（`t[m] <_B t` と `t[m] <_B t[m+1]` のほうは経験検証ではなく定理である:
`buchholz_fseq_lt`（[Buc1] Lemma 3.2(a)）と `operB_numBT_step`（`16c-operB-mono`）。）

[Buc1] の加法標準形のうち原文が使う分は `Cited.lean` の `o_addBT_DzeroZero`
として証明済みである。本ファイルの検証は `y4_bachmann` の結論と `operB` の実装が
食い違っていないことの独立チェックにあたる。
-/

namespace Bijectivity

open PSS

/-- 各段で \(OT_{\textrm{B}}\) に落としながら深さを増やす、小さな
\(OT_{\textrm{B}}\) 項のプール（principal リスト長 ≤ 2）。 -/
def otbGrow (idx : List ℕ∞) : ℕ → List BT
  | 0 => [BZero]
  | d + 1 =>
      let sub := otbGrow idx d
      let ps : List BP := idx.flatMap (fun v => sub.map (fun b => BP.db v b))
      let ts : List BT :=
        BZero ::
          (ps.map (fun p => BT.trm [p]) ++ ps.flatMap (fun p => ps.map (fun q => BT.trm [p, q])))
      (ts.filter (fun t => isOT_BT t && dfree_BT t)).eraseDups

/-- `pool` の中で `t` 未満の元が、`t[0..B]` のどれかで覆えるか。 -/
def coversBelow (pool : List BT) (B : ℕ) (t : BT) : Bool :=
  let fs := (List.range (B + 1)).map (fun m => operB t (numBT m))
  (pool.filter (fun u => lessBT u t)).all (fun u => fs.any (fun f => leBT u f))

/-- `(プールの大きさ, dom = ω の項の数, 反例の数)`。 -/
def cofAudit (idx : List ℕ∞) (d B : ℕ) : ℕ × ℕ × ℕ :=
  let pool := otbGrow idx d
  let ts := pool.filter (fun t => domTag t == BDom.naturals)
  (pool.length, ts.length, (ts.filter (fun t => !coversBelow pool B t)).length)

/-- 深い `t` を浅いプールで検査する非対称版（`t` は深さ 3 の単項）。 -/
def cofAuditDeep (idx : List ℕ∞) (d B : ℕ) : ℕ × ℕ × ℕ :=
  let uPool := otbGrow idx d
  let ps : List BP := idx.flatMap (fun v => uPool.map (fun b => BP.db v b))
  let tPool := ((ps.map (fun p => BT.trm [p])).filter (fun t => isOT_BT t && dfree_BT t)).eraseDups
  let ts := tPool.filter (fun t => domTag t == BDom.naturals)
  (uPool.length, ts.length, (ts.filter (fun t => !coversBelow uPool B t)).length)

#guard cofAudit [0, 1] 2 6 == (91, 64, 0)
#guard cofAudit [0, 1, 2] 2 6 == (496, 361, 0)
#guard cofAudit [0, 1, 2, 3] 2 8 == (1891, 1355, 0)
#guard cofAuditDeep [0, 1, 2] 2 8 == (496, 1071, 0)

end Bijectivity

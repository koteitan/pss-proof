import Bijectivity.Cited
import «Buchholz-1986».«Buchholz-1986-3.3»

/-!
# 監査 — 基本列の共終性（`o_iSup_operB` の経験的検証）

`Cited.lean` に残る 2 本の実質的な外部引用のうち、**深いほうは
`o_iSup_operB`**（[Buc2] Theorem 1.4(a)）である。これは

\[
\textrm{dom}(t)=\omega \;\Longrightarrow\; \sup_m o(t[m])=o(t)
\]

すなわち「基本列 \(t[0],t[1],\dots\) が \(t\) 未満で共終」という主張で、`o` を
\((OT_{\textrm{B}\omega},<_{\textrm{B}})\) の順序同型として取る模型では
**この主張が成り立つかどうかがそのまま公理系の無矛盾性を左右する**。

しかも本リポジトリの `operB` は [Buc2] の定義そのものではなく、**訂正 A23** を
当てた形（`x₀ = D_u0`、`x_{i+1} = D_u(b[x_i])`、`(D_vb)[n] = D_v(b[x_n])`,
`Buchholz-rel-ord-6.lean` 参照）である。したがって共終性は「引用すれば済む」
ものではなく、**この定義に対して**確かめる価値がある。

本ファイルは小さな \(OT_{\textrm{B}}\) 項のプールを全数列挙し、
\(\textrm{dom}(t)=\omega\) なる各 \(t\) について

* プール内の \(u<_{\textrm{B}}t\) すべてに対して \(u\leq_{\textrm{B}}t[m]\) となる
  \(m\leq B\) が存在する

ことを `#guard` で検査する。反例が出ればビルドが落ちる。

## 結果

| 指標の範囲 | 深さ | プール | \(\textrm{dom}=\omega\) の項 | 反例 |
|---|---|---|---|---|
| \(\{0,1\}\) | 2 | 91 | 64 | **0** |
| \(\{0,1,2\}\) | 2 | 496 | 361 | **0** |

（`t[m] <_B t` と `t[m] <_B t[m+1]` のほうは経験検証ではなく定理である:
`buchholz_fseq_lt`（[Buc1] Lemma 3.2(a)）と `operB_numBT_step`（`16c-operB-mono`）。）

もう 1 本の `o_addBT` は [Buc1] の加法標準形＝Cantor 標準形の加法性で、
`addBT` が principal リストの連結であることから直接従う性質なので、ここでは
経験検証していない。
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

#guard cofAudit [0, 1] 2 6 == (91, 64, 0)
#guard cofAudit [0, 1, 2] 2 6 == (496, 361, 0)

end Bijectivity

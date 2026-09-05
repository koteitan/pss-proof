import Bijectivity.Defs

/-!
# 命題（基本列の切片の不変性）

原文: 任意の \(M\in T_{\textrm{PS}}\) と \(j_0,j_1\in\mathbb{N}\) と
\(m,n\in\mathbb{N}_+\) に対して、\(j_0\leq j_1\) かつ
\(j_1<\textrm{Lng}(M[m])\) かつ \(j_1<\textrm{Lng}(M[n])\) ならば
\((M[m]_j)_{j=j_0}^{j_1}=(M[n]_j)_{j=j_0}^{j_1}\) である。

原文の証明（要旨）:
> \(m<n\) としてよい。\(M[n]\) の先頭 \(\textrm{Lng}(M[m])\) 項は
> \(G\oplus\left(\bigoplus(B_k)_{k=0}^{m-1}\right)=M[m]\) に一致する。
> よって \(j_0\leq j_1<\textrm{Lng}(M[m])\) より従う。□

UNPROVEN STUB — `oper` のブロック分解 \(G\oplus\bigoplus B\) に対する補題を要する。
-/

namespace Bijectivity

open PSS

/-- 原文の命題（基本列の切片の不変性）。 -/
theorem oper_seg_invariance {M : PS} {j0 j1 m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hj : j0 ≤ j1)
    (h1 : j1 < Lng (oper M m)) (h2 : j1 < Lng (oper M n)) :
    seg (oper M m) j0 j1 = seg (oper M n) j0 j1 := by
  sorry

end Bijectivity

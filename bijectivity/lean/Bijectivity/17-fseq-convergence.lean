import Bijectivity.«16-fseq-relation»

/-!
# 命題（基本列の収束性）

原文: 任意の \(M\in ST_{\textrm{PS}}\) に対して、
\(\textrm{dom}(\textrm{Trans}(M))=\omega\) ならば
\(\sup_{n\in\mathbb{N}_+}o(\textrm{Trans}(M[n]))=o(\textrm{Trans}(M))\) である。

原文の証明:
> 基本列の関係、[1] の基本列の降下性、[5] の Theorem 1.4(a) 及び Lemma 1.6 より
> \(\{o(\textrm{Trans}(M[n]))\mid n\in\mathbb{N}_+\}\) は \(o(\textrm{Trans}(M))\) の
> 非有界な部分集合であることから即座に従う。□

**順序数を用いる言明**（評価写像 \(o\) は `Bijectivity.Cited` の外部引用）。
UNPROVEN STUB。
-/

namespace Bijectivity

open PSS

/-- 原文の命題（基本列の収束性）。 -/
theorem fseq_convergence {M : PS} (hM : STPS M) (hdom : domIsOmega (PSS.Trans M)) :
    ⨆ n : {n : ℕ // 1 ≤ n}, o (PSS.Trans (oper M n.1)) = o (PSS.Trans M) := by
  sorry

end Bijectivity

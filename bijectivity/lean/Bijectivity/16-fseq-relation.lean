import Bijectivity.Cited
import PSS.Trans
import «Buchholz-rel-ord».«Buchholz-rel-ord-6»

/-!
# 補題（基本列の関係）

原文: 任意の \(M\in ST_{\textrm{PS}}\) と \(m\in\mathbb{N}\) に対して、
\(\textrm{dom}(\textrm{Trans}(M))=\omega\) ならばある \(n\in\mathbb{N}_+\) が存在して
\(\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])\) である。

原文の注記: 「幸いにも、基本列の関係 の証明に見られるようにすでに必要なものは揃っている」
（[1] の議論を流用できる）。

UNPROVEN STUB — 原文の全射性の核。
-/

namespace Bijectivity

open PSS

/-- 原文の補題（基本列の関係）。 -/
theorem fseq_relation {M : PS} (hM : STPS M) (m : ℕ)
    (hdom : domIsOmega (PSS.Trans M)) :
    ∃ n : ℕ, 1 ≤ n ∧ leBT (operB (PSS.Trans M) (numBT m)) (PSS.Trans (oper M n)) = true := by
  sorry

end Bijectivity

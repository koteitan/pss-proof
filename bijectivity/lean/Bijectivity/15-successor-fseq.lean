import Bijectivity.Cited
import PSS.Trans
import PSS.Red

/-!
# 命題（後続な項の基本列）

原文: 任意の \(M\in RT_{\textrm{PS}}\) と \(n\in\mathbb{N}_+\) に対して、
\(\textrm{dom}(\textrm{Trans}(M))=1\) ならば
\((\textrm{Trans}(M),\textrm{Trans}(M[n]))=(D_00,0)\) または
\(\textrm{Trans}(M[n])+D_00=\textrm{Trans}(M)\) である。

原文の証明（要旨）: \(\textrm{dom}\) の定義より \(\textrm{Trans}(M)=D_00\) か、
ある \(s\) で \(\underline{(}s\underline{,}D_00\underline{)}\) の形。前者では [1] の
\(\textrm{Trans}\) と非可算基数の関係より \(M=((0,0),(0,0))\)。後者では \(M\) は複項で、
\(P(M)_{J_1}=((0,0))\)、[1] の \(P\) の加法性より
\(M=\textrm{Pred}(M)\oplus_{\mathbb{N}^2}((0,0))\)、よって
\(\textrm{Trans}(M)=\textrm{Trans}(\textrm{Pred}(M))+D_00=\textrm{Trans}(M[n])+D_00\)。□

UNPROVEN STUB。
-/

namespace Bijectivity

open PSS

/-- \(D_00\)。 -/
def DzeroZero : BT := Dprin 0 (BT.trm [])

/-- 原文の命題（後続な項の基本列）。 -/
theorem successor_fseq {M : PS} (hM : RTPS M) {n : ℕ} (hn : 1 ≤ n)
    (hdom : domIsOne (PSS.Trans M)) :
    (PSS.Trans M = DzeroZero ∧ PSS.Trans (oper M n) = BT.trm []) ∨
      addBT (PSS.Trans (oper M n)) DzeroZero = PSS.Trans M := by
  sorry

end Bijectivity

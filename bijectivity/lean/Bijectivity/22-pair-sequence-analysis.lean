import Bijectivity.«21-ordinal-bijectivity»

/-!
# 系（ペア数列の解析）

原文:
(1) 任意の \(M\in CT_{\textrm{PS}}\) に対して、\(o\circ\textrm{Trans}\) は同型写像
\((\{N\mid N\in CT_{\textrm{PS}}\land N<_{\textrm{PS}}M\},<_{\textrm{PS}})
\to(\{\alpha\mid\alpha\in o(\textrm{Trans}(M))\},\in)\) である。
(2) 任意の \(M\in CT_{\textrm{PS}}\) に対して、\(\textrm{Trans}\) は同型写像
\((\{N\mid N\in CT_{\textrm{PS}}\land N<_{\textrm{PS}}M\},<_{\textrm{PS}})
\to(\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}\textrm{Trans}(M)\},<_{\textrm{B}})\)
である。

原文の証明:
> (1) \(\textrm{Trans}\) が順序を保つこと 及び 変換写像の順序数への全単射性 より即座に従う。
> (2) 対応する項の上界 (1)(2)、対応する項の上界未満の字母、[4] Lemma 2.2(c) 及び 2.3(b) より
> \(o\) は \(\{t\mid t<_{\textrm{B}}D_0D_\omega0\}\to\psi_0\psi_\omega0\) の同型写像。
> \(\textrm{Trans}=o^{-1}\circ o\circ\textrm{Trans}\) であるから (1) より従う。□

UNPROVEN STUB。
-/

namespace Bijectivity

open PSS

/-- 原文の系（ペア数列の解析）(1)。 -/
theorem analysis_ordinal {M : PS} (hM : CTPS M) :
    Set.BijOn (fun N => o (PSS.Trans N)) {N : PS | CTPS N ∧ N <ₚ M}
      {α : Ordinal | α < o (PSS.Trans M)} := by
  sorry

/-- 原文の系（ペア数列の解析）(2)。 -/
theorem analysis_term {M : PS} (hM : CTPS M) :
    Set.BijOn PSS.Trans {N : PS | CTPS N ∧ N <ₚ M}
      {t : BT | t ∈ OT ∧ lessBT t (PSS.Trans M) = true} := by
  sorry

end Bijectivity

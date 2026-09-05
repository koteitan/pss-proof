import Bijectivity.«17-fseq-convergence»
import Bijectivity.«18-trans-preserves-order»
import Bijectivity.«20-term-upper-bound»

/-!
# 命題（変換写像の順序数への全単射性）

原文: \(o\circ\textrm{Trans}\) は \(CT_{\textrm{PS}}\to\psi_0\psi_\omega0\) 上で
全域かつ全単射である。

原文の証明（要旨）:
> 対応する項の上界未満の字母、対応する項の上界 (1)(2) 及び [1] の \(\textrm{Trans}\) が
> 標準形を保つことより \(\{\textrm{Trans}(M)\}\) は
> \(\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}\) の
> \(<_{\textrm{B}}\) に対して非有界な部分集合。[4] Lemma 2.2(c) より
> \(\{o(\textrm{Trans}(M))\}\) は \(\psi_0\psi_\omega0\) の非有界な部分集合。
> [4] Lemma 2.3(b) 及び [5] Lemma 1.6 より \(\textrm{dom}(t)=\textrm{cof}(o(t))\)。
> 後続な項の基本列 より \(\textrm{cof}=1\) の場合、基本列の収束性 より
> \(\textrm{cof}=\omega\) の場合が押さえられ、[3] の命題 11 より全射。
> \(\textrm{Trans}\) が順序を保つこと、[4] Lemma 2.1 及び 2.2(c) より単射。□

**順序数を用いる言明**。UNPROVEN STUB。
-/

namespace Bijectivity

open PSS

/-- 原文の命題（変換写像の順序数への全単射性）。 -/
theorem oTrans_bijOn :
    Set.BijOn (fun M => o (PSS.Trans M)) {M : PS | CTPS M} {α : Ordinal | α < psi0psiOmega0} := by
  sorry

end Bijectivity

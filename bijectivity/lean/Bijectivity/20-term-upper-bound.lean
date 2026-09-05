import Bijectivity.«19-alphabet-below-bound»
import Bijectivity.«10-countable-standard-origin»
import PSS.Trans

/-!
# 命題（対応する項の上界）

原文:
(1) 任意の \(M\in CT_{\textrm{PS}}\) に対して \(\textrm{Trans}(M)<_{\textrm{B}}D_0D_\omega0\)。
(2) 任意の \(t\in T_{\textrm{B}}\) に対して、\(t<_{\textrm{B}}D_0D_\omega0\) ならば
ある \(M\in CT_{\textrm{PS}}\) が存在して \(t<_{\textrm{B}}\textrm{Trans}(M)\)。

原文の証明 (1):
> 可算な標準形の起源 より \(M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v\) なる \(v\) が取れ、
> 辞書式的順序が基本列的順序を含意すること より \(M\leq_{\textrm{PS}}((j,j))_{j=0}^v\)。
> [1] の公差 \((1,1)\) のペア数列の \(\textrm{Trans}\) の基本性質より
> \(\textrm{Trans}(((j,j))_{j=0}^v)=D_0D_v0<_{\textrm{B}}D_0D_\omega0\)。

UNPROVEN STUB。
-/

namespace Bijectivity

open PSS

/-- 原文の命題（対応する項の上界）(1)。 -/
theorem trans_lt_bound {M : PS} (hM : CTPS M) :
    lessBT (PSS.Trans M) DzeroDomegaZero = true := by
  sorry

/-- 原文の命題（対応する項の上界）(2)。 -/
theorem exists_trans_gt {t : BT} (ht : t ∈ T_B) (h : lessBT t DzeroDomegaZero = true) :
    ∃ M : PS, CTPS M ∧ lessBT t (PSS.Trans M) = true := by
  sorry

end Bijectivity

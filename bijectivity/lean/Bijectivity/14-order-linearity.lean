import Bijectivity.«13-order-equivalence»

/-!
# 系（順序の線形性）

原文: \(\leq_{\textrm{PS}}\) 及び \(\leq_{\textrm{PS}[]}\) は
\(CT_{\textrm{PS}}\) 上で全順序である。

原文の証明:
> 辞書式的順序の線形性 及び 順序の等価性 より即座に従う。□
-/

namespace Bijectivity

open PSS

/-- \(\leq_{\textrm{PS}}\) が \(CT_{\textrm{PS}}\) 上で全順序であること。 -/
theorem lePS_total_ctps {M N : PS} (hM : CTPS M) (hN : CTPS N) :
    M ≤ₚ N ∨ N ≤ₚ M := lePS_total M N

/-- \(\leq_{\textrm{PS}[]}\) が \(CT_{\textrm{PS}}\) 上で全順序であること。 -/
theorem leExpPS_total_ctps {M N : PS} (hM : CTPS M) (hN : CTPS N) :
    M ≤ₚ[] N ∨ N ≤ₚ[] M := by
  rcases lePS_total M N with h | h
  · exact Or.inl ((lePS_iff_leExpPS hM hN).mp h)
  · exact Or.inr ((lePS_iff_leExpPS hN hM).mp h)

end Bijectivity

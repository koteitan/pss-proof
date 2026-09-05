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

/-! ## \(\leq_{\textrm{PS}}\) が \(CT_{\textrm{PS}}\) 上で全順序であること

全順序は反射性・反対称性・推移性・全律の 4 つ。`≤ₚ` については `02-lex-linear` が
\(T_{\textrm{PS}}\) 全体で与えているので、そのまま制限すればよい。 -/

theorem lePS_refl_ctps {M : PS} (_hM : CTPS M) : M ≤ₚ M := lePS_refl M

theorem lePS_antisymm_ctps {M N : PS} (_hM : CTPS M) (_hN : CTPS N)
    (h1 : M ≤ₚ N) (h2 : N ≤ₚ M) : M = N := lePS_antisymm h1 h2

theorem lePS_trans_ctps {M N O : PS} (_hM : CTPS M) (_hN : CTPS N) (_hO : CTPS O)
    (h1 : M ≤ₚ N) (h2 : N ≤ₚ O) : M ≤ₚ O := lePS_trans h1 h2

theorem lePS_total_ctps {M N : PS} (_hM : CTPS M) (_hN : CTPS N) :
    M ≤ₚ N ∨ N ≤ₚ M := lePS_total M N

/-! ## \(\leq_{\textrm{PS}[]}\) が \(CT_{\textrm{PS}}\) 上で全順序であること

推移性は 命題（基本列的順序が推移性）＝`leExpPS_trans`（`03`）。反対称性は
系（順序の等価性）で `≤ₚ` に移してから `lePS_antisymm` を使う。 -/

theorem leExpPS_refl (M : PS) : M ≤ₚ[] M := ⟨[], by simp, rfl⟩

theorem leExpPS_antisymm_ctps {M N : PS} (hM : CTPS M) (hN : CTPS N)
    (h1 : M ≤ₚ[] N) (h2 : N ≤ₚ[] M) : M = N :=
  lePS_antisymm ((lePS_iff_leExpPS hM hN).mpr h1) ((lePS_iff_leExpPS hN hM).mpr h2)

theorem leExpPS_trans_ctps {M N O : PS} (_hM : CTPS M) (_hN : CTPS N) (_hO : CTPS O)
    (h1 : M ≤ₚ[] N) (h2 : N ≤ₚ[] O) : M ≤ₚ[] O := leExpPS_trans h1 h2

theorem leExpPS_total_ctps {M N : PS} (hM : CTPS M) (hN : CTPS N) :
    M ≤ₚ[] N ∨ N ≤ₚ[] M := by
  rcases lePS_total M N with h | h
  · exact Or.inl ((lePS_iff_leExpPS hM hN).mp h)
  · exact Or.inr ((lePS_iff_leExpPS hN hM).mp h)

end Bijectivity

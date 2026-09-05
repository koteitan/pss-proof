import Bijectivity.«05-exp-implies-lex»
import Bijectivity.«12-lex-implies-exp»

/-!
# 系（順序の等価性）

原文: 任意の \(M,N\in CT_{\textrm{PS}}\) に対して、\(M\leq_{\textrm{PS}}N\) は
\(M\leq_{\textrm{PS}[]}N\) と同値である。

原文の証明:
> 基本列的順序が辞書式的順序を含意すること 及び
> 辞書式的順序が基本列的順序を含意すること より即座に従う。□

なお原文が引く「辞書式的順序が基本列的順序を含意すること」は逐語形では偽なので
（`05-exp-implies-lex.lean` の訂正候補を参照）、ここではその訂正形を用い、
\(\textrm{Lng}(N)\leq1\) の場合は展開が自明であることから直接処理する。
-/

namespace Bijectivity

open PSS

/-- 原文の系（順序の等価性）。 -/
theorem lePS_iff_leExpPS {M N : PS} (hM : CTPS M) (hN : CTPS N) :
    M ≤ₚ N ↔ M ≤ₚ[] N := by
  constructor
  · rintro (rfl | h)
    · exact ⟨[], by simp, rfl⟩
    · obtain ⟨a, _, ha, he⟩ := ltPS_ltExpPS hM hN h
      exact ⟨a, ha, he⟩
  · rintro ⟨a, ha, he⟩
    cases a with
    | nil => exact Or.inl (by simpa [expand] using he)
    | cons n a =>
        rcases Nat.lt_or_ge 1 (Lng N) with hN1 | hN1
        · exact Or.inr (ltExpPS_ltPS_of_lng hN1 ⟨n :: a, by simp, ha, he⟩)
        · exact Or.inl (by rw [he, expand_of_lng_le_one _ hN1])

end Bijectivity

import Bijectivity.Defs

/-!
# 系（辞書式的順序が辞書式順序であること）

原文: \(<_{\textrm{lex}}\) を数列に対する辞書式順序としたとき、任意の
\(M,N\in T_{\textrm{PS}}\) に対して、\(M<_{\textrm{PS}}N\) は
\(\bigoplus_\mathbb{N}M<_{\textrm{lex}}\bigoplus_\mathbb{N}N\) と同値である。

原文の証明:
> \(<_{\textrm{PS}}\) の定義から即座に従う。□
-/

namespace Bijectivity

open PSS

/-- \(\bigoplus_\mathbb{N}M\): ペア数列を \(\mathbb{N}\) 列へ平坦化する。 -/
def flatten : PS → List ℕ
  | [] => []
  | p :: M => p.1 :: p.2 :: flatten M

/-- 数列に対する辞書式順序 \(<_{\textrm{lex}}\)。 -/
def ltLex : List ℕ → List ℕ → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a :: x, b :: y => a < b ∨ (a = b ∧ ltLex x y)

/-- 原文の系（辞書式的順序が辞書式順序であること）。 -/
theorem ltPS_iff_ltLex (M N : PS) : M <ₚ N ↔ ltLex (flatten M) (flatten N) := by
  induction M generalizing N with
  | nil => cases N <;> simp [ltPS, flatten, ltLex]
  | cons p M ih =>
      cases N with
      | nil => simp [ltPS, flatten, ltLex]
      | cons q N =>
          simp only [ltPS, flatten, ltLex, ih]
          constructor
          · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
            · exact Or.inl h
            · exact Or.inr ⟨h1, Or.inl h2⟩
            · exact Or.inr ⟨h1, Or.inr ⟨h2, h3⟩⟩
          · rintro (h | ⟨h1, h2 | ⟨h2, h3⟩⟩)
            · exact Or.inl h
            · exact Or.inr (Or.inl ⟨h1, h2⟩)
            · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)

end Bijectivity

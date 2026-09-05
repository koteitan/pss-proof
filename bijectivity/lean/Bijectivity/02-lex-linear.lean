import Bijectivity.«01-lex-is-lexicographic»

/-!
# 系（辞書式的順序の線形性）

原文: \(<_{\textrm{PS}}\) は狭義全順序、\(\leq_{\textrm{PS}}\) は全順序である。

原文の証明:
> 辞書式的順序が辞書式順序であること より即座に従う。□
-/

namespace Bijectivity

open PSS

theorem ltLex_irrefl : ∀ x : List ℕ, ¬ ltLex x x
  | [] => by simp [ltLex]
  | a :: x => by
      simp only [ltLex, not_or, not_and]
      exact ⟨lt_irrefl a, fun _ => ltLex_irrefl x⟩

theorem ltLex_trans : ∀ {x y z : List ℕ}, ltLex x y → ltLex y z → ltLex x z
  | [], [], _, h, _ => absurd h (by simp [ltLex])
  | [], _ :: _, [], _, h => absurd h (by simp [ltLex])
  | [], _ :: _, _ :: _, _, _ => by simp [ltLex]
  | _ :: _, [], _, h, _ => absurd h (by simp [ltLex])
  | _ :: _, _ :: _, [], _, h => absurd h (by simp [ltLex])
  | a :: x, b :: y, c :: z, hxy, hyz => by
      simp only [ltLex] at hxy hyz ⊢
      rcases hxy with h1 | ⟨e1, t1⟩
      · rcases hyz with h2 | ⟨e2, _⟩
        · exact Or.inl (lt_trans h1 h2)
        · exact Or.inl (e2 ▸ h1)
      · rcases hyz with h2 | ⟨e2, t2⟩
        · exact Or.inl (e1 ▸ h2)
        · exact Or.inr ⟨e1.trans e2, ltLex_trans t1 t2⟩

theorem ltLex_trichotomy : ∀ x y : List ℕ, ltLex x y ∨ x = y ∨ ltLex y x
  | [], [] => Or.inr (Or.inl rfl)
  | [], _ :: _ => Or.inl (by simp [ltLex])
  | _ :: _, [] => Or.inr (Or.inr (by simp [ltLex]))
  | a :: x, b :: y => by
      rcases lt_trichotomy a b with h | h | h
      · exact Or.inl (by simp [ltLex, h])
      · subst h
        rcases ltLex_trichotomy x y with h2 | h2 | h2
        · exact Or.inl (by simp [ltLex, h2])
        · exact Or.inr (Or.inl (by simp [h2]))
        · exact Or.inr (Or.inr (by simp [ltLex, h2]))
      · exact Or.inr (Or.inr (by simp [ltLex, h]))

/-- 原文の系（辞書式的順序の線形性）: 非反射性。 -/
theorem ltPS_irrefl (M : PS) : ¬ M <ₚ M := by
  rw [ltPS_iff_ltLex]; exact ltLex_irrefl _

/-- 原文の系（辞書式的順序の線形性）: 推移性。 -/
theorem ltPS_trans {M N O : PS} (h1 : M <ₚ N) (h2 : N <ₚ O) : M <ₚ O := by
  rw [ltPS_iff_ltLex] at h1 h2 ⊢; exact ltLex_trans h1 h2

/-- 平坦化は単射である（三分律の等号の場合に使う）。 -/
theorem flatten_inj : ∀ {M N : PS}, flatten M = flatten N → M = N
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [flatten] at h
  | _ :: _, [], h => by simp [flatten] at h
  | p :: M, q :: N, h => by
      simp only [flatten, List.cons.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hM : M = N := flatten_inj h3
      have hp : p = q := Prod.ext h1 h2
      simp [hp, hM]

/-- 原文の系（辞書式的順序の線形性）: 三分律。 -/
theorem ltPS_trichotomy (M N : PS) : M <ₚ N ∨ M = N ∨ N <ₚ M := by
  rcases ltLex_trichotomy (flatten M) (flatten N) with h | h | h
  · exact Or.inl ((ltPS_iff_ltLex M N).mpr h)
  · exact Or.inr (Or.inl (flatten_inj h))
  · exact Or.inr (Or.inr ((ltPS_iff_ltLex N M).mpr h))

/-- 原文の系（辞書式的順序の線形性）: \(\leq_{\textrm{PS}}\) の全律。 -/
theorem lePS_total (M N : PS) : M ≤ₚ N ∨ N ≤ₚ M := by
  rcases ltPS_trichotomy M N with h | h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- 原文の系（辞書式的順序の線形性）: \(\leq_{\textrm{PS}}\) の反射性。 -/
theorem lePS_refl (M : PS) : M ≤ₚ M := Or.inl rfl

/-- 原文の系（辞書式的順序の線形性）: \(\leq_{\textrm{PS}}\) の推移性。 -/
theorem lePS_trans {M N O : PS} (h1 : M ≤ₚ N) (h2 : N ≤ₚ O) : M ≤ₚ O := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  exact Or.inr (ltPS_trans h1 h2)

/-- 原文の系（辞書式的順序の線形性）: \(\leq_{\textrm{PS}}\) の反対称性。 -/
theorem lePS_antisymm {M N : PS} (h1 : M ≤ₚ N) (h2 : N ≤ₚ M) : M = N := by
  rcases h1 with rfl | h1
  · rfl
  rcases h2 with rfl | h2
  · rfl
  exact absurd (ltPS_trans h1 h2) (ltPS_irrefl M)

end Bijectivity

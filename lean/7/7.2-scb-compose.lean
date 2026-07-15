import PSS.Scb

/-!
# §7.2 命題（scb 分解の合成則）

- Isabelle: `m_7_2_scb_compose`, `scbcomp_compose2_PT`
- 訂正: A11（第 2 主張には `isPTB_str c` が必要）
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- Composing an scb decomposition inside a principal marked component. -/
theorem scb_compose (t c₀ : BT) (s₀ s₁ c₁ b₁ b₀ : List Sym)
    (hc₀ : ∃ p, c₀ = .trm [p])
    (h₀ : scb_decomp t s₀ (flatBT c₀) b₀)
    (h₁ : scb_decomp c₀ s₁ c₁ b₁) :
    scb_decomp t (s₀ ++ s₁) c₁ (b₁ ++ b₀) := by
  obtain ⟨p, rfl⟩ := hc₀
  rcases h₀ with ⟨hflat₀, hprincipal₀, htail₀⟩
  rcases h₁ with ⟨hflat₁, hprincipal₁, htail₁⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hflat₀, hflat₁]
    simp [List.append_assoc]
  · intro _
    exact hprincipal₁ (by simp [BZero])
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact htail₁ x hx
    · exact htail₀ x hx

/-- Corrected A11 form: a decomposition remains one after adding a `D_v` prefix,
provided the marked string is principal. -/
theorem scb_compose_dprin (v : ℕ∞) (t : BT) (s c b : List Sym)
    (h : scb_decomp t s c b) (hc : isPTB_str c) :
    scb_decomp (Dprin v t) (.dsym v :: s) c b := by
  rcases h with ⟨hflat, _, htail⟩
  refine ⟨?_, ?_, htail⟩
  · simp [Dprin, flatBT, flatBP, hflat, List.append_assoc]
  · intro _
    exact hc

private theorem not_isPTB_zero : ¬isPTB_str [.zero] := by
  rintro ⟨p, _, hp⟩
  cases p with
  | db u a => simp [flatBP] at hp

/-- The uncorrected second claim is false at zero: its hypothesis does not force
the marked string to be principal. -/
theorem scb_compose_dprin_original_false (v : ℕ∞) :
    scb_decomp BZero [] [.zero] [] ∧
      ¬scb_decomp (Dprin v BZero) [.dsym v] [.zero] [] := by
  constructor
  · simp [scb_decomp, BZero, flatBT]
  · simp [scb_decomp, Dprin, BZero, flatBT, flatBP, not_isPTB_zero]

#print axioms scb_compose
#print axioms scb_compose_dprin
#print axioms scb_compose_dprin_original_false

end PSS

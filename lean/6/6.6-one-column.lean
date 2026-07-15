import «6».«6.6-reduced-iff-condAB»

/-!
# §6.6 系（`1` 列ペア数列の基本性質）

- 原文: `tmp/content.md` の「系（1列ペア数列の基本性質）」
- 訂正: なし
- Isabelle: `m_6_6_oneColumn`, `Red_singleton`
- 依存: §6.5 `Red_rebase_nonmulti`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem singleton_RedCondA (a b : ℕ) :
    RedCondA [(a, b)] = true := by
  apply RedCondA_intro
  intro i j hi hj hp
  have hj0 : j = 0 := by simpa using hj
  subst j
  rw [no_parent_zero] at hp
  contradiction

private theorem singleton_nonmulti (a b : ℕ) :
    multiT [(a, b)] = false := by
  by_cases hb : b = 0
  · simp [multiT, zeroT, hb, entry]
  · have hz : zeroT [(a, b)] = false := by
      simp [zeroT, entry, hb]
    have hmono : monoT [(a, b)] = true := by
      simp [monoT, hz, leR, le0, le0Aux]
    simp [multiT, hz, hmono]

theorem Red_singleton (a b : ℕ) : Red [(a, b)] = [(b, b)] := by
  have hT : TPS [(a, b)] := by simp [TPS]
  have hred := Red_rebase_nonmulti [(a, b)] hT
    (singleton_RedCondA a b) (singleton_nonmulti a b)
  simpa [rebaseRow0, entry] using hred

/-- A reduced one-column pair sequence is exactly a diagonal singleton. -/
theorem one_column (M : PS) (hM : TPS M) :
    (Lng M = 1 ∧ RTPS M) ↔ ∃ v, M = [(v, v)] := by
  constructor
  · rintro ⟨hL, hR⟩
    rcases List.length_eq_one_iff.mp hL with ⟨p, rfl⟩
    rcases p with ⟨a, b⟩
    have hfix := RTPS_Red_eq [(a, b)] hR
    have heq : [(a, b)] = [(b, b)] := hfix.symm.trans (Red_singleton a b)
    have hab : a = b := by simpa using congrArg (fun X : PS => entry X 0 0) heq
    exact ⟨b, by simp [hab]⟩
  · rintro ⟨v, rfl⟩
    constructor
    · simp
    · have hfix := Red_singleton v v
      simp [RTPS, reduced, hfix]

#print axioms Red_singleton
#print axioms one_column

end PSS

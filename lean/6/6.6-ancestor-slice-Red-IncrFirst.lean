import «6».«6.6-reduced-coeff»
import «6».«6.2-mono-ancestor-slice»

/-!
# §6.6 系（直系先祖による切片と `Red` と `IncrFirst` の関係）

- 原文: `tmp/content.md` の同名の系
- 訂正: A2（反復回数の添字 `m` を `j₀` に訂正）
- Isabelle: `m_6_6_ancestor_slice_Red_IncrFirst`
- 依存: §6.5 `Red_rebase_nonmulti`, §6.6 `reduced_coeff`, RED2
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- A reduced ancestor-anchored slice is recovered from its reduction by
raising row zero by the coefficient gap at the slice's left endpoint. -/
theorem ancestor_slice_Red_IncrFirst (M : PS) (j₀ j₁ : ℕ)
    (hR : RTPS M) (hlt : j₀ < j₁) (hj₁ : j₁ ≤ Lng M - 1)
    (hanc : leR M 0 j₀ j₁ = true) :
    let S := seg M j₀ j₁
    let N := Red S
    Red N = N ∧ monoT N = true ∧
      S = IncrFirstN (entry M 0 j₀ - entry M 1 j₀) N := by
  let S := seg M j₀ j₁
  let N := Red S
  let c := entry M 0 j₀
  let d := entry M 1 j₀
  let k := c - d
  have hM : TPS M := RTPS_TPS M hR
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hj₁L : j₁ < Lng M := by omega
  have hj₀L : j₀ < Lng M := hlt.trans hj₁L
  have hSlen : Lng S = j₁ + 1 - j₀ := by simp [S]
  have hSpos : 0 < Lng S := by rw [hSlen]; omega
  have hST : TPS S := List.ne_nil_of_length_pos hSpos
  have hmonoS : monoT S = true := by
    simpa [S] using mono_ancestor_slice M j₀ j₁ hM hlt hanc
  have hSnm : multiT S = false := by simp [multiT, hmonoS]
  obtain ⟨hAM, _hBM⟩ := RTPS_condAB M hR
  have hAS : RedCondA S = true := by
    simpa [S] using RedCondA_seg M j₀ j₁ hlt.le hj₁L hAM
  have hcS : entry S 0 0 = c := by
    simpa [S, c] using entry_seg M j₀ j₁ 0 0 hSpos
  have hdS : entry S 1 0 = d := by
    simpa [S, d] using entry_seg M j₀ j₁ 1 0 hSpos
  have hdom : d ≤ c := by
    simpa [c, d] using reduced_coeff M hR j₀ hj₀L
  have hfloor : ∀ q < Lng S, c ≤ entry S 0 q := by
    intro q hq
    by_cases hq0 : q = 0
    · subst q
      simpa [hcS]
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      have hidx : j₀ + q ≤ j₁ := by rw [hSlen] at hq; omega
      have hgrowth := ancestor_basic_1 M j₀ (j₀ + q) j₁ hM
        (by omega) hidx hanc
      have heq := entry_seg M j₀ j₁ 0 q (by simpa [S] using hq)
      simpa [S, c] using (hgrowth.le.trans_eq heq.symm)
  have hNrebase : N = rebaseRow0 c d S := by
    simpa [N, c, d, hcS, hdS] using
      Red_rebase_nonmulti S hST hAS hSnm
  have hread : S = IncrFirstN k N := by
    rw [hNrebase, IncrFirstN_eq_map]
    apply List.ext_getElem
    · simp [rebaseRow0]
    · intro q hqS _hqR
      have hq : q < Lng S := by simpa using hqS
      have hSq : S[q] = (entry S 0 q, entry S 1 q) := by
        apply Prod.ext
        · exact (entry0_eq_fst_getElem_mr S q hq).symm
        · simpa [entry, List.getElem?_eq_getElem hq]
      simp only [rebaseRow0, List.getElem_map]
      rw [hSq]
      apply Prod.ext
      · simp only [Prod.fst, k]
        have := hfloor q hq
        omega
      · simp
  have hNR : RTPS N := by
    simpa [N] using Red_nonmulti_RTPS S hST hSnm
  have hredN : Red N = N := RTPS_Red_eq N hNR
  have hmonoN : monoT N = true := by
    simpa [N] using Red_preserves_monoT_forward S hST hmonoS
  simpa [S, N, c, d, k] using And.intro hredN (And.intro hmonoN hread)

#print axioms ancestor_slice_Red_IncrFirst

end PSS

import «6».«6.5-Red-welldefined»
import «6».«6.2-P-IncrFirst-equivariance»

/-!
# §6.5 命題（`Red` の `IncrFirst` 不変性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_IncrFirst`
- 訂正: なし
- Isabelle: `m_6_5_Red_IncrFirst`
- 依存: `6.5-Red-welldefined`, `6.2-P-IncrFirst-equivariance`
- 状態: 🚨 証明作業中
-/

namespace PSS

@[simp] private theorem length_IncrFirst_ri (M : PS) :
    Lng (IncrFirst M) = Lng M := by
  simp [IncrFirst]

private theorem IncrFirst_TPS (M : PS) (hM : TPS M) : TPS (IncrFirst M) := by
  simpa [TPS, IncrFirst] using hM

private theorem entry_IncrFirst0_ri (M : PS) (j : ℕ) (hj : j < Lng M) :
    entry (IncrFirst M) 0 j = entry M 0 j + 1 := by
  simp [IncrFirst, entry, hj]

private theorem entry_IncrFirst1_ri (M : PS) (j : ℕ) :
    entry (IncrFirst M) 1 j = entry M 1 j := by
  simp only [IncrFirst, entry, List.getElem?_map]
  cases h : M[j]? <;> simp [h]

private theorem zeroT_IncrFirst_ri (M : PS) :
    zeroT (IncrFirst M) = zeroT M := by
  simp [zeroT, entry_IncrFirst1_ri]

private theorem monoT_IncrFirst_ri (M : PS) :
    monoT (IncrFirst M) = monoT M := by
  simp [monoT, zeroT_IncrFirst_ri, le_IncrFirst_invariance]

private theorem multiT_IncrFirst_ri (M : PS) :
    multiT (IncrFirst M) = multiT M := by
  simp [multiT, zeroT_IncrFirst_ri, monoT_IncrFirst_ri]

/-- In the `m₁₀ = 0` branch, shifting row zero and then rebasing it gives
exactly the same recursive argument. -/
private theorem coreReduce_IncrFirst_zero (M : PS) (hM : TPS M)
    (hm₁ : entry M 1 0 = 0) :
    coreReduce (IncrFirst M) = coreReduce M := by
  have hMpos := List.length_pos_of_ne_nil hM
  change 0 < Lng M at hMpos
  have hI₁ : entry (IncrFirst M) 1 0 = 0 := by
    rw [entry_IncrFirst1_ri, hm₁]
  rw [coreReduce, if_pos hI₁, coreReduce, if_pos hm₁]
  rw [length_IncrFirst_ri]
  apply List.map_congr_left
  intro j hj
  have hjL : j < Lng M := List.mem_range.mp hj
  rw [entry_IncrFirst0_ri M j hjL,
    entry_IncrFirst0_ri M 0 hMpos, entry_IncrFirst1_ri]
  congr 1 <;> omega

private theorem entries_range_eq (M : PS) :
    (List.range (Lng M)).map (fun j => (entry M 0 j, entry M 1 j)) = M := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    have hj : j < Lng M := by simpa using hj₂
    simp only [List.getElem_map, List.getElem_range]
    simp [entry, List.getElem?_eq_getElem hj]

private theorem Red_zero_branch (M : PS) (hz : zeroT M = true) :
    Red M = [(0, 0)] := by
  unfold Red
  rw [RedAux, if_pos hz]

private theorem Red_multi_branch (M : PS) (hM : TPS M)
    (hmulti : multiT M = true) :
    Red M = (P M).flatMap Red := by
  have hz : zeroT M ≠ true := by
    intro hz
    simp [multiT, hz] at hmulti
  unfold Red
  rw [RedAux, if_neg hz, if_pos hmulti]
  apply List.flatMap_congr
  intro Q hQ
  have hQT : TPS Q := by
    obtain ⟨J, hJ, hget⟩ := List.mem_iff_getElem.mp hQ
    have hpos := P_component_nonempty M J hM hJ
    have heq : (P M).getD J [] = Q := by
      rw [getD_eq_getElem_idx (P M) [] hJ]
      exact hget
    rw [heq] at hpos
    exact List.ne_nil_of_length_pos hpos
  apply RedAux_stable Q hQT (nu M)
  exact nu_Pblock_lt M Q hM hmulti hQ

/-! The four easy branches of the Isabelle proof reduce to the remaining
positive-`m₁₀` cut identity.  The cut engine is developed below this lemma. -/

theorem Red_IncrFirst_of_positive (M : PS) (hM : TPS M)
    (hPositive : ∀ X, TPS X → monoT X = true → 0 < entry X 1 0 →
      Red (IncrFirst X) = Red X) :
    Red (IncrFirst M) = Red M := by
  generalize hn : nu M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hIT := IncrFirst_TPS M hM
      by_cases hz : zeroT M = true
      · have hzI : zeroT (IncrFirst M) = true := by
          simpa [zeroT_IncrFirst_ri] using hz
        rw [Red_zero_branch M hz, Red_zero_branch (IncrFirst M) hzI]
      · by_cases hmulti : multiT M = true
        · have hmultiI : multiT (IncrFirst M) = true := by
            simpa [multiT_IncrFirst_ri] using hmulti
          rw [Red_multi_branch M hM hmulti,
            Red_multi_branch (IncrFirst M) hIT hmultiI,
            P_IncrFirst_equivariance]
          simp only [List.flatMap_map]
          apply List.flatMap_congr
          intro Q hQ
          have hQT : TPS Q := by
            obtain ⟨J, hJ, hget⟩ := List.mem_iff_getElem.mp hQ
            have hpos := P_component_nonempty M J hM hJ
            have heq : (P M).getD J [] = Q := by
              rw [getD_eq_getElem_idx (P M) [] hJ]
              exact hget
            rw [heq] at hpos
            exact List.ne_nil_of_length_pos hpos
          have hdesc := nu_Pblock_lt M Q hM hmulti hQ
          exact ih (nu Q) (by omega) Q hQT rfl
        · have hmono : monoT M = true := by
            have hh := hmulti
            simp [multiT, hz] at hh
            exact hh
          let m₀ := entry M 0 0
          let m₁ := entry M 1 0
          by_cases hcore : m₀ = 0 ∧ m₁ = 0
          · have hcore' : entry M 0 0 = 0 ∧ entry M 1 0 = 0 := by
              simpa [m₀, m₁] using hcore
            have hIcore : ¬(entry (IncrFirst M) 0 0 = 0 ∧
                entry (IncrFirst M) 1 0 = 0) := by
              have hMpos := List.length_pos_of_ne_nil hM
              change 0 < Lng M at hMpos
              have he := entry_IncrFirst0_ri M 0 hMpos
              omega
            have hI₁ : entry (IncrFirst M) 1 0 = 0 := by
              simpa [entry_IncrFirst1_ri] using hcore'.2
            have hcr : coreReduce (IncrFirst M) = M := by
              rw [coreReduce_IncrFirst_zero M hM hcore'.2]
              simpa [coreReduce, hcore'.2, hcore'.1] using entries_range_eq M
            have hnu : nu M < nu (IncrFirst M) := by
              have hmM : multiT M = false := by simpa using hmulti
              have hmI : multiT (IncrFirst M) = false := by
                simpa [multiT_IncrFirst_ri] using hmulti
              have hbeta : betaM (coreReduce (IncrFirst M)) = betaM M := by rw [hcr]
              simp [nu, muMono, hmM, hmI, hcore', hIcore, hbeta]
            unfold Red
            rw [RedAux, if_neg (by simpa [zeroT_IncrFirst_ri] using hz),
              if_neg (by simpa [multiT_IncrFirst_ri] using hmulti),
              if_neg hIcore, if_pos hI₁, hcr]
            exact RedAux_stable M hM (nu (IncrFirst M)) hnu
          · have hcore' : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by
              simpa [m₀, m₁] using hcore
            by_cases hm₁ : m₁ = 0
            · have hm₁' : entry M 1 0 = 0 := by simpa [m₁] using hm₁
              have hcrEq := coreReduce_IncrFirst_zero M hM hm₁'
              have hIcore : ¬(entry (IncrFirst M) 0 0 = 0 ∧
                  entry (IncrFirst M) 1 0 = 0) := by
                have hMpos := List.length_pos_of_ne_nil hM
                change 0 < Lng M at hMpos
                have he := entry_IncrFirst0_ri M 0 hMpos
                omega
              have hI₁ : entry (IncrFirst M) 1 0 = 0 := by
                simpa [entry_IncrFirst1_ri] using hm₁'
              have hcrT : TPS (coreReduce M) := by
                apply List.ne_nil_of_length_pos
                change 0 < Lng (coreReduce M)
                simp [coreReduce, hm₁']
                exact List.length_pos_of_ne_nil hM
              have hdesc := nu_coreReduce_lt M hM hmono hcore'
              have hstableM := RedAux_stable (coreReduce M) hcrT (nu M) hdesc
              have hmonoI : monoT (IncrFirst M) = true := by
                simpa [monoT_IncrFirst_ri] using hmono
              have hdescI := nu_coreReduce_lt (IncrFirst M) hIT hmonoI hIcore
              have hstableI := RedAux_stable (coreReduce (IncrFirst M))
                (by rw [hcrEq]; exact hcrT) (nu (IncrFirst M)) hdescI
              have hRM : Red M = Red (coreReduce M) := by
                change RedAux (nu M + 1) M = Red (coreReduce M)
                rw [RedAux, if_neg hz, if_neg hmulti, if_neg hcore', if_pos hm₁',
                  hstableM]
              have hRI : Red (IncrFirst M) = Red (coreReduce (IncrFirst M)) := by
                change RedAux (nu (IncrFirst M) + 1) (IncrFirst M) =
                  Red (coreReduce (IncrFirst M))
                rw [RedAux, if_neg (by simpa [zeroT_IncrFirst_ri] using hz),
                  if_neg (by simpa [multiT_IncrFirst_ri] using hmulti),
                  if_neg hIcore, if_pos hI₁, hstableI]
              rw [hRI, hRM, hcrEq]
            · have hm₁pos : 0 < entry M 1 0 := by
                change entry M 1 0 ≠ 0 at hm₁
                omega
              exact hPositive M hM hmono hm₁pos

end PSS

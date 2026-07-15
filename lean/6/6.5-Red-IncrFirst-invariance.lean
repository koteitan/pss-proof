import «6».«6.5-Red-welldefined»
import «6».«6.5-monoT-Red»
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

/-! ## The cut-bump engine

`bumpAt M n` raises precisely the row-zero values at or above `n`.  It is an
order embedding, so all structural predicates used by `Red` are unchanged.
-/

def bumpV (n v : ℕ) : ℕ := if v < n then v else v + 1

def bumpAt (M : PS) (n : ℕ) : PS :=
  M.map (fun p => (bumpV n p.1, p.2))

@[simp] theorem length_bumpAt (M : PS) (n : ℕ) :
    Lng (bumpAt M n) = Lng M := by simp [bumpAt]

theorem bumpV_lt_iff (n a b : ℕ) : bumpV n a < bumpV n b ↔ a < b := by
  simp only [bumpV]
  split <;> split <;> omega

theorem bumpV_le_iff (n a b : ℕ) : bumpV n a ≤ bumpV n b ↔ a ≤ b := by
  simp only [bumpV]
  split <;> split <;> omega

private theorem entry_bumpAt0 (M : PS) (n j : ℕ) (hj : j < Lng M) :
    entry (bumpAt M n) 0 j = bumpV n (entry M 0 j) := by
  simp [bumpAt, entry, hj]

private theorem entry_bumpAt1 (M : PS) (n j : ℕ) :
    entry (bumpAt M n) 1 j = entry M 1 j := by
  simp only [bumpAt, entry, List.getElem?_map]
  cases h : M[j]? <;> simp [h]

theorem nextrel0_bumpAt (M : PS) (n : ℕ) :
    nextrel0 (bumpAt M n) = nextrel0 M := by
  funext a b
  by_cases ha : a < Lng M
  · by_cases hb : b < Lng M
    · simp only [nextrel0, length_bumpAt, Bool.and_eq_true,
        decide_eq_true_eq]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, List.mem_range]
      simp only [ha, hb, true_and]
      constructor
      · rintro ⟨⟨hab, hentry⟩, hall⟩
        refine ⟨⟨hab, ?_⟩, ?_⟩
        · rw [entry_bumpAt0 M n a ha, entry_bumpAt0 M n b hb] at hentry
          exact (bumpV_lt_iff n _ _).mp hentry
        · intro j hj
          have hjL : j < Lng M := hj.trans hb
          have hh := hall j hj
          by_cases haj : a < j
          · simp only [haj, decide_true, Bool.not_true, Bool.false_or] at hh ⊢
            rw [entry_bumpAt0 M n b hb, entry_bumpAt0 M n j hjL] at hh
            exact decide_eq_true ((bumpV_le_iff n _ _).mp (of_decide_eq_true hh))
          · simpa [haj]
      · rintro ⟨⟨hab, hentry⟩, hall⟩
        refine ⟨⟨hab, ?_⟩, ?_⟩
        · rw [entry_bumpAt0 M n a ha, entry_bumpAt0 M n b hb]
          exact (bumpV_lt_iff n _ _).mpr hentry
        · intro j hj
          have hjL : j < Lng M := hj.trans hb
          have hh := hall j hj
          by_cases haj : a < j
          · simp only [haj, decide_true, Bool.not_true, Bool.false_or] at hh ⊢
            rw [entry_bumpAt0 M n b hb, entry_bumpAt0 M n j hjL]
            exact decide_eq_true ((bumpV_le_iff n _ _).mpr (of_decide_eq_true hh))
          · simpa [haj]
    · simp [nextrel0, hb]
  · simp [nextrel0, ha]

private theorem le0Aux_bumpAt (M : PS) (n fuel a b : ℕ) :
    le0Aux (bumpAt M n) fuel a b = le0Aux M fuel a b := by
  induction fuel generalizing b with
  | zero => rfl
  | succ fuel ih =>
      simp only [le0Aux, nextrel0_bumpAt M n, ih]

theorem le0_bumpAt (M : PS) (n : ℕ) : le0 (bumpAt M n) = le0 M := by
  funext a b
  simp [le0, le0Aux_bumpAt]

theorem nextrel1_bumpAt (M : PS) (n : ℕ) :
    nextrel1 (bumpAt M n) = nextrel1 M := by
  funext a b
  by_cases ha : a < Lng M
  · by_cases hb : b < Lng M
    · simp [nextrel1, ha, hb, entry_bumpAt1, le0_bumpAt]
    · simp [nextrel1, hb]
  · simp [nextrel1, ha]

private theorem le1Aux_bumpAt (M : PS) (n fuel a b : ℕ) :
    le1Aux (bumpAt M n) fuel a b = le1Aux M fuel a b := by
  induction fuel generalizing b with
  | zero => rfl
  | succ fuel ih =>
      simp only [le1Aux, nextrel1_bumpAt M n, ih]

theorem le1_bumpAt (M : PS) (n : ℕ) : le1 (bumpAt M n) = le1 M := by
  funext a b
  simp [le1, le1Aux_bumpAt]

theorem nextR_bumpAt (M : PS) (n : ℕ) : nextR (bumpAt M n) = nextR M := by
  funext i a b
  by_cases hi : i = 0
  · simp [nextR, hi, nextrel0_bumpAt]
  · simp [nextR, hi, nextrel1_bumpAt]

theorem leR_bumpAt (M : PS) (n : ℕ) : leR (bumpAt M n) = leR M := by
  funext i a b
  by_cases hi : i = 0
  · simp [leR, hi, le0_bumpAt]
  · simp [leR, hi, le1_bumpAt]

@[simp] theorem zeroT_bumpAt (M : PS) (n : ℕ) :
    zeroT (bumpAt M n) = zeroT M := by
  simp [zeroT, entry_bumpAt1]

@[simp] theorem monoT_bumpAt (M : PS) (n : ℕ) :
    monoT (bumpAt M n) = monoT M := by
  simp [monoT, leR_bumpAt]

@[simp] theorem multiT_bumpAt (M : PS) (n : ℕ) :
    multiT (bumpAt M n) = multiT M := by
  simp [multiT]

theorem TrMax_bumpAt (M : PS) (n : ℕ) :
    TrMax (bumpAt M n) = TrMax M := by
  simp [TrMax, nextR_bumpAt]

@[simp] theorem Pcut_bumpAt (M : PS) (n : ℕ) :
    Pcut (bumpAt M n) = Pcut M := by
  simp [Pcut, leR_bumpAt]

private theorem bumpAt_take (M : PS) (n k : ℕ) :
    bumpAt (M.take k) n = (bumpAt M n).take k := by
  simp [bumpAt]

private theorem bumpAt_drop (M : PS) (n k : ℕ) :
    bumpAt (M.drop k) n = (bumpAt M n).drop k := by
  simp [bumpAt]

private theorem PAux_bumpAt (fuel : ℕ) (M : PS) (n : ℕ) :
    PAux fuel (bumpAt M n) = (PAux fuel M).map (fun Q => bumpAt Q n) := by
  induction fuel generalizing M with
  | zero => simp [PAux]
  | succ fuel ih =>
      by_cases hc : multiT M = true ∧ 1 < Lng M
      · have hcB : multiT (bumpAt M n) = true ∧ 1 < Lng (bumpAt M n) := by
          simpa using hc
        rw [PAux, if_pos (by simpa [Bool.and_eq_true] using hcB),
          PAux, if_pos (by simpa [Bool.and_eq_true] using hc)]
        rw [Pcut_bumpAt, ← bumpAt_take M n (Pcut M),
          ← bumpAt_drop M n (Pcut M), ih]
        simp
      · have hcB : ¬(multiT (bumpAt M n) = true ∧
            1 < Lng (bumpAt M n)) := by simpa using hc
        rw [PAux, if_neg (by simpa [Bool.and_eq_true] using hcB),
          PAux, if_neg (by simpa [Bool.and_eq_true] using hc)]
        simp

theorem P_bumpAt (M : PS) (n : ℕ) :
    P (bumpAt M n) = (P M).map (fun Q => bumpAt Q n) := by
  simp [P, PAux_bumpAt]

def cutOK (M : PS) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ j, TrMax M < j → j < Lng M → n ≤ entry M 0 j

private theorem entry_IncrFirstN0_ri (n : ℕ) (M : PS) (j : ℕ)
    (hj : j < Lng M) :
    entry (IncrFirstN n M) 0 j = entry M 0 j + n := by
  induction n generalizing M with
  | zero => rfl
  | succ n ih =>
      simp only [IncrFirstN]
      rw [ih (IncrFirst M) (by simpa using hj)]
      rw [entry_IncrFirst0_ri M j hj]
      omega

private theorem entry_coreReduce_pos_tail_ri (M : PS) (j : ℕ)
    (hpos : 0 < entry M 1 0)
    (hj : entry M 1 0 ≤ j) (hjL : j < Lng (coreReduce M)) :
    entry (coreReduce M) 0 j =
      entry M 0 (j - entry M 1 0) + entry M 1 0 := by
  let m := entry M 1 0
  have hm : entry M 1 0 ≠ 0 := by omega
  have hDlen : Lng (diagSeq 0 (m - 1)) = m := by
    simp [diagSeq, m]
    omega
  have hform : coreReduce M = diagSeq 0 (m - 1) ++ IncrFirstN m M := by
    simp [coreReduce, hm, m]
  have hML : j - m < Lng M := by
    have hlen : Lng (coreReduce M) = m + Lng M := by
      simp [coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
      omega
    omega
  have hjD : Lng (diagSeq 0 (m - 1)) ≤ j := by rw [hDlen]; exact hj
  have he : entry (diagSeq 0 (m - 1) ++ IncrFirstN m M) 0 j =
      entry (IncrFirstN m M) 0 (j - Lng (diagSeq 0 (m - 1))) := by
    simp [entry, List.getElem?_append_right hjD]
  rw [hform, he, hDlen]
  exact entry_IncrFirstN0_ri m M (j - m) hML

theorem cutOK_coreReduce (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    cutOK (coreReduce M) (entry M 1 0) := by
  constructor
  · omega
  · intro j hjtr hjL
    have hmtr := coreReduce_m10_le_TrMax M hM hpos
    have hmj : entry M 1 0 ≤ j := by omega
    rw [entry_coreReduce_pos_tail_ri M j hpos hmj hjL]
    omega

end PSS

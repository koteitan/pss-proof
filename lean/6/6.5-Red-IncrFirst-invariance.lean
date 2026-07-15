import «6».«6.5-Red-welldefined»
import «6».«6.5-monoT-Red»
import «6».«6.2-P-IncrFirst-equivariance»

/-!
# §6.5 命題（`Red` の `IncrFirst` 不変性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_IncrFirst`
- 訂正: なし
- Isabelle: `m_6_5_Red_IncrFirst`
- 依存: `6.5-Red-welldefined`, `6.2-P-IncrFirst-equivariance`
- 状態: ✅ 証明済（sorry 0）
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

theorem multiT_IncrFirst_ri (M : PS) :
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

theorem coreReduce_IncrFirst_bumpAt (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    coreReduce (IncrFirst M) =
      bumpAt (coreReduce M) (entry M 1 0) := by
  have hm : entry M 1 0 ≠ 0 := by omega
  have hmI : entry (IncrFirst M) 1 0 = entry M 1 0 :=
    entry_IncrFirst1_ri M 0
  rw [coreReduce, if_neg (by simpa [hmI] using hm),
    coreReduce, if_neg hm]
  rw [hmI]
  simp only [IncrFirstN_eq_map, IncrFirst, bumpAt, List.map_append,
    List.map_map]
  congr 1
  · symm
    calc
      List.map (fun p => (bumpV (entry M 1 0) p.1, p.2))
          (diagSeq 0 (entry M 1 0 - 1)) =
          List.map id (diagSeq 0 (entry M 1 0 - 1)) := by
            apply List.map_congr_left
            intro p hp
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
            simp only [Function.comp_apply, Prod.fst, Prod.snd, id_eq]
            have hjlt : j < entry M 1 0 := by
              simp [diagSeq] at hj
              omega
            simp [bumpV, hjlt]
      _ = diagSeq 0 (entry M 1 0 - 1) := List.map_id _
  · apply List.map_congr_left
    intro p hp
    obtain ⟨a, b⟩ := p
    simp [bumpV]
    omega

private theorem seg_bumpAt (M : PS) (n a b : ℕ)
    (ha : a ≤ b) (hb : b < Lng M) :
    seg (bumpAt M n) a b = bumpAt (seg M a b) n := by
  unfold seg bumpAt
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  have hjr := List.mem_range'.mp hj
  have hjL : j < Lng M := by omega
  apply Prod.ext
  · simp only [Prod.fst, Function.comp_apply]
    change entry (bumpAt M n) 0 j = bumpV n (entry M 0 j)
    exact entry_bumpAt0 M n j hjL
  · simp only [Prod.snd, Function.comp_apply]
    change entry (bumpAt M n) 1 j = entry M 1 j
    exact entry_bumpAt1 M n j

private theorem seg_bumpAt_cut (M : PS) (n : ℕ) (hM : TPS M)
    (hcut : cutOK M n) (hne : TrMax M ≠ Lng M - 1) :
    seg (bumpAt M n) (TrMax M + 1) (Lng M - 1) =
      IncrFirst (seg M (TrMax M + 1) (Lng M - 1)) := by
  have htr := TrMax_bound M hM
  have hL : 0 < Lng M := List.length_pos_of_ne_nil hM
  have ha : TrMax M + 1 ≤ Lng M - 1 := by omega
  have hb : Lng M - 1 < Lng M := by omega
  rw [seg_bumpAt M n _ _ ha hb]
  unfold bumpAt IncrFirst seg
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  have hjr := List.mem_range'.mp hj
  have hjtr : TrMax M < j := by omega
  have hjL : j < Lng M := by omega
  have hge := hcut.2 j hjtr hjL
  simp [bumpV, Nat.not_lt.mpr hge]

theorem Br_bumpAt (M : PS) (n : ℕ) (hM : TPS M)
    (hcut : cutOK M n) :
    Br (bumpAt M n) = (Br M).map IncrFirst := by
  by_cases hne : TrMax M = Lng M - 1
  · simp [Br, TrMax_bumpAt, hne]
  · rw [Br, if_neg (by simpa [TrMax_bumpAt] using hne),
      Br, if_neg hne]
    rw [TrMax_bumpAt, length_bumpAt]
    rw [seg_bumpAt_cut M n hM hcut hne]
    exact P_IncrFirst_equivariance _

private theorem IdxSum_map_IncrFirst (Q : List PS) :
    IdxSum (Q.map IncrFirst) = IdxSum Q := by
  unfold IdxSum
  simp only [List.length_map]
  apply List.map_congr_left
  intro a ha
  have htake : (Q.map IncrFirst).take a = (Q.take a).map IncrFirst := by
    simp
  rw [htake, List.map_map]
  congr 1
  apply List.map_congr_left
  intro M hM
  simp [IncrFirst]

theorem FirstNodes_bumpAt (M : PS) (n : ℕ) (hM : TPS M)
    (hcut : cutOK M n) :
    FirstNodes (bumpAt M n) = FirstNodes M := by
  simp [FirstNodes, Br_bumpAt M n hM hcut, TrMax_bumpAt,
    IdxSum_map_IncrFirst]

theorem parent_bumpAt (M : PS) (n i j : ℕ) :
    parent (bumpAt M n) i j = parent M i j := by
  simp [parent, parents, length_bumpAt, nextR_bumpAt]

theorem Joints_bumpAt (M : PS) (n : ℕ) (hM : TPS M)
    (hcut : cutOK M n) :
    Joints (bumpAt M n) = Joints M := by
  simp [Joints, Br_bumpAt M n hM hcut,
    FirstNodes_bumpAt M n hM hcut, parent_bumpAt]

private theorem Br_getD_bumpAt (M : PS) (n J : ℕ) (hM : TPS M)
    (hcut : cutOK M n) (hJ : J < (Br M).length) :
    (Br (bumpAt M n)).getD J [] = IncrFirst ((Br M).getD J []) := by
  have hJA : J < (Br (bumpAt M n)).length := by
    simpa [Br_bumpAt M n hM hcut] using hJ
  rw [getD_eq_getElem_idx (Br (bumpAt M n)) [] hJA,
    getD_eq_getElem_idx (Br M) [] hJ]
  simp [Br_bumpAt M n hM hcut, List.getElem_map]

private def branchNP_ri (M : PS) (J : ℕ) : ℕ :=
  if entry ((Br M).getD J []) 1 0 = 0 then 0
  else parent M 1 ((FirstNodes M).getD J 0) + 1

private theorem branchNP_bumpAt (M : PS) (n J : ℕ) (hM : TPS M)
    (hcut : cutOK M n) (hJ : J < (Br M).length) :
    branchNP_ri (bumpAt M n) J = branchNP_ri M J := by
  have hb := Br_getD_bumpAt M n J hM hcut hJ
  rw [branchNP_ri, branchNP_ri, hb, entry_IncrFirst1_ri,
    FirstNodes_bumpAt M n hM hcut, parent_bumpAt]

private theorem branch_tail_ge_fresh_cut (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore0 : entry M 0 0 = 0) (hJ : J < (Br M).length)
    (p : ℕ × ℕ) (hp : p ∈ ((Br M).getD J []).tail) :
    (Joints M).getD J 0 + 2 ≤ p.1 := by
  let B := (Br M).getD J []
  have hBT : TPS B := Br_component_TPS M J hM hJ
  obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp hp
  have htailLen : B.tail.length + 1 = B.length := by
    cases hB : B with
    | nil => exact (hBT hB).elim
    | cons q qs => simp
  have hkBlen : k + 1 < B.length := by
    change k < B.tail.length at hk
    omega
  have hkB : k + 1 < Lng B := hkBlen
  have hpget : p = B[k + 1] := by
    rw [← hkp, List.getElem_tail]
  have hBmulti : multiT B = false := by
    rcases Br_component_nonmulti M J hM hJ with hz | hm
    · have hBL : Lng B = 1 := by
        have hh := hz
        simp [zeroT] at hh
        exact hh.1
      omega
    · change monoT B = true at hm
      simp [multiT, hm]
  have hstrict := (multi_criterion_12 B hBT).mp hBmulti
    (k + 1) (by omega) hkB
  have hhead := redNJ_head_le_block M J hM hmono hcore0 hJ
  change (Joints M).getD J 0 + 1 ≤ entry B 0 0 at hhead
  have he : entry B 0 (k + 1) = B[k + 1].1 := by
    simp [entry, List.getElem?_eq_getElem hkB]
  rw [hpget, ← he]
  omega

theorem redNJ_bumpAt (M : PS) (n J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hcut : cutOK M n)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hJ : J < (Br M).length) :
    redNJ (bumpAt M n) J =
      bumpAt (redNJ M J) ((Joints M).getD J 0 + 2) := by
  have hL : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hA0 : entry (bumpAt M n) 0 0 = 0 := by
    rw [entry_bumpAt0 M n 0 hL]
    have hc : 1 ≤ n ∧ ∀ j, TrMax M < j → j < Lng M →
        n ≤ entry M 0 j := by simpa [cutOK] using hcut
    have hn : 1 ≤ n := hc.1
    have h0n : 0 < n := by omega
    simp [bumpV, hcore.1, h0n]
  have hA1 : entry (bumpAt M n) 1 0 = 0 := by
    rw [entry_bumpAt1 M n 0, hcore.2]
  have hB := Br_getD_bumpAt M n J hM hcut hJ
  have hF := FirstNodes_bumpAt M n hM hcut
  have hK := Joints_bumpAt M n hM hcut
  have hnp := branchNP_bumpAt M n J hM hcut hJ
  change
    (entry (bumpAt M n) 0 0 + (Joints (bumpAt M n)).getD J 0 + 1,
        entry (bumpAt M n) 1 0 + branchNP_ri (bumpAt M n) J) ::
        ((Br (bumpAt M n)).getD J []).tail =
      bumpAt
        ((entry M 0 0 + (Joints M).getD J 0 + 1,
            entry M 1 0 + branchNP_ri M J) :: ((Br M).getD J []).tail)
        ((Joints M).getD J 0 + 2)
  rw [hA0, hA1, hcore.1, hcore.2, hB, hK, hnp]
  simp only [bumpAt, IncrFirst, List.map_cons]
  congr 1
  · simp [bumpV]
  · have ht :
        (List.map (fun p => (p.1 + 1, p.2)) ((Br M).getD J [])).tail =
          List.map (fun p => (p.1 + 1, p.2)) ((Br M).getD J []).tail := by
        cases (Br M).getD J [] <;> simp
    rw [ht]
    apply List.map_congr_left
    intro p hp
    have hge := branch_tail_ge_fresh_cut M J hM hmono hcore.1 hJ p hp
    change (Joints M)[J]?.getD 0 + 2 ≤ p.1 at hge
    simp [bumpV, Nat.not_lt.mpr hge]

private theorem branch_entry_ge_fresh_cut (M : PS) (J j : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore0 : entry M 0 0 = 0) (hJ : J < (Br M).length)
    (hjpos : 0 < j) (hj : j < Lng ((Br M).getD J [])) :
    (Joints M).getD J 0 + 2 ≤ entry ((Br M).getD J []) 0 j := by
  let B := (Br M).getD J []
  change j < Lng B at hj
  have hBT : TPS B := Br_component_TPS M J hM hJ
  have hBmulti : multiT B = false := by
    rcases Br_component_nonmulti M J hM hJ with hz | hm
    · have hBL : Lng B = 1 := by
        have hh := hz
        simp [zeroT] at hh
        exact hh.1
      omega
    · change monoT B = true at hm
      simp [multiT, hm]
  have hstrict := (multi_criterion_12 B hBT).mp hBmulti j hjpos hj
  have hhead := redNJ_head_le_block M J hM hmono hcore0 hJ
  change (Joints M).getD J 0 + 1 ≤ entry B 0 0 at hhead
  change (Joints M).getD J 0 + 2 ≤ entry B 0 j
  omega

theorem cutOK_redNJ (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hcore0 : entry M 0 0 = 0)
    (hJ : J < (Br M).length) :
    cutOK (redNJ M J) ((Joints M).getD J 0 + 2) := by
  have hbT := Br_component_TPS M J hM hJ
  constructor
  · omega
  · intro j hjtr hjL
    have hjpos : 0 < j := by omega
    have hjB : j < Lng ((Br M).getD J []) := by
      rw [← redNJ_length M J hbT]
      exact hjL
    rw [redNJ_entry_hi M J j hjpos hjB]
    exact branch_entry_ge_fresh_cut M J j hM hmono hcore0 hJ hjpos hjB

private def branchE_ri (M : PS) (J : ℕ) : ℕ :=
  (Joints M).getD J 0 + 1 - branchNP_ri M J

theorem Red_core_trunk_ri (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M = Lng M - 1) :
    Red M = diagSeq 0 (Lng M - 1) := by
  have hz : zeroT M = false := by
    have hh := hmono
    simp [monoT] at hh
    exact hh.1
  have hmulti : multiT M = false := by simp [multiT, hmono]
  change RedAux (nu M + 1) M = _
  rw [RedAux, if_neg (by simpa using hz), if_neg (by simpa using hmulti),
    if_pos hcore, if_pos ht, hcore.2]
  simp

private theorem Red_core_nontrunk_ri (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M ≠ Lng M - 1) :
    Red M = diagSeq 0 (TrMax M) ++
      (List.range (Br M).length).flatMap (fun J =>
        IncrFirstN (branchE_ri M J) (Red (redNJ M J))) := by
  have hz : zeroT M = false := by
    have hh := hmono
    simp [monoT] at hh
    exact hh.1
  have hmulti : multiT M = false := by simp [multiT, hmono]
  change RedAux (nu M + 1) M = _
  rw [RedAux, if_neg (by simpa using hz), if_neg (by simpa using hmulti),
    if_pos hcore, if_neg ht]
  congr 1
  apply List.flatMap_congr
  intro J hJmem
  have hJ : J < (Br M).length := List.mem_range.mp hJmem
  have hbT := Br_component_TPS M J hM hJ
  have hNJT : TPS (redNJ M J) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [redNJ_length M J hbT]
    exact List.length_pos_of_ne_nil hbT
  have hdesc := nu_redNJ_lt M J hM hmono hcore hJ
  change IncrFirstN _ (RedAux (nu M) (redNJ M J)) =
    IncrFirstN (branchE_ri M J) (Red (redNJ M J))
  have he : (Joints M).getD J 0 + 1 -
      (if entry ((Br M).getD J []) 1 0 = 0 then 0
       else parent M 1 ((FirstNodes M).getD J 0) + 1) = branchE_ri M J := by
    rfl
  rw [he, RedAux_stable (redNJ M J) hNJT (nu M) hdesc]

def redPositiveOut_ri (M N : PS) : PS :=
  let m := entry M 1 0
  let jN := Lng N - 1
  let S := seg N m jN
  if decide (m ≤ jN) && monoT S then
    (List.range' m (jN + 1 - m)).map (fun j =>
      (entry N 0 j - entry N 0 m + entry N 1 m, entry N 1 j))
  else M

theorem Red_noncore_ri (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0)) :
    Red M = if entry M 1 0 = 0 then Red (coreReduce M)
      else redPositiveOut_ri M (Red (coreReduce M)) := by
  have hz : zeroT M = false := by
    have hh := hmono
    simp [monoT] at hh
    exact hh.1
  have hmulti : multiT M = false := by simp [multiT, hmono]
  have hcrT := coreReduce_TPS M hM
  have hdesc := nu_coreReduce_lt M hM hmono hnoncore
  change RedAux (nu M + 1) M = _
  rw [RedAux, if_neg (by simpa using hz), if_neg (by simpa using hmulti),
    if_neg hnoncore]
  by_cases hm : entry M 1 0 = 0
  · rw [if_pos hm, if_pos hm,
      RedAux_stable (coreReduce M) hcrT (nu M) hdesc]
  · rw [if_neg hm, if_neg hm,
      RedAux_stable (coreReduce M) hcrT (nu M) hdesc]
    rfl

private theorem mono_row0_min_ri (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (j : ℕ) (hj : j < Lng M) :
    entry M 0 0 ≤ entry M 0 j := by
  cases j with
  | zero => simp
  | succ j =>
      have hmulti : multiT M = false := by simp [multiT, hmono]
      exact ((multi_criterion_12 M hM).mp hmulti (j + 1) (by omega) hj).le

private theorem TrMax_IncrFirst_ri (M : PS) :
    TrMax (IncrFirst M) = TrMax M := by
  have heq : IncrFirst M = bumpAt M 0 := by
    simp [IncrFirst, bumpAt, bumpV]
  rw [heq, TrMax_bumpAt]

private theorem TrMax_IncrFirstN_ri (k : ℕ) (M : PS) :
    TrMax (IncrFirstN k M) = TrMax M := by
  induction k generalizing M with
  | zero => rfl
  | succ k ih =>
      rw [IncrFirstN, ih, TrMax_IncrFirst_ri]

private theorem coreReduce_zero_reconstruct (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hm : entry M 1 0 = 0) :
    IncrFirstN (entry M 0 0) (coreReduce M) = M := by
  rw [IncrFirstN_eq_map, coreReduce, if_pos hm]
  rw [List.map_map]
  refine Eq.trans ?_ (entries_range_eq M)
  apply List.map_congr_left
  intro j hjmem
  have hj : j < Lng M := List.mem_range.mp hjmem
  simp only [Function.comp_apply]
  apply Prod.ext
  · simp only [Prod.fst]
    have hmin := mono_row0_min_ri M hM hmono j hj
    omega
  · simp

private theorem TrMax_coreReduce_zero (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hm : entry M 1 0 = 0) :
    TrMax (coreReduce M) = TrMax M := by
  rw [← TrMax_IncrFirstN_ri (entry M 0 0) (coreReduce M),
    coreReduce_zero_reconstruct M hM hmono hm]

private theorem bumpV_sub (n v m : ℕ) (hmv : m ≤ v) (hmn : m < n) :
    bumpV n v - bumpV n m = bumpV (n - m) (v - m) := by
  by_cases hv : v < n
  · have hd : v - m < n - m := by omega
    simp [bumpV, hmn, hv, hd]
  · have hd : ¬v - m < n - m := by omega
    simp only [bumpV, if_neg hv, if_pos hmn, if_neg hd]
    exact Nat.succ_sub hmv

private theorem coreReduce_bumpAt_zero (M : PS) (n : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hm : entry M 1 0 = 0) :
    coreReduce (bumpAt M n) =
      if n ≤ entry M 0 0 then coreReduce M
      else bumpAt (coreReduce M) (n - entry M 0 0) := by
  have hL : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hmA : entry (bumpAt M n) 1 0 = 0 := by
    rw [entry_bumpAt1 M n 0, hm]
  rw [coreReduce, if_pos hmA, coreReduce, if_pos hm, length_bumpAt]
  by_cases hn : n ≤ entry M 0 0
  · rw [if_pos hn]
    apply List.ext_getElem
    · simp
    · intro j hj₁ hj₂
      have hj : j < Lng M := by simpa using hj₂
      have hmin := mono_row0_min_ri M hM hmono j hj
      have hnv : n ≤ entry M 0 j := hn.trans hmin
      simp only [List.getElem_map, List.getElem_range]
      rw [entry_bumpAt0 M n j hj, entry_bumpAt0 M n 0 hL,
        entry_bumpAt1 M n j]
      simp [bumpV, Nat.not_lt.mpr hn, Nat.not_lt.mpr hnv]
  · rw [if_neg hn]
    apply List.ext_getElem
    · simp [bumpAt]
    · intro j hj₁ hj₂
      have hj : j < Lng M := by simpa using hj₂
      have hmin := mono_row0_min_ri M hM hmono j hj
      have hmn : entry M 0 0 < n := by omega
      simp only [List.getElem_map, List.getElem_range]
      rw [entry_bumpAt0 M n j hj, entry_bumpAt0 M n 0 hL,
        entry_bumpAt1 M n j]
      rw [bumpV_sub n (entry M 0 j) (entry M 0 0) hmin hmn]
      simp [bumpAt, List.getElem_map, List.getElem_range]

private theorem entry_coreReduce_zero_ri (M : PS) (j : ℕ)
    (hm : entry M 1 0 = 0) (hj : j < Lng M) :
    entry (coreReduce M) 0 j = entry M 0 j - entry M 0 0 := by
  exact entry_coreReduce_zero M j hm hj

private theorem cutOK_coreReduce_zero (M : PS) (n : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hm : entry M 1 0 = 0)
    (hcut : cutOK M n) (hmn : entry M 0 0 < n) :
    cutOK (coreReduce M) (n - entry M 0 0) := by
  have hc : 1 ≤ n ∧ ∀ j, TrMax M < j → j < Lng M →
      n ≤ entry M 0 j := by simpa [cutOK] using hcut
  constructor
  · omega
  · intro j hjtr hjL
    have hlen : Lng (coreReduce M) = Lng M := by simp [coreReduce, hm]
    have hjM : j < Lng M := by simpa [hlen] using hjL
    have htr := TrMax_coreReduce_zero M hM hmono hm
    have hge := hc.2 j (by omega) hjM
    rw [entry_coreReduce_zero_ri M j hm hjM]
    omega

private theorem nextR_IncrFirst_ri (M : PS) :
    nextR (IncrFirst M) = nextR M := by
  have heq : IncrFirst M = bumpAt M 0 := by
    simp [IncrFirst, bumpAt, bumpV]
  rw [heq, nextR_bumpAt]

theorem nextR_IncrFirstN_ri (k : ℕ) (M : PS) :
    nextR (IncrFirstN k M) = nextR M := by
  induction k generalizing M with
  | zero => rfl
  | succ k ih =>
      rw [IncrFirstN, ih, nextR_IncrFirst_ri]

theorem TrMax_coreReduce_pos_shift (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    entry M 1 0 + TrMax M ≤ TrMax (coreReduce M) := by
  let m := entry M 1 0
  have hm : entry M 1 0 ≠ 0 := by omega
  have hCT := coreReduce_TPS M hM
  apply le_TrMax_intro_wd (coreReduce M) (m + TrMax M) hCT
  intro j hj
  by_cases hjm : j < m
  · exact coreReduce_prefix_step M j hM hm (by simpa [m] using hjm)
  · let a := j - m
    have hma : m + a = j := by simp [a]; omega
    have ha : a < TrMax M := by dsimp [a]; omega
    have hstepM := TrMax_trunk_step M a hM ha
    have hstepR : nextR (IncrFirstN m M) 1 a (a + 1) = true := by
      rw [nextR_IncrFirstN_ri]
      exact hstepM
    have hdrop : (coreReduce M).drop m = IncrFirstN m M := by
      rw [coreReduce, if_neg hm]
      have hDlen : Lng (diagSeq 0 (entry M 1 0 - 1)) = m := by
        simp [diagSeq, m]
        omega
      simpa [hDlen, m]
    have hlenC : Lng (coreReduce M) = m + Lng M := by
      simp [coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
      omega
    have hbound := TrMax_bound M hM
    have haD : a < Lng (coreReduce M) - m := by
      rw [hlenC]
      omega
    have ha1D : a + 1 < Lng (coreReduce M) - m := by
      rw [hlenC]
      omega
    have hrel := nextR_drop (coreReduce M) m 1 a (a + 1) haD ha1D
    rw [hdrop] at hrel
    rw [hrel] at hstepR
    have hma1 : m + (a + 1) = j + 1 := by omega
    rw [hma, hma1] at hstepR
    exact hstepR

private theorem bumpV_shift (n m v : ℕ) :
    bumpV (n + m) (v + m) = bumpV n v + m := by
  simp only [bumpV]
  by_cases hv : v < n
  · have hs : v + m < n + m := by omega
    simp [hv, hs]
  · have hs : ¬v + m < n + m := by omega
    simp [hv, hs]
    omega

private theorem coreReduce_bumpAt_pos (M : PS) (n : ℕ)
    (hpos : 0 < entry M 1 0) :
    coreReduce (bumpAt M n) =
      bumpAt (coreReduce M) (n + entry M 1 0) := by
  have hm : entry M 1 0 ≠ 0 := by omega
  have hmA : entry (bumpAt M n) 1 0 = entry M 1 0 :=
    entry_bumpAt1 M n 0
  rw [coreReduce, if_neg (by simpa [hmA] using hm),
    coreReduce, if_neg hm, hmA]
  simp only [IncrFirstN_eq_map, bumpAt, List.map_append, List.map_map]
  congr 1
  · symm
    calc
      List.map (fun p => (bumpV (n + entry M 1 0) p.1, p.2))
          (diagSeq 0 (entry M 1 0 - 1)) =
          List.map id (diagSeq 0 (entry M 1 0 - 1)) := by
            apply List.map_congr_left
            intro p hp
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
            simp only [id_eq]
            have hjlt : j < n + entry M 1 0 := by
              simp at hj
              omega
            simp [bumpV, hjlt]
      _ = diagSeq 0 (entry M 1 0 - 1) := List.map_id _
  · apply List.map_congr_left
    intro p hp
    obtain ⟨a, b⟩ := p
    simp [bumpV_shift]

private theorem cutOK_coreReduce_pos (M : PS) (n : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0)
    (hcut : cutOK M n) :
    cutOK (coreReduce M) (n + entry M 1 0) := by
  have hc : 1 ≤ n ∧ ∀ j, TrMax M < j → j < Lng M →
      n ≤ entry M 0 j := by simpa [cutOK] using hcut
  constructor
  · omega
  · intro j hjtr hjL
    let m := entry M 1 0
    have hm : entry M 1 0 ≠ 0 := by omega
    have htr := TrMax_coreReduce_pos_shift M hM hmono hpos
    have hmj : m ≤ j := by omega
    have hlen : Lng (coreReduce M) = m + Lng M := by
      simp [coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
      omega
    have hjM : j - m < Lng M := by omega
    have hjtrM : TrMax M < j - m := by omega
    have hge := hc.2 (j - m) hjtrM hjM
    have hge' : n ≤ entry M 0 (j - entry M 1 0) := by
      simpa [m] using hge
    rw [entry_coreReduce_pos_tail_ri M j hpos hmj hjL]
    omega

theorem Red_bumpAt_of_cutOK_nonmulti (X : PS) (n : ℕ)
    (hX : TPS X) (hmulti : multiT X = false) (hcut : cutOK X n) :
    Red (bumpAt X n) = Red X := by
  generalize hk : nu X = k
  induction k using Nat.strong_induction_on generalizing X n with
  | h k ih =>
      let A := bumpAt X n
      have hA : TPS A := by
        simpa [TPS, A, bumpAt] using hX
      have hmultiA : multiT A = false := by simpa [A] using hmulti
      by_cases hz : zeroT X = true
      · have hzA : zeroT A = true := by simpa [A] using hz
        rw [Red_zero_branch X hz, Red_zero_branch A hzA]
      · have hmono : monoT X = true := by
          have hh := hmulti
          simp [multiT, hz] at hh
          exact hh
        have hmonoA : monoT A = true := by simpa [A] using hmono
        have hL : 0 < Lng X := List.length_pos_of_ne_nil hX
        have hA1 : entry A 1 0 = entry X 1 0 := by
          simpa [A] using entry_bumpAt1 X n 0
        have hA0 : entry A 0 0 = bumpV n (entry X 0 0) := by
          simpa [A] using entry_bumpAt0 X n 0 hL
        by_cases hcore : entry X 0 0 = 0 ∧ entry X 1 0 = 0
        · have hc : 1 ≤ n ∧ ∀ j, TrMax X < j → j < Lng X →
              n ≤ entry X 0 j := by simpa [cutOK] using hcut
          have hAcore : entry A 0 0 = 0 ∧ entry A 1 0 = 0 := by
            constructor
            · rw [hA0, hcore.1]
              simp [bumpV]
              omega
            · simpa [hA1] using hcore.2
          by_cases ht : TrMax X = Lng X - 1
          · have htA : TrMax A = Lng A - 1 := by
              simpa [A, TrMax_bumpAt] using ht
            rw [Red_core_trunk_ri A hA hmonoA hAcore htA,
              Red_core_trunk_ri X hX hmono hcore ht]
            simp [A, length_bumpAt]
          · have htA : TrMax A ≠ Lng A - 1 := by
              simpa [A, TrMax_bumpAt] using ht
            rw [Red_core_nontrunk_ri A hA hmonoA hAcore htA,
              Red_core_nontrunk_ri X hX hmono hcore ht]
            have htr : TrMax A = TrMax X := by simp [A, TrMax_bumpAt]
            rw [htr]
            congr 1
            have hBr := Br_bumpAt X n hX hcut
            have hRange : List.range (Br A).length = List.range (Br X).length := by
              simp [A, hBr]
            rw [hRange]
            apply List.flatMap_congr
            intro J hJmem
            have hJ : J < (Br X).length := List.mem_range.mp hJmem
            have hbT := Br_component_TPS X J hX hJ
            have hNJT : TPS (redNJ X J) := by
              apply List.ne_nil_of_length_pos
              change 0 < Lng (redNJ X J)
              rw [redNJ_length X J hbT]
              exact List.length_pos_of_ne_nil hbT
            have hNJmulti := redNJ_multi_false X J hX hmono hcore.1 hJ
            have hdesc := nu_redNJ_lt X J hX hmono hcore hJ
            have hcutNJ := cutOK_redNJ X J hX hmono hcore.1 hJ
            have hred := ih (nu (redNJ X J)) (by omega) (redNJ X J)
              ((Joints X).getD J 0 + 2) hNJT hNJmulti hcutNJ rfl
            have hNJrel := redNJ_bumpAt X n J hX hmono hcut hcore hJ
            have hE : branchE_ri A J = branchE_ri X J := by
              simp [branchE_ri, A, Joints_bumpAt X n hX hcut,
                branchNP_bumpAt X n J hX hcut hJ]
            rw [hE, hNJrel, hred]
        · have hAnoncore : ¬(entry A 0 0 = 0 ∧ entry A 1 0 = 0) := by
            intro ha
            have hx1 : entry X 1 0 = 0 := by omega
            have hx0 : entry X 0 0 ≠ 0 := by
              intro hx0
              exact hcore ⟨hx0, hx1⟩
            have hpos0 : 0 < entry X 0 0 := Nat.pos_of_ne_zero hx0
            have hbpos : 0 < bumpV n (entry X 0 0) := by
              simp only [bumpV]
              split <;> omega
            omega
          rw [Red_noncore_ri A hA hmonoA hAnoncore,
            Red_noncore_ri X hX hmono hcore, hA1]
          by_cases hm : entry X 1 0 = 0
          · simp only [if_pos hm]
            have hcrEq := coreReduce_bumpAt_zero X n hX hmono hm
            by_cases hn : n ≤ entry X 0 0
            · rw [hcrEq, if_pos hn]
            · have hmn : entry X 0 0 < n := by omega
              have hcrT := coreReduce_TPS X hX
              have hcrMulti := coreReduce_multi_false X hX hmono
              have hcutCr := cutOK_coreReduce_zero X n hX hmono hm hcut hmn
              have hdesc := nu_coreReduce_lt X hX hmono hcore
              have hred := ih (nu (coreReduce X)) (by omega) (coreReduce X)
                (n - entry X 0 0) hcrT hcrMulti hcutCr rfl
              rw [hcrEq, if_neg hn, hred]
          · have hpos : 0 < entry X 1 0 := by omega
            simp only [if_neg hm]
            have hcrEq := coreReduce_bumpAt_pos X n hpos
            have hcrT := coreReduce_TPS X hX
            have hcrMulti := coreReduce_multi_false X hX hmono
            have hcutCr := cutOK_coreReduce_pos X n hX hmono hpos hcut
            have hdesc := nu_coreReduce_lt X hX hmono hcore
            have hred := ih (nu (coreReduce X)) (by omega) (coreReduce X)
              (n + entry X 1 0) hcrT hcrMulti hcutCr rfl
            rw [hcrEq, hred]
            let N := Red (coreReduce X)
            let m := entry X 1 0
            let jN := Lng N - 1
            let S := seg N m jN
            have hg := monoT_Red_m10pos X hX hmono hpos
            have hST : TPS S := by simpa [N, m, jN, S] using hg.1
            have hmonoS : monoT S = true := by
              simpa [N, m, jN, S] using hg.2
            have hSpos := List.length_pos_of_ne_nil hST
            have hmj : m ≤ jN := by
              change 0 < Lng S at hSpos
              simp [S, seg] at hSpos
              omega
            simp [redPositiveOut_ri, hA1, N, m, jN, S, hmj, hmonoS]

theorem Red_coreReduce_IncrFirst (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    Red (coreReduce (IncrFirst M)) = Red (coreReduce M) := by
  have hEq := coreReduce_IncrFirst_bumpAt M hM hmono hpos
  have hCT := coreReduce_TPS M hM
  have hmulti := coreReduce_multi_false M hM hmono
  have hcut := cutOK_coreReduce M hM hmono hpos
  rw [hEq]
  exact Red_bumpAt_of_cutOK_nonmulti (coreReduce M) (entry M 1 0)
    hCT hmulti hcut

theorem Red_IncrFirst_positive (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    Red (IncrFirst M) = Red M := by
  have hIT := IncrFirst_TPS M hM
  have hmonoI : monoT (IncrFirst M) = true := by
    simpa [monoT_IncrFirst_ri] using hmono
  have hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by omega
  have hnoncoreI : ¬(entry (IncrFirst M) 0 0 = 0 ∧
      entry (IncrFirst M) 1 0 = 0) := by
    intro h
    have he1 := entry_IncrFirst1_ri M 0
    omega
  rw [Red_noncore_ri (IncrFirst M) hIT hmonoI hnoncoreI,
    Red_noncore_ri M hM hmono hnoncore]
  have hm : entry M 1 0 ≠ 0 := by omega
  have hmI : entry (IncrFirst M) 1 0 ≠ 0 := by
    rw [entry_IncrFirst1_ri]
    exact hm
  simp only [if_neg hmI, if_neg hm]
  rw [Red_coreReduce_IncrFirst M hM hmono hpos]
  let N := Red (coreReduce M)
  let m := entry M 1 0
  let jN := Lng N - 1
  let S := seg N m jN
  have hg := monoT_Red_m10pos M hM hmono hpos
  have hST : TPS S := by simpa [N, m, jN, S] using hg.1
  have hmonoS : monoT S = true := by
    simpa [N, m, jN, S] using hg.2
  have hSpos := List.length_pos_of_ne_nil hST
  have hmj : m ≤ jN := by
    change 0 < Lng S at hSpos
    simp [S, seg] at hSpos
    omega
  simp [redPositiveOut_ri, entry_IncrFirst1_ri, N, m, jN, S,
    hmj, hmonoS]

/-- §6.5 proposition: reduction is invariant under a uniform increment of
row zero. -/
theorem Red_IncrFirst (M : PS) (hM : TPS M) :
    Red (IncrFirst M) = Red M := by
  apply Red_IncrFirst_of_positive M hM
  intro X hXT hmono hpos
  exact Red_IncrFirst_positive X hXT hmono hpos

#print axioms Red_IncrFirst

end PSS

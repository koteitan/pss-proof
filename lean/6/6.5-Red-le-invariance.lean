import «6».«6.5-P-Red-equivariance»

/-!
# §6.5 系（直系先祖の `Red` 不変性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_le`
- 訂正: A4（原文の `TPS` 版は偽。`anchoredSlice` 上に制限）
- Isabelle: `m_6_5_Red_le_final`, `m_6_5_congR_self_Red_monoT`
- 依存: `6.5-Red-preserves-monoT`, `6.5-monoT-Red`, `PSS.Standard`
- 状態: 🚨 証明作業中
-/

namespace PSS

/-! ## Row-zero rebasing preserves the ancestor structure -/

/-- Uniformly subtract `c` and add `d` on row zero, leaving row one fixed. -/
def rebaseRow0 (c d : ℕ) (M : PS) : PS :=
  M.map (fun p => (p.1 - c + d, p.2))

@[simp] theorem length_rebaseRow0 (c d : ℕ) (M : PS) :
    Lng (rebaseRow0 c d M) = Lng M := by simp [rebaseRow0]

theorem entry_rebaseRow0_zero (c d : ℕ) (M : PS) (j : ℕ)
    (hj : j < Lng M) :
    entry (rebaseRow0 c d M) 0 j = entry M 0 j - c + d := by
  simp [rebaseRow0, entry, hj]

theorem entry_rebaseRow0_one (c d : ℕ) (M : PS) (j : ℕ) :
    entry (rebaseRow0 c d M) 1 j = entry M 1 j := by
  simp only [rebaseRow0, entry, List.getElem?_map]
  cases h : M[j]? <;> simp [h]

private theorem rebase_lt_iff (c d x y : ℕ) (hx : c ≤ x) (hy : c ≤ y) :
    x - c + d < y - c + d ↔ x < y := by omega

private theorem rebase_le_iff (c d x y : ℕ) (hx : c ≤ x) (hy : c ≤ y) :
    x - c + d ≤ y - c + d ↔ x ≤ y := by omega

theorem nextrel0_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    nextrel0 (rebaseRow0 c d M) = nextrel0 M := by
  funext a b
  by_cases ha : a < Lng M
  · by_cases hb : b < Lng M
    · simp only [nextrel0, length_rebaseRow0]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, List.mem_range]
      simp only [ha, hb, true_and]
      constructor
      · rintro ⟨⟨hab, hentry⟩, hall⟩
        refine ⟨⟨hab, ?_⟩, ?_⟩
        · rw [entry_rebaseRow0_zero c d M a ha,
            entry_rebaseRow0_zero c d M b hb] at hentry
          exact (rebase_lt_iff c d _ _ (hfloor a ha) (hfloor b hb)).mp hentry
        · intro j hj
          have hjL : j < Lng M := hj.trans hb
          have hh := hall j hj
          by_cases haj : a < j
          · simp only [haj, decide_true, Bool.not_true, Bool.false_or] at hh ⊢
            rw [entry_rebaseRow0_zero c d M b hb,
              entry_rebaseRow0_zero c d M j hjL] at hh
            exact decide_eq_true ((rebase_le_iff c d _ _
              (hfloor b hb) (hfloor j hjL)).mp (of_decide_eq_true hh))
          · simpa [haj]
      · rintro ⟨⟨hab, hentry⟩, hall⟩
        refine ⟨⟨hab, ?_⟩, ?_⟩
        · rw [entry_rebaseRow0_zero c d M a ha,
            entry_rebaseRow0_zero c d M b hb]
          exact (rebase_lt_iff c d _ _ (hfloor a ha) (hfloor b hb)).mpr hentry
        · intro j hj
          have hjL : j < Lng M := hj.trans hb
          have hh := hall j hj
          by_cases haj : a < j
          · simp only [haj, decide_true, Bool.not_true, Bool.false_or] at hh ⊢
            rw [entry_rebaseRow0_zero c d M b hb,
              entry_rebaseRow0_zero c d M j hjL]
            exact decide_eq_true ((rebase_le_iff c d _ _
              (hfloor b hb) (hfloor j hjL)).mpr (of_decide_eq_true hh))
          · simpa [haj]
    · simp [nextrel0, hb]
  · simp [nextrel0, ha]

private theorem le0Aux_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j)
    (fuel a b : ℕ) :
    le0Aux (rebaseRow0 c d M) fuel a b = le0Aux M fuel a b := by
  induction fuel generalizing b with
  | zero => rfl
  | succ fuel ih =>
      simp only [le0Aux, nextrel0_rebaseRow0 c d M hfloor, ih]

theorem le0_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    le0 (rebaseRow0 c d M) = le0 M := by
  funext a b
  simp [le0, le0Aux_rebaseRow0 c d M hfloor]

theorem nextrel1_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    nextrel1 (rebaseRow0 c d M) = nextrel1 M := by
  funext a b
  by_cases ha : a < Lng M
  · by_cases hb : b < Lng M
    · simp [nextrel1, ha, hb, entry_rebaseRow0_one,
        le0_rebaseRow0 c d M hfloor]
    · simp [nextrel1, hb]
  · simp [nextrel1, ha]

private theorem le1Aux_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j)
    (fuel a b : ℕ) :
    le1Aux (rebaseRow0 c d M) fuel a b = le1Aux M fuel a b := by
  induction fuel generalizing b with
  | zero => rfl
  | succ fuel ih =>
      simp only [le1Aux, nextrel1_rebaseRow0 c d M hfloor, ih]

theorem le1_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    le1 (rebaseRow0 c d M) = le1 M := by
  funext a b
  simp [le1, le1Aux_rebaseRow0 c d M hfloor]

theorem nextR_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    nextR (rebaseRow0 c d M) = nextR M := by
  funext i a b
  by_cases hi : i = 0
  · simp [nextR, hi, nextrel0_rebaseRow0 c d M hfloor]
  · simp [nextR, hi, nextrel1_rebaseRow0 c d M hfloor]

theorem leR_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    leR (rebaseRow0 c d M) = leR M := by
  funext i a b
  by_cases hi : i = 0
  · simp [leR, hi, le0_rebaseRow0 c d M hfloor]
  · simp [leR, hi, le1_rebaseRow0 c d M hfloor]

/-! ## Coefficient condition (A) on the trunk -/

theorem RedCondA_apply (M : PS) (hA : RedCondA M = true)
    (i j : ℕ) (hi : i < 2) (hj : j < Lng M)
    (hp : hasParent M i j = true) :
    entry M i (parent M i j) + 1 = entry M i j := by
  have hh := hA
  simp only [RedCondA, List.all_eq_true, List.mem_range] at hh
  have hh' := hh i hi j hj
  simp [hp] at hh'
  exact hh'

private theorem le0Aux_adjacent (M : PS) (fuel j : ℕ)
    (h : le0Aux M fuel j (j + 1) = true) :
    nextrel0 M j (j + 1) = true := by
  cases fuel with
  | zero => simp [le0Aux] at h
  | succ fuel =>
      have hne : (j == j + 1) = false := by simp
      simp only [le0Aux, hne, Bool.false_or, List.any_eq_true] at h
      rcases h with ⟨p, hpMem, hp⟩
      simp only [Bool.and_eq_true] at hp
      rcases hp with ⟨hpNext, hpAnc⟩
      have hpLt : p < j + 1 := List.mem_range.mp hpMem
      have hjp : j ≤ p := le0Aux_index_fseq hpAnc
      have : p = j := by omega
      simpa [this] using hpNext

theorem le0_adjacent (M : PS) (j : ℕ)
    (h : le0 M j (j + 1) = true) :
    nextrel0 M j (j + 1) = true := by
  have hh := h
  simp only [le0, Bool.and_eq_true] at hh
  exact le0Aux_adjacent M (Lng M) j hh.2

theorem trunk_entries_offset (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (j : ℕ) (hj : j ≤ TrMax M) :
    entry M 0 j = entry M 0 0 + j ∧
      entry M 1 j = entry M 1 0 + j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjtr : j < TrMax M := by omega
      have hstep1 := TrMax_trunk_step M j hM hjtr
      have hstep1' : nextrel1 M j (j + 1) = true := by
        simpa [nextR] using hstep1
      have hle0 : le0 M j (j + 1) = true := by
        have hh := hstep1'
        simp only [nextrel1, Bool.and_eq_true] at hh
        exact hh.1.2
      have hstep0' := le0_adjacent M j hle0
      have hstep0 : nextR M 0 j (j + 1) = true := by
        simpa [nextR] using hstep0'
      have hhas0 : hasParent M 0 (j + 1) = true :=
        (hasParent_iff_unique_fseq M 0 (j + 1)).mpr
          ⟨j, hstep0, fun q hq => row0_parent_unique M q j (j + 1) hq hstep0⟩
      have hpar0 : parent M 0 (j + 1) = j :=
        parent_eq_of_nextR0 M j (j + 1) hstep0
      have hhas1 : hasParent M 1 (j + 1) = true :=
        (hasParent_iff_unique_fseq M 1 (j + 1)).mpr
          ⟨j, hstep1, fun q hq => nextR1_unique_mr M q j (j + 1) hq hstep1⟩
      have hpar1 : parent M 1 (j + 1) = j :=
        parent_eq_of_unique_fseq M 1 (j + 1) j hstep1
          (fun q hq => nextR1_unique_mr M q j (j + 1) hq hstep1)
      have hjL : j + 1 < Lng M := by
        have ht := TrMax_bound M hM
        omega
      have hA0 := RedCondA_apply M hA 0 (j + 1) (by omega) hjL hhas0
      have hA1 := RedCondA_apply M hA 1 (j + 1) (by omega) hjL hhas1
      rw [hpar0] at hA0
      rw [hpar1] at hA1
      have hi := ih (by omega)
      constructor <;> omega

theorem core_trunk_eq_diag (M : PS) (hM : TPS M)
    (hA : RedCondA M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M = Lng M - 1) :
    M = diagSeq 0 (Lng M - 1) := by
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  apply List.ext_getElem
  · have hlen : Lng M - 1 + 1 = Lng M := by omega
    simp [diagSeq, hlen]
  · intro n hnM hnD
    have hnM' : n < Lng M := by simpa using hnM
    have hn : n ≤ TrMax M := by rw [ht]; omega
    have he := trunk_entries_offset M hM hA n hn
    rw [hcore.1, hcore.2] at he
    have hMn : M[n] = (n, n) := by
      apply Prod.ext
      · simpa [entry, List.getElem?_eq_getElem hnM] using he.1
      · simpa [entry, List.getElem?_eq_getElem hnM] using he.2
    rw [hMn]
    simp [diagSeq, List.getElem_map, List.getElem_range']

theorem Red_core_fixed_of_condA_trunk (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M = Lng M - 1) : Red M = M := by
  calc
    Red M = diagSeq 0 (Lng M - 1) :=
      Red_core_trunk_ri M hM hmono hcore ht
    _ = M := (core_trunk_eq_diag M hM hA hcore ht).symm

#print axioms leR_rebaseRow0
#print axioms trunk_entries_offset

end PSS

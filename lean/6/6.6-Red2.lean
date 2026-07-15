import «6».«6.5-Red-Pred-commute»
import «6».«6.5-Red-preserves-monoT»
import «6».«6.5-monoT-Red»
import «6».«6.6-Red-leftend»
import «6».«6.4-P-leftend-mono»

/-!
# RED2: two reductions reach a reduced pair sequence

This is Isabelle `y3r_RED2`, the missing A15 orbit bound.  The present file
first establishes invariant (D): every `P` component of `Red M` has a
diagonal left end.

- 状態: 🚧 invariant (D) と `P` のブロック再構成まで移植済み
-/

namespace PSS

/-- Reduction preserves nonemptiness. -/
theorem Red_TPS (M : PS) (hM : TPS M) : TPS (Red M) := by
  apply List.ne_nil_of_length_pos
  change 0 < Lng (Red M)
  rw [Lng_Red_invariance M hM]
  exact List.length_pos_of_ne_nil hM

/-- Reduction preserves non-multiness on all pair sequences. -/
theorem Red_preserves_nonmulti (M : PS) (hM : TPS M)
    (hnm : multiT M = false) : multiT (Red M) = false := by
  by_cases hz : zeroT M = true
  · have hzR := (Red_preserves_zeroT M hM).1 hz
    simp [multiT, hzR]
  · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
    have hmono : monoT M = true := by
      have hh := hnm
      simp [multiT, hz'] at hh
      exact hh
    have hmonoR := Red_preserves_monoT_forward M hM hmono
    simp [multiT, hmonoR]

/-- A reduced image of a non-multi block attains its row-zero minimum
strictly at the left end. -/
theorem Red_strict_leftmin_nonmulti (M : PS) (hM : TPS M)
    (hnm : multiT M = false) (r : ℕ)
    (hr0 : 0 < r) (hrL : r < Lng (Red M)) :
    entry (Red M) 0 0 < entry (Red M) 0 r := by
  have hRT : TPS (Red M) := Red_TPS M hM
  have hRnm : multiT (Red M) = false :=
    Red_preserves_nonmulti M hM hnm
  by_contra hnot
  have hle : entry (Red M) 0 r ≤ entry (Red M) 0 0 := by omega
  have hmin0 : ∀ k < Lng (Red M),
      entry (Red M) 0 0 ≤ entry (Red M) 0 k := by
    by_cases hz : zeroT M = true
    · have hzR := (Red_preserves_zeroT M hM).1 hz
      have hL : Lng (Red M) = 1 := by
        have hh := hzR
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
        exact hh.1
      omega
    · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
      have hmono : monoT M = true := by
        have hh := hnm
        simp [multiT, hz'] at hh
        exact hh
      exact Red_leftend_row0_min M hM hmono
  have hlmin : ∀ j, j < r →
      entry (Red M) 0 r ≤ entry (Red M) 0 j := by
    intro j hj
    exact hle.trans (hmin0 j (hj.trans hrL))
  have hstrict := (multi_criterion_12 (Red M) hRT).1 hRnm r hr0 hrL
  exact (not_lt_of_ge (hlmin 0 hr0)) hstrict

private theorem P_member_TPS_red2 (M Q : PS) (hM : TPS M)
    (hQ : Q ∈ P M) : TPS Q := by
  obtain ⟨J, hJ, hget⟩ := List.mem_iff_getElem.mp hQ
  have hpos := P_component_nonempty M J hM hJ
  have heq : (P M).getD J [] = Q := by
    rw [getD_eq_getElem_idx (P M) [] hJ]
    exact hget
  rw [heq] at hpos
  exact List.ne_nil_of_length_pos hpos

private theorem P_member_nonmulti_red2 (M Q : PS) (hM : TPS M)
    (hQ : Q ∈ P M) : multiT Q = false := by
  rcases P_components_nonmulti M hM Q hQ with hz | hmono
  · simp [multiT, hz]
  · simp [multiT, hmono]

/-- Adjacent block heads are non-increasing from left to right. -/
private def headNonincreasing : List PS → Prop
  | [] => True
  | _ :: [] => True
  | C :: D :: Rs =>
      entry D 0 0 ≤ entry C 0 0 ∧ headNonincreasing (D :: Rs)

/-- A concatenation of non-multi blocks with strict internal minima and
non-increasing heads is split by `P` at exactly the block boundaries. -/
theorem P_flatten_eq_of_strict_blocks (R : List PS)
    (hne : R ≠ [])
    (hT : ∀ C ∈ R, TPS C)
    (hnm : ∀ C ∈ R, multiT C = false)
    (hstrict : ∀ C ∈ R, ∀ r, 0 < r → r < Lng C →
      entry C 0 0 < entry C 0 r)
    (hheads : headNonincreasing R) :
    P R.flatten = R := by
  induction R with
  | nil => exact (hne rfl).elim
  | cons C Rs ih =>
      have hCT : TPS C := hT C (by simp)
      have hCnm : multiT C = false := hnm C (by simp)
      have hCpos : 0 < Lng C := List.length_pos_of_ne_nil hCT
      have hCstrict := hstrict C (by simp)
      cases Rs with
      | nil => simpa using P_nonmulti_eq C hCnm
      | cons D Ds =>
          let T := (D :: Ds).flatten
          let W := C ++ T
          have hDT : TPS D := hT D (by simp)
          have hDpos : 0 < Lng D := List.length_pos_of_ne_nil hDT
          have hTpos : 0 < Lng T := by simp [T, hDpos]
          have hWT : TPS W := by
            apply List.ne_nil_of_length_pos
            simp [W, hCpos]
          have hWlen : Lng W = Lng C + Lng T := by simp [W]
          have hcutpos : 0 < Lng C := hCpos
          have hcutlast : Lng C ≤ Lng W - 1 := by
            rw [hWlen]
            omega
          have hadj : entry D 0 0 ≤ entry C 0 0 := hheads.1
          have hlmin : ∀ j, j < Lng C →
              entry W 0 (Lng C) ≤ entry W 0 j := by
            intro j hj
            have hstep : entry C 0 0 ≤ entry C 0 j := by
              by_cases hj0 : j = 0
              · subst j
                exact le_rfl
              · exact (hCstrict j (Nat.pos_of_ne_zero hj0) hj).le
            calc
              entry W 0 (Lng C) = entry T 0 0 := by
                simpa [W] using entry_append_right_mr C T 0 (Lng C) (le_refl _)
              _ = entry D 0 0 := by
                simpa [T] using entry_append_left_mr D Ds.flatten 0 0 hDpos
              _ ≤ entry C 0 0 := hadj
              _ ≤ entry C 0 j := hstep
              _ = entry W 0 j := by
                symm
                simpa [W] using entry_append_left_mr C T 0 j hj
          have hsplit := P_additivity W (Lng C) hWT hcutpos hcutlast hlmin
          have hsegL : seg W 0 (Lng C - 1) = C := by
            rw [← take_eq_seg W (Lng C) hcutpos hcutlast]
            simp [W]
          have hsegR : seg W (Lng C) (Lng W - 1) = T := by
            rw [← drop_eq_seg W (Lng C) (by
              rw [hWlen]
              omega)]
            simp [W]
          have hTtail : ∀ E ∈ D :: Ds, TPS E := by
            intro E hE
            exact hT E (List.mem_cons_of_mem C hE)
          have hnmtail : ∀ E ∈ D :: Ds, multiT E = false := by
            intro E hE
            exact hnm E (List.mem_cons_of_mem C hE)
          have hstricttail : ∀ E ∈ D :: Ds, ∀ r, 0 < r → r < Lng E →
              entry E 0 0 < entry E 0 r := by
            intro E hE
            exact hstrict E (List.mem_cons_of_mem C hE)
          have hPtail : P T = D :: Ds := by
            simpa [T] using ih (by simp) hTtail hnmtail hstricttail hheads.2
          rw [show (C :: D :: Ds).flatten = W by simp [W, T]]
          rw [hsplit, hsegL, hsegR, P_nonmulti_eq C hCnm, hPtail]
          simp

/-- If every block has a diagonal head and a strict row-zero minimum there,
then every row-zero left-minimum of their concatenation is diagonal. -/
private theorem flatten_lmin_diag (R : List PS)
    (hT : ∀ C ∈ R, TPS C)
    (hdiag : ∀ C ∈ R, entry C 0 0 = entry C 1 0)
    (hstrict : ∀ C ∈ R, ∀ r, 0 < r → r < Lng C →
      entry C 0 0 < entry C 0 r)
    (p : ℕ) (hp : p < Lng R.flatten)
    (hlmin : ∀ j, j < p →
      entry R.flatten 0 p ≤ entry R.flatten 0 j) :
    entry R.flatten 0 p = entry R.flatten 1 p := by
  induction R generalizing p with
  | nil => simp at hp
  | cons C Rs ih =>
      have hflat : (C :: Rs).flatten = C ++ Rs.flatten := by simp
      rw [hflat] at hp hlmin ⊢
      have hCT : TPS C := hT C (by simp)
      have hCpos : 0 < Lng C := List.length_pos_of_ne_nil hCT
      have hCdiag : entry C 0 0 = entry C 1 0 := hdiag C (by simp)
      have hCstrict := hstrict C (by simp)
      by_cases hpC : p < Lng C
      · have hp0 : p = 0 := by
          by_contra hpne
          have hppos : 0 < p := Nat.pos_of_ne_zero hpne
          have hlt := hCstrict p hppos hpC
          have hle := hlmin 0 hppos
          rw [entry_append_left_mr C Rs.flatten 0 p hpC,
            entry_append_left_mr C Rs.flatten 0 0 hCpos] at hle
          omega
        subst p
        rw [entry_append_left_mr C Rs.flatten 0 0 hCpos,
          entry_append_left_mr C Rs.flatten 1 0 hCpos]
        exact hCdiag
      · have hpge : Lng C ≤ p := by omega
        let q := p - Lng C
        have hpEq : p = Lng C + q := by simp [q, hpge]
        have hqL : q < Lng Rs.flatten := by
          simp only [List.length_append] at hp
          change p - C.length < Rs.flatten.length
          change p < C.length + Rs.flatten.length at hp
          have hpge' : C.length ≤ p := hpge
          omega
        have hT' : ∀ D ∈ Rs, TPS D := by
          intro D hD
          exact hT D (List.mem_cons_of_mem C hD)
        have hdiag' : ∀ D ∈ Rs, entry D 0 0 = entry D 1 0 := by
          intro D hD
          exact hdiag D (List.mem_cons_of_mem C hD)
        have hstrict' : ∀ D ∈ Rs, ∀ r, 0 < r → r < Lng D →
            entry D 0 0 < entry D 0 r := by
          intro D hD
          exact hstrict D (List.mem_cons_of_mem C hD)
        have hlmin' : ∀ j, j < q →
            entry Rs.flatten 0 q ≤ entry Rs.flatten 0 j := by
          intro j hj
          have hcut : Lng C + j < p := by omega
          have hh := hlmin (Lng C + j) hcut
          rw [entry_append_right_mr C Rs.flatten 0 p hpge,
            entry_append_right_mr C Rs.flatten 0 (Lng C + j)
              (Nat.le_add_right _ _)] at hh
          simpa only [q, Nat.add_sub_cancel_left] using hh
        have hih := ih hT' hdiag' hstrict' q hqL hlmin'
        rw [entry_append_right_mr C Rs.flatten 0 p hpge,
          entry_append_right_mr C Rs.flatten 1 p hpge]
        simpa [q] using hih

private theorem P_component_head_entry (M : PS) (J i : ℕ) (hM : TPS M)
    (hJ : J < (P M).length) :
    entry ((P M).getD J []) i 0 =
      entry M i ((IdxSum (P M)).getD J 0) := by
  have hcomp := P_IdxSum M J hM (by omega)
  have hpos := P_component_nonempty M J hM hJ
  have hsegpos : 0 < Lng (seg M
      ((IdxSum (P M)).getD J 0)
      ((IdxSum (P M)).getD (J + 1) 0 - 1)) := by
    rw [← hcomp]
    exact hpos
  rw [hcomp]
  exact entry_seg M _ _ i 0 hsegpos

/-- Invariant (D): every `P` component of the first reduct has a diagonal
left end. -/
theorem Red_P_components_head_diag (M : PS) (hM : TPS M) :
    ∀ I, I < (P (Red M)).length →
      entry ((P (Red M)).getD I []) 0 0 =
        entry ((P (Red M)).getD I []) 1 0 := by
  let R := (P M).map Red
  have hX : Red M = R.flatten := by
    simpa [R] using Red_eq_flatMap_P M hM
  have hRT : TPS (Red M) := Red_TPS M hM
  have hT : ∀ C ∈ R, TPS C := by
    intro C hC
    rcases List.mem_map.mp hC with ⟨Q, hQ, rfl⟩
    exact Red_TPS Q (P_member_TPS_red2 M Q hM hQ)
  have hdiag : ∀ C ∈ R, entry C 0 0 = entry C 1 0 := by
    intro C hC
    rcases List.mem_map.mp hC with ⟨Q, hQ, rfl⟩
    exact Red_nonmulti_head_eq Q (P_member_TPS_red2 M Q hM hQ)
      (P_member_nonmulti_red2 M Q hM hQ)
  have hstrict : ∀ C ∈ R, ∀ r, 0 < r → r < Lng C →
      entry C 0 0 < entry C 0 r := by
    intro C hC
    rcases List.mem_map.mp hC with ⟨Q, hQ, rfl⟩
    exact Red_strict_leftmin_nonmulti Q (P_member_TPS_red2 M Q hM hQ)
      (P_member_nonmulti_red2 M Q hM hQ)
  intro I hI
  let s := (IdxSum (P (Red M))).getD I 0
  have hsmin := P_leftend_lmin (Red M) I hRT hI
  have hXpos : 0 < Lng (Red M) := List.length_pos_of_ne_nil hRT
  have hsL : s < Lng (Red M) := by
    dsimp [s]
    omega
  have hflat : entry R.flatten 0 s = entry R.flatten 1 s := by
    apply flatten_lmin_diag R hT hdiag hstrict s
    · simpa [← hX] using hsL
    · intro j hj
      simpa [← hX, s] using hsmin.2 j (by simpa [s] using hj)
  calc
    entry ((P (Red M)).getD I []) 0 0 = entry (Red M) 0 s := by
      simpa [s] using P_component_head_entry (Red M) I 0 hRT hI
    _ = entry R.flatten 0 s := by rw [hX]
    _ = entry R.flatten 1 s := hflat
    _ = entry (Red M) 1 s := by rw [hX]
    _ = entry ((P (Red M)).getD I []) 1 0 := by
      symm
      simpa [s] using P_component_head_entry (Red M) I 1 hRT hI

#print axioms Red_nonmulti_head_eq
#print axioms P_flatten_eq_of_strict_blocks
#print axioms Red_P_components_head_diag

end PSS

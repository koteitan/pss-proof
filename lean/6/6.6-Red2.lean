import «6».«6.5-Red-Pred-commute»
import «6».«6.5-Red-preserves-monoT»
import «6».«6.5-monoT-Red»
import «6».«6.6-Red-leftend»
import «6».«6.4-P-leftend-mono»
import «6».«6.6-one-column»

/-!
# RED2: two reductions reach a reduced pair sequence

This is Isabelle `y3r_RED2`, the missing A15 orbit bound.  The present file
first establishes invariant (D): every `P` component of `Red M` has a
diagonal left end.

- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- Reduction preserves nonemptiness. -/
theorem Red_TPS (M : PS) (hM : TPS M) : TPS (Red M) := by
  apply List.ne_nil_of_length_pos
  change 0 < Lng (Red M)
  rw [Lng_Red_invariance M hM]
  exact List.length_pos_of_ne_nil hM

private theorem Red_IncrFirstN (n : ℕ) (M : PS) (hM : TPS M) :
    Red (IncrFirstN n M) = Red M := by
  induction n generalizing M with
  | zero => rfl
  | succ n ih =>
      rw [IncrFirstN]
      have hI : TPS (IncrFirst M) := by
        simpa [TPS, IncrFirst] using hM
      rw [ih (IncrFirst M) hI, Red_IncrFirst M hM]

private theorem RTPS_of_fixed (M : PS) (hM : TPS M)
    (hfix : Red M = M) : RTPS M := by
  have hpair : M ≠ [] ∧ Red M = M := ⟨hM, hfix⟩
  simpa [RTPS, reduced] using hpair

/-- Every initial diagonal is reduced. -/
theorem RTPS_diagSeq_zero (n : ℕ) : RTPS (diagSeq 0 n) := by
  by_cases hn : n = 0
  · subst n
    have hT : TPS [(0, 0)] := by simp [TPS]
    exact ((one_column [(0, 0)] hT).2 ⟨0, rfl⟩).2
  · let S : PS := [(n, n)]
    have hST : TPS S := by simp [S, TPS]
    have hSR : RTPS S := ((one_column S hST).2 ⟨n, by simp [S]⟩).2
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hSmono : monoT S = true := by
      have hz : zeroT S = false := by simp [S, zeroT, entry, hn]
      simp [S, monoT, hz, leR, le0, le0Aux]
    have hpref := (RTPS_diag_prefix S 0 hSR hSmono (Nat.zero_le _)).1
    have hshape : diagSeq 0 (n - 1) ++ S = diagSeq 0 n := by
      dsimp [S]
      simp only [diagSeq, Nat.zero_add, Nat.sub_zero]
      have hn1 : n - 1 + 1 = n := by omega
      rw [hn1]
      calc
        List.map (fun j => (j, j)) (List.range' 0 n) ++ [(n, n)] =
            List.map (fun j => (j, j)) (List.range' 0 n ++ [n]) := by
              rw [List.map_append]
              rfl
        _ = List.map (fun j => (j, j)) (List.range' 0 (n + 1)) := by
          congr 1
          simpa using (show
            List.range' 0 n ++ List.range' n 1 = List.range' 0 (n + 1) by
              calc
                List.range' 0 n ++ List.range' n 1 =
                    List.range' 0 n ++ List.range' (0 + n) 1 := by simp
                _ = List.range' 0 (n + 1) := List.range'_append_1)
    have hpref' : RTPS (diagSeq 0 (n - 1) ++ S) := by
      simpa [S, hnpos, entry] using hpref
    rw [hshape] at hpref'
    exact hpref'

/-- A fixed guarded diagonal extension can be cancelled on the left. -/
theorem RTPS_of_diag_extension (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0)
    (hdom : entry M 1 0 ≤ entry M 0 0)
    (hR : RTPS (diagSeq 0 (entry M 1 0 - 1) ++ M)) :
    RTPS M := by
  let D := diagSeq 0 (entry M 1 0 - 1)
  have hfixD : Red (D ++ M) = D ++ M := by
    simpa [D] using RTPS_Red_eq (D ++ M) hR
  have hcomm : Red (D ++ M) = D ++ Red M := by
    simpa [D] using Red_diag_prefix M hM hmono hpos hdom
  have hcancel : D ++ Red M = D ++ M := hcomm.symm.trans hfixD
  exact RTPS_of_fixed M hM (List.append_cancel_left hcancel)

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

/-- All non-core branches of non-multi image reducedness follow from smaller
recursive images.  The remaining callback is precisely the core/non-trunk
branch. -/
private theorem Red_nonmulti_RTPS_from_core
    (coreCase : ∀ X : PS, TPS X → monoT X = true →
      entry X 0 0 = 0 ∧ entry X 1 0 = 0 →
      TrMax X ≠ Lng X - 1 →
      (∀ J, J < (Br X).length → RTPS (Red (redNJ X J))) →
      RTPS (Red X))
    (M : PS) (hM : TPS M) (hnm : multiT M = false) :
    RTPS (Red M) := by
  generalize hn : nu M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      by_cases hz : zeroT M = true
      · rw [Red_zero_mr M hz]
        have hT : TPS [(0, 0)] := by simp [TPS]
        exact ((one_column [(0, 0)] hT).2 ⟨0, rfl⟩).2
      · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
        have hmono : monoT M = true := by
          have hh := hnm
          simp [multiT, hz'] at hh
          exact hh
        by_cases hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0
        · by_cases ht : TrMax M = Lng M - 1
          · rw [Red_core_trunk_ri M hM hmono hcore ht]
            exact RTPS_diagSeq_zero (Lng M - 1)
          · apply coreCase M hM hmono hcore ht
            intro J hJ
            have hBT := Br_component_TPS M J hM hJ
            have hNJT : TPS (redNJ M J) := by
              apply List.ne_nil_of_length_pos
              change 0 < Lng (redNJ M J)
              rw [redNJ_length M J hBT]
              exact List.length_pos_of_ne_nil hBT
            have hNJnm := redNJ_multi_false M J hM hmono hcore.1 hJ
            have hdesc := nu_redNJ_lt M J hM hmono hcore hJ
            exact ih (nu (redNJ M J)) (by omega) (redNJ M J)
              hNJT hNJnm rfl
        · let C := coreReduce M
          have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
          have hCnm : multiT C = false := by
            simpa [C] using coreReduce_multi_false M hM hmono
          have hdesc := nu_coreReduce_lt M hM hmono hcore
          have hCR : RTPS (Red C) :=
            ih (nu C) (by rw [← hn]; simpa [C] using hdesc) C hCT hCnm rfl
          by_cases hm : entry M 1 0 = 0
          · have hred := Red_noncore_ri M hM hmono hcore
            have hred' : Red M = Red C := by simpa [C, hm] using hred
            rw [hred']
            exact hCR
          · have hmpos : 0 < entry M 1 0 := Nat.pos_of_ne_zero hm
            let R := Red M
            have hRT : TPS R := by simpa [R] using Red_TPS M hM
            have hRmono : monoT R = true := by
              simpa [R] using Red_preserves_monoT_forward M hM hmono
            have hRhead : entry R 0 0 = entry R 1 0 := by
              simpa [R] using Red_nonmulti_head_eq M hM hnm
            have hRpos : 0 < entry R 1 0 := by
              rw [show entry R 1 0 = entry M 1 0 by
                simpa [R] using Red_leftend_row1 M hM]
              exact hmpos
            have hdecomp := Red_coreReduce_eq_diag_Red M hM hmono hmpos
            have hExt : RTPS
                (diagSeq 0 (entry R 1 0 - 1) ++ R) := by
              have hCR' : RTPS (Red (coreReduce M)) := by simpa [C] using hCR
              rw [hdecomp] at hCR'
              simpa [R, Red_leftend_row1 M hM] using hCR'
            exact RTPS_of_diag_extension R hRT hRmono hRpos hRhead.ge hExt

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

private theorem headNonincreasing_of_adjacent (R : List PS)
    (h : ∀ I, I + 1 < R.length →
      entry (R.getD (I + 1) []) 0 0 ≤ entry (R.getD I []) 0 0) :
    headNonincreasing R := by
  induction R with
  | nil => trivial
  | cons C Rs ih =>
      cases Rs with
      | nil => trivial
      | cons D Ds =>
          constructor
          · simpa using h 0 (by simp)
          · apply ih
            intro I hI
            have hh := h (I + 1) (by simpa [Nat.add_assoc] using hI)
            simpa [Nat.add_assoc] using hh

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

private theorem Red_nonmulti_head_value (M : PS) (hM : TPS M)
    (hnm : multiT M = false) :
    entry (Red M) 0 0 = entry M 1 0 := by
  exact (Red_nonmulti_head_eq M hM hnm).trans (Red_leftend_row1 M hM)

private def red2BranchBlock (M : PS) (J : ℕ) : PS :=
  IncrFirstN (branchE M J) (Red (redNJ M J))

private def red2BranchBlocks (M : PS) : List PS :=
  (List.range (Br M).length).map (red2BranchBlock M)

private theorem red2BranchBlock_TPS (M : PS) (J : ℕ)
    (hM : TPS M) (hJ : J < (Br M).length) :
    TPS (red2BranchBlock M J) := by
  have hBT := Br_component_TPS M J hM hJ
  have hNJT : TPS (redNJ M J) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [redNJ_length M J hBT]
    exact List.length_pos_of_ne_nil hBT
  have hRT := Red_TPS (redNJ M J) hNJT
  simpa [red2BranchBlock, TPS, IncrFirstN_eq_map] using hRT

private theorem red2BranchBlock_nonmulti (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore0 : entry M 0 0 = 0) (hJ : J < (Br M).length) :
    multiT (red2BranchBlock M J) = false := by
  have hBT := Br_component_TPS M J hM hJ
  have hNJT : TPS (redNJ M J) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [redNJ_length M J hBT]
    exact List.length_pos_of_ne_nil hBT
  have hNJnm := redNJ_multi_false M J hM hmono hcore0 hJ
  rw [red2BranchBlock, multiT_IncrFirstN]
  exact Red_preserves_nonmulti (redNJ M J) hNJT hNJnm

private theorem red2BranchBlock_strict (M : PS) (J r : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore0 : entry M 0 0 = 0) (hJ : J < (Br M).length)
    (hr0 : 0 < r) (hrL : r < Lng (red2BranchBlock M J)) :
    entry (red2BranchBlock M J) 0 0 <
      entry (red2BranchBlock M J) 0 r := by
  have hBT := Br_component_TPS M J hM hJ
  have hNJT : TPS (redNJ M J) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [redNJ_length M J hBT]
    exact List.length_pos_of_ne_nil hBT
  have hNJnm := redNJ_multi_false M J hM hmono hcore0 hJ
  have hrL' : r < Lng (Red (redNJ M J)) := by
    simpa [red2BranchBlock, IncrFirstN_eq_map] using hrL
  have hzero : 0 < Lng (Red (redNJ M J)) :=
    List.length_pos_of_ne_nil (Red_TPS (redNJ M J) hNJT)
  have hs := Red_strict_leftmin_nonmulti (redNJ M J) hNJT hNJnm r hr0 hrL'
  rw [red2BranchBlock,
    entry_IncrFirstN_zero (branchE M J) (Red (redNJ M J)) 0 hzero,
    entry_IncrFirstN_zero (branchE M J) (Red (redNJ M J)) r hrL']
  omega

private theorem red2BranchBlock_head (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hJ : J < (Br M).length) :
    entry (red2BranchBlock M J) 0 0 = (Joints M).getD J 0 + 1 := by
  have hBT := Br_component_TPS M J hM hJ
  have hNJT : TPS (redNJ M J) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [redNJ_length M J hBT]
    exact List.length_pos_of_ne_nil hBT
  have hNJnm := redNJ_multi_false M J hM hmono hcore.1 hJ
  have hRpos : 0 < Lng (Red (redNJ M J)) :=
    List.length_pos_of_ne_nil (Red_TPS (redNJ M J) hNJT)
  have hnp : branchNP M J ≤ (Joints M).getD J 0 + 1 := by
    simpa [branchNP] using redNJ_np_le_joint M J hM hmono hcore.2 hJ
  rw [red2BranchBlock,
    entry_IncrFirstN_zero (branchE M J) (Red (redNJ M J)) 0 hRpos,
    Red_nonmulti_head_value (redNJ M J) hNJT hNJnm,
    redNJ_entry1_mr, hcore.2]
  simp only [Nat.zero_add, branchE]
  omega

private theorem red2BranchBlocks_getD (M : PS) (J : ℕ)
    (hJ : J < (Br M).length) :
    (red2BranchBlocks M).getD J [] = red2BranchBlock M J := by
  rw [getD_eq_getElem_idx (red2BranchBlocks M) [] (by
    simpa [red2BranchBlocks] using hJ)]
  simp [red2BranchBlocks, List.getElem_map, List.getElem_range']

private theorem red2BranchBlocks_nonempty (M : PS)
    (ht : TrMax M ≠ Lng M - 1) : red2BranchBlocks M ≠ [] := by
  have hBrne : Br M ≠ [] := by simp [Br, ht, P_nonempty]
  simpa [red2BranchBlocks] using hBrne

private theorem red2BranchBlocks_heads (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0) :
    headNonincreasing (red2BranchBlocks M) := by
  apply headNonincreasing_of_adjacent
  intro I hI
  have hS : I + 1 < (Br M).length := by
    simpa [red2BranchBlocks] using hI
  have hI' : I < (Br M).length := Nat.lt_of_succ_lt hS
  rw [red2BranchBlocks_getD M (I + 1) hS,
    red2BranchBlocks_getD M I hI',
    red2BranchBlock_head M (I + 1) hM hmono hcore hS,
    red2BranchBlock_head M I hM hmono hcore hI']
  have hj := (FirstNodes_Joints_mono M I (I + 1) hM hmono
    (by omega) hS).2.1
  omega

private theorem red2BranchBlocks_P (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M ≠ Lng M - 1) :
    P (red2BranchBlocks M).flatten = red2BranchBlocks M := by
  apply P_flatten_eq_of_strict_blocks
  · exact red2BranchBlocks_nonempty M ht
  · intro C hC
    rcases List.mem_map.mp hC with ⟨J, hJrange, rfl⟩
    exact red2BranchBlock_TPS M J hM (by simpa [red2BranchBlocks] using hJrange)
  · intro C hC
    rcases List.mem_map.mp hC with ⟨J, hJrange, rfl⟩
    exact red2BranchBlock_nonmulti M J hM hmono hcore.1
      (by simpa [red2BranchBlocks] using hJrange)
  · intro C hC r hr0 hrL
    rcases List.mem_map.mp hC with ⟨J, hJrange, rfl⟩
    exact red2BranchBlock_strict M J r hM hmono hcore.1
      (by simpa [red2BranchBlocks] using hJrange) hr0 hrL
  · exact red2BranchBlocks_heads M hM hmono hcore

private theorem Red_core_eq_diag_red2Blocks (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M ≠ Lng M - 1) :
    Red M = diagSeq 0 (TrMax M) ++ (red2BranchBlocks M).flatten := by
  simpa [red2BranchBlocks, red2BranchBlock] using
    Red_core_nontrunk_mr M hM hmono hcore ht

private theorem branchNP_zero_le_TrMax (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hcore1 : entry M 1 0 = 0)
    (ht : TrMax M ≠ Lng M - 1) :
    branchNP M 0 ≤ TrMax M := by
  have hBrne : Br M ≠ [] := by simp [Br, ht, P_nonempty]
  have hJ : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  by_cases hb : entry ((Br M).getD 0 []) 1 0 = 0
  · rw [branchNP, if_pos hb]
    omega
  · let f := (FirstNodes M).getD 0 0
    have hf : f = TrMax M + 1 := by
      dsimp [f]
      rw [FirstNodes_getD M 0 hJ]
      rw [idxSum_getD (Br M) 0 (Nat.zero_le _)]
      simp
    have htr := FirstNodes_TrMax_Joints M 0 hM hmono hJ
    have hnext0 := Joints_nextR_FirstNodes M 0 hM hmono hJ
    have hfL : f < Lng M := by
      have hn : nextrel0 M ((Joints M).getD 0 0)
          ((FirstNodes M).getD 0 0) = true := by
        simpa [nextR] using hnext0
      have hh := hn
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
      simpa [f] using hh.1.1.1.2
    have hfpos : 0 < f := by rw [hf]; omega
    have hef : entry M 1 f = entry ((Br M).getD 0 []) 1 0 := by
      simpa [f] using entry_FirstNodes_eq_component_mr M 0 1 hM hJ
    have he10 : entry M 1 0 < entry M 1 f := by rw [hcore1, hef]; omega
    have hfull : leR M 0 0 (Lng M - 1) = true := by
      have hh := hmono
      simp only [monoT, Bool.and_eq_true] at hh
      exact hh.2
    have h0f : leR M 0 0 f = true :=
      ancestor_tree_1 M 0 f (Lng M - 1) hM hfull (Nat.zero_le _) (by omega)
    obtain ⟨p, _, hpf, hpnext⟩ :=
      parent_exists_2 M 0 f hM hfpos hfL he10 h0f
    have hparent : parent M 1 f = p := by
      apply parent_eq_of_unique_fseq M 1 f p hpnext
      intro q hq
      exact nextR1_unique_mr M q p f hq hpnext
    have hpne : p ≠ TrMax M := by
      intro hp
      have hs : nextR M 1 (TrMax M) (TrMax M + 1) = true := by
        simpa [hp, hf] using hpnext
      rw [TrMax_stop_uncond M hM] at hs
      contradiction
    have hplt : p < TrMax M := by rw [hf] at hpf; omega
    rw [branchNP, if_neg hb, show parent M 1 ((FirstNodes M).getD 0 0) = p by
      simpa [f] using hparent]
    omega

private theorem nextR1_consecutive_red2 (M : PS) (j : ℕ)
    (hL : j + 1 < Lng M)
    (he0 : entry M 0 j < entry M 0 (j + 1))
    (he1 : entry M 1 j < entry M 1 (j + 1)) :
    nextR M 1 j (j + 1) = true := by
  have hn0 : nextR M 0 j (j + 1) = true := by
    simp only [nextR, if_pos]
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨by omega, hL⟩, by omega⟩, he0⟩, ?_⟩
    intro k hk
    by_cases hjk : j < k
    · have : k = j + 1 := by omega
      subst k
      simp
    · simp [hjk]
  have hle0 : le0 M j (j + 1) = true := by
    simpa [leR] using nextR0_leR M j (j + 1) hn0
  simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨by omega, hL⟩, by omega⟩, he1⟩, hle0⟩, ?_⟩
  intro k hk
  by_cases hjk : j < k
  · by_cases hle : le0 M k (j + 1) = true
    · have hkle := le0_index_fseq hle
      have : k = j + 1 := by omega
      subst k
      simp
    · simp [hjk, hle]
  · simp [hjk]

private theorem entry_flatten_head (R : List PS) (i : ℕ)
    (hne : R ≠ []) (hT : TPS (R.getD 0 [])) :
    entry R.flatten i 0 = entry (R.getD 0 []) i 0 := by
  cases R with
  | nil => contradiction
  | cons C Cs =>
      have hC : TPS C := by simpa using hT
      simpa using entry_append_left_mr C Cs.flatten i 0
        (List.length_pos_of_ne_nil hC)

private theorem cons_entries_tail (B : PS) (hB : TPS B) :
    (entry B 0 0, entry B 1 0) :: B.tail = B := by
  cases B with
  | nil => contradiction
  | cons b Bs => simp [entry]

private theorem red2BranchBlock_head_row1 (M : PS) (J : ℕ)
    (hM : TPS M) (hcore1 : entry M 1 0 = 0)
    (hJ : J < (Br M).length) :
    entry (red2BranchBlock M J) 1 0 = branchNP M J := by
  have hBT := Br_component_TPS M J hM hJ
  have hNJT : TPS (redNJ M J) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [redNJ_length M J hBT]
    exact List.length_pos_of_ne_nil hBT
  rw [red2BranchBlock, entry_IncrFirstN_one,
    Red_leftend_row1 (redNJ M J) hNJT, redNJ_entry1_mr, hcore1]
  simp

private theorem TrMax_Red_core_nontrunk (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M ≠ Lng M - 1) :
    TrMax (Red M) = TrMax M := by
  let R := Red M
  let t := TrMax M
  have hRT : TPS R := by simpa [R] using Red_TPS M hM
  have hlen : Lng R = Lng M := by simpa [R] using Lng_Red_invariance M hM
  have htbound := TrMax_bound M hM
  have htlt : t < Lng M - 1 := by simpa [t] using (lt_of_le_of_ne htbound ht)
  have htLower : t ≤ TrMax R := by
    apply le_TrMax_intro_wd R t hRT
    intro j hj
    have hjL : j + 1 < Lng R := by rw [hlen]; omega
    have he0j := Red_core_prefix_diag M hmono hcore 0 j (by
      change j ≤ TrMax M
      change j < TrMax M at hj
      omega)
    have he0s := Red_core_prefix_diag M hmono hcore 0 (j + 1) (by
      change j + 1 ≤ TrMax M
      change j < TrMax M at hj
      omega)
    have he1j := Red_core_prefix_diag M hmono hcore 1 j (by
      change j ≤ TrMax M
      change j < TrMax M at hj
      omega)
    have he1s := Red_core_prefix_diag M hmono hcore 1 (j + 1) (by
      change j + 1 ≤ TrMax M
      change j < TrMax M at hj
      omega)
    apply nextR1_consecutive_red2 R j hjL
    · simpa [R] using (show entry (Red M) 0 j < entry (Red M) 0 (j + 1) by
        rw [he0j, he0s]; omega)
    · simpa [R] using (show entry (Red M) 1 j < entry (Red M) 1 (j + 1) by
        rw [he1j, he1s]; omega)
  have hblocksNe := red2BranchBlocks_nonempty M ht
  have hJ0 : 0 < (Br M).length := by
    have : 0 < (red2BranchBlocks M).length :=
      List.length_pos_of_ne_nil hblocksNe
    simpa [red2BranchBlocks] using this
  have hB0T := red2BranchBlock_TPS M 0 hM hJ0
  have hshape := Red_core_eq_diag_red2Blocks M hM hmono hcore ht
  have hDlen : Lng (diagSeq 0 t) = t + 1 := by simp [diagSeq, t]
  have heTail : entry (red2BranchBlocks M).flatten 1 0 =
      entry (red2BranchBlock M 0) 1 0 := by
    calc
      entry (red2BranchBlocks M).flatten 1 0 =
          entry ((red2BranchBlocks M).getD 0 []) 1 0 :=
            entry_flatten_head (red2BranchBlocks M) 1 hblocksNe (by
              rw [red2BranchBlocks_getD M 0 hJ0]
              exact hB0T)
      _ = entry (red2BranchBlock M 0) 1 0 := by
        rw [red2BranchBlocks_getD M 0 hJ0]
  have heRsucc : entry R 1 (t + 1) = branchNP M 0 := by
    rw [show R = diagSeq 0 t ++ (red2BranchBlocks M).flatten by
      simpa [R, t] using hshape,
      entry_append_right_mr (diagSeq 0 t) (red2BranchBlocks M).flatten 1
        (t + 1) (by rw [hDlen]), hDlen]
    simpa [heTail] using red2BranchBlock_head_row1 M 0 hM hcore.2 hJ0
  have heRt : entry R 1 t = t := by
    simpa [R, t] using Red_core_prefix_diag M hmono hcore 1 (TrMax M)
      (le_refl _)
  have hnp := branchNP_zero_le_TrMax M hM hmono hcore.2 ht
  have hstop : nextR R 1 t (t + 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hs
    have hs1 : nextrel1 R t (t + 1) = true := by simpa [nextR] using hs
    have hh := hs1
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
    have hstrict := hh.1.1.2
    rw [heRt, heRsucc] at hstrict
    omega
  have htUpper : TrMax R ≤ t := by
    by_contra hnot
    have hs := TrMax_trunk_step R t hRT (by omega)
    rw [hstop] at hs
    contradiction
  exact Nat.le_antisymm htUpper htLower

private theorem Br_Red_core_nontrunk (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M ≠ Lng M - 1) :
    Br (Red M) = red2BranchBlocks M := by
  let R := Red M
  let t := TrMax M
  let Q := red2BranchBlocks M
  have hRT : TPS R := by simpa [R] using Red_TPS M hM
  have hlen : Lng R = Lng M := by simpa [R] using Lng_Red_invariance M hM
  have htr : TrMax R = t := by
    simpa [R, t] using TrMax_Red_core_nontrunk M hM hmono hcore ht
  have hneR : TrMax R ≠ Lng R - 1 := by
    rw [htr, hlen]
    exact ht
  have hshape : R = diagSeq 0 t ++ Q.flatten := by
    simpa [R, t, Q] using Red_core_eq_diag_red2Blocks M hM hmono hcore ht
  have hDlen : Lng (diagSeq 0 t) = t + 1 := by simp [diagSeq]
  have htlt : t + 1 < Lng R := by
    have hb := TrMax_bound M hM
    rw [hlen]
    omega
  have hseg : seg R (t + 1) (Lng R - 1) = Q.flatten := by
    rw [← drop_eq_seg R (t + 1) htlt, hshape]
    simp [hDlen]
  rw [Br, if_neg hneR, htr, hseg]
  exact red2BranchBlocks_P M hM hmono hcore ht

private theorem Joints_Red_core_nontrunk (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M ≠ Lng M - 1) (hJ : J < (Br M).length) :
    (Joints (Red M)).getD J 0 = (Joints M).getD J 0 := by
  let R := Red M
  let t := TrMax M
  let Q := red2BranchBlocks M
  let a := (Joints M).getD J 0
  let f := (FirstNodes R).getD J 0
  let s := (IdxSum Q).getD J 0
  have hRT : TPS R := by simpa [R] using Red_TPS M hM
  have hmonoR : monoT R = true := by
    simpa [R] using Red_preserves_monoT_forward M hM hmono
  have hlen : Lng R = Lng M := by
    simpa [R] using Lng_Red_invariance M hM
  have htr : TrMax R = t := by
    simpa [R, t] using TrMax_Red_core_nontrunk M hM hmono hcore ht
  have hBr : Br R = Q := by
    simpa [R, Q] using Br_Red_core_nontrunk M hM hmono hcore ht
  have hQlen : Q.length = (Br M).length := by simp [Q, red2BranchBlocks]
  have hJR : J < (Br R).length := by rw [hBr, hQlen]; exact hJ
  have hQJ : Q.getD J [] = red2BranchBlock M J := by
    simpa [Q] using red2BranchBlocks_getD M J hJ
  have hfn : f = t + 1 + s := by
    rw [show f = (FirstNodes R).getD J 0 by rfl,
      FirstNodes_getD R J hJR, htr, hBr]
  have hhead : entry R 0 f = a + 1 := by
    calc
      entry R 0 f = entry ((Br R).getD J []) 0 0 :=
        entry_FirstNodes_eq_component_mr R J 0 hRT hJR
      _ = entry (red2BranchBlock M J) 0 0 := by rw [hBr, hQJ]
      _ = a + 1 := by
        simpa [a] using red2BranchBlock_head M J hM hmono hcore hJ
  have haTr : a ≤ t := by
    simpa [a, t] using (FirstNodes_TrMax_Joints M J hM hmono hJ).1
  have htlt : t < Lng M - 1 := by
    have hb := TrMax_bound M hM
    simpa [t] using (lt_of_le_of_ne hb ht)
  have haL : a < Lng R := by rw [hlen]; omega
  have heA : entry R 0 a = a := by
    simpa [R, a, t] using Red_core_prefix_diag M hmono hcore 0 a haTr
  have hactual := Joints_nextR_FirstNodes R J hRT hmonoR hJR
  have hactual0 : nextrel0 R ((Joints R).getD J 0) f = true := by
    simpa [nextR, f] using hactual
  have hfL : f < Lng R := by
    have hh := hactual0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.1.2
  have haf : a < f := by
    have htf := (FirstNodes_TrMax_Joints R J hRT hmonoR hJR).2
    have htf' : t < f := by simpa [f, t, htr] using htf
    exact haTr.trans_lt htf'
  have hshape : R = diagSeq 0 t ++ Q.flatten := by
    simpa [R, t, Q] using Red_core_eq_diag_red2Blocks M hM hmono hcore ht
  have hDlen : Lng (diagSeq 0 t) = t + 1 := by simp [diagSeq]
  have hblockT : TPS (red2BranchBlock M J) :=
    red2BranchBlock_TPS M J hM hJ
  have hQmem : red2BranchBlock M J ∈ Q := by
    rw [← hQJ, getD_eq_getElem_idx Q [] (by simpa [hQlen] using hJ)]
    exact List.getElem_mem (by simpa [hQlen] using hJ)
  have htailT : TPS Q.flatten := by
    exact List.flatten_ne_nil_iff.mpr
      ⟨red2BranchBlock M J, hQmem, hblockT⟩
  have hPQ : P Q.flatten = Q := by
    simpa [Q] using red2BranchBlocks_P M hM hmono hcore ht
  have hleft := P_leftend_lmin Q.flatten J htailT (by
    rw [hPQ]
    simpa [hQlen] using hJ)
  rw [hPQ] at hleft
  have hnext : nextR R 0 a f = true := by
    change nextrel0 R a f = true
    rw [nextrel0, Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      constructor
      · rw [Bool.and_eq_true]
        constructor
        · rw [Bool.and_eq_true]
          exact ⟨by simpa using haL, by simpa using hfL⟩
        · simpa using haf
      · rw [heA, hhead]
        simp
    · rw [List.all_eq_true]
      intro k hk
      have hkf : k < f := List.mem_range.mp hk
      by_cases hak : a < k
      · have hle : entry R 0 f ≤ entry R 0 k := by
          by_cases hkt : k ≤ t
          · have heK : entry R 0 k = k := by
              simpa [R, t] using
                Red_core_prefix_diag M hmono hcore 0 k hkt
            rw [hhead, heK]
            omega
          · have htk : t + 1 ≤ k := by omega
            have hqLt : k - (t + 1) < s := by rw [hfn] at hkf; omega
            have hh := hleft.2 (k - (t + 1)) (by simpa [s] using hqLt)
            rw [hshape,
              entry_append_right_mr (diagSeq 0 t) Q.flatten 0 f (by
                rw [hDlen, hfn]; omega),
              entry_append_right_mr (diagSeq 0 t) Q.flatten 0 k (by
                rw [hDlen]; exact htk), hDlen, hfn]
            simpa only [Nat.add_sub_cancel_left] using hh
        simp [hak, hle]
      · simp [hak]
  have hp : parent R 0 f = a := parent_eq_of_nextR0 R a f hnext
  calc
    (Joints (Red M)).getD J 0 = (Joints R).getD J 0 := by rfl
    _ = parent R 0 f := by
      simpa [f] using Joints_getD R J hJR
    _ = a := hp
    _ = (Joints M).getD J 0 := by rfl

private theorem branchNP_Red_core_nontrunk (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M ≠ Lng M - 1) (hJ : J < (Br M).length) :
    branchNP (Red M) J = branchNP M J := by
  let R := Red M
  let Q := red2BranchBlocks M
  let a := (Joints M).getD J 0
  let f := (FirstNodes R).getD J 0
  let n := branchNP M J
  let p := n - 1
  have hRT : TPS R := by simpa [R] using Red_TPS M hM
  have hmonoR : monoT R = true := by
    simpa [R] using Red_preserves_monoT_forward M hM hmono
  have hlen : Lng R = Lng M := by
    simpa [R] using Lng_Red_invariance M hM
  have htr : TrMax R = TrMax M := by
    simpa [R] using TrMax_Red_core_nontrunk M hM hmono hcore ht
  have hBr : Br R = Q := by
    simpa [R, Q] using Br_Red_core_nontrunk M hM hmono hcore ht
  have hQlen : Q.length = (Br M).length := by simp [Q, red2BranchBlocks]
  have hJR : J < (Br R).length := by rw [hBr, hQlen]; exact hJ
  have hQJ : Q.getD J [] = red2BranchBlock M J := by
    simpa [Q] using red2BranchBlocks_getD M J hJ
  have hBrHead : entry ((Br R).getD J []) 1 0 = n := by
    rw [hBr, hQJ]
    simpa [n] using red2BranchBlock_head_row1 M J hM hcore.2 hJ
  have hhead : entry R 1 f = n := by
    calc
      entry R 1 f = entry ((Br R).getD J []) 1 0 :=
        entry_FirstNodes_eq_component_mr R J 1 hRT hJR
      _ = n := hBrHead
  by_cases hn : n = 0
  · change branchNP R J = n
    rw [branchNP, if_pos (hBrHead.trans hn)]
    exact hn.symm
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hpone : p + 1 = n := by simp [p]; omega
    have hnle : n ≤ a + 1 := by
      simpa [n, a, branchNP] using
        redNJ_np_le_joint M J hM hmono hcore.2 hJ
    have hpa : p ≤ a := by simp [p]; omega
    have haTr : a ≤ TrMax M := by
      simpa [a] using (FirstNodes_TrMax_Joints M J hM hmono hJ).1
    have hpTr : p ≤ TrMax M := hpa.trans haTr
    have hpL : p < Lng R := by
      rw [hlen]
      have hb := TrMax_bound M hM
      omega
    have heP : entry R 1 p = p := by
      simpa [R, p] using
        Red_core_prefix_diag M hmono hcore 1 p hpTr
    have hnext0 : nextR R 0 a f = true := by
      have hh := Joints_nextR_FirstNodes R J hRT hmonoR hJR
      rw [show (Joints R).getD J 0 = a by
        simpa [R, a] using
          Joints_Red_core_nontrunk M J hM hmono hcore ht hJ] at hh
      simpa [f] using hh
    have hnext0rel : nextrel0 R a f = true := by
      simpa [nextR] using hnext0
    have hfL : f < Lng R := by
      have hh := hnext0rel
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
      exact hh.1.1.1.2
    have haf : a < f := by
      have hh := (FirstNodes_TrMax_Joints R J hRT hmonoR hJR).2
      rw [htr] at hh
      simpa [f] using haTr.trans_lt hh
    have hpf : p < f := hpa.trans_lt haf
    have hpa0 : leR R 0 p a = true := by
      apply trunk_le0 R p a hRT hpa
      simpa [htr] using haTr
    have hp0fR : leR R 0 p f = true :=
      row0_transitive R p a f hRT hpa0 (nextR0_leR R a f hnext0)
    have hp0f : le0 R p f = true := by simpa [leR] using hp0fR
    have he1 : entry R 1 p < entry R 1 f := by
      rw [heP, hhead, ← hpone]
      omega
    have hnext1 : nextR R 1 p f = true := by
      simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
        Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range]
      refine ⟨⟨⟨⟨⟨hpL, hfL⟩, hpf⟩, he1⟩, hp0f⟩, ?_⟩
      intro k hk
      by_cases hc : p < k ∧ le0 R k f = true
      · have hkL : k < Lng R := by
          have hh := hc.2
          simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
          exact hh.1.1
        have hkf : k ≤ f := le0_index_fseq hc.2
        have hle : entry R 1 f ≤ entry R 1 k := by
          by_cases heq : k = f
          · subst k
            exact le_rfl
          · have hkflt : k < f := by omega
            have hk0fR : leR R 0 k f = true := by
              simpa [leR] using hc.2
            have he0 : entry R 0 k < entry R 0 f :=
              ancestor_basic_1 R k f f hRT hkflt (le_refl _) hk0fR
            have hka : k ≤ a :=
              nextR0_largest_below R a k f hnext0 hkflt he0
            have hkTr : k ≤ TrMax M := hka.trans haTr
            have heK : entry R 1 k = k := by
              simpa [R] using
                Red_core_prefix_diag M hmono hcore 1 k hkTr
            rw [hhead, heK, ← hpone]
            omega
        simp [hc, hle]
      · by_cases hpk : p < k
        · have hfalse : le0 R k f = false := by
            cases heq : le0 R k f with
            | false => rfl
            | true => exact False.elim (hc ⟨hpk, heq⟩)
          simp [hpk, hfalse]
        · simp [hpk]
    have hparent : parent R 1 f = p := by
      apply parent_eq_of_unique_fseq R 1 f p hnext1
      intro q hq
      exact nextR1_unique_mr R q p f hq hnext1
    change branchNP R J = n
    rw [branchNP, if_neg (by rw [hBrHead]; exact hn),
      show parent R 1 ((FirstNodes R).getD J 0) = p by
        simpa [f] using hparent, hpone]

private theorem redNJ_Red_core_nontrunk (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M ≠ Lng M - 1) (hJ : J < (Br M).length) :
    redNJ (Red M) J = red2BranchBlock M J := by
  let R := Red M
  let Q := red2BranchBlocks M
  let B := red2BranchBlock M J
  have hBr : Br R = Q := by
    simpa [R, Q] using Br_Red_core_nontrunk M hM hmono hcore ht
  have hQJ : Q.getD J [] = B := by
    simpa [Q, B] using red2BranchBlocks_getD M J hJ
  have hR0 : entry R 0 0 = 0 := by
    simpa [R] using Red_core_prefix_diag M hmono hcore 0 0
      (Nat.zero_le _)
  have hR1 : entry R 1 0 = 0 := by
    simpa [R] using Red_core_prefix_diag M hmono hcore 1 0
      (Nat.zero_le _)
  have hjoint : (Joints R).getD J 0 = (Joints M).getD J 0 := by
    simpa [R] using Joints_Red_core_nontrunk M J hM hmono hcore ht hJ
  have hnp : branchNP R J = branchNP M J := by
    simpa [R] using branchNP_Red_core_nontrunk M J hM hmono hcore ht hJ
  have hBT : TPS B := by
    simpa [B] using red2BranchBlock_TPS M J hM hJ
  change (entry R 0 0 + (Joints R).getD J 0 + 1,
      entry R 1 0 + branchNP R J) :: ((Br R).getD J []).tail = B
  rw [hR0, hR1, hjoint, hnp, hBr, hQJ]
  simp only [zero_add]
  rw [← red2BranchBlock_head M J hM hmono hcore hJ,
    ← red2BranchBlock_head_row1 M J hM hcore.2 hJ]
  exact cons_entries_tail B hBT

private theorem Red_core_nontrunk_RTPS (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M ≠ Lng M - 1)
    (hchildren : ∀ J, J < (Br M).length → RTPS (Red (redNJ M J))) :
    RTPS (Red M) := by
  let R := Red M
  let Q := red2BranchBlocks M
  have hRT : TPS R := by simpa [R] using Red_TPS M hM
  have hmonoR : monoT R = true := by
    simpa [R] using Red_preserves_monoT_forward M hM hmono
  have hlen : Lng R = Lng M := by
    simpa [R] using Lng_Red_invariance M hM
  have htr : TrMax R = TrMax M := by
    simpa [R] using TrMax_Red_core_nontrunk M hM hmono hcore ht
  have hBr : Br R = Q := by
    simpa [R, Q] using Br_Red_core_nontrunk M hM hmono hcore ht
  have hQlen : Q.length = (Br M).length := by simp [Q, red2BranchBlocks]
  have hcoreR : entry R 0 0 = 0 ∧ entry R 1 0 = 0 := by
    constructor
    · simpa [R] using Red_core_prefix_diag M hmono hcore 0 0
        (Nat.zero_le _)
    · simpa [R] using Red_core_prefix_diag M hmono hcore 1 0
        (Nat.zero_le _)
  have htR : TrMax R ≠ Lng R - 1 := by
    rw [htr, hlen]
    exact ht
  have hblocks : red2BranchBlocks R = Q := by
    apply List.ext_getElem
    · simp [red2BranchBlocks, hBr, hQlen]
    · intro J hJL hJRlen
      have hJ : J < (Br M).length := by
        simpa [Q, red2BranchBlocks] using hJRlen
      have hJR : J < (Br R).length := by
        rw [hBr, hQlen]
        exact hJ
      have hjoint : (Joints R).getD J 0 = (Joints M).getD J 0 := by
        simpa [R] using
          Joints_Red_core_nontrunk M J hM hmono hcore ht hJ
      have hnp : branchNP R J = branchNP M J := by
        simpa [R] using
          branchNP_Red_core_nontrunk M J hM hmono hcore ht hJ
      have he : branchE R J = branchE M J := by
        rw [branchE, branchE, hjoint, hnp]
      have hNJ : redNJ R J = red2BranchBlock M J := by
        simpa [R] using
          redNJ_Red_core_nontrunk M J hM hmono hcore ht hJ
      have hBT := Br_component_TPS M J hM hJ
      have hNJT : TPS (redNJ M J) := by
        apply List.ne_nil_of_length_pos
        change 0 < Lng (redNJ M J)
        rw [redNJ_length M J hBT]
        exact List.length_pos_of_ne_nil hBT
      have hredChild : Red (Red (redNJ M J)) = Red (redNJ M J) :=
        RTPS_Red_eq (Red (redNJ M J)) (hchildren J hJ)
      have hredNJ : Red (redNJ R J) = Red (redNJ M J) := by
        rw [hNJ]
        change Red (IncrFirstN (branchE M J) (Red (redNJ M J))) =
          Red (redNJ M J)
        rw [Red_IncrFirstN (branchE M J) (Red (redNJ M J))
          (Red_TPS (redNJ M J) hNJT), hredChild]
      rw [show (red2BranchBlocks R)[J] = red2BranchBlock R J by
        simp [red2BranchBlocks, List.getElem_map],
        show Q[J] = red2BranchBlock M J by
          simp [Q, red2BranchBlocks, List.getElem_map]]
      simp only [red2BranchBlock]
      rw [he, hredNJ]
  have hshape : R = diagSeq 0 (TrMax M) ++ Q.flatten := by
    simpa [R, Q] using Red_core_eq_diag_red2Blocks M hM hmono hcore ht
  have hfix : Red R = R := by
    calc
      Red R = diagSeq 0 (TrMax R) ++ (red2BranchBlocks R).flatten :=
        Red_core_eq_diag_red2Blocks R hRT hmonoR hcoreR htR
      _ = diagSeq 0 (TrMax M) ++ Q.flatten := by rw [htr, hblocks]
      _ = R := hshape.symm
  exact RTPS_of_fixed R hRT hfix

/-- Every non-multi pair sequence becomes reduced after one application of
`Red`. -/
theorem Red_nonmulti_RTPS (M : PS) (hM : TPS M)
    (hnm : multiT M = false) : RTPS (Red M) := by
  exact Red_nonmulti_RTPS_from_core
    (fun X hXT hmono hcore ht hchildren =>
      Red_core_nontrunk_RTPS X hXT hmono hcore ht hchildren)
    M hM hnm

private theorem Red_blocks_headNonincreasing (X : PS) (hX : TPS X)
    (hdiag : ∀ I, I < (P X).length →
      entry ((P X).getD I []) 0 0 = entry ((P X).getD I []) 1 0) :
    headNonincreasing ((P X).map Red) := by
  apply headNonincreasing_of_adjacent
  intro I hI
  have hI' : I < (P X).length := by simpa using (Nat.lt_of_succ_lt hI)
  have hS : I + 1 < (P X).length := by simpa using hI
  let Q := (P X).getD I []
  let S := (P X).getD (I + 1) []
  have hQT : TPS Q := by
    apply List.ne_nil_of_length_pos
    simpa [Q] using P_component_nonempty X I hX hI'
  have hST : TPS S := by
    apply List.ne_nil_of_length_pos
    simpa [S] using P_component_nonempty X (I + 1) hX hS
  have hQnm : multiT Q = false := by
    apply P_member_nonmulti_red2 X Q hX
    dsimp [Q]
    rw [getD_eq_getElem_idx (P X) [] hI']
    exact List.getElem_mem hI'
  have hSnm : multiT S = false := by
    apply P_member_nonmulti_red2 X S hX
    dsimp [S]
    rw [getD_eq_getElem_idx (P X) [] hS]
    exact List.getElem_mem hS
  have hmono := P_leftend_mono X I (I + 1) hX (by omega) (by omega)
  have hmapS : ((P X).map Red).getD (I + 1) [] = Red S := by
    dsimp [S]
    rw [getD_eq_getElem_idx ((P X).map Red) [] (by simpa using hS),
      getD_eq_getElem_idx (P X) [] hS]
    simp
  have hmapQ : ((P X).map Red).getD I [] = Red Q := by
    dsimp [Q]
    rw [getD_eq_getElem_idx ((P X).map Red) [] (by simpa using hI'),
      getD_eq_getElem_idx (P X) [] hI']
    simp
  rw [hmapS, hmapQ]
  calc
    entry (Red S) 0 0 = entry S 1 0 := Red_nonmulti_head_value S hST hSnm
    _ = entry S 0 0 := (hdiag (I + 1) hS).symm
    _ ≤ entry Q 0 0 := by simpa [Q, S] using hmono
    _ = entry Q 1 0 := hdiag I hI'
    _ = entry (Red Q) 0 0 := (Red_nonmulti_head_value Q hQT hQnm).symm

/-- Once reducedness of the individual non-multi images is available, the
diagonal-head invariant prevents the second reduction from merging blocks. -/
theorem Red_reduced_of_diag_of_blocks (X : PS) (hX : TPS X)
    (hdiag : ∀ I, I < (P X).length →
      entry ((P X).getD I []) 0 0 = entry ((P X).getD I []) 1 0)
    (hblockR : ∀ I, I < (P X).length →
      RTPS (Red ((P X).getD I []))) :
    RTPS (Red X) := by
  let R := (P X).map Red
  have hRne : R ≠ [] := by simp [R, P_nonempty X]
  have hRT : ∀ C ∈ R, TPS C := by
    intro C hC
    rcases List.mem_map.mp hC with ⟨Q, hQ, rfl⟩
    exact Red_TPS Q (P_member_TPS_red2 X Q hX hQ)
  have hRnm : ∀ C ∈ R, multiT C = false := by
    intro C hC
    rcases List.mem_map.mp hC with ⟨Q, hQ, rfl⟩
    exact Red_preserves_nonmulti Q (P_member_TPS_red2 X Q hX hQ)
      (P_member_nonmulti_red2 X Q hX hQ)
  have hRstrict : ∀ C ∈ R, ∀ r, 0 < r → r < Lng C →
      entry C 0 0 < entry C 0 r := by
    intro C hC
    rcases List.mem_map.mp hC with ⟨Q, hQ, rfl⟩
    exact Red_strict_leftmin_nonmulti Q (P_member_TPS_red2 X Q hX hQ)
      (P_member_nonmulti_red2 X Q hX hQ)
  have hRheads : headNonincreasing R := by
    simpa [R] using Red_blocks_headNonincreasing X hX hdiag
  have hPRflat : P R.flatten = R :=
    P_flatten_eq_of_strict_blocks R hRne hRT hRnm hRstrict hRheads
  have hred : Red X = R.flatten := by
    simpa [R] using Red_eq_flatMap_P X hX
  have hPred : P (Red X) = R := by rw [hred]; exact hPRflat
  apply (RTPS_iff_P_components (Red X) (Red_TPS X hX)).mpr
  intro J hJ
  have hJ' : J < (P X).length := by simpa [hPred, R] using hJ
  rw [hPred]
  have hmap : R.getD J [] = Red ((P X).getD J []) := by
    rw [getD_eq_getElem_idx R [] (by simpa [R] using hJ'),
      getD_eq_getElem_idx (P X) [] hJ']
    simp [R]
  rw [hmap]
  exact hblockR J hJ'

/-- A diagonal left end in every `P` component is sufficient for the first
reduct to be reduced. -/
theorem Red_reduced_of_diag (X : PS) (hX : TPS X)
    (hdiag : ∀ I, I < (P X).length →
      entry ((P X).getD I []) 0 0 = entry ((P X).getD I []) 1 0) :
    RTPS (Red X) := by
  apply Red_reduced_of_diag_of_blocks X hX hdiag
  intro I hI
  have hBT : TPS ((P X).getD I []) := by
    apply List.ne_nil_of_length_pos
    exact P_component_nonempty X I hX hI
  have hnm : multiT ((P X).getD I []) = false := by
    apply P_member_nonmulti_red2 X ((P X).getD I []) hX
    rw [getD_eq_getElem_idx (P X) [] hI]
    exact List.getElem_mem hI
  exact Red_nonmulti_RTPS ((P X).getD I []) hBT hnm

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

/-- RED2 (A15): two reductions suffice for every nonempty pair sequence. -/
theorem Red2 (M : PS) (hM : TPS M) : RTPS (Red (Red M)) := by
  exact Red_reduced_of_diag (Red M) (Red_TPS M hM)
    (Red_P_components_head_diag M hM)

#print axioms Red_nonmulti_head_eq
#print axioms P_flatten_eq_of_strict_blocks
#print axioms Red_P_components_head_diag
#print axioms Red_nonmulti_RTPS
#print axioms Red2

end PSS

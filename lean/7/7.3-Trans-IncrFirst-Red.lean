import «7».«7.3-Trans-welldefined»
import «6».«6.6-Red2»

/-!
# §7.3 命題（`Trans` の `(IncrFirst, Red)` 不変 `P` 同変性）

- 原文: `tmp/content.md` の同名命題
- 訂正: A15（`Red` 軌道が簡約形に達する域）、A16（先頭 `P` 成分は非零項）
- Isabelle: `m_7_3_Trans_Red`, `m_7_3_Trans_IncrFirst`,
  `m_7_3_Trans_P_equivariance`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem fuel_after_red_ge (M : PS) (hM : TPS M) :
    Lng (Red M) ≤ transFuel M - 1 := by
  have hmul : Lng M + 1 ≤ 8 * (nu M + 1) * (Lng M + 1) :=
    Nat.le_mul_of_pos_left (Lng M + 1) (by positivity)
  rw [Lng_Red_invariance M hM]
  simp only [transFuel]
  omega

private theorem fuel_after_red2_ge (M : PS) (hM : TPS M) :
    Lng (Red (Red M)) ≤ transFuel M - 2 := by
  have hRM : TPS (Red M) := Red_TPS M hM
  have hfactor : 2 ≤ 8 * (nu M + 1) := by
    calc
      2 ≤ 8 * 1 := by norm_num
      _ ≤ 8 * (nu M + 1) :=
        Nat.mul_le_mul_left 8 (Nat.succ_le_succ (Nat.zero_le (nu M)))
  have hmul : Lng M + 2 ≤ 8 * (nu M + 1) * (Lng M + 1) := by
    calc
      Lng M + 2 ≤ 2 * (Lng M + 1) := by omega
      _ ≤ (8 * (nu M + 1)) * (Lng M + 1) :=
        Nat.mul_le_mul_right (Lng M + 1) hfactor
  rw [Lng_Red_invariance (Red M) hRM, Lng_Red_invariance M hM]
  simp only [transFuel]
  omega

/-- One reduction step agrees with the public value when that reduct is
already reduced. -/
theorem Trans_Red_of_Red_reduced (M : PS) (hM : TPS M)
    (hRR : RTPS (Red M)) :
    Trans M = Trans (Red M) := by
  by_cases hR : RTPS M
  · rw [RTPS_Red_eq M hR]
  · have hred : reduced M = false := Bool.eq_false_of_not_eq_true hR
    calc
      Trans M = TransAux (transFuel M - 1) (Red M) := by
        rw [Trans, show transFuel M = (transFuel M - 1) + 1 by
          have : 0 < transFuel M := by simp [transFuel]
          omega]
        simp [TransAux, hred]
      _ = TransAux (transFuel (Red M)) (Red M) :=
        (TransAux_MarkAux_fuel_irrel_RTPS (Red M) hRR
          (transFuel M - 1) (transFuel (Red M))
          (fuel_after_red_ge M hM) (transFuel_ge_length (Red M))).1
      _ = Trans (Red M) := rfl

private theorem Trans_Red_of_Red2 (M : PS) (hM : TPS M)
    (hRR2 : RTPS (Red (Red M))) :
    Trans M = Trans (Red M) := by
  by_cases hRR : RTPS (Red M)
  · exact Trans_Red_of_Red_reduced M hM hRR
  · have hRM : TPS (Red M) := Red_TPS M hM
    have hredR : reduced (Red M) = false :=
      Bool.eq_false_of_not_eq_true hRR
    have hredM : reduced M = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hR
      have hfix : Red M = M := RTPS_Red_eq M hR
      exact hRR (by simpa [hfix] using hR)
    have hfuel : 2 ≤ transFuel M := by
      have hfactor : 2 ≤ 8 * (nu M + 1) := by
        calc
          2 ≤ 8 * 1 := by norm_num
          _ ≤ 8 * (nu M + 1) :=
            Nat.mul_le_mul_left 8 (Nat.succ_le_succ (Nat.zero_le (nu M)))
      calc
        2 ≤ 2 * (Lng M + 1) := by omega
        _ ≤ (8 * (nu M + 1)) * (Lng M + 1) :=
          Nat.mul_le_mul_right (Lng M + 1) hfactor
        _ ≤ transFuel M := by simp [transFuel]
    calc
      Trans M = TransAux (transFuel M - 2) (Red (Red M)) := by
        rw [Trans, show transFuel M = (transFuel M - 2) + 2 by omega]
        simp [TransAux, hredM, hredR]
      _ = TransAux (transFuel (Red (Red M))) (Red (Red M)) :=
        (TransAux_MarkAux_fuel_irrel_RTPS (Red (Red M)) hRR2
          (transFuel M - 2) (transFuel (Red (Red M)))
          (fuel_after_red2_ge M hM)
          (transFuel_ge_length (Red (Red M)))).1
      _ = Trans (Red (Red M)) := rfl
      _ = Trans (Red M) :=
        (Trans_Red_of_Red_reduced (Red M) hRM hRR2).symm

private theorem Trans_IncrFirst_of_Red2 (M : PS) (hM : TPS M)
    (hRR2 : RTPS (Red (Red M))) :
    Trans (IncrFirst M) = Trans M := by
  have hIT : TPS (IncrFirst M) := by
    simpa [TPS, IncrFirst] using hM
  have hRI : Red (IncrFirst M) = Red M := Red_IncrFirst M hM
  have hRRI2 : RTPS (Red (Red (IncrFirst M))) := by
    simpa [hRI] using hRR2
  calc
    Trans (IncrFirst M) = Trans (Red (IncrFirst M)) :=
      Trans_Red_of_Red2 (IncrFirst M) hIT hRRI2
    _ = Trans (Red M) := by rw [hRI]
    _ = Trans M := (Trans_Red_of_Red2 M hM hRR2).symm

/-- Reduction leaves `Trans` invariant on every pair sequence. -/
theorem Trans_Red (M : PS) (hM : TPS M) :
    Trans M = Trans (Red M) :=
  Trans_Red_of_Red2 M hM (Red2 M hM)

/-- Incrementing row zero leaves `Trans` invariant on every pair sequence. -/
theorem Trans_IncrFirst (M : PS) (hM : TPS M) :
    Trans (IncrFirst M) = Trans M :=
  Trans_IncrFirst_of_Red2 M hM (Red2 M hM)

/-- Part (1) of the corrected invariance proposition. -/
theorem Trans_IncrFirst_Red (M : PS) (hM : TPS M) :
    Trans M = Trans (Red M) ∧ Trans M = Trans (IncrFirst M) :=
  ⟨Trans_Red M hM, (Trans_IncrFirst M hM).symm⟩

/-- The contribution assigned to one principal component in corrected A16. -/
def transPComponent (J : PS) : BT :=
  if zeroT J then Dprin 0 BZero else Trans J

private theorem SigmaB_single (t : BT) : SigmaB [t] = t := by
  cases t
  simp [SigmaB, untrm]

private theorem SigmaB_append (xs ys : List BT) :
    SigmaB (xs ++ ys) = addBT (SigmaB xs) (SigmaB ys) := by
  simp [SigmaB, addBT, List.flatMap_append]

/-- Corrected A16: `Trans` is the Buchholz sum of the translations of the
`P` components, provided that the leading component is not the zero term.
Without this hypothesis the recursive base case absorbs the leading zero
component, so the unqualified formula from the source text is false. -/
theorem Trans_P_equivariance (M : PS) (hR : RTPS M)
    (hnz0 : zeroT ((P M).getD 0 []) = false) :
    Trans M = SigmaB ((P M).map transPComponent) := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      by_cases hmulti : multiT M = true
      · have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
        let A := M.take (Pcut M)
        let J := M.drop (Pcut M)
        have hAR : RTPS A := by
          simpa [A] using trans_multi_prefix_RTPS M hR hmulti
        have hcut := Pcut_props M hlen
        have hALen : Lng A = Pcut M := by
          simp [A, Nat.min_eq_left (by omega : Pcut M ≤ Lng M)]
        have hALt : Lng A < n := by
          rw [hALen, ← hn]
          omega
        have hPsplit : P M = P A ++ [J] := by
          simpa [A, J] using P_multi_step M hmulti hlen
        have hPAne : P A ≠ [] := P_nonempty A
        have hhead : (P A).getD 0 [] = (P M).getD 0 [] := by
          rw [hPsplit]
          cases hPA : P A with
          | nil => exact (hPAne hPA).elim
          | cons x xs => simp
        have hnzA : zeroT ((P A).getD 0 []) = false := by
          rw [hhead]
          exact hnz0
        have hIHA : Trans A = SigmaB ((P A).map transPComponent) :=
          ih (Lng A) hALt A hAR hnzA rfl
        have hlast := (trans_multi_last_component M hM hmulti).1
        have hPne : P M ≠ [] := P_nonempty M
        have hidx : (P M).length - 1 < (P M).length := by
          have := List.length_pos_of_ne_nil hPne
          omega
        have hpJR := (RTPS_iff_P_components M hM).1 hR
          ((P M).length - 1) hidx
        have hJR : RTPS J := by
          dsimp [J]
          rw [← hlast]
          exact hpJR
        have hJzero_iff : zeroT J = true ↔ J = [(0, 0)] := by
          constructor
          · intro hz
            have hh := hz
            simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
            obtain ⟨v, hv⟩ :=
              (one_column J (RTPS_TPS J hJR)).1 ⟨hh.1, hJR⟩
            have hv0 : v = 0 := by
              simpa [hv, entry] using hh.2
            simpa [hv0] using hv
          · intro hJ
            rw [hJ]
            simp [zeroT, entry]
        have heq := Trans_Mark_multi_equations M hR hmulti
        rw [hPsplit, List.map_append, SigmaB_append]
        simp only [List.map_singleton, SigmaB_single]
        rw [← hIHA]
        by_cases hJ0 : J = [(0, 0)]
        · have hz : zeroT J = true := hJzero_iff.2 hJ0
          simpa [transPComponent, A, J, hJ0, hz] using heq.1
        · have hz : zeroT J = false := by
            apply Bool.eq_false_of_not_eq_true
            exact fun hzt => hJ0 (hJzero_iff.1 hzt)
          simpa [transPComponent, A, J, hJ0, hz] using heq.1
      · have hmulti' : multiT M = false :=
          Bool.eq_false_of_not_eq_true hmulti
        have hP : P M = [M] := P_nonmulti_eq M hmulti'
        have hnzM : zeroT M = false := by
          simpa [hP] using hnz0
        simp [hP, transPComponent, hnzM, SigmaB_single]

#print axioms Trans_Red
#print axioms Trans_Red_of_Red_reduced
#print axioms Trans_IncrFirst
#print axioms Trans_IncrFirst_Red
#print axioms Trans_P_equivariance

end PSS

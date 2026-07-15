import «6».«6.5-Red-Pred-commute»
import «6».«6.6-P-preserves-reduced»
import «6».«6.6-reduced-leftend»
import PSS.Trans

/-!
# §7.3 命題（`Trans` の well-defined 性）

- 原文: `tmp/content.md` の「命題（`Trans` の well-defined 性）」
- 訂正: A15（停止性・値域の証明域は `RTPS`）
- Isabelle: `Pred_RT_PS`, `trans_multiT_prefix_RT_PS`,
  `trans_multiT_last_component`, `Trans_Mark_invariant_aux`
- 状態: 🚧 証明中
-/

namespace PSS

/-- In the multi branch, the prefix left after removing the final principal
component is again a reduced pair sequence. -/
theorem trans_multi_prefix_RTPS (M : PS) (hR : RTPS M)
    (hmulti : multiT M = true) : RTPS (M.take (Pcut M)) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
  have hcut := Pcut_props M hlen
  have htakeT : TPS (M.take (Pcut M)) := by
    have htakeLen : Lng (M.take (Pcut M)) = Pcut M := by
      simp [Nat.min_eq_left (by omega : Pcut M ≤ Lng M)]
    exact List.ne_nil_of_length_pos (by simpa [htakeLen] using hcut.1)
  apply (RTPS_iff_P_components (M.take (Pcut M)) htakeT).2
  intro J hJ
  have hblocks : (P M).dropLast = P (M.take (Pcut M)) :=
    (P_last_multi M hmulti hlen).2
  have hJdrop : J < (P M).dropLast.length := by simpa [hblocks] using hJ
  have hJfull : J < (P M).length := by
    have hPne : P M ≠ [] := P_nonempty M
    simp only [List.length_dropLast] at hJdrop
    omega
  have hcomp := (RTPS_iff_P_components M hM).1 hR J hJfull
  have hget : ((P M).dropLast).getD J [] = (P M).getD J [] := by
    rw [getD_eq_getElem_idx ((P M).dropLast) [] hJdrop,
      getD_eq_getElem_idx (P M) [] hJfull]
    simp only [List.getElem_dropLast]
  rw [← hblocks]
  exact hget ▸ hcomp

private theorem getLastD_eq_getD_last_tw {α : Type} (Q : List α) (d : α)
    (hQ : Q ≠ []) : Q.getLastD d = Q.getD (Q.length - 1) d := by
  cases h : Q with
  | nil => exact (hQ h).elim
  | cons x xs =>
      simp [List.getLastD, List.getD, List.getLast_eq_getElem]

/-- The last `P` component in the multi branch is exactly the suffix beginning
at `Pcut M`; consequently the local index `j₀` used by `TransAux` is `Pcut M`. -/
theorem trans_multi_last_component (M : PS) (hM : TPS M)
    (hmulti : multiT M = true) :
    (P M).getD ((P M).length - 1) [] = M.drop (Pcut M) ∧
      Lng M - 1 - Lng ((P M).getD ((P M).length - 1) []) + 1 = Pcut M := by
  have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
  have hcut := Pcut_props M hlen
  have hPne : P M ≠ [] := P_nonempty M
  have hlast : (P M).getD ((P M).length - 1) [] = M.drop (Pcut M) := by
    rw [← getLastD_eq_getD_last_tw (P M) [] hPne]
    exact (P_last_multi M hmulti hlen).1
  refine ⟨hlast, ?_⟩
  have hdropLen : Lng (M.drop (Pcut M)) = Lng M - Pcut M := by simp
  rw [hlast, hdropLen]
  omega

/-- The prefix expression occurring literally in `TransAux`'s multi branch is
the prefix ending just before `Pcut M`. -/
theorem trans_multi_prefix_seg (M : PS) (hM : TPS M)
    (hmulti : multiT M = true) :
    let pJ := (P M).getD ((P M).length - 1) []
    let j₀ := Lng M - 1 - Lng pJ + 1
    seg M 0 (j₀ - 1) = M.take (Pcut M) := by
  dsimp only
  have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
  have hcut := Pcut_props M hlen
  have hj₀ := (trans_multi_last_component M hM hmulti).2
  rw [hj₀]
  exact (take_eq_seg M (Pcut M) hcut.1 hcut.2.1).symm

/-- On reduced inputs, every recursive call strictly shortens the pair
sequence.  Hence two fuel values at least `Lng M` compute identical `TransAux`
and `MarkAux` values.  This is the total Lean counterpart of the domain part
of Isabelle's `Trans_Mark_invariant_aux`. -/
theorem TransAux_MarkAux_fuel_irrel_RTPS (M : PS) (hR : RTPS M)
    (fuel₁ fuel₂ : ℕ) (hf₁ : Lng M ≤ fuel₁) (hf₂ : Lng M ≤ fuel₂) :
    TransAux fuel₁ M = TransAux fuel₂ M ∧
      ∀ m, MarkAux fuel₁ M m = MarkAux fuel₂ M m := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M fuel₁ fuel₂ with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      have hred : reduced M = true := hR
      cases fuel₁ with
      | zero => omega
      | succ fuel₁ =>
          cases fuel₂ with
          | zero => omega
          | succ fuel₂ =>
              by_cases hlast : Lng M - 1 = 0
              · constructor
                · simp [TransAux, lastIdx, hred, hlast]
                · intro m
                  simp [MarkAux, lastIdx, hred, hlast]
              · have hlen : 1 < Lng M := by omega
                by_cases hmono : monoT M = true
                · have hPR : RTPS (Pred M) := RTPS_Pred M hR
                  have hPL : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
                  have hrec := ih (Lng (Pred M)) (by omega) (Pred M) hPR
                    fuel₁ fuel₂ (by omega) (by omega) rfl
                  by_cases ht : TransAux fuel₁ (Pred M) = BZero
                  · have ht₂ : TransAux fuel₂ (Pred M) = BZero :=
                      hrec.1.symm.trans ht
                    constructor
                    · simp [TransAux, lastIdx, hred, hlast, hmono,
                        ht, ht₂]
                    · intro m
                      simp [MarkAux, lastIdx, hred, hlast, hmono,
                        ht, ht₂]
                  · have ht₂ : TransAux fuel₂ (Pred M) ≠ BZero := by
                      intro heq
                      exact ht (hrec.1.trans heq)
                    constructor
                    · simp [TransAux, lastIdx, hred, hlast, hmono,
                        ht₂, hrec.1, hrec.2]
                    · intro m
                      simp [MarkAux, lastIdx, hred, hlast, hmono,
                        ht₂, hrec.1, hrec.2]
                · have hzero : zeroT M = false := by
                    simp [zeroT]
                    omega
                  have hmulti : multiT M = true := by
                    simp [multiT, hzero, hmono]
                  have hcut := Pcut_props M hlen
                  let pJ := (P M).getD ((P M).length - 1) []
                  have hlastComp := trans_multi_last_component M hM hmulti
                  have hpJeq : pJ = M.drop (Pcut M) := by
                    simpa [pJ] using hlastComp.1
                  have hPne : P M ≠ [] := P_nonempty M
                  have hJ : (P M).length - 1 < (P M).length := by
                    have := List.length_pos_of_ne_nil hPne
                    omega
                  have hpJR : RTPS pJ := by
                    simpa [pJ] using
                      (RTPS_iff_P_components M hM).1 hR
                        ((P M).length - 1) hJ
                  have hpJL : Lng pJ < Lng M := by
                    calc
                      Lng pJ = Lng M - Pcut M := by rw [hpJeq]; simp
                      _ < Lng M := by omega
                  have hpJrec := ih (Lng pJ) (by omega) pJ hpJR
                    fuel₁ fuel₂ (by omega) (by omega) rfl
                  let A := M.take (Pcut M)
                  have hAR : RTPS A := by
                    simpa [A] using trans_multi_prefix_RTPS M hR hmulti
                  have hAL : Lng A < Lng M := by
                    simp [A, Nat.min_eq_left (by omega : Pcut M ≤ Lng M)]
                    omega
                  have hArec := ih (Lng A) (by omega) A hAR
                    fuel₁ fuel₂ (by omega) (by omega) rfl
                  have hend :
                      Lng M - 1 - Lng
                          ((P M).getD ((P M).length - 1) []) =
                        Pcut M - 1 := by
                    omega
                  have hseg :
                      seg M 0
                        (Lng M - 1 - Lng
                          ((P M).getD ((P M).length - 1) [])) = A := by
                    rw [hend]
                    simpa [A] using
                      (take_eq_seg M (Pcut M) hcut.1 hcut.2.1).symm
                  have hsegRec :
                      TransAux fuel₁
                          (seg M 0
                            (Lng M - 1 - Lng
                              ((P M).getD ((P M).length - 1) []))) =
                        TransAux fuel₂
                          (seg M 0
                            (Lng M - 1 - Lng
                              ((P M).getD ((P M).length - 1) []))) := by
                    rw [hseg]
                    exact hArec.1
                  have hpJTrec :
                      TransAux fuel₁
                          ((P M).getD ((P M).length - 1) []) =
                        TransAux fuel₂
                          ((P M).getD ((P M).length - 1) []) := by
                    simpa [pJ] using hpJrec.1
                  have hpJMrec : ∀ m,
                      MarkAux fuel₁
                          ((P M).getD ((P M).length - 1) []) m =
                        MarkAux fuel₂
                          ((P M).getD ((P M).length - 1) []) m := by
                    simpa [pJ] using hpJrec.2
                  simp only [List.getD_eq_getElem?_getD] at hsegRec hpJTrec hpJMrec
                  by_cases hpJzero :
                      (P M).getD ((P M).length - 1) [] = [(0, 0)]
                  · simp only [List.getD_eq_getElem?_getD] at hpJzero
                    have hsegRecZero :
                        TransAux fuel₁ (seg M 0 (Lng M - 1 - 1)) =
                          TransAux fuel₂ (seg M 0 (Lng M - 1 - 1)) := by
                      simpa [hpJzero] using hsegRec
                    constructor
                    ·
                      simp [TransAux, lastIdx, hred, hlast, hmono,
                        hpJzero, hsegRecZero]
                    · intro m
                      simp [MarkAux, lastIdx, hred, hlast, hmono, hpJzero]
                  · constructor
                    · simp only [List.getD_eq_getElem?_getD] at hpJzero
                      simp [TransAux, lastIdx, hred, hlast, hmono,
                        hpJzero, hsegRec, hpJTrec]
                    · intro m
                      simp only [List.getD_eq_getElem?_getD] at hpJzero
                      simp [MarkAux, lastIdx, hred, hlast, hmono,
                        hpJzero, hpJMrec]

/-- The conservative public fuel bound is in particular at least the input
length. -/
theorem transFuel_ge_length (M : PS) : Lng M ≤ transFuel M := by
  have hfactor : 1 ≤ 8 * (nu M + 1) := by omega
  calc
    Lng M ≤ 1 * (Lng M + 1) := by omega
    _ ≤ (8 * (nu M + 1)) * (Lng M + 1) :=
      Nat.mul_le_mul_right (Lng M + 1) hfactor
    _ ≤ (8 * (nu M + 1)) * (Lng M + 1) + 8 := by omega
    _ = transFuel M := by simp [transFuel, Nat.mul_assoc]

/-- On a reduced input, the public translation is already determined by the
minimal length fuel. -/
theorem Trans_eq_lengthAux (M : PS) (hR : RTPS M) :
    Trans M = TransAux (Lng M) M := by
  exact (TransAux_MarkAux_fuel_irrel_RTPS M hR
    (transFuel M) (Lng M) (transFuel_ge_length M) (le_refl _)).1

/-- The analogous minimal-fuel equation for every marked translation. -/
theorem Mark_eq_lengthAux (M : PS) (m : ℕ) (hR : RTPS M) :
    Mark M m = MarkAux (Lng M) M m := by
  exact (TransAux_MarkAux_fuel_irrel_RTPS M hR
    (transFuel M) (Lng M) (transFuel_ge_length M) (le_refl _)).2 m

#print axioms TransAux_MarkAux_fuel_irrel_RTPS
#print axioms Trans_eq_lengthAux
#print axioms Mark_eq_lengthAux

#print axioms trans_multi_prefix_RTPS
#print axioms trans_multi_last_component
#print axioms trans_multi_prefix_seg

end PSS

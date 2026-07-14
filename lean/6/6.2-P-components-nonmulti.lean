import PSS.Mono
import «6».«6.2-mono-ancestor-slice»

/-!
# §6.2 命題（`P` の各成分の非複項性）

- 原文: `isabelle/pss_paper.thy` の `p_6_2_P_components_1`, `_2`
- 訂正: なし
- Isabelle: `m_6_2_P_components_1`, `_2`
- 依存: `PSS.Mono`, `6.2-mono-ancestor-slice`
- 状態: ✅ 証明済み
-/

namespace PSS

private theorem le0Aux_refl (M : PS) (fuel j : ℕ) :
    le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

private theorem multi_length_gt_one (M : PS) (hM : TPS M)
    (hm : multiT M = true) : 1 < Lng M := by
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  by_contra h
  have hlen : Lng M = 1 := by omega
  simp [multiT, monoT, zeroT, hlen, leR, le0, le0Aux] at hm

private theorem pcut_spec (M : PS) (hlen : 1 < Lng M) :
    0 < Pcut M ∧ Pcut M ≤ Lng M - 1 ∧
      leR M 0 (Pcut M) (Lng M - 1) = true := by
  let q : ℕ → Bool := fun j =>
    (0 < j) && (j ≤ Lng M - 1) && leR M 0 j (Lng M - 1)
  have hlast_mem : Lng M - 1 ∈ List.range (Lng M) := by
    simp
    omega
  have hlast : q (Lng M - 1) = true := by
    have hp : 0 < Lng M - 1 := by omega
    have hi : Lng M - 1 < Lng M := by omega
    have hr : leR M 0 (Lng M - 1) (Lng M - 1) = true := by
      simp [leR, le0, hi, le0Aux_refl]
    simp [q, hp, hr]
  have hsome : ∃ c, (List.range (Lng M)).find? q = some c := by
    cases hfind : (List.range (Lng M)).find? q with
    | none =>
        have hall := (List.find?_eq_none.mp hfind) (Lng M - 1) hlast_mem
        simp [hlast] at hall
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hsome
  have hqc : q c = true := List.find?_some hc
  have hPcut : Pcut M = c := by
    unfold Pcut
    change ((List.range (Lng M)).find? q).getD (Lng M - 1) = c
    rw [hc]
    rfl
  rw [hPcut]
  simp [q] at hqc
  exact ⟨hqc.1.1, hqc.1.2, hqc.2⟩

private theorem drop_eq_seg (M : PS) (k : ℕ) (hk : k < Lng M) :
    M.drop k = seg M k (Lng M - 1) := by
  apply List.ext_getElem
  · have hpred : Lng M - 1 + 1 = Lng M := by omega
    simp [seg, hpred]
  · intro j hj₁ hj₂
    have hkj : k + j < Lng M := by
      simp only [List.length_drop] at hj₁
      exact Nat.add_lt_of_lt_sub' hj₁
    simp [seg, List.getElem_range', entry, hkj]

private theorem pAux_nonempty (fuel : ℕ) (M : PS) : PAux fuel M ≠ [] := by
  cases fuel with
  | zero => simp [PAux]
  | succ fuel =>
      simp only [PAux]
      split <;> simp

private theorem pAux_of_nonmulti (fuel : ℕ) (M : PS)
    (hm : multiT M = false) : PAux fuel M = [M] := by
  cases fuel <;> simp [PAux, hm]

private theorem pAux_components (fuel : ℕ) (M : PS) (hM : TPS M)
    (hbound : Lng M ≤ fuel) :
    ∀ M' ∈ PAux fuel M, zeroT M' = true ∨ monoT M' = true := by
  induction fuel generalizing M with
  | zero =>
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      omega
  | succ fuel ih =>
      by_cases hs : (multiT M && decide (1 < Lng M)) = true
      · have hsplit : multiT M = true ∧ 1 < Lng M := by simpa using hs
        have hm : multiT M = true := hsplit.1
        have hlen : 1 < Lng M := hsplit.2
        have hc := pcut_spec M hlen
        rcases hc with ⟨hcpos, hcle, hanc⟩
        have hclt : Pcut M < Lng M := by omega
        have hprelen : Lng (M.take (Pcut M)) = Pcut M := by
          simp [Nat.min_eq_left hclt.le]
        have hpre : TPS (M.take (Pcut M)) := by
          intro heq
          have : Lng (M.take (Pcut M)) = 0 := by simp [heq]
          omega
        have hprebound : Lng (M.take (Pcut M)) ≤ fuel := by omega
        have htail : zeroT (M.drop (Pcut M)) = true ∨
            monoT (M.drop (Pcut M)) = true := by
          by_cases hstrict : Pcut M < Lng M - 1
          · right
            rw [drop_eq_seg M (Pcut M) hclt]
            exact mono_ancestor_slice M (Pcut M) (Lng M - 1) hM hstrict hanc
          · have hceq : Pcut M = Lng M - 1 := by omega
            have htail_len : Lng (M.drop (Pcut M)) = 1 := by
              have hpred : Lng M - (Lng M - 1) = 1 := by omega
              simpa only [List.length_drop, hceq] using hpred
            by_cases hz : zeroT (M.drop (Pcut M)) = true
            · exact Or.inl hz
            · right
              simp [monoT, hz, htail_len, leR, le0, le0Aux]
        rw [PAux, if_pos hs]
        intro M' hmem
        simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | rfl
        · exact ih (M.take (Pcut M)) hpre hprebound M' hmem
        · exact htail
      · have hnonmulti : zeroT M = true ∨ monoT M = true := by
          by_cases hz : zeroT M = true
          · exact Or.inl hz
          · by_cases hm : monoT M = true
            · exact Or.inr hm
            · have hmulti : multiT M = true := by simp [multiT, hz, hm]
              have hlen := multi_length_gt_one M hM hmulti
              simp [hmulti, hlen] at hs
        rw [PAux, if_neg hs]
        simpa using hnonmulti

theorem P_components_nonmulti (M : PS) (hM : TPS M) :
    ∀ M' ∈ P M, zeroT M' = true ∨ monoT M' = true := by
  exact pAux_components (Lng M) M hM (by rfl)

theorem P_components_multi_iff (M : PS) (hM : TPS M) :
    multiT M = true ↔ 1 < (P M).length := by
  constructor
  · intro hm
    have hlen := multi_length_gt_one M hM hm
    unfold P
    have hstep :
        PAux (Lng M) M =
          PAux (Lng M - 1) (M.take (Pcut M)) ++ [M.drop (Pcut M)] := by
      cases heq : Lng M with
      | zero => omega
      | succ fuel =>
          rw [PAux, if_pos (by simp [hm, hlen])]
          simp
    rw [hstep]
    have hn := pAux_nonempty (Lng M - 1) (M.take (Pcut M))
    have hp : 0 < (PAux (Lng M - 1) (M.take (Pcut M))).length :=
      List.length_pos_of_ne_nil hn
    simp only [List.length_append, List.length_singleton]
    omega
  · intro hP
    cases hm : multiT M
    · have heq := pAux_of_nonmulti (Lng M) M hm
      simp [P, heq] at hP
    · rfl

#print axioms P_components_nonmulti
#print axioms P_components_multi_iff

end PSS

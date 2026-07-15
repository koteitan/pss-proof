import «6».«6.5-Red-IncrFirst-invariance»
import «6».«6.5-Lng-Red-invariance»
import «6».«6.2-mono-prefix»
import «5».«5.3-pred-is-oper1»

/-!
# §6.5 命題（`Red` と `Pred` の可換性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_Pred`
- 訂正: なし
- Isabelle: `m_6_5_Red_Pred`
- 依存: `6.5-Red-welldefined`, `6.5-Red-IncrFirst-invariance`,
  `6.5-Lng-Red-invariance`, §6.2
- 状態: ✅ 証明済（sorry 0）

The proof follows the recursive structure of `Red`.  The structural facts below
say that `Pred` removes exactly the final column and commutes with the
transformations used by every recursive branch.
-/

namespace PSS

theorem Pred_eq_take (M : PS) (hlen : 1 < Lng M) :
    Pred M = M.take (Lng M - 1) := by
  simp [Pred, Nat.not_le_of_lt hlen, List.dropLast_eq_take]

@[simp] theorem length_Pred (M : PS) (hlen : 1 < Lng M) :
    Lng (Pred M) = Lng M - 1 := by
  rw [Pred_eq_take M hlen]
  simp

theorem Pred_TPS (M : PS) (hM : TPS M) : TPS (Pred M) := by
  by_cases hlen : Lng M ≤ 1
  · simpa [Pred, hlen] using hM
  · have hlen' : 1 < Lng M := by omega
    rw [Pred_eq_take M hlen']
    apply List.ne_nil_of_length_pos
    simp
    omega

theorem entry_Pred (M : PS) (i j : ℕ) (hj : j < Lng M - 1) :
    entry (Pred M) i j = entry M i j := by
  have hlen : 1 < Lng M := by omega
  rw [Pred_eq_take M hlen, entry_take M (Lng M - 1) i j hj]

theorem entry_Pred_zero (M : PS) (i : ℕ) (hlen : 1 < Lng M) :
    entry (Pred M) i 0 = entry M i 0 := by
  apply entry_Pred
  omega

theorem nonmulti_Pred (M : PS) (hM : TPS M)
    (hm : multiT M = false) (hlen : 1 < Lng M) :
    multiT (Pred M) = false := by
  have hpred := Pred_eq_take M hlen
  have hpredlen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hpredT : TPS (Pred M) := Pred_TPS M hM
  apply (multi_criterion_12 (Pred M) hpredT).mpr
  intro j hjpos hjL
  rw [hpred, entry_take M (Lng M - 1) 0 0 (by omega),
    entry_take M (Lng M - 1) 0 j (by simpa [hpredlen] using hjL)]
  exact (multi_criterion_12 M hM).mp hm j hjpos (by omega)

@[simp] theorem IncrFirstN_dropLast (n : ℕ) (M : PS) :
    IncrFirstN n M.dropLast = (IncrFirstN n M).dropLast := by
  induction n generalizing M with
  | zero => rfl
  | succ n ih =>
      simp only [IncrFirstN]
      rw [show IncrFirst M.dropLast = (IncrFirst M).dropLast by
        simp [IncrFirst, List.map_dropLast], ih]

theorem IncrFirstN_Pred (n : ℕ) (M : PS) (hlen : 1 < Lng M) :
    IncrFirstN n (Pred M) = Pred (IncrFirstN n M) := by
  have hIL : Lng (IncrFirstN n M) = Lng M := by
    simp [IncrFirstN_eq_map]
  simp only [Pred, Nat.not_le_of_lt hlen]
  rw [if_neg (by omega : ¬Lng (IncrFirstN n M) ≤ 1)]
  exact IncrFirstN_dropLast n M

private theorem dropLast_append_of_right_ne (A B : PS) (hBne : B ≠ []) :
    (A ++ B).dropLast = A ++ B.dropLast := by
  induction A with
  | nil => simp
  | cons a A ih =>
      rw [List.cons_append,
        List.dropLast_cons_of_ne_nil
          (List.append_ne_nil_of_right_ne_nil A hBne), ih]
      rfl

theorem Pred_append_right (A B : PS) (hB : 1 < Lng B) :
    Pred (A ++ B) = A ++ Pred B := by
  change 1 < B.length at hB
  have hBne : B ≠ [] := by
    intro h
    simp [h] at hB
  have hAB : ¬Lng (A ++ B) ≤ 1 := by
    simp only [List.length_append]
    omega
  have hdrop := dropLast_append_of_right_ne A B hBne
  simp only [Pred, if_neg hAB, if_neg (Nat.not_le_of_lt hB)]
  exact hdrop

/-- The positive-row-one recursive argument of `Red` commutes with `Pred`.
This is Isabelle's `m_6_5_T4_coreArg_Pred`, expressed with Lean's
`IncrFirstN` rather than function powers. -/
theorem positiveCoreArg_Pred (M : PS) (hlen : 1 < Lng M)
    (_hpos : 0 < entry M 1 0) :
    diagSeq 0 (entry M 1 0 - 1) ++
        IncrFirstN (entry M 1 0) (Pred M) =
      Pred (diagSeq 0 (entry M 1 0 - 1) ++
        IncrFirstN (entry M 1 0) M) := by
  rw [Pred_append_right _ _ (by simpa [IncrFirstN_eq_map] using hlen),
    IncrFirstN_Pred]
  exact hlen

theorem coreReduce_Pred (M : PS) (hlen : 1 < Lng M) :
    coreReduce (Pred M) = Pred (coreReduce M) := by
  have he : entry (Pred M) 1 0 = entry M 1 0 :=
    entry_Pred_zero M 1 hlen
  by_cases hm : entry M 1 0 = 0
  · have hmP : entry (Pred M) 1 0 = 0 := he.trans hm
    rw [coreReduce, if_pos hmP, coreReduce, if_pos hm]
    rw [Pred_eq_take M hlen]
    have hout : 1 < Lng
        ((List.range (Lng M)).map (fun j =>
          (entry M 0 j - entry M 0 0, entry M 1 j))) := by
      simpa using hlen
    rw [Pred_eq_take _ hout]
    apply List.ext_getElem
    · simp
    · intro j hj₁ hj₂
      have hj : j < Lng M - 1 := by simpa using hj₂
      simp only [List.getElem_map, List.getElem_range, List.getElem_take]
      rw [entry_take M (Lng M - 1) 0 j hj,
        entry_take M (Lng M - 1) 0 0 (by omega),
        entry_take M (Lng M - 1) 1 j hj]
  · have hmP : entry (Pred M) 1 0 ≠ 0 := by simpa [he] using hm
    rw [coreReduce, if_neg hmP, coreReduce, if_neg hm, he]
    exact positiveCoreArg_Pred M hlen (Nat.pos_of_ne_zero hm)

private theorem diagSeq_succ_snoc_rp (u v : ℕ) (huv : u ≤ v) :
    diagSeq u (v + 1) = diagSeq u v ++ [(v + 1, v + 1)] := by
  have hrange :
      List.range' u (v + 1 + 1 - u) =
        List.range' u (v + 1 - u) ++ [v + 1] := by
    calc
      List.range' u (v + 1 + 1 - u) =
          List.range' u ((v + 1 - u) + 1) := by
            congr 1
            omega
      _ = List.range' u (v + 1 - u) ++
          List.range' (u + (v + 1 - u)) 1 := List.range'_append_1.symm
      _ = List.range' u (v + 1 - u) ++ [v + 1] := by
        rw [Nat.add_sub_of_le (by omega : u ≤ v + 1)]
        simp
  simp [diagSeq, hrange]

theorem Pred_diagSeq_succ_rp (u v : ℕ) (huv : u ≤ v) :
    Pred (diagSeq u (v + 1)) = diagSeq u v := by
  have hlen : 1 < Lng (diagSeq u (v + 1)) := by
    simp [diagSeq]
    omega
  rw [Pred, if_neg (Nat.not_le_of_lt hlen),
    diagSeq_succ_snoc_rp u v huv]
  simp

private theorem TrMax_stop_rp (M : PS) (hM : TPS M) :
    nextR M 1 (TrMax M) (TrMax M + 1) = false := by
  apply Bool.eq_false_iff.mpr
  intro hstep
  have hle : TrMax M + 1 ≤ TrMax M := by
    apply le_TrMax_intro_wd M (TrMax M + 1) hM
    intro j hj
    by_cases heq : j = TrMax M
    · simpa [heq] using hstep
    · exact TrMax_trunk_step M j hM (by omega)
  omega

theorem TrMax_Pred_nontrunk (M : PS) (hM : TPS M)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1) :
    TrMax (Pred M) = TrMax M := by
  have hPredT := Pred_TPS M hM
  have hpred := Pred_eq_take M hlen
  have hPL := length_Pred M hlen
  have hbound := TrMax_bound M hM
  have htrlt : TrMax M < Lng M - 1 := by omega
  have hlower : TrMax M ≤ TrMax (Pred M) := by
    apply le_TrMax_intro_wd (Pred M) (TrMax M) hPredT
    intro j hj
    have hs := TrMax_trunk_step M j hM hj
    rw [hpred, nextR_take_adm M (Lng M - 1) 1 j (j + 1)
      (by omega) (by omega) (by omega)]
    exact hs
  apply Nat.le_antisymm ?_ hlower
  by_contra hnot
  have hstrict : TrMax M < TrMax (Pred M) := by omega
  have hsP := TrMax_trunk_step (Pred M) (TrMax M) hPredT hstrict
  have hend : TrMax M + 1 < Lng (Pred M) := by
    have hh : nextrel1 (Pred M) (TrMax M) (TrMax M + 1) = true := by
      simpa [nextR] using hsP
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
    omega
  have hsM : nextR M 1 (TrMax M) (TrMax M + 1) = true := by
    rw [hpred, nextR_take_adm M (Lng M - 1) 1 (TrMax M) (TrMax M + 1)
      (by omega) (by rw [hPL] at hend; omega) (by rw [hPL] at hend; omega)] at hsP
    exact hsP
  rw [TrMax_stop_rp M hM] at hsM
  contradiction

theorem TrMax_Pred_trunk (M : PS) (hM : TPS M)
    (hlen : 1 < Lng M) (htrunk : TrMax M = Lng M - 1) :
    TrMax (Pred M) = Lng (Pred M) - 1 := by
  have hPredT := Pred_TPS M hM
  have hpred := Pred_eq_take M hlen
  have hPL := length_Pred M hlen
  apply Nat.le_antisymm (TrMax_bound (Pred M) hPredT)
  apply le_TrMax_intro_wd (Pred M) (Lng (Pred M) - 1) hPredT
  intro j hj
  have hjtr : j < TrMax M := by
    rw [htrunk]
    rw [hPL] at hj
    omega
  have hs := TrMax_trunk_step M j hM hjtr
  rw [hpred, nextR_take_adm M (Lng M - 1) 1 j (j + 1)
    (by omega) (by rw [hPL] at hj; omega) (by rw [hPL] at hj; omega)]
  exact hs

theorem monoT_Pred_long (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hlen : 2 < Lng M) :
    monoT (Pred M) = true := by
  have hlen1 : 1 < Lng M := by omega
  have hpred := Pred_eq_take M hlen1
  have hseg : M.take (Lng M - 1) = seg M 0 (Lng M - 2) := by
    simpa using take_eq_seg M (Lng M - 1) (by omega) (by omega)
  rw [hpred, hseg]
  exact mono_prefix M (Lng M - 2) hM hmono (by omega) (by omega)

theorem Red_Pred_core_trunk (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (htrunk : TrMax M = Lng M - 1) :
    Red (Pred M) = Pred (Red M) := by
  have hlen : 1 < Lng M := by
    have hh := hmono
    simp [monoT] at hh
    have hz : zeroT M = false := hh.1
    by_contra h
    have hLpos := List.length_pos_of_ne_nil hM
    change 0 < Lng M at hLpos
    have hle : Lng M ≤ 1 := Nat.le_of_not_gt h
    have hL : Lng M = 1 := by omega
    simp [zeroT, hL, hcore.2] at hz
  have hRM := Red_core_trunk_ri M hM hmono hcore htrunk
  by_cases hshort : Lng M = 2
  · have hzeroP : zeroT (Pred M) = true := by
      simp [zeroT, length_Pred M hlen, hshort,
        entry_Pred_zero M 1 hlen, hcore.2]
    have hRP := Red_zero_mr (Pred M) hzeroP
    rw [hRP, hRM, hshort]
    simp [Pred, diagSeq]
    decide
  · have hlong : 2 < Lng M := by omega
    have hmonoP := monoT_Pred_long M hM hmono hlong
    have hcoreP : entry (Pred M) 0 0 = 0 ∧ entry (Pred M) 1 0 = 0 := by
      simpa [entry_Pred_zero M 0 hlen, entry_Pred_zero M 1 hlen] using hcore
    have htrP := TrMax_Pred_trunk M hM hlen htrunk
    have hRP := Red_core_trunk_ri (Pred M) (Pred_TPS M hM) hmonoP hcoreP htrP
    rw [hRP, hRM]
    rw [show Lng M - 1 = (Lng M - 2) + 1 by omega,
      Pred_diagSeq_succ_rp 0 (Lng M - 2) (Nat.zero_le _)]
    have hPL : Lng (Pred M) - 1 = Lng M - 2 := by
      have he := length_Pred M hlen
      omega
    rw [hPL]

theorem Red_Pred_noncore_zero (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0))
    (hm : entry M 1 0 = 0)
    (hIH : Red (Pred (coreReduce M)) = Pred (Red (coreReduce M))) :
    Red (Pred M) = Pred (Red M) := by
  have hlen : 1 < Lng M := by
    have hpos := List.length_pos_of_ne_nil hM
    change 0 < Lng M at hpos
    by_contra h
    have hle : Lng M ≤ 1 := Nat.le_of_not_gt h
    have hL : Lng M = 1 := by omega
    have hz : zeroT M = true := by simp [zeroT, hL, hm]
    have hh := hmono
    simp [monoT, hz] at hh
  have hRM : Red M = Red (coreReduce M) := by
    simpa [hm] using Red_noncore_ri M hM hmono hnoncore
  have hcomm := coreReduce_Pred M hlen
  by_cases hshort : Lng M = 2
  · have hPredT := Pred_TPS M hM
    have hmP : entry (Pred M) 1 0 = 0 := by
      rw [entry_Pred_zero M 1 hlen, hm]
    have hzP : zeroT (Pred M) = true := by
      simp [zeroT, length_Pred M hlen, hshort, hmP]
    have hRP := Red_zero_mr (Pred M) hzP
    have hCPcore := coreReduce_core (Pred M) hPredT
    have hCPL : Lng (coreReduce (Pred M)) = 1 := by
      simp [coreReduce, hmP, length_Pred M hlen, hshort]
    have hzPC : zeroT (Pred (coreReduce M)) = true := by
      rw [← hcomm]
      simp [zeroT, hCPL, hCPcore.2]
    rw [hRP, hRM, ← hIH, Red_zero_mr _ hzPC]
  · have hlong : 2 < Lng M := by omega
    have hmonoP := monoT_Pred_long M hM hmono hlong
    have hPredT := Pred_TPS M hM
    have hmP : entry (Pred M) 1 0 = 0 := by
      rw [entry_Pred_zero M 1 hlen, hm]
    have hnoncoreP :
        ¬(entry (Pred M) 0 0 = 0 ∧ entry (Pred M) 1 0 = 0) := by
      intro hc
      apply hnoncore
      rw [entry_Pred_zero M 0 hlen, entry_Pred_zero M 1 hlen] at hc
      exact hc
    have hRP : Red (Pred M) = Red (coreReduce (Pred M)) := by
      simpa [hmP] using
        Red_noncore_ri (Pred M) hPredT hmonoP hnoncoreP
    calc
      Red (Pred M) = Red (coreReduce (Pred M)) := hRP
      _ = Red (Pred (coreReduce M)) := by rw [hcomm]
      _ = Pred (Red (coreReduce M)) := hIH
      _ = Pred (Red M) := by rw [hRM]

theorem monoT_Pred_positive (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M)
    (hpos : 0 < entry M 1 0) : monoT (Pred M) = true := by
  by_cases hshort : Lng M = 2
  · have hPL : Lng (Pred M) = 1 := by rw [length_Pred M hlen, hshort]
    have he1 : entry (Pred M) 1 0 = entry M 1 0 :=
      entry_Pred_zero M 1 hlen
    have hz : zeroT (Pred M) = false := by
      simp [zeroT, hPL, he1]
      omega
    have hle : leR (Pred M) 0 0 (Lng (Pred M) - 1) = true := by
      simp [hPL, leR, le0, le0Aux]
    simp [monoT, hz, hle]
  · exact monoT_Pred_long M hM hmono (by omega)

private def positiveOutMap (N : PS) (m : ℕ) : PS :=
  let jN := Lng N - 1
  (List.range' m (jN + 1 - m)).map (fun j =>
    (entry N 0 j - entry N 0 m + entry N 1 m, entry N 1 j))

private theorem redPositiveOut_eq_map (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    redPositiveOut_ri M (Red (coreReduce M)) =
      positiveOutMap (Red (coreReduce M)) (entry M 1 0) := by
  have hg := monoT_Red_m10pos M hM hmono hpos
  let N := Red (coreReduce M)
  let m := entry M 1 0
  have hCT := coreReduce_TPS M hM
  have hNL : Lng N = m + Lng M := by
    calc
      Lng N = Lng (coreReduce M) := Lng_Red_invariance (coreReduce M) hCT
      _ = m + Lng M := by
        simp [coreReduce, m, Nat.ne_of_gt hpos, diagSeq, IncrFirstN_eq_map]
        omega
  have hmj : m ≤ Lng N - 1 := by
    have hMpos := List.length_pos_of_ne_nil hM
    change 0 < Lng M at hMpos
    rw [hNL]
    omega
  have hmonoS : monoT (seg N m (Lng N - 1)) = true := by
    simpa [N, m] using hg.2
  simp [redPositiveOut_ri, positiveOutMap, N, m, hmj, hmonoS]

private theorem positiveOutMap_Pred (N : PS) (m : ℕ)
    (hm : m < Lng N - 1) :
    positiveOutMap (Pred N) m = Pred (positiveOutMap N m) := by
  have hNlen : 1 < Lng N := by omega
  have hPL := length_Pred N hNlen
  have hfullLen : Lng (positiveOutMap N m) = Lng N - m := by
    simp [positiveOutMap]
    omega
  have hfullLong : 1 < Lng (positiveOutMap N m) := by omega
  rw [Pred_eq_take _ hfullLong]
  apply List.ext_getElem
  · simp [positiveOutMap, hPL]
    omega
  · intro k hk₁ hk₂
    have hk : k < Lng N - 1 - m := by
      simp only [positiveOutMap, List.length_map, List.length_range'] at hk₁
      rw [hPL] at hk₁
      omega
    have hmk : m + k < Lng N - 1 := by omega
    simp only [positiveOutMap, List.getElem_map, List.getElem_range',
      List.getElem_take, Nat.one_mul]
    rw [entry_Pred N 0 (m + k) hmk, entry_Pred N 0 m (by omega),
      entry_Pred N 1 m (by omega), entry_Pred N 1 (m + k) hmk]

theorem Red_Pred_noncore_positive (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M)
    (hpos : 0 < entry M 1 0)
    (hIH : Red (Pred (coreReduce M)) = Pred (Red (coreReduce M))) :
    Red (Pred M) = Pred (Red M) := by
  let m := entry M 1 0
  let N := Red (coreReduce M)
  have hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by omega
  have hmne : entry M 1 0 ≠ 0 := Nat.ne_of_gt hpos
  have hRM : Red M = redPositiveOut_ri M N := by
    simpa [N, hmne] using Red_noncore_ri M hM hmono hnoncore
  have hPredT := Pred_TPS M hM
  have hmonoP := monoT_Pred_positive M hM hmono hlen hpos
  have heP : entry (Pred M) 1 0 = entry M 1 0 :=
    entry_Pred_zero M 1 hlen
  have hposP : 0 < entry (Pred M) 1 0 := by simpa [heP] using hpos
  have hnoncoreP :
      ¬(entry (Pred M) 0 0 = 0 ∧ entry (Pred M) 1 0 = 0) := by omega
  have hRP : Red (Pred M) =
      redPositiveOut_ri (Pred M) (Red (coreReduce (Pred M))) := by
    simpa [Nat.ne_of_gt hposP] using
      Red_noncore_ri (Pred M) hPredT hmonoP hnoncoreP
  have hcomm := coreReduce_Pred M hlen
  have hNP : Red (coreReduce (Pred M)) = Pred N := by
    calc
      Red (coreReduce (Pred M)) = Red (Pred (coreReduce M)) := by rw [hcomm]
      _ = Pred (Red (coreReduce M)) := hIH
      _ = Pred N := rfl
  have hCT := coreReduce_TPS M hM
  have hNL : Lng N = m + Lng M := by
    calc
      Lng N = Lng (coreReduce M) := by
        simpa [N] using Lng_Red_invariance (coreReduce M) hCT
      _ = m + Lng M := by
        simp [coreReduce, m, hmne, diagSeq, IncrFirstN_eq_map]
        omega
  have hmN : m < Lng N - 1 := by rw [hNL]; omega
  calc
    Red (Pred M) =
        redPositiveOut_ri (Pred M) (Red (coreReduce (Pred M))) := hRP
    _ = positiveOutMap (Red (coreReduce (Pred M)))
          (entry (Pred M) 1 0) :=
      redPositiveOut_eq_map (Pred M) hPredT hmonoP hposP
    _ = positiveOutMap (Pred N) m := by rw [hNP, heP]
    _ = Pred (positiveOutMap N m) := positiveOutMap_Pred N m hmN
    _ = Pred (redPositiveOut_ri M N) := by
      rw [redPositiveOut_eq_map M hM hmono hpos]
    _ = Pred (Red M) := by rw [hRM]

private theorem P_getLastD_mem_rp (M : PS) :
    (P M).getLastD [] ∈ P M := by
  have hne := P_nonempty M
  cases h : P M with
  | nil => exact (hne h).elim
  | cons A Q => simp [List.getLastD]

private theorem P_member_TPS_rp (M Q : PS) (hM : TPS M)
    (hQ : Q ∈ P M) : TPS Q := by
  obtain ⟨J, hJ, hget⟩ := List.mem_iff_getElem.mp hQ
  have hpos := P_component_nonempty M J hM hJ
  have heq : (P M).getD J [] = Q := by
    rw [getD_eq_getElem_idx (P M) [] hJ]
    exact hget
  rw [heq] at hpos
  exact List.ne_nil_of_length_pos hpos

/-- `Pred` acts only on the final principal component.  This is Isabelle's
`pred_P_decomp`; using `Pred M = M[1]` makes the proof a direct consequence of
the two already established `P`/fundamental-sequence equations. -/
theorem P_Pred_multi (M : PS) (hM : TPS M) (hmulti : multiT M = true) :
    P (Pred M) =
      if Lng ((P M).getLastD []) = 1 then
        (P M).dropLast
      else
        (P M).dropLast ++ [Pred ((P M).getLastD [])] := by
  have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
  have hPlen : 1 < (P M).length :=
    (P_components_multi_iff M hM).mp hmulti
  have hPne : (P M).length ≠ 1 := by omega
  let D := (P M).getLastD []
  have hDmem : D ∈ P M := by simpa [D] using P_getLastD_mem_rp M
  have hDT : TPS D := P_member_TPS_rp M D hM hDmem
  by_cases hDlen : Lng D = 1
  · have hf := P_fseq_1 M 1 hM (by omega) (by simpa [D] using hDlen)
    rw [if_pos (by simpa [D] using hDlen)]
    simpa [← pred_is_oper1 M hM hlen, hPne] using hf.2
  · have hDpos : 0 < Lng D := List.length_pos_of_ne_nil hDT
    have hDgt : 1 < Lng D := by omega
    have hcomp := P_components_nonmulti M hM D hDmem
    have hDnm : multiT D = false := by
      rcases hcomp with hz | hmono
      · simp [multiT, hz]
      · simp [multiT, hmono]
    have hprednm := nonmulti_Pred D hDT hDnm hDgt
    have hf := P_fseq_2 M 1 hM (by omega) (by simpa [D] using hDgt)
    rw [if_neg (by simpa [D] using hDlen)]
    have hDoper : oper D 1 = Pred D :=
      (pred_is_oper1 D hDT hDgt).symm
    rw [pred_is_oper1 M hM hlen, hf.2]
    change (P M).dropLast ++ P (oper D 1) =
      (P M).dropLast ++ [Pred D]
    rw [hDoper, P_nonmulti_eq (Pred D) hprednm]

theorem P_Pred_decomp (M : PS) (hM : TPS M) (hlen : 1 < Lng M) :
    P (Pred M) = (P M).dropLast ++
      (if Lng ((P M).getLastD []) ≤ 1 then []
       else [((P M).getLastD []).dropLast]) := by
  let D := (P M).getLastD []
  change P (Pred M) = (P M).dropLast ++
    (if Lng D ≤ 1 then [] else [D.dropLast])
  by_cases hmulti : multiT M = true
  · have hDmem : D ∈ P M := by simpa [D] using P_getLastD_mem_rp M
    have hDT := P_member_TPS_rp M D hM hDmem
    have hDpos : 0 < Lng D :=
      List.length_pos_of_ne_nil hDT
    have hdec := P_Pred_multi M hM hmulti
    change P (Pred M) = if Lng D = 1 then (P M).dropLast
      else (P M).dropLast ++ [Pred D] at hdec
    rw [hdec]
    by_cases hDone : Lng D = 1
    · rw [if_pos hDone, if_pos (by omega)]
      simp
    · have hDgt : 1 < Lng D := by omega
      rw [if_neg hDone, if_neg (Nat.not_le_of_lt hDgt)]
      simp [Pred, Nat.not_le_of_lt hDgt]
  · have hnm : multiT M = false := Bool.eq_false_of_not_eq_true hmulti
    have hprednm := nonmulti_Pred M hM hnm hlen
    rw [P_nonmulti_eq M hnm, P_nonmulti_eq (Pred M) hprednm]
    have hD : D = M := by simp [D, P_nonmulti_eq M hnm]
    rw [hD, if_neg (Nat.not_le_of_lt hlen)]
    simp [Pred, Nat.not_le_of_lt hlen]

private theorem multiT_length_one_false (M : PS) (hL : Lng M = 1) :
    multiT M = false := by
  by_cases hz : zeroT M = true
  · simp [multiT, hz]
  · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
    have hmono : monoT M = true := by
      have hle : leR M 0 0 (Lng M - 1) = true := by
        simp [hL, leR, le0, le0Aux]
      simp [monoT, hz', hle]
    simp [multiT, hmono]

theorem Br_Pred_core_nontrunk (M : PS) (hM : TPS M)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1) :
    Br (Pred M) = (Br M).dropLast ++
      (if Lng ((Br M).getLastD []) ≤ 1 then []
       else [((Br M).getLastD []).dropLast]) := by
  let t := TrMax M
  let j₀ := t + 1
  let S := M.drop j₀
  have htbound := TrMax_bound M hM
  have htlt : t < Lng M - 1 := by simpa [t] using lt_of_le_of_ne htbound hne
  have hj₀L : j₀ < Lng M := by simp [j₀]; omega
  have hST : TPS S := by
    apply List.ne_nil_of_length_pos
    simp [S]
    omega
  have hSL : Lng S = Lng M - j₀ := by simp [S]
  have hBrM : Br M = P S := by
    rw [Br, if_neg hne]
    simpa [S, j₀, t] using congrArg P
      (drop_eq_seg M (TrMax M + 1) (by omega)).symm
  have htrP := TrMax_Pred_nontrunk M hM hlen hne
  have hPL := length_Pred M hlen
  by_cases hSone : Lng S = 1
  · have htlastP : TrMax (Pred M) = Lng (Pred M) - 1 := by
      rw [htrP, hPL]
      simp [t, j₀] at hSL
      omega
    have hBrP : Br (Pred M) = [] := by simp [Br, htlastP]
    have hPS : P S = [S] :=
      P_nonmulti_eq S (multiT_length_one_false S hSone)
    rw [hBrP, hBrM, hPS]
    simp [hSone]
  · have hSpos := List.length_pos_of_ne_nil hST
    change 0 < Lng S at hSpos
    have hSgt : 1 < Lng S := by omega
    have htneP : TrMax (Pred M) ≠ Lng (Pred M) - 1 := by
      rw [htrP, hPL]
      simp [t, j₀] at hSL
      omega
    have hdropPred : (Pred M).drop j₀ = Pred S := by
      have htakeL : Lng (M.take j₀) = j₀ := by simp [Nat.min_eq_left hj₀L.le]
      calc
        (Pred M).drop j₀ =
            (Pred (M.take j₀ ++ M.drop j₀)).drop j₀ := by simp
        _ = (M.take j₀ ++ Pred (M.drop j₀)).drop j₀ := by
          rw [Pred_append_right (M.take j₀) (M.drop j₀)
            (by simpa [S] using hSgt)]
        _ = Pred S := by simp [S, htakeL]
    have hBrP : Br (Pred M) = P (Pred S) := by
      rw [Br, if_neg htneP]
      rw [← drop_eq_seg (Pred M) (TrMax (Pred M) + 1) (by omega),
        htrP]
      simpa [j₀, t] using congrArg P hdropPred
    rw [hBrP, hBrM]
    exact P_Pred_decomp S hST hSgt

private theorem take_dropLast_eq_take (Q : List PS) (J : ℕ)
    (hJ : J ≤ Q.length - 1) : Q.dropLast.take J = Q.take J := by
  rw [List.dropLast_eq_take, List.take_take]
  congr 1
  omega

private theorem Br_Pred_index_bound (M : PS) (hM : TPS M)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (J : ℕ) (hJ : J < (Br (Pred M)).length) :
    J < (Br M).length := by
  have hshape := Br_Pred_core_nontrunk M hM hlen hne
  let D := (Br M).getLastD []
  change Br (Pred M) = (Br M).dropLast ++
    (if Lng D ≤ 1 then [] else [D.dropLast]) at hshape
  by_cases hd : Lng D ≤ 1
  · rw [hshape, if_pos hd] at hJ
    simp only [List.append_nil, List.length_dropLast] at hJ
    omega
  · rw [hshape, if_neg hd] at hJ
    have hBrNe : Br M ≠ [] := by
      intro hnil
      simp [D, hnil] at hd
    have hBrPos := List.length_pos_of_ne_nil hBrNe
    simp only [List.length_append, List.length_dropLast,
      List.length_singleton] at hJ
    omega

private theorem Br_Pred_take_eq (M : PS) (hM : TPS M)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (J : ℕ) (hJ : J < (Br (Pred M)).length) :
    (Br (Pred M)).take J = (Br M).take J := by
  have hshape := Br_Pred_core_nontrunk M hM hlen hne
  have hJM := Br_Pred_index_bound M hM hlen hne J hJ
  let D := (Br M).getLastD []
  change Br (Pred M) = (Br M).dropLast ++
    (if Lng D ≤ 1 then [] else [D.dropLast]) at hshape
  have hJdrop : J ≤ (Br M).dropLast.length := by simp; omega
  rw [hshape, List.take_append_of_le_length hJdrop]
  exact take_dropLast_eq_take (Br M) J (by omega)

private theorem IdxSum_Br_Pred (M : PS) (hM : TPS M)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (J : ℕ) (hJ : J < (Br (Pred M)).length) :
    (IdxSum (Br (Pred M))).getD J 0 = (IdxSum (Br M)).getD J 0 := by
  have hJM := Br_Pred_index_bound M hM hlen hne J hJ
  rw [idxSum_getD (Br (Pred M)) J hJ.le,
    idxSum_getD (Br M) J hJM.le, Br_Pred_take_eq M hM hlen hne J hJ]

theorem FirstNodes_Pred_core (M : PS) (hM : TPS M)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (J : ℕ) (hJ : J < (Br (Pred M)).length) :
    (FirstNodes (Pred M)).getD J 0 = (FirstNodes M).getD J 0 := by
  have hJM := Br_Pred_index_bound M hM hlen hne J hJ
  rw [FirstNodes_getD (Pred M) J hJ, FirstNodes_getD M J hJM,
    TrMax_Pred_nontrunk M hM hlen hne,
    IdxSum_Br_Pred M hM hlen hne J hJ]

theorem Joints_Pred_core (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M)
    (hne : TrMax M ≠ Lng M - 1)
    (J : ℕ) (hJ : J < (Br (Pred M)).length) :
    (Joints (Pred M)).getD J 0 = (Joints M).getD J 0 := by
  have hPredT := Pred_TPS M hM
  have hJM := Br_Pred_index_bound M hM hlen hne J hJ
  have hfn := FirstNodes_Pred_core M hM hlen hne J hJ
  have hPL := length_Pred M hlen
  have hPredLong : 1 < Lng (Pred M) := by
    by_contra hnot
    have hle : Lng (Pred M) ≤ 1 := Nat.le_of_not_gt hnot
    have hpos := List.length_pos_of_ne_nil hPredT
    change 0 < Lng (Pred M) at hpos
    have hL : Lng (Pred M) = 1 := by omega
    have ht := TrMax_bound (Pred M) hPredT
    have htr : TrMax (Pred M) = Lng (Pred M) - 1 := by omega
    have : Br (Pred M) = [] := by simp [Br, htr]
    rw [this] at hJ
    simp at hJ
  have hnm : multiT M = false := by simp [multiT, hmono]
  have hnmP := nonmulti_Pred M hM hnm hlen
  have hzP : zeroT (Pred M) = false := by
    have hne1 : Lng (Pred M) ≠ 1 := by omega
    simp [zeroT, hne1]
  have hmonoP : monoT (Pred M) = true := by
    have hh := hnmP
    simp [multiT, hzP] at hh
    exact hh
  have hnextM := Joints_nextR_FirstNodes M J hM hmono hJM
  have hnextP0 := Joints_nextR_FirstNodes (Pred M) J hPredT hmonoP hJ
  have hfL : (FirstNodes M).getD J 0 < Lng (Pred M) := by
    have hh : nextrel0 (Pred M) ((Joints (Pred M)).getD J 0)
        ((FirstNodes (Pred M)).getD J 0) = true := by
      simpa [nextR] using hnextP0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    rw [hfn] at hh
    exact hh.1.1.1.2
  have hnextMP : nextR (Pred M) 0 ((Joints M).getD J 0)
      ((FirstNodes M).getD J 0) = true := by
    rw [Pred_eq_take M hlen,
      nextR_take_adm M (Lng M - 1) 0 ((Joints M).getD J 0)
        ((FirstNodes M).getD J 0) (by omega)]
    · exact hnextM
    · have hjoint := (FirstNodes_TrMax_Joints M J hM hmono hJM).1
      have htbound := TrMax_bound M hM
      rw [hPL] at hfL
      omega
    · rw [hPL] at hfL
      exact hfL
  have hparentP : parent (Pred M) 0 ((FirstNodes M).getD J 0) =
      (Joints M).getD J 0 :=
    parent_eq_of_nextR0 (Pred M) _ _ hnextMP
  rw [Joints_getD (Pred M) J hJ, hfn, hparentP]

private theorem monoT_Pred_core_branch (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M)
    (J : ℕ) (hJ : J < (Br (Pred M)).length) :
    monoT (Pred M) = true := by
  have hPredT := Pred_TPS M hM
  have hPredLong : 1 < Lng (Pred M) := by
    by_contra hnot
    have hpos := List.length_pos_of_ne_nil hPredT
    change 0 < Lng (Pred M) at hpos
    have hL : Lng (Pred M) = 1 := by omega
    have ht := TrMax_bound (Pred M) hPredT
    have htr : TrMax (Pred M) = Lng (Pred M) - 1 := by omega
    have : Br (Pred M) = [] := by simp [Br, htr]
    rw [this] at hJ
    simp at hJ
  have hnm : multiT M = false := by simp [multiT, hmono]
  have hnmP := nonmulti_Pred M hM hnm hlen
  have hzP : zeroT (Pred M) = false := by
    have hne1 : Lng (Pred M) ≠ 1 := by omega
    simp [zeroT, hne1]
  have hh := hnmP
  simp [multiT, hzP] at hh
  exact hh

private theorem FirstNodes_Pred_lt (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M)
    (J : ℕ) (hJ : J < (Br (Pred M)).length) :
    (FirstNodes (Pred M)).getD J 0 < Lng (Pred M) := by
  have hmonoP := monoT_Pred_core_branch M hM hmono hlen J hJ
  have hn := Joints_nextR_FirstNodes (Pred M) J (Pred_TPS M hM) hmonoP hJ
  have hh : nextrel0 (Pred M) ((Joints (Pred M)).getD J 0)
      ((FirstNodes (Pred M)).getD J 0) = true := by
    simpa [nextR] using hn
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact hh.1.1.1.2

theorem branch_entry1_Pred_core (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M)
    (hne : TrMax M ≠ Lng M - 1)
    (J : ℕ) (hJ : J < (Br (Pred M)).length) :
    entry ((Br (Pred M)).getD J []) 1 0 =
      entry ((Br M).getD J []) 1 0 := by
  have hJM := Br_Pred_index_bound M hM hlen hne J hJ
  have hfn := FirstNodes_Pred_core M hM hlen hne J hJ
  have hfL := FirstNodes_Pred_lt M hM hmono hlen J hJ
  calc
    entry ((Br (Pred M)).getD J []) 1 0 =
        entry (Pred M) 1 ((FirstNodes (Pred M)).getD J 0) :=
      (entry_FirstNodes_eq_component_mr (Pred M) J 1 (Pred_TPS M hM) hJ).symm
    _ = entry M 1 ((FirstNodes M).getD J 0) := by
      rw [hfn]
      apply entry_Pred
      have hh := hfL
      rw [hfn, length_Pred M hlen] at hh
      exact hh
    _ = entry ((Br M).getD J []) 1 0 :=
      entry_FirstNodes_eq_component_mr M J 1 hM hJM

theorem branchNP_Pred_core (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hcore1 : entry M 1 0 = 0)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (J : ℕ) (hJ : J < (Br (Pred M)).length) :
    branchNP (Pred M) J = branchNP M J := by
  have hJM := Br_Pred_index_bound M hM hlen hne J hJ
  have he := branch_entry1_Pred_core M hM hmono hlen hne J hJ
  have hfn := FirstNodes_Pred_core M hM hlen hne J hJ
  by_cases hb : entry ((Br M).getD J []) 1 0 = 0
  · unfold branchNP
    rw [he, hb]
    simp
  · have hbP : entry ((Br (Pred M)).getD J []) 1 0 ≠ 0 := by omega
    let f := (FirstNodes M).getD J 0
    have htr := FirstNodes_TrMax_Joints M J hM hmono hJM
    have hnext0 := Joints_nextR_FirstNodes M J hM hmono hJM
    have hfL : f < Lng M := by
      have hh : nextrel0 M ((Joints M).getD J 0) f = true := by
        simpa [f, nextR] using hnext0
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
      exact hh.1.1.1.2
    have hfpos : 0 < f := by
      change 0 < (FirstNodes M).getD J 0
      omega
    have hef : entry M 1 f = entry ((Br M).getD J []) 1 0 := by
      simpa [f] using entry_FirstNodes_eq_component_mr M J 1 hM hJM
    have he10 : entry M 1 0 < entry M 1 f := by rw [hcore1, hef]; omega
    have hfull : leR M 0 0 (Lng M - 1) = true := by
      have hh := hmono
      simp only [monoT, Bool.and_eq_true] at hh
      exact hh.2
    have h0f : leR M 0 0 f = true :=
      ancestor_tree_1 M 0 f (Lng M - 1) hM hfull (Nat.zero_le _) (by omega)
    obtain ⟨p, _, _, hpnext⟩ :=
      parent_exists_2 M 0 f hM hfpos hfL he10 h0f
    have hparentM : parent M 1 f = p := by
      apply parent_eq_of_unique_fseq M 1 f p hpnext
      intro q hq
      exact nextR1_unique_mr M q p f hq hpnext
    have hfP : f < Lng (Pred M) := by
      have hh := FirstNodes_Pred_lt M hM hmono hlen J hJ
      rw [hfn] at hh
      exact hh
    have hpnextP : nextR (Pred M) 1 p f = true := by
      have hpflt := (nextR_implies_row0 M 1 p f hpnext).1
      rw [Pred_eq_take M hlen,
        nextR_take_adm M (Lng M - 1) 1 p f (by omega)]
      · exact hpnext
      · have hPL := length_Pred M hlen
        rw [hPL] at hfP
        omega
      · have hPL := length_Pred M hlen
        rw [hPL] at hfP
        exact hfP
    have hparentP : parent (Pred M) 1 f = p := by
      apply parent_eq_of_unique_fseq (Pred M) 1 f p hpnextP
      intro q hq
      exact nextR1_unique_mr (Pred M) q p f hq hpnextP
    unfold branchNP
    rw [he, hfn]
    simp only [if_neg hb]
    change parent (Pred M) 1 f + 1 = parent M 1 f + 1
    rw [hparentP, hparentM]

private theorem Br_block_Pred_interior (M : PS) (hM : TPS M)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (J : ℕ) (hJ : J < (Br M).length - 1) :
    (Br (Pred M)).getD J [] = (Br M).getD J [] := by
  have hshape := Br_Pred_core_nontrunk M hM hlen hne
  let ext := if Lng ((Br M).getLastD []) ≤ 1 then []
    else [((Br M).getLastD []).dropLast]
  change Br (Pred M) = (Br M).dropLast ++ ext at hshape
  have hJdrop : J < (Br M).dropLast.length := by simp; omega
  unfold List.getD
  rw [hshape, List.getElem?_append_left hJdrop,
    List.dropLast_eq_take, List.getElem?_take_of_lt hJ]

private theorem getLastD_eq_getD_last_rp (Q : List PS) (hQ : Q ≠ []) :
    Q.getLastD [] = Q.getD (Q.length - 1) [] := by
  cases h : Q with
  | nil => exact (hQ h).elim
  | cons A R =>
      simp [List.getLastD, List.getD, List.getLast_eq_getElem]

private theorem Br_lastblock_Pred (M : PS) (hM : TPS M)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (hlast : 1 < Lng ((Br M).getLastD [])) :
    (Br (Pred M)).length = (Br M).length ∧
      (Br (Pred M)).getD ((Br M).length - 1) [] =
        ((Br M).getD ((Br M).length - 1) []).dropLast := by
  have hshape := Br_Pred_core_nontrunk M hM hlen hne
  have hcond : ¬Lng ((Br M).getLastD []) ≤ 1 := Nat.not_le_of_lt hlast
  rw [if_neg hcond] at hshape
  have hBrNe : Br M ≠ [] := by
    intro h
    simp [h] at hlast
  have hlastEq := getLastD_eq_getD_last_rp (Br M) hBrNe
  constructor
  · rw [hshape]
    simp only [List.length_append, List.length_dropLast,
      List.length_singleton]
    have hpos := List.length_pos_of_ne_nil hBrNe
    omega
  · unfold List.getD
    rw [hshape]
    have hidx : (Br M).length - 1 = (Br M).dropLast.length := by
      simp
    rw [List.getElem?_append_right (by rw [hidx])]
    have hz : (Br M).length - 1 - (Br M).dropLast.length = 0 := by omega
    simp only [List.getElem?_singleton, if_pos hz, Option.getD_some]
    rw [hlastEq, List.getD_eq_getElem?_getD]

private theorem redNJ_eq_branchNP (M : PS) (J : ℕ) :
    redNJ M J =
      (entry M 0 0 + (Joints M).getD J 0 + 1,
        entry M 1 0 + branchNP M J) :: ((Br M).getD J []).tail := by
  rfl

theorem redNJ_Pred_interior (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (J : ℕ) (hJ : J < (Br M).length - 1)
    (hJP : J < (Br (Pred M)).length) :
    redNJ (Pred M) J = redNJ M J := by
  have hblock := Br_block_Pred_interior M hM hlen hne J hJ
  have hjoint := Joints_Pred_core M hM hmono hlen hne J hJP
  have hnp := branchNP_Pred_core M hM hmono hcore.2 hlen hne J hJP
  have he0 := entry_Pred_zero M 0 hlen
  have he1 := entry_Pred_zero M 1 hlen
  rw [redNJ_eq_branchNP, redNJ_eq_branchNP,
    he0, he1, hjoint, hnp, hblock]

theorem redNJ_Pred_last (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (hlast : 1 < Lng ((Br M).getLastD [])) :
    redNJ (Pred M) ((Br M).length - 1) =
      Pred (redNJ M ((Br M).length - 1)) := by
  let J := (Br M).length - 1
  have hlastData := Br_lastblock_Pred M hM hlen hne hlast
  have hBrNe : Br M ≠ [] := by
    intro h
    simp [h] at hlast
  have hJM : J < (Br M).length := by simp [J, List.length_pos_of_ne_nil hBrNe]
  have hJP : J < (Br (Pred M)).length := by rw [hlastData.1]; exact hJM
  have hblock : (Br (Pred M)).getD J [] =
      ((Br M).getD J []).dropLast := by simpa [J] using hlastData.2
  have hjoint := Joints_Pred_core M hM hmono hlen hne J hJP
  have hnp := branchNP_Pred_core M hM hmono hcore.2 hlen hne J hJP
  have he0 := entry_Pred_zero M 0 hlen
  have he1 := entry_Pred_zero M 1 hlen
  have hBgt : 1 < Lng ((Br M).getD J []) := by
    rw [← getLastD_eq_getD_last_rp (Br M) hBrNe]
    exact hlast
  have hredLen : 1 < Lng (redNJ M J) := by
    rw [redNJ_length M J (Br_component_TPS M J hM hJM)]
    exact hBgt
  change redNJ (Pred M) J =
    if Lng (redNJ M J) ≤ 1 then redNJ M J else (redNJ M J).dropLast
  rw [if_neg (Nat.not_le_of_lt hredLen)]
  rw [redNJ_eq_branchNP, redNJ_eq_branchNP,
    he0, he1, hjoint, hnp, hblock]
  cases hB : (Br M).getD J [] with
  | nil =>
      change 1 < ((Br M).getD J []).length at hBgt
      rw [hB] at hBgt
      simp at hBgt
  | cons b B =>
      cases B with
      | nil =>
          change 1 < ((Br M).getD J []).length at hBgt
          rw [hB] at hBgt
          simp at hBgt
      | cons b' B => simp

private def branchBlock (M : PS) (J : ℕ) : PS :=
  IncrFirstN (branchE M J) (Red (redNJ M J))

private theorem branchBlock_nonempty (M : PS) (J : ℕ) (hM : TPS M)
    (hJ : J < (Br M).length) : branchBlock M J ≠ [] := by
  have hBT := Br_component_TPS M J hM hJ
  have hNJT : TPS (redNJ M J) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [redNJ_length M J hBT]
    exact List.length_pos_of_ne_nil hBT
  apply List.ne_nil_of_length_pos
  have hpos : 0 < Lng (Red (redNJ M J)) := by
    rw [Lng_Red_invariance (redNJ M J) hNJT]
    exact List.length_pos_of_ne_nil hNJT
  simpa [branchBlock, IncrFirstN_eq_map] using hpos

private theorem branchBlock_length (M : PS) (J : ℕ) (hM : TPS M)
    (hJ : J < (Br M).length) :
    Lng (branchBlock M J) = Lng ((Br M).getD J []) := by
  have hBT := Br_component_TPS M J hM hJ
  have hNJT : TPS (redNJ M J) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [redNJ_length M J hBT]
    exact List.length_pos_of_ne_nil hBT
  simp [branchBlock, IncrFirstN_eq_map,
    Lng_Red_invariance (redNJ M J) hNJT, redNJ_length M J hBT]

private theorem branchBlock_Pred_interior (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (J : ℕ) (hJ : J < (Br M).length - 1)
    (hJP : J < (Br (Pred M)).length) :
    branchBlock (Pred M) J = branchBlock M J := by
  have hjoint := Joints_Pred_core M hM hmono hlen hne J hJP
  have hnp := branchNP_Pred_core M hM hmono hcore.2 hlen hne J hJP
  have hNJ := redNJ_Pred_interior M hM hmono hcore hlen hne J hJ hJP
  have he : branchE (Pred M) J = branchE M J := by
    change (Joints (Pred M)).getD J 0 + 1 - branchNP (Pred M) J =
      (Joints M).getD J 0 + 1 - branchNP M J
    rw [hjoint, hnp]
  simp [branchBlock, he, hNJ]

private theorem branchBlock_Pred_last (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (hlast : 1 < Lng ((Br M).getLastD []))
    (hIH : Red (Pred (redNJ M ((Br M).length - 1))) =
      Pred (Red (redNJ M ((Br M).length - 1)))) :
    branchBlock (Pred M) ((Br M).length - 1) =
      Pred (branchBlock M ((Br M).length - 1)) := by
  let J := (Br M).length - 1
  have hlastData := Br_lastblock_Pred M hM hlen hne hlast
  have hBrNe : Br M ≠ [] := by intro h; simp [h] at hlast
  have hJM : J < (Br M).length := by simp [J, List.length_pos_of_ne_nil hBrNe]
  have hJP : J < (Br (Pred M)).length := by rw [hlastData.1]; exact hJM
  have hjoint := Joints_Pred_core M hM hmono hlen hne J hJP
  have hnp := branchNP_Pred_core M hM hmono hcore.2 hlen hne J hJP
  have hNJ := redNJ_Pred_last M hM hmono hcore hlen hne hlast
  have he : branchE (Pred M) J = branchE M J := by
    change (Joints (Pred M)).getD J 0 + 1 - branchNP (Pred M) J =
      (Joints M).getD J 0 + 1 - branchNP M J
    rw [hjoint, hnp]
  have hBT := Br_component_TPS M J hM hJM
  have hNJT : TPS (redNJ M J) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [redNJ_length M J hBT]
    exact List.length_pos_of_ne_nil hBT
  have hRedLong : 1 < Lng (Red (redNJ M J)) := by
    rw [Lng_Red_invariance (redNJ M J) hNJT,
      redNJ_length M J hBT]
    rw [← getLastD_eq_getD_last_rp (Br M) hBrNe]
    exact hlast
  change IncrFirstN (branchE (Pred M) J) (Red (redNJ (Pred M) J)) =
    Pred (IncrFirstN (branchE M J) (Red (redNJ M J)))
  rw [he, hNJ, show Red (Pred (redNJ M J)) =
    Pred (Red (redNJ M J)) by simpa [J] using hIH,
    IncrFirstN_Pred _ _ hRedLong]

private theorem branchTail_Pred_core (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hlen : 1 < Lng M) (hne : TrMax M ≠ Lng M - 1)
    (hIH : ∀ J, J < (Br M).length →
      Red (Pred (redNJ M J)) = Pred (Red (redNJ M J))) :
    (List.range (Br (Pred M)).length).flatMap (branchBlock (Pred M)) =
      ((List.range (Br M).length).flatMap (branchBlock M)).dropLast := by
  have hBrNe : Br M ≠ [] := by
    rw [Br, if_neg hne]
    exact P_nonempty _
  have hnpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrNe
  have hJlast : (Br M).length - 1 < (Br M).length := by omega
  have hrange : List.range (Br M).length =
      List.range ((Br M).length - 1) ++ [(Br M).length - 1] := by
    nth_rewrite 1 [show (Br M).length = (Br M).length - 1 + 1 by omega]
    exact List.range_succ
  have hlastBT := Br_component_TPS M ((Br M).length - 1) hM hJlast
  have hlastPos : 0 < Lng ((Br M).getLastD []) := by
    rw [getLastD_eq_getD_last_rp (Br M) hBrNe]
    exact List.length_pos_of_ne_nil hlastBT
  have hlastBlockNe := branchBlock_nonempty M ((Br M).length - 1) hM hJlast
  by_cases hsmall : Lng ((Br M).getLastD []) ≤ 1
  · have hlastLen : Lng ((Br M).getLastD []) = 1 := by omega
    have hshape := Br_Pred_core_nontrunk M hM hlen hne
    rw [if_pos hsmall] at hshape
    have hlenP : (Br (Pred M)).length = (Br M).length - 1 := by
      rw [hshape]
      simp
    have hinterior :
        (List.range ((Br M).length - 1)).flatMap (branchBlock (Pred M)) =
          (List.range ((Br M).length - 1)).flatMap (branchBlock M) := by
      apply List.flatMap_congr
      intro J hJmem
      have hJ := List.mem_range.mp hJmem
      apply branchBlock_Pred_interior M hM hmono hcore hlen hne J hJ
      rw [hlenP]
      exact hJ
    have hblockLen : Lng (branchBlock M ((Br M).length - 1)) = 1 := by
      rw [branchBlock_length M ((Br M).length - 1) hM hJlast,
        ← getLastD_eq_getD_last_rp (Br M) hBrNe]
      exact hlastLen
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hblockLen
    calc
      (List.range (Br (Pred M)).length).flatMap (branchBlock (Pred M)) =
          (List.range ((Br M).length - 1)).flatMap (branchBlock M) := by
            rw [hlenP, hinterior]
      _ = ((List.range ((Br M).length - 1)).flatMap (branchBlock M) ++
          branchBlock M ((Br M).length - 1)).dropLast := by
            rw [dropLast_append_of_right_ne _ _ hlastBlockNe]
            simp [hx]
      _ = ((List.range (Br M).length).flatMap (branchBlock M)).dropLast := by
            rw [hrange, List.flatMap_append]
            simp
  · have hlast : 1 < Lng ((Br M).getLastD []) := by omega
    have hlastData := Br_lastblock_Pred M hM hlen hne hlast
    have hlenP : (Br (Pred M)).length = (Br M).length := hlastData.1
    have hinterior :
        (List.range ((Br M).length - 1)).flatMap (branchBlock (Pred M)) =
          (List.range ((Br M).length - 1)).flatMap (branchBlock M) := by
      apply List.flatMap_congr
      intro J hJmem
      have hJ := List.mem_range.mp hJmem
      apply branchBlock_Pred_interior M hM hmono hcore hlen hne J hJ
      rw [hlenP]
      omega
    have hblockLong : 1 < Lng (branchBlock M ((Br M).length - 1)) := by
      rw [branchBlock_length M ((Br M).length - 1) hM hJlast,
        ← getLastD_eq_getD_last_rp (Br M) hBrNe]
      exact hlast
    have hpredBlock : Pred (branchBlock M ((Br M).length - 1)) =
        (branchBlock M ((Br M).length - 1)).dropLast := by
      simp [Pred, Nat.not_le_of_lt hblockLong]
    have hlastEq : branchBlock (Pred M) ((Br M).length - 1) =
        (branchBlock M ((Br M).length - 1)).dropLast := by
      rw [branchBlock_Pred_last M hM hmono hcore hlen hne hlast
        (hIH ((Br M).length - 1) hJlast), hpredBlock]
    calc
      (List.range (Br (Pred M)).length).flatMap (branchBlock (Pred M)) =
          (List.range ((Br M).length - 1)).flatMap (branchBlock (Pred M)) ++
            branchBlock (Pred M) ((Br M).length - 1) := by
              rw [hlenP, hrange, List.flatMap_append]
              simp
      _ = (List.range ((Br M).length - 1)).flatMap (branchBlock M) ++
          (branchBlock M ((Br M).length - 1)).dropLast := by
            rw [hinterior, hlastEq]
      _ = ((List.range ((Br M).length - 1)).flatMap (branchBlock M) ++
          branchBlock M ((Br M).length - 1)).dropLast := by
            exact (dropLast_append_of_right_ne _ _ hlastBlockNe).symm
      _ = ((List.range (Br M).length).flatMap (branchBlock M)).dropLast := by
            rw [hrange, List.flatMap_append]
            simp

private theorem Red_core_eq_diag_branchTail (M : PS) (hM : TPS M)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hnm : multiT M = false) :
    Red M = diagSeq 0 (TrMax M) ++
      (List.range (Br M).length).flatMap (branchBlock M) := by
  by_cases hz : zeroT M = true
  · have hL : Lng M = 1 := by
      have hh := hz
      simp [zeroT] at hh
      exact hh.1
    have ht : TrMax M = 0 := by
      have := TrMax_bound M hM
      omega
    have hBr : Br M = [] := by simp [Br, hL, ht]
    rw [Red_zero_mr M hz, ht, hBr]
    simp [diagSeq]
  · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
    have hmono : monoT M = true := by
      have hh := hnm
      simp [multiT, hz'] at hh
      exact hh
    by_cases ht : TrMax M = Lng M - 1
    · rw [Red_core_trunk_ri M hM hmono hcore ht, ht]
      simp [Br, ht]
    · simpa [branchBlock] using
        Red_core_nontrunk_mr M hM hmono hcore ht

theorem Red_Pred_core_nontrunk (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hne : TrMax M ≠ Lng M - 1)
    (hIH : ∀ J, J < (Br M).length →
      Red (Pred (redNJ M J)) = Pred (Red (redNJ M J))) :
    Red (Pred M) = Pred (Red M) := by
  have hlen : 1 < Lng M := by
    have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
    have ht := TrMax_bound M hM
    omega
  have hPredT := Pred_TPS M hM
  have hcoreP : entry (Pred M) 0 0 = 0 ∧ entry (Pred M) 1 0 = 0 := by
    constructor
    · simpa [hcore.1] using entry_Pred_zero M 0 hlen
    · simpa [hcore.2] using entry_Pred_zero M 1 hlen
  have hnm : multiT M = false := by simp [multiT, hmono]
  have hnmP := nonmulti_Pred M hM hnm hlen
  have htrP := TrMax_Pred_nontrunk M hM hlen hne
  let tailM := (List.range (Br M).length).flatMap (branchBlock M)
  let tailP := (List.range (Br (Pred M)).length).flatMap (branchBlock (Pred M))
  have hredM : Red M = diagSeq 0 (TrMax M) ++ tailM := by
    simpa [tailM] using Red_core_eq_diag_branchTail M hM hcore hnm
  have hredP : Red (Pred M) = diagSeq 0 (TrMax M) ++ tailP := by
    have hh := Red_core_eq_diag_branchTail (Pred M) hPredT hcoreP hnmP
    rw [htrP] at hh
    simpa [tailP] using hh
  have hBrNe : Br M ≠ [] := by
    rw [Br, if_neg hne]
    exact P_nonempty _
  have hnpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrNe
  have htailNe : tailM ≠ [] := by
    have hblockNe := branchBlock_nonempty M 0 hM hnpos
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (branchBlock M 0) hblockNe
    apply List.ne_nil_of_mem
    change x ∈ (List.range (Br M).length).flatMap (branchBlock M)
    exact List.mem_flatMap.mpr ⟨0, List.mem_range.mpr hnpos, hx⟩
  have hredLong : 1 < Lng (Red M) := by
    rw [Lng_Red_invariance M hM]
    exact hlen
  have hpredRed : Pred (Red M) = diagSeq 0 (TrMax M) ++ tailM.dropLast := by
    calc
      Pred (Red M) = (Red M).dropLast := by
        simp [Pred, Nat.not_le_of_lt hredLong]
      _ = (diagSeq 0 (TrMax M) ++ tailM).dropLast := by rw [hredM]
      _ = diagSeq 0 (TrMax M) ++ tailM.dropLast :=
        dropLast_append_of_right_ne _ _ htailNe
  have htail := branchTail_Pred_core M hM hmono hcore hlen hne hIH
  change tailP = tailM.dropLast at htail
  rw [hredP, hpredRed, htail]

private theorem dropLast_flatMap (Q : List PS) (f : PS → PS)
    (hQ : Q ≠ []) (hf : ∀ X ∈ Q, f X ≠ []) :
    (Q.flatMap f).dropLast =
      Q.dropLast.flatMap f ++ (f (Q.getLastD [])).dropLast := by
  have hlastMem : Q.getLastD [] ∈ Q := by
    cases h : Q with
    | nil => exact (hQ h).elim
    | cons A R => simp [List.getLastD]
  have hlastNe : f (Q.getLastD []) ≠ [] := hf _ hlastMem
  have hdecomp : Q.dropLast ++ [Q.getLastD []] = Q := by
    cases h : Q with
    | nil => exact (hQ h).elim
    | cons A R =>
        simpa [List.getLastD] using List.dropLast_append_getLast
          (show A :: R ≠ [] by simp)
  calc
    (Q.flatMap f).dropLast =
        ((Q.dropLast ++ [Q.getLastD []]).flatMap f).dropLast := by rw [hdecomp]
    _ = (Q.dropLast.flatMap f ++ f (Q.getLastD [])).dropLast := by simp
    _ = Q.dropLast.flatMap f ++ (f (Q.getLastD [])).dropLast :=
      dropLast_append_of_right_ne _ _ hlastNe

theorem Red_multi_rp (M : PS) (hM : TPS M)
    (hmulti : multiT M = true) :
    Red M = (P M).flatMap Red := by
  have hz : zeroT M ≠ true := by
    intro hz
    simp [multiT, hz] at hmulti
  unfold Red
  rw [RedAux, if_neg hz, if_pos hmulti]
  apply List.flatMap_congr
  intro Q hQ
  have hQT : TPS Q := P_member_TPS_rp M Q hM hQ
  apply RedAux_stable Q hQT (nu M)
  exact nu_Pblock_lt M Q hM hmulti hQ

theorem Red_eq_flatMap_P (M : PS) (hM : TPS M) :
    Red M = (P M).flatMap Red := by
  by_cases hmulti : multiT M = true
  · exact Red_multi_rp M hM hmulti
  · have hnm : multiT M = false := Bool.eq_false_of_not_eq_true hmulti
    rw [P_nonmulti_eq M hnm]
    simp

theorem Red_Pred_multi (M : PS) (hM : TPS M)
    (hmulti : multiT M = true)
    (hIH : Red (Pred ((P M).getLastD [])) =
      Pred (Red ((P M).getLastD []))) :
    Red (Pred M) = Pred (Red M) := by
  have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
  have hPredT : TPS (Pred M) := Pred_TPS M hM
  let D := (P M).getLastD []
  have hDmem : D ∈ P M := by simpa [D] using P_getLastD_mem_rp M
  have hDT : TPS D := P_member_TPS_rp M D hM hDmem
  have hredNonempty : ∀ X ∈ P M, Red X ≠ [] := by
    intro X hX
    have hXT := P_member_TPS_rp M X hM hX
    apply List.ne_nil_of_length_pos
    change 0 < Lng (Red X)
    rw [Lng_Red_invariance X hXT]
    exact List.length_pos_of_ne_nil hXT
  have hdropFlat := dropLast_flatMap (P M) Red (P_nonempty M) hredNonempty
  have hredLen : 1 < Lng (Red M) := by
    rw [Lng_Red_invariance M hM]
    exact hlen
  have hPredRed : Pred (Red M) = (Red M).dropLast := by
    simp [Pred, Nat.not_le_of_lt hredLen]
  by_cases hDlen : Lng D = 1
  · have hRDlen : Lng (Red D) = 1 := by
      rw [Lng_Red_invariance D hDT, hDlen]
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hRDlen
    calc
      Red (Pred M) = (P (Pred M)).flatMap Red :=
        Red_eq_flatMap_P (Pred M) hPredT
      _ = ((P M).dropLast).flatMap Red := by
        rw [P_Pred_multi M hM hmulti, if_pos (by simpa [D] using hDlen)]
      _ = ((P M).dropLast).flatMap Red ++ (Red D).dropLast := by
        simp [hx]
      _ = ((P M).flatMap Red).dropLast := by
        simpa [D] using hdropFlat.symm
      _ = (Red M).dropLast := by rw [Red_eq_flatMap_P M hM]
      _ = Pred (Red M) := hPredRed.symm
  · have hDpos : 0 < Lng D := List.length_pos_of_ne_nil hDT
    have hDgt : 1 < Lng D := by omega
    have hRDgt : 1 < Lng (Red D) := by
      rw [Lng_Red_invariance D hDT]
      exact hDgt
    have hPredRD : Pred (Red D) = (Red D).dropLast := by
      simp [Pred, Nat.not_le_of_lt hRDgt]
    calc
      Red (Pred M) = (P (Pred M)).flatMap Red :=
        Red_eq_flatMap_P (Pred M) hPredT
      _ = ((P M).dropLast ++ [Pred D]).flatMap Red := by
        rw [P_Pred_multi M hM hmulti, if_neg (by simpa [D] using hDlen)]
      _ = ((P M).dropLast).flatMap Red ++ Red (Pred D) := by simp
      _ = ((P M).dropLast).flatMap Red ++ Pred (Red D) := by
        rw [show Red (Pred D) = Pred (Red D) by simpa [D] using hIH]
      _ = ((P M).dropLast).flatMap Red ++ (Red D).dropLast := by rw [hPredRD]
      _ = ((P M).flatMap Red).dropLast := by
        simpa [D] using hdropFlat.symm
      _ = (Red M).dropLast := by rw [Red_eq_flatMap_P M hM]
      _ = Pred (Red M) := hPredRed.symm

/-- §6.5: reduction commutes with deleting the final column. -/
theorem Red_Pred (M : PS) (hM : TPS M) :
    Red (Pred M) = Pred (Red M) := by
  generalize hn : nu M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      by_cases hlen : 1 < Lng M
      · have hz : zeroT M = false := by
          simp [zeroT]
          omega
        by_cases hmulti : multiT M = true
        · let D := (P M).getLastD []
          have hDmem : D ∈ P M := by simpa [D] using P_getLastD_mem_rp M
          have hDT := P_member_TPS_rp M D hM hDmem
          have hdesc := nu_Pblock_lt M D hM hmulti hDmem
          have hcomm : Red (Pred D) = Pred (Red D) :=
            ih (nu D) (by omega) D hDT rfl
          exact Red_Pred_multi M hM hmulti (by simpa [D] using hcomm)
        · have hmulti' : multiT M = false :=
            Bool.eq_false_of_not_eq_true hmulti
          have hmono : monoT M = true := by
            have hh := hmulti'
            simp [multiT, hz] at hh
            exact hh
          by_cases hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0
          · by_cases htrunk : TrMax M = Lng M - 1
            · exact Red_Pred_core_trunk M hM hmono hcore htrunk
            · apply Red_Pred_core_nontrunk M hM hmono hcore htrunk
              intro J hJ
              have hBT := Br_component_TPS M J hM hJ
              have hNJT : TPS (redNJ M J) := by
                apply List.ne_nil_of_length_pos
                change 0 < Lng (redNJ M J)
                rw [redNJ_length M J hBT]
                exact List.length_pos_of_ne_nil hBT
              have hdesc := nu_redNJ_lt M J hM hmono hcore hJ
              exact ih (nu (redNJ M J)) (by omega) (redNJ M J) hNJT rfl
          · have hCT := coreReduce_TPS M hM
            have hdesc := nu_coreReduce_lt M hM hmono hcore
            have hcomm : Red (Pred (coreReduce M)) =
                Pred (Red (coreReduce M)) :=
              ih (nu (coreReduce M)) (by omega) (coreReduce M) hCT rfl
            by_cases hm : entry M 1 0 = 0
            · exact Red_Pred_noncore_zero M hM hmono hcore hm hcomm
            · exact Red_Pred_noncore_positive M hM hmono hlen
                (Nat.pos_of_ne_zero hm) hcomm
      · have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
        have hL : Lng M = 1 := by omega
        have hpredM : Pred M = M := by simp [Pred, hL]
        have hredL : Lng (Red M) = 1 := by
          rw [Lng_Red_invariance M hM, hL]
        have hpredRed : Pred (Red M) = Red M := by simp [Pred, hredL]
        rw [hpredM, hpredRed]

#print axioms Red_Pred

end PSS

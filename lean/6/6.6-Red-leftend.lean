import «6».«6.6-condAB-coeff»

/-!
# §6.6 補題（`Red` と左端の関係）

- 原文: `tmp/content.md` の「補題（Red と左端の関係）」
- 訂正: なし
- Isabelle: `m_6_6_Red_leftend_1`, `m_6_6_Red_leftend_2`
- 依存: §6.5 `Red` の分岐方程式、§6.4 `P_IdxSum`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem Red_multi_leftend_eq (M : PS) (hM : TPS M)
    (hmulti : multiT M = true) : Red M = (P M).flatMap Red := by
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

private theorem redPositiveOut_entry1_head (M N : PS)
    (hmj : entry M 1 0 ≤ Lng N - 1)
    (hmono : monoT (seg N (entry M 1 0) (Lng N - 1)) = true) :
    entry (redPositiveOut_ri M N) 1 0 =
      entry N 1 (entry M 1 0) := by
  let m := entry M 1 0
  let jN := Lng N - 1
  have hlen : 0 < jN + 1 - m := by
    dsimp [m, jN]
    omega
  unfold redPositiveOut_ri
  dsimp only
  rw [if_pos (by simp [hmj, hmono])]
  let R := (List.range' m (jN + 1 - m)).map (fun j =>
    (entry N 0 j - entry N 0 m + entry N 1 m, entry N 1 j))
  change entry R 1 0 = entry N 1 m
  have hRpos : 0 < Lng R := by simp [R, hlen]
  have hget : R[0] = (entry N 1 m, entry N 1 m) := by
    simp [R, List.getElem_map, List.getElem_range']
  simp [entry, List.getElem?_eq_getElem hRpos, hget]

private theorem redPositiveOut_head_diag_rl (M N : PS)
    (hmj : entry M 1 0 ≤ Lng N - 1)
    (hmono : monoT (seg N (entry M 1 0) (Lng N - 1)) = true) :
    entry (redPositiveOut_ri M N) 0 0 =
      entry (redPositiveOut_ri M N) 1 0 := by
  let m := entry M 1 0
  let jN := Lng N - 1
  unfold redPositiveOut_ri
  dsimp only
  rw [if_pos (by simp [hmj, hmono])]
  have hlen : 0 < jN + 1 - m := by
    dsimp [m, jN]
    omega
  let R := (List.range' m (jN + 1 - m)).map (fun j =>
    (entry N 0 j - entry N 0 m + entry N 1 m, entry N 1 j))
  change entry R 0 0 = entry R 1 0
  have hRpos : 0 < Lng R := by simp [R, hlen]
  have hget : R[0] = (entry N 1 m, entry N 1 m) := by
    simp [R, List.getElem_map, List.getElem_range']
  simp [entry, List.getElem?_eq_getElem hRpos, hget]

private theorem nextR1_consecutive_rl (M : PS) (j : ℕ)
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

private theorem entry_diagSeq_general (u d i k : ℕ) (hk : k ≤ d) :
    entry (diagSeq u (u + d)) i k = u + k := by
  have hlen : k < Lng (diagSeq u (u + d)) := by
    simp [diagSeq]
    omega
  have hget : (diagSeq u (u + d))[k] = (u + k, u + k) := by
    simp [diagSeq, List.getElem_map, List.getElem_range']
  simp [entry, List.getElem?_eq_getElem hlen, hget]

private theorem getElem_eq_entries_rl (M : PS) (j : ℕ) (hj : j < Lng M) :
    M[j] = (entry M 0 j, entry M 1 j) := by
  apply Prod.ext
  · exact (entry0_eq_fst_getElem_mr M j hj).symm
  · simp [entry, List.getElem?_eq_getElem hj]

/-- `Red` preserves the row-one coefficient of the first column. -/
theorem Red_leftend_row1 (M : PS) (hM : TPS M) :
    entry (Red M) 1 0 = entry M 1 0 := by
  generalize hn : nu M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      by_cases hz : zeroT M = true
      · have hm10 : entry M 1 0 = 0 := by
          have hh := hz
          simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
          exact hh.2
        rw [Red_zero_mr M hz, hm10]
        simp [entry]
      · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
        by_cases hmulti : multiT M = true
        · have hPpos : 0 < (P M).length :=
            List.length_pos_of_ne_nil (P_nonempty M)
          let Q := (P M).getD 0 []
          have hQmem : Q ∈ P M := by
            have hget : Q = (P M)[0] := by
              simpa [Q] using getD_eq_getElem_idx (P M) [] hPpos
            rw [hget]
            exact List.getElem_mem hPpos
          have hQT : TPS Q := by
            have hQpos := P_component_nonempty M 0 hM hPpos
            simpa [Q] using List.ne_nil_of_length_pos hQpos
          have hdesc := nu_Pblock_lt M Q hM hmulti hQmem
          have hih : entry (Red Q) 1 0 = entry Q 1 0 :=
            ih (nu Q) (by omega) Q hQT rfl
          have hQpos : 0 < Lng Q := List.length_pos_of_ne_nil hQT
          have hRQpos : 0 < Lng (Red Q) := by
            rw [Lng_Red_invariance Q hQT]
            exact hQpos
          have hPdecomp : P M = Q :: (P M).tail := by
            cases hp : P M with
            | nil => simp [hp] at hPpos
            | cons A As => simp [Q, hp]
          have hheadRed : entry (Red M) 1 0 = entry (Red Q) 1 0 := by
            rw [Red_multi_leftend_eq M hM hmulti, hPdecomp]
            simp only [List.flatMap_cons]
            exact entry_append_left_mr (Red Q) ((P M).tail.flatMap Red)
              1 0 hRQpos
          have hJle : 0 ≤ (P M).length - 1 := Nat.zero_le _
          have hcomp := P_IdxSum M 0 hM hJle
          have hsegpos : 0 < Lng (seg M
              ((IdxSum (P M)).getD 0 0)
              ((IdxSum (P M)).getD 1 0 - 1)) := by
            rw [← hcomp]
            simpa [Q] using hQpos
          have hQhead : entry Q 1 0 = entry M 1 0 := by
            change entry ((P M).getD 0 []) 1 0 = entry M 1 0
            rw [hcomp]
            have he := entry_seg M ((IdxSum (P M)).getD 0 0)
              ((IdxSum (P M)).getD 1 0 - 1) 1 0 hsegpos
            simpa [IdxSum] using he
          exact hheadRed.trans (hih.trans hQhead)
        · have hmulti' : multiT M = false := Bool.eq_false_of_not_eq_true hmulti
          have hmono : monoT M = true := by
            have hh := hmulti'
            simp [multiT, hz'] at hh
            exact hh
          by_cases hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0
          · have he := Red_core_prefix_diag M hmono hcore 1 0 (Nat.zero_le _)
            simpa [hcore.2] using he
          · by_cases hm : entry M 1 0 = 0
            · have hCT := coreReduce_TPS M hM
              have hdesc := nu_coreReduce_lt M hM hmono hcore
              have hih : entry (Red (coreReduce M)) 1 0 =
                  entry (coreReduce M) 1 0 :=
                ih (nu (coreReduce M)) (by omega) (coreReduce M) hCT rfl
              have hred : Red M = Red (coreReduce M) := by
                simpa [hm] using Red_noncore_ri M hM hmono hcore
              have hChead : entry (coreReduce M) 1 0 = entry M 1 0 := by
                have hMpos := List.length_pos_of_ne_nil hM
                change 0 < Lng M at hMpos
                have hCpos : 0 < Lng (coreReduce M) := by
                  simpa [coreReduce, hm] using hMpos
                have hget : (coreReduce M)[0] =
                    (entry M 0 0 - entry M 0 0, entry M 1 0) := by
                  simp [coreReduce, hm, List.getElem_map, List.getElem_range]
                simp [entry, List.getElem?_eq_getElem hCpos, hget]
              rw [hred]
              exact hih.trans hChead
            · have hpos : 0 < entry M 1 0 := Nat.pos_of_ne_zero hm
              let C := coreReduce M
              let N := Red C
              let m := entry M 1 0
              have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
              have hCL : Lng C = m + Lng M := by
                simp [C, m, coreReduce, hm, diagSeq, IncrFirstN_eq_map]
                omega
              have hNL : Lng N = m + Lng M := by
                calc
                  Lng N = Lng C := Lng_Red_invariance C hCT
                  _ = m + Lng M := hCL
              have hMpos := List.length_pos_of_ne_nil hM
              change 0 < Lng M at hMpos
              have hmj : m ≤ Lng N - 1 := by rw [hNL]; omega
              have hmonoS : monoT (seg N m (Lng N - 1)) = true := by
                simpa [N, C, m] using
                  (monoT_Red_m10pos M hM hmono hpos).2
              have hred : Red M = redPositiveOut_ri M N := by
                simpa [N, C, hm] using Red_noncore_ri M hM hmono hcore
              have hout := redPositiveOut_entry1_head M N
                (by simpa [m] using hmj) (by simpa [m] using hmonoS)
              have hanchor : entry N 1 m = m := by
                simpa [N, C, m] using
                  redB_prefix_diag M hM hmono hpos 1 (entry M 1 0) (le_refl _)
              rw [hred]
              exact hout.trans hanchor

/-- Reduction gives every non-multi input a diagonal first column.  This is
the first invariant needed for the second-reduct theorem; unlike
`RTPS_mono_head_eq`, it does not assume that the input was already reduced. -/
theorem Red_nonmulti_head_eq (M : PS) (hM : TPS M)
    (hnm : multiT M = false) :
    entry (Red M) 0 0 = entry (Red M) 1 0 := by
  by_cases hz : zeroT M = true
  · rw [Red_zero_mr M hz]
    simp [entry]
  · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
    have hmono : monoT M = true := by
      have hh := hnm
      simp [multiT, hz'] at hh
      exact hh
    by_cases hm : entry M 1 0 = 0
    · by_cases hc0 : entry M 0 0 = 0
      · have hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0 := ⟨hc0, hm⟩
        have hleft : entry (Red M) 0 0 = 0 :=
          Red_core_prefix_diag M hmono hcore 0 0 (Nat.zero_le _)
        rw [Red_leftend_row1 M hM, hleft, hm]
      · let C := coreReduce M
        have hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by
          simp [hc0]
        have hred : Red M = Red C := by
          simpa [C, hm] using Red_noncore_ri M hM hmono hnoncore
        have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
        have hCcore : entry C 0 0 = 0 ∧ entry C 1 0 = 0 := by
          simpa [C] using coreReduce_core M hM
        have hCnm : multiT C = false := by
          simpa [C] using coreReduce_multi_false M hM hmono
        have hRedC0 : entry (Red C) 0 0 = 0 := by
          by_cases hzC : zeroT C = true
          · rw [Red_zero_mr C hzC]
            simp [entry]
          · have hzC' : zeroT C = false := Bool.eq_false_of_not_eq_true hzC
            have hmonoC : monoT C = true := by
              have hh := hCnm
              simp [multiT, hzC'] at hh
              exact hh
            exact Red_core_prefix_diag C hmonoC hCcore 0 0 (Nat.zero_le _)
        calc
          entry (Red M) 0 0 = entry (Red C) 0 0 := by rw [hred]
          _ = 0 := hRedC0
          _ = entry M 1 0 := hm.symm
          _ = entry (Red M) 1 0 := (Red_leftend_row1 M hM).symm
    · have hpos : 0 < entry M 1 0 := by omega
      have hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by
        intro h
        exact hm h.2
      let C := coreReduce M
      let N := Red C
      let m := entry M 1 0
      have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
      have hCL : Lng C = m + Lng M := by
        simp [C, m, coreReduce, hm, diagSeq, IncrFirstN_eq_map]
        omega
      have hNL : Lng N = m + Lng M := by
        calc
          Lng N = Lng C := Lng_Red_invariance C hCT
          _ = m + Lng M := hCL
      have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      have hmj : m ≤ Lng N - 1 := by rw [hNL]; omega
      have hmonoS : monoT (seg N m (Lng N - 1)) = true := by
        simpa [N, C, m] using (monoT_Red_m10pos M hM hmono hpos).2
      have hdiag : entry (redPositiveOut_ri M N) 0 0 =
          entry (redPositiveOut_ri M N) 1 0 := by
        apply redPositiveOut_head_diag_rl M N
        · simpa [m] using hmj
        · simpa [m] using hmonoS
      have hred : Red M = redPositiveOut_ri M N := by
        simpa [N, C, hm] using Red_noncore_ri M hM hmono hnoncore
      rw [hred]
      exact hdiag

/-- A leading diagonal prefix of a mono sequence is copied by `Red`. -/
theorem Red_leading_diag (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (j₀ u : ℕ)
    (hj₀ : j₀ ≤ Lng M - 1)
    (hdiag : seg M 0 j₀ = diagSeq u (j₀ + u)) :
    (Red M)[j₀]'(by
      change j₀ < Lng (Red M)
      rw [Lng_Red_invariance M hM]
      have hp := List.length_pos_of_ne_nil hM
      change 0 < Lng M at hp
      omega) = (j₀ + u, j₀ + u) := by
  have hMpos := List.length_pos_of_ne_nil hM
  change 0 < Lng M at hMpos
  have hj₀L : j₀ < Lng M := by omega
  have hprefix : ∀ i k, k ≤ j₀ → entry M i k = u + k := by
    intro i k hk
    have hkseg : k < Lng (seg M 0 j₀) := by simp; omega
    calc
      entry M i k = entry (seg M 0 j₀) i k := by
        simpa using (entry_seg M 0 j₀ i k hkseg).symm
      _ = entry (diagSeq u (j₀ + u)) i k := by rw [hdiag]
      _ = u + k := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          entry_diagSeq_general u j₀ i k hk
  have hm00 : entry M 0 0 = u := by simpa using hprefix 0 0 (Nat.zero_le _)
  have hm10 : entry M 1 0 = u := by simpa using hprefix 1 0 (Nat.zero_le _)
  have htrM : j₀ ≤ TrMax M := by
    apply le_TrMax_intro_wd M j₀ hM
    intro j hj
    apply nextR1_consecutive_rl M j
    · omega
    · rw [hprefix 0 j (by omega), hprefix 0 (j + 1) (by omega)]
      omega
    · rw [hprefix 1 j (by omega), hprefix 1 (j + 1) (by omega)]
      omega
  have hjR : j₀ < Lng (Red M) := by
    rw [Lng_Red_invariance M hM]
    exact hj₀L
  by_cases hu : u = 0
  · have hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0 := by
      simp [hm00, hm10, hu]
    have he0 := Red_core_prefix_diag M hmono hcore 0 j₀ htrM
    have he1 := Red_core_prefix_diag M hmono hcore 1 j₀ htrM
    calc
      (Red M)[j₀] = (entry (Red M) 0 j₀, entry (Red M) 1 j₀) :=
        getElem_eq_entries_rl (Red M) j₀ hjR
      _ = (j₀ + u, j₀ + u) := by simp [he0, he1, hu]
  · have hupos : 0 < u := Nat.pos_of_ne_zero hu
    have hm : entry M 1 0 ≠ 0 := by simpa [hm10] using hu
    let D := diagSeq 0 (u - 1)
    let R := IncrFirstN u M
    let C := coreReduce M
    let N := Red C
    have hDlen : Lng D = u := by simp [D, diagSeq]; omega
    have hCeq : C = D ++ R := by
      change coreReduce M = diagSeq 0 (u - 1) ++ IncrFirstN u M
      rw [coreReduce, if_neg hm, hm10]
    have hCL : Lng C = u + Lng M := by
      rw [hCeq]
      simp [hDlen, R, IncrFirstN_eq_map]
    have hCT : TPS C := by
      apply List.ne_nil_of_length_pos
      change 0 < Lng C
      rw [hCL]
      omega
    have hCcore : entry C 0 0 = 0 ∧ entry C 1 0 = 0 := by
      simpa [C] using coreReduce_core M hM
    have hCmono : monoT C = true := by
      have hmultiC : multiT C = false := by
        simpa [C] using coreReduce_multi_false M hM hmono
      have hzC : zeroT C = false := by
        have hL : 1 < Lng C := by rw [hCL]; omega
        simp [zeroT]
        omega
      have hh := hmultiC
      simp [multiT, hzC] at hh
      exact hh
    have hC1 : ∀ p, p ≤ u + j₀ → entry C 1 p = p := by
      intro p hp
      by_cases hpu : p < u
      · rw [hCeq, entry_append_left_mr D R 1 p (by simpa [hDlen] using hpu)]
        simpa [D] using entry_diagSeq_zero_mr (u - 1) 1 p (by omega)
      · let q := p - u
        have hq : q ≤ j₀ := by simp [q]; omega
        have hqL : q < Lng M := hq.trans_lt hj₀L
        rw [hCeq, entry_append_right_mr D R 1 p (by rw [hDlen]; omega), hDlen]
        change entry R 1 (p - u) = p
        rw [show p - u = q by rfl]
        have hR1 : entry R 1 q = entry M 1 q := by
          simpa [R] using (entry_IncrFirstN_one u M q)
        rw [hR1, hprefix 1 q hq]
        have hpform : u + q = p := by simp [q]; omega
        exact hpform
    have hC0pre : ∀ p, p < u → entry C 0 p = p := by
      intro p hp
      rw [hCeq, entry_append_left_mr D R 0 p (by simpa [hDlen] using hp)]
      simpa [D] using entry_diagSeq_zero_mr (u - 1) 0 p (by omega)
    have hC0tail : ∀ q, q ≤ j₀ → entry C 0 (u + q) = u + q + u := by
      intro q hq
      have hqL : q < Lng M := hq.trans_lt hj₀L
      rw [hCeq, entry_append_right_mr D R 0 (u + q)
        (by rw [hDlen]; omega), hDlen]
      simp only [Nat.add_sub_cancel_left]
      have hR0 : entry R 0 q = entry M 0 q + u := by
        simpa [R] using (entry_IncrFirstN_zero u M q hqL)
      rw [hR0, hprefix 0 q hq]
    have htrC : u + j₀ ≤ TrMax C := by
      apply le_TrMax_intro_wd C (u + j₀) hCT
      intro p hp
      have hpL : p + 1 < Lng C := by rw [hCL]; omega
      have he1p := hC1 p (by omega)
      have he1s := hC1 (p + 1) (by omega)
      by_cases hspre : p + 1 < u
      · exact nextR1_consecutive_rl C p hpL
          (by rw [hC0pre p (by omega), hC0pre (p + 1) hspre]; omega)
          (by rw [he1p, he1s]; omega)
      · by_cases hppre : p < u
        · have hpeq : p + 1 = u := by omega
          exact nextR1_consecutive_rl C p hpL
            (by rw [hC0pre p hppre, hpeq, show u = u + 0 by omega,
                hC0tail 0 (Nat.zero_le _)]; omega)
            (by rw [he1p, he1s]; omega)
        · let q := p - u
          have hpform : p = u + q := by simp [q]; omega
          have hq : q < j₀ := by simp [q]; omega
          exact nextR1_consecutive_rl C p hpL
            (by rw [hpform, hC0tail q hq.le,
                show u + q + 1 = u + (q + 1) by omega,
                hC0tail (q + 1) (by omega)]; omega)
            (by rw [he1p, he1s]; omega)
    have hNdiag : ∀ i, entry N i (u + j₀) = u + j₀ := by
      intro i
      simpa [N] using Red_core_prefix_diag C hCmono hCcore i (u + j₀) htrC
    have hNu0 : entry N 0 u = u := by
      simpa [N] using Red_core_prefix_diag C hCmono hCcore 0 u
        (le_trans (by omega) htrC)
    have hNu1 : entry N 1 u = u := by
      simpa [N] using Red_core_prefix_diag C hCmono hCcore 1 u
        (le_trans (by omega) htrC)
    have hNL : Lng N = u + Lng M := by
      calc
        Lng N = Lng C := Lng_Red_invariance C hCT
        _ = u + Lng M := hCL
    have huj : u ≤ Lng N - 1 := by rw [hNL]; omega
    have hposM : 0 < entry M 1 0 := by rw [hm10]; exact hupos
    have hmonoS : monoT (seg N u (Lng N - 1)) = true := by
      simpa [N, C, hm10] using (monoT_Red_m10pos M hM hmono hposM).2
    have hred : Red M = redPositiveOut_ri M N := by
      have hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by
        simp [hm10, hupos.ne']
      have hh := Red_noncore_ri M hM hmono hnoncore
      rw [if_neg hm] at hh
      simpa [N, C] using hh
    let O := redPositiveOut_ri M N
    have hredO : Red M = O := by simpa [O] using hred
    have hjO : j₀ < Lng O := by
      rw [← hredO]
      exact hjR
    have hout : O[j₀]'hjO = (j₀ + u, j₀ + u) := by
      rw [← getD_eq_getElem_idx O (0, 0) hjO]
      unfold O redPositiveOut_ri
      dsimp only
      rw [if_pos (by simp [hm10, huj, hmonoS])]
      let L := (List.range' (entry M 1 0)
        (Lng N - 1 + 1 - entry M 1 0)).map (fun j =>
          (entry N 0 j - entry N 0 (entry M 1 0) +
            entry N 1 (entry M 1 0), entry N 1 j))
      change L.getD j₀ (0, 0) = (j₀ + u, j₀ + u)
      have hjLout : j₀ < Lng L := by
        simp [L, hm10]
        rw [hNL]
        omega
      rw [getD_eq_getElem_idx L (0, 0) hjLout]
      simp only [L, List.getElem_map, List.getElem_range']
      have he0 := hNdiag 0
      have he1 := hNdiag 1
      simp only [one_mul]
      rw [hm10, he0, hNu0, hNu1, he1]
      apply Prod.ext <;> simp <;> omega
    have heq : (Red M)[j₀]'hjR = O[j₀]'hjO := by
      simpa only [hredO]
    exact heq.trans hout

#print axioms Red_leftend_row1
#print axioms Red_leading_diag

end PSS

import «6».«6.5-Red-IncrFirst-invariance»
import «6».«6.5-Red-le-invariance»
import «6».«6.2-multi-criterion»

/-!
# §6.6 補題（簡約性と左端の関係）

- 原文: `tmp/content.md` の「補題（簡約性と左端の関係）」
- Isabelle: `m_6_6_Red_diag_prefix`, `m_6_6_reduced_leftend`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem RTPS_TPS (M : PS) (hM : RTPS M) : TPS M := by
  have hh := hM
  simp only [RTPS, reduced, Bool.and_eq_true, beq_iff_eq] at hh
  simpa [TPS] using hh.1

theorem RTPS_Red_eq (M : PS) (hM : RTPS M) : Red M = M := by
  have hh := hM
  simp only [RTPS, reduced, Bool.and_eq_true, beq_iff_eq] at hh
  exact hh.2

private theorem redPositiveOut_head_diag_dp (M N : PS)
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

/-- The first column of every reduced mono sequence is diagonal. -/
theorem RTPS_mono_head_eq (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) :
    entry M 0 0 = entry M 1 0 := by
  have hM := RTPS_TPS M hR
  have hfix := RTPS_Red_eq M hR
  have hnm : multiT M = false := by simp [multiT, hmono]
  by_cases hm : entry M 1 0 = 0
  · by_cases hc0 : entry M 0 0 = 0
    · omega
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
      have hc0z : entry M 0 0 = 0 := by
        calc
          entry M 0 0 = entry (Red M) 0 0 := by rw [hfix]
          _ = entry (Red C) 0 0 := by rw [hred]
          _ = 0 := hRedC0
      exact False.elim (hc0 hc0z)
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
      apply redPositiveOut_head_diag_dp M N
      · simpa [m] using hmj
      · simpa [m] using hmonoS
    have hred : Red M = redPositiveOut_ri M N := by
      simpa [N, C, hm] using Red_noncore_ri M hM hmono hnoncore
    calc
      entry M 0 0 = entry (Red M) 0 0 := by rw [hfix]
      _ = entry (redPositiveOut_ri M N) 0 0 := by rw [hred]
      _ = entry (redPositiveOut_ri M N) 1 0 := hdiag
      _ = entry (Red M) 1 0 := by rw [hred]
      _ = entry M 1 0 := by rw [hfix]

private theorem nextR1_consecutive_dp (M : PS) (j : ℕ)
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

private theorem entry_diag_append_lo (k : ℕ) (Y : PS) (i j : ℕ)
    (hj : j ≤ k) :
    entry (diagSeq 0 k ++ Y) i j = j := by
  rw [entry_append_left_mr]
  · exact entry_diagSeq_zero_mr k i j hj
  · simp [diagSeq]
    omega

private theorem entry_diag_append_hi (k : ℕ) (Y : PS) (i a : ℕ)
    (ha : a < Lng Y) :
    entry (diagSeq 0 k ++ Y) i (k + 1 + a) = entry Y i a := by
  have hDlen : Lng (diagSeq 0 k) = k + 1 := by simp [diagSeq]
  rw [entry_append_right_mr (diagSeq 0 k) Y i (k + 1 + a) (by omega),
    hDlen]
  congr 1
  omega

private theorem bumpAt_diag_append (Y : PS) (k : ℕ) (hY : TPS Y)
    (hmono : monoT Y = true) (hdom : k + 1 ≤ entry Y 0 0) :
    bumpAt (diagSeq 0 k ++ Y) (k + 1) =
      diagSeq 0 k ++ IncrFirst Y := by
  simp only [bumpAt, List.map_append, IncrFirst]
  congr 1
  · calc
      List.map (fun p => (bumpV (k + 1) p.1, p.2)) (diagSeq 0 k) =
          List.map id (diagSeq 0 k) := by
        apply List.map_congr_left
        intro p hp
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
        simp only [Prod.fst]
        have hjlt : j < k + 1 := by simpa [diagSeq] using hj
        simp [bumpV, hjlt]
      _ = diagSeq 0 k := List.map_id _
  · apply List.map_congr_left
    intro p hp
    obtain ⟨j, hj, hpj⟩ := List.mem_iff_getElem.mp hp
    have hjL : j < Lng Y := by simpa using hj
    have hmin := mono_row0_min_mr Y hY hmono j hjL
    have hfst : p.1 = entry Y 0 j := by
      rw [← hpj]
      exact (entry0_eq_fst_getElem_mr Y j hjL).symm
    apply Prod.ext
    · simp only [Prod.fst]
      rw [hfst]
      simp [bumpV, show ¬entry Y 0 j < k + 1 by omega]
    · rfl

private theorem cutOK_diag_append (Y : PS) (k : ℕ) (hY : TPS Y)
    (hmono : monoT Y = true)
    (hr0 : k < entry Y 0 0) (hr1 : k < entry Y 1 0) :
    cutOK (diagSeq 0 k ++ Y) (k + 1) := by
  let A := diagSeq 0 k ++ Y
  have hAT : TPS A := by
    apply List.ne_nil_of_length_pos
    simp [A, diagSeq]
  have hYpos : 0 < Lng Y := List.length_pos_of_ne_nil hY
  have hAL : Lng A = k + 1 + Lng Y := by simp [A, diagSeq]
  have htr : k + 1 ≤ TrMax A := by
    apply le_TrMax_intro_wd A (k + 1) hAT
    intro j hj
    apply nextR1_consecutive_dp A j
    · rw [hAL]
      omega
    · by_cases hjk : j < k
      · rw [entry_diag_append_lo k Y 0 j (by omega),
          entry_diag_append_lo k Y 0 (j + 1) (by omega)]
        omega
      · have hjeq : j = k := by omega
        subst j
        rw [entry_diag_append_lo k Y 0 k le_rfl,
          show k + 1 = k + 1 + 0 by omega,
          entry_diag_append_hi k Y 0 0 hYpos]
        omega
    · by_cases hjk : j < k
      · rw [entry_diag_append_lo k Y 1 j (by omega),
          entry_diag_append_lo k Y 1 (j + 1) (by omega)]
        omega
      · have hjeq : j = k := by omega
        subst j
        rw [entry_diag_append_lo k Y 1 k le_rfl,
          show k + 1 = k + 1 + 0 by omega,
          entry_diag_append_hi k Y 1 0 hYpos]
        omega
  constructor
  · omega
  · intro j hjtr hjL
    have hjtrA : TrMax A < j := by simpa [A] using hjtr
    have hjpref : k + 1 ≤ j := by omega
    let a := j - (k + 1)
    have hja : j = k + 1 + a := by dsimp [a]; omega
    have haY : a < Lng Y := by rw [hja, hAL] at hjL; omega
    rw [hja, entry_diag_append_hi k Y 0 a haY]
    exact hr0.trans_le (mono_row0_min_mr Y hY hmono a haY)

private theorem diag_append_multi_false (Y : PS) (k : ℕ) (hY : TPS Y)
    (hmono : monoT Y = true) (hr0 : k < entry Y 0 0) :
    multiT (diagSeq 0 k ++ Y) = false := by
  let A := diagSeq 0 k ++ Y
  have hAT : TPS A := by
    apply List.ne_nil_of_length_pos
    simp [A, diagSeq]
  have hYpos : 0 < Lng Y := List.length_pos_of_ne_nil hY
  have hAL : Lng A = k + 1 + Lng Y := by simp [A, diagSeq]
  apply (multi_criterion_12 A hAT).mpr
  intro j hjpos hjL
  have hhead : entry A 0 0 = 0 := by
    simpa [A] using entry_diag_append_lo k Y 0 0 (Nat.zero_le _)
  rw [hhead]
  by_cases hjD : j < k + 1
  · have hjk : j ≤ k := by omega
    rw [show entry A 0 j = j by simpa [A] using entry_diag_append_lo k Y 0 j hjk]
    omega
  · let a := j - (k + 1)
    have hja : j = k + 1 + a := by dsimp [a]; omega
    have haY : a < Lng Y := by rw [hja, hAL] at hjL; omega
    rw [show entry A 0 j = entry Y 0 a by
      rw [hja]
      simpa [A] using entry_diag_append_hi k Y 0 a haY]
    exact Nat.zero_lt_of_lt (hr0.trans_le
      (mono_row0_min_mr Y hY hmono a haY))

private theorem monoT_IncrFirst_dp (Y : PS) :
    monoT (IncrFirst Y) = monoT Y := by
  have hzero : zeroT (IncrFirst Y) = zeroT Y := by
    simp only [zeroT, IncrFirst, List.length_map, entry, List.getElem?_map]
    cases h : Y[0]? <;> simp [h]
  simp [monoT, hzero, le_IncrFirst_invariance]

private theorem Red_diag_IncrFirst_step (Y : PS) (k : ℕ) (hY : TPS Y)
    (hmono : monoT Y = true)
    (hr0 : k < entry Y 0 0) (hr1 : k < entry Y 1 0) :
    Red (diagSeq 0 k ++ IncrFirst Y) = Red (diagSeq 0 k ++ Y) := by
  let A := diagSeq 0 k ++ Y
  have hAT : TPS A := by
    apply List.ne_nil_of_length_pos
    simp [A, diagSeq]
  have hcut := cutOK_diag_append Y k hY hmono hr0 hr1
  have hmulti := diag_append_multi_false Y k hY hmono hr0
  have hbump := bumpAt_diag_append Y k hY hmono (by omega)
  rw [← hbump]
  exact Red_bumpAt_of_cutOK_nonmulti A (k + 1) hAT (by simpa [A] using hmulti)
    (by simpa [A] using hcut)

private theorem Red_diag_IncrFirstN (Y : PS) (k n : ℕ) (hY : TPS Y)
    (hmono : monoT Y = true)
    (hr0 : k < entry Y 0 0) (hr1 : k < entry Y 1 0) :
    Red (diagSeq 0 k ++ IncrFirstN n Y) = Red (diagSeq 0 k ++ Y) := by
  induction n generalizing Y with
  | zero => rfl
  | succ n ih =>
      have hIY : TPS (IncrFirst Y) := by simpa [TPS, IncrFirst] using hY
      have hImono : monoT (IncrFirst Y) = true := by
        simpa [monoT_IncrFirst_dp] using hmono
      have hYpos : 0 < Lng Y := List.length_pos_of_ne_nil hY
      have hI0 : entry (IncrFirst Y) 0 0 = entry Y 0 0 + 1 := by
        simp [IncrFirst, entry, hYpos]
      have hI1 : entry (IncrFirst Y) 1 0 = entry Y 1 0 := by
        simp only [IncrFirst, entry, List.getElem?_map]
        cases h : Y[0]? <;> simp [h]
      calc
        Red (diagSeq 0 k ++ IncrFirstN (n + 1) Y) =
            Red (diagSeq 0 k ++ IncrFirstN n (IncrFirst Y)) := by rfl
        _ = Red (diagSeq 0 k ++ IncrFirst Y) :=
          ih (IncrFirst Y) hIY hImono (by omega) (by omega)
        _ = Red (diagSeq 0 k ++ Y) :=
          Red_diag_IncrFirst_step Y k hY hmono hr0 hr1

/-- The diagonal-prefix input and `coreReduce M` have the same reduct. -/
theorem Red_diag_eq_coreReduce (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0)
    (hdom : entry M 1 0 ≤ entry M 0 0) :
    Red (diagSeq 0 (entry M 1 0 - 1) ++ M) = Red (coreReduce M) := by
  let m := entry M 1 0
  have hm : entry M 1 0 ≠ 0 := by omega
  have hform : coreReduce M = diagSeq 0 (m - 1) ++ IncrFirstN m M := by
    simp [coreReduce, hm, m]
  rw [hform]
  symm
  exact Red_diag_IncrFirstN M (m - 1) m hM hmono (by dsimp [m]; omega)
    (by dsimp [m]; omega)

/-- In the positive left-end branch, `Red M` is exactly the suffix of the
reduced core beginning at its diagonal anchor. -/
theorem Red_eq_coreReduce_suffix (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    Red M = seg (Red (coreReduce M)) (entry M 1 0)
      (Lng (Red (coreReduce M)) - 1) := by
  let m := entry M 1 0
  let N := Red (coreReduce M)
  let jN := Lng N - 1
  let S := seg N m jN
  have hm : entry M 1 0 ≠ 0 := by omega
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hCL : Lng (coreReduce M) = m + Lng M := by
    simp [coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
    omega
  have hNL : Lng N = m + Lng M := by
    calc
      Lng N = Lng (coreReduce M) := Lng_Red_invariance (coreReduce M)
        (coreReduce_TPS M hM)
      _ = m + Lng M := hCL
  have hmN : m < Lng N := by rw [hNL]; omega
  have hmj : m ≤ jN := by dsimp [jN]; omega
  have hg := monoT_Red_m10pos M hM hmono hpos
  have hmonoS : monoT S = true := by simpa [N, m, jN, S] using hg.2
  have hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by omega
  have hbranch := Red_noncore_ri M hM hmono hnoncore
  let R := (List.range' m (jN + 1 - m)).map (fun j =>
    (entry N 0 j - entry N 0 m + entry N 1 m, entry N 1 j))
  have hred : Red M = R := by
    rw [hbranch]
    simp only [if_neg hm]
    simp [redPositiveOut_ri, N, m, jN, S, hmj, hmonoS, R]
  have hanchor0 : entry N 0 m = m := by
    simpa [N, m] using (redB_row0_strict_suffix_min M hM hmono hpos).1
  have hanchor1 : entry N 1 m = m := by
    simpa [N, m] using redB_prefix_diag M hM hmono hpos 1
      (entry M 1 0) (le_refl _)
  rw [hred]
  apply List.ext_getElem
  · simp [R, seg, N, m, jN]
  · intro p hpR hpS
    have hpLen : p < jN + 1 - m := by simpa [R] using hpR
    have hmpL : m + p < Lng N := by dsimp [jN] at hpLen; omega
    have hge : m ≤ entry N 0 (m + p) := by
      by_cases hp0 : p = 0
      · subst p
        simpa using hanchor0.ge
      · exact (redB_row0_strict_suffix_min M hM hmono hpos).2
          (m + p) (by omega) (by simpa [N, m] using hmpL) |>.le
    have hfirst :
        entry N 0 (m + p) - entry N 0 m + entry N 1 m =
          entry N 0 (m + p) := by
      rw [hanchor0, hanchor1]
      omega
    simp [R, seg, N, m, jN, List.getElem_map, List.getElem_range', hfirst]

/-- `Red (coreReduce M)` splits into its forced diagonal prefix and `Red M`. -/
theorem Red_coreReduce_eq_diag_Red (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    Red (coreReduce M) =
      diagSeq 0 (entry M 1 0 - 1) ++ Red M := by
  let m := entry M 1 0
  let N := Red (coreReduce M)
  have hm : entry M 1 0 ≠ 0 := by omega
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hCL : Lng (coreReduce M) = m + Lng M := by
    simp [coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
    omega
  have hNL : Lng N = m + Lng M := by
    calc
      Lng N = Lng (coreReduce M) := Lng_Red_invariance (coreReduce M)
        (coreReduce_TPS M hM)
      _ = m + Lng M := hCL
  have hmN : m < Lng N := by rw [hNL]; omega
  have htake : N.take m = diagSeq 0 (m - 1) := by
    apply List.ext_getElem
    · simp [diagSeq, hNL]
      omega
    · intro p hpT hpD
      have hp : p < m := by simpa [hNL] using hpT
      have hpN : p < Lng N := hp.trans hmN
      have he0 : entry N 0 p = p := by
        simpa [N, m] using redB_prefix_diag M hM hmono hpos 0 p hp.le
      have he1 : entry N 1 p = p := by
        simpa [N, m] using redB_prefix_diag M hM hmono hpos 1 p hp.le
      apply Prod.ext
      · simpa [entry, List.getElem?_eq_getElem hpN, he0, diagSeq,
          List.getElem_map, List.getElem_range'] using he0
      · simpa [entry, List.getElem?_eq_getElem hpN, he1, diagSeq,
          List.getElem_map, List.getElem_range'] using he1
  have hdrop : N.drop m = Red M := by
    rw [drop_eq_seg N m hmN]
    symm
    simpa [N, m] using Red_eq_coreReduce_suffix M hM hmono hpos
  calc
    Red (coreReduce M) = N.take m ++ N.drop m := by simp [N]
    _ = diagSeq 0 (m - 1) ++ Red M := by rw [htake, hdrop]
    _ = diagSeq 0 (entry M 1 0 - 1) ++ Red M := by rfl

/-- Prepending the forced diagonal prefix commutes with reduction. -/
theorem Red_diag_prefix (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0)
    (hdom : entry M 1 0 ≤ entry M 0 0) :
    Red (diagSeq 0 (entry M 1 0 - 1) ++ M) =
      diagSeq 0 (entry M 1 0 - 1) ++ Red M := by
  rw [Red_diag_eq_coreReduce M hM hmono hpos hdom,
    Red_coreReduce_eq_diag_Red M hM hmono hpos]

private theorem diagSeq_zero_split (u m : ℕ) (hu : 0 < u) (hum : u < m) :
    diagSeq 0 (u - 1) ++ diagSeq u (m - 1) = diagSeq 0 (m - 1) := by
  have hu1 : u - 1 + 1 = u := by omega
  have hm1 : m - 1 + 1 = m := by omega
  simp only [diagSeq, hu1, hm1, Nat.zero_add, Nat.sub_zero, ← List.map_append]
  congr 1
  calc
    List.range' 0 u ++ List.range' u (m - u) =
        List.range' 0 u ++ List.range' (0 + u) (m - u) := by simp
    _ = List.range' 0 (u + (m - u)) := List.range'_append_1
    _ = List.range' 0 m := by rw [Nat.add_sub_of_le hum.le]

private theorem entry_diag_general (u v i j : ℕ)
    (hj : j < v + 1 - u) :
    entry (diagSeq u v) i j = u + j := by
  have hjL : j < Lng (diagSeq u v) := by simpa [diagSeq] using hj
  have hopt : (diagSeq u v)[j]? = some (u + j, u + j) := by
    rw [List.getElem?_eq_getElem hjL]
    congr 1
    simp [diagSeq, List.getElem_map, List.getElem_range']
  simp [entry, hopt]

private theorem entry_diag_general_append_lo (u v : ℕ) (Y : PS) (i j : ℕ)
    (hj : j < v + 1 - u) :
    entry (diagSeq u v ++ Y) i j = u + j := by
  rw [entry_append_left_mr]
  · exact entry_diag_general u v i j hj
  · simpa [diagSeq] using hj

private theorem entry_diag_general_append_hi (u v : ℕ) (Y : PS) (i a : ℕ)
    (ha : a < Lng Y) :
    entry (diagSeq u v ++ Y) i (v + 1 - u + a) = entry Y i a := by
  have hDlen : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
  rw [entry_append_right_mr (diagSeq u v) Y i (v + 1 - u + a) (by omega),
    hDlen]
  congr 1
  omega

/-- The guarded diagonal left extension of a mono sequence is again mono. -/
theorem monoT_diag_prefix (M : PS) (u : ℕ) (hM : TPS M)
    (hmono : monoT M = true)
    (hdom : entry M 1 0 ≤ entry M 0 0)
    (hu : u ≤ entry M 1 0) :
    monoT ((if u < entry M 1 0 then
      diagSeq u (entry M 1 0 - 1) else []) ++ M) = true := by
  let m := entry M 1 0
  by_cases hum : u < m
  · let D := diagSeq u (m - 1)
    let N := D ++ M
    have hmpos : 0 < m := by omega
    have hDlen : Lng D = m - u := by
      simp [D, diagSeq]
      omega
    have hDpos : 0 < Lng D := by rw [hDlen]; omega
    have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
    have hNL : Lng N = (m - u) + Lng M := by simp [N, hDlen]
    have hNT : TPS N := by
      apply List.ne_nil_of_length_pos
      change 0 < Lng N
      rw [hNL]
      omega
    have hhead : entry N 0 0 = u := by
      simpa [N, D, m] using
        entry_diag_general_append_lo u (m - 1) M 0 0 (by omega)
    have hmulti : multiT N = false := by
      apply (multi_criterion_12 N hNT).mpr
      intro j hjpos hjL
      rw [hhead]
      by_cases hjD : j < m - u
      · have he : entry N 0 j = u + j := by
          simpa [N, D, m, show m - 1 + 1 - u = m - u by omega] using
            entry_diag_general_append_lo u (m - 1) M 0 j (by omega)
        rw [he]
        omega
      · let a := j - (m - u)
        have hja : j = m - u + a := by dsimp [a]; omega
        have haM : a < Lng M := by rw [hja, hNL] at hjL; omega
        have he : entry N 0 j = entry M 0 a := by
          rw [hja]
          simpa [N, D, m, show m - 1 + 1 - u = m - u by omega] using
            entry_diag_general_append_hi u (m - 1) M 0 a haM
        rw [he]
        exact hum.trans_le (hdom.trans
          (mono_row0_min_mr M hM hmono a haM))
    have hz : zeroT N = false := by
      simp [zeroT, hNL]
      omega
    have hmonoN : monoT N = true := by
      have hh := hmulti
      simp [multiT, hz] at hh
      exact hh
    simpa [N, D, m, hum] using hmonoN
  · have humeq : u = m := by omega
    simpa [m, hum] using hmono

/-- §6.6 left-end lemma (corrected guarded form).  A diagonal segment may be
prepended up to the row-one left end without destroying reducedness or
monicity. -/
theorem RTPS_diag_prefix (M : PS) (u : ℕ) (hR : RTPS M)
    (hmono : monoT M = true) (hu : u ≤ entry M 1 0) :
    let N := (if u < entry M 1 0 then
      diagSeq u (entry M 1 0 - 1) else []) ++ M
    RTPS N ∧ monoT N = true := by
  let m := entry M 1 0
  let N := (if u < m then diagSeq u (m - 1) else []) ++ M
  have hM := RTPS_TPS M hR
  have hfix := RTPS_Red_eq M hR
  have hhead := RTPS_mono_head_eq M hR hmono
  have hmonoN : monoT N = true := by
    simpa [N, m] using monoT_diag_prefix M u hM hmono hhead.ge hu
  have hredN : Red N = N := by
    by_cases hmpos : 0 < m
    · have hmM : 0 < entry M 1 0 := by simpa [m] using hmpos
      have hredA : Red (diagSeq 0 (m - 1) ++ M) =
          diagSeq 0 (m - 1) ++ M := by
        calc
          Red (diagSeq 0 (m - 1) ++ M) =
              diagSeq 0 (m - 1) ++ Red M := by
            simpa [m] using Red_diag_prefix M hM hmono hmM hhead.ge
          _ = diagSeq 0 (m - 1) ++ M := by rw [hfix]
      by_cases hum : u < m
      · have hNeq : N = diagSeq u (m - 1) ++ M := by simp [N, hum]
        by_cases hu0 : u = 0
        · simpa [hNeq, hu0] using hredA
        · have hupos : 0 < u := Nat.pos_of_ne_zero hu0
          let E := diagSeq 0 (u - 1)
          have hENA : E ++ N = diagSeq 0 (m - 1) ++ M := by
            rw [hNeq, ← List.append_assoc, diagSeq_zero_split u m hupos hum]
          have hNpos : 0 < Lng N := by
            have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
            change 0 < List.length M at hMpos
            simp only [N, hum, if_pos, List.length_append]
            omega
          have hN0 : entry N 0 0 = u := by
            rw [hNeq]
            exact entry_diag_general_append_lo u (m - 1) M 0 0 (by omega)
          have hN1 : entry N 1 0 = u := by
            rw [hNeq]
            exact entry_diag_general_append_lo u (m - 1) M 1 0 (by omega)
          have hNT : TPS N := List.ne_nil_of_length_pos hNpos
          have hcruxN : Red (E ++ N) = E ++ Red N := by
            simpa [E, hN0, hN1] using
              Red_diag_prefix N hNT hmonoN (by omega) (by omega)
          have hfixedEN : Red (E ++ N) = E ++ N := by
            rw [hENA, hredA, ← hENA]
          have hcancel : E ++ Red N = E ++ N := by
            rw [← hcruxN, hfixedEN]
          exact List.append_cancel_left hcancel
      · have humeq : u = m := by omega
        simpa [N, hum] using hfix
    · have hmzero : m = 0 := by omega
      have huzero : u = 0 := by omega
      simpa [N, hmzero, huzero] using hfix
  have hNT : TPS N := by
    apply List.ne_nil_of_length_pos
    have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
    change 0 < List.length M at hMpos
    simp only [N, List.length_append]
    omega
  have hRT : RTPS N := by
    have hne : N ≠ [] := hNT
    simp [RTPS, reduced, hne, hredN]
  simpa [N, m] using And.intro hRT hmonoN

/-- Condition (A) on a sequence with a nonempty diagonal prefix descends to
the original suffix.  This packages the suffix as a `seg`, so all parent
bookkeeping at the prefix/suffix junction is discharged by `RedCondA_seg`. -/
theorem RedCondA_of_diag_prefix (M : PS) (m : ℕ) (hM : TPS M)
    (hm : 0 < m)
    (hA : RedCondA (diagSeq 0 (m - 1) ++ M) = true) :
    RedCondA M = true := by
  let N := diagSeq 0 (m - 1) ++ M
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hDlen : Lng (diagSeq 0 (m - 1)) = m := by
    simp [diagSeq]
    omega
  have hNlen : Lng N = m + Lng M := by simp [N, hDlen]
  have hmN : m < Lng N := by omega
  have hmend : m ≤ Lng N - 1 := by omega
  have hend : Lng N - 1 < Lng N := by omega
  have hseg := RedCondA_seg N m (Lng N - 1) hmend hend
    (by simpa [N] using hA)
  have hdrop : N.drop m = M := by simp [N, hDlen]
  calc
    RedCondA M = RedCondA (N.drop m) := by rw [hdrop]
    _ = RedCondA (seg N m (Lng N - 1)) := by rw [drop_eq_seg N m hmN]
    _ = true := hseg

#print axioms Red_diag_eq_coreReduce
#print axioms Red_eq_coreReduce_suffix
#print axioms Red_coreReduce_eq_diag_Red
#print axioms Red_diag_prefix
#print axioms monoT_diag_prefix
#print axioms RTPS_diag_prefix
#print axioms RedCondA_of_diag_prefix

end PSS

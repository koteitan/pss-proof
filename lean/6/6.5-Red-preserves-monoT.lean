import PSS.Standard
import «6».«6.2-P-fseq»
import «6».«6.5-Red-IncrFirst-invariance»
import «6».«6.5-Red-preserves-zeroT»

/-!
# §6.5 系（`Red` が単項性を保つこと）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_monoT`
- 訂正: A4（原文の `TPS` 版は偽。`anchoredSlice` 上に制限）
- Isabelle: `m_6_5_Red_preserves_monoT`, `m_6_5_Red_monoT_final`
- 依存: `6.5-monoT-Red`, `6.5-Red-preserves-zeroT`, §6.2
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem Red_core_row0_strict (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0) :
    ∀ j, 0 < j → j < Lng (Red M) → 0 < entry (Red M) 0 j := by
  intro j hjpos hjL
  by_cases hjtr : j ≤ TrMax M
  · have he := Red_core_prefix_diag M hmono hcore 0 j hjtr
    omega
  · have hLR := Lng_Red_invariance M hM
    have ht : TrMax M ≠ Lng M - 1 := by
      intro heq
      omega
    let tail := (List.range (Br M).length).flatMap (fun J =>
      IncrFirstN (branchE M J) (Red (redNJ M J)))
    have hred : Red M = diagSeq 0 (TrMax M) ++ tail := by
      simpa [tail] using Red_core_nontrunk_mr M hM hmono hcore ht
    have hjD : Lng (diagSeq 0 (TrMax M)) ≤ j := by
      simp [diagSeq]
      omega
    let k := j - Lng (diagSeq 0 (TrMax M))
    have hk : k < Lng tail := by
      have hh := hjL
      rw [hred] at hh
      simp only [List.length_append] at hh
      change j < Lng (diagSeq 0 (TrMax M)) + Lng tail at hh
      change k < Lng tail
      dsimp [k]
      omega
    have he : entry (Red M) 0 j = entry tail 0 k := by
      rw [hred]
      exact entry_append_right_mr (diagSeq 0 (TrMax M)) tail 0 j hjD
    have hget : entry tail 0 k = tail[k].1 :=
      entry0_eq_fst_getElem_mr tail k hk
    have hmem : tail[k] ∈ tail := List.getElem_mem hk
    change tail[k] ∈ (List.range (Br M).length).flatMap (fun J =>
      IncrFirstN (branchE M J) (Red (redNJ M J))) at hmem
    rcases List.mem_flatMap.mp hmem with ⟨J, hJmem, hp⟩
    have hJ : J < (Br M).length := List.mem_range.mp hJmem
    have hge := branch_block_row0_ge_joint_mr M J hM hmono hcore hJ tail[k] hp
    rw [he, hget]
    omega

private theorem redPositiveOut_mono (M N : PS)
    (hmj : entry M 1 0 ≤ Lng N - 1)
    (hSmono : monoT (seg N (entry M 1 0) (Lng N - 1)) = true) :
    monoT (redPositiveOut_ri M N) = true := by
  let m := entry M 1 0
  let jN := Lng N - 1
  let S := seg N m jN
  let R := (List.range' m (jN + 1 - m)).map (fun j =>
    (entry N 0 j - entry N 0 m + entry N 1 m, entry N 1 j))
  have hred : redPositiveOut_ri M N = R := by
    simp [redPositiveOut_ri, R, m, jN, hmj, hSmono]
  have hSL : Lng S = jN + 1 - m := by simp [S]
  have hRL : Lng R = jN + 1 - m := by simp [R]
  have hST : TPS S := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng S
    rw [hSL]
    omega
  have hposS : 0 < Lng S := List.length_pos_of_ne_nil hST
  have hposR : 0 < Lng R := by rw [hRL, ← hSL]; exact hposS
  have eR0 : ∀ k, k < Lng R →
      entry R 0 k = entry N 0 (m + k) - entry N 0 m + entry N 1 m := by
    intro k hk
    rw [entry0_eq_fst_getElem_mr R k hk]
    simp [R, List.getElem_map, List.getElem_range']
  have eR1 : ∀ k, k < Lng R → entry R 1 k = entry N 1 (m + k) := by
    intro k hk
    have hget : R[k] =
        (entry N 0 (m + k) - entry N 0 m + entry N 1 m,
          entry N 1 (m + k)) := by
      simp [R, List.getElem_map, List.getElem_range']
    simp [entry, List.getElem?_eq_getElem hk, hget]
  have eS : ∀ i k, k < Lng S → entry S i k = entry N i (m + k) := by
    intro i k hk
    exact entry_seg N m jN i k hk
  have hzeroS : zeroT S = false := by
    have hh := hSmono
    simp [monoT] at hh
    exact hh.1
  have hzeroR : zeroT R = false := by
    by_cases hL : Lng S = 1
    · have hLR : Lng R = 1 := by rw [hRL, ← hSL, hL]
      have heS1 : entry S 1 0 = entry N 1 m := by
        simpa using eS 1 0 (by omega)
      have heR1 : entry R 1 0 = entry N 1 m := by
        simpa using eR1 0 (by omega)
      have hne : entry S 1 0 ≠ 0 := by
        simpa [zeroT, hL] using hzeroS
      simp [zeroT, hLR, heR1, ← heS1, hne]
    · have hLR : Lng R ≠ 1 := by rw [hRL, ← hSL]; exact hL
      simp [zeroT, hLR]
  have hleR : leR R 0 0 (Lng R - 1) = true := by
    by_cases hL : Lng R = 1
    · simp [leR, le0, hL, le0Aux]
    · apply parent_exists_3 R 0 (Lng R - 1) (by
        exact List.ne_nil_of_length_pos hposR)
      · omega
      · omega
      · intro k hkpos hklast
        have hkR : k < Lng R := by omega
        have hkS : k < Lng S := by rw [hSL, ← hRL]; exact hkR
        have hfull : leR S 0 0 (Lng S - 1) = true := by
          have hh := hSmono
          simp only [monoT, Bool.and_eq_true] at hh
          exact hh.2
        have hstrict := ancestor_basic_1 S 0 k (Lng S - 1) hST
          hkpos (by omega) hfull
        have heS0 : entry S 0 0 = entry N 0 m := by
          simpa using eS 0 0 hposS
        have heSk : entry S 0 k = entry N 0 (m + k) := eS 0 k hkS
        have hb : entry N 0 m < entry N 0 (m + k) := by
          simpa [heS0, heSk] using hstrict
        rw [eR0 0 hposR, eR0 k hkR]
        simp only [Nat.add_zero, Nat.sub_self, zero_add]
        omega
  rw [hred]
  simp [monoT, hzeroR, hleR]

/-- A4-independent forward half: every mono input remains mono after `Red`. -/
theorem Red_preserves_monoT_forward (M : PS) (hM : TPS M)
    (hmono : monoT M = true) : monoT (Red M) = true := by
  generalize hn : nu M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hz : zeroT M = false := by
        have hh := hmono
        simp [monoT] at hh
        exact hh.1
      have hmulti : multiT M = false := by simp [multiT, hmono]
      have hLR := Lng_Red_invariance M hM
      have hRT : TPS (Red M) := by
        apply List.ne_nil_of_length_pos
        change 0 < Lng (Red M)
        rw [hLR]
        exact List.length_pos_of_ne_nil hM
      have hzR : zeroT (Red M) = false := by
        have heq := Red_preserves_zeroT M hM
        by_cases hh : zeroT (Red M) = true
        · exact False.elim (by simpa [hz] using heq.mpr hh)
        · exact Bool.eq_false_of_not_eq_true hh
      by_cases hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0
      · have hle : leR (Red M) 0 0 (Lng (Red M) - 1) = true := by
          have hposR : 0 < Lng (Red M) := List.length_pos_of_ne_nil hRT
          by_cases hL : Lng (Red M) = 1
          · simp [leR, le0, hL, le0Aux]
          · apply parent_exists_3 (Red M) 0 (Lng (Red M) - 1) hRT
            · omega
            · omega
            · intro j hjpos hjlast
              have he0 := Red_core_prefix_diag M hmono hcore 0 0 (Nat.zero_le _)
              have hej := Red_core_row0_strict M hM hmono hcore j hjpos (by omega)
              omega
        simp [monoT, hzR, hle]
      · by_cases hm : entry M 1 0 = 0
        · have hCT := coreReduce_TPS M hM
          have hdesc := nu_coreReduce_lt M hM hmono hcore
          have hmultiC := coreReduce_multi_false M hM hmono
          have hLC : Lng (coreReduce M) = Lng M := by simp [coreReduce, hm]
          have hzC : zeroT (coreReduce M) = false := by
            have hcoreC := coreReduce_core M hM
            have hMlen : Lng M ≠ 1 := by
              intro hL
              have : zeroT M = true := by simp [zeroT, hL, hm]
              simp [hz] at this
            simp [zeroT, hLC, hcoreC.2, hMlen]
          have hmonoC : monoT (coreReduce M) = true := by
            simpa [multiT, hzC] using hmultiC
          have hred := Red_noncore_ri M hM hmono hcore
          rw [if_pos hm] at hred
          rw [hred]
          exact ih (nu (coreReduce M)) (by omega) (coreReduce M) hCT hmonoC rfl
        · have hpos : 0 < entry M 1 0 := by omega
          have hseg := monoT_Red_m10pos M hM hmono hpos
          let N := Red (coreReduce M)
          have hseg' : TPS (seg N (entry M 1 0) (Lng N - 1)) ∧
              monoT (seg N (entry M 1 0) (Lng N - 1)) = true := by
            simpa [N] using hseg
          have hmj : entry M 1 0 ≤ Lng N - 1 := by
            have hp := List.length_pos_of_ne_nil hseg'.1
            simp at hp
            omega
          have hred := Red_noncore_ri M hM hmono hcore
          rw [if_neg hm] at hred
          rw [hred]
          exact redPositiveOut_mono M N hmj hseg'.2

private theorem RTPS_TPS (M : PS) (hM : RTPS M) : TPS M := by
  have h := hM
  simp only [RTPS, reduced, Bool.and_eq_true, beq_iff_eq] at h
  simpa [TPS] using h.1

private theorem oper_TPS_of_TPS (M : PS) (n : ℕ) (hM : TPS M)
    (hn : 1 ≤ n) : TPS (oper M n) := by
  by_cases hlen : 1 < Lng M
  · exact oper_nonempty_fseq M n hM hlen hn
  · have hpos := List.length_pos_of_ne_nil hM
    change 0 < Lng M at hpos
    have hL : Lng M = 1 := by omega
    simpa [oper, hL] using hM

private theorem STPS_TPS (M : PS) (hM : STPS M) : TPS M := by
  induction hM with
  | diag u v huv =>
      apply List.ne_nil_of_length_pos
      simp [diagSeq]
      omega
  | oper hS n hn ih =>
      exact oper_TPS_of_TPS _ n ih hn

/-- Every corrected A4 anchored slice is zero or mono, never multi. -/
theorem anchoredSlice_zero_or_mono (M : PS) (hM : anchoredSlice M) :
    zeroT M = true ∨ monoT M = true := by
  rcases hM with ⟨S, a, b, hsource, hab, hbL, habAnc, rfl⟩
  have hST : TPS S := hsource.elim (STPS_TPS S) (fun h => RTPS_TPS S h.1)
  by_cases heq : a = b
  · subst b
    have hL : Lng (seg S a a) = 1 := by simp
    by_cases hz : zeroT (seg S a a) = true
    · exact Or.inl hz
    · right
      have hz' : zeroT (seg S a a) = false := Bool.eq_false_of_not_eq_true hz
      simp [monoT, hz', leR, le0, hL, le0Aux]
  · right
    have hlt : a < b := by omega
    exact mono_ancestor_slice S a b hST hlt (by simpa [leR] using habAnc)

/-- 訂正 A4 後の主張: anchored slice 上で単項性は `Red` と同値。 -/
theorem Red_preserves_monoT (M : PS) (hM : anchoredSlice M) :
    monoT M = true ↔ monoT (Red M) = true := by
  have hMT : TPS M := by
    rcases hM with ⟨S, a, b, hsource, hab, hbL, habAnc, hseg⟩
    rw [hseg]
    apply List.ne_nil_of_length_pos
    simp
    omega
  constructor
  · exact Red_preserves_monoT_forward M hMT
  · intro hmonoR
    rcases anchoredSlice_zero_or_mono M hM with hz | hmono
    · have hzR := (Red_preserves_zeroT M hMT).mp hz
      have hh := hmonoR
      simp [monoT, hzR] at hh
    · exact hmono

/-- 原文の `TPS` 版に対する A4 の最小反例。 -/
theorem Red_preserves_monoT_original_false :
    ∃ M : PS, TPS M ∧ monoT M = false ∧ monoT (Red M) = true := by
  refine ⟨[(0, 0), (0, 1)], ?_, ?_, ?_⟩
  · simp [TPS]
  · decide
  · decide

#print axioms Red_preserves_monoT
#print axioms Red_preserves_monoT_original_false

end PSS

import «6».«6.5-Lng-Red-invariance»

/-!
# §6.5 系（`Red` が零項性を保つこと）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_zeroT`
- 訂正: なし
- Isabelle: `m_6_5_Red_zeroT`
- 依存: `6.5-Lng-Red-invariance`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem length_one_leR_refl (M : PS) (hL : Lng M = 1) :
    leR M 0 0 (Lng M - 1) = true := by
  simp [leR, le0, hL, le0Aux]

private theorem RedAux_length_one_entry1_ne (fuel : ℕ) (M : PS)
    (hM : TPS M) (hL : Lng M = 1) (hnz : zeroT M ≠ true) :
    entry (RedAux fuel M) 1 0 ≠ 0 := by
  have hm₁ : entry M 1 0 ≠ 0 := by
    intro heq
    apply hnz
    simp [zeroT, hL, heq]
  cases fuel with
  | zero => simpa [RedAux] using hm₁
  | succ fuel =>
      have hmono : monoT M = true := by
        simp [monoT, hnz, length_one_leR_refl M hL]
      have hmulti : multiT M ≠ true := by simp [multiT, hnz, hmono]
      rw [RedAux, if_neg hnz, if_neg hmulti]
      have hcore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by omega
      rw [if_neg hcore, if_neg hm₁]
      let m₁ := entry M 1 0
      let A := coreReduce M
      let N := RedAux fuel A
      let jN := Lng N - 1
      have hm₁pos : 0 < m₁ := by simp [m₁]; omega
      have hAL : Lng A = m₁ + 1 := by
        simp [A, coreReduce, m₁, hm₁, diagSeq, hL]
        omega
      have hAT : TPS A := by
        apply List.ne_nil_of_length_pos
        change 0 < Lng A
        rw [hAL]
        omega
      have hNL : Lng N = m₁ + 1 := by
        simpa [N, hAL] using RedAux_length fuel A hAT
      have hjN : jN = m₁ := by simp [jN, hNL]
      let cond := decide (m₁ ≤ jN) && monoT (seg N m₁ jN)
      change entry (if cond then
          (List.range' m₁ (jN + 1 - m₁)).map (fun j =>
            (entry N 0 j - entry N 0 m₁ + entry N 1 m₁, entry N 1 j))
        else M) 1 0 ≠ 0
      by_cases hc : cond = true
      · rw [if_pos hc]
        have hc' := hc
        simp only [cond, Bool.and_eq_true, decide_eq_true_eq] at hc'
        have hSmono := hc'.2
        have hSlen : Lng (seg N m₁ jN) = 1 := by simp [hjN]
        have hSnz : zeroT (seg N m₁ jN) = false := by
          have hh := hSmono
          simp only [monoT, Bool.and_eq_true] at hh
          simpa using hh.1
        have heSeg : entry (seg N m₁ jN) 1 0 = entry N 1 m₁ := by
          simpa using entry_seg N m₁ jN 1 0 (by omega : 0 < Lng (seg N m₁ jN))
        have heN : entry N 1 m₁ ≠ 0 := by
          intro heq
          have : zeroT (seg N m₁ jN) = true := by
            simp [zeroT, hSlen, heSeg, heq]
          simp [hSnz] at this
        simp [hjN]
        change entry N 1 m₁ ≠ 0
        exact heN
      · rw [if_neg hc]
        exact hm₁

theorem Red_preserves_zeroT (M : PS) (hM : TPS M) :
    zeroT M = true ↔ zeroT (Red M) = true := by
  constructor
  · intro hz
    unfold Red
    rw [RedAux, if_pos hz]
    simp [zeroT, entry]
  · intro hzR
    have hLR := Lng_Red_invariance M hM
    have hL : Lng M = 1 := by
      have hh := hzR
      simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
      omega
    by_contra hnz
    have hne := RedAux_length_one_entry1_ne (nu M + 1) M hM hL hnz
    have heq : entry (Red M) 1 0 = 0 := by
      have hh := hzR
      simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
      exact hh.2
    exact hne (by simpa [Red] using heq)

#print axioms Red_preserves_zeroT

end PSS

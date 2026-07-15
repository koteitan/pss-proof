import «6».«6.5-Red-welldefined»
import «6».«6.5-Lng-Red-invariance»

/-!
# §6.5 命題（単項性と `Red` の関係）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_monoT_Red`
- 訂正: `m₁₀ = 0` では紙面の空対角列を用いる必要があるため、実際に `Red` の正係数分岐で
  必要となる `0 < m₁₀` 版を先に形式化する
- Isabelle: `m_6_5_monoT_Red_m10pos`
- 依存: `6.5-Red-welldefined`, `6.5-Lng-Red-invariance`, §6.4
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem entry_append_left_mr (A B : PS) (i j : ℕ)
    (hj : j < Lng A) : entry (A ++ B) i j = entry A i j := by
  simp [entry, List.getElem?_append_left hj]

theorem entry_append_right_mr (A B : PS) (i j : ℕ)
    (hj : Lng A ≤ j) : entry (A ++ B) i j = entry B i (j - Lng A) := by
  simp [entry, List.getElem?_append_right hj]

theorem entry_diagSeq_zero_mr (t i j : ℕ) (hj : j ≤ t) :
    entry (diagSeq 0 t) i j = j := by
  have hlen : j < Lng (diagSeq 0 t) := by
    simp [diagSeq]
    omega
  have hget : (diagSeq 0 t)[j] = (j, j) := by
    simp [diagSeq]
  simp [entry, List.getElem?_eq_getElem hlen, hget]

/-- The positive `m₁₀` diagonal inserted by `coreReduce` reaches the trunk.
This arithmetic proof packages the stronger already established bound
`betaM (coreReduce M) ≤ Lng M`. -/
theorem coreReduce_m10_le_TrMax (M : PS) (hM : TPS M)
    (hpos : 0 < entry M 1 0) :
    entry M 1 0 ≤ TrMax (coreReduce M) := by
  have hm : entry M 1 0 ≠ 0 := by omega
  have hlen : Lng (coreReduce M) = entry M 1 0 + Lng M := by
    simp [coreReduce, hm, diagSeq, IncrFirstN_eq_map]
    omega
  have hCT : TPS (coreReduce M) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (coreReduce M)
    rw [hlen]
    omega
  have hbeta := betaM_coreReduce_le M hM
  have htr := TrMax_bound (coreReduce M) hCT
  simp only [betaM] at hbeta
  omega

/-- A core mono sequence is reduced with its whole trunk copied as a
diagonal prefix. -/
theorem Red_core_prefix_diag (B : PS) (hmono : monoT B = true)
    (hcore : entry B 0 0 = 0 ∧ entry B 1 0 = 0)
    (i j : ℕ) (hj : j ≤ TrMax B) :
    entry (Red B) i j = j := by
  have hz : zeroT B = false := by
    have hh := hmono
    simp [monoT] at hh
    exact hh.1
  have hmulti : multiT B = false := by
    simp [multiT, hmono]
  change entry (RedAux (nu B + 1) B) i j = j
  rw [RedAux, if_neg (by simpa using hz), if_neg (by simpa using hmulti),
    if_pos hcore]
  by_cases ht : TrMax B = Lng B - 1
  · rw [if_pos ht]
    rw [hcore.2]
    simpa using
      entry_diagSeq_zero_mr (Lng B - 1) i j (by simpa [ht] using hj)
  · rw [if_neg ht]
    apply Eq.trans (entry_append_left_mr (diagSeq 0 (TrMax B)) _ i j ?_)
    · exact entry_diagSeq_zero_mr (TrMax B) i j hj
    · simp [diagSeq]
      omega

/-- Specialization of `Red_core_prefix_diag` to the positive `coreReduce`
argument used by the fifth branch of `Red`. -/
theorem redB_prefix_diag (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0)
    (i j : ℕ) (hj : j ≤ entry M 1 0) :
    entry (Red (coreReduce M)) i j = j := by
  have hmonoC : monoT (coreReduce M) = true := by
    have hmulti := coreReduce_multi_false M hM hmono
    have hcore := coreReduce_core M hM
    have hz : zeroT (coreReduce M) = false := by
      have hlen : 1 < Lng (coreReduce M) := by
        have hm : entry M 1 0 ≠ 0 := by omega
        have hMpos := List.length_pos_of_ne_nil hM
        simp [coreReduce, hm, diagSeq, IncrFirstN_eq_map]
        omega
      simp [zeroT]
      omega
    simpa [multiT, hz] using hmulti
  apply Red_core_prefix_diag (coreReduce M) hmonoC
    (coreReduce_core M hM) i j
  exact le_trans hj (coreReduce_m10_le_TrMax M hM hpos)

theorem mono_row0_min_mr (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (k : ℕ) (hk : k < Lng M) :
    entry M 0 0 ≤ entry M 0 k := by
  cases k with
  | zero => simp
  | succ k =>
      have hfull : leR M 0 0 (Lng M - 1) = true := by
        have hh := hmono
        simp only [monoT, Bool.and_eq_true] at hh
        exact hh.2
      have hstrict := ancestor_basic_1 M 0 (k + 1) (Lng M - 1) hM
        (by omega) (by omega) hfull
      omega

theorem entry0_eq_fst_getElem_mr (M : PS) (j : ℕ)
    (hj : j < Lng M) : entry M 0 j = M[j].1 := by
  simp [entry, List.getElem?_eq_getElem hj]

private theorem entry_rebase0_mr (N : PS) (m len k : ℕ)
    (hk : k < len) :
    entry ((List.range' m len).map (fun j =>
      (entry N 0 j - entry N 0 m + entry N 1 m, entry N 1 j))) 0 k =
      entry N 0 (m + k) - entry N 0 m + entry N 1 m := by
  have hL : k < Lng ((List.range' m len).map (fun j =>
      (entry N 0 j - entry N 0 m + entry N 1 m, entry N 1 j))) := by
    simp
    exact hk
  rw [entry0_eq_fst_getElem_mr _ k hL]
  simp [List.getElem_map, List.getElem_range']

/-- For a mono input, the leftmost row-zero coefficient of its reduction is
a minimum among all row-zero coefficients of the reduction.  This is the
non-circular value invariant used for the branch tail. -/
theorem Red_leftend_row0_min (M : PS) (hM : TPS M)
    (hmono : monoT M = true) :
    ∀ k < Lng (Red M), entry (Red M) 0 0 ≤ entry (Red M) 0 k := by
  generalize hn : nu M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hz : zeroT M = false := by
        have hh := hmono
        simp [monoT] at hh
        exact hh.1
      have hmulti : multiT M = false := by simp [multiT, hmono]
      by_cases hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0
      · have he0 := Red_core_prefix_diag M hmono hcore 0 0 (Nat.zero_le _)
        intro k hk
        rw [he0]
        omega
      · by_cases hm : entry M 1 0 = 0
        · have hCT : TPS (coreReduce M) := by
            have hlen : Lng (coreReduce M) = Lng M := by simp [coreReduce, hm]
            apply List.ne_nil_of_length_pos
            change 0 < Lng (coreReduce M)
            rw [hlen]
            exact List.length_pos_of_ne_nil hM
          have hdesc := nu_coreReduce_lt M hM hmono hcore
          have hmonoC : monoT (coreReduce M) = true := by
            have hmultiC := coreReduce_multi_false M hM hmono
            have hlen : Lng (coreReduce M) = Lng M := by simp [coreReduce, hm]
            have hzC : zeroT (coreReduce M) = false := by
              have hcoreC := coreReduce_core M hM
              have hzeq : zeroT (coreReduce M) = zeroT M := by
                simp [zeroT, hlen, hcoreC.2, hm]
              rw [hzeq, hz]
            simpa [multiT, hzC] using hmultiC
          have hred : Red M = Red (coreReduce M) := by
            change RedAux (nu M + 1) M = Red (coreReduce M)
            rw [RedAux, if_neg (by simpa using hz),
              if_neg (by simpa using hmulti), if_neg hcore, if_pos hm,
              RedAux_stable (coreReduce M) hCT (nu M) hdesc]
          rw [hred]
          exact ih (nu (coreReduce M)) (by omega) (coreReduce M) hCT hmonoC rfl
        · have hmpos : 0 < entry M 1 0 := by omega
          let A := coreReduce M
          have hAT : TPS A := by
            apply List.ne_nil_of_length_pos
            change 0 < Lng A
            simp [A, coreReduce, hm, diagSeq, IncrFirstN_eq_map]
          have hdesc : nu A < nu M := by
            simpa [A] using nu_coreReduce_lt M hM hmono hcore
          have hstable : RedAux (nu M) A = Red A :=
            RedAux_stable A hAT (nu M) hdesc
          let N := Red A
          let jN := Lng N - 1
          let cond := decide (entry M 1 0 ≤ jN) &&
            monoT (seg N (entry M 1 0) jN)
          let R := (List.range' (entry M 1 0)
              (jN + 1 - entry M 1 0)).map (fun j =>
                (entry N 0 j - entry N 0 (entry M 1 0) +
                    entry N 1 (entry M 1 0), entry N 1 j))
          have hred : Red M = if cond then R else M := by
            change RedAux (nu M + 1) M = if cond then R else M
            rw [RedAux, if_neg (by simpa using hz),
              if_neg (by simpa using hmulti), if_neg hcore, if_neg hm]
            simp only [A, N, jN, cond, R]
            rw [hstable]
          by_cases hc : cond = true
          · have hc' := hc
            simp only [cond, Bool.and_eq_true, decide_eq_true_eq] at hc'
            have hmj : entry M 1 0 ≤ jN := hc'.1
            have hSmono : monoT (seg N (entry M 1 0) jN) = true := hc'.2
            have hST : TPS (seg N (entry M 1 0) jN) := by
              apply List.ne_nil_of_length_pos
              simp
              omega
            rw [hred, if_pos hc]
            intro k hk
            have hklen : k < jN + 1 - entry M 1 0 := by
              simpa [R] using hk
            have hsegk : k < Lng (seg N (entry M 1 0) jN) := by
              simpa using hklen
            have hmin := mono_row0_min_mr (seg N (entry M 1 0) jN)
              hST hSmono k hsegk
            have he0 : entry (seg N (entry M 1 0) jN) 0 0 =
                entry N 0 (entry M 1 0) := by
              simpa using entry_seg N (entry M 1 0) jN 0 0 (by simp; omega)
            have hek : entry (seg N (entry M 1 0) jN) 0 k =
                entry N 0 (entry M 1 0 + k) :=
              entry_seg N (entry M 1 0) jN 0 k hsegk
            have hbase : entry N 0 (entry M 1 0) ≤
                entry N 0 (entry M 1 0 + k) := by
              simpa [he0, hek] using hmin
            have er0 := entry_rebase0_mr N (entry M 1 0)
              (jN + 1 - entry M 1 0) 0 (by omega)
            have erk := entry_rebase0_mr N (entry M 1 0)
              (jN + 1 - entry M 1 0) k hklen
            change entry R 0 0 ≤ entry R 0 k
            change entry ((List.range' (entry M 1 0)
                (jN + 1 - entry M 1 0)).map (fun j =>
                  (entry N 0 j - entry N 0 (entry M 1 0) +
                    entry N 1 (entry M 1 0), entry N 1 j))) 0 0 ≤
              entry ((List.range' (entry M 1 0)
                (jN + 1 - entry M 1 0)).map (fun j =>
                  (entry N 0 j - entry N 0 (entry M 1 0) +
                    entry N 1 (entry M 1 0), entry N 1 j))) 0 k
            rw [er0, erk]
            simp only [Nat.add_zero]
            omega
          · have hredM : Red M = M := by rw [hred, if_neg hc]
            rw [hredM]
            intro k hk
            exact mono_row0_min_mr M hM hmono k hk

/-- On a non-multi input whose row-one left end is below its row-zero left
end, reduction cannot move the row-zero left end below that row-one value.
This is exactly the form needed for the non-multi branch arguments `redNJ`. -/
theorem Red_leftend_ge_row1_nonmulti (M : PS) (hM : TPS M)
    (hnonmulti : multiT M = false)
    (hguard : entry M 1 0 ≤ entry M 0 0) :
    entry M 1 0 ≤ entry (Red M) 0 0 := by
  by_cases hz : zeroT M = true
  · have he1 : entry M 1 0 = 0 := by
      have hh := hz
      simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
      exact hh.2
    omega
  · have hmono : monoT M = true := by
      have hh := hnonmulti
      simp [multiT, hz] at hh
      exact hh
    by_cases hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0
    · have he0 := Red_core_prefix_diag M hmono hcore 0 0 (Nat.zero_le _)
      omega
    · by_cases hm : entry M 1 0 = 0
      · omega
      · have hmpos : 0 < entry M 1 0 := by omega
        let A := coreReduce M
        have hAT : TPS A := by
          apply List.ne_nil_of_length_pos
          change 0 < Lng A
          simp [A, coreReduce, hm, diagSeq, IncrFirstN_eq_map]
        have hdesc : nu A < nu M := by
          simpa [A] using nu_coreReduce_lt M hM hmono hcore
        have hstable : RedAux (nu M) A = Red A :=
          RedAux_stable A hAT (nu M) hdesc
        let N := Red A
        let jN := Lng N - 1
        let cond := decide (entry M 1 0 ≤ jN) &&
          monoT (seg N (entry M 1 0) jN)
        let R := (List.range' (entry M 1 0)
            (jN + 1 - entry M 1 0)).map (fun j =>
              (entry N 0 j - entry N 0 (entry M 1 0) +
                  entry N 1 (entry M 1 0), entry N 1 j))
        have hred : Red M = if cond then R else M := by
          change RedAux (nu M + 1) M = if cond then R else M
          rw [RedAux, if_neg hz, if_neg (by simpa using hnonmulti),
            if_neg hcore, if_neg hm]
          simp only [A, N, jN, cond, R]
          rw [hstable]
        by_cases hc : cond = true
        · have hc' := hc
          simp only [cond, Bool.and_eq_true, decide_eq_true_eq] at hc'
          have hmj : entry M 1 0 ≤ jN := hc'.1
          have hNanchor : entry N 1 (entry M 1 0) = entry M 1 0 := by
            simpa [N, A] using
              redB_prefix_diag M hM hmono hmpos 1 (entry M 1 0) (le_refl _)
          have er0 := entry_rebase0_mr N (entry M 1 0)
            (jN + 1 - entry M 1 0) 0 (by omega)
          rw [hred, if_pos hc]
          change entry M 1 0 ≤ entry R 0 0
          change entry M 1 0 ≤ entry ((List.range' (entry M 1 0)
              (jN + 1 - entry M 1 0)).map (fun j =>
                (entry N 0 j - entry N 0 (entry M 1 0) +
                  entry N 1 (entry M 1 0), entry N 1 j))) 0 0
          rw [er0]
          simp only [Nat.add_zero, Nat.sub_self, zero_add, hNanchor]
          exact le_refl _
        · rw [hred, if_neg hc]
          exact hguard

theorem nextR1_unique_mr (M : PS) (p q k : ℕ)
    (hp : nextR M 1 p k = true) (hq : nextR M 1 q k = true) : p = q := by
  have hhp := hp
  simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hhp
  rcases hhp with ⟨⟨⟨⟨⟨hpL, hkL⟩, hpk⟩, hep⟩, hp0raw⟩, hallp⟩
  have hhq := hq
  simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hhq
  rcases hhq with ⟨⟨⟨⟨⟨hqL, _⟩, hqk⟩, heq⟩, hq0raw⟩, hallq⟩
  have hMT : TPS M :=
    List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hkL)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · have hq0 : leR M 0 q k = true := by
      simpa [leR] using hq0raw
    have hle := parent_basic_2 M p q k hMT hpq hqk.le hp hq0
    have hstrict : entry M 1 q < entry M 1 k := heq
    omega
  · have hp0 : leR M 0 p k = true := by
      simpa [leR] using hp0raw
    have hle := parent_basic_2 M q p k hMT hqp hpk.le hq hp0
    have hstrict : entry M 1 p < entry M 1 k := hep
    omega

private theorem P_component_leftend_mr (M : PS) (J i : ℕ)
    (hM : TPS M) (hJ : J < (P M).length) :
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

theorem entry_FirstNodes_eq_component_mr (M : PS) (J i : ℕ)
    (hM : TPS M)
    (hJ : J < (Br M).length) :
    entry M i ((FirstNodes M).getD J 0) =
      entry ((Br M).getD J []) i 0 := by
  have hbound := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have : Br M = [] := by simp [Br, heq]
    rw [this] at hJ
    simp at hJ
  let N := seg M (TrMax M + 1) (Lng M - 1)
  have hBr : Br M = P N := by simp [N, Br, hne]
  have hNpos : 0 < Lng N := by simp [N]; omega
  have hNT : TPS N := List.ne_nil_of_length_pos hNpos
  have hJP : J < (P N).length := by simpa [hBr] using hJ
  let k := (IdxSum (P N)).getD J 0
  have hkN : k < Lng N := by
    have hl := (P_leftend_lmin N J hNT hJP).1
    have hpred : Lng N - 1 + 1 = Lng N :=
      Nat.sub_add_cancel (show 1 ≤ Lng N from hNpos)
    simpa [k] using (show (IdxSum (P N)).getD J 0 < Lng N by omega)
  have hentryN : entry N i k = entry ((P N).getD J []) i 0 := by
    symm
    simpa [k] using P_component_leftend_mr N J i hNT hJP
  have hentryM : entry N i k = entry M i (TrMax M + 1 + k) := by
    simpa [N] using entry_seg M (TrMax M + 1) (Lng M - 1) i k hkN
  have hfn := FirstNodes_getD M J hJ
  rw [hfn, hBr]
  change entry M i (TrMax M + 1 + k) = entry ((P N).getD J []) i 0
  rw [← hentryM, hentryN]

/-- The row-one lift `np` used in `redNJ` never exceeds its row-zero joint
plus one. -/
theorem redNJ_np_le_joint (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hcore1 : entry M 1 0 = 0)
    (hJ : J < (Br M).length) :
    (if entry ((Br M).getD J []) 1 0 = 0 then 0
      else parent M 1 ((FirstNodes M).getD J 0) + 1) ≤
      (Joints M).getD J 0 + 1 := by
  by_cases hb : entry ((Br M).getD J []) 1 0 = 0
  · rw [if_pos hb]
    omega
  · let f := (FirstNodes M).getD J 0
    rw [if_neg hb]
    have htr := FirstNodes_TrMax_Joints M J hM hmono hJ
    have hnext0 := Joints_nextR_FirstNodes M J hM hmono hJ
    have hfL : f < Lng M := by
      have hn : nextrel0 M ((Joints M).getD J 0)
          ((FirstNodes M).getD J 0) = true := by
        simpa [nextR] using hnext0
      have hh := hn
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
      simpa [f] using hh.1.1.1.2
    have hfpos : 0 < f := by
      have htf : TrMax M < f := by simpa [f] using htr.2
      omega
    have hef : entry M 1 f = entry ((Br M).getD J []) 1 0 := by
      simpa [f] using entry_FirstNodes_eq_component_mr M J 1 hM hJ
    have he10 : entry M 1 0 < entry M 1 f := by
      rw [hcore1, hef]
      omega
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
    have hp0f : leR M 0 p f = true := by
      have hh := hpnext
      simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
        Bool.and_eq_true] at hh
      simpa [leR] using hh.1.2
    have hep : entry M 0 p < entry M 0 f :=
      ancestor_basic_1 M p f f hM hpf (le_refl _) hp0f
    have hple : p ≤ (Joints M).getD J 0 :=
      nextR0_largest_below M ((Joints M).getD J 0) p f hnext0 hpf hep
    have hparent' : parent M 1 ((FirstNodes M).getD J 0) = p := by
      simpa [f] using hparent
    rw [hparent']
    omega

private theorem entry_IncrFirstN0_mr (n : ℕ) (M : PS) (j : ℕ)
    (hj : j < Lng M) :
    entry (IncrFirstN n M) 0 j = entry M 0 j + n := by
  have hL : j < Lng (IncrFirstN n M) := by simpa using hj
  rw [entry0_eq_fst_getElem_mr (IncrFirstN n M) j hL]
  simp [IncrFirstN_eq_map, List.getElem_map,
    ← entry0_eq_fst_getElem_mr M j hj]

/-- Every branch joint of a positive `coreReduce` lies at or to the right of
the inserted diagonal prefix. -/
theorem joints_coreReduce_ge_m10 (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0)
    (hJ : J < (Br (coreReduce M)).length) :
    entry M 1 0 ≤ (Joints (coreReduce M)).getD J 0 := by
  let m := entry M 1 0
  let B := coreReduce M
  have hm : entry M 1 0 ≠ 0 := by omega
  have hBL : Lng B = m + Lng M := by
    simp [B, m, coreReduce, hm, diagSeq, IncrFirstN_eq_map]
    omega
  have hBT : TPS B := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng B
    rw [hBL]
    omega
  have hmonoB : monoT B = true := by
    have hmultiB := coreReduce_multi_false M hM hmono
    have hcoreB := coreReduce_core M hM
    have hzB : zeroT B = false := by
      have hmpos : 0 < m := by simpa [m] using hpos
      have hMpos := List.length_pos_of_ne_nil hM
      change 0 < Lng M at hMpos
      have hL : 1 < Lng B := by rw [hBL]; omega
      have hLne : Lng B ≠ 1 := by omega
      simp [zeroT, hLne]
    simpa [B, multiT, hzB] using hmultiB
  let f := (FirstNodes B).getD J 0
  have hmtr : m ≤ TrMax B := by
    simpa [m, B] using coreReduce_m10_le_TrMax M hM hpos
  have htr := FirstNodes_TrMax_Joints B J hBT hmonoB (by simpa [B] using hJ)
  have hnext := Joints_nextR_FirstNodes B J hBT hmonoB (by simpa [B] using hJ)
  have hmf : m < f := by
    have htf : TrMax B < f := by simpa [f] using htr.2
    omega
  have hfL : f < Lng B := by
    have hn : nextrel0 B ((Joints B).getD J 0) ((FirstNodes B).getD J 0) = true := by
      simpa [nextR] using hnext
    have hh := hn
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    simpa [f] using hh.1.1.1.2
  have hfdL : f - m < Lng M := by rw [hBL] at hfL; omega
  have hfdpos : 0 < f - m := by omega
  have hDlen : Lng (diagSeq 0 (m - 1)) = m := by
    simp [diagSeq, m]
    omega
  have hBform : B = diagSeq 0 (m - 1) ++ IncrFirstN m M := by
    simp [B, coreReduce, m, hm]
  have hrest : ∀ d < Lng M,
      entry B 0 (m + d) = entry M 0 d + m := by
    intro d hd
    rw [hBform, entry_append_right_mr (diagSeq 0 (m - 1))
      (IncrFirstN m M) 0 (m + d) (by rw [hDlen]; omega)]
    rw [hDlen]
    have hsub : m + d - m = d := by omega
    rw [hsub]
    exact entry_IncrFirstN0_mr m M d hd
  have heBm : entry B 0 m = entry M 0 0 + m := by
    have hMpos := List.length_pos_of_ne_nil hM
    simpa using hrest 0 hMpos
  have heBf : entry B 0 f = entry M 0 (f - m) + m := by
    have hfEq : f = m + (f - m) := by omega
    have hh := hrest (f - m) hfdL
    rw [← hfEq] at hh
    exact hh
  have hfull : leR M 0 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hstrictM : entry M 0 0 < entry M 0 (f - m) :=
    ancestor_basic_1 M 0 (f - m) (Lng M - 1) hM hfdpos (by omega) hfull
  have hstrictB : entry B 0 m < entry B 0 f := by omega
  have hmjoint : m ≤ (Joints B).getD J 0 :=
    nextR0_largest_below B ((Joints B).getD J 0) m f hnext hmf hstrictB
  simpa [m, B] using hmjoint

def branchNP (M : PS) (J : ℕ) : ℕ :=
  if entry ((Br M).getD J []) 1 0 = 0 then 0
  else parent M 1 ((FirstNodes M).getD J 0) + 1

def branchE (M : PS) (J : ℕ) : ℕ :=
  (Joints M).getD J 0 + 1 - branchNP M J

theorem redNJ_entry0_mr (M : PS) (J : ℕ) :
    entry (redNJ M J) 0 0 = entry M 0 0 + (Joints M).getD J 0 + 1 := by
  simp [redNJ, entry]

theorem redNJ_entry1_mr (M : PS) (J : ℕ) :
    entry (redNJ M J) 1 0 = entry M 1 0 + branchNP M J := by
  simp [redNJ, branchNP, entry]

theorem Red_zero_mr (M : PS) (hz : zeroT M = true) :
    Red M = [(0, 0)] := by
  unfold Red
  rw [RedAux, if_pos hz]

/-- The core/non-trunk equation for `Red`, with every recursive fuel call
replaced by the total `Red` supplied by well-definedness. -/
theorem Red_core_nontrunk_mr (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M ≠ Lng M - 1) :
    Red M = diagSeq 0 (TrMax M) ++
      (List.range (Br M).length).flatMap (fun J =>
        IncrFirstN (branchE M J) (Red (redNJ M J))) := by
  have hz : zeroT M = false := by
    have hh := hmono
    simp [monoT] at hh
    exact hh.1
  have hmulti : multiT M = false := by simp [multiT, hmono]
  change RedAux (nu M + 1) M = _
  rw [RedAux, if_neg (by simpa using hz), if_neg (by simpa using hmulti),
    if_pos hcore, if_neg ht]
  congr 1
  apply List.flatMap_congr
  intro J hJmem
  have hJ : J < (Br M).length := List.mem_range.mp hJmem
  have hbT := Br_component_TPS M J hM hJ
  have hNJT : TPS (redNJ M J) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [redNJ_length M J hbT]
    exact List.length_pos_of_ne_nil hbT
  have hdesc := nu_redNJ_lt M J hM hmono hcore hJ
  change IncrFirstN _ (RedAux (nu M) (redNJ M J)) =
    IncrFirstN (branchE M J) (Red (redNJ M J))
  have he : (Joints M).getD J 0 + 1 -
      (if entry ((Br M).getD J []) 1 0 = 0 then 0
       else parent M 1 ((FirstNodes M).getD J 0) + 1) = branchE M J := by
    rfl
  rw [he, RedAux_stable (redNJ M J) hNJT (nu M) hdesc]

private theorem branchNP_le_Red_entry_mr (M : PS) (J k : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hJ : J < (Br M).length) (hk : k < Lng (Red (redNJ M J))) :
    branchNP M J ≤ entry (Red (redNJ M J)) 0 k := by
  have hbT := Br_component_TPS M J hM hJ
  have hNJT : TPS (redNJ M J) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [redNJ_length M J hbT]
    exact List.length_pos_of_ne_nil hbT
  have hNJmulti := redNJ_multi_false M J hM hmono hcore.1 hJ
  have hnp := redNJ_np_le_joint M J hM hmono hcore.2 hJ
  have hguard : entry (redNJ M J) 1 0 ≤ entry (redNJ M J) 0 0 := by
    rw [redNJ_entry0_mr, redNJ_entry1_mr, hcore.1, hcore.2]
    simpa [branchNP] using hnp
  have hroot := Red_leftend_ge_row1_nonmulti (redNJ M J) hNJT hNJmulti hguard
  have hroot' : branchNP M J ≤ entry (Red (redNJ M J)) 0 0 := by
    rw [redNJ_entry1_mr, hcore.2] at hroot
    simpa using hroot
  by_cases hz : zeroT (redNJ M J) = true
  · have he1 : entry (redNJ M J) 1 0 = 0 := by
      have hh := hz
      simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
      exact hh.2
    rw [redNJ_entry1_mr, hcore.2] at he1
    omega
  · have hNJmono : monoT (redNJ M J) = true := by
      have hh := hNJmulti
      simp [multiT, hz] at hh
      exact hh
    have hmin := Red_leftend_row0_min (redNJ M J) hNJT hNJmono k hk
    omega

theorem branch_block_row0_ge_joint_mr (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hJ : J < (Br M).length) (p : ℕ × ℕ)
    (hp : p ∈ IncrFirstN (branchE M J) (Red (redNJ M J))) :
    (Joints M).getD J 0 + 1 ≤ p.1 := by
  rw [IncrFirstN_eq_map] at hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hq
  have hqentry : q.1 = entry (Red (redNJ M J)) 0 k := by
    rw [entry0_eq_fst_getElem_mr (Red (redNJ M J)) k hk]
    exact congrArg Prod.fst hget.symm
  have hnpEntry := branchNP_le_Red_entry_mr M J k hM hmono hcore hJ hk
  have hnpJoint := redNJ_np_le_joint M J hM hmono hcore.2 hJ
  change (Joints M).getD J 0 + 1 ≤ q.1 + branchE M J
  simp only [branchE]
  rw [hqentry]
  have hnpJoint' : branchNP M J ≤ (Joints M).getD J 0 + 1 := by
    simpa [branchNP] using hnpJoint
  omega

/-- Every index in the branch tail of `Red (coreReduce M)` has row zero
strictly above the original positive `m₁₀` anchor. -/
theorem redB_tail_row0_above_anchor (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    ∀ j, TrMax (coreReduce M) < j → j < Lng (Red (coreReduce M)) →
      entry M 1 0 < entry (Red (coreReduce M)) 0 j := by
  let B := coreReduce M
  have hBT : TPS B := by
    apply List.ne_nil_of_length_pos
    have hm : entry M 1 0 ≠ 0 := by omega
    change 0 < Lng B
    simp [B, coreReduce, hm, diagSeq, IncrFirstN_eq_map]
  have hmonoB : monoT B = true := by
    have hmultiB := coreReduce_multi_false M hM hmono
    have hcoreB := coreReduce_core M hM
    have hBL : Lng B = entry M 1 0 + Lng M := by
      have hm : entry M 1 0 ≠ 0 := by omega
      simp [B, coreReduce, hm, diagSeq, IncrFirstN_eq_map]
      omega
    have hMpos := List.length_pos_of_ne_nil hM
    change 0 < Lng M at hMpos
    have hzB : zeroT B = false := by
      have hLne : Lng B ≠ 1 := by omega
      simp [zeroT, hLne]
    simpa [B, multiT, hzB] using hmultiB
  have hcoreB : entry B 0 0 = 0 ∧ entry B 1 0 = 0 := by
    simpa [B] using coreReduce_core M hM
  intro j htj hjL
  have htjB : TrMax B < j := by simpa [B] using htj
  have hjLB : j < Lng (Red B) := by simpa [B] using hjL
  by_cases ht : TrMax B = Lng B - 1
  · have hLR := Lng_Red_invariance B hBT
    omega
  · let tail := (List.range (Br B).length).flatMap (fun J =>
        IncrFirstN (branchE B J) (Red (redNJ B J)))
    have hred : Red B = diagSeq 0 (TrMax B) ++ tail := by
      simpa [tail] using Red_core_nontrunk_mr B hBT hmonoB hcoreB ht
    have hDlen : Lng (diagSeq 0 (TrMax B)) = TrMax B + 1 := by
      simp [diagSeq]
    have hjD : Lng (diagSeq 0 (TrMax B)) ≤ j := by omega
    let k := j - Lng (diagSeq 0 (TrMax B))
    have hk : k < Lng tail := by
      have hjTotal := hjLB
      rw [hred] at hjTotal
      simp only [List.length_append] at hjTotal
      change j < Lng (diagSeq 0 (TrMax B)) + Lng tail at hjTotal
      change j - Lng (diagSeq 0 (TrMax B)) < Lng tail
      omega
    have he : entry (Red B) 0 j = entry tail 0 k := by
      rw [hred]
      exact entry_append_right_mr (diagSeq 0 (TrMax B)) tail 0 j hjD
    have htailEntry : entry tail 0 k = tail[k].1 :=
      entry0_eq_fst_getElem_mr tail k hk
    have hmem : tail[k] ∈ tail := List.getElem_mem hk
    change tail[k] ∈ (List.range (Br B).length).flatMap (fun J =>
      IncrFirstN (branchE B J) (Red (redNJ B J))) at hmem
    rcases List.mem_flatMap.mp hmem with ⟨J, hJmem, hp⟩
    have hJ : J < (Br B).length := List.mem_range.mp hJmem
    have hjoint := branch_block_row0_ge_joint_mr B J hBT hmonoB hcoreB hJ tail[k] hp
    have hmjoint : entry M 1 0 ≤ (Joints B).getD J 0 := by
      simpa [B] using joints_coreReduce_ge_m10 M J hM hmono hpos
        (by simpa [B] using hJ)
    change entry M 1 0 < entry (Red B) 0 j
    rw [he, htailEntry]
    omega

/-- The positive diagonal anchor is the strict row-zero minimum of the
suffix of `Red (coreReduce M)` beginning at that anchor. -/
theorem redB_row0_strict_suffix_min (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    entry (Red (coreReduce M)) 0 (entry M 1 0) = entry M 1 0 ∧
      ∀ j, entry M 1 0 < j → j < Lng (Red (coreReduce M)) →
        entry M 1 0 < entry (Red (coreReduce M)) 0 j := by
  constructor
  · exact redB_prefix_diag M hM hmono hpos 0 (entry M 1 0) (le_refl _)
  · intro j hmj hjL
    by_cases hjtr : j ≤ TrMax (coreReduce M)
    · have he := Red_core_prefix_diag (coreReduce M) (by
          have hmulti := coreReduce_multi_false M hM hmono
          have hcore := coreReduce_core M hM
          have hBL : Lng (coreReduce M) = entry M 1 0 + Lng M := by
            have hm : entry M 1 0 ≠ 0 := by omega
            simp [coreReduce, hm, diagSeq, IncrFirstN_eq_map]
            omega
          have hMpos := List.length_pos_of_ne_nil hM
          change 0 < Lng M at hMpos
          have hz : zeroT (coreReduce M) = false := by
            have hLne : Lng (coreReduce M) ≠ 1 := by omega
            simp [zeroT, hLne]
          simpa [multiT, hz] using hmulti)
        (coreReduce_core M hM) 0 j hjtr
      omega
    · exact redB_tail_row0_above_anchor M hM hmono hpos j (by omega) hjL

/-- The positive-`m₁₀` instance of the paper's monoT/Red proposition.  It is
the guard required by the fifth branch of `Red`. -/
theorem monoT_Red_m10pos (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    let N := Red (coreReduce M)
    let S := seg N (entry M 1 0) (Lng N - 1)
    TPS S ∧ monoT S = true := by
  let m := entry M 1 0
  let B := coreReduce M
  let N := Red B
  let jN := Lng N - 1
  let S := seg N m jN
  have hBL : Lng B = m + Lng M := by
    have hm : entry M 1 0 ≠ 0 := by omega
    simp [B, m, coreReduce, hm, diagSeq, IncrFirstN_eq_map]
    omega
  have hBT : TPS B := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng B
    rw [hBL]
    omega
  have hNL : Lng N = m + Lng M := by
    calc
      Lng N = Lng B := Lng_Red_invariance B hBT
      _ = m + Lng M := hBL
  have hMpos := List.length_pos_of_ne_nil hM
  change 0 < Lng M at hMpos
  have hmN : m < Lng N := by rw [hNL]; omega
  have hmj : m ≤ jN := by simp [jN]; omega
  have hSL : Lng S = jN + 1 - m := by simp [S]
  have hST : TPS S := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng S
    rw [hSL]
    omega
  have hNT : TPS N := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng N
    omega
  have hstrict := (redB_row0_strict_suffix_min M hM hmono hpos).2
  have hmonoS : monoT S = true := by
    by_cases heq : m = jN
    · have hS1 : Lng S = 1 := by rw [hSL, ← heq]; omega
      have he1N : entry N 1 m = m := by
        simpa [N, B, m] using
          redB_prefix_diag M hM hmono hpos 1 (entry M 1 0) (le_refl _)
      have he1S : entry S 1 0 = m := by
        have he := entry_seg N m jN 1 0 (by rw [hSL]; omega)
        simpa [S] using he.trans he1N
      have hzS : zeroT S = false := by
        simp [zeroT, hS1, he1S]
        omega
      have hleS : leR S 0 0 (Lng S - 1) = true := by
        simp [hS1, leR, le0, le0Aux]
      simp [monoT, hzS, hleS]
    · have hlt : m < jN := by omega
      have hjNL : jN < Lng N := by simp [jN]; omega
      have hanc : leR N 0 m jN = true := by
        apply parent_exists_3 N m jN hNT hlt hjNL
        intro j hmj' hjj
        have hjLN : j < Lng N := hjj.trans_lt hjNL
        have hs := hstrict j hmj' (by simpa [N, B, m] using hjLN)
        have hanchor := (redB_row0_strict_suffix_min M hM hmono hpos).1
        have hanchorN : entry N 0 m = m := by simpa [N, B, m] using hanchor
        have hsN : m < entry N 0 j := by simpa [N, B, m] using hs
        omega
      exact mono_ancestor_slice N m jN hNT hlt hanc
  simpa [N, B, S, m, jN] using And.intro hST hmonoS

end PSS

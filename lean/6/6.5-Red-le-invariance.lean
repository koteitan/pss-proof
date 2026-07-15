import «6».«6.5-P-Red-equivariance»

/-!
# §6.5 系（直系先祖の `Red` 不変性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_le`
- 訂正: A4（原文の `TPS` 版は偽。`anchoredSlice` 上に制限）
- Isabelle: `m_6_5_Red_le_final`, `m_6_5_congR_self_Red_monoT`
- 依存: `6.5-Red-preserves-monoT`, `6.5-monoT-Red`, `PSS.Standard`
- 状態: 🚨 証明作業中
-/

namespace PSS

/-! ## Row-zero rebasing preserves the ancestor structure -/

/-- Uniformly subtract `c` and add `d` on row zero, leaving row one fixed. -/
def rebaseRow0 (c d : ℕ) (M : PS) : PS :=
  M.map (fun p => (p.1 - c + d, p.2))

@[simp] theorem length_rebaseRow0 (c d : ℕ) (M : PS) :
    Lng (rebaseRow0 c d M) = Lng M := by simp [rebaseRow0]

theorem entry_rebaseRow0_zero (c d : ℕ) (M : PS) (j : ℕ)
    (hj : j < Lng M) :
    entry (rebaseRow0 c d M) 0 j = entry M 0 j - c + d := by
  simp [rebaseRow0, entry, hj]

theorem entry_rebaseRow0_one (c d : ℕ) (M : PS) (j : ℕ) :
    entry (rebaseRow0 c d M) 1 j = entry M 1 j := by
  simp only [rebaseRow0, entry, List.getElem?_map]
  cases h : M[j]? <;> simp [h]

private theorem rebase_lt_iff (c d x y : ℕ) (hx : c ≤ x) (hy : c ≤ y) :
    x - c + d < y - c + d ↔ x < y := by omega

private theorem rebase_le_iff (c d x y : ℕ) (hx : c ≤ x) (hy : c ≤ y) :
    x - c + d ≤ y - c + d ↔ x ≤ y := by omega

theorem nextrel0_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    nextrel0 (rebaseRow0 c d M) = nextrel0 M := by
  funext a b
  by_cases ha : a < Lng M
  · by_cases hb : b < Lng M
    · simp only [nextrel0, length_rebaseRow0]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, List.mem_range]
      simp only [ha, hb, true_and]
      constructor
      · rintro ⟨⟨hab, hentry⟩, hall⟩
        refine ⟨⟨hab, ?_⟩, ?_⟩
        · rw [entry_rebaseRow0_zero c d M a ha,
            entry_rebaseRow0_zero c d M b hb] at hentry
          exact (rebase_lt_iff c d _ _ (hfloor a ha) (hfloor b hb)).mp hentry
        · intro j hj
          have hjL : j < Lng M := hj.trans hb
          have hh := hall j hj
          by_cases haj : a < j
          · simp only [haj, decide_true, Bool.not_true, Bool.false_or] at hh ⊢
            rw [entry_rebaseRow0_zero c d M b hb,
              entry_rebaseRow0_zero c d M j hjL] at hh
            exact decide_eq_true ((rebase_le_iff c d _ _
              (hfloor b hb) (hfloor j hjL)).mp (of_decide_eq_true hh))
          · simpa [haj]
      · rintro ⟨⟨hab, hentry⟩, hall⟩
        refine ⟨⟨hab, ?_⟩, ?_⟩
        · rw [entry_rebaseRow0_zero c d M a ha,
            entry_rebaseRow0_zero c d M b hb]
          exact (rebase_lt_iff c d _ _ (hfloor a ha) (hfloor b hb)).mpr hentry
        · intro j hj
          have hjL : j < Lng M := hj.trans hb
          have hh := hall j hj
          by_cases haj : a < j
          · simp only [haj, decide_true, Bool.not_true, Bool.false_or] at hh ⊢
            rw [entry_rebaseRow0_zero c d M b hb,
              entry_rebaseRow0_zero c d M j hjL]
            exact decide_eq_true ((rebase_le_iff c d _ _
              (hfloor b hb) (hfloor j hjL)).mpr (of_decide_eq_true hh))
          · simpa [haj]
    · simp [nextrel0, hb]
  · simp [nextrel0, ha]

private theorem le0Aux_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j)
    (fuel a b : ℕ) :
    le0Aux (rebaseRow0 c d M) fuel a b = le0Aux M fuel a b := by
  induction fuel generalizing b with
  | zero => rfl
  | succ fuel ih =>
      simp only [le0Aux, nextrel0_rebaseRow0 c d M hfloor, ih]

theorem le0_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    le0 (rebaseRow0 c d M) = le0 M := by
  funext a b
  simp [le0, le0Aux_rebaseRow0 c d M hfloor]

theorem nextrel1_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    nextrel1 (rebaseRow0 c d M) = nextrel1 M := by
  funext a b
  by_cases ha : a < Lng M
  · by_cases hb : b < Lng M
    · simp [nextrel1, ha, hb, entry_rebaseRow0_one,
        le0_rebaseRow0 c d M hfloor]
    · simp [nextrel1, hb]
  · simp [nextrel1, ha]

private theorem le1Aux_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j)
    (fuel a b : ℕ) :
    le1Aux (rebaseRow0 c d M) fuel a b = le1Aux M fuel a b := by
  induction fuel generalizing b with
  | zero => rfl
  | succ fuel ih =>
      simp only [le1Aux, nextrel1_rebaseRow0 c d M hfloor, ih]

theorem le1_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    le1 (rebaseRow0 c d M) = le1 M := by
  funext a b
  simp [le1, le1Aux_rebaseRow0 c d M hfloor]

theorem nextR_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    nextR (rebaseRow0 c d M) = nextR M := by
  funext i a b
  by_cases hi : i = 0
  · simp [nextR, hi, nextrel0_rebaseRow0 c d M hfloor]
  · simp [nextR, hi, nextrel1_rebaseRow0 c d M hfloor]

theorem leR_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j) :
    leR (rebaseRow0 c d M) = leR M := by
  funext i a b
  by_cases hi : i = 0
  · simp [leR, hi, le0_rebaseRow0 c d M hfloor]
  · simp [leR, hi, le1_rebaseRow0 c d M hfloor]

/-! ## Coefficient condition (A) on the trunk -/

theorem RedCondA_apply (M : PS) (hA : RedCondA M = true)
    (i j : ℕ) (hi : i < 2) (hj : j < Lng M)
    (hp : hasParent M i j = true) :
    entry M i (parent M i j) + 1 = entry M i j := by
  have hh := hA
  simp only [RedCondA, List.all_eq_true, List.mem_range] at hh
  have hh' := hh i hi j hj
  simp [hp] at hh'
  exact hh'

theorem RedCondA_intro (M : PS)
    (h : ∀ i j, i < 2 → j < Lng M → hasParent M i j = true →
      entry M i (parent M i j) + 1 = entry M i j) :
    RedCondA M = true := by
  simp only [RedCondA, List.all_eq_true, List.mem_range]
  intro i hi j hj
  by_cases hp : hasParent M i j = true
  · simp [hp, h i j hi hj hp]
  · have hp' : hasParent M i j = false := Bool.eq_false_of_not_eq_true hp
    simp [hp']

theorem RedCondA_rebaseRow0 (c d : ℕ) (M : PS)
    (hfloor : ∀ j < Lng M, c ≤ entry M 0 j)
    (hA : RedCondA M = true) :
    RedCondA (rebaseRow0 c d M) = true := by
  apply RedCondA_intro
  intro i j hi hj hp
  have hjM : j < Lng M := by simpa using hj
  have hnxt := nextR_rebaseRow0 c d M hfloor
  have hhas : hasParent (rebaseRow0 c d M) i j = hasParent M i j := by
    simp [hasParent, parents, length_rebaseRow0, hnxt]
  have hpar : parent (rebaseRow0 c d M) i j = parent M i j := by
    simp [parent, parents, length_rebaseRow0, hnxt]
  have hpM : hasParent M i j = true := by simpa [hhas] using hp
  have hnext := hasParent_next_fseq M i j hpM
  have hpj : parent M i j < j := by
    by_cases hi0 : i = 0
    · have hh : nextrel0 M (parent M i j) j = true := by
        simpa [nextR, hi0] using hnext
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hh
      exact hh.1.1.2
    · have hh : nextrel1 M (parent M i j) j = true := by
        simpa [nextR, hi0] using hnext
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hh
      exact hh.1.1.1.2
  have hpL : parent M i j < Lng M := hpj.trans hjM
  have hbase := RedCondA_apply M hA i j hi hjM hpM
  rw [hpar]
  by_cases hi0 : i = 0
  · subst i
    rw [entry_rebaseRow0_zero c d M (parent M 0 j) hpL,
      entry_rebaseRow0_zero c d M j hjM]
    have hfp := hfloor (parent M 0 j) hpL
    have hfj := hfloor j hjM
    omega
  · have hi1 : i = 1 := by omega
    subst i
    simpa [entry_rebaseRow0_one] using hbase

theorem RedCondA_seg (M : PS) (s e : ℕ)
    (hse : s ≤ e) (he : e < Lng M)
    (hA : RedCondA M = true) :
    RedCondA (seg M s e) = true := by
  apply RedCondA_intro
  intro i q hi hq hpS
  let p := parent (seg M s e) i q
  have hnextS : nextR (seg M s e) i p q = true :=
    hasParent_next_fseq (seg M s e) i q hpS
  have hpq : p < q := by
    by_cases hi0 : i = 0
    · have hh : nextrel0 (seg M s e) p q = true := by
        simpa [nextR, hi0] using hnextS
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hh
      exact hh.1.1.2
    · have hh : nextrel1 (seg M s e) p q = true := by
        simpa [nextR, hi0] using hnextS
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hh
      exact hh.1.1.1.2
  have hpSbound : p < Lng (seg M s e) := hpq.trans hq
  have hnextM : nextR M i (s + p) (s + q) = true := by
    simpa only [nextR_seg_adm M s e i p q hse he hpSbound hq] using hnextS
  have huniqM : ∀ y, nextR M i y (s + q) = true → y = s + p := by
    intro y hy
    by_cases hi0 : i = 0
    · subst i
      exact row0_parent_unique M y (s + p) (s + q) hy hnextM
    · have hi1 : i = 1 := by omega
      subst i
      exact nextR1_unique_mr M y (s + p) (s + q) hy hnextM
  have hpM : hasParent M i (s + q) = true :=
    (hasParent_iff_unique_fseq M i (s + q)).mpr ⟨s + p, hnextM, huniqM⟩
  have hparM : parent M i (s + q) = s + p :=
    parent_eq_of_unique_fseq M i (s + q) (s + p) hnextM huniqM
  have hqM : s + q < Lng M := by
    have hlen : Lng (seg M s e) = e + 1 - s := by simp
    rw [hlen] at hq
    omega
  have hbase := RedCondA_apply M hA i (s + q) hi hqM hpM
  rw [hparM] at hbase
  have hep := entry_seg M s e i p hpSbound
  have heq := entry_seg M s e i q hq
  simpa [p, hep, heq] using hbase

private theorem le0Aux_adjacent (M : PS) (fuel j : ℕ)
    (h : le0Aux M fuel j (j + 1) = true) :
    nextrel0 M j (j + 1) = true := by
  cases fuel with
  | zero => simp [le0Aux] at h
  | succ fuel =>
      have hne : (j == j + 1) = false := by simp
      simp only [le0Aux, hne, Bool.false_or, List.any_eq_true] at h
      rcases h with ⟨p, hpMem, hp⟩
      simp only [Bool.and_eq_true] at hp
      rcases hp with ⟨hpNext, hpAnc⟩
      have hpLt : p < j + 1 := List.mem_range.mp hpMem
      have hjp : j ≤ p := le0Aux_index_fseq hpAnc
      have : p = j := by omega
      simpa [this] using hpNext

theorem le0_adjacent (M : PS) (j : ℕ)
    (h : le0 M j (j + 1) = true) :
    nextrel0 M j (j + 1) = true := by
  have hh := h
  simp only [le0, Bool.and_eq_true] at hh
  exact le0Aux_adjacent M (Lng M) j hh.2

theorem trunk_entries_offset (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (j : ℕ) (hj : j ≤ TrMax M) :
    entry M 0 j = entry M 0 0 + j ∧
      entry M 1 j = entry M 1 0 + j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjtr : j < TrMax M := by omega
      have hstep1 := TrMax_trunk_step M j hM hjtr
      have hstep1' : nextrel1 M j (j + 1) = true := by
        simpa [nextR] using hstep1
      have hle0 : le0 M j (j + 1) = true := by
        have hh := hstep1'
        simp only [nextrel1, Bool.and_eq_true] at hh
        exact hh.1.2
      have hstep0' := le0_adjacent M j hle0
      have hstep0 : nextR M 0 j (j + 1) = true := by
        simpa [nextR] using hstep0'
      have hhas0 : hasParent M 0 (j + 1) = true :=
        (hasParent_iff_unique_fseq M 0 (j + 1)).mpr
          ⟨j, hstep0, fun q hq => row0_parent_unique M q j (j + 1) hq hstep0⟩
      have hpar0 : parent M 0 (j + 1) = j :=
        parent_eq_of_nextR0 M j (j + 1) hstep0
      have hhas1 : hasParent M 1 (j + 1) = true :=
        (hasParent_iff_unique_fseq M 1 (j + 1)).mpr
          ⟨j, hstep1, fun q hq => nextR1_unique_mr M q j (j + 1) hq hstep1⟩
      have hpar1 : parent M 1 (j + 1) = j :=
        parent_eq_of_unique_fseq M 1 (j + 1) j hstep1
          (fun q hq => nextR1_unique_mr M q j (j + 1) hq hstep1)
      have hjL : j + 1 < Lng M := by
        have ht := TrMax_bound M hM
        omega
      have hA0 := RedCondA_apply M hA 0 (j + 1) (by omega) hjL hhas0
      have hA1 := RedCondA_apply M hA 1 (j + 1) (by omega) hjL hhas1
      rw [hpar0] at hA0
      rw [hpar1] at hA1
      have hi := ih (by omega)
      constructor <;> omega

theorem core_trunk_eq_diag (M : PS) (hM : TPS M)
    (hA : RedCondA M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M = Lng M - 1) :
    M = diagSeq 0 (Lng M - 1) := by
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  apply List.ext_getElem
  · have hlen : Lng M - 1 + 1 = Lng M := by omega
    simp [diagSeq, hlen]
  · intro n hnM hnD
    have hnM' : n < Lng M := by simpa using hnM
    have hn : n ≤ TrMax M := by rw [ht]; omega
    have he := trunk_entries_offset M hM hA n hn
    rw [hcore.1, hcore.2] at he
    have hMn : M[n] = (n, n) := by
      apply Prod.ext
      · simpa [entry, List.getElem?_eq_getElem hnM] using he.1
      · simpa [entry, List.getElem?_eq_getElem hnM] using he.2
    rw [hMn]
    simp [diagSeq, List.getElem_map, List.getElem_range']

theorem trunk_take_eq_diag (M : PS) (hM : TPS M)
    (hA : RedCondA M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0) :
    M.take (TrMax M + 1) = diagSeq 0 (TrMax M) := by
  have hbound := TrMax_bound M hM
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  apply List.ext_getElem
  · have hle : TrMax M + 1 ≤ M.length := by
      change TrMax M + 1 ≤ Lng M
      omega
    simp [diagSeq, Nat.min_eq_left hle]
  · intro n hnT hnD
    have hnT' : n ≤ TrMax M ∧ n < M.length := by simpa using hnT
    have hn : n ≤ TrMax M := hnT'.1
    have hnM : n < Lng M := by omega
    have he := trunk_entries_offset M hM hA n hn
    rw [hcore.1, hcore.2] at he
    have hMn : M[n] = (n, n) := by
      apply Prod.ext
      · simpa [entry, List.getElem?_eq_getElem hnM] using he.1
      · simpa [entry, List.getElem?_eq_getElem hnM] using he.2
    rw [List.getElem_take, hMn]
    simp [diagSeq, List.getElem_map, List.getElem_range']

/-! ## The core branch blocks under coefficient condition (A) -/

theorem redNJ_eq_Br_component (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hA : RedCondA M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hJ : J < (Br M).length) :
    redNJ M J = (Br M).getD J [] := by
  let B := (Br M).getD J []
  let f := (FirstNodes M).getD J 0
  let q := (Joints M).getD J 0
  have hBT : TPS B := by simpa [B] using Br_component_TPS M J hM hJ
  have htr := FirstNodes_TrMax_Joints M J hM hmono hJ
  have hnext0 : nextR M 0 q f = true := by
    simpa [q, f] using Joints_nextR_FirstNodes M J hM hmono hJ
  have hfL : f < Lng M := by
    have hh : nextrel0 M q f = true := by simpa [nextR] using hnext0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hh
    exact hh.1.1.1.2
  have hp0 : hasParent M 0 f = true :=
    (hasParent_iff_unique_fseq M 0 f).mpr
      ⟨q, hnext0, fun y hy => row0_parent_unique M y q f hy hnext0⟩
  have hpar0 : parent M 0 f = q :=
    parent_eq_of_unique_fseq M 0 f q hnext0
      (fun y hy => row0_parent_unique M y q f hy hnext0)
  have heq := trunk_entries_offset M hM hA q (by simpa [q] using htr.1)
  have hA0 := RedCondA_apply M hA 0 f (by omega) hfL hp0
  rw [hpar0, heq.1, hcore.1] at hA0
  have hB0 : entry B 0 0 = q + 1 := by
    have hef : entry M 0 f = entry B 0 0 := by
      simpa [B, f] using entry_FirstNodes_eq_component_mr M J 0 hM hJ
    rw [← hef]
    omega
  have hB1 : entry B 1 0 = branchNP M J := by
    by_cases hz : entry B 1 0 = 0
    · unfold branchNP
      change entry B 1 0 = if entry B 1 0 = 0 then 0
        else parent M 1 f + 1
      rw [if_pos hz]
      exact hz
    · have hef : entry M 1 f = entry B 1 0 := by
        simpa [B, f] using entry_FirstNodes_eq_component_mr M J 1 hM hJ
      have hfpos : 0 < f := by
        have := htr.2
        omega
      have hroot : leR M 0 0 (Lng M - 1) = true := by
        have hh := hmono
        simp only [monoT, Bool.and_eq_true] at hh
        exact hh.2
      have h0f : leR M 0 0 f = true :=
        ancestor_tree_1 M 0 f (Lng M - 1) hM hroot (Nat.zero_le _) (by omega)
      obtain ⟨p, _, hpf, hpnext⟩ :=
        parent_exists_2 M 0 f hM hfpos hfL (by rw [hcore.2, hef]; omega) h0f
      have huniq : ∀ y, nextR M 1 y f = true → y = p := by
        intro y hy
        exact nextR1_unique_mr M y p f hy hpnext
      have hp1 : hasParent M 1 f = true :=
        (hasParent_iff_unique_fseq M 1 f).mpr ⟨p, hpnext, huniq⟩
      have hpar1 : parent M 1 f = p :=
        parent_eq_of_unique_fseq M 1 f p hpnext huniq
      have hnple := redNJ_np_le_joint M J hM hmono hcore.2 hJ
      have hpq : p ≤ q := by
        change (if entry B 1 0 = 0 then 0 else parent M 1 f + 1) ≤ q + 1 at hnple
        rw [if_neg hz, hpar1] at hnple
        omega
      have hep := trunk_entries_offset M hM hA p (hpq.trans htr.1)
      have hA1 := RedCondA_apply M hA 1 f (by omega) hfL hp1
      rw [hpar1, hep.2, hcore.2] at hA1
      have hefval : entry M 1 f = p + 1 := by omega
      rw [hef] at hefval
      have hnp : branchNP M J = p + 1 := by
        unfold branchNP
        change (if entry B 1 0 = 0 then 0 else parent M 1 f + 1) = p + 1
        rw [if_neg hz, hpar1]
      rw [hnp]
      exact hefval
  have hdecomp : (entry B 0 0, entry B 1 0) :: B.tail = B := by
    cases hB : B with
    | nil => exact (hBT hB).elim
    | cons x xs =>
        rcases x with ⟨x0, x1⟩
        simp [hB, entry]
  change (entry M 0 0 + q + 1, entry M 1 0 + branchNP M J) :: B.tail = B
  rw [hcore.1, hcore.2]
  simpa [hB0, hB1] using hdecomp

theorem RedCondA_Br_component (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hA : RedCondA M = true)
    (hJ : J < (Br M).length) :
    RedCondA ((Br M).getD J []) = true := by
  have hbound := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have hBrnil : Br M = [] := by simp [Br, heq]
    rw [hBrnil] at hJ
    simp at hJ
  let N := seg M (TrMax M + 1) (Lng M - 1)
  let Q := P N
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have htrlt : TrMax M < Lng M - 1 := by omega
  have hBr : Br M = Q := by simp [Q, N, Br, hne]
  have hNlen : Lng N = Lng M - 1 - TrMax M := by simp [N]
  have hNpos : 0 < Lng N := by rw [hNlen]; omega
  have hNT : TPS N := List.ne_nil_of_length_pos hNpos
  have hAN : RedCondA N = true := by
    apply RedCondA_seg M (TrMax M + 1) (Lng M - 1) (by omega) (by omega) hA
  have hJQ : J < Q.length := by simpa [hBr] using hJ
  let a := (IdxSum Q).getD J 0
  let b := (IdxSum Q).getD (J + 1) 0 - 1
  have hJlast : J ≤ (P N).length - 1 := by
    change J ≤ Q.length - 1
    omega
  have hcomp : Q.getD J [] = seg N a b := by
    simpa [Q, a, b] using P_IdxSum N J hNT hJlast
  have hpos : 0 < Lng (Q.getD J []) := by
    simpa [Q] using P_component_nonempty N J hNT (by simpa [Q] using hJQ)
  have hdiff : (IdxSum Q).getD (J + 1) 0 =
      (IdxSum Q).getD J 0 + Lng (Q.getD J []) :=
    idxSum_diff Q J hJQ
  have hsplit : (Q.map Lng).sum =
      ((Q.take (J + 1)).map Lng).sum + ((Q.drop (J + 1)).map Lng).sum := by
    calc
      (Q.map Lng).sum = ((Q.take (J + 1) ++ Q.drop (J + 1)).map Lng).sum := by
        rw [List.take_append_drop]
      _ = _ := by simp
  have htotal : (Q.map Lng).sum = Lng N := by
    have hflat := congrArg Lng (P_concat N)
    simpa [Q, List.length_flatten] using hflat
  have hprefix : (IdxSum Q).getD (J + 1) 0 =
      ((Q.take (J + 1)).map Lng).sum := idxSum_getD Q (J + 1) (by omega)
  have hidxle : (IdxSum Q).getD (J + 1) 0 ≤ Lng N := by
    rw [hprefix, ← htotal, hsplit]
    omega
  have hab : a ≤ b := by
    dsimp [a, b]
    omega
  have hbN : b < Lng N := by
    dsimp [b]
    omega
  have hAB : RedCondA (Q.getD J []) = true := by
    rw [hcomp]
    exact RedCondA_seg N a b hab hbN hAN
  simpa [hBr] using hAB

theorem branch_block_identity (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hA : RedCondA M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hJ : J < (Br M).length)
    (hred : Red ((Br M).getD J []) =
      rebaseRow0 (entry ((Br M).getD J []) 0 0)
        (entry ((Br M).getD J []) 1 0) ((Br M).getD J [])) :
    IncrFirstN (branchE M J) (Red (redNJ M J)) = (Br M).getD J [] := by
  let B := (Br M).getD J []
  let q := (Joints M).getD J 0
  have hBT : TPS B := by simpa [B] using Br_component_TPS M J hM hJ
  have hNJ : redNJ M J = B := by
    simpa [B] using redNJ_eq_Br_component M J hM hmono hA hcore hJ
  have hB0 : entry B 0 0 = q + 1 := by
    rw [← hNJ, redNJ_entry0_mr, hcore.1]
    simp [q]
  have hB1 : entry B 1 0 = branchNP M J := by
    rw [← hNJ, redNJ_entry1_mr, hcore.2]
    simp
  have hnple := redNJ_np_le_joint M J hM hmono hcore.2 hJ
  have hB10 : entry B 1 0 ≤ entry B 0 0 := by
    rw [hB0, hB1]
    simpa [branchNP, q] using hnple
  have he : branchE M J = entry B 0 0 - entry B 1 0 := by
    simp [branchE, hB0, hB1, q]
  have hfloor : ∀ j < Lng B, entry B 0 0 ≤ entry B 0 j := by
    intro j hj
    rcases Br_component_nonmulti M J hM hJ with hz | hm
    · have hL : Lng B = 1 := by
        have hh := hz
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
        simpa [B] using hh.1
      have hj0 : j = 0 := by omega
      subst j
      exact le_refl _
    · exact mono_row0_min_mr B hBT (by simpa [B] using hm) j hj
  have hmap : IncrFirstN (branchE M J)
      (rebaseRow0 (entry B 0 0) (entry B 1 0) B) =
      B.map (fun p =>
        (p.1 - entry B 0 0 + entry B 1 0 + branchE M J, p.2)) := by
    simp [IncrFirstN_eq_map, rebaseRow0, List.map_map]
  rw [hNJ]
  change IncrFirstN (branchE M J) (Red B) = B
  rw [show Red B = rebaseRow0 (entry B 0 0) (entry B 1 0) B by simpa [B] using hred,
    hmap]
  apply List.ext_getElem
  · simp
  · intro n hnmap hnB
    have hn : n < Lng B := by simpa using hnB
    have hfirst : B[n].1 = entry B 0 n := by
      symm
      exact entry0_eq_fst_getElem_mr B n hn
    simp only [List.getElem_map]
    apply Prod.ext
    · simp only [Prod.fst]
      rw [hfirst, he]
      have hf := hfloor n hn
      omega
    · simp

theorem Red_core_fixed_of_condA_trunk (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (ht : TrMax M = Lng M - 1) : Red M = M := by
  calc
    Red M = diagSeq 0 (Lng M - 1) :=
      Red_core_trunk_ri M hM hmono hcore ht
    _ = M := (core_trunk_eq_diag M hM hA hcore ht).symm

theorem coreReduce_zero_eq_rebaseRow0 (M : PS)
    (hm : entry M 1 0 = 0) :
    coreReduce M = rebaseRow0 (entry M 0 0) 0 M := by
  rw [coreReduce, if_pos hm]
  apply List.ext_getElem
  · simp [rebaseRow0]
  · intro n hnC hnR
    have hnM : n < Lng M := by simpa [rebaseRow0] using hnR
    simp [rebaseRow0, List.getElem_map,
      List.getElem_range, entry, List.getElem?_eq_getElem hnM]

theorem core_zeroT_eq_singleton (M : PS) (hM : TPS M)
    (hz : zeroT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0) :
    M = [(0, 0)] := by
  have hL : Lng M = 1 := by
    have hh := hz
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
    exact hh.1
  apply List.ext_getElem
  · simpa using hL
  · intro n hnM hnS
    have hn0 : n = 0 := by simpa using hnS
    subst n
    have h0 : M[0] = (0, 0) := by
      apply Prod.ext
      · simpa [entry, List.getElem?_eq_getElem (by omega : 0 < M.length)] using hcore.1
      · simpa [entry, List.getElem?_eq_getElem (by omega : 0 < M.length)] using hcore.2
    simpa using h0

theorem Red_core_fixed_of_condA (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (IH : ∀ X, Lng X < Lng M → TPS X → RedCondA X = true →
      multiT X = false →
      Red X = rebaseRow0 (entry X 0 0) (entry X 1 0) X) :
    Red M = M := by
  by_cases ht : TrMax M = Lng M - 1
  · exact Red_core_fixed_of_condA_trunk M hM hA hmono hcore ht
  · let blocks := (List.range (Br M).length).map (fun J =>
      IncrFirstN (branchE M J) (Red (redNJ M J)))
    have hred : Red M = diagSeq 0 (TrMax M) ++ blocks.flatten := by
      have hh := Red_core_nontrunk_mr M hM hmono hcore ht
      simpa [blocks] using hh
    have hblock : ∀ J, J < (Br M).length →
        IncrFirstN (branchE M J) (Red (redNJ M J)) =
          (Br M).getD J [] := by
      intro J hJ
      let B := (Br M).getD J []
      have hBT : TPS B := by simpa [B] using Br_component_TPS M J hM hJ
      have hlenBound := Br_component_length_bound M J hM hJ
      have hlen : Lng B < Lng M := by
        have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
        simpa [B] using (show Lng ((Br M).getD J []) < Lng M by omega)
      have hBA : RedCondA B = true := by
        simpa [B] using RedCondA_Br_component M J hM hmono hA hJ
      have hnm : multiT B = false := by
        rcases Br_component_nonmulti M J hM hJ with hz | hm
        · have hzB : zeroT B = true := by simpa [B] using hz
          simp [multiT, hzB]
        · have hmB : monoT B = true := by simpa [B] using hm
          have hzB : zeroT B = false := by
            cases hz : zeroT B with
            | false => rfl
            | true => simp [monoT, hz] at hmB
          simp [multiT, hzB, hmB]
      have hredB := IH B hlen hBT hBA hnm
      exact branch_block_identity M J hM hmono hA hcore hJ (by simpa [B] using hredB)
    have hblocks : blocks = Br M := by
      apply List.ext_getElem
      · simp [blocks]
      · intro n hnBlocks hnBr
        have hn : n < (Br M).length := by simpa [blocks] using hnBlocks
        simp only [blocks, List.getElem_map, List.getElem_range]
        rw [hblock n hn, getD_eq_getElem_idx (Br M) [] hn]
    let N := seg M (TrMax M + 1) (Lng M - 1)
    have hBr : Br M = P N := by simp [N, Br, ht]
    have hdropBound : TrMax M + 1 < Lng M := by
      have hbound := TrMax_bound M hM
      omega
    have hflat : (Br M).flatten = M.drop (TrMax M + 1) := by
      calc
        (Br M).flatten = (P N).flatten := by rw [hBr]
        _ = N := P_concat N
        _ = M.drop (TrMax M + 1) := by
          simpa [N] using (drop_eq_seg M (TrMax M + 1) hdropBound).symm
    calc
      Red M = diagSeq 0 (TrMax M) ++ blocks.flatten := hred
      _ = M.take (TrMax M + 1) ++ M.drop (TrMax M + 1) := by
        rw [← trunk_take_eq_diag M hM hA hcore, hblocks, hflat]
      _ = M := List.take_append_drop (TrMax M + 1) M

theorem Red_core_fixed_of_condA_nonmulti (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hnm : multiT M = false)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (IH : ∀ X, Lng X < Lng M → TPS X → RedCondA X = true →
      multiT X = false →
      Red X = rebaseRow0 (entry X 0 0) (entry X 1 0) X) :
    Red M = M := by
  by_cases hz : zeroT M = true
  · rw [Red_zero_mr M hz, core_zeroT_eq_singleton M hM hz hcore]
  · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
    have hmono : monoT M = true := by
      have hh := hnm
      simp [multiT, hz'] at hh
      exact hh
    exact Red_core_fixed_of_condA M hM hA hmono hcore IH

#print axioms leR_rebaseRow0
#print axioms trunk_entries_offset

end PSS

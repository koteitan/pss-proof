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

/-! ## The positive second-coordinate core reduction -/

theorem TrMax_stop_uncond (M : PS) (hM : TPS M) :
    nextR M 1 (TrMax M) (TrMax M + 1) = false := by
  apply Bool.eq_false_iff.mpr
  intro hnot
  have hstep : nextR M 1 (TrMax M) (TrMax M + 1) = true := hnot
  have hle : TrMax M + 1 ≤ TrMax M := by
    apply le_TrMax_intro_wd M (TrMax M + 1) hM
    intro j hj
    by_cases heq : j = TrMax M
    · simpa [heq] using hstep
    · exact TrMax_trunk_step M j hM (by omega)
  omega

theorem TrMax_coreReduce_pos (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    TrMax (coreReduce M) = entry M 1 0 + TrMax M := by
  let m := entry M 1 0
  have hm : entry M 1 0 ≠ 0 := by omega
  have hCT := coreReduce_TPS M hM
  have hlower := TrMax_coreReduce_pos_shift M hM hmono hpos
  apply Nat.le_antisymm ?_ hlower
  by_contra hnot
  have hlt : m + TrMax M < TrMax (coreReduce M) := by
    dsimp [m]
    omega
  have hstep := TrMax_trunk_step (coreReduce M) (m + TrMax M) hCT hlt
  have hlenC : Lng (coreReduce M) = m + Lng M := by
    simp [coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
    omega
  have hbound := TrMax_bound M hM
  by_cases ht : TrMax M = Lng M - 1
  · have hright : ¬(m + TrMax M + 1 < Lng (coreReduce M)) := by
      rw [hlenC, ht]
      have hMpos := List.length_pos_of_ne_nil hM
      omega
    have hh := hstep
    simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
      Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hright (by omega)
  · have htrlt : TrMax M < Lng M - 1 := by omega
    have ha : TrMax M < Lng (coreReduce M) - m := by
      rw [hlenC]
      omega
    have hb : TrMax M + 1 < Lng (coreReduce M) - m := by
      rw [hlenC]
      omega
    have hdrop : (coreReduce M).drop m = IncrFirstN m M := by
      rw [coreReduce, if_neg hm]
      have hDlen : Lng (diagSeq 0 (entry M 1 0 - 1)) = m := by
        simp [diagSeq, m]
        omega
      simpa [hDlen, m]
    have hrel := nextR_drop (coreReduce M) m 1 (TrMax M)
      (TrMax M + 1) ha hb
    rw [hdrop, nextR_IncrFirstN_ri] at hrel
    have hstop := TrMax_stop_uncond M hM
    rw [hrel] at hstop
    have hstop' : nextR (coreReduce M) 1 (m + TrMax M)
        (m + TrMax M + 1) = false := by
      simpa [Nat.add_assoc] using hstop
    rw [hstop'] at hstep
    simp at hstep

theorem IncrFirstN_drop (n : ℕ) (M : PS) (k : ℕ) :
    (IncrFirstN n M).drop k = IncrFirstN n (M.drop k) := by
  simp [IncrFirstN_eq_map]

theorem P_IncrFirstN_equivariance (n : ℕ) (M : PS) :
    P (IncrFirstN n M) = (P M).map (IncrFirstN n) := by
  induction n generalizing M with
  | zero => simp [IncrFirstN]
  | succ n ih =>
      rw [IncrFirstN, ih, P_IncrFirst_equivariance]
      simp only [List.map_map]
      apply List.map_congr_left
      intro X hX
      rfl

theorem IdxSum_map_IncrFirstN (n : ℕ) (Q : List PS) :
    IdxSum (Q.map (IncrFirstN n)) = IdxSum Q := by
  unfold IdxSum
  simp only [List.length_map]
  apply List.map_congr_left
  intro a ha
  have htake : (Q.map (IncrFirstN n)).take a =
      (Q.take a).map (IncrFirstN n) := by simp
  rw [htake, List.map_map]
  congr 1
  apply List.map_congr_left
  intro X hX
  simp

theorem Br_coreReduce_pos (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    Br (coreReduce M) = (Br M).map (IncrFirstN (entry M 1 0)) := by
  let m := entry M 1 0
  have hm : entry M 1 0 ≠ 0 := by omega
  have hMpos := List.length_pos_of_ne_nil hM
  have htr := TrMax_coreReduce_pos M hM hmono hpos
  have hlenC : Lng (coreReduce M) = m + Lng M := by
    simp [coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
    omega
  by_cases ht : TrMax M = Lng M - 1
  · have htC : TrMax (coreReduce M) = Lng (coreReduce M) - 1 := by
      dsimp [m] at hlenC ⊢
      calc
        TrMax (coreReduce M) = entry M 1 0 + TrMax M := htr
        _ = entry M 1 0 + (Lng M - 1) := by rw [ht]
        _ = entry M 1 0 + Lng M - 1 := by
          symm
          exact Nat.add_sub_assoc (m := Lng M) (k := 1) hMpos
            (entry M 1 0)
        _ = Lng (coreReduce M) - 1 := by rw [hlenC]
    simp [Br, ht, htC]
  · have hbound := TrMax_bound M hM
    have htrlt : TrMax M < Lng M - 1 := by omega
    have htC : TrMax (coreReduce M) ≠ Lng (coreReduce M) - 1 := by
      dsimp [m] at hlenC ⊢
      rw [htr, hlenC]
      omega
    rw [Br, if_neg htC, Br, if_neg ht]
    have hdropC : TrMax (coreReduce M) + 1 < Lng (coreReduce M) := by
      rw [htr, hlenC]
      omega
    have hdropM : TrMax M + 1 < Lng M := by omega
    rw [← drop_eq_seg (coreReduce M) (TrMax (coreReduce M) + 1) hdropC,
      ← drop_eq_seg M (TrMax M + 1) hdropM]
    rw [htr]
    have hcoreDrop : (coreReduce M).drop (m + TrMax M + 1) =
        IncrFirstN m (M.drop (TrMax M + 1)) := by
      rw [coreReduce, if_neg hm]
      have hDlen : Lng (diagSeq 0 (entry M 1 0 - 1)) = m := by
        simp [diagSeq, m]
        omega
      change List.drop (m + (TrMax M + 1))
          (diagSeq 0 (entry M 1 0 - 1) ++ IncrFirstN m M) =
        IncrFirstN m (M.drop (TrMax M + 1))
      rw [← hDlen]
      simp [IncrFirstN_drop]
    rw [hcoreDrop, P_IncrFirstN_equivariance]

theorem FirstNodes_coreReduce_pos (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    FirstNodes (coreReduce M) =
      (FirstNodes M).map (fun x => entry M 1 0 + x) := by
  rw [FirstNodes, FirstNodes, Br_coreReduce_pos M hM hmono hpos,
    IdxSum_map_IncrFirstN, TrMax_coreReduce_pos M hM hmono hpos]
  simp only [List.map_map]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply]
  omega

theorem FirstNodes_coreReduce_pos_getD (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0)
    (hJ : J < (Br M).length) :
    (FirstNodes (coreReduce M)).getD J 0 =
      entry M 1 0 + (FirstNodes M).getD J 0 := by
  have hFn := FirstNodes_coreReduce_pos M hM hmono hpos
  have hJFnM : J < (FirstNodes M).length := by
    have : J < (Br M).length + 1 := Nat.lt_succ_of_lt hJ
    simpa [FirstNodes, IdxSum] using this
  rw [hFn]
  have hJMap : J < ((FirstNodes M).map
      (fun x => entry M 1 0 + x)).length := by simpa using hJFnM
  rw [getD_eq_getElem_idx _ _ hJMap, List.getElem_map]
  rw [getD_eq_getElem_idx _ _ hJFnM]

theorem nextR_coreReduce_pos_tail (M : PS) (i a b : ℕ) (hM : TPS M)
    (hpos : 0 < entry M 1 0) (ha : a < Lng M) (hb : b < Lng M) :
    nextR (coreReduce M) i (entry M 1 0 + a) (entry M 1 0 + b) =
      nextR M i a b := by
  let m := entry M 1 0
  have hm : entry M 1 0 ≠ 0 := by omega
  have hlenC : Lng (coreReduce M) = m + Lng M := by
    simp [coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
    omega
  have hdrop : (coreReduce M).drop m = IncrFirstN m M := by
    rw [coreReduce, if_neg hm]
    have hDlen : Lng (diagSeq 0 (entry M 1 0 - 1)) = m := by
      simp [diagSeq, m]
      omega
    change List.drop m
        (diagSeq 0 (entry M 1 0 - 1) ++ IncrFirstN m M) =
      IncrFirstN m M
    rw [← hDlen]
    simp
  have haD : a < Lng (coreReduce M) - m := by rw [hlenC]; omega
  have hbD : b < Lng (coreReduce M) - m := by rw [hlenC]; omega
  have hrel := nextR_drop (coreReduce M) m i a b haD hbD
  rw [hdrop, nextR_IncrFirstN_ri] at hrel
  simpa [m] using hrel.symm

theorem IncrFirstN_eq_rebaseRow0_zero (n : ℕ) (M : PS) :
    IncrFirstN n M = rebaseRow0 0 n M := by
  simp [IncrFirstN_eq_map, rebaseRow0]

theorem leR_IncrFirstN (n : ℕ) (M : PS) :
    leR (IncrFirstN n M) = leR M := by
  rw [IncrFirstN_eq_rebaseRow0_zero]
  exact leR_rebaseRow0 0 n M (by intro j hj; omega)

theorem leR_coreReduce_pos_tail (M : PS) (i a b : ℕ) (hM : TPS M)
    (hpos : 0 < entry M 1 0) (ha : a < Lng M) (hb : b < Lng M) :
    leR (coreReduce M) i (entry M 1 0 + a) (entry M 1 0 + b) =
      leR M i a b := by
  let m := entry M 1 0
  have hm : entry M 1 0 ≠ 0 := by omega
  have hlenC : Lng (coreReduce M) = m + Lng M := by
    simp [coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
    omega
  have hdrop : (coreReduce M).drop m = IncrFirstN m M := by
    rw [coreReduce, if_neg hm]
    have hDlen : Lng (diagSeq 0 (entry M 1 0 - 1)) = m := by
      simp [diagSeq, m]
      omega
    change List.drop m
        (diagSeq 0 (entry M 1 0 - 1) ++ IncrFirstN m M) =
      IncrFirstN m M
    rw [← hDlen]
    simp
  have haD : a < Lng (coreReduce M) - m := by rw [hlenC]; omega
  have hbD : b < Lng (coreReduce M) - m := by rw [hlenC]; omega
  have hrel := leR_drop (coreReduce M) m i a b haD hbD
  rw [hdrop, leR_IncrFirstN] at hrel
  simpa [m] using hrel.symm

theorem entry_IncrFirstN_one (n : ℕ) (M : PS) (j : ℕ) :
    entry (IncrFirstN n M) 1 j = entry M 1 j := by
  simp only [IncrFirstN_eq_map, entry, List.getElem?_map]
  cases h : M[j]? <;> simp [h]

theorem entry1_coreReduce_pos_tail (M : PS) (j : ℕ)
    (hpos : 0 < entry M 1 0) (hj : j < Lng M) :
    entry (coreReduce M) 1 (entry M 1 0 + j) = entry M 1 j := by
  let m := entry M 1 0
  have hm : entry M 1 0 ≠ 0 := by omega
  have hDlen : Lng (diagSeq 0 (entry M 1 0 - 1)) = m := by
    simp [diagSeq, m]
    omega
  rw [coreReduce, if_neg hm, entry_append_right_mr]
  · rw [hDlen, show m + j - m = j by omega, entry_IncrFirstN_one]
  · rw [hDlen]
    dsimp [m]
    omega

theorem monoT_coreReduce_pos (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0) :
    monoT (coreReduce M) = true := by
  have hmulti := coreReduce_multi_false M hM hmono
  have hcore := coreReduce_core M hM
  have hm : entry M 1 0 ≠ 0 := by omega
  have hMpos := List.length_pos_of_ne_nil hM
  have hlen : 1 < Lng (coreReduce M) := by
    simp [coreReduce, hm, diagSeq, IncrFirstN_eq_map]
    omega
  have hz : zeroT (coreReduce M) = false := by
    simp [zeroT]
    omega
  simpa [multiT, hz] using hmulti

theorem entry1_coreReduce_trunk_pos (M : PS) (p : ℕ) (hM : TPS M)
    (hA : RedCondA M = true) (hmono : monoT M = true)
    (hpos : 0 < entry M 1 0) (hp : p ≤ TrMax (coreReduce M)) :
    entry (coreReduce M) 1 p = p := by
  let m := entry M 1 0
  have hm : entry M 1 0 ≠ 0 := by omega
  have hDlen : Lng (diagSeq 0 (entry M 1 0 - 1)) = m := by
    simp [diagSeq, m]
    omega
  have htr := TrMax_coreReduce_pos M hM hmono hpos
  rw [coreReduce, if_neg hm]
  by_cases hpm : p < m
  · rw [entry_append_left_mr]
    · exact entry_diagSeq_zero_mr (entry M 1 0 - 1) 1 p (by
        dsimp [m] at hpm
        omega)
    · simpa [hDlen] using hpm
  · let k := p - m
    have hpk : p = m + k := by simp [k]; omega
    have hkTr : k ≤ TrMax M := by
      rw [htr] at hp
      dsimp [m] at hpk ⊢
      omega
    have hbound := TrMax_bound M hM
    have hkM : k < Lng M := by
      have hMpos := List.length_pos_of_ne_nil hM
      have hlast : Lng M - 1 < Lng M :=
        Nat.sub_lt hMpos (by omega)
      exact lt_of_le_of_lt hkTr (lt_of_le_of_lt hbound hlast)
    rw [entry_append_right_mr]
    · rw [hDlen, show p - m = k by rfl, entry_IncrFirstN_one]
      have he := (trunk_entries_offset M hM hA k hkTr).2
      dsimp [m] at he hpk
      omega
    · rw [hDlen]
      omega

theorem Joints_coreReduce_pos_getD (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hpos : 0 < entry M 1 0)
    (hJ : J < (Br M).length) :
    (Joints (coreReduce M)).getD J 0 =
      entry M 1 0 + (Joints M).getD J 0 := by
  let m := entry M 1 0
  let q := (Joints M).getD J 0
  let f := (FirstNodes M).getD J 0
  have hBr := Br_coreReduce_pos M hM hmono hpos
  have hFn := FirstNodes_coreReduce_pos M hM hmono hpos
  have hJBrC : J < (Br (coreReduce M)).length := by
    rw [hBr]
    simpa
  have hJFnM : J < (FirstNodes M).length := by
    have : J < (Br M).length + 1 := Nat.lt.step hJ
    simpa [FirstNodes, IdxSum] using this
  have hFnGet : (FirstNodes (coreReduce M)).getD J 0 = m + f := by
    rw [hFn]
    have hJMap : J < ((FirstNodes M).map
        (fun x => entry M 1 0 + x)).length := by simpa using hJFnM
    rw [getD_eq_getElem_idx _ _ hJMap, List.getElem_map]
    dsimp [m, f]
    rw [getD_eq_getElem_idx _ _ hJFnM]
  have hnextM : nextR M 0 q f = true := by
    simpa [q, f] using Joints_nextR_FirstNodes M J hM hmono hJ
  have hbounds : q < Lng M ∧ f < Lng M := by
    have hh : nextrel0 M q f = true := by simpa [nextR] using hnextM
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hh
    omega
  have hnextC : nextR (coreReduce M) 0 (m + q) (m + f) = true := by
    rw [nextR_coreReduce_pos_tail M 0 q f hM hpos hbounds.1 hbounds.2]
    exact hnextM
  have hparC : parent (coreReduce M) 0 (m + f) = m + q :=
    parent_eq_of_nextR0 (coreReduce M) (m + q) (m + f) hnextC
  rw [getD_eq_getElem_idx _ _ (by simp [Joints]; exact hJBrC)]
  simp only [Joints, List.getElem_map, List.getElem_range]
  rw [hFnGet, hparC]
  rfl

theorem branchNP_coreReduce_pos (M : PS) (J : ℕ) (hM : TPS M)
    (hA : RedCondA M = true) (hmono : monoT M = true)
    (hpos : 0 < entry M 1 0) (hJ : J < (Br M).length) :
    branchNP (coreReduce M) J = entry ((Br M).getD J []) 1 0 := by
  let C := coreReduce M
  let B := (Br M).getD J []
  let m := entry M 1 0
  let b := entry B 1 0
  let q := (Joints M).getD J 0
  let f := (FirstNodes M).getD J 0
  let fC := m + f
  have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
  have hmonoC : monoT C = true := by
    simpa [C] using monoT_coreReduce_pos M hM hmono hpos
  have hBr := Br_coreReduce_pos M hM hmono hpos
  have hJC : J < (Br C).length := by
    simpa [C, hBr] using hJ
  have hBT : TPS B := by simpa [B] using Br_component_TPS M J hM hJ
  have hBC : (Br C).getD J [] = IncrFirstN m B := by
    rw [show Br C = (Br M).map (IncrFirstN m) by simpa [C, m] using hBr]
    rw [getD_eq_getElem_idx _ _ (by simpa using hJ), List.getElem_map]
    dsimp [B]
    rw [getD_eq_getElem_idx _ _ hJ]
  have hBC1 : entry ((Br C).getD J []) 1 0 = b := by
    rw [hBC, entry_IncrFirstN_one]
  by_cases hb : b = 0
  · have hzeroC : entry ((Br C).getD J []) 1 0 = 0 := hBC1.trans hb
    rw [branchNP, if_pos hzeroC]
    change 0 = b
    exact hb.symm
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    have htrM := FirstNodes_TrMax_Joints M J hM hmono hJ
    have hnext0M : nextR M 0 q f = true := by
      simpa [q, f] using Joints_nextR_FirstNodes M J hM hmono hJ
    have hboundsM : q < Lng M ∧ f < Lng M := by
      have hh : nextrel0 M q f = true := by simpa [nextR] using hnext0M
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hh
      omega
    have hfCeq : (FirstNodes C).getD J 0 = fC := by
      simpa [C, m, f, fC] using
        FirstNodes_coreReduce_pos_getD M J hM hmono hpos hJ
    have hqCeq : (Joints C).getD J 0 = m + q := by
      simpa [C, m, q] using
        Joints_coreReduce_pos_getD M J hM hmono hpos hJ
    have he1fM : entry M 1 f = b := by
      simpa [B, b, f] using entry_FirstNodes_eq_component_mr M J 1 hM hJ
    have he1fC : entry C 1 fC = b := by
      change entry (coreReduce M) 1 (entry M 1 0 + f) = b
      rw [entry1_coreReduce_pos_tail M f hpos hboundsM.2]
      exact he1fM
    have hlenC : Lng C = m + Lng M := by
      have hm : entry M 1 0 ≠ 0 := by omega
      simp [C, coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
      omega
    have hfCL : fC < Lng C := by rw [hlenC]; simp [fC]; omega
    have hfCpos : 0 < fC := by simp [fC, m]; omega
    have hcoreC := coreReduce_core M hM
    have he10lt : entry C 1 0 < entry C 1 fC := by
      have he10C : entry C 1 0 = 0 := by simpa [C] using hcoreC.2
      rw [he10C, he1fC]
      exact hbpos
    have hrootC : leR C 0 0 (Lng C - 1) = true := by
      have hh := hmonoC
      simp only [monoT, Bool.and_eq_true] at hh
      exact hh.2
    have h0fC : leR C 0 0 fC = true :=
      ancestor_tree_1 C 0 fC (Lng C - 1) hCT hrootC
        (Nat.zero_le _) (by omega)
    obtain ⟨p, hp0, hpf, hpnext⟩ :=
      parent_exists_2 C 0 fC hCT hfCpos hfCL he10lt h0fC
    have hparC : parent C 1 fC = p :=
      parent_eq_of_unique_fseq C 1 fC p hpnext
        (fun y hy => nextR1_unique_mr C y p fC hy hpnext)
    have hNP : branchNP C J = p + 1 := by
      have hnzC : entry ((Br C).getD J []) 1 0 ≠ 0 := by
        rw [hBC1]
        exact hb
      rw [branchNP, if_neg hnzC, hfCeq, hparC]
    have hnext0C : nextR C 0 (m + q) fC = true := by
      have hh := nextR_coreReduce_pos_tail M 0 q f hM hpos
        hboundsM.1 hboundsM.2
      rw [hh]
      simpa [fC] using hnext0M
    have hp0fC : leR C 0 p fC = true := by
      have hh := hpnext
      simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
        Bool.and_eq_true] at hh
      simpa [leR] using hh.1.2
    have he0p : entry C 0 p < entry C 0 fC :=
      ancestor_basic_1 C p fC fC hCT hpf (le_refl _) hp0fC
    have hpJoint : p ≤ m + q :=
      nextR0_largest_below C (m + q) p fC hnext0C hpf he0p
    have htrC := TrMax_coreReduce_pos M hM hmono hpos
    have hpTrC : p ≤ TrMax C := by
      have hqTr : q ≤ TrMax M := by simpa [q] using htrM.1
      change p ≤ TrMax (coreReduce M)
      rw [htrC]
      omega
    have he1p : entry C 1 p = p := by
      simpa [C] using entry1_coreReduce_trunk_pos M p hM hA hmono hpos hpTrC
    have hpSucc : p + 1 = b := by
      by_cases hmp : m ≤ p
      · let k := p - m
        have hpk : p = m + k := by simp [k]; omega
        have hkTr : k ≤ TrMax M := by
          have hp' : p ≤ m + TrMax M := by simpa [C, m, htrC] using hpTrC
          omega
        have hbound := TrMax_bound M hM
        have hMpos := List.length_pos_of_ne_nil hM
        have hkL : k < Lng M := by
          exact lt_of_le_of_lt hkTr
            (lt_of_le_of_lt hbound (Nat.sub_lt hMpos (by omega)))
        have hnextM : nextR M 1 k f = true := by
          have hh := nextR_coreReduce_pos_tail M 1 k f hM hpos hkL hboundsM.2
          rw [← hh]
          simpa [hpk, fC] using hpnext
        have hhasM : hasParent M 1 f = true :=
          (hasParent_iff_unique_fseq M 1 f).mpr
            ⟨k, hnextM, fun y hy => nextR1_unique_mr M y k f hy hnextM⟩
        have hparM : parent M 1 f = k :=
          parent_eq_of_unique_fseq M 1 f k hnextM
            (fun y hy => nextR1_unique_mr M y k f hy hnextM)
        have hcond := RedCondA_apply M hA 1 f (by omega) hboundsM.2 hhasM
        rw [hparM] at hcond
        have he1k := (trunk_entries_offset M hM hA k hkTr).2
        dsimp [m] at hpk ⊢
        omega
      · have hpm : p < m := by omega
        have hNoSmall : ∀ k, k < Lng M → leR M 0 k f = true →
            b ≤ entry M 1 k := by
          intro k hkL hle
          by_contra hnot
          have heLt : entry M 1 k < entry M 1 f := by omega
          have hkfLe : k ≤ f := by
            have hh : le0 M k f = true := by simpa [leR] using hle
            exact le0_index_fseq hh
          have hkf : k < f := by
            by_contra hnotkf
            have : k = f := by omega
            subst k
            omega
          obtain ⟨p', hkp', hp'f, hp'next⟩ :=
            parent_exists_2 M k f hM hkf hboundsM.2 heLt hle
          have hp'L : p' < Lng M := hp'f.trans hboundsM.2
          have hp'nextC : nextR C 1 (m + p') fC = true := by
            have hh := nextR_coreReduce_pos_tail M 1 p' f hM hpos
              hp'L hboundsM.2
            rw [hh]
            simpa [fC] using hp'next
          have heq : m + p' = p :=
            nextR1_unique_mr C (m + p') p fC hp'nextC hpnext
          omega
        have hrootM : leR M 0 0 (Lng M - 1) = true := by
          have hh := hmono
          simp only [monoT, Bool.and_eq_true] at hh
          exact hh.2
        have h0fM : leR M 0 0 f = true :=
          ancestor_tree_1 M 0 f (Lng M - 1) hM hrootM
            (Nat.zero_le _) (by omega)
        have hbM : b ≤ m := by
          have hh := hNoSmall 0 (List.length_pos_of_ne_nil hM) h0fM
          simpa [m] using hh
        have hqTr : q ≤ TrMax M := by simpa [q] using htrM.1
        have hqTrC : m + q ≤ TrMax C := by
          rw [htrC]
          dsimp [m]
          omega
        have hbq : b - 1 ≤ m + q := by omega
        have hleBq : leR C 0 (b - 1) (m + q) = true :=
          trunk_le0 C (b - 1) (m + q) hCT hbq hqTrC
        have hleQf : leR C 0 (m + q) fC = true :=
          nextR0_leR C (m + q) fC hnext0C
        have hleBf : leR C 0 (b - 1) fC = true :=
          row0_transitive C (b - 1) (m + q) fC hCT hleBq hleQf
        have hle0Bf : le0 C (b - 1) fC = true := by
          simpa [leR] using hleBf
        have hb1Tr : b - 1 ≤ TrMax C := le_trans hbq hqTrC
        have he1b1 : entry C 1 (b - 1) = b - 1 := by
          simpa [C] using
            entry1_coreReduce_trunk_pos M (b - 1) hM hA hmono hpos hb1Tr
        have hb1f : b - 1 < fC := by omega
        have he1lt : entry C 1 (b - 1) < entry C 1 fC := by omega
        have hAll : (List.range (Lng C)).all (fun j =>
            !(decide (b - 1 < j) && le0 C j fC) ||
              decide (entry C 1 fC ≤ entry C 1 j)) = true := by
          apply List.all_eq_true.mpr
          intro j hjmem
          have hjL : j < Lng C := List.mem_range.mp hjmem
          by_cases hjgt : b - 1 < j
          · by_cases hjle : le0 C j fC = true
            · have hge : b ≤ entry C 1 j := by
                by_cases hjm : j < m
                · have hmTr : m ≤ TrMax C := by
                    simpa [C, m] using coreReduce_m10_le_TrMax M hM hpos
                  have hjTr : j ≤ TrMax C := by omega
                  have hej : entry C 1 j = j := by
                    simpa [C] using entry1_coreReduce_trunk_pos M j hM hA
                      hmono hpos hjTr
                  omega
                · let k := j - m
                  have hjk : j = m + k := by simp [k]; omega
                  have hkL : k < Lng M := by rw [hlenC] at hjL; omega
                  have hleRC : leR C 0 (m + k) (m + f) = true := by
                    simpa [hjk, fC] using (show leR C 0 j fC = true by
                      simpa [leR] using hjle)
                  have hleM : leR M 0 k f = true := by
                    have hh := leR_coreReduce_pos_tail M 0 k f hM hpos
                      hkL hboundsM.2
                    rw [← hh]
                    exact hleRC
                  have hsmall := hNoSmall k hkL hleM
                  have hej := entry1_coreReduce_pos_tail M k hpos hkL
                  rw [← hjk] at hej
                  simpa [C] using (show b ≤ entry C 1 j by
                    rw [hej]
                    exact hsmall)
              simp [hjgt, hjle, he1fC, hge]
            · simp [hjgt, hjle]
          · simp [hjgt]
        have hnextB : nextR C 1 (b - 1) fC = true := by
          simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
            Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨⟨⟨⟨by omega, hfCL⟩, hb1f⟩, he1lt⟩, hle0Bf⟩, hAll⟩
        have heq : b - 1 = p :=
          nextR1_unique_mr C (b - 1) p fC hnextB hpnext
        omega
    rw [hNP, hpSucc]

theorem IncrFirst_cons_eq_bumpAt_succ (b h : ℕ) (T : PS)
    (hstrict : ∀ q, 1 ≤ q → q < Lng ((b + 1, h) :: T) →
      b + 1 < entry ((b + 1, h) :: T) 0 q) :
    IncrFirst ((b, h) :: T) = bumpAt ((b + 1, h) :: T) (b + 2) := by
  apply List.ext_getElem
  · simp [IncrFirst, bumpAt]
  · intro n hnI hnB
    cases n with
    | zero => simp [IncrFirst, bumpAt, bumpV]
    | succ k =>
        have hkT : k < T.length := by simpa [IncrFirst] using hnI
        have hs := hstrict (k + 1) (by omega) (by simpa using hnB)
        have he : b + 1 < T[k].1 := by
          simpa [entry, List.getElem?_eq_getElem (by simpa using hnB)] using hs
        have hnot : ¬T[k].1 < b + 2 := by omega
        simp [IncrFirst, bumpAt, List.getElem_map, bumpV, hnot]

theorem Red_cons_head0_lower (a b h : ℕ) (T : PS)
    (hab : a ≤ b) (hnm : multiT ((b, h) :: T) = false)
    (hstrict : ∀ q, 1 ≤ q → q < Lng ((b, h) :: T) →
      b < entry ((b, h) :: T) 0 q) :
    Red ((a, h) :: T) = Red ((b, h) :: T) := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      rfl
  | succ b ih =>
      by_cases heq : a = b + 1
      · subst a
        rfl
      · have hab' : a ≤ b := by omega
        let Y : PS := (b, h) :: T
        let X : PS := (b + 1, h) :: T
        have hstep : IncrFirst Y = bumpAt X (b + 2) := by
          apply IncrFirst_cons_eq_bumpAt_succ b h T
          intro q hq hqL
          simpa [X] using hstrict q hq (by simpa [X] using hqL)
        have hnmY : multiT Y = false := by
          calc
            multiT Y = multiT (IncrFirst Y) := (multiT_IncrFirst_ri Y).symm
            _ = multiT (bumpAt X (b + 2)) := congrArg multiT hstep
            _ = multiT X := multiT_bumpAt X (b + 2)
            _ = false := by simpa [X] using hnm
        have hstrictY : ∀ q, 1 ≤ q → q < Lng Y →
            b < entry Y 0 q := by
          intro q hq hqL
          have hqLX : q < Lng X := by simpa [X, Y] using hqL
          have hs := hstrict q hq (by simpa [X] using hqLX)
          have hsX : b + 1 < entry X 0 q := by simpa [X] using hs
          have heqTail : entry Y 0 q = entry X 0 q := by
            cases q with
            | zero => omega
            | succ k => simp [Y, X, entry]
          rw [heqTail]
          omega
        have hleft : Red ((a, h) :: T) = Red Y := by
          exact ih a hab' hnmY (by simpa [Y] using hstrictY)
        have hcutX : cutOK X (b + 2) := by
          constructor
          · omega
          · intro j hjTr hjL
            have hj1 : 1 ≤ j := by
              have : 0 ≤ TrMax X := Nat.zero_le _
              omega
            have hs := hstrict j hj1 (by simpa [X] using hjL)
            have hsX : b + 1 < entry X 0 j := by simpa [X] using hs
            omega
        have hYT : TPS Y := by simp [Y, TPS]
        have hXT : TPS X := by simp [X, TPS]
        have hright : Red Y = Red X := by
          calc
            Red Y = Red (IncrFirst Y) := (Red_IncrFirst Y hYT).symm
            _ = Red (bumpAt X (b + 2)) := congrArg Red hstep
            _ = Red X := Red_bumpAt_of_cutOK_nonmulti X (b + 2) hXT
              (by simpa [X] using hnm) hcutX
        exact hleft.trans hright

theorem entry_IncrFirstN_zero (n : ℕ) (M : PS) (j : ℕ)
    (hj : j < Lng M) :
    entry (IncrFirstN n M) 0 j = entry M 0 j + n := by
  rw [IncrFirstN_eq_map]
  simp [entry, List.getElem?_eq_getElem hj, List.getElem_map]

theorem multiT_IncrFirstN (n : ℕ) (M : PS) :
    multiT (IncrFirstN n M) = multiT M := by
  induction n generalizing M with
  | zero => rfl
  | succ n ih =>
      rw [IncrFirstN, ih, multiT_IncrFirst_ri]

theorem mono_tail_row0_strict (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (q : ℕ) (hq1 : 1 ≤ q) (hqL : q < Lng M) :
    entry M 0 0 < entry M 0 q := by
  have hfull : leR M 0 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  exact ancestor_basic_1 M 0 q (Lng M - 1) hM (by omega) (by omega) hfull

theorem Br_component_head0_condA (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hA : RedCondA M = true)
    (hJ : J < (Br M).length) :
    entry ((Br M).getD J []) 0 0 =
      entry M 0 0 + (Joints M).getD J 0 + 1 := by
  let q := (Joints M).getD J 0
  let f := (FirstNodes M).getD J 0
  have htr := FirstNodes_TrMax_Joints M J hM hmono hJ
  have hnext : nextR M 0 q f = true := by
    simpa [q, f] using Joints_nextR_FirstNodes M J hM hmono hJ
  have hfL : f < Lng M := by
    have hh : nextrel0 M q f = true := by simpa [nextR] using hnext
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hh
    omega
  have hhas : hasParent M 0 f = true :=
    (hasParent_iff_unique_fseq M 0 f).mpr
      ⟨q, hnext, fun y hy => row0_parent_unique M y q f hy hnext⟩
  have hpar : parent M 0 f = q :=
    parent_eq_of_nextR0 M q f hnext
  have heq := (trunk_entries_offset M hM hA q (by simpa [q] using htr.1)).1
  have hcond := RedCondA_apply M hA 0 f (by omega) hfL hhas
  rw [hpar, heq] at hcond
  have hef := entry_FirstNodes_eq_component_mr M J 0 hM hJ
  dsimp [q, f] at hcond ⊢
  rw [← hef]
  omega

theorem coreReduce_branch_block_value (M : PS) (J : ℕ) (hM : TPS M)
    (hA : RedCondA M = true) (hmono : monoT M = true)
    (hpos : 0 < entry M 1 0) (hJ : J < (Br M).length)
    (hIH : Red (IncrFirstN (entry M 1 0) ((Br M).getD J [])) =
      rebaseRow0
        (entry (IncrFirstN (entry M 1 0) ((Br M).getD J [])) 0 0)
        (entry (IncrFirstN (entry M 1 0) ((Br M).getD J [])) 1 0)
        (IncrFirstN (entry M 1 0) ((Br M).getD J []))) :
    IncrFirstN (branchE (coreReduce M) J)
        (Red (redNJ (coreReduce M) J)) =
      rebaseRow0 (entry M 0 0) (entry M 1 0) ((Br M).getD J []) := by
  let C := coreReduce M
  let B := (Br M).getD J []
  let m := entry M 1 0
  let c0 := entry M 0 0
  let q := (Joints M).getD J 0
  let b := entry B 1 0
  let X := IncrFirstN m B
  have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
  have hmonoC : monoT C = true := by
    simpa [C] using monoT_coreReduce_pos M hM hmono hpos
  have hBr := Br_coreReduce_pos M hM hmono hpos
  have hJC : J < (Br C).length := by simpa [C, hBr] using hJ
  have hBT : TPS B := by simpa [B] using Br_component_TPS M J hM hJ
  have hXT : TPS X := by
    apply List.ne_nil_of_length_pos
    simpa [X] using List.length_pos_of_ne_nil hBT
  have hblockC : (Br C).getD J [] = X := by
    rw [show Br C = (Br M).map (IncrFirstN m) by simpa [C, m] using hBr]
    rw [getD_eq_getElem_idx _ _ (by simpa using hJ), List.getElem_map]
    dsimp [B, X]
    rw [getD_eq_getElem_idx _ _ hJ]
  have hqC : (Joints C).getD J 0 = m + q := by
    simpa [C, m, q] using Joints_coreReduce_pos_getD M J hM hmono hpos hJ
  have hnpC : branchNP C J = b := by
    simpa [C, B, b] using branchNP_coreReduce_pos M J hM hA hmono hpos hJ
  have hcoreC := coreReduce_core M hM
  have hc0 : entry C 0 0 = 0 := by simpa [C] using hcoreC.1
  have hc1 : entry C 1 0 = 0 := by simpa [C] using hcoreC.2
  have hB0 : entry B 0 0 = c0 + q + 1 := by
    simpa [B, c0, q] using Br_component_head0_condA M J hM hmono hA hJ
  have hBpos := List.length_pos_of_ne_nil hBT
  have hX0 : entry X 0 0 = c0 + q + 1 + m := by
    rw [entry_IncrFirstN_zero m B 0 hBpos, hB0]
  have hX1 : entry X 1 0 = b := by
    simpa [X, b] using entry_IncrFirstN_one m B 0
  have hnpInline :
      (if entry ((Br C).getD J []) 1 0 = 0 then 0
        else parent C 1 ((FirstNodes C).getD J 0) + 1) = b := by
    simpa [branchNP] using hnpC
  have hNJ : redNJ C J = (m + q + 1, b) :: X.tail := by
    change (entry C 0 0 + (Joints C).getD J 0 + 1,
        entry C 1 0 +
          (if entry ((Br C).getD J []) 1 0 = 0 then 0
            else parent C 1 ((FirstNodes C).getD J 0) + 1)) ::
      ((Br C).getD J []).tail = (m + q + 1, b) :: X.tail
    rw [hc0, hc1, hqC, hnpInline, hblockC]
    simp
  have hXcons : X = (c0 + q + 1 + m, b) :: X.tail := by
    have hdecomp : (entry X 0 0, entry X 1 0) :: X.tail = X := by
      cases hX : X with
      | nil => exact (hXT hX).elim
      | cons p ps =>
          rcases p with ⟨u, v⟩
          simp [hX, entry]
    rw [hX0, hX1] at hdecomp
    exact hdecomp.symm
  have hnmB : multiT B = false := by
    rcases Br_component_nonmulti M J hM hJ with hz | hm
    · have hzB : zeroT B = true := by simpa [B] using hz
      simp [multiT, hzB]
    · have hmB : monoT B = true := by simpa [B] using hm
      simp [multiT, hmB]
  have hnmX : multiT X = false := by
    simpa [X, multiT_IncrFirstN] using hnmB
  have hstrictX : ∀ k, 1 ≤ k → k < Lng X →
      c0 + q + 1 + m < entry X 0 k := by
    intro k hk1 hkL
    have hkB : k < Lng B := by simpa [X] using hkL
    rcases Br_component_nonmulti M J hM hJ with hz | hm
    · have hLB : Lng B = 1 := by
        have hh := hz
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
        simpa [B] using hh.1
      omega
    · have hmonoB : monoT B = true := by simpa [B] using hm
      have hs := mono_tail_row0_strict B hBT hmonoB k hk1 hkB
      have he0 := entry_IncrFirstN_zero m B 0 hBpos
      have hek := entry_IncrFirstN_zero m B k hkB
      rw [hB0] at he0
      simpa [X] using (show c0 + q + 1 + m < entry (IncrFirstN m B) 0 k by
        omega)
  have hredEq : Red (redNJ C J) = Red X := by
    calc
      Red (redNJ C J) = Red ((m + q + 1, b) :: X.tail) := congrArg Red hNJ
      _ = Red ((c0 + q + 1 + m, b) :: X.tail) := by
        have hnmCons : multiT ((c0 + q + 1 + m, b) :: X.tail) = false := by
          rw [← hXcons]
          exact hnmX
        apply Red_cons_head0_lower
        · omega
        · exact hnmCons
        · intro k hk1 hkL
          have hkX : k < Lng X := by
            rw [hXcons]
            exact hkL
          have hs := hstrictX k hk1 hkX
          have heq : entry ((c0 + q + 1 + m, b) :: X.tail) 0 k =
              entry X 0 k := by
            cases hX : X with
            | nil => exact (hXT hX).elim
            | cons x xs =>
                cases k with
                | zero => omega
                | succ k => simp [hX, entry]
          rw [heq]
          exact hs
      _ = Red X := congrArg Red hXcons.symm
  have hnple : b ≤ m + q + 1 := by
    have hh := redNJ_np_le_joint C J hCT hmonoC hc1 hJC
    change branchNP C J ≤ (Joints C).getD J 0 + 1 at hh
    rw [hnpC, hqC] at hh
    omega
  have hfloorB : ∀ k < Lng B, c0 + q + 1 ≤ entry B 0 k := by
    intro k hkB
    rcases Br_component_nonmulti M J hM hJ with hz | hm
    · have hLB : Lng B = 1 := by
        have hh := hz
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
        simpa [B] using hh.1
      have : k = 0 := by omega
      subst k
      rw [hB0]
    · have hmonoB : monoT B = true := by simpa [B] using hm
      rw [← hB0]
      exact mono_row0_min_mr B hBT hmonoB k hkB
  have hE : branchE C J = m + q + 1 - b := by
    rw [branchE, hqC, hnpC]
  have hIHX : Red X = rebaseRow0 (entry X 0 0) (entry X 1 0) X := by
    simpa [X, B, m] using hIH
  change IncrFirstN (branchE C J) (Red (redNJ C J)) =
    rebaseRow0 c0 m B
  rw [hE, hredEq, hIHX, hX0, hX1]
  dsimp [X]
  simp only [IncrFirstN_eq_map, rebaseRow0, List.map_map]
  apply List.ext_getElem
  · simp
  · intro k hkL hkR
    have hkB : k < Lng B := by simpa using hkR
    have hfst : B[k].1 = entry B 0 k := by
      symm
      exact entry0_eq_fst_getElem_mr B k hkB
    simp only [List.getElem_map, Function.comp_apply]
    apply Prod.ext
    · simp only [Prod.fst]
      rw [hfst]
      have hf := hfloorB k hkB
      omega
    · simp

theorem Red_coreReduce_value (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hmono : monoT M = true)
    (hpos : 0 < entry M 1 0)
    (IH : ∀ X, Lng X < Lng M → TPS X → RedCondA X = true →
      multiT X = false →
      Red X = rebaseRow0 (entry X 0 0) (entry X 1 0) X) :
    Red (coreReduce M) =
      diagSeq 0 (entry M 1 0 + TrMax M) ++
        (List.range (Br M).length).flatMap (fun J =>
          rebaseRow0 (entry M 0 0) (entry M 1 0) ((Br M).getD J [])) := by
  let C := coreReduce M
  let m := entry M 1 0
  have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
  have hmonoC : monoT C = true := by
    simpa [C] using monoT_coreReduce_pos M hM hmono hpos
  have hcoreC : entry C 0 0 = 0 ∧ entry C 1 0 = 0 := by
    simpa [C] using coreReduce_core M hM
  have htrC := TrMax_coreReduce_pos M hM hmono hpos
  have hBrC := Br_coreReduce_pos M hM hmono hpos
  have hm : entry M 1 0 ≠ 0 := by omega
  have hMpos := List.length_pos_of_ne_nil hM
  have hlenC : Lng C = m + Lng M := by
    simp [C, coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
    omega
  by_cases ht : TrMax M = Lng M - 1
  · have htC : TrMax C = Lng C - 1 := by
      change TrMax (coreReduce M) = Lng C - 1
      rw [htrC, hlenC, ht]
      dsimp [m]
      have hadd := Nat.add_sub_assoc (m := Lng M) (k := 1) hMpos
        (entry M 1 0)
      omega
    have hBrnil : Br M = [] := by simp [Br, ht]
    calc
      Red C = diagSeq 0 (Lng C - 1) :=
        Red_core_trunk_ri C hCT hmonoC hcoreC htC
      _ = diagSeq 0 (entry M 1 0 + TrMax M) := by rw [← htC, htrC]
      _ = diagSeq 0 (entry M 1 0 + TrMax M) ++
          (List.range (Br M).length).flatMap (fun J =>
            rebaseRow0 (entry M 0 0) (entry M 1 0) ((Br M).getD J [])) := by
        simp [hBrnil]
  · have hbound := TrMax_bound M hM
    have htrlt : TrMax M < Lng M - 1 := by omega
    have htC : TrMax C ≠ Lng C - 1 := by
      intro heq
      have heq' : entry M 1 0 + TrMax M = m + Lng M - 1 := by
        rw [← htrC, ← hlenC]
        exact heq
      dsimp [m] at heq'
      omega
    have hred := Red_core_nontrunk_mr C hCT hmonoC hcoreC htC
    rw [hred, show TrMax C = entry M 1 0 + TrMax M by simpa [C] using htrC]
    congr 1
    have hRange : List.range (Br C).length = List.range (Br M).length := by
      simp [C, hBrC]
    rw [hRange]
    apply List.flatMap_congr
    intro J hJmem
    have hJ : J < (Br M).length := List.mem_range.mp hJmem
    let B := (Br M).getD J []
    let X := IncrFirstN m B
    have hBT : TPS B := by simpa [B] using Br_component_TPS M J hM hJ
    have hXT : TPS X := by
      apply List.ne_nil_of_length_pos
      simpa [X] using List.length_pos_of_ne_nil hBT
    have hlenBound := Br_component_length_bound M J hM hJ
    have hlen : Lng X < Lng M := by
      have : Lng B < Lng M := by
        have hBpos := List.length_pos_of_ne_nil hBT
        dsimp [B] at hlenBound ⊢
        omega
      simpa [X] using this
    have hBA : RedCondA B = true := by
      simpa [B] using RedCondA_Br_component M J hM hmono hA hJ
    have hXA : RedCondA X = true := by
      have hh := RedCondA_rebaseRow0 0 m B (by intro k hk; omega) hBA
      rw [← IncrFirstN_eq_rebaseRow0_zero] at hh
      simpa [X] using hh
    have hnmB : multiT B = false := by
      rcases Br_component_nonmulti M J hM hJ with hz | hmonoB
      · have hzB : zeroT B = true := by simpa [B] using hz
        simp [multiT, hzB]
      · have hmB : monoT B = true := by simpa [B] using hmonoB
        simp [multiT, hmB]
    have hnmX : multiT X = false := by
      simpa [X, multiT_IncrFirstN] using hnmB
    have hIH := IH X hlen hXT hXA hnmX
    simpa [C, X, B, m] using
      coreReduce_branch_block_value M J hM hA hmono hpos hJ (by
        simpa [X, B, m] using hIH)

/-! ## Reassembling the positive reduction window -/

theorem rebaseRow0_trunk_take (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) :
    rebaseRow0 (entry M 0 0) (entry M 1 0)
        (M.take (TrMax M + 1)) =
      diagSeq (entry M 1 0) (entry M 1 0 + TrMax M) := by
  have hbound := TrMax_bound M hM
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  apply List.ext_getElem
  · have hle : TrMax M + 1 ≤ Lng M := by omega
    simp [rebaseRow0, diagSeq, Nat.min_eq_left hle]
    omega
  · intro k hkL hkR
    have hk : k ≤ TrMax M := (by simpa [rebaseRow0] using hkL :
      k ≤ TrMax M ∧ k < Lng M).1
    have hkM : k < Lng M := by omega
    have he := trunk_entries_offset M hM hA k hk
    have hMk : M[k] = (entry M 0 k, entry M 1 k) := by
      apply Prod.ext
      · exact (entry0_eq_fst_getElem_mr M k hkM).symm
      · simpa [entry, List.getElem?_eq_getElem hkM]
    simp only [rebaseRow0, List.getElem_map, List.getElem_take,
      diagSeq, List.getElem_map, List.getElem_range']
    rw [hMk, he.1, he.2]
    simp
    omega

theorem Br_flatten_eq_drop (M : PS) (hM : TPS M) :
    (Br M).flatten = M.drop (TrMax M + 1) := by
  by_cases ht : TrMax M = Lng M - 1
  · have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
    have hlen : TrMax M + 1 = Lng M := by omega
    have hBr : Br M = [] := by simp [Br, ht]
    rw [hBr, hlen]
    simp
  · let N := seg M (TrMax M + 1) (Lng M - 1)
    have hBr : Br M = P N := by simp [Br, ht, N]
    have hdropBound : TrMax M + 1 < Lng M := by
      have hbound := TrMax_bound M hM
      omega
    calc
      (Br M).flatten = (P N).flatten := by rw [hBr]
      _ = N := P_concat N
      _ = M.drop (TrMax M + 1) := by
        simpa [N] using (drop_eq_seg M (TrMax M + 1) hdropBound).symm

theorem flatMap_rebaseRow0_Br (c d : ℕ) (M : PS) :
    (List.range (Br M).length).flatMap (fun J =>
        rebaseRow0 c d ((Br M).getD J [])) =
      rebaseRow0 c d (Br M).flatten := by
  have hblocks : (List.range (Br M).length).map (fun J =>
      (Br M).getD J []) = Br M := by
    apply List.ext_getElem
    · simp
    · intro k hkL hkR
      have hk : k < (Br M).length := by simpa using hkL
      simp only [List.getElem_map, List.getElem_range]
      rw [getD_eq_getElem_idx (Br M) [] hk]
  have hrebased : (List.range (Br M).length).map (fun J =>
      rebaseRow0 c d ((Br M).getD J [])) =
      (Br M).map (rebaseRow0 c d) := by
    simpa only [List.map_map, Function.comp_apply] using
      congrArg (List.map (rebaseRow0 c d)) hblocks
  change ((List.range (Br M).length).map (fun J =>
      rebaseRow0 c d ((Br M).getD J []))).flatten = _
  rw [hrebased]
  clear hblocks hrebased
  have hmapFlatten : ∀ Q : List PS,
      (Q.map (rebaseRow0 c d)).flatten = rebaseRow0 c d Q.flatten := by
    intro Q
    induction Q with
    | nil => rfl
    | cons B Q ih => simp [rebaseRow0, ih]
  exact hmapFlatten (Br M)

theorem rebaseRow0_decompose (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) :
    rebaseRow0 (entry M 0 0) (entry M 1 0) M =
      diagSeq (entry M 1 0) (entry M 1 0 + TrMax M) ++
        (List.range (Br M).length).flatMap (fun J =>
          rebaseRow0 (entry M 0 0) (entry M 1 0)
            ((Br M).getD J [])) := by
  calc
    rebaseRow0 (entry M 0 0) (entry M 1 0) M =
        rebaseRow0 (entry M 0 0) (entry M 1 0)
          (M.take (TrMax M + 1) ++ M.drop (TrMax M + 1)) := by
      rw [List.take_append_drop]
    _ = rebaseRow0 (entry M 0 0) (entry M 1 0)
          (M.take (TrMax M + 1)) ++
        rebaseRow0 (entry M 0 0) (entry M 1 0)
          (M.drop (TrMax M + 1)) := by simp [rebaseRow0]
    _ = _ := by
      rw [rebaseRow0_trunk_take M hM hA, ← Br_flatten_eq_drop M hM,
        ← flatMap_rebaseRow0_Br]

theorem drop_diagSeq_zero (m t : ℕ) :
    (diagSeq 0 (m + t)).drop m = diagSeq m (m + t) := by
  simp only [diagSeq, ← List.map_drop, List.drop_range']
  congr 2 <;> omega

theorem coreReduce_positive_window (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hmono : monoT M = true)
    (hpos : 0 < entry M 1 0)
    (IH : ∀ X, Lng X < Lng M → TPS X → RedCondA X = true →
      multiT X = false →
      Red X = rebaseRow0 (entry X 0 0) (entry X 1 0) X) :
    seg (Red (coreReduce M)) (entry M 1 0)
        (Lng (Red (coreReduce M)) - 1) =
      rebaseRow0 (entry M 0 0) (entry M 1 0) M := by
  let m := entry M 1 0
  let C := coreReduce M
  let N := Red C
  have hm : entry M 1 0 ≠ 0 := by omega
  have hCL : Lng C = m + Lng M := by
    simp [C, m, coreReduce, hm, diagSeq, IncrFirstN_eq_map]
    omega
  have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
  have hNL : Lng N = m + Lng M := by
    calc
      Lng N = Lng C := Lng_Red_invariance C hCT
      _ = m + Lng M := hCL
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hmN : m < Lng N := by rw [hNL]; omega
  have hval := Red_coreReduce_value M hM hA hmono hpos IH
  calc
    seg (Red (coreReduce M)) (entry M 1 0)
        (Lng (Red (coreReduce M)) - 1) = N.drop m := by
      simpa [N, C, m] using (drop_eq_seg N m hmN).symm
    _ = (diagSeq 0 (m + TrMax M)).drop m ++
        (List.range (Br M).length).flatMap (fun J =>
          rebaseRow0 (entry M 0 0) (entry M 1 0)
            ((Br M).getD J [])) := by
      rw [show N = Red (coreReduce M) by rfl, hval]
      apply List.drop_append_of_le_length
      simp [diagSeq]
      omega
    _ = diagSeq m (m + TrMax M) ++
        (List.range (Br M).length).flatMap (fun J =>
          rebaseRow0 (entry M 0 0) (entry M 1 0)
            ((Br M).getD J [])) := by rw [drop_diagSeq_zero]
    _ = rebaseRow0 (entry M 0 0) (entry M 1 0) M := by
      simpa [m] using (rebaseRow0_decompose M hM hA).symm

theorem redPositiveOut_eq_seg (M N : PS)
    (hmj : entry M 1 0 ≤ Lng N - 1)
    (hjN : Lng N - 1 < Lng N)
    (hmono : monoT (seg N (entry M 1 0) (Lng N - 1)) = true)
    (hanchor : entry N 0 (entry M 1 0) =
      entry N 1 (entry M 1 0))
    (hfloor : ∀ j, entry M 1 0 ≤ j → j ≤ Lng N - 1 →
      entry N 0 (entry M 1 0) ≤ entry N 0 j) :
    redPositiveOut_ri M N =
      seg N (entry M 1 0) (Lng N - 1) := by
  let m := entry M 1 0
  let jN := Lng N - 1
  unfold redPositiveOut_ri
  dsimp only
  rw [if_pos (by simp [hmj, hmono])]
  apply List.ext_getElem
  · simp [seg]
  · intro k hkL hkR
    have hk : k < jN + 1 - m := by simpa [m, jN] using hkL
    have hmjk : m + k ≤ jN := by omega
    have hjL : m + k < Lng N := by omega
    have hf := hfloor (m + k) (by omega) (by simpa [m, jN] using hmjk)
    simp only [List.getElem_map, List.getElem_range', seg]
    apply Prod.ext
    · simp only [Prod.fst, one_mul]
      change entry N 0 (m + k) - entry N 0 m + entry N 1 m =
        entry N 0 (m + k)
      rw [← show entry N 0 m = entry N 1 m by simpa [m] using hanchor]
      exact Nat.sub_add_cancel (by simpa [m] using hf)
    · simp

theorem rebaseRow0_zeroT (M : PS) (hM : TPS M)
    (hz : zeroT M = true) :
    rebaseRow0 (entry M 0 0) (entry M 1 0) M = [(0, 0)] := by
  have hL : Lng M = 1 := by
    have hh := hz
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
    exact hh.1
  have he1 : entry M 1 0 = 0 := by
    have hh := hz
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
    exact hh.2
  apply List.ext_getElem
  · simp [rebaseRow0, hL]
  · intro k hkL hkR
    have hk0 : k = 0 := by simpa [rebaseRow0, hL] using hkL
    subst k
    have h0 : 0 < Lng M := List.length_pos_of_ne_nil hM
    have hMk : M[0] = (entry M 0 0, entry M 1 0) := by
      apply Prod.ext
      · exact (entry0_eq_fst_getElem_mr M 0 h0).symm
      · simpa [entry, List.getElem?_eq_getElem h0]
    simp [rebaseRow0, hMk, he1]

theorem Red_rebase_nonmulti_step (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hnm : multiT M = false)
    (IH : ∀ X, Lng X < Lng M → TPS X → RedCondA X = true →
      multiT X = false →
      Red X = rebaseRow0 (entry X 0 0) (entry X 1 0) X) :
    Red M = rebaseRow0 (entry M 0 0) (entry M 1 0) M := by
  by_cases hz : zeroT M = true
  · rw [Red_zero_mr M hz, rebaseRow0_zeroT M hM hz]
  · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
    have hmono : monoT M = true := by
      have hh := hnm
      simp [multiT, hz'] at hh
      exact hh
    by_cases hm : entry M 1 0 = 0
    · by_cases hc0 : entry M 0 0 = 0
      · have hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0 := ⟨hc0, hm⟩
        have hfix := Red_core_fixed_of_condA_nonmulti M hM hA hnm hcore IH
        rw [hfix]
        simp [rebaseRow0, hc0, hm]
      · let C := coreReduce M
        have hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by
          simp [hc0]
        have hred : Red M = Red C := by
          simpa [C, hm] using Red_noncore_ri M hM hmono hnoncore
        have hCeq : C = rebaseRow0 (entry M 0 0) 0 M := by
          simpa [C] using coreReduce_zero_eq_rebaseRow0 M hm
        have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
        have hCcore : entry C 0 0 = 0 ∧ entry C 1 0 = 0 := by
          simpa [C] using coreReduce_core M hM
        have hCnm : multiT C = false := by
          simpa [C] using coreReduce_multi_false M hM hmono
        have hfloor : ∀ j < Lng M, entry M 0 0 ≤ entry M 0 j := by
          intro j hj
          exact mono_row0_min_mr M hM hmono j hj
        have hCA : RedCondA C = true := by
          have hh := RedCondA_rebaseRow0 (entry M 0 0) 0 M hfloor hA
          simpa [hCeq] using hh
        have hCL : Lng C = Lng M := by simp [C, coreReduce, hm]
        have IHC : ∀ X, Lng X < Lng C → TPS X →
            RedCondA X = true → multiT X = false →
            Red X = rebaseRow0 (entry X 0 0) (entry X 1 0) X := by
          intro X hlen hXT hXA hXnm
          apply IH X (by rw [hCL] at hlen; exact hlen) hXT hXA hXnm
        have hfix := Red_core_fixed_of_condA_nonmulti C hCT hCA hCnm hCcore IHC
        calc
          Red M = Red C := hred
          _ = C := hfix
          _ = rebaseRow0 (entry M 0 0) (entry M 1 0) M := by
            simpa [hm] using hCeq
    · have hpos : 0 < entry M 1 0 := by omega
      have hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by
        intro h
        exact hm h.2
      let C := coreReduce M
      let N := Red C
      let m := entry M 1 0
      have hCT : TPS C := by simpa [C] using coreReduce_TPS M hM
      have hmne : entry M 1 0 ≠ 0 := by omega
      have hCL : Lng C = m + Lng M := by
        simp [C, m, coreReduce, hmne, diagSeq, IncrFirstN_eq_map]
        omega
      have hNL : Lng N = m + Lng M := by
        calc
          Lng N = Lng C := Lng_Red_invariance C hCT
          _ = m + Lng M := hCL
      have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      have hmj : m ≤ Lng N - 1 := by rw [hNL]; omega
      have hjN : Lng N - 1 < Lng N := by rw [hNL]; omega
      have hmonoS : monoT (seg N m (Lng N - 1)) = true := by
        simpa [N, C, m] using (monoT_Red_m10pos M hM hmono hpos).2
      have hanchor0 : entry N 0 m = m := by
        simpa [N, C, m] using
          (redB_row0_strict_suffix_min M hM hmono hpos).1
      have hanchor1 : entry N 1 m = m := by
        simpa [N, C, m] using
          redB_prefix_diag M hM hmono hpos 1 (entry M 1 0) (le_refl _)
      have hfloorN : ∀ j, m ≤ j → j ≤ Lng N - 1 →
          entry N 0 m ≤ entry N 0 j := by
        intro j hmj' hj
        by_cases heq : j = m
        · subst j
          exact le_rfl
        · have hlt : m < j := by omega
          have hjL : j < Lng N := by omega
          have hs := (redB_row0_strict_suffix_min M hM hmono hpos).2
            j (by simpa [m] using hlt) (by simpa [N, C, m] using hjL)
          rw [hanchor0]
          simpa [N, C, m] using hs.le
      have hout : redPositiveOut_ri M N = seg N m (Lng N - 1) := by
        apply redPositiveOut_eq_seg M N
        · simpa [m] using hmj
        · exact hjN
        · simpa [m] using hmonoS
        · simpa [m] using hanchor0.trans hanchor1.symm
        · simpa [m] using hfloorN
      have hwindow := coreReduce_positive_window M hM hA hmono hpos IH
      calc
        Red M = redPositiveOut_ri M N := by
          simpa [N, C, hm] using Red_noncore_ri M hM hmono hnoncore
        _ = seg N m (Lng N - 1) := hout
        _ = rebaseRow0 (entry M 0 0) (entry M 1 0) M := by
          simpa [N, C, m] using hwindow

/-- Isabelle's `m_6_5_Red_rebase`: on the coefficient-condition domain,
`Red` of every non-multi sequence is exactly its row-zero rebase. -/
theorem Red_rebase_nonmulti (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hnm : multiT M = false) :
    Red M = rebaseRow0 (entry M 0 0) (entry M 1 0) M := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      apply Red_rebase_nonmulti_step M hM hA hnm
      intro X hlen hXT hXA hXnm
      exact ih (Lng X) (by omega) X hXT hXA hXnm rfl

theorem Red_le_of_condA_nonmulti (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hnm : multiT M = false)
    (i j₀ j₁ : ℕ) :
    leR M i j₀ j₁ = leR (Red M) i j₀ j₁ := by
  have hfloor : ∀ j < Lng M, entry M 0 0 ≤ entry M 0 j := by
    by_cases hz : zeroT M = true
    · have hL : Lng M = 1 := by
        have hh := hz
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
        exact hh.1
      intro j hj
      have : j = 0 := by omega
      subst j
      exact le_rfl
    · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
      have hmono : monoT M = true := by
        have hh := hnm
        simp [multiT, hz'] at hh
        exact hh
      intro j hj
      exact mono_row0_min_mr M hM hmono j hj
  rw [Red_rebase_nonmulti M hM hA hnm]
  exact congrFun (congrFun (congrFun (leR_rebaseRow0
    (entry M 0 0) (entry M 1 0) M hfloor).symm i) j₀) j₁

theorem anchoredSlice_TPS (M : PS) (hM : anchoredSlice M) : TPS M := by
  rcases hM with ⟨S, a, b, hsource, hab, hbL, hanc, rfl⟩
  apply List.ne_nil_of_length_pos
  simp
  omega

theorem anchoredSlice_nonmulti (M : PS) (hM : anchoredSlice M) :
    multiT M = false := by
  rcases anchoredSlice_zero_or_mono M hM with hz | hmono
  · simp [multiT, hz]
  · simp [multiT, hmono]

/-- The A4 headline once the source-side coefficient condition has been
discharged.  The unconditional anchored theorem is completed after the
standard/reduced `RedCondA` prerequisites. -/
theorem Red_le_anchored_of_condA (M : PS) (hM : anchoredSlice M)
    (hA : RedCondA M = true) (i j₀ j₁ : ℕ) :
    leR M i j₀ j₁ = leR (Red M) i j₀ j₁ := by
  exact Red_le_of_condA_nonmulti M (anchoredSlice_TPS M hM) hA
    (anchoredSlice_nonmulti M hM) i j₀ j₁

#print axioms leR_rebaseRow0
#print axioms trunk_entries_offset

end PSS

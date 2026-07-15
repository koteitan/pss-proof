import PSS.Red
import «6».«6.4-mono-slice»

/-!
# §6.5 命題（`Red` の well-defined 性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_welldef`
- 訂正: なし
- Isabelle: `m_6_5_Red_welldef`
- 依存: `PSS.Red`
- 状態: ✅ 証明済（sorry 0）

Isabelle の部分関数では主張は `Red_dom M` である。Lean 版では全再帰先で `nu` が真に減ることを
示し、`nu M` より大きい任意の燃料で `RedAux` の値が一致することとして存在一意性を表す。
-/

namespace PSS

theorem P_member_multi_false (M Q : PS) (hM : TPS M) (hQ : Q ∈ P M) :
    multiT Q = false := by
  rcases P_components_nonmulti M hM Q hQ with hz | hm
  · simp [multiT, hz]
  · simp [multiT, hm]

theorem nu_Pblock_lt (M Q : PS) (hM : TPS M)
    (hmulti : multiT M = true) (hQ : Q ∈ P M) : nu Q < nu M := by
  have hQmulti := P_member_multi_false M Q hM hQ
  have hmem : muMono Q ∈ (P M).map muMono := List.mem_map.mpr ⟨Q, hQ, rfl⟩
  have hsub : List.Sublist [muMono Q] ((P M).map muMono) :=
    List.singleton_sublist.mpr hmem
  have hle : muMono Q ≤ ((P M).map muMono).sum := by
    simpa using hsub.sum_le_sum (by simp)
  simp [nu, hQmulti, hmulti]
  omega

theorem coreReduce_core (M : PS) (hM : TPS M) :
    entry (coreReduce M) 0 0 = 0 ∧ entry (coreReduce M) 1 0 = 0 := by
  cases M with
  | nil => exact (hM rfl).elim
  | cons p ps =>
      rcases p with ⟨a, b⟩
      by_cases hb : b = 0
      · simp [coreReduce, entry, hb]
      · have hbpos : 0 < b := by omega
        simp [coreReduce, entry, hb, diagSeq, hbpos]

theorem nu_coreReduce_lt_of_nonmulti (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0))
    (hcr : multiT (coreReduce M) = false) :
    nu (coreReduce M) < nu M := by
  have hm : multiT M = false := by simp [multiT, hmono]
  have hc := coreReduce_core M hM
  simp [nu, muMono, hm, hcr, hnoncore, hc]

theorem IncrFirstN_eq_map (n : ℕ) (M : PS) :
    IncrFirstN n M = M.map (fun p => (p.1 + n, p.2)) := by
  induction n generalizing M with
  | zero => simp [IncrFirstN]
  | succ n ih =>
      rw [IncrFirstN, ih]
      simp [IncrFirst, List.map_map]
      intro a b hp
      omega

private theorem IncrFirstN_head (n : ℕ) (M : PS) (hM : TPS M) :
    entry (IncrFirstN n M) 0 0 = entry M 0 0 + n ∧
      entry (IncrFirstN n M) 1 0 = entry M 1 0 := by
  cases M with
  | nil => exact (hM rfl).elim
  | cons p ps =>
      rcases p with ⟨a, b⟩
      simp [IncrFirstN_eq_map, entry]

private theorem nextR1_consecutive_wd (M : PS) (j : ℕ)
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
  have hleR := nextR0_leR M j (j + 1) hn0
  have hle0 : le0 M j (j + 1) = true := by simpa [leR] using hleR
  simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨by omega, hL⟩, by omega⟩, he1⟩, hle0⟩, ?_⟩
  intro k hk
  by_cases hjk : j < k
  · by_cases hle : le0 M k (j + 1) = true
    · have hkle := le0_index_fseq hle
      have hkeq : k = j + 1 := by omega
      subst k
      simp
    · simp [hjk, hle]
  · simp [hjk]

theorem le_TrMax_intro_wd (M : PS) (n : ℕ) (hM : TPS M)
    (hall : ∀ j < n, nextR M 1 j (j + 1) = true) :
    n ≤ TrMax M := by
  let q := fun j => !nextR M 1 j (j + 1)
  unfold TrMax
  change n ≤ ((List.range (Lng M)).find? q).getD (Lng M - 1)
  cases hf : (List.range (Lng M)).find? q with
  | none =>
      simp only [Option.getD_none]
      by_contra hn
      have hstep := hall (Lng M - 1) (by omega)
      have hnext : nextrel1 M (Lng M - 1) (Lng M - 1 + 1) = true := by
        simpa [nextR] using hstep
      have hh := hnext
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
      have hMpos := List.length_pos_of_ne_nil hM
      omega
  | some c =>
      simp only [Option.getD_some]
      by_contra hn
      have hc : c < n := by omega
      have hstep := hall c hc
      have hq := List.find?_some hf
      change (!nextR M 1 c (c + 1)) = true at hq
      simp [hstep] at hq

private theorem entry_append_left_wd (A B : PS) (i j : ℕ)
    (hj : j < Lng A) : entry (A ++ B) i j = entry A i j := by
  simp [entry, List.getElem?_append_left hj]

private theorem entry_append_right_wd (A B : PS) (i j : ℕ)
    (hj : Lng A ≤ j) : entry (A ++ B) i j = entry B i (j - Lng A) := by
  simp [entry, List.getElem?_append_right hj]

private theorem entry_diagSeq_wd (m i j : ℕ) (hm : 0 < m) (hj : j < m) :
    entry (diagSeq 0 (m - 1)) i j = j := by
  have hlen : j < Lng (diagSeq 0 (m - 1)) := by
    simp [diagSeq]
    omega
  have hget : (diagSeq 0 (m - 1))[j] = (j, j) := by
    simp [diagSeq]
  simp [entry, List.getElem?_eq_getElem hlen, hget]

theorem coreReduce_prefix_step (M : PS) (j : ℕ) (hM : TPS M)
    (hm : entry M 1 0 ≠ 0) (hj : j < entry M 1 0) :
    nextR (coreReduce M) 1 j (j + 1) = true := by
  let m := entry M 1 0
  let D := diagSeq 0 (m - 1)
  let R := IncrFirstN m M
  have hmpos : 0 < m := by simp [m]; omega
  have hDlen : Lng D = m := by
    simp [D, diagSeq]
    omega
  have hRlen : Lng R = Lng M := by simp [R, IncrFirstN_eq_map]
  have hRhead := IncrFirstN_head m M hM
  have hcore : coreReduce M = D ++ R := by simp [coreReduce, hm, D, R, m]
  have hMpos := List.length_pos_of_ne_nil hM
  change 0 < Lng M at hMpos
  have hL : j + 1 < Lng (coreReduce M) := by
    rw [hcore]
    simp only [List.length_append]
    change j + 1 < Lng D + Lng R
    omega
  have hej0 : entry (coreReduce M) 0 j = j := by
    rw [hcore, entry_append_left_wd D R 0 j (by simpa [hDlen, m] using hj)]
    exact entry_diagSeq_wd m 0 j hmpos (by simpa [m] using hj)
  have hej1 : entry (coreReduce M) 1 j = j := by
    rw [hcore, entry_append_left_wd D R 1 j (by simpa [hDlen, m] using hj)]
    exact entry_diagSeq_wd m 1 j hmpos (by simpa [m] using hj)
  by_cases hnext : j + 1 < m
  · have he10 : entry (coreReduce M) 0 (j + 1) = j + 1 := by
      rw [hcore, entry_append_left_wd D R 0 (j + 1) (by simpa [hDlen] using hnext)]
      exact entry_diagSeq_wd m 0 (j + 1) hmpos hnext
    have he11 : entry (coreReduce M) 1 (j + 1) = j + 1 := by
      rw [hcore, entry_append_left_wd D R 1 (j + 1) (by simpa [hDlen] using hnext)]
      exact entry_diagSeq_wd m 1 (j + 1) hmpos hnext
    exact nextR1_consecutive_wd (coreReduce M) j hL (by omega) (by omega)
  · have hjeq : j + 1 = m := by omega
    have he10 : entry (coreReduce M) 0 (j + 1) = entry M 0 0 + m := by
      rw [hjeq, hcore, entry_append_right_wd D R 0 m (by omega), hDlen]
      simpa using hRhead.1
    have he11 : entry (coreReduce M) 1 (j + 1) = m := by
      rw [hjeq, hcore, entry_append_right_wd D R 1 m (by omega), hDlen]
      simpa [m] using hRhead.2
    exact nextR1_consecutive_wd (coreReduce M) j hL (by omega) (by omega)

theorem betaM_coreReduce_le (M : PS) (hM : TPS M) :
    betaM (coreReduce M) ≤ Lng M := by
  by_cases hm : entry M 1 0 = 0
  · have hlen : Lng (coreReduce M) = Lng M := by simp [coreReduce, hm]
    simp [betaM, hlen]
  · have htr : entry M 1 0 ≤ TrMax (coreReduce M) := by
      apply le_TrMax_intro_wd (coreReduce M) (entry M 1 0)
      · apply List.ne_nil_of_length_pos
        simp [coreReduce, hm, diagSeq, IncrFirstN_eq_map]
      · intro j hj
        exact coreReduce_prefix_step M j hM hm hj
    have hlen : Lng (coreReduce M) = entry M 1 0 + Lng M := by
      simp [coreReduce, hm, diagSeq, IncrFirstN_eq_map]
      omega
    simp [betaM, hlen]
    omega

private theorem entry0_eq_fst_getElem (M : PS) (j : ℕ) (hj : j < Lng M) :
    entry M 0 j = M[j].1 := by
  simp [entry, List.getElem?_eq_getElem hj]

theorem entry_coreReduce_zero (M : PS) (j : ℕ)
    (hm : entry M 1 0 = 0) (hj : j < Lng M) :
    entry (coreReduce M) 0 j = entry M 0 j - entry M 0 0 := by
  have hlen : Lng (coreReduce M) = Lng M := by simp [coreReduce, hm]
  rw [entry0_eq_fst_getElem (coreReduce M) j (by simpa [hlen] using hj)]
  simp [coreReduce, hm, List.getElem_map, List.getElem_range]

private theorem entry_coreReduce_pos (M : PS) (j : ℕ)
    (hm : entry M 1 0 ≠ 0) (hj : j < Lng (coreReduce M)) (hjpos : 0 < j) :
    0 < entry (coreReduce M) 0 j := by
  let m := entry M 1 0
  have hmpos : 0 < m := by simp [m]; omega
  have hlen : Lng (coreReduce M) = m + Lng M := by
    simp [coreReduce, hm, m, diagSeq, IncrFirstN_eq_map]
    omega
  have hj' : j < m + Lng M := by rw [← hlen]; exact hj
  have hdiaglen : Lng (diagSeq 0 (m - 1)) = m := by
    simp [diagSeq]
    omega
  have hcore : coreReduce M =
      diagSeq 0 (m - 1) ++ IncrFirstN m M := by
    simp [coreReduce, hm, m]
  rw [entry0_eq_fst_getElem (coreReduce M) j hj]
  simp only [hcore]
  by_cases hjm : j < m
  · rw [List.getElem_append_left (by simpa [hdiaglen] using hjm)]
    simp [diagSeq]
    omega
  · have hmj : m ≤ j := Nat.le_of_not_gt hjm
    have hr : j - m < Lng M := by omega
    rw [List.getElem_append_right (by simpa [hdiaglen] using hmj)]
    simp only [IncrFirstN_eq_map, List.getElem_map]
    simp
    omega

theorem coreReduce_multi_false (M : PS) (hM : TPS M)
    (hmono : monoT M = true) : multiT (coreReduce M) = false := by
  have hMpos := List.length_pos_of_ne_nil hM
  change 0 < Lng M at hMpos
  have hfull : leR M 0 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  by_cases hm : entry M 1 0 = 0
  · have hlen : Lng (coreReduce M) = Lng M := by simp [coreReduce, hm]
    have hLgt : 1 < Lng M := by
      by_contra hnot
      have hL1 : Lng M = 1 := by omega
      have hz : zeroT M = true := by simp [zeroT, hL1, hm]
      have hh := hmono
      simp [monoT, hz] at hh
    have hCT : TPS (coreReduce M) := by
      apply List.ne_nil_of_length_pos
      change 0 < Lng (coreReduce M)
      rw [hlen]
      exact hMpos
    have hle : leR (coreReduce M) 0 0 (Lng (coreReduce M) - 1) = true := by
      apply parent_exists_3 (coreReduce M) 0 (Lng (coreReduce M) - 1) hCT
      · rw [hlen]; omega
      · rw [hlen]; omega
      · intro j hj hlast
        have hjM : j < Lng M := by rw [hlen] at hlast; omega
        have hg := ancestor_basic_1 M 0 j (Lng M - 1) hM hj
          (by omega) hfull
        have he0 := entry_coreReduce_zero M 0 hm (by omega)
        have hej := entry_coreReduce_zero M j hm hjM
        omega
    have hzC : zeroT (coreReduce M) = false := by
      simp [zeroT, hlen]
      omega
    have hmonoC : monoT (coreReduce M) = true := by
      simp [monoT, hzC, hle]
    simp [multiT, hzC, hmonoC]
  · have hmpos : 0 < entry M 1 0 := by omega
    have hlen : Lng (coreReduce M) = entry M 1 0 + Lng M := by
      simp [coreReduce, hm, diagSeq, IncrFirstN_eq_map]
      omega
    have hLgt : 1 < Lng (coreReduce M) := by rw [hlen]; omega
    have hCT : TPS (coreReduce M) := by
      apply List.ne_nil_of_length_pos
      change 0 < Lng (coreReduce M)
      omega
    have hle : leR (coreReduce M) 0 0 (Lng (coreReduce M) - 1) = true := by
      apply parent_exists_3 (coreReduce M) 0 (Lng (coreReduce M) - 1) hCT
      · omega
      · omega
      · intro j hj hlast
        have he0 := (coreReduce_core M hM).1
        have hej := entry_coreReduce_pos M j hm (by omega) hj
        omega
    have hzC : zeroT (coreReduce M) = false := by
      simp [zeroT]
      omega
    have hmonoC : monoT (coreReduce M) = true := by
      simp [monoT, hzC, hle]
    simp [multiT, hzC, hmonoC]

theorem nu_coreReduce_lt (M : PS) (hM : TPS M)
    (hmono : monoT M = true)
    (hnoncore : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0)) :
    nu (coreReduce M) < nu M :=
  nu_coreReduce_lt_of_nonmulti M hM hmono hnoncore
    (coreReduce_multi_false M hM hmono)

/-! The remaining recursive argument in the core/branch case. -/

def redNJ (M : PS) (J : ℕ) : PS :=
  let block := (Br M).getD J []
  let firstNode := (FirstNodes M).getD J 0
  let joint := (Joints M).getD J 0
  let np := if entry block 1 0 = 0 then 0 else parent M 1 firstNode + 1
  (entry M 0 0 + joint + 1, entry M 1 0 + np) :: block.tail

theorem Br_component_TPS (M : PS) (J : ℕ) (hM : TPS M)
    (hJ : J < (Br M).length) : TPS ((Br M).getD J []) := by
  have hbound := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have : Br M = [] := by simp [Br, heq]
    rw [this] at hJ
    simp at hJ
  let N := seg M (TrMax M + 1) (Lng M - 1)
  have hBr : Br M = P N := by simp [N, Br, hne]
  have hNpos : 0 < Lng N := by
    simp [N]
    omega
  have hNT : TPS N := by
    intro hnil
    have : Lng N = 0 := by simp [hnil]
    omega
  rw [hBr] at hJ ⊢
  have hpos := P_component_nonempty N J hNT hJ
  exact List.ne_nil_of_length_pos hpos

theorem Br_component_nonmulti (M : PS) (J : ℕ) (hM : TPS M)
    (hJ : J < (Br M).length) :
    zeroT ((Br M).getD J []) = true ∨
      monoT ((Br M).getD J []) = true := by
  have hbound := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have : Br M = [] := by simp [Br, heq]
    rw [this] at hJ
    simp at hJ
  let N := seg M (TrMax M + 1) (Lng M - 1)
  have hBr : Br M = P N := by simp [N, Br, hne]
  have hNpos : 0 < Lng N := by
    simp [N]
    omega
  have hNT : TPS N := by
    intro hnil
    have : Lng N = 0 := by simp [hnil]
    omega
  have hmem : (P N).getD J [] ∈ P N := by
    rw [getD_eq_getElem_idx (P N) [] (by simpa [hBr] using hJ)]
    exact List.getElem_mem (by simpa [hBr] using hJ)
  rw [hBr]
  exact P_components_nonmulti N hNT ((P N).getD J []) hmem

private theorem trunk_row0_inc_core (M : PS) (j : ℕ) (hM : TPS M)
    (hcore : entry M 0 0 = 0) (hj : j ≤ TrMax M) :
    j ≤ entry M 0 j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjtr : j < TrMax M := by omega
      have hs := TrMax_trunk_step M j hM hjtr
      have hs' : nextrel1 M j (j + 1) = true := by simpa [nextR] using hs
      have hs'' := hs'
      simp only [nextrel1, Bool.and_eq_true] at hs''
      have hle0 : le0 M j (j + 1) = true := hs''.1.2
      have hle : leR M 0 j (j + 1) = true := by simpa [leR] using hle0
      have hentry := ancestor_basic_1 M j (j + 1) (j + 1) hM
        (by omega) (le_refl _) hle
      have hih := ih (by omega)
      omega

theorem Joints_nextR_FirstNodes (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) :
    nextR M 0 ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have : Br M = [] := by simp [Br, heq]
    rw [this] at hJ
    simp at hJ
  let N := seg M (TrMax M + 1) (Lng M - 1)
  have hBr : Br M = P N := by simp [N, Br, hne]
  have hJP : J ≤ (P N).length - 1 := by rw [← hBr]; omega
  have hs := mono_slice_next M (TrMax M + 1) J hM hmono
    (by omega) (by have := TrMax_bound M hM; omega)
    (by simpa [N] using hJP)
  have hfn := FirstNodes_getD M J hJ
  have habs : TrMax M + 1 + (IdxSum (P N)).getD J 0 =
      (FirstNodes M).getD J 0 := by simpa [hBr] using hfn.symm
  have hhas : hasParent M 0 ((FirstNodes M).getD J 0) = true := by
    rw [← habs]
    simpa [N] using hs.1
  have hnext := nextR_parent0_of_hasParent M ((FirstNodes M).getD J 0) hhas
  rw [Joints_getD M J hJ]
  exact hnext

theorem redNJ_head_le_block (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore0 : entry M 0 0 = 0) (hJ : J < (Br M).length) :
    (Joints M).getD J 0 + 1 ≤ entry ((Br M).getD J []) 0 0 := by
  have ht := (FirstNodes_TrMax_Joints M J hM hmono hJ).1
  have htrunk := trunk_row0_inc_core M ((Joints M).getD J 0) hM hcore0 ht
  have hn := Joints_nextR_FirstNodes M J hM hmono hJ
  have hn' : nextrel0 M ((Joints M).getD J 0)
      ((FirstNodes M).getD J 0) = true := by simpa [nextR] using hn
  have hh := hn'
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
  have hstrict : entry M 0 ((Joints M).getD J 0) <
      entry M 0 ((FirstNodes M).getD J 0) := hh.1.2
  have heq := entry_FirstNodes_eq_component M J hM hmono hJ
  omega

private theorem entry_cons_tail_pos (Q : PS) (x : ℕ × ℕ) (i j : ℕ)
    (hjpos : 0 < j) (hj : j < Lng Q) :
    entry (x :: Q.tail) i j = entry Q i j := by
  cases Q with
  | nil => simp at hj
  | cons q qs =>
      cases j with
      | zero => omega
      | succ j => simp [entry]

theorem redNJ_length (M : PS) (J : ℕ)
    (hblock : TPS ((Br M).getD J [])) :
    Lng (redNJ M J) = Lng ((Br M).getD J []) := by
  unfold redNJ
  simp only [List.length_cons, List.length_tail]
  have hpos := List.length_pos_of_ne_nil hblock
  simpa [Nat.succ_eq_add_one, Nat.add_comm] using
    Nat.succ_pred_eq_of_pos hpos

theorem redNJ_entry_hi (M : PS) (J j : ℕ)
    (hjpos : 0 < j) (hj : j < Lng ((Br M).getD J [])) :
    entry (redNJ M J) 0 j = entry ((Br M).getD J []) 0 j := by
  exact entry_cons_tail_pos ((Br M).getD J [])
    (entry M 0 0 + (Joints M).getD J 0 + 1,
      entry M 1 0 + if entry ((Br M).getD J []) 1 0 = 0 then 0
        else parent M 1 ((FirstNodes M).getD J 0) + 1) 0 j hjpos hj

theorem redNJ_multi_false (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hcore0 : entry M 0 0 = 0) (hJ : J < (Br M).length) :
    multiT (redNJ M J) = false := by
  let block := (Br M).getD J []
  have hbT : TPS block := Br_component_TPS M J hM hJ
  have hlen : Lng (redNJ M J) = Lng block := redNJ_length M J hbT
  by_cases hL : Lng block = 1
  · have hNJ1 : Lng (redNJ M J) = 1 := by omega
    by_cases he : entry (redNJ M J) 1 0 = 0
    · have hz : zeroT (redNJ M J) = true := by simp [zeroT, hNJ1, he]
      simp [multiT, hz]
    · have hz : zeroT (redNJ M J) = false := by simp [zeroT, hNJ1, he]
      have hle : leR (redNJ M J) 0 0 (Lng (redNJ M J) - 1) = true := by
        simp [leR, le0, hNJ1, le0Aux]
      have hm : monoT (redNJ M J) = true := by simp [monoT, hz, hle]
      simp [multiT, hz, hm]
  · have hbmono : monoT block = true := by
      rcases Br_component_nonmulti M J hM hJ with hz | hm
      · have hh := hz
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
        exact (hL (by simpa [block] using hh.1)).elim
      · exact hm
    have hNJpos : 0 < Lng (redNJ M J) := by
      rw [hlen]
      exact List.length_pos_of_ne_nil hbT
    have hNJgt : 1 < Lng (redNJ M J) := by omega
    have hNJT : TPS (redNJ M J) := List.ne_nil_of_length_pos hNJpos
    have hhead := redNJ_head_le_block M J hM hmono hcore0 hJ
    have hblockfull : leR block 0 0 (Lng block - 1) = true := by
      have hh := hbmono
      simp only [monoT, Bool.and_eq_true] at hh
      exact hh.2
    have hle : leR (redNJ M J) 0 0 (Lng (redNJ M J) - 1) = true := by
      apply parent_exists_3 (redNJ M J) 0 (Lng (redNJ M J) - 1) hNJT
      · omega
      · omega
      · intro j hj hlast
        have hjblock : j < Lng block := by omega
        have hg := ancestor_basic_1 block 0 j (Lng block - 1) hbT hj
          (by omega) hblockfull
        have he0 : entry (redNJ M J) 0 0 = (Joints M).getD J 0 + 1 := by
          change entry M 0 0 + (Joints M).getD J 0 + 1 =
            (Joints M).getD J 0 + 1
          omega
        have hej := redNJ_entry_hi M J j hj hjblock
        change entry (redNJ M J) 0 j = entry block 0 j at hej
        change (Joints M).getD J 0 + 1 ≤ entry block 0 0 at hhead
        omega
    have hz : zeroT (redNJ M J) = false := by
      simp [zeroT]
      omega
    have hm : monoT (redNJ M J) = true := by simp [monoT, hz, hle]
    simp [multiT, hz, hm]

private theorem Br_component_length_bound (M : PS) (J : ℕ)
    (hM : TPS M) (hJ : J < (Br M).length) :
    Lng ((Br M).getD J []) ≤ Lng M - TrMax M - 1 := by
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have : Br M = [] := by simp [Br, heq]
    rw [this] at hJ
    simp at hJ
  let N := seg M (TrMax M + 1) (Lng M - 1)
  have hBr : Br M = P N := by simp [N, Br, hne]
  have hmem : Lng ((Br M).getD J []) ∈ (Br M).map Lng := by
    apply List.mem_map.mpr
    exact ⟨(Br M).getD J [], by
      rw [getD_eq_getElem_idx (Br M) [] hJ]
      exact List.getElem_mem hJ, rfl⟩
  have hle : Lng ((Br M).getD J []) ≤ ((Br M).map Lng).sum := by
    have hsub : List.Sublist [Lng ((Br M).getD J [])] ((Br M).map Lng) :=
      List.singleton_sublist.mpr hmem
    simpa using hsub.sum_le_sum (by simp)
  have hsum : ((Br M).map Lng).sum = Lng N := by
    rw [hBr]
    simpa [List.length_flatten] using congrArg Lng (P_concat N)
  rw [hsum] at hle
  have hTr := TrMax_bound M hM
  have hNlen : Lng N = Lng M - (TrMax M + 1) := by
    simp [N]
    omega
  rw [hNlen] at hle
  omega

theorem nu_redNJ_lt (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true)
    (hcore : entry M 0 0 = 0 ∧ entry M 1 0 = 0)
    (hJ : J < (Br M).length) : nu (redNJ M J) < nu M := by
  have hMmulti : multiT M = false := by simp [multiT, hmono]
  have hNJmulti := redNJ_multi_false M J hM hmono hcore.1 hJ
  have hNJnoncore : ¬(entry (redNJ M J) 0 0 = 0 ∧
      entry (redNJ M J) 1 0 = 0) := by
    intro hh
    have he0 : entry (redNJ M J) 0 0 = (Joints M).getD J 0 + 1 := by
      change entry M 0 0 + (Joints M).getD J 0 + 1 =
        (Joints M).getD J 0 + 1
      omega
    omega
  have hbT := Br_component_TPS M J hM hJ
  have hlen := redNJ_length M J hbT
  have hlenBound := Br_component_length_bound M J hM hJ
  have hbeta : betaM (coreReduce (redNJ M J)) ≤ Lng (redNJ M J) := by
    apply betaM_coreReduce_le
    apply List.ne_nil_of_length_pos
    change 0 < Lng (redNJ M J)
    rw [hlen]
    exact List.length_pos_of_ne_nil hbT
  have hTr := TrMax_bound M hM
  have hMpos := List.length_pos_of_ne_nil hM
  change 0 < Lng M at hMpos
  have hbetaMpos : 1 ≤ betaM M := by
    simp [betaM]
    omega
  have hlenBound' : Lng (redNJ M J) ≤ Lng M - TrMax M - 1 := by
    calc
      Lng (redNJ M J) = Lng ((Br M).getD J []) := hlen
      _ ≤ Lng M - TrMax M - 1 := hlenBound
  have hlenBeta : Lng (redNJ M J) ≤ betaM M - 1 := by
    simp [betaM]
    omega
  have hnuM : nu M = 2 * betaM M := by
    simp [nu, muMono, hMmulti, hcore]
  have hnuNJ : nu (redNJ M J) =
      2 * betaM (coreReduce (redNJ M J)) + 1 := by
    simp [nu, muMono, hNJmulti, hNJnoncore]
  rw [hnuNJ, hnuM]
  omega

private theorem P_member_TPS_wd (M Q : PS) (hM : TPS M) (hQ : Q ∈ P M) :
    TPS Q := by
  obtain ⟨J, hJ, hget⟩ := List.mem_iff_getElem.mp hQ
  have hpos := P_component_nonempty M J hM hJ
  have heq : (P M).getD J [] = Q := by
    rw [getD_eq_getElem_idx (P M) [] hJ]
    exact hget
  rw [heq] at hpos
  exact List.ne_nil_of_length_pos hpos

theorem coreReduce_TPS (M : PS) (hM : TPS M) : TPS (coreReduce M) := by
  apply List.ne_nil_of_length_pos
  by_cases hm : entry M 1 0 = 0
  · have hlen : Lng (coreReduce M) = Lng M := by simp [coreReduce, hm]
    change 0 < Lng (coreReduce M)
    rw [hlen]
    exact List.length_pos_of_ne_nil hM
  · simp [coreReduce, hm, diagSeq, IncrFirstN_eq_map]

/-- Once the fuel is larger than `nu M`, evaluation is independent of the
chosen fuel.  This is the total Lean counterpart of Isabelle's `Red_dom`. -/
theorem RedAux_fuel_irrel (M : PS) (hM : TPS M) (fuel₁ fuel₂ : ℕ)
    (hf₁ : nu M < fuel₁) (hf₂ : nu M < fuel₂) :
    RedAux fuel₁ M = RedAux fuel₂ M := by
  generalize hn : nu M = n
  induction n using Nat.strong_induction_on generalizing M fuel₁ fuel₂ with
  | h n ih =>
      cases fuel₁ with
      | zero => omega
      | succ fuel₁ =>
          cases fuel₂ with
          | zero => omega
          | succ fuel₂ =>
              by_cases hz : zeroT M = true
              · simp [RedAux, hz]
              · by_cases hmulti : multiT M = true
                · simp only [RedAux, if_neg hz, if_pos hmulti]
                  apply List.flatMap_congr
                  intro Q hQ
                  have hQT := P_member_TPS_wd M Q hM hQ
                  have hdesc := nu_Pblock_lt M Q hM hmulti hQ
                  exact ih (nu Q) (by omega) Q hQT fuel₁ fuel₂
                    (by omega) (by omega) rfl
                · let j₁ := Lng M - 1
                  let t := TrMax M
                  let m₀ := entry M 0 0
                  let m₁ := entry M 1 0
                  by_cases hcore : m₀ = 0 ∧ m₁ = 0
                  · by_cases ht : t = j₁
                    · have hcore' : entry M 0 0 = 0 ∧ entry M 1 0 = 0 := by
                        simpa [m₀, m₁] using hcore
                      have ht' : TrMax M = Lng M - 1 := by simpa [t, j₁] using ht
                      simp [RedAux, hz, hmulti, hcore', ht']
                    · have hcore' : entry M 0 0 = 0 ∧ entry M 1 0 = 0 := by
                        simpa [m₀, m₁] using hcore
                      have ht' : TrMax M ≠ Lng M - 1 := by simpa [t, j₁] using ht
                      simp only [RedAux, if_neg hz, if_neg hmulti, if_pos hcore',
                        if_neg ht']
                      congr 1
                      apply List.flatMap_congr
                      intro J hJmem
                      have hJ : J < (Br M).length := List.mem_range.mp hJmem
                      have hmono : monoT M = true := by
                        have hh := hmulti
                        simp [multiT, hz] at hh
                        exact hh
                      have hNJT : TPS (redNJ M J) := by
                        have hbT := Br_component_TPS M J hM hJ
                        apply List.ne_nil_of_length_pos
                        change 0 < Lng (redNJ M J)
                        rw [redNJ_length M J hbT]
                        exact List.length_pos_of_ne_nil hbT
                      have hdesc := nu_redNJ_lt M J hM hmono
                        (by simpa [m₀, m₁] using hcore) hJ
                      have hrec := ih (nu (redNJ M J)) (by omega)
                        (redNJ M J) hNJT fuel₁ fuel₂ (by omega) (by omega) rfl
                      change IncrFirstN _ (RedAux fuel₁ (redNJ M J)) =
                        IncrFirstN _ (RedAux fuel₂ (redNJ M J))
                      rw [hrec]
                  · have hmono : monoT M = true := by
                      have hh := hmulti
                      simp [multiT, hz] at hh
                      exact hh
                    have hcore' : ¬(entry M 0 0 = 0 ∧ entry M 1 0 = 0) := by
                      simpa [m₀, m₁] using hcore
                    have hcrT := coreReduce_TPS M hM
                    have hdesc := nu_coreReduce_lt M hM hmono hcore'
                    have hrec := ih (nu (coreReduce M)) (by omega)
                      (coreReduce M) hcrT fuel₁ fuel₂ (by omega) (by omega) rfl
                    by_cases hm₁ : m₁ = 0
                    · have hm₁' : entry M 1 0 = 0 := by simpa [m₁] using hm₁
                      simp only [RedAux, if_neg hz, if_neg hmulti, if_neg hcore',
                        if_pos hm₁']
                      exact hrec
                    · have hm₁' : entry M 1 0 ≠ 0 := by simpa [m₁] using hm₁
                      simp only [RedAux, if_neg hz, if_neg hmulti, if_neg hcore',
                        if_neg hm₁']
                      rw [hrec]

theorem RedAux_stable (M : PS) (hM : TPS M) (fuel : ℕ)
    (hf : nu M < fuel) : RedAux fuel M = Red M := by
  unfold Red
  exact RedAux_fuel_irrel M hM fuel (nu M + 1) hf (by omega)

theorem Red_welldefined (M : PS) (hM : TPS M) :
    ∃! N, ∀ fuel, nu M < fuel → RedAux fuel M = N := by
  refine ⟨Red M, ?_, ?_⟩
  · intro fuel hf
    exact RedAux_stable M hM fuel hf
  · intro N hN
    have h := hN (nu M + 1) (by omega)
    simpa [Red] using h.symm

#print axioms Red_welldefined

end PSS

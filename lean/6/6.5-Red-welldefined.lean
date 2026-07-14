import PSS.Red
import «6».«6.4-mono-slice»

/-!
# §6.5 命題（`Red` の well-defined 性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_welldef`
- 訂正: なし
- Isabelle: `m_6_5_Red_welldef`
- 依存: `PSS.Red`
- 状態: ✅ 証明済（sorry 0）

Isabelle の部分関数では主張は `Red_dom M` である。Lean 版の `Red` は `nu M + 1` を燃料に
持つ全域関数として定義済みなので、対応する主張を値の存在一意性として表す。
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

private theorem entry0_eq_fst_getElem (M : PS) (j : ℕ) (hj : j < Lng M) :
    entry M 0 j = M[j].1 := by
  simp [entry, List.getElem?_eq_getElem hj]

private theorem entry_coreReduce_zero (M : PS) (j : ℕ)
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

theorem Red_welldefined (M : PS) (hM : TPS M) : ∃! N, N = Red M := by
  exact ⟨Red M, rfl, fun N hN => hN⟩

#print axioms Red_welldefined

end PSS

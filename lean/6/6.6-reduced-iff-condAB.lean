import «6».«6.6-P-condAB»
import «6».«6.6-reduced-leftend»

/-!
# §6.6 命題（簡約性と係数の関係）

- 原文: `tmp/content.md` の「命題（簡約性と係数の関係）」
- 訂正: なし
- Isabelle: `p_6_6_reduced_iff_cond`, `kst_reduced_imp_condAB_uncond`
- 依存: §6.5 `Red_rebase_nonmulti`, §6.2
- 状態: 🚨 証明作業中
-/

namespace PSS

theorem no_parent_zero (M : PS) (i : ℕ) : hasParent M i 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro hp
  have hn := hasParent_next_fseq M i 0 hp
  by_cases hi : i = 0
  · simp [nextR, hi, nextrel0] at hn
  · simp [nextR, hi, nextrel1] at hn

theorem RedCondB_apply (M : PS) (hM : TPS M)
    (hB : RedCondB M = true) (j : ℕ) (hj : j < Lng M)
    (hnp : hasParent M 0 j = false) :
    entry M 0 j = entry M 1 j := by
  have hh := hB
  simp only [RedCondB, List.all_eq_true, List.mem_range] at hh
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hj' : j < Lng M - 1 + 1 := by omega
  have hjB := hh j hj'
  simpa [hnp] using hjB

theorem RedCondB_head_eq (M : PS) (hM : TPS M)
    (hB : RedCondB M = true) :
    entry M 0 0 = entry M 1 0 := by
  exact RedCondB_apply M hM hB 0 (List.length_pos_of_ne_nil hM)
    (no_parent_zero M 0)

theorem rebaseRow0_self_of_head_eq_nonmulti (M : PS) (hM : TPS M)
    (hnm : multiT M = false)
    (hhead : entry M 0 0 = entry M 1 0) :
    rebaseRow0 (entry M 0 0) (entry M 1 0) M = M := by
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
  apply List.ext_getElem
  · simp [rebaseRow0]
  · intro j hjR hjM
    have hj : j < Lng M := by simpa using hjM
    have hMj : M[j] = (entry M 0 j, entry M 1 j) := by
      apply Prod.ext
      · exact (entry0_eq_fst_getElem_mr M j hj).symm
      · simpa [entry, List.getElem?_eq_getElem hj]
    simp only [rebaseRow0, List.getElem_map]
    rw [hMj, hhead]
    apply Prod.ext
    · simp only [Prod.fst]
      exact Nat.sub_add_cancel (by rw [← hhead]; exact hfloor j hj)
    · simp

/-- The non-multi half of the backward implication in
`reduced ↔ RedCondA ∧ RedCondB`. -/
theorem RTPS_of_condAB_nonmulti (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hB : RedCondB M = true)
    (hnm : multiT M = false) : RTPS M := by
  have hred := Red_rebase_nonmulti M hM hA hnm
  have hhead := RedCondB_head_eq M hM hB
  have hid := rebaseRow0_self_of_head_eq_nonmulti M hM hnm hhead
  have hfix : Red M = M := hred.trans hid
  have hne : M ≠ [] := hM
  simp [RTPS, reduced, hne, hfix]

theorem mono_hasParent_row0 (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (j : ℕ)
    (hjpos : 0 < j) (hjL : j < Lng M) :
    hasParent M 0 j = true := by
  have hfull : leR M 0 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hjlast : j ≤ Lng M - 1 := by omega
  have hanc := ancestor_tree_1 M 0 j (Lng M - 1) hM hfull
    (Nat.zero_le _) hjlast
  have hstrict := ancestor_basic_1 M 0 j j hM hjpos (le_refl _) hanc
  rcases parent_exists_1 M 0 j hM hjpos hjL hstrict with
    ⟨p, hp0, hpj, hp⟩
  exact (hasParent_iff_unique_fseq M 0 j).mpr
    ⟨p, hp, fun q hq => row0_parent_unique M q p j hq hp⟩

theorem RTPS_mono_RedCondB (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) : RedCondB M = true := by
  have hM := RTPS_TPS M hR
  have hhead := RTPS_mono_head_eq M hR hmono
  simp only [RedCondB, List.all_eq_true, List.mem_range]
  intro j hj
  by_cases hp : hasParent M 0 j = true
  · simp [hp]
  · have hp' : hasParent M 0 j = false := Bool.eq_false_of_not_eq_true hp
    have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
    have hjL : j < Lng M := by omega
    have hj0 : j = 0 := by
      by_contra hjne
      have hjpos : 0 < j := Nat.pos_of_ne_zero hjne
      exact hp (mono_hasParent_row0 M hM hmono j hjpos hjL)
    subst j
    simp [hp', hhead]

theorem RTPS_iff_condAB_zeroT (M : PS) (hM : TPS M)
    (hz : zeroT M = true) :
    RTPS M ↔ RedCondA M = true ∧ RedCondB M = true := by
  constructor
  · intro hR
    have hfix := RTPS_Red_eq M hR
    have hred := Red_zero_mr M hz
    have hMeq : M = [(0, 0)] := by rw [← hfix, hred]
    subst M
    decide
  · rintro ⟨hA, hB⟩
    have hnm : multiT M = false := by simp [multiT, hz]
    exact RTPS_of_condAB_nonmulti M hM hA hB hnm

/-- The `multiT` branch of the keystone equivalence.  Once the equivalence is
known recursively on every `P` component, reducedness and conditions (A), (B)
are transferred blockwise in both directions. -/
theorem RTPS_iff_condAB_multi (M : PS) (hM : TPS M)
    (_hmulti : multiT M = true)
    (IH : ∀ J, J < (P M).length →
      (RTPS ((P M).getD J []) ↔
        RedCondA ((P M).getD J []) = true ∧
          RedCondB ((P M).getD J []) = true)) :
    RTPS M ↔ RedCondA M = true ∧ RedCondB M = true := by
  constructor
  · intro hR
    have hblocksR := (RTPS_iff_P_components M hM).mp hR
    apply RedCondAB_of_P_components M hM
    intro J hJ
    exact (IH J hJ).mp (hblocksR J hJ)
  · rintro ⟨hA, hB⟩
    apply (RTPS_iff_P_components M hM).mpr
    intro J hJ
    apply (IH J hJ).mpr
    exact RedCondAB_P_component M J hM hA hB hJ

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
  have hseg := RedCondA_seg N m (Lng N - 1) hmend hend (by simpa [N] using hA)
  have hdrop : N.drop m = M := by simp [N, hDlen]
  calc
    RedCondA M = RedCondA (N.drop m) := by rw [hdrop]
    _ = RedCondA (seg N m (Lng N - 1)) := by rw [drop_eq_seg N m hmN]
    _ = true := hseg

#print axioms RTPS_of_condAB_nonmulti
#print axioms RTPS_mono_head_eq
#print axioms RTPS_mono_RedCondB
#print axioms RTPS_iff_condAB_zeroT
#print axioms RTPS_iff_condAB_multi
#print axioms RedCondA_of_diag_prefix

end PSS

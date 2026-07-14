import «5».«5.1-ancestor-tree»
import «6».«6.4-FirstNodes-TrMax-Joints»

/-!
# §6.4 系（`FirstNodes` と `Joints` の単調性）

- 原文: `isabelle/pss_paper.thy` の `p_6_4_FirstNodes_Joints_mono`
- 訂正: A3。偽である `Joints` の狭義減少を除き、三つの非狭義関係を主張する
- Isabelle: `m_6_4_FirstNodes_Joints_mono_aux`, `_mono`
- 依存: `6.4-FirstNodes-TrMax-Joints`, `6.4-P-leftend-mono`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem le0Aux_refl_fn (M : PS) (fuel j : ℕ) :
    le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

theorem nextR0_leR (M : PS) (a b : ℕ)
    (hab : nextR M 0 a b = true) : leR M 0 a b = true := by
  have hn : nextrel0 M a b = true := by simpa [nextR] using hab
  have hh := hn
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
  have haL : a < Lng M := hh.1.1.1.1
  have hbL : b < Lng M := hh.1.1.1.2
  have hablt : a < b := hh.1.1.2
  have haux : le0Aux M (Lng M) a b = true := by
    cases heq : Lng M with
    | zero => omega
    | succ fuel =>
        simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
          Bool.and_eq_true, List.mem_range]
        right
        exact ⟨a, hablt, hn, le0Aux_refl_fn M fuel a⟩
  simp [leR, le0, haL, hbL, haux]

theorem nextR0_largest_below (M : PS) (a j k : ℕ)
    (ha : nextR M 0 a k = true) (hjk : j < k)
    (he : entry M 0 j < entry M 0 k) : j ≤ a := by
  have hn : nextrel0 M a k = true := by simpa [nextR] using ha
  have hh := hn
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hh
  by_contra hnot
  have haj : a < j := by omega
  have hs := hh.2 j (List.mem_range.mpr hjk)
  have : entry M 0 k ≤ entry M 0 j := by simpa [haj] using hs
  omega

theorem nextR_parent0_of_hasParent (M : PS) (k : ℕ)
    (h : hasParent M 0 k = true) : nextR M 0 (parent M 0 k) k = true := by
  obtain ⟨p, hp, _⟩ := (hasParent_iff_unique_fseq M 0 k).mp h
  have heq := parent_eq_of_nextR0 M p k hp
  simpa [heq] using hp

theorem entry_FirstNodes_eq_component (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) :
    entry M 0 ((FirstNodes M).getD J 0) =
      entry ((Br M).getD J []) 0 0 := by
  have hbound := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have : Br M = [] := by simp [Br, heq]
    rw [this] at hJ
    simp at hJ
  have htrlt : TrMax M < Lng M - 1 := by omega
  let N := seg M (TrMax M + 1) (Lng M - 1)
  have hBr : Br M = P N := by simp [N, Br, hne]
  have hNpos : 0 < Lng N := by simp [N]; omega
  have hNT : TPS N := by
    intro hnil
    have : Lng N = 0 := by simp [hnil]
    omega
  have hJP : J < (P N).length := by simpa [hBr] using hJ
  let k := (IdxSum (P N)).getD J 0
  have hkN : k < Lng N := by
    have hl := (P_leftend_lmin N J hNT hJP).1
    have hpred : Lng N - 1 + 1 = Lng N :=
      Nat.sub_add_cancel (show 1 ≤ Lng N from hNpos)
    simpa [k] using (show (IdxSum (P N)).getD J 0 < Lng N by omega)
  have hentryN : entry N 0 k = entry ((P N).getD J []) 0 0 := by
    symm
    simpa [k] using P_component_leftend N J hNT hJP
  have hentryM : entry N 0 k = entry M 0 (TrMax M + 1 + k) := by
    simpa [N] using entry_seg M (TrMax M + 1) (Lng M - 1) 0 k hkN
  have hfn := FirstNodes_getD M J hJ
  rw [hfn, hBr]
  change entry M 0 (TrMax M + 1 + k) = entry ((P N).getD J []) 0 0
  rw [← hentryM, hentryN]

theorem FirstNodes_Joints_mono (M : PS) (J₀ J₁ : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (h01 : J₀ < J₁) (hJ₁ : J₁ < (Br M).length) :
    (FirstNodes M).getD J₀ 0 ≤ (FirstNodes M).getD J₁ 0 ∧
      (Joints M).getD J₁ 0 ≤ (Joints M).getD J₀ 0 ∧
      entry M 0 ((FirstNodes M).getD J₁ 0) ≤
        entry M 0 ((FirstNodes M).getD J₀ 0) := by
  have hJ₀ : J₀ < (Br M).length := h01.trans hJ₁
  have hidx := idxSum_mono (Br M) J₀ J₁ h01.le hJ₁.le
  have hfn₀ := FirstNodes_getD M J₀ hJ₀
  have hfn₁ := FirstNodes_getD M J₁ hJ₁
  have hpart1 : (FirstNodes M).getD J₀ 0 ≤ (FirstNodes M).getD J₁ 0 := by
    omega
  have hbound := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have : Br M = [] := by simp [Br, heq]
    rw [this] at hJ₁
    simp at hJ₁
  have htrlt : TrMax M < Lng M - 1 := by omega
  let N := seg M (TrMax M + 1) (Lng M - 1)
  have hBr : Br M = P N := by simp [N, Br, hne]
  have hNpos : 0 < Lng N := by simp [N]; omega
  have hNT : TPS N := by
    intro hnil
    have : Lng N = 0 := by simp [hnil]
    omega
  have hJ₁P : J₁ ≤ (P N).length - 1 := by rw [← hBr]; omega
  have hleft := P_leftend_mono N J₀ J₁ hNT h01.le hJ₁P
  have he₀ := entry_FirstNodes_eq_component M J₀ hM hmono hJ₀
  have he₁ := entry_FirstNodes_eq_component M J₁ hM hmono hJ₁
  have hpart3 : entry M 0 ((FirstNodes M).getD J₁ 0) ≤
      entry M 0 ((FirstNodes M).getD J₀ 0) := by
    rw [he₀, he₁, hBr]
    exact hleft
  let f₀ := (FirstNodes M).getD J₀ 0
  let f₁ := (FirstNodes M).getD J₁ 0
  let a₀ := (Joints M).getD J₀ 0
  let a₁ := (Joints M).getD J₁ 0
  have ht₀ := FirstNodes_TrMax_Joints M J₀ hM hmono hJ₀
  have ht₁ := FirstNodes_TrMax_Joints M J₁ hM hmono hJ₁
  have hJ₀P : J₀ ≤ (P N).length - 1 := by rw [← hBr]; omega
  have hs₀ := mono_slice_next M (TrMax M + 1) J₀ hM hmono
    (by omega) (by omega) (by simpa [N] using hJ₀P)
  have hs₁ := mono_slice_next M (TrMax M + 1) J₁ hM hmono
    (by omega) (by omega) (by simpa [N] using hJ₁P)
  have habs₀ : TrMax M + 1 + (IdxSum (P N)).getD J₀ 0 = f₀ := by
    simpa [f₀, hBr] using hfn₀.symm
  have habs₁ : TrMax M + 1 + (IdxSum (P N)).getD J₁ 0 = f₁ := by
    simpa [f₁, hBr] using hfn₁.symm
  have hhas₀ : hasParent M 0 f₀ = true := by
    rw [← habs₀]
    simpa [N] using hs₀.1
  have hhas₁ : hasParent M 0 f₁ = true := by
    rw [← habs₁]
    simpa [N] using hs₁.1
  have ha₀ : a₀ = parent M 0 f₀ := by
    simpa [a₀, f₀] using Joints_getD M J₀ hJ₀
  have ha₁ : a₁ = parent M 0 f₁ := by
    simpa [a₁, f₁] using Joints_getD M J₁ hJ₁
  have hnx₀ : nextR M 0 a₀ f₀ = true := by
    rw [ha₀]
    exact nextR_parent0_of_hasParent M f₀ hhas₀
  have hnx₁ : nextR M 0 a₁ f₁ = true := by
    rw [ha₁]
    exact nextR_parent0_of_hasParent M f₁ hhas₁
  have ha₁f₀ : a₁ < f₀ := by
    change (Joints M).getD J₁ 0 < (FirstNodes M).getD J₀ 0
    omega
  have hf₀f₁ : f₀ ≤ f₁ := by simpa [f₀, f₁] using hpart1
  have ha₁le : leR M 0 a₁ f₁ = true := nextR0_leR M a₁ f₁ hnx₁
  have ha₁f₀anc := ancestor_tree_1 M a₁ f₀ f₁ hM ha₁le ha₁f₀.le hf₀f₁
  have he₁f₀ : entry M 0 a₁ < entry M 0 f₀ :=
    ancestor_basic_1 M a₁ f₀ f₀ hM ha₁f₀ (le_refl _) ha₁f₀anc
  have hpart2 : a₁ ≤ a₀ := nextR0_largest_below M a₀ a₁ f₀ hnx₀ ha₁f₀ he₁f₀
  exact ⟨hpart1, by simpa [a₀, a₁] using hpart2, hpart3⟩

#print axioms FirstNodes_Joints_mono

end PSS

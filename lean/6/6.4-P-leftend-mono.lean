import «6».«6.4-P-IdxSum-characterization»

/-!
# §6.4 命題（`P` の各成分の左端の単調性）

- 原文: `isabelle/pss_paper.thy` の `p_6_4_P_leftend_mono`
- 訂正: なし
- Isabelle: `m_6_4_P_leftend_mono`
- 依存: `6.4-P-IdxSum-characterization`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem idxSum_mono (Q : List PS) (J₀ J₁ : ℕ)
    (h01 : J₀ ≤ J₁) (h1 : J₁ ≤ Q.length) :
    (IdxSum Q).getD J₀ 0 ≤ (IdxSum Q).getD J₁ 0 := by
  rw [idxSum_getD Q J₀ (h01.trans h1), idxSum_getD Q J₁ h1]
  have hp : Q.take J₀ <+: Q.take J₁ :=
    List.take_isPrefix_take.mpr (Or.inl h01)
  rcases hp with ⟨r, hr⟩
  rw [← hr]
  simp

theorem P_component_leftend (M : PS) (J : ℕ) (hM : TPS M)
    (hJ : J < (P M).length) :
    entry ((P M).getD J []) 0 0 =
      entry M 0 ((IdxSum (P M)).getD J 0) := by
  have hcomp := P_IdxSum M J hM (by omega)
  have hpos := P_component_nonempty M J hM hJ
  have hsegpos : 0 < Lng (seg M
      ((IdxSum (P M)).getD J 0)
      ((IdxSum (P M)).getD (J + 1) 0 - 1)) := by
    rw [← hcomp]
    exact hpos
  rw [hcomp]
  exact entry_seg M _ _ 0 0 hsegpos

theorem P_leftend_mono (M : PS) (J₀ J₁ : ℕ) (hM : TPS M)
    (h01 : J₀ ≤ J₁) (hJ₁ : J₁ ≤ (P M).length - 1) :
    entry ((P M).getD J₁ []) 0 0 ≤
      entry ((P M).getD J₀ []) 0 0 := by
  have hPpos := List.length_pos_of_ne_nil (P_nonempty M)
  have hJ₁L : J₁ < (P M).length := by omega
  have hJ₀L : J₀ < (P M).length := h01.trans_lt hJ₁L
  let a₀ := (IdxSum (P M)).getD J₀ 0
  let a₁ := (IdxSum (P M)).getD J₁ 0
  have ha : a₀ ≤ a₁ := idxSum_mono (P M) J₀ J₁ h01 hJ₁L.le
  have hlmin := (P_leftend_lmin M J₁ hM hJ₁L).2
  rw [P_component_leftend M J₀ hM hJ₀L,
    P_component_leftend M J₁ hM hJ₁L]
  change entry M 0 a₁ ≤ entry M 0 a₀
  by_cases heq : a₀ = a₁
  · exact (congrArg (fun x => entry M 0 x) heq.symm).le
  · exact hlmin a₀ (by omega)

#print axioms P_leftend_mono

end PSS

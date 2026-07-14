import PSS.Red
import «6».«6.4-mono-slice»

/-!
# §6.5 命題（`Lng` の `Red` 不変性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Lng_Red`
- 訂正: なし
- Isabelle: `m_6_5_Lng_Red`
- 依存: `6.5-Red-welldefined`, §6.4
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

@[simp] theorem length_IncrFirstN (n : ℕ) (M : PS) :
    Lng (IncrFirstN n M) = Lng M := by
  induction n generalizing M with
  | zero => rfl
  | succ n ih =>
      simp only [IncrFirstN]
      rw [ih]
      simp [IncrFirst]

private theorem P_member_TPS (M Q : PS) (hM : TPS M) (hQ : Q ∈ P M) : TPS Q := by
  obtain ⟨J, hJ, hget⟩ := List.mem_iff_getElem.mp hQ
  have hpos := P_component_nonempty M J hM hJ
  have heq : (P M).getD J [] = Q := by
    rw [getD_eq_getElem_idx (P M) [] hJ]
    exact hget
  rw [heq] at hpos
  intro hnil
  simp [hnil] at hpos

private theorem Br_component_nonempty (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hJ : J < (Br M).length) :
    0 < Lng ((Br M).getD J []) := by
  have hbound := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have : Br M = [] := by simp [Br, heq]
    rw [this] at hJ
    simp at hJ
  let N := seg M (TrMax M + 1) (Lng M - 1)
  have hBr : Br M = P N := by simp [N, Br, hne]
  have hNpos : 0 < Lng N := by
    have hMpos := List.length_pos_of_ne_nil hM
    simp [N]
    omega
  have hNT : TPS N := by
    intro hnil
    have : Lng N = 0 := by simp [hnil]
    omega
  rw [hBr] at hJ ⊢
  exact P_component_nonempty N J hNT hJ

private theorem map_range_getD_length (Q : List PS) :
    (List.range Q.length).map (fun J => Lng (Q.getD J [])) = Q.map Lng := by
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    have hn : n < Q.length := by simpa using h₁
    simp only [List.getElem_map, List.getElem_range]
    rw [getD_eq_getElem_idx Q [] hn]

theorem RedAux_length (fuel : ℕ) (M : PS) (hM : TPS M) :
    Lng (RedAux fuel M) = Lng M := by
  induction fuel generalizing M with
  | zero => simp [RedAux]
  | succ fuel ih =>
      have hMpos := List.length_pos_of_ne_nil hM
      by_cases hz : zeroT M = true
      · rw [RedAux, if_pos hz]
        have hh := hz
        simp [zeroT] at hh
        exact hh.1.symm
      · rw [RedAux, if_neg hz]
        by_cases hmulti : multiT M = true
        · rw [if_pos hmulti]
          have hlenEach : ∀ Q ∈ P M, Lng (RedAux fuel Q) = Lng Q := by
            intro Q hQ
            exact ih Q (P_member_TPS M Q hM hQ)
          have hmaps : (P M).map (fun Q => Lng (RedAux fuel Q)) =
              (P M).map Lng := by
            apply List.map_congr_left
            intro Q hQ
            exact hlenEach Q hQ
          calc
            Lng ((P M).flatMap (fun Q => RedAux fuel Q)) =
                ((P M).map (fun Q => Lng (RedAux fuel Q))).sum := by
                  simp [List.length_flatMap]
            _ = ((P M).map Lng).sum := by rw [hmaps]
            _ = Lng (P M).flatten := by simp [List.length_flatten]
            _ = Lng M := by rw [P_concat]
        · rw [if_neg hmulti]
          let j₁ := Lng M - 1
          let t := TrMax M
          let m₀ := entry M 0 0
          let m₁ := entry M 1 0
          by_cases hcore : m₀ = 0 ∧ m₁ = 0
          · rw [if_pos hcore]
            by_cases ht : t = j₁
            · rw [if_pos ht]
              change Lng (diagSeq m₁ (m₁ + j₁)) = Lng M
              rw [hcore.2]
              simpa [diagSeq, j₁] using Nat.sub_add_cancel hMpos
            · rw [if_neg ht]
              have hmono : monoT M = true := by
                simp [multiT, hz] at hmulti
                exact hmulti
              have htbound := TrMax_bound M hM
              have htlt : t < j₁ := by simp [t, j₁] at ht ⊢; omega
              have hBrlen : Lng (Br M).flatten = Lng M - (t + 1) := by
                have hBr : Br M = P (seg M (t + 1) (Lng M - 1)) := by
                  have hne0 : TrMax M ≠ Lng M - 1 := by simpa [t, j₁] using ht
                  simp [Br, hne0, t]
                rw [hBr, P_concat]
                simp [t]
                omega
              let f : ℕ → PS := fun J =>
                let block := (Br M).getD J []
                let firstNode := (FirstNodes M).getD J 0
                let joint := (Joints M).getD J 0
                let np := if entry block 1 0 = 0 then 0 else parent M 1 firstNode + 1
                let eJ := joint + 1 - np
                let NJ := (m₀ + joint + 1, m₁ + np) :: block.tail
                IncrFirstN eJ (RedAux fuel NJ)
              have hf : ∀ J, J < (Br M).length → Lng (f J) = Lng ((Br M).getD J []) := by
                intro J hJ
                let block := (Br M).getD J []
                let firstNode := (FirstNodes M).getD J 0
                let joint := (Joints M).getD J 0
                let np := if entry block 1 0 = 0 then 0 else parent M 1 firstNode + 1
                let eJ := joint + 1 - np
                let NJ := (m₀ + joint + 1, m₁ + np) :: block.tail
                have hbpos := Br_component_nonempty M J hM hmono hJ
                change 0 < block.length at hbpos
                have hNJ : TPS NJ := by
                  intro hnil
                  simp [NJ] at hnil
                have hih := ih NJ hNJ
                have hNJlen : Lng NJ = Lng block := by
                  change NJ.length = block.length
                  simp [NJ]
                  omega
                change Lng (IncrFirstN eJ (RedAux fuel NJ)) = Lng block
                rw [length_IncrFirstN, hih, hNJlen]
              have hmap : (List.range (Br M).length).map (fun J => Lng (f J)) =
                  (Br M).map Lng := by
                rw [← map_range_getD_length (Br M)]
                apply List.map_congr_left
                intro J hJ
                exact hf J (List.mem_range.mp hJ)
              change Lng (diagSeq 0 t ++ (List.range (Br M).length).flatMap f) = Lng M
              simp only [List.length_append, List.length_flatMap]
              rw [hmap]
              have hsum : ((Br M).map Lng).sum = Lng M - (t + 1) := by
                simpa [List.length_flatten] using hBrlen
              rw [hsum]
              simp [diagSeq]
              omega
          · rw [if_neg hcore]
            by_cases hm₁ : m₁ = 0
            · rw [if_pos hm₁]
              have hcoreLen : Lng (coreReduce M) = Lng M := by
                unfold coreReduce
                rw [if_pos (by simpa [m₁] using hm₁)]
                simp
              have hcoreT : TPS (coreReduce M) := by
                apply List.ne_nil_of_length_pos
                change 0 < Lng (coreReduce M)
                rw [hcoreLen]
                exact hMpos
              rw [ih (coreReduce M) hcoreT, hcoreLen]
            · rw [if_neg hm₁]
              have hm₁pos : 0 < m₁ := by omega
              have hcoreLen : Lng (coreReduce M) = m₁ + Lng M := by
                simp [coreReduce, m₁, hm₁, diagSeq]
                omega
              have hcoreT : TPS (coreReduce M) := by
                intro hnil
                have : Lng (coreReduce M) = 0 := by simp [hnil]
                omega
              let N := RedAux fuel (coreReduce M)
              let jN := Lng N - 1
              have hNlen : Lng N = m₁ + Lng M := by
                simpa [N, hcoreLen] using ih (coreReduce M) hcoreT
              let cond := decide (m₁ ≤ jN) && monoT (seg N m₁ jN)
              change Lng (if cond then
                (List.range' m₁ (jN + 1 - m₁)).map (fun j =>
                  (entry N 0 j - entry N 0 m₁ + entry N 1 m₁, entry N 1 j))
                else M) = Lng M
              by_cases hcond : cond = true
              · rw [if_pos hcond]
                simp [jN, hNlen]
                omega
              · rw [if_neg hcond]

theorem Lng_Red_invariance (M : PS) (hM : TPS M) : Lng (Red M) = Lng M := by
  exact RedAux_length (nu M + 1) M hM

#print axioms Lng_Red_invariance

end PSS

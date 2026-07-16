import «6».«6.7-standard-P-components»
import «6».«6.4-P-leftend-mono»

/-!
# §6.8 命題（標準形の単項成分が降順であること）

- 原文: `isabelle/pss_paper.thy` の `p_6_8_standard_P_descending`
- Isabelle: `m_6_8_standard_P_descending`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem multiT_diagSeq_false_sd (u v : ℕ) (huv : u ≤ v) :
    multiT (diagSeq u v) = false := by
  let M := diagSeq u v
  have hM : TPS M := by
    apply List.ne_nil_of_length_pos
    simp [M, diagSeq]
    omega
  apply (multi_criterion_12 M hM).mpr
  intro j hjpos hjL
  have hentry (q : ℕ) (hq : q < Lng M) : entry M 0 q = u + q := by
    have hget : M[q]? = some (u + q, u + q) := by
      rw [List.getElem?_eq_getElem hq]
      congr 1
      simp [M, diagSeq, List.getElem_map, List.getElem_range']
    simp [entry, hget]
  rw [hentry 0 (List.length_pos_of_ne_nil hM), hentry j hjL]
  omega

private theorem oper_entry_zero_sd (M : PS) (n i : ℕ)
    (hM : TPS M) (hn : 1 ≤ n) :
    entry (oper M n) i 0 = entry M i 0 := by
  by_cases hlen : 1 < Lng M
  · unfold entry
    rw [oper_head_fseq M n hM hlen hn]
  · have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
    have hL : Lng M = 1 := by omega
    simp [oper, hL]

private theorem getD_mem_sd {α : Type} (Q : List α) (d : α)
    (j : ℕ) (hj : j < Q.length) : Q.getD j d ∈ Q := by
  rw [getD_eq_getElem_idx Q d hj]
  exact List.getElem_mem hj

private theorem getD_dropLast_sd {α : Type} (Q : List α) (d : α)
    (j : ℕ) (hj : j < Q.dropLast.length) :
    Q.dropLast.getD j d = Q.getD j d := by
  have hjQ : j < Q.length := by
    have hle : Q.dropLast.length ≤ Q.length := by simp
    omega
  rw [getD_eq_getElem_idx Q.dropLast d hj,
    getD_eq_getElem_idx Q d hjQ]
  simp only [List.getElem_dropLast]

private theorem getD_append_left_sd {α : Type} (A B : List α) (d : α)
    (j : ℕ) (hj : j < A.length) :
    (A ++ B).getD j d = A.getD j d := by
  have hjAB : j < (A ++ B).length := by simp; omega
  rw [getD_eq_getElem_idx (A ++ B) d hjAB,
    getD_eq_getElem_idx A d hj]
  exact List.getElem_append_left hj

private theorem getD_append_right_sd {α : Type} (A B : List α) (d : α)
    (j : ℕ) (hj : A.length ≤ j) (hjAB : j < (A ++ B).length) :
    (A ++ B).getD j d = B.getD (j - A.length) d := by
  have hjB : j - A.length < B.length := by simp at hjAB; omega
  rw [getD_eq_getElem_idx (A ++ B) d hjAB,
    getD_eq_getElem_idx B d hjB]
  exact List.getElem_append_right hj

private theorem getLastD_eq_getD_last_sd {α : Type} (Q : List α) (d : α)
    (hQ : Q ≠ []) : Q.getLastD d = Q.getD (Q.length - 1) d := by
  cases h : Q with
  | nil => exact (hQ h).elim
  | cons x xs =>
      simp [List.getLastD, List.getD, List.getLast_eq_getElem]

private theorem getLastD_mem_sd {α : Type} (Q : List α) (d : α)
    (hQ : Q ≠ []) : Q.getLastD d ∈ Q := by
  cases h : Q with
  | nil => exact (hQ h).elim
  | cons x xs => simp [List.getLastD]

private theorem entry_Pred_zero_sd (M : PS) (i : ℕ) (hlen : 1 < Lng M) :
    entry (Pred M) i 0 = entry M i 0 := by
  simp [Pred, Nat.not_le_of_lt hlen, List.dropLast_eq_take,
    entry, List.getElem?_take_of_lt (by omega : 0 < Lng M - 1)]

/-- Every principal component of a non-multi fundamental-sequence value keeps
both entries of the source's left column. -/
private theorem nonmulti_oper_component_leftcol_sd (C D : PS) (n : ℕ)
    (hC : TPS C) (hn : 1 ≤ n) (hnm : multiT C = false)
    (hD : D ∈ P (oper C n)) :
    entry D 0 0 = entry C 0 0 ∧ entry D 1 0 = entry C 1 0 := by
  by_cases hcond : nextR C 0 0 (Lng C - 1) = true ∧
      entry C 1 (Lng C - 1) = 0
  · have hP := nonmulti_fseq_1 C n hC hn hnm hcond.1 hcond.2
    have hDeq : D = Pred C := by
      have hm : D ∈ List.replicate n (Pred C) := by simpa [hP] using hD
      have hh : n ≠ 0 ∧ D = Pred C := by simpa using hm
      exact hh.2
    have hlastpos : 0 < Lng C - 1 :=
      (nextR_implies_row0 C 0 0 (Lng C - 1) hcond.1).1
    have hlen : 1 < Lng C := by omega
    subst D
    exact ⟨entry_Pred_zero_sd C 0 hlen, entry_Pred_zero_sd C 1 hlen⟩
  · have hcases : nextR C 0 0 (Lng C - 1) = false ∨
        0 < entry C 1 (Lng C - 1) := by
      cases hnxt : nextR C 0 0 (Lng C - 1) with
      | false => exact Or.inl rfl
      | true =>
          right
          by_contra hz
          have hz0 : entry C 1 (Lng C - 1) = 0 := by omega
          exact hcond ⟨hnxt, hz0⟩
    have hP := nonmulti_fseq_2 C n hC hn hnm hcases
    have hDeq : D = oper C n := by simpa [hP] using hD
    subst D
    exact ⟨oper_entry_zero_sd C n 0 hC hn,
      oper_entry_zero_sd C n 1 hC hn⟩

/-- §6.8 row-one tie-break: later principal components of a standard pair
sequence cannot have a larger row-one left entry when row zero ties. -/
theorem standard_P_descending (M : PS) (hM : STPS M)
    (J₀ J₁ : ℕ) (hJ : J₀ ≤ J₁) (hJ₁ : J₁ ≤ (P M).length - 1)
    (htie : entry ((P M).getD J₀ []) 0 0 =
      entry ((P M).getD J₁ []) 0 0) :
    entry ((P M).getD J₁ []) 1 0 ≤
      entry ((P M).getD J₀ []) 1 0 := by
  induction hM generalizing J₀ J₁ with
  | diag u v huv =>
      have hP : P (diagSeq u v) = [diagSeq u v] :=
        P_nonmulti_eq (diagSeq u v) (multiT_diagSeq_false_sd u v huv)
      have hJ₁0 : J₁ = 0 := by simp [hP] at hJ₁; omega
      have hJ₀0 : J₀ = 0 := by omega
      subst J₀
      subst J₁
      exact le_rfl
  | oper hST n hn ih =>
      rename_i N
      have hNT : TPS N := STPS_TPS N hST
      have hPne : P N ≠ [] := P_nonempty N
      have hJ₁op : J₁ < (P (oper N n)).length := by
        have := List.length_pos_of_ne_nil (P_nonempty (oper N n))
        omega
      have hJ₀op : J₀ < (P (oper N n)).length := hJ.trans_lt hJ₁op
      by_cases hmulti : multiT N = true
      · have hPlen : 1 < (P N).length :=
          (P_components_multi_iff N hNT).mp hmulti
        let D := (P N).getLastD []
        have hDmem : D ∈ P N := by
          simpa [D] using getLastD_mem_sd (P N) [] hPne
        have hDT : TPS D := by
          rcases List.mem_iff_getElem.mp hDmem with ⟨j, hj, hjD⟩
          have hpos := P_component_nonempty N j hNT hj
          have hget : (P N).getD j [] = D := by
            rw [getD_eq_getElem_idx (P N) [] hj]
            exact hjD
          rw [hget] at hpos
          exact List.ne_nil_of_length_pos hpos
        have hDnm : multiT D = false := by
          rcases P_components_nonmulti N hNT D hDmem with hz | hm
          · simp [multiT, hz]
          · simp [multiT, hm]
        by_cases hDone : Lng D = 1
        · have hrel := P_fseq_1 N n hNT hn (by simpa [D] using hDone)
          have hP : P (oper N n) = (P N).dropLast := by
            simpa [show (P N).length ≠ 1 by omega] using hrel.2
          have hJ₁drop : J₁ < (P N).dropLast.length := by simpa [hP] using hJ₁op
          have hJ₀drop : J₀ < (P N).dropLast.length := hJ.trans_lt hJ₁drop
          have e₀ : (P (oper N n)).getD J₀ [] = (P N).getD J₀ [] := by
            rw [hP, getD_dropLast_sd (P N) [] J₀ hJ₀drop]
          have e₁ : (P (oper N n)).getD J₁ [] = (P N).getD J₁ [] := by
            rw [hP, getD_dropLast_sd (P N) [] J₁ hJ₁drop]
          have hJ₁N : J₁ ≤ (P N).length - 1 := by
            have hdropLen : (P N).dropLast.length = (P N).length - 1 := by simp
            omega
          have htieN : entry ((P N).getD J₀ []) 0 0 =
              entry ((P N).getD J₁ []) 0 0 := by
            rw [e₀, e₁] at htie
            exact htie
          rw [e₀, e₁]
          exact ih J₀ J₁ hJ hJ₁N htieN
        · have hDgt : 1 < Lng D := by
            have hDpos : 0 < Lng D := List.length_pos_of_ne_nil hDT
            omega
          have hrel := P_fseq_2 N n hNT hn (by simpa [D] using hDgt)
          let A := (P N).dropLast
          let B := P (oper D n)
          have hP : P (oper N n) = A ++ B := by simpa [A, B, D] using hrel.2
          let K := A.length
          have hK : K = (P N).length - 1 := by simp [K, A]
          by_cases hJ₁K : J₁ < K
          · have hJ₀K : J₀ < K := hJ.trans_lt hJ₁K
            have hJ₀drop := hJ₀K
            change J₀ < (P N).dropLast.length at hJ₀drop
            have hJ₁drop := hJ₁K
            change J₁ < (P N).dropLast.length at hJ₁drop
            have e₀ : (P (oper N n)).getD J₀ [] = (P N).getD J₀ [] := by
              rw [hP, getD_append_left_sd A B [] J₀ hJ₀K,
                show A.getD J₀ [] = (P N).getD J₀ [] by
                  exact getD_dropLast_sd (P N) [] J₀ hJ₀drop]
            have e₁ : (P (oper N n)).getD J₁ [] = (P N).getD J₁ [] := by
              rw [hP, getD_append_left_sd A B [] J₁ hJ₁K,
                show A.getD J₁ [] = (P N).getD J₁ [] by
                  exact getD_dropLast_sd (P N) [] J₁ hJ₁drop]
            have hJ₁N : J₁ ≤ (P N).length - 1 := by omega
            have htieN : entry ((P N).getD J₀ []) 0 0 =
                entry ((P N).getD J₁ []) 0 0 := by
              rw [e₀, e₁] at htie
              exact htie
            rw [e₀, e₁]
            exact ih J₀ J₁ hJ hJ₁N htieN
          · have hKJ₁ : K ≤ J₁ := by omega
            have e₁ : (P (oper N n)).getD J₁ [] = B.getD (J₁ - K) [] := by
              rw [hP]
              exact getD_append_right_sd A B [] J₁ hKJ₁ (by simpa [hP] using hJ₁op)
            have hJ₁B : J₁ - K < B.length := by
              have : J₁ < (A ++ B).length := by simpa [hP] using hJ₁op
              simp at this
              omega
            have hcomp₁ : B.getD (J₁ - K) [] ∈ P (oper D n) := by
              simpa [B] using getD_mem_sd B [] (J₁ - K) hJ₁B
            have hleft₁ := nonmulti_oper_component_leftcol_sd D
              (B.getD (J₁ - K) []) n hDT hn hDnm (by simpa [B] using hcomp₁)
            by_cases hJ₀K : J₀ < K
            · have hJ₀drop := hJ₀K
              change J₀ < (P N).dropLast.length at hJ₀drop
              have e₀ : (P (oper N n)).getD J₀ [] = (P N).getD J₀ [] := by
                rw [hP, getD_append_left_sd A B [] J₀ hJ₀K,
                  show A.getD J₀ [] = (P N).getD J₀ [] by
                    exact getD_dropLast_sd (P N) [] J₀ hJ₀drop]
              have hDlast : D = (P N).getD K [] := by
                calc
                  D = (P N).getLastD [] := rfl
                  _ = (P N).getD ((P N).length - 1) [] :=
                    getLastD_eq_getD_last_sd (P N) [] hPne
                  _ = (P N).getD K [] := by rw [hK]
              have htieN : entry ((P N).getD J₀ []) 0 0 =
                  entry ((P N).getD K []) 0 0 := by
                rw [← hDlast, ← hleft₁.1, ← e₁, ← e₀]
                exact htie
              have hih := ih J₀ K (by omega) (by rw [hK]) htieN
              rw [e₀, e₁, hleft₁.2, hDlast]
              exact hih
            · have hKJ₀ : K ≤ J₀ := by omega
              have e₀ : (P (oper N n)).getD J₀ [] = B.getD (J₀ - K) [] := by
                rw [hP]
                exact getD_append_right_sd A B [] J₀ hKJ₀ (by simpa [hP] using hJ₀op)
              have hJ₀B : J₀ - K < B.length := by
                have : J₀ < (A ++ B).length := by simpa [hP] using hJ₀op
                simp at this
                omega
              have hcomp₀ : B.getD (J₀ - K) [] ∈ P (oper D n) := by
                simpa [B] using getD_mem_sd B [] (J₀ - K) hJ₀B
              have hleft₀ := nonmulti_oper_component_leftcol_sd D
                (B.getD (J₀ - K) []) n hDT hn hDnm (by simpa [B] using hcomp₀)
              rw [e₀, e₁, hleft₀.2, hleft₁.2]
      · have hnonmulti : multiT N = false := Bool.eq_false_of_not_eq_true hmulti
        have hQ₀ : (P (oper N n)).getD J₀ [] ∈ P (oper N n) :=
          getD_mem_sd (P (oper N n)) [] J₀ hJ₀op
        have hQ₁ : (P (oper N n)).getD J₁ [] ∈ P (oper N n) :=
          getD_mem_sd (P (oper N n)) [] J₁ hJ₁op
        have hleft₀ := nonmulti_oper_component_leftcol_sd N
          ((P (oper N n)).getD J₀ []) n hNT hn hnonmulti hQ₀
        have hleft₁ := nonmulti_oper_component_leftcol_sd N
          ((P (oper N n)).getD J₁ []) n hNT hn hnonmulti hQ₁
        rw [hleft₀.2, hleft₁.2]

#print axioms standard_P_descending

end PSS

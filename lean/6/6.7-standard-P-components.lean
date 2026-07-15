import «5».«5.3-pred-is-oper1»
import «6».«6.2-nonmulti-fseq»
import «6».«6.4-P-IdxSum»
import «6».«6.7-standard-prefix»

/-!
# §6.7 命題（標準形の単項成分が標準形であること）

- Isabelle: `m_6_7_standard_P_components`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- Every fixed-rank standard sequence is standard. -/
theorem SkTPS_STPS (k : ℕ) (M : PS) (hM : SkTPS k M) : STPS M := by
  induction k generalizing M with
  | zero =>
      rcases hM with ⟨u, v, rfl, huv⟩
      exact STPS.diag u v huv
  | succ k ih =>
      rcases hM with ⟨N, n, rfl, hN, hn⟩
      exact STPS.oper (ih N hN) n hn

/-- Every fixed-rank standard sequence is nonempty. -/
theorem SkTPS_TPS (k : ℕ) (M : PS) (hM : SkTPS k M) : TPS M :=
  STPS_TPS M (SkTPS_STPS k M hM)

private theorem diagSeq_succ_snoc (u v : ℕ) (huv : u ≤ v) :
    diagSeq u (v + 1) = diagSeq u v ++ [(v + 1, v + 1)] := by
  have hrange :
    List.range' u (v + 1 + 1 - u) =
      List.range' u (v + 1 - u) ++ [v + 1] := by
    calc
      List.range' u (v + 1 + 1 - u) =
          List.range' u ((v + 1 - u) + 1) := by congr 2; omega
      _ = List.range' u (v + 1 - u) ++
          List.range' (u + (v + 1 - u)) 1 := List.range'_append_1.symm
      _ = List.range' u (v + 1 - u) ++ [v + 1] := by
        rw [Nat.add_sub_of_le (by omega : u ≤ v + 1)]
        simp
  simp [diagSeq, hrange]

private theorem Pred_diagSeq_succ (u v : ℕ) (huv : u ≤ v) :
    Pred (diagSeq u (v + 1)) = diagSeq u v := by
  have hlen : 1 < Lng (diagSeq u (v + 1)) := by
    simp [diagSeq]
    omega
  rw [Pred, if_neg (by omega), diagSeq_succ_snoc u v huv]
  simp

private theorem entry_diagSeq_rank (u v i j : ℕ)
    (hj : j < Lng (diagSeq u v)) :
    entry (diagSeq u v) i j = u + j := by
  have hget : (diagSeq u v)[j]? = some (u + j, u + j) := by
    rw [List.getElem?_eq_getElem hj]
    congr 1
    simp [diagSeq, List.getElem_map, List.getElem_range']
  simp [entry, hget]

private theorem multiT_diagSeq_false (u v : ℕ) (huv : u ≤ v) :
    multiT (diagSeq u v) = false := by
  let M := diagSeq u v
  have hM : TPS M := by
    apply List.ne_nil_of_length_pos
    simp [M, diagSeq]
    omega
  apply (multi_criterion_12 M hM).mpr
  intro j hjpos hjL
  rw [entry_diagSeq_rank u v 0 0 (by simpa [M] using List.length_pos_of_ne_nil hM),
    entry_diagSeq_rank u v 0 j (by simpa [M] using hjL)]
  omega

/-- The fixed-rank hierarchy is monotone in its rank. -/
theorem SkTPS_mono (k : ℕ) (M : PS) (hM : SkTPS k M) : SkTPS (k + 1) M := by
  induction k generalizing M with
  | zero =>
      rcases hM with ⟨u, v, rfl, huv⟩
      let N := diagSeq u (v + 1)
      have hN : SkTPS 0 N := ⟨u, v + 1, rfl, by omega⟩
      have hNT : TPS N := SkTPS_TPS 0 N hN
      have hlen : 1 < Lng N := by simp [N, diagSeq]; omega
      have hpred : Pred N = diagSeq u v := Pred_diagSeq_succ u v huv
      refine ⟨N, 1, ?_, hN, by omega⟩
      rw [← pred_is_oper1 N hNT hlen]
      exact hpred.symm
  | succ k ih =>
      rcases hM with ⟨N, n, rfl, hN, hn⟩
      exact ⟨N, n, rfl, ih N hN, hn⟩

private theorem P_member_TPS_rank (M Q : PS) (hM : TPS M)
    (hQ : Q ∈ P M) : TPS Q := by
  obtain ⟨J, hJ, hget⟩ := List.mem_iff_getElem.mp hQ
  have hpos := P_component_nonempty M J hM hJ
  have heq : (P M).getD J [] = Q := by
    rw [getD_eq_getElem_idx (P M) [] hJ]
    exact hget
  rw [heq] at hpos
  exact List.ne_nil_of_length_pos hpos

private theorem P_getLastD_mem (M : PS) : (P M).getLastD [] ∈ P M := by
  have hne := P_nonempty M
  cases hPM : P M with
  | nil => exact (hne hPM).elim
  | cons A Q =>
      simp [List.getLastD]

/-- Every principal component of a rank-`k` standard sequence has rank `k`. -/
theorem SkTPS_P_component (k : ℕ) (M Q : PS) (hM : SkTPS k M)
    (hQ : Q ∈ P M) : SkTPS k Q := by
  induction k generalizing M Q with
  | zero =>
      rcases hM with ⟨u, v, rfl, huv⟩
      have hP : P (diagSeq u v) = [diagSeq u v] :=
        P_nonmulti_eq (diagSeq u v) (multiT_diagSeq_false u v huv)
      have hQeq : Q = diagSeq u v := by simpa [hP] using hQ
      rw [hQeq]
      exact ⟨u, v, rfl, huv⟩
  | succ k outer =>
      generalize hlenEq : Lng M = L
      induction L using Nat.strong_induction_on generalizing M Q with
      | h L inner =>
          rcases hM with ⟨N, n, hMN, hN, hn⟩
          subst M
          have hNT : TPS N := SkTPS_TPS k N hN
          by_cases hmulti : multiT N = true
          · have hNlen : 1 < Lng N := multi_length_fseq N hNT hmulti
            have hPlen : 1 < (P N).length :=
              (P_components_multi_iff N hNT).mp hmulti
            let D := (P N).getLastD []
            have hDmem : D ∈ P N := P_getLastD_mem N
            have hDT : TPS D := P_member_TPS_rank N D hNT hDmem
            have hDpos : 0 < Lng D := List.length_pos_of_ne_nil hDT
            by_cases hDone : Lng D = 1
            · have hrel := P_fseq_1 N n hNT hn (by simpa [D] using hDone)
              have hP : P (oper N n) = (P N).dropLast := by
                simpa [show (P N).length ≠ 1 by omega] using hrel.2
              have hQPN : Q ∈ P N := by
                apply List.mem_of_mem_dropLast
                simpa [hP] using hQ
              exact SkTPS_mono k Q (outer N Q hN hQPN)
            · have hDgt : 1 < Lng D := by omega
              have hrel := P_fseq_2 N n hNT hn (by simpa [D] using hDgt)
              have hP : P (oper N n) =
                  (P N).dropLast ++ P (oper D n) := by
                simpa [D] using hrel.2
              have hsplit : oper N n =
                  (P N).dropLast.flatten ++ oper D n := by
                simpa [D] using hrel.1
              rcases List.mem_append.mp (by simpa [hP] using hQ) with hQlead | hQtail
              · have hQPN : Q ∈ P N := List.mem_of_mem_dropLast hQlead
                exact SkTPS_mono k Q (outer N Q hN hQPN)
              · have hDS : SkTPS k D := outer N D hN hDmem
                have hYS : SkTPS (k + 1) (oper D n) := ⟨D, n, rfl, hDS, hn⟩
                have hcpos : 0 < Pcut N := (Pcut_props N hNlen).1
                have hcle : Pcut N ≤ Lng N := by
                  have := (Pcut_props N hNlen).2.1
                  omega
                have hlead : 0 < Lng (P N).dropLast.flatten := by
                  rw [(P_last_multi N hmulti hNlen).2, P_concat]
                  simp [Nat.min_eq_left hcle, hcpos]
                have hshort : Lng (oper D n) < L := by
                  calc
                    Lng (oper D n) <
                        Lng (P N).dropLast.flatten + Lng (oper D n) := by omega
                    _ = Lng ((P N).dropLast.flatten ++ oper D n) := by simp
                    _ = Lng (oper N n) := congrArg Lng hsplit.symm
                    _ = L := hlenEq
                exact inner (Lng (oper D n)) hshort (oper D n) Q hYS hQtail rfl
          · have hnonmulti : multiT N = false := Bool.eq_false_of_not_eq_true hmulti
            by_cases hcond :
                nextR N 0 0 (Lng N - 1) = true ∧
                  entry N 1 (Lng N - 1) = 0
            · have hP := nonmulti_fseq_1 N n hNT hn hnonmulti hcond.1 hcond.2
              have hQpred : Q = Pred N := by
                have : Q ∈ List.replicate n (Pred N) := by simpa [hP] using hQ
                have hh : n ≠ 0 ∧ Q = Pred N := by simpa using this
                exact hh.2
              subst Q
              by_cases hNgt : 1 < Lng N
              · exact ⟨N, 1, pred_is_oper1 N hNT hNgt, hN, by omega⟩
              · have hpred : Pred N = N := by
                  simp [Pred, Nat.le_of_not_gt hNgt]
                rw [hpred]
                exact SkTPS_mono k N hN
            · have hcond₂ : nextR N 0 0 (Lng N - 1) = false ∨
                  0 < entry N 1 (Lng N - 1) := by
                cases hnxt : nextR N 0 0 (Lng N - 1) with
                | false => exact Or.inl rfl
                | true =>
                    right
                    by_contra hz
                    have hz' : entry N 1 (Lng N - 1) = 0 := by omega
                    exact hcond ⟨hnxt, hz'⟩
              have hP := nonmulti_fseq_2 N n hNT hn hnonmulti hcond₂
              have hQeq : Q = oper N n := by simpa [hP] using hQ
              subst Q
              exact ⟨N, n, rfl, hN, hn⟩

/-- Indexed form of `SkTPS_P_component`. -/
theorem SkTPS_P_components (k : ℕ) (M : PS) (hM : SkTPS k M) :
    ∀ J < (P M).length, SkTPS k ((P M).getD J []) := by
  intro J hJ
  apply SkTPS_P_component k M ((P M).getD J []) hM
  rw [getD_eq_getElem_idx (P M) [] hJ]
  exact List.getElem_mem hJ

#print axioms SkTPS_STPS
#print axioms SkTPS_TPS
#print axioms SkTPS_mono
#print axioms SkTPS_P_component
#print axioms SkTPS_P_components

end PSS

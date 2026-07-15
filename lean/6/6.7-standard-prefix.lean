import PSS.Standard
import «5».«5.3-pred-is-oper1»
import «6».«6.2-P-fseq»
import «6».«6.3-adm-slice»

/-!
# §6.7 命題（標準形の始切片への遺伝性）

- Isabelle: `m_6_7_standard_prefix`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- Every standard sequence is a nonempty pair sequence. -/
theorem STPS_TPS (M : PS) (hM : STPS M) : TPS M := by
  induction hM with
  | diag u v huv =>
      apply List.ne_nil_of_length_pos
      simp [diagSeq]
      omega
  | oper hST n hn ih =>
      rename_i M
      by_cases hlen : 1 < Lng M
      · exact oper_nonempty_fseq M n ih hlen hn
      · have hpos : 0 < Lng M := List.length_pos_of_ne_nil ih
        have hL : Lng M = 1 := by omega
        simpa [oper, hL] using ih

private theorem seg_zero_eq_take (M : PS) (j : ℕ) (hj : j < Lng M) :
    seg M 0 j = M.take (j + 1) := by
  simpa using seg_eq_take_drop_adm M 0 j (Nat.zero_le _) hj

/-- Standardness is inherited by every nonempty initial segment. -/
theorem STPS_prefix (M : PS) (j : ℕ) (hST : STPS M)
    (hj : j ≤ Lng M - 1) : STPS (seg M 0 j) := by
  generalize hd : Lng M - 1 - j = d
  induction d using Nat.strong_induction_on generalizing M j with
  | h d ih =>
      have hM := STPS_TPS M hST
      have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      have hjL : j < Lng M := by omega
      by_cases hjlast : j = Lng M - 1
      · have hseg : seg M 0 j = M := by
          rw [seg_zero_eq_take M j hjL, hjlast]
          have : Lng M - 1 + 1 = Lng M := by omega
          rw [this, List.take_length]
        simpa [hseg] using hST
      · have hjlt : j < Lng M - 1 := by omega
        have hlen : 1 < Lng M := by omega
        have hpred : Pred M = oper M 1 := pred_is_oper1 M hM hlen
        have hSTP : STPS (Pred M) := by
          rw [hpred]
          exact STPS.oper hST 1 (by omega)
        have hpredTake : Pred M = M.take (Lng M - 1) := by
          simp [Pred, Nat.not_le_of_lt hlen, List.dropLast_eq_take]
        have hPL : Lng (Pred M) = Lng M - 1 := by
          rw [hpredTake]
          simp [Nat.min_eq_left (by omega)]
        have hjP : j ≤ Lng (Pred M) - 1 := by rw [hPL]; omega
        have hdlt : Lng (Pred M) - 1 - j < d := by
          rw [hPL]
          omega
        have hrec := ih (Lng (Pred M) - 1 - j) hdlt
          (Pred M) j hSTP hjP (by rfl)
        have hjPL : j < Lng (Pred M) := by rw [hPL]; omega
        have hseg : seg (Pred M) 0 j = seg M 0 j := by
          rw [seg_zero_eq_take (Pred M) j hjPL,
            seg_zero_eq_take M j hjL, hpredTake]
          simp only [List.take_take]
          congr 1
          omega
        simpa [hseg] using hrec

#print axioms STPS_TPS
#print axioms STPS_prefix

end PSS

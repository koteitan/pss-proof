import «6».«6.5-Red-Pred-commute»
import «6».«6.2-P-additivity»
import «6».«6.3-adm-slice»

/-!
# §6.6 命題（簡約性の切片への遺伝性）

- 原文: `isabelle/pss_paper.thy` の `p_6_6_reduced_slice`
- 訂正: A5（始点条件を `j₀ ≤ TrMax M` から `j₀ = 0` へ強化）
- Isabelle: `herd_6_6_reduced_slice`
- 依存: `6.5-Red-Pred-commute`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem iterate_Pred_take (M : PS) (k : ℕ) (hk : k < Lng M) :
    (Pred^[k]) M = M.take (Lng M - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k < Lng M := by omega
      have hrem : 1 < Lng M - k := by omega
      rw [Function.iterate_succ_apply', ih hk']
      have htakeLen : Lng (M.take (Lng M - k)) = Lng M - k := by
        simp
      rw [Pred_eq_take _ (by simpa [htakeLen] using hrem)]
      simp only [htakeLen, List.take_take]
      congr 1
      omega

private theorem RTPS_iterate_Pred (M : PS) (k : ℕ) (hM : RTPS M) :
    RTPS ((Pred^[k]) M) := by
  induction k with
  | zero => simpa using hM
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact RTPS_Pred _ ih

/-- A reduced pair sequence has reduced trunk-anchored initial slices.

The lower trunk bound is retained from the article's statement, although the
proof via repeated `Pred` establishes the stronger fact for every nonempty
initial slice. -/
theorem RTPS_slice (M : PS) (j₀ j₁ : ℕ) (hM : RTPS M)
    (hj₀ : j₀ = 0) (_htr : TrMax M ≤ j₁)
    (hj₁ : j₁ ≤ Lng M - 1) : RTPS (seg M j₀ j₁) := by
  have hh := hM
  simp only [RTPS, reduced, Bool.and_eq_true, beq_iff_eq] at hh
  have hMT : TPS M := by simpa [TPS] using hh.1
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hMT
  let k := Lng M - 1 - j₁
  have hk : k < Lng M := by dsimp [k]; omega
  have hremain : Lng M - k = j₁ + 1 := by dsimp [k]; omega
  have hj₁L : j₁ < Lng M := by omega
  have htakeSeg : M.take (j₁ + 1) = seg M 0 j₁ := by
    simpa using (seg_eq_take_drop_adm M 0 j₁ (Nat.zero_le _) hj₁L).symm
  have heq : (Pred^[k]) M = seg M j₀ j₁ := by
    rw [iterate_Pred_take M k hk, hremain, htakeSeg, hj₀]
  rw [← heq]
  exact RTPS_iterate_Pred M k hM

#print axioms RTPS_slice

end PSS

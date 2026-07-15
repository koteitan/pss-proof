import «6».«6.5-Red-idempotence»

/-!
# §6.6 `RT_PS` と `Red` の像の関係

- 原文: `tmp/content.md` の簡約性の定義直後の注
- 訂正: A41（等号は偽。成立するのは `RT_PS ⊆ Im(Red)` のみ）
- 依存: §6.5 `Red` の冪等性（訂正版）
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- `Red` を `T_PS` に制限した像。Isabelle の部分関数としての
`Im(Red)` に対応する。 -/
def RedImage (N : PS) : Prop := ∃ M, TPS M ∧ Red M = N

/-- 訂正 A41: 簡約形は `Red` の像に含まれる。 -/
theorem RTPS_subset_RedImage (N : PS) (hN : RTPS N) : RedImage N := by
  refine ⟨N, ?_, Red_eq_self_of_RTPS N hN⟩
  have h := hN
  simp only [RTPS, reduced, Bool.and_eq_true, beq_iff_eq] at h
  simpa [TPS] using h.1

/-- A41 で削除された逆包含は偽である。 -/
theorem RedImage_not_subset_RTPS :
    ∃ N : PS, RedImage N ∧ ¬ RTPS N := by
  let M : PS := [(0, 0), (0, 2)]
  let N : PS := [(0, 0), (2, 2)]
  refine ⟨N, ?_, ?_⟩
  · refine ⟨M, ?_, ?_⟩
    · simp [M, TPS]
    · decide
  · decide

#print axioms RTPS_subset_RedImage
#print axioms RedImage_not_subset_RTPS

end PSS

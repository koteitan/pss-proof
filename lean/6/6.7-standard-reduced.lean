import PSS.Standard
import «6».«6.6-reduced-fseq»

/-!
# §6.7 命題（標準形の簡約性）

- 原文: `tmp/content.md` の「命題（標準形の簡約性）」
- 訂正: なし
- Isabelle: `m_6_7_ST_PS_subseteq_RT_PS`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem diagSeq_succ_snoc_sr (u v : ℕ) (huv : u ≤ v) :
    diagSeq u (v + 1) = diagSeq u v ++ [(v + 1, v + 1)] := by
  have hrange :
      List.range' u (v + 1 + 1 - u) =
        List.range' u (v + 1 - u) ++ [v + 1] := by
    calc
      List.range' u (v + 1 + 1 - u) =
          List.range' u ((v + 1 - u) + 1) := by
        congr 1
        omega
      _ = List.range' u (v + 1 - u) ++
          List.range' (u + (v + 1 - u)) 1 :=
        List.range'_append_1.symm
      _ = List.range' u (v + 1 - u) ++ [v + 1] := by
        rw [Nat.add_sub_of_le (by omega : u ≤ v + 1)]
        simp
  simp [diagSeq, hrange]

private theorem RTPS_diagSeq_sr (u v : ℕ) (huv : u ≤ v) :
    RTPS (diagSeq u v) := by
  by_cases hv : v = 0
  · subst v
    have hu : u = 0 := by omega
    subst u
    simpa [diagSeq] using RTPS_diagSeq_zero 0
  have hsingleT : TPS [(v, v)] := by simp [TPS]
  have hsingleR : RTPS [(v, v)] :=
    ((one_column [(v, v)] hsingleT).2 ⟨v, rfl⟩).2
  have hz : zeroT [(v, v)] = false := by
    simp [zeroT, entry, hv]
  have hsingleMono : monoT [(v, v)] = true := by
    simp [monoT, hz, leR, le0, le0Aux]
  have hp := RTPS_diag_prefix [(v, v)] u hsingleR hsingleMono huv
  by_cases huvlt : u < v
  · have heq : diagSeq u v = diagSeq u (v - 1) ++ [(v, v)] := by
      have hs := diagSeq_succ_snoc_sr u (v - 1) (by omega)
      have hv' : v - 1 + 1 = v := by omega
      simpa only [hv'] using hs
    simpa [entry, huvlt, ← heq] using hp.1
  · have huvEq : u = v := by omega
    subst u
    simpa [diagSeq, entry] using hsingleR

/-- Every standard pair sequence is reduced. -/
theorem STPS_RTPS (M : PS) (hM : STPS M) : RTPS M := by
  induction hM with
  | diag u v huv => exact RTPS_diagSeq_sr u v huv
  | oper hST n hn ih =>
      rename_i M
      exact RTPS_oper M n ih hn

#print axioms STPS_RTPS

end PSS

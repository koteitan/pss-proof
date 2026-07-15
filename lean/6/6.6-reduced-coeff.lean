import «6».«6.6-reduced-iff-condAB»
import «6».«6.6-condAB-coeff»

/-!
# §6.6 補題（簡約性と係数の基本性質）

- 原文: `tmp/content.md` の「補題（簡約性と係数の基本性質）」
- 訂正: なし
- Isabelle: `m_6_6_reduced_coeff`
- 依存: §6.6 `RTPS_iff_condAB`, §5.1 `parent_exists_2`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- In a reduced pair sequence, the row-zero coefficient dominates the
row-one coefficient at every column. -/
theorem reduced_coeff (M : PS) (hR : RTPS M) (j : ℕ)
    (hj : j < Lng M) : entry M 1 j ≤ entry M 0 j := by
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hA, hB⟩ := RTPS_condAB M hR
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hp1 : hasParent M 1 j = true
      · let p := parent M 1 j
        have hpj : p < j := by
          simpa [p] using parent_lt_of_hasParent M 1 j hp1
        have hpL : p < Lng M := hpj.trans hj
        have hprev := ih p hpj hpL
        have hstep := RedCondA_apply M hA 1 j (by omega) hj hp1
        change entry M 1 p + 1 = entry M 1 j at hstep
        have hnext := hasParent_next_fseq M 1 j hp1
        have hanc : leR M 0 p j = true := by
          simpa [p] using (nextR_implies_row0 M 1 (parent M 1 j) j hnext).2
        have hgrowth := ancestor_basic_1 M p j j hM hpj (le_refl _) hanc
        omega
      · have hp1' : hasParent M 1 j = false :=
          Bool.eq_false_of_not_eq_true hp1
        by_cases hp0 : hasParent M 0 j = true
        · let p := parent M 0 j
          have hpj : p < j := by
            simpa [p] using parent_lt_of_hasParent M 0 j hp0
          have hpL : p < Lng M := hpj.trans hj
          have hnext := hasParent_next_fseq M 0 j hp0
          have hanc : leR M 0 p j = true := by
            simpa [p] using (nextR_implies_row0 M 0 (parent M 0 j) j hnext).2
          have hrow1 : entry M 1 j ≤ entry M 1 p := by
            by_contra hnot
            have hlt : entry M 1 p < entry M 1 j := by omega
            obtain ⟨q, _hpq, _hqj, hq⟩ :=
              parent_exists_2 M p j hM hpj hj hlt hanc
            have hhas : hasParent M 1 j = true :=
              (hasParent_iff_unique_fseq M 1 j).mpr
                ⟨q, hq, fun r hr => nextR1_unique_mr M r q j hr hq⟩
            rw [hp1'] at hhas
            contradiction
          have hprev := ih p hpj hpL
          have hgrowth := ancestor_basic_1 M p j j hM hpj (le_refl _) hanc
          omega
        · have hp0' : hasParent M 0 j = false :=
            Bool.eq_false_of_not_eq_true hp0
          have heq := RedCondB_apply M hM hB j hj hp0'
          omega

#print axioms reduced_coeff

end PSS

import «7».«7.4-Mark-Trans-repr»
import «7».«7.3-Trans-preserves-zeroT»

/-!
# §8.1 part (4) 前剥がしコアエンジン（front-peel）

- 原文: `tmp/content.md` 2923 付近（補題「条件(I)か(III)の下での `c₁` 前後の
  具体表示」part (4-1)(4-2) の基盤）
- 訂正: なし
- Isabelle: `Trans_front_peel` (isabelle/layerB/pss_wip.thy:18435)、
  `Mark_rightmost_adjacent_peel` (同 18558)
- 依存: «7».«7.4-Mark-Trans-repr»（`Mark_Trans_repr`, `Mark_zero_eq_Trans`、
  経由で `Mark_nest_common_marked` / `two_column_Trans` /
  `ancestor_slice_Red_IncrFirst` / `Mark_rightmost1_forward` /
  `scb_unique_decomp_unconditional` / `scb_compose_dprin` / `flatBT_injective`）、
  «7».«7.3-Trans-preserves-zeroT»
- 状態: ✅ 証明済（sorry 0）

part (3-1) の gap-peel エンジン（`Mark_gap_*_gp`、8.1-condI-III-c1-around 内
private）の隣接版。`Mark_rightmost_adjacent_peel` は右端隣接対 `k, k+1` の剥がし
（`Mark_Trans_repr` で値化 → `ancestor_slice_Red_IncrFirst` の Red 切片は 2 列
→ `two_column_Trans`）。`Trans_front_peel` は左端隣接対 `0, 1` の剥がしで、
`Lng` 強帰納 ＋ `Mark_nest_common_marked` の共通 scb 位置転送。Isabelle の
TransAux 手展開は `Mark_zero_eq_Trans` により不要。
-/

namespace PSS

/-! ## 私的補助（`IncrFirstN` は行 1 の entry を変えない） -/

private theorem entry_IncrFirstN_one_fp (n : ℕ) (M : PS) (j : ℕ)
    (hj : j < Lng M) :
    entry (IncrFirstN n M) 1 j = entry M 1 j := by
  rw [IncrFirstN_eq_map]
  simp [entry, List.getElem?_eq_getElem hj]

/-! ## 右端隣接剥がし（Isabelle `Mark_rightmost_adjacent_peel`, layerB:18558）

`k, k+1` が両方基点で `k+1` が右端のとき、
`Mark Q k = D_{Q₁,k} (Mark Q (k+1))`。`Mark_Trans_repr` で
`Mark Q k = Trans (seg Q k (Lng Q - 1))` と値化し、切片の `Red` は 2 列
（`ancestor_slice_Red_IncrFirst`）なので `two_column_Trans` が閉形式を与える。
行 1 の entry は `IncrFirstN` 不変量で `Q` へ読み戻す。 -/

theorem Mark_rightmost_adjacent_peel (Q : PS) (k : ℕ)
    (hQR : RTPS Q) (hmk : Marked Q k) (_hmk1 : Marked Q (k + 1))
    (hkj1 : k + 1 = Lng Q - 1) (hL : 1 < Lng Q) :
    Mark Q k = Dprin (entry Q 1 k : ℕ∞) (Mark Q (k + 1)) := by
  have hab : k < Lng Q - 1 := by omega
  have hzQ : zeroT Q = false := by
    rw [Bool.eq_false_iff]
    intro h
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at h
    omega
  have hmarkb : Mark Q (Lng Q - 1)
      = Dprin (entry Q 1 (Lng Q - 1) : ℕ∞) BZero :=
    Mark_rightmost1_forward Q hQR hzQ
  have hmk1' : Mark Q (k + 1) = Dprin (entry Q 1 (k + 1) : ℕ∞) BZero := by
    rw [hkj1]
    exact hmarkb
  have hrepr : Mark Q k = Trans (seg Q k (Lng Q - 1)) :=
    Mark_Trans_repr Q k hmk hQR hab
  have hleMa : leR Q 0 k (Lng Q - 1) = true := hmk.2.2
  have hfacts := ancestor_slice_Red_IncrFirst Q k (Lng Q - 1) hQR hab
    (le_refl _) hleMa
  have hRedN : Red (Red (seg Q k (Lng Q - 1))) = Red (seg Q k (Lng Q - 1)) :=
    hfacts.1
  have hmonoN : monoT (Red (seg Q k (Lng Q - 1))) = true := hfacts.2.1
  have hIF : seg Q k (Lng Q - 1)
      = IncrFirstN (entry Q 0 k - entry Q 1 k) (Red (seg Q k (Lng Q - 1))) :=
    hfacts.2.2
  have hLS : Lng (seg Q k (Lng Q - 1)) = 2 := by
    simp only [length_seg]
    omega
  have hLN : Lng (Red (seg Q k (Lng Q - 1))) = 2 := by
    have h1 : Lng (IncrFirstN (entry Q 0 k - entry Q 1 k)
        (Red (seg Q k (Lng Q - 1))))
        = Lng (Red (seg Q k (Lng Q - 1))) := by
      simp [IncrFirstN_eq_map]
    have h2 := congrArg Lng hIF
    rw [h1] at h2
    omega
  have hNT : TPS (Red (seg Q k (Lng Q - 1))) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (Red (seg Q k (Lng Q - 1)))
    omega
  have hNR : RTPS (Red (seg Q k (Lng Q - 1))) := by
    show reduced (Red (seg Q k (Lng Q - 1))) = true
    have hne : Red (seg Q k (Lng Q - 1)) ≠ [] := hNT
    simp [reduced, hne, hRedN]
  have hSTrans : Trans (seg Q k (Lng Q - 1))
      = Trans (Red (seg Q k (Lng Q - 1))) := by
    apply Trans_Red
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg Q k (Lng Q - 1))
    omega
  -- 2 列閉形式
  have htower : Trans (Red (seg Q k (Lng Q - 1)))
      = Dprin (entry (Red (seg Q k (Lng Q - 1))) 1 0 : ℕ∞)
          (Dprin (entry (Red (seg Q k (Lng Q - 1))) 1 1 : ℕ∞) BZero) :=
    two_column_Trans (Red (seg Q k (Lng Q - 1))) hNR hmonoN hLN
  -- 行 1 entry の読み戻し
  have hIF1 : ∀ j, j < Lng (Red (seg Q k (Lng Q - 1))) →
      entry (seg Q k (Lng Q - 1)) 1 j
      = entry (Red (seg Q k (Lng Q - 1))) 1 j := by
    intro j hj
    conv_lhs => rw [hIF]
    exact entry_IncrFirstN_one_fp _ _ j hj
  have he0 : entry (Red (seg Q k (Lng Q - 1))) 1 0 = entry Q 1 k := by
    have h1 := hIF1 0 (by omega)
    have h2 : entry (seg Q k (Lng Q - 1)) 1 0 = entry Q 1 (k + 0) :=
      entry_seg Q k (Lng Q - 1) 1 0 (by omega)
    rw [← h1, h2]
    simp
  have he1 : entry (Red (seg Q k (Lng Q - 1))) 1 1 = entry Q 1 (k + 1) := by
    have h1 := hIF1 1 (by omega)
    have h2 : entry (seg Q k (Lng Q - 1)) 1 1 = entry Q 1 (k + 1) :=
      entry_seg Q k (Lng Q - 1) 1 1 (by omega)
    rw [← h1, h2]
  rw [hrepr, hSTrans, htower, he0, he1, ← hmk1']

/-! ## 前剥がし（Isabelle `Trans_front_peel`, layerB:18435）

`0, 1` が両方基点のとき `Trans S = D_{S₁,₀} (Mark S 1)`。`Lng` 強帰納。
base（`Lng S = 2`）は右端隣接剥がし ＋ `Mark_zero_eq_Trans`。step は
`Pred S` 上の IH を `Mark_nest_common_marked`（`m = 0`, `m' = 1`）の共通
scb 位置 `([D_{S₁,₀}], [])` で `S` へ転送し、`flatBT_injective` で値化。 -/

private theorem Trans_front_peel_aux_fp : ∀ (n : ℕ) (S : PS), Lng S ≤ n →
    RTPS S → Marked S 0 → Marked S 1 →
    Trans S = Dprin (entry S 1 0 : ℕ∞) (Mark S 1)
  | 0, S, hn, hR, _, _ => by
      have hST : TPS S := RTPS_TPS S hR
      have hpos : 0 < Lng S := List.length_pos_of_ne_nil hST
      exact absurd (Nat.lt_of_lt_of_le hpos hn) (lt_irrefl 0)
  | n + 1, S, hn, hR, hm0, hm1 => by
      have hST : TPS S := RTPS_TPS S hR
      -- `Marked S 1` は `1 < Lng S` を強制する
      have hle1 : le0 S 1 (Lng S - 1) = true := by
        have h := hm1.2.2
        simpa [leR] using h
      have hL1 : 1 < Lng S := by
        have hh := hle1
        simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
        exact hh.1.1
      by_cases hL2 : Lng S = 2
      · -- base: `k = 0` の右端隣接剥がし
        have hpeel := Mark_rightmost_adjacent_peel S 0 hR hm0 hm1
          (by omega) hL1
        have hmark0 : Mark S 0 = Trans S := Mark_zero_eq_Trans S hR hm0
        rw [← hmark0]
        simpa using hpeel
      · have hL3 : 2 < Lng S := by omega
        -- `Pred S` の基本事実
        have hpredRT : RTPS (Pred S) := RTPS_Pred S hR
        have hPredEq : Pred S = S.take (Lng S - 1) := Pred_eq_take S hL1
        have hPredL : Lng (Pred S) = Lng S - 1 := by
          rw [hPredEq]
          simp
        have hPredT : TPS (Pred S) := by
          apply List.ne_nil_of_length_pos
          change 0 < Lng (Pred S)
          omega
        have hmP0 : Marked (Pred S) 0 :=
          Marked_Pred S 0 hST hL1 hm0 (by omega)
        have hmP1 : Marked (Pred S) 1 :=
          Marked_Pred S 1 hST hL1 hm1 (by omega)
        -- 行 1 左端 entry は `butlast` で不変
        have he10 : entry (Pred S) 1 0 = entry S 1 0 := by
          rw [hPredEq]
          exact entry_take S (Lng S - 1) 1 0 (by omega)
        -- IH on `Pred S`
        have hIH : Trans (Pred S)
            = Dprin (entry S 1 0 : ℕ∞) (Mark (Pred S) 1) := by
          have h := Trans_front_peel_aux_fp n (Pred S) (by omega)
            hpredRT hmP0 hmP1
          rwa [he10] at h
        -- `Mark _ 0 = Trans _` on both `Pred S` and `S`
        have hmarkP0 : Mark (Pred S) 0 = Trans (Pred S) :=
          Mark_zero_eq_Trans (Pred S) hpredRT hmP0
        have hmarkS0 : Mark S 0 = Trans S := Mark_zero_eq_Trans S hR hm0
        -- `Mark (Pred S) 1` は principal
        have hprinP : ∃ p, Mark (Pred S) 1 = .trm [p] := by
          have hTransNe : Trans (Pred S) ≠ BZero := by
            intro hzero
            have hz : zeroT (Pred S) = true :=
              (Trans_preserves_zeroT (Pred S) hPredT).2 hzero
            simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
            omega
          exact marked_component_principal hTransNe
            (Trans_Mark_mem_MarkedB (Pred S) 1 hpredRT hmP1)
        obtain ⟨p, hp⟩ := hprinP
        have hPTB : isPTB_str (flatBT (Mark (Pred S) 1)) := by
          rw [hp]
          have hTB : Mark (Pred S) 1 ∈ T_B :=
            Mark_mem_T_B (Pred S) 1 hpredRT hmP1
          rw [hp] at hTB
          exact (principal_flat_properties hTB ⟨p, rfl⟩).1
        have hself : scb_decomp (Mark (Pred S) 1) []
            (flatBT (Mark (Pred S) 1)) [] :=
          ⟨by simp, fun _ => hPTB, by simp⟩
        -- `Pred S` 側の scb 位置は `([D_{S₁,₀}], [])`
        have hdP : scb_decomp (Mark (Pred S) 0) [.dsym (entry S 1 0 : ℕ∞)]
            (flatBT (Mark (Pred S) 1)) [] := by
          have hlift := scb_compose_dprin (entry S 1 0 : ℕ∞)
            (Mark (Pred S) 1) [] (flatBT (Mark (Pred S) 1)) [] hself hPTB
          have hrel : Mark (Pred S) 0
              = Dprin (entry S 1 0 : ℕ∞) (Mark (Pred S) 1) :=
            hmarkP0.trans hIH
          rwa [← hrel] at hlift
        -- 共通 scb 位置で `S` に転送
        obtain ⟨sb, ⟨hsbP, hsbS⟩, _⟩ :=
          Mark_nest_common_marked S 0 1 hR hm0 hm1 (by omega) (by omega)
        have hsbeq := scb_unique_decomp_unconditional (Mark (Pred S) 0) sb.1
          [.dsym (entry S 1 0 : ℕ∞)] (flatBT (Mark (Pred S) 1)) sb.2 []
          hsbP hdP
        have hdS : scb_decomp (Mark S 0) [.dsym (entry S 1 0 : ℕ∞)]
            (flatBT (Mark S 1)) [] := by
          rw [← hsbeq.1, ← hsbeq.2]
          exact hsbS
        have hflat : flatBT (Mark S 0)
            = flatBT (Dprin (entry S 1 0 : ℕ∞) (Mark S 1)) := by
          have h1 := hdS.1
          have h2 : flatBT (Dprin (entry S 1 0 : ℕ∞) (Mark S 1))
              = .dsym (entry S 1 0 : ℕ∞) :: flatBT (Mark S 1) := rfl
          rw [h2, h1]
          simp
        have hval := flatBT_injective hflat
        rw [← hmarkS0]
        exact hval

/-- 前剥がしエンジン（Isabelle `Trans_front_peel`）: 簡約 `S` の左端 2 列
`0, 1` が両方基点なら、`Trans S` は左端列を剥がして
`Trans S = D_{S₁,₀} (Mark S 1)`。 -/
theorem Trans_front_peel (S : PS) (hR : RTPS S)
    (hm0 : Marked S 0) (hm1 : Marked S 1) :
    Trans S = Dprin (entry S 1 0 : ℕ∞) (Mark S 1) :=
  Trans_front_peel_aux_fp (Lng S) S (le_refl _) hR hm0 hm1

#print axioms Trans_front_peel
#print axioms Mark_rightmost_adjacent_peel

end PSS

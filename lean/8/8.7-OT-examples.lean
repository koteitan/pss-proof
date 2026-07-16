import PSS.Buchholz

/-!
# §8.7 補題（順序数項の基本例）

- 原文: `tmp/content.md` L6066 付近（「補題（順序数項の基本例）」）
- 訂正: なし
- Isabelle: `p_8_7_OT_examples` (isabelle/pss_paper.thy:2307) の証明は
            `m_8_7_OT_examples` (isabelle/pss_mechanized.thy:24537)
- 依存: PSS.Buchholz
- 状態: ✅ 証明済（sorry 0）

`OT_B` の基本例 4 本: (1) `D_u 0`、(2) `D_u (D_v 0)`、(3) `(D_u 0) ×_B (n-1)`、
(4) 塔 `D_u^n 0`。(4) は Isabelle と同じく「塔の `G_u` は下の塔全体」＋「塔の狭義単調性」
の同時帰納で閉じる（`m < n → D_u^m 0 <_B D_u^n 0`）。
-/

namespace PSS

/-! ## 補助: 有限指標・反射律 -/

private theorem coe_ne_top_ot (u : ℕ) : ((u : ℕ∞)) ≠ ⊤ := by simp

private theorem leBT_refl_ot (a : BT) : leBT a a = true := by
  simp [leBT]

/-! ## 補助: 塔 `D_u^n 0` -/

/-- 塔 `D_u^n 0`（`n` 段）。 -/
private def tower (u : ℕ) : ℕ → BT
  | 0 => BZero
  | n + 1 => Dprin (u : ℕ∞) (tower u n)

private theorem iterate_tower_ot (u : ℕ) : ∀ n, (Dprin (u : ℕ∞))^[n] BZero = tower u n
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply', iterate_tower_ot u n]
      rfl

private theorem dfree_tower_ot (u : ℕ) : ∀ n, dfree_BT (tower u n) = true
  | 0 => rfl
  | n + 1 => by
      simp [tower, Dprin, dfree_BT, dfree_BPList, dfree_BP,
        coe_ne_top_ot u, dfree_tower_ot u n]

/-- 塔 1 段の `gather` 展開: `G_u (D_u^{n+1} 0)` は `D_u^n 0` とその下。 -/
private theorem gather_tower_succ_ot (u : ℕ) (n : ℕ) :
    gatherBT (u : ℕ∞) (tower u (n + 1))
      = tower u n :: gatherBT (u : ℕ∞) (tower u n) := by
  simp [tower, Dprin, gatherBT, gatherBPList, gatherBP]

/-- `G_u (D_u^n 0)` の元はすべて下の塔。 -/
private theorem gather_tower_mem_ot (u : ℕ) :
    ∀ n x, x ∈ gatherBT (u : ℕ∞) (tower u n) → ∃ m, m < n ∧ x = tower u m
  | 0, x, hx => by simp [tower, BZero, gatherBT, gatherBPList] at hx
  | n + 1, x, hx => by
      rw [gather_tower_succ_ot] at hx
      rcases List.mem_cons.mp hx with h | h
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · obtain ⟨m, hm, rfl⟩ := gather_tower_mem_ot u n x h
        exact ⟨m, Nat.lt_succ_of_lt hm, rfl⟩

private theorem lessBT_zero_Dprin_ot (v : ℕ∞) (a : BT) :
    lessBT BZero (Dprin v a) = true := by
  simp [BZero, Dprin, lessBT, lessBPList]

/-- 同一指標の principal 包みは `<_B` を保つ。 -/
private theorem lessBT_Dprin_mono_ot (v : ℕ∞) {a b : BT} (h : lessBT a b = true) :
    lessBT (Dprin v a) (Dprin v b) = true := by
  simp [Dprin, lessBT, lessBPList, lessBP, h]

/-- 塔の狭義単調性（content.md 6102–6106）: `m < n → D_u^m 0 <_B D_u^n 0`。 -/
private theorem tower_mono_ot (u : ℕ) : ∀ n m, m < n → lessBT (tower u m) (tower u n) = true
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _ => lessBT_zero_Dprin_ot (u : ℕ∞) (tower u n)
  | n + 1, m + 1, h => by
      have hk : m < n := Nat.succ_lt_succ_iff.mp h
      exact lessBT_Dprin_mono_ot (u : ℕ∞) (tower_mono_ot u n m hk)

/-- 塔は順序数項（content.md 6110–6118 の帰納）。 -/
private theorem isOT_tower_ot (u : ℕ) : ∀ n, isOT_BT (tower u n) = true
  | 0 => rfl
  | n + 1 => by
      have hall : (gatherBT (u : ℕ∞) (tower u n)).all
          (fun x => lessBT x (tower u n)) = true := by
        rw [List.all_eq_true]
        intro x hx
        obtain ⟨m, hm, rfl⟩ := gather_tower_mem_ot u n x hx
        exact tower_mono_ot u n m hm
      simp [tower, Dprin, isOT_BT, isOT_BPList, isOT_BP, descP,
        isOT_tower_ot u n, hall]

/-! ## 補助: `(D_u 0) ×_B m` は同一 principal の replicate -/

private theorem multBT_eq_replicate_ot (v : ℕ∞) :
    ∀ m, multBT (Dprin v BZero) m = .trm (List.replicate m (.db v BZero))
  | 0 => rfl
  | m + 1 => by
      show addBT (multBT (Dprin v BZero) m) (Dprin v BZero) = _
      rw [multBT_eq_replicate_ot v m]
      simp [addBT, Dprin, List.replicate_succ']

private theorem descP_replicate_ot (p : BP) : ∀ m, descP (List.replicate m p) = true
  | 0 => rfl
  | 1 => rfl
  | m + 2 => by
      have ih := descP_replicate_ot p (m + 1)
      simp only [List.replicate_succ, descP] at ih ⊢
      simp [leBT_refl_ot, ih]

private theorem isOT_BPList_replicate_ot (p : BP) (hp : isOT_BP p = true) :
    ∀ m, isOT_BPList (List.replicate m p) = true
  | 0 => rfl
  | m + 1 => by
      simp [List.replicate_succ, isOT_BPList, hp, isOT_BPList_replicate_ot p hp m]

private theorem dfree_BPList_replicate_ot (p : BP) (hp : dfree_BP p = true) :
    ∀ m, dfree_BPList (List.replicate m p) = true
  | 0 => rfl
  | m + 1 => by
      simp [List.replicate_succ, dfree_BPList, hp, dfree_BPList_replicate_ot p hp m]

private theorem isOT_BP_Du0_ot (u : ℕ) : isOT_BP (.db (u : ℕ∞) BZero) = true := by
  simp [isOT_BP, BZero, isOT_BT, isOT_BPList, descP, gatherBT, gatherBPList]

private theorem dfree_BP_Du0_ot (u : ℕ) : dfree_BP (.db (u : ℕ∞) BZero) = true := by
  simp [dfree_BP, BZero, dfree_BT, dfree_BPList, coe_ne_top_ot u]

/-! ## 主結果 (原文の 4 主張) -/

/-- (1) `D_u 0 ∈ OT_B`（content.md 6087）。 -/
theorem OT_examples_1 (u : ℕ) : Dprin (u : ℕ∞) BZero ∈ OT_B := by
  constructor
  · show isOT_BT _ = true
    simp [Dprin, BZero, isOT_BT, isOT_BPList, isOT_BP, descP,
      gatherBT, gatherBPList, gatherBP]
  · show dfree_BT _ = true
    simp [Dprin, BZero, dfree_BT, dfree_BPList, dfree_BP, coe_ne_top_ot u]

/-- (2) `D_u (D_v 0) ∈ OT_B`（content.md 6089–6098）。 -/
theorem OT_examples_2 (u v : ℕ) : Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) ∈ OT_B := by
  have h0 : lessBT BZero (Dprin (v : ℕ∞) BZero) = true :=
    lessBT_zero_Dprin_ot _ _
  constructor
  · show isOT_BT _ = true
    simp only [Dprin, isOT_BT, isOT_BPList, isOT_BP, descP, Bool.and_eq_true,
      List.all_eq_true, and_true]
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · intro x hx
      simp [BZero, gatherBT, gatherBPList] at hx
    · intro x hx
      simp only [BZero, gatherBT, gatherBPList, gatherBP, List.append_nil] at hx
      split at hx
      · rcases List.mem_cons.mp hx with rfl | h
        · simpa [Dprin, BZero] using h0
        · simp [gatherBT, gatherBPList] at h
      · simp at hx
  · show dfree_BT _ = true
    simp [Dprin, BZero, dfree_BT, dfree_BPList, dfree_BP,
      coe_ne_top_ot u, coe_ne_top_ot v]

/-- (3) `n ≥ 1 → (D_u 0) ×_B (n-1) ∈ OT_B`（content.md 6100）。 -/
theorem OT_examples_3 (u n : ℕ) (_hn : 1 ≤ n) :
    multBT (Dprin (u : ℕ∞) BZero) (n - 1) ∈ OT_B := by
  rw [multBT_eq_replicate_ot]
  constructor
  · show isOT_BT _ = true
    simp [isOT_BT,
      isOT_BPList_replicate_ot _ (isOT_BP_Du0_ot u),
      descP_replicate_ot]
  · show dfree_BT _ = true
    simp [dfree_BT, dfree_BPList_replicate_ot _ (dfree_BP_Du0_ot u)]

/-- (4) 塔 `D_u^n 0 ∈ OT_B`（content.md 6102–6120）。 -/
theorem OT_examples_4 (u n : ℕ) : (Dprin (u : ℕ∞))^[n] BZero ∈ OT_B := by
  rw [iterate_tower_ot]
  exact ⟨isOT_tower_ot u n, dfree_tower_ot u n⟩

/-! ## 回帰ベクトル -/

#guard isOT_BT (Dprin (3 : ℕ∞) BZero)
#guard dfree_BT (Dprin (0 : ℕ∞) (Dprin (5 : ℕ∞) BZero))
#guard isOT_BT (multBT (Dprin (2 : ℕ∞) BZero) 4)
#guard isOT_BT ((Dprin (2 : ℕ∞))^[3] BZero)
#guard lessBT ((Dprin (2 : ℕ∞))^[2] BZero) ((Dprin (2 : ℕ∞))^[3] BZero)

#print axioms OT_examples_1
#print axioms OT_examples_2
#print axioms OT_examples_3
#print axioms OT_examples_4

end PSS

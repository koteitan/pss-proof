import «8».«8.6-condVI-close»
import «8».«8.6-condVI-props»
import «8».«8.6-condVI-Ltower-facta»
import «8».«8.6-Trans-Red-funpow-IncrFirst»
import «8».«8.5-exchV-props»
import «8».«8.6-condVI-nadm-forms»
import «8».«8.4-s84x-vocab-run»
import «7».«7.3-Mark-rightmost2»
import «7».«7.3-two-column»

/-!
# §8.6 条件 (VI) 非許容 `j₀` L 塔閉形式 — `CondVIres_nadm_Ltower_v6p` の討伐

- 原文: 停止性定理 §8.6 条件 (VI) の `Trans`/基本列交換則（`tmp/content.md` 5484）の
  **非許容 `j₀`** 枝。残差 `CondVI_scbdec_nadm_forms_v6`（`8.6-condVI-close`:317）は
  `condVI_scbdec_nadm_forms_holds_v6p`（`8.6-condVI-props`:459）で
  **`CondVIres_nadm_Ltower_v6p`（`8.6-condVI-props`:421）1 本**に削減済み。本ファイルが
  その L 塔を閉じる（許容枝 `CondVIres_adm_Ltower_holds_af` の非許容双子）。
- Isabelle 対応（`isabelle/layerB/pss_wip.thy`）:
  * L 塔閉形式 = `c6zx_L_tower`（:72166）を、条件 (VI) 崩壊（`w = 1`）下で
    `oper M (n+1) = oper M n ++ [colₙ]` に還元して `trans_surgery_localized_v6p`＋
    `scb_unique_decomp_unconditional` で 1 段ずつ伸ばす（`m_8_4_oper_props_5` を迂回）。
  * 非許容の唯一の相違 = fact (c) `c6nx_t2eq`（:76619）＝ `transT2 M = D_{M_{1,j₀}} 0`。
    許容枝では `transC1 M = D_u 0` だが、非許容枝では外側の頭 `D_V`（`V = M_{1,j₋₁}`）が
    残り `transC1 M = D_V(D_u 0)`。この余分な `dsym V` を base scb 分解から s 側へ剥がす
    だけで、塔の帰納段は許容枝と完全に同一になる。
  * fact (c) = `c6nx_t2eq` を `m_7_3_Mark_rightmost2`（`7.3-Mark-rightmost2`、移植済）＋
    補助 `c6nx_predVI` / `c6nx_jm1eq`（本ファイルで移植）＋ corner 枝
    `two_column_Mark`（`7.3-two-column`）で完全に閉じる。
- 依存: 上記 8 import（推移的に §5.1/§6.5/§6.6/§7.3/§7.4/§8.4-L 塔クラスタ）。
- 状態: ✅ GREEN（sorry 0、公理は propext/Classical.choice/Quot.sound のみ）。
  private 補助は `_nc` 接尾辞。`_af`（許容枝）と同一の崩壊補助は逐語複製。
-/

namespace PSS

/-! ## 条件 (VI) の崩壊事実（`«8».«8.6-condVI-Ltower-facta»` の private を再導出） -/

/-- 条件 (VI) の指標事実（Isabelle `c6gx_condVI_j0`）。 -/
private theorem condVI_idx_nc {M : PS} (hcond : transCondVI M = true) :
    parent M 0 (Lng M - 1) = Lng M - 2 ∧
    entry M 1 (Lng M - 2) + 1 = entry M 1 (Lng M - 1) ∧
    0 < entry M 1 (Lng M - 1) := by
  simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    lastIdx, lastParent] at hcond
  obtain ⟨⟨hpos, heq⟩, hadj⟩ := hcond
  have hp0 : parent M 0 (Lng M - 1) = Lng M - 2 := by omega
  refine ⟨hp0, ?_, hpos⟩
  rw [hp0] at heq; exact heq

/-- 正の親は本物の `nextR` 辺。 -/
private theorem nextR_of_parent_pos_nc (M : PS) (i k : ℕ)
    (hpos : 0 < parent M i k) : nextR M i (parent M i k) k = true := by
  have hmem : parent M i k ∈ parents M i k := by
    have hdef : parent M i k = (parents M i k).headD 0 := rfl
    cases hl : parents M i k with
    | nil => rw [hdef, hl] at hpos; simp at hpos
    | cons x xs => rw [hdef, hl]; simp
  simp only [parents, List.mem_filter] at hmem
  exact hmem.2

/-- 条件 (VI) の橋（Isabelle `c6gx_condVI_bridge`）。 -/
private theorem condVI_bridge_nc (M : PS) (hM : TPS M)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    hasParent M 1 (Lng M - 1) = true ∧ parent M 1 (Lng M - 1) = Lng M - 2 := by
  obtain ⟨hp0, he1, hpos1⟩ := condVI_idx_nc hcond
  have hpar0pos : 0 < parent M 0 (Lng M - 1) := by rw [hp0]; omega
  have hnext0 : nextR M 0 (Lng M - 2) (Lng M - 1) = true := by
    have h := nextR_of_parent_pos_nc M 0 (Lng M - 1) hpar0pos
    rwa [hp0] at h
  have hle0 : leR M 0 (Lng M - 2) (Lng M - 1) = true := nextR0_leR M _ _ hnext0
  have hle0' : le0 M (Lng M - 2) (Lng M - 1) = true := by simpa [leR] using hle0
  have hnr1 : nextrel1 M (Lng M - 2) (Lng M - 1) = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, hle0'⟩, ?_⟩
    intro u _
    by_cases hpu : Lng M - 2 < u
    · by_cases hux : le0 M u (Lng M - 1) = true
      · have hule : u ≤ Lng M - 1 := le0_index_fseq hux
        have hueq : u = Lng M - 1 := by omega
        subst hueq
        simp [hpu, hux]
      · simp [hpu, hux]
    · simp [hpu]
  have hnextR1 : nextR M 1 (Lng M - 2) (Lng M - 1) = true := by simpa [nextR] using hnr1
  have huniq : ∀ y, nextR M 1 y (Lng M - 1) = true → y = Lng M - 2 := by
    intro y hy; exact nextR1_unique_mr M y (Lng M - 2) (Lng M - 1) hy hnextR1
  exact ⟨(hasParent_iff_unique_fseq M 1 (Lng M - 1)).mpr ⟨Lng M - 2, hnextR1, huniq⟩,
    parent_eq_of_unique_fseq M 1 (Lng M - 1) (Lng M - 2) hnextR1 huniq⟩

/-- 条件 (VI) 下の tiling 前提（`idx1 = 1`, `w = 1`）。 -/
private theorem condVI_tiling_nc (M : PS) (hM : TPS M)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    1 < Lng M ∧
    ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) ∧
    idx1 M (Lng M - 1) = 1 ∧
    hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true ∧
    parent M (idx1 M (Lng M - 1)) (Lng M - 1) = Lng M - 2 := by
  obtain ⟨_, _, hpos1⟩ := condVI_idx_nc hcond
  obtain ⟨hhp, hjp⟩ := condVI_bridge_nc M hM hcond hj₁
  have hi1 : idx1 M (Lng M - 1) = 1 := by simp [idx1, hpos1]
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨_, h2⟩; omega
  refine ⟨hlast, hzero, hi1, ?_, ?_⟩
  · rw [hi1]; exact hhp
  · rw [hi1]; exact hjp

/-- 条件 (VI) 下の `oper` の長さ `Lng (oper M N) = Lng M - 2 + N`。 -/
private theorem oper_len_nc (M : PS) (N : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    Lng (oper M N) = Lng M - 2 + N := by
  obtain ⟨hlast, hzero, hi1, hp, hjp⟩ := condVI_tiling_nc M hM hcond hj₁
  have h := length_oper_tiling M N hlast hzero hp
  simp only [hjp] at h
  rw [show Lng M - 1 - (Lng M - 2) = 1 by omega] at h
  simpa using h

/-- 条件 (VI) 崩壊（`w = 1`）: `oper M (n+1)` は `oper M n` に 1 列を append したもの。
Isabelle `c6zx_condVI_oper_L` の Lean 版の骨。 -/
private theorem oper_append_block_nc (M : PS) (n : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    oper M (n + 1) = oper M n ++
      [(entry M 0 (Lng M - 2) + n * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)),
        entry M 1 (Lng M - 2))] := by
  obtain ⟨hlast, hzero, hi1, hp, hjp⟩ := condVI_tiling_nc M hM hcond hj₁
  set g : ℕ → PS := fun k =>
    (List.range' (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
        (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1))).map
      (fun j => (entry M 0 j + k * (if 0 < idx1 M (Lng M - 1) then
          entry M 0 (Lng M - 1) - entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) else 0),
        entry M 1 j + k * (if 1 < idx1 M (Lng M - 1) then
          entry M 1 (Lng M - 1) - entry M 1 (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) else 0)))
    with hg
  have hexp : ∀ N : ℕ, oper M N =
      M.take (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) ++ (List.range N).flatMap g := by
    intro N
    rw [hg]
    exact oper_tiling_expand M N hlast hzero hp
  have hp1 : parent M 1 (Lng M - 1) = Lng M - 2 := (condVI_bridge_nc M hM hcond hj₁).2
  have hgn : g n = [(entry M 0 (Lng M - 2)
      + n * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)), entry M 1 (Lng M - 2))] := by
    rw [hg]
    simp only [hi1]
    rw [hp1, show Lng M - 1 - (Lng M - 2) = 1 by omega]
    simp [List.range', Nat.mul_zero, Nat.add_zero]
  rw [hexp (n + 1), hexp n, List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← List.append_assoc, hgn]

/-- `Pred (oper M (n+1)) = oper M n`（条件 (VI) 崩壊）。 -/
private theorem Pred_oper_succ_nc (M : PS) (n : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    Pred (oper M (n + 1)) = oper M n := by
  have hc := oper_append_block_nc M n hM hcond hj₁
  have hlen : 1 < Lng (oper M (n + 1)) := by
    rw [oper_len_nc M (n + 1) hM hcond hj₁]; omega
  have hP : Pred (oper M (n + 1)) = (oper M (n + 1)).dropLast := by
    rw [Pred, if_neg (by omega)]
  rw [hP, hc]
  simp

/-! ## 最終列の行 1 は `u = M_{1,j₀}`、および `monoT (oper M k)` -/

/-- 最終列の行 1 の値はブロック定数 `u = entry M 1 (Lng M - 2)`。 -/
private theorem entry_oper_last_row1_nc (M : PS) (k : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hk : 1 ≤ k) :
    entry (oper M k) 1 (Lng (oper M k) - 1) = entry M 1 (Lng M - 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hc := oper_append_block_nc M j hM hcond hj₁
  have hlenj : Lng (oper M j) = Lng M - 2 + j := oper_len_nc M j hM hcond hj₁
  have hlensj : Lng (oper M (j + 1)) = Lng M - 2 + (j + 1) := oper_len_nc M (j + 1) hM hcond hj₁
  have hidx : Lng (oper M (j + 1)) - 1 = Lng (oper M j) := by rw [hlensj, hlenj]; omega
  rw [hidx, hc]
  rw [entry_append_right_mr _ _ 1 (Lng (oper M j)) (le_refl _)]
  simp [entry]

/-- 条件 (VI) 崩壊下、`oper M k` は `monoT`（`leR ... 0 0 last`）。 -/
private theorem le0_oper_full_nc (M : PS)
    (hM : TPS M) (hmono : monoT M = true) (hcond : transCondVI M = true)
    (hj₁ : 1 < Lng M - 1) :
    ∀ k, 1 ≤ k → leR (oper M k) 0 0 (Lng (oper M k) - 1) = true := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ j ih =>
      intro _
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · -- 基底 `k = 1`: `oper M 1 = Pred M`
        subst hj0
        have hop1 : oper M 1 = Pred M := (pred_is_oper1 M hM (by omega)).symm
        have hmonoP : monoT (Pred M) = true := monoT_Pred_long M hM hmono (by omega)
        simp only [monoT, Bool.and_eq_true] at hmonoP
        rw [hop1]; exact hmonoP.2
      · -- 帰納段: append 転送 ＋ `s84c1_le0_L_mstar` ＋ 推移律
        have hopJ : TPS (oper M j) := oper_TPS M j hM hjpos
        have hopSJ : TPS (oper M (j + 1)) := oper_TPS M (j + 1) hM (by omega)
        have hlenj : Lng (oper M j) = Lng M - 2 + j := oper_len_nc M j hM hcond hj₁
        have hlensj : Lng (oper M (j + 1)) = Lng M - 2 + (j + 1) :=
          oper_len_nc M (j + 1) hM hcond hj₁
        have hc := oper_append_block_nc M j hM hcond hj₁
        -- IH: `0 → (Lng (oper M j) - 1)` in `oper M j`
        have hIH := ih hjpos
        -- 転送: `0 → (Lng (oper M j) - 1)` in `oper M (j+1)`
        have hbLtJ : Lng (oper M j) - 1 < Lng (oper M j) := by rw [hlenj]; omega
        have hbLtSJ : Lng (oper M j) - 1 < Lng (oper M (j + 1)) := by
          rw [hlensj, hlenj]; omega
        have htransfer : leR (oper M (j + 1)) 0 0 (Lng (oper M j) - 1) = true := by
          apply parent_exists_3 (oper M (j + 1)) 0 (Lng (oper M j) - 1) hopSJ
            (by rw [hlenj]; omega) hbLtSJ
          intro z hz0 hzb
          have hzLt : z < Lng (oper M j) := by omega
          have hentry0 : entry (oper M (j + 1)) 0 0 = entry (oper M j) 0 0 := by
            rw [hc, entry_append_left_mr _ _ 0 0 (by rw [hlenj]; omega)]
          have hentryz : entry (oper M (j + 1)) 0 z = entry (oper M j) 0 z := by
            rw [hc, entry_append_left_mr _ _ 0 z hzLt]
          rw [hentry0, hentryz]
          exact ancestor_basic_1 (oper M j) 0 z (Lng (oper M j) - 1) hopJ hz0 hzb hIH
        -- 末端エッジ: `(Lng (oper M j)-1) → last` in `oper M (j+1)`
        have hedge := s84c1_le0_L_mstar M j hM hcond hj₁ hjpos
        exact row0_transitive (oper M (j + 1)) 0 (Lng (oper M j) - 1)
          (Lng (oper M (j + 1)) - 1) hopSJ htransfer hedge

/-- `monoT (oper M k) = true`（条件 (VI) 崩壊）。 -/
private theorem monoT_oper_nc (M : PS)
    (hM : TPS M) (hmono : monoT M = true) (hcond : transCondVI M = true)
    (hj₁ : 1 < Lng M - 1) (k : ℕ) (hk : 1 ≤ k) :
    monoT (oper M k) = true := by
  have hlen : Lng (oper M k) = Lng M - 2 + k := oper_len_nc M k hM hcond hj₁
  have hnz : zeroT (oper M k) = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    left; rw [hlen]; omega
  simp only [monoT, hnz, Bool.not_false, Bool.true_and]
  exact le0_oper_full_nc M hM hmono hcond hj₁ k hk

/-! ## `oper M (n+1)` の `transJ0` / `transC1` / `transC2`（塔の 1 段） -/

/-- 行 0 の増分 `d₀ > 0`（Isabelle `s84c1_e0_jm2_lt`）。 -/
private theorem condVI_d0_pos_nc (M : PS) (hM : TPS M)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    entry M 0 (Lng M - 2) < entry M 0 (Lng M - 1) := by
  obtain ⟨hhp, hjp⟩ := condVI_bridge_nc M hM hcond hj₁
  have hnext1 := hasParent_next_fseq M 1 (Lng M - 1) hhp
  have hleR := (nextR_implies_row0 M 1 (parent M 1 (Lng M - 1)) (Lng M - 1) hnext1).2
  rw [hjp] at hleR
  exact ancestor_basic_1 M (Lng M - 2) (Lng M - 1) (Lng M - 1) hM (by omega) (le_refl _) hleR

/-- 最終列の行 0 の値。 -/
private theorem entry_oper_last_row0_nc (M : PS) (k : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hk : 1 ≤ k) :
    entry (oper M k) 0 (Lng (oper M k) - 1)
      = entry M 0 (Lng M - 2)
        + (k - 1) * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hc := oper_append_block_nc M j hM hcond hj₁
  have hlenj : Lng (oper M j) = Lng M - 2 + j := oper_len_nc M j hM hcond hj₁
  have hlensj : Lng (oper M (j + 1)) = Lng M - 2 + (j + 1) := oper_len_nc M (j + 1) hM hcond hj₁
  have hidx : Lng (oper M (j + 1)) - 1 = Lng (oper M j) := by rw [hlensj, hlenj]; omega
  rw [hidx, hc, entry_append_right_mr _ _ 0 (Lng (oper M j)) (le_refl _)]
  simp [entry]

/-- 基点 `ms = Lng (oper M n) - 1` は `oper M (n+1)` で許容的（行 1 が定数 `u` なので
`ms → ms+1` の行 1 辺が立たない）。 -/
private theorem adm_oper_ms_nc (M : PS) (n : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hn : 1 ≤ n) :
    adm (oper M (n + 1)) (Lng (oper M n) - 1) = true := by
  have hlenj : Lng (oper M n) = Lng M - 2 + n := oper_len_nc M n hM hcond hj₁
  have hlensj : Lng (oper M (n + 1)) = Lng M - 2 + (n + 1) := oper_len_nc M (n + 1) hM hcond hj₁
  have hc := oper_append_block_nc M n hM hcond hj₁
  set ms := Lng (oper M n) - 1 with hms
  have hms1 : ms + 1 = Lng (oper M (n + 1)) - 1 := by rw [hms, hlensj, hlenj]; omega
  -- 行 1 の値: `ms` と `ms+1` はともに `u`
  have e_ms1 : entry (oper M (n + 1)) 1 (ms + 1) = entry M 1 (Lng M - 2) := by
    rw [hms1]; exact entry_oper_last_row1_nc M (n + 1) hM hcond hj₁ (by omega)
  have hmslt : ms < Lng (oper M n) := by rw [hms, hlenj]; omega
  have e_ms : entry (oper M (n + 1)) 1 ms = entry M 1 (Lng M - 2) := by
    rw [hc, entry_append_left_mr (oper M n) _ 1 ms hmslt]
    exact entry_oper_last_row1_nc M n hM hcond hj₁ hn
  -- `nextR (oper M (n+1)) 1 ms (ms+1) = false`（行 1 が定数）
  have hnr1 : nextR (oper M (n + 1)) 1 ms (ms + 1) = false := by
    by_contra hcon
    have h : nextR (oper M (n + 1)) 1 ms (ms + 1) = true := by
      cases hb : nextR (oper M (n + 1)) 1 ms (ms + 1)
      · exact absurd hb hcon
      · rfl
    simp only [nextR, if_neg (by omega : ¬(1 : ℕ) = 0), nextrel1,
      Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, hstrict⟩, _⟩, _⟩ := h
    rw [e_ms, e_ms1] at hstrict
    exact absurd hstrict (lt_irrefl _)
  have hnadm : nadm (oper M (n + 1)) ms = false := by
    simp only [nadm, Bool.or_eq_false_iff]
    refine ⟨by simp only [decide_eq_false_iff_not]; rw [hms, hlensj, hlenj]; omega, ?_⟩
    simp [hnr1]
  simp [adm, hnadm]

/-- `transJ0 (oper M (n+1)) = Lng (oper M n) - 1`（最終列の行 0 の親＝直前列）。 -/
private theorem transJ0_oper_succ_nc (M : PS) (n : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hn : 1 ≤ n) :
    transJ0 (oper M (n + 1)) = Lng (oper M n) - 1 := by
  have hlenj : Lng (oper M n) = Lng M - 2 + n := oper_len_nc M n hM hcond hj₁
  have hlensj : Lng (oper M (n + 1)) = Lng M - 2 + (n + 1) := oper_len_nc M (n + 1) hM hcond hj₁
  have hc := oper_append_block_nc M n hM hcond hj₁
  have hd0 := condVI_d0_pos_nc M hM hcond hj₁
  set ms := Lng (oper M n) - 1 with hms
  have hms1 : ms + 1 = Lng (oper M (n + 1)) - 1 := by rw [hms, hlensj, hlenj]; omega
  have hmslt : ms < Lng (oper M n) := by rw [hms, hlenj]; omega
  -- 行 0 の値
  have e_ms1 : entry (oper M (n + 1)) 0 (ms + 1)
      = entry M 0 (Lng M - 2) + n * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)) := by
    rw [hms1]
    have := entry_oper_last_row0_nc M (n + 1) hM hcond hj₁ (by omega)
    simpa using this
  have hmslt2 : ms < Lng (oper M n) := by rw [hms, hlenj]; omega
  have e_ms : entry (oper M (n + 1)) 0 ms
      = entry M 0 (Lng M - 2) + (n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)) := by
    rw [hc, entry_append_left_mr (oper M n) _ 0 ms hmslt2]
    exact entry_oper_last_row0_nc M n hM hcond hj₁ hn
  have hstrict : entry (oper M (n + 1)) 0 ms < entry (oper M (n + 1)) 0 (ms + 1) := by
    rw [e_ms, e_ms1]
    have hmul : (n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2))
        < n * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega
  -- 直接親エッジ `nextrel0 ms (ms+1)`
  have hnr0 : nextrel0 (oper M (n + 1)) ms (ms + 1) = true := by
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hstrict⟩, ?_⟩
    · rw [hms, hlensj, hlenj]; omega
    · rw [hms1, hlensj]; omega
    · omega
    · intro j hj
      have hjms : ¬ (ms < j) := by omega
      simp [hjms]
  have hnextR : nextR (oper M (n + 1)) 0 ms (ms + 1) = true := by simpa [nextR] using hnr0
  have huniq : ∀ y, nextR (oper M (n + 1)) 0 y (ms + 1) = true → y = ms :=
    fun y hy => row0_parent_unique (oper M (n + 1)) y ms (ms + 1) hy hnextR
  have hpar : parent (oper M (n + 1)) 0 (ms + 1) = ms :=
    parent_eq_of_unique_fseq (oper M (n + 1)) 0 (ms + 1) ms hnextR huniq
  rw [transJ0, lastParent, lastIdx, ← hms1]
  exact hpar

/-- `transC1 (oper M (n+1)) = D_u 0`。 -/
private theorem transC1_oper_succ_nc (M : PS) (n : ℕ)
    (hST : STPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hn : 1 ≤ n) :
    transC1 (oper M (n + 1)) = Dprin (entry M 1 (Lng M - 2) : ℕ∞) BZero := by
  have hM : TPS M := STPS_TPS M hST
  have hRn : RTPS (oper M n) := STPS_RTPS _ (STPS.oper hST n hn)
  have hJ0 : transJ0 (oper M (n + 1)) = Lng (oper M n) - 1 :=
    transJ0_oper_succ_nc M n hM hcond hj₁ hn
  have hadm : adm (oper M (n + 1)) (Lng (oper M n) - 1) = true :=
    adm_oper_ms_nc M n hM hcond hj₁ hn
  have hJm1 : transJm1 (oper M (n + 1)) = Lng (oper M n) - 1 := by
    rw [transJm1, hJ0, Adm, if_pos hadm]
  have hnz : zeroT (oper M n) = false := by
    have hlen := oper_len_nc M n hM hcond hj₁
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    left; rw [hlen]; omega
  rw [transC1, hJm1, Pred_oper_succ_nc M n hM hcond hj₁,
    Mark_rightmost1_forward (oper M n) hRn hnz,
    entry_oper_last_row1_nc M n hM hcond hj₁ hn]

/-- `transC2 (oper M (n+1)) = D_u(D_u 0)`（`oper M (n+1)` は条件 (I) または (III)）。 -/
private theorem transC2_oper_succ_nc (M : PS) (n : ℕ)
    (hST : STPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hn : 1 ≤ n) :
    transC2 (oper M (n + 1))
      = Dprin (entry M 1 (Lng M - 2) : ℕ∞)
          (Dprin (entry M 1 (Lng M - 2) : ℕ∞) BZero) := by
  have hM : TPS M := STPS_TPS M hST
  have hC1 : transC1 (oper M (n + 1)) = Dprin (entry M 1 (Lng M - 2) : ℕ∞) BZero :=
    transC1_oper_succ_nc M n hST hcond hj₁ hn
  have hV : transV (oper M (n + 1)) = (entry M 1 (Lng M - 2) : ℕ∞) := by
    rw [transV, hC1]; rfl
  have hT2 : transT2 (oper M (n + 1)) = BZero := by
    rw [transT2, hC1]; rfl
  have hJ0 : transJ0 (oper M (n + 1)) = Lng (oper M n) - 1 :=
    transJ0_oper_succ_nc M n hM hcond hj₁ hn
  have hadm : adm (oper M (n + 1)) (Lng (oper M n) - 1) = true :=
    adm_oper_ms_nc M n hM hcond hj₁ hn
  have hadmlp : adm (oper M (n + 1)) (lastParent (oper M (n + 1))) = true := by
    rw [show lastParent (oper M (n + 1)) = Lng (oper M n) - 1 from hJ0]; exact hadm
  -- 行 1 の値: 最終列と親（＝ms）はともに `u`
  have hlastu : entry (oper M (n + 1)) 1 (lastIdx (oper M (n + 1)))
      = entry M 1 (Lng M - 2) := entry_oper_last_row1_nc M (n + 1) hM hcond hj₁ (by omega)
  have hlpu : entry (oper M (n + 1)) 1 (lastParent (oper M (n + 1)))
      = entry M 1 (Lng M - 2) := by
    have hlenj : Lng (oper M n) = Lng M - 2 + n := oper_len_nc M n hM hcond hj₁
    have hc := oper_append_block_nc M n hM hcond hj₁
    have hlt : Lng (oper M n) - 1 < Lng (oper M n) := by rw [hlenj]; omega
    rw [show lastParent (oper M (n + 1)) = Lng (oper M n) - 1 from hJ0]
    rw [hc, entry_append_left_mr (oper M n) _ 1 (Lng (oper M n) - 1) hlt]
    exact entry_oper_last_row1_nc M n hM hcond hj₁ hn
  -- 条件 (I) ∨ (III)
  have hbranch : (transCondI (oper M (n + 1)) || transCondIII (oper M (n + 1))
      || transCondV (oper M (n + 1))) = true := by
    by_cases hu : entry M 1 (Lng M - 2) = 0
    · have hI : transCondI (oper M (n + 1)) = true := by
        simp [transCondI, hlastu, hu, hadmlp]
      simp [hI]
    · have hupos : 0 < entry M 1 (Lng M - 2) := by omega
      have hIII : transCondIII (oper M (n + 1)) = true := by
        simp [transCondIII, hlastu, hlpu, hadmlp, hupos]
      simp [hIII]
  rw [transC2, hV, hT2]
  simp only [transC2Core, hbranch, if_true, hlastu]
  simp [addBT, BZero, Dprin]

/-! ## L 塔の平坦形と閉形式（Isabelle `c6zx_L_tower` / `flat_Dtower`） -/

/-- `flatBT (D_u^[m] 0) = [D_u]^m ++ [Z]`（Isabelle `flat_Dtower`）。 -/
private theorem flat_tower_nc (u : ℕ) (m : ℕ) :
    flatBT ((Dprin (u : ℕ∞))^[m] BZero)
      = List.replicate m (Sym.dsym (u : ℕ∞)) ++ [Sym.zero] := by
  induction m with
  | zero => simp [BZero, flatBT]
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      have hf : flatBT (Dprin (u : ℕ∞) ((Dprin (u : ℕ∞))^[m] BZero))
          = Sym.dsym (u : ℕ∞) :: flatBT ((Dprin (u : ℕ∞))^[m] BZero) := rfl
      rw [hf, ih, List.replicate_succ]
      simp
/-! ## 塔の `T_B` 事実（`8.6-condVI-close` の `Dtower_*_v6` は `private` なので複製） -/

private theorem BZero_mem_T_B_nc : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

private theorem tower_mem_T_B_nc (u k : ℕ) : (Dprin (u : ℕ∞))^[k] BZero ∈ T_B := by
  induction k with
  | zero => simpa using BZero_mem_T_B_nc
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h : dfree_BT ((Dprin (u : ℕ∞))^[k] BZero) = true := ih
      simp [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, h]

private theorem isPTB_str_Dprin_tower_nc (U u k : ℕ) :
    isPTB_str (flatBT (Dprin (U : ℕ∞) ((Dprin (u : ℕ∞))^[k] BZero))) := by
  refine ⟨.db (U : ℕ∞) _, ?_, rfl⟩
  have h : dfree_BT ((Dprin (u : ℕ∞))^[k] BZero) = true := tower_mem_T_B_nc u k
  simp [dfree_BP, h]

/-! ## 非退化枝の guard（Isabelle `c6gx_condVI_setup`, pss_wip.thy:69867 の複製） -/

private theorem condVI_setup_nc {M : PS} (hR : RTPS M) (_hcond : transCondVI M = true)
    (hj₁ : 1 < Lng M - 1) : 0 < transJ1 M ∧ transT1 M ≠ BZero := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 2 < Lng M := by omega
  refine ⟨by simp only [transJ1, lastIdx]; omega, ?_⟩
  intro ht₁
  have hzP : zeroT (Pred M) = true :=
    (Trans_preserves_zeroT (Pred M) (Pred_TPS M hM)).2 ht₁
  have hLP : Lng (Pred M) = Lng M - 1 := by
    simp only [Pred]; rw [if_neg (by omega)]; simp
  have h1 : Lng (Pred M) = 1 := by
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzP; exact hzP.1
  omega

/-! ## fact (c) の残差 Prop（Isabelle `c6nx_t2eq`, pss_wip.thy:76619） -/

/-- **fact (c)**（`c6nx_t2eq`）: 非許容枝の `transT2 M`（`transC1 M` の頭部内側）は
`D_{M_{1,j₀}} 0`。許容枝の `transC1 M = D_u 0` に対し、非許容枝は外側 `D_V` が残る
（`transC1 M = D_V(D_u 0)`）。 -/
def CondVInadm_t2eq_fc : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → transCondVI M = true → 1 < Lng M - 1 →
    ¬ (adm M (transJ0 M) = true) →
    transT2 M = Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero

/-! ## L 塔（許容枝 `CondVIres_adm_Ltower_holds_af` の非許容双子、fact (c) modulo） -/

/-- **削減後の残差 (B′) `CondVIres_nadm_Ltower_v6p`（`8.6-condVI-props`:421）**を
fact (c)（`CondVInadm_t2eq_fc`）から証明。塔の帰納段は許容枝と完全に同一で、
唯一の相違は base scb 分解から余分な `dsym V`（`V = M_{1,j₋₁}`）を s 側へ剥がす点。 -/
theorem CondVIres_nadm_Ltower_of_t2eq_nc (hfc : CondVInadm_t2eq_fc) :
    CondVIres_nadm_Ltower_v6p := by
  intro M s₁ b₁ hST hmono hcond hj₁ hnadm hd1 _hk1
  have hM : TPS M := STPS_TPS M hST
  have hR : RTPS M := STPS_RTPS M hST
  have htj0 : transJ0 M = Lng M - 2 := (condVI_idx_nc hcond).1
  set u := entry M 1 (Lng M - 2) with hudef
  -- 頭 `V = M_{1,j₋₁}` と `transC1 M = D_V(D_u 0)`
  have hj₁pos : 0 < transJ1 M := (condVI_setup_nc hR hcond hj₁).1
  have ht₁ : transT1 M ≠ BZero := (condVI_setup_nc hR hcond hj₁).2
  have hc1 : transC1 M = Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M) :=
    (c1_shape_holds M hR hM hmono hj₁pos ht₁).2.1
  have ht2 : transT2 M = Dprin (u : ℕ∞) BZero := by
    have h := hfc M hR hmono hcond hj₁ hnadm
    rw [h, htj0]
  have hc1' : transC1 M
      = Dprin (entry M 1 (transJm1 M) : ℕ∞) (Dprin (u : ℕ∞) BZero) := by
    rw [hc1, ht2]
  -- `T_B` 事実
  have hbrp : ∀ x ∈ b₁, x = Sym.rp := hd1.2.2
  have hptb : isPTB_str (flatBT (Dprin (u : ℕ∞) BZero)) :=
    ⟨.db (u : ℕ∞) BZero, by simp [dfree_BP, dfree_BT, dfree_BPList, BZero], rfl⟩
  -- base: 余分な `dsym V` を s 側へ剥がす
  have hbase2 : scb_decomp (Trans (oper M 1))
      (s₁ ++ [Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)])
      (flatBT (Dprin (u : ℕ∞) BZero)) b₁ := by
    refine ⟨?_, fun _ => hptb, hbrp⟩
    have h1 := hd1.1
    rw [h1, hc1']
    have hfV : flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (Dprin (u : ℕ∞) BZero))
        = Sym.dsym (entry M 1 (transJm1 M) : ℕ∞) :: flatBT (Dprin (u : ℕ∞) BZero) := rfl
    rw [hfV]; simp [List.append_assoc]
  -- 塔の帰納 `Q(k)`
  have Q : ∀ k, scb_decomp (Trans (oper M (k + 1)))
      (s₁ ++ [Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)] ++ List.replicate k (Sym.dsym (u : ℕ∞)))
      (flatBT (Dprin (u : ℕ∞) BZero)) b₁ := by
    intro k
    induction k with
    | zero => simpa using hbase2
    | succ k ih =>
        have hRsj : RTPS (oper M (k + 2)) := STPS_RTPS _ (STPS.oper hST (k + 2) (by omega))
        have hmsj : monoT (oper M (k + 2)) = true :=
          monoT_oper_nc M hM hmono hcond hj₁ (k + 2) (by omega)
        have hj₁sj : 0 < transJ1 (oper M (k + 2)) := by
          rw [transJ1, lastIdx, oper_len_nc M (k + 2) hM hcond hj₁]; omega
        have hpredsj : Pred (oper M (k + 2)) = oper M (k + 1) :=
          Pred_oper_succ_nc M (k + 1) hM hcond hj₁
        have ht1sj : transT1 (oper M (k + 2)) ≠ BZero := by
          rw [transT1, hpredsj]
          intro hz
          have hzt : zeroT (oper M (k + 1)) = true :=
            (Trans_preserves_zeroT (oper M (k + 1)) (oper_TPS M (k + 1) hM (by omega))).mpr hz
          have hnz : zeroT (oper M (k + 1)) = false := by
            simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
            left; rw [oper_len_nc M (k + 1) hM hcond hj₁]; omega
          rw [hnz] at hzt; exact Bool.noConfusion hzt
        have hC1 : transC1 (oper M (k + 2)) = Dprin (u : ℕ∞) BZero :=
          transC1_oper_succ_nc M (k + 1) hST hcond hj₁ (by omega)
        have hC2 : transC2 (oper M (k + 2)) = Dprin (u : ℕ∞) (Dprin (u : ℕ∞) BZero) :=
          transC2_oper_succ_nc M (k + 1) hST hcond hj₁ (by omega)
        have hc₂P : ∃ p, transC2 (oper M (k + 2)) = .trm [p] :=
          ⟨.db (u : ℕ∞) (Dprin (u : ℕ∞) BZero), by rw [hC2]; rfl⟩
        obtain ⟨s', b', hd1', hd2⟩ :=
          trans_surgery_localized_v6p (oper M (k + 2)) hRsj hmsj hj₁sj ht1sj hc₂P
        rw [hpredsj, hC1] at hd1'
        rw [hC2] at hd2
        obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (oper M (k + 1)))
          s' (s₁ ++ [Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)] ++ List.replicate k (Sym.dsym (u : ℕ∞)))
          (flatBT (Dprin (u : ℕ∞) BZero)) b' b₁ hd1' ih
        rw [hs, hb] at hd2
        refine ⟨?_, fun _ => hptb, hbrp⟩
        rw [hd2.1]
        have hfd : flatBT (Dprin (u : ℕ∞) (Dprin (u : ℕ∞) BZero))
            = Sym.dsym (u : ℕ∞) :: flatBT (Dprin (u : ℕ∞) BZero) := rfl
        rw [hfd, List.replicate_add k 1, List.replicate_one]
        simp [List.append_assoc]
  -- 残差の結論（`n ≥ 1`）
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hqm := Q m
  have hL : (s₁ ++ [Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)]
        ++ List.replicate m (Sym.dsym (u : ℕ∞)))
        ++ flatBT (Dprin (u : ℕ∞) BZero) ++ b₁
      = s₁ ++ (Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
          :: (List.replicate (m + 1) (Sym.dsym (u : ℕ∞)) ++ [Sym.zero])) ++ b₁ := by
    have hfz : flatBT (Dprin (u : ℕ∞) BZero) = [Sym.dsym (u : ℕ∞), Sym.zero] := rfl
    rw [hfz, List.replicate_add m 1, List.replicate_one]
    simp [List.append_assoc]
  have hRt : flatBP (BP.db (entry M 1 (transJm1 M) : ℕ∞) ((Dprin (u : ℕ∞))^[m + 1] BZero))
      = Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
        :: (List.replicate (m + 1) (Sym.dsym (u : ℕ∞)) ++ [Sym.zero]) := by
    have hfb : flatBP (BP.db (entry M 1 (transJm1 M) : ℕ∞) ((Dprin (u : ℕ∞))^[m + 1] BZero))
        = Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
          :: flatBT ((Dprin (u : ℕ∞))^[m + 1] BZero) := rfl
    rw [hfb, flat_tower_nc]
  rw [htj0, ← hudef, hqm.1, hL, hRt]

/-! ## fact (c) = `c6nx_t2eq`（`m_7_3_Mark_rightmost2` + `c6nx_predVI` + `c6nx_jm1eq`）

Isabelle は `w1x_nadm_nextrel0_left`（rtrancl 最終段）／`monoT_branch_hasParent`／
`adm_prefix_agree_eq`（接頭辞一致）を使うが、Lean 側は
* 行 0 隣接 = `c3cx_nextrel0_adj_of_le0`（`8.4-s84x-vocab-run`、`le0`→直接辺）、
* 許容化の接頭辞一致 = `admof_slice`（`6.3-admof-slice`、`Adm(seg)=Adm-s`）＋
  `Adm M j₀ = Adm M (j₀-1)`（`j₀` 非許容 ⟹ 直接 `Adm_max`/`Adm_le`/`Adm_adm`）
で置換して、深い機構を回避する。 -/

/-- `Pred M` は末尾より手前で entry を保つ（任意段 `i`）。 -/
private theorem entry_Pred_nc (M : PS) (i j : ℕ) (hlen : 1 < Lng M)
    (hj : j < Lng M - 1) : entry (Pred M) i j = entry M i j := by
  rw [Pred_eq_take M hlen]
  exact entry_take M (Lng M - 1) i j (by omega)

/-- `Lng (Pred M) = Lng M - 1`（`8.6-condVI-props` `Lng_Pred_v6p` の複製）。 -/
private theorem Lng_Pred_nc (M : PS) (hlen : 1 < Lng M) : Lng (Pred M) = Lng M - 1 := by
  simp only [Pred]; rw [if_neg (by omega)]; simp

/-- 非許容 `j₀` の行 1 隣接辺（`nadm` の定義から直接）。 -/
private theorem nadm_row1_edge_nc (M : PS) (hcond : transCondVI M = true)
    (hj₁ : 1 < Lng M - 1) (hnadm : ¬ (adm M (transJ0 M) = true)) :
    nextR M 1 (transJ0 M - 1) (transJ0 M) = true := by
  have htj0 : transJ0 M = Lng M - 2 := (condVI_idx_nc hcond).1
  have hna : adm M (transJ0 M) = false := by simpa using hnadm
  have hnadmB : nadm M (transJ0 M) = true := by
    have h := hna; unfold adm at h; simpa using h
  simp only [nadm, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hnadmB
  rcases hnadmB with h | ⟨h1, _⟩
  · omega
  · exact h1

/-- **fact (c) の親事実**（Isabelle `c6nx_nadm_jp0`）: `j₀` の行 0/1 親は `j₀-1`、
`0 < M_{1,j₀}`、`M_{1,j₀-1}+1 = M_{1,j₀}`、行 0 の直接辺。 -/
private theorem nadm_jp0_nc (M : PS) (hR : RTPS M) (hcond : transCondVI M = true)
    (hj₁ : 1 < Lng M - 1) (hnadm : ¬ (adm M (transJ0 M) = true)) :
    0 < entry M 1 (transJ0 M) ∧
      entry M 1 (transJ0 M - 1) + 1 = entry M 1 (transJ0 M) ∧
      nextrel0 M (transJ0 M - 1) (transJ0 M) = true := by
  have hM : TPS M := RTPS_TPS M hR
  have htj0 : transJ0 M = Lng M - 2 := (condVI_idx_nc hcond).1
  have hj0ge1 : 1 ≤ transJ0 M := by omega
  have hj0L : transJ0 M < Lng M := by omega
  have hedge : nextR M 1 (transJ0 M - 1) (transJ0 M) = true :=
    nadm_row1_edge_nc M hcond hj₁ hnadm
  have hh := hedge
  simp only [nextR, if_neg (by omega : ¬(1 : ℕ) = 0), nextrel1, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hh
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, hltu⟩, hle0e⟩, _⟩ := hh
  have huPos : 0 < entry M 1 (transJ0 M) := by omega
  -- 行 0 の直接辺
  have hnr0 : nextrel0 M (transJ0 M - 1) (transJ0 M) = true := by
    have h := c3cx_nextrel0_adj_of_le0 M hle0e (by omega)
    rwa [show transJ0 M - 1 + 1 = transJ0 M from by omega] at h
  -- 行 1 親と RedCondA での増分
  have huniq1 : ∀ y, nextR M 1 y (transJ0 M) = true → y = transJ0 M - 1 :=
    fun y hy => nextR1_unique_mr M y (transJ0 M - 1) (transJ0 M) hy hedge
  have hp1 : hasParent M 1 (transJ0 M) = true :=
    (hasParent_iff_unique_fseq M 1 (transJ0 M)).mpr ⟨transJ0 M - 1, hedge, huniq1⟩
  have hpar1 : parent M 1 (transJ0 M) = transJ0 M - 1 :=
    parent_eq_of_unique_fseq M 1 (transJ0 M) (transJ0 M - 1) hedge huniq1
  obtain ⟨hA, _⟩ := RTPS_condAB M hR
  have hincr : entry M 1 (transJ0 M - 1) + 1 = entry M 1 (transJ0 M) := by
    have := RedCondA_apply M hA 1 (transJ0 M) (by omega) hj0L hp1
    rwa [hpar1] at this
  exact ⟨huPos, hincr, hnr0⟩

/-- **`Pred M` も条件 (VI) ホスト**（Isabelle `c6nx_predVI`）。 -/
private theorem c6nx_predVI_nc (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1)
    (hnadm : ¬ (adm M (transJ0 M) = true)) :
    transCondVI (Pred M) = true ∧ transJ0 (Pred M) = transJ0 M - 1 := by
  have hM : TPS M := RTPS_TPS M hR
  have htj0 : transJ0 M = Lng M - 2 := (condVI_idx_nc hcond).1
  have hj0ge1 : 1 ≤ transJ0 M := by omega
  have hLP : Lng (Pred M) = Lng M - 1 := Lng_Pred_nc M (by omega)
  have hLPm1 : Lng (Pred M) - 1 = transJ0 M := by omega
  obtain ⟨huPos, hincr, hnr0⟩ := nadm_jp0_nc M hR hcond hj₁ hnadm
  -- 行 0 の直接辺を `Pred M` へ転送
  have hePm1_0 : entry (Pred M) 0 (transJ0 M - 1) = entry M 0 (transJ0 M - 1) :=
    entry_Pred_nc M 0 (transJ0 M - 1) (by omega) (by omega)
  have heP0_0 : entry (Pred M) 0 (transJ0 M) = entry M 0 (transJ0 M) :=
    entry_Pred_nc M 0 (transJ0 M) (by omega) (by omega)
  have hnr0P : nextrel0 (Pred M) (transJ0 M - 1) (transJ0 M) = true := by
    have hh0 := hnr0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at hh0 ⊢
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, he0lt⟩, _⟩ := hh0
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, ?_⟩, ?_⟩
    · rw [hePm1_0, heP0_0]; exact he0lt
    · intro j hj
      have hnlt : ¬ (transJ0 M - 1 < j) := by omega
      simp [hnlt]
  have hnextR0P : nextR (Pred M) 0 (transJ0 M - 1) (transJ0 M) = true := by
    simpa [nextR] using hnr0P
  have huniq0P : ∀ y, nextR (Pred M) 0 y (transJ0 M) = true → y = transJ0 M - 1 :=
    fun y hy => row0_parent_unique (Pred M) y (transJ0 M - 1) (transJ0 M) hy hnextR0P
  have hpar0P : parent (Pred M) 0 (transJ0 M) = transJ0 M - 1 :=
    parent_eq_of_unique_fseq (Pred M) 0 (transJ0 M) (transJ0 M - 1) hnextR0P huniq0P
  have hpredJ0 : transJ0 (Pred M) = transJ0 M - 1 := by
    simp only [transJ0, lastParent, lastIdx, hLPm1]; exact hpar0P
  -- 行 1 の entry を `Pred M` へ転送
  have heP0_1 : entry (Pred M) 1 (transJ0 M) = entry M 1 (transJ0 M) :=
    entry_Pred_nc M 1 (transJ0 M) (by omega) (by omega)
  have hePm1_1 : entry (Pred M) 1 (transJ0 M - 1) = entry M 1 (transJ0 M - 1) :=
    entry_Pred_nc M 1 (transJ0 M - 1) (by omega) (by omega)
  have hcondP : transCondVI (Pred M) = true := by
    simp only [transCondVI, lastIdx, lastParent, hLPm1, hpar0P, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [heP0_1]; exact huPos
    · rw [hePm1_1, heP0_1]; exact hincr
    · omega
  exact ⟨hcondP, hpredJ0⟩

/-- **`transJm1 M = transJm1 (Pred M)`**（Isabelle `c6nx_jm1eq`）。
`admof_slice` で `Adm (Pred M)(j₀-1) = Adm M (j₀-1)`、`Adm M j₀ = Adm M (j₀-1)`（`j₀` 非許容）。 -/
private theorem c6nx_jm1eq_nc (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1)
    (hnadm : ¬ (adm M (transJ0 M) = true)) :
    transJm1 M = transJm1 (Pred M) := by
  have hM : TPS M := RTPS_TPS M hR
  have htj0 : transJ0 M = Lng M - 2 := (condVI_idx_nc hcond).1
  have hj0ge1 : 1 ≤ transJ0 M := by omega
  have hna : adm M (transJ0 M) = false := by simpa using hnadm
  have hpredJ0 : transJ0 (Pred M) = transJ0 M - 1 :=
    (c6nx_predVI_nc M hR hmono hcond hj₁ hnadm).2
  -- `Adm M j₀ = Adm M (j₀-1)`
  have hAdmStep : Adm M (transJ0 M) = Adm M (transJ0 M - 1) := by
    have hleA : Adm M (transJ0 M) ≤ transJ0 M := Adm_le M (transJ0 M)
    have hadmA : adm M (Adm M (transJ0 M)) = true := Adm_adm M (transJ0 M)
    have hneJ0 : Adm M (transJ0 M) ≠ transJ0 M := by
      intro h; rw [h, hna] at hadmA; exact Bool.noConfusion hadmA
    by_cases hadm1 : adm M (transJ0 M - 1) = true
    · have e1 : Adm M (transJ0 M - 1) = transJ0 M - 1 := by simp [Adm, hadm1]
      have hge : transJ0 M - 1 ≤ Adm M (transJ0 M) :=
        Adm_max M (transJ0 M - 1) (transJ0 M) hadm1 (by omega)
      omega
    · have hna1 : adm M (transJ0 M - 1) = false := by simpa using hadm1
      have hadmA1 : adm M (Adm M (transJ0 M - 1)) = true := Adm_adm M (transJ0 M - 1)
      have hleA1 : Adm M (transJ0 M - 1) ≤ transJ0 M - 1 := Adm_le M (transJ0 M - 1)
      have hneJ01 : Adm M (transJ0 M) ≠ transJ0 M - 1 := by
        intro h; rw [h, hna1] at hadmA; exact Bool.noConfusion hadmA
      have hne1 : Adm M (transJ0 M - 1) ≠ transJ0 M - 1 := by
        intro h; rw [h, hna1] at hadmA1; exact Bool.noConfusion hadmA1
      have hge : Adm M (transJ0 M) ≤ Adm M (transJ0 M - 1) :=
        Adm_max M (Adm M (transJ0 M)) (transJ0 M - 1) hadmA (by omega)
      have hle2 : Adm M (transJ0 M - 1) ≤ Adm M (transJ0 M) :=
        Adm_max M (Adm M (transJ0 M - 1)) (transJ0 M) hadmA1 (by omega)
      omega
  -- `Adm (Pred M)(j₀-1) = Adm M (j₀-1)` via `admof_slice`
  have hPredSeg : Pred M = seg M 0 (Lng M - 2) := by
    rw [Pred_eq_take M (by omega)]
    have h := take_eq_seg M (Lng M - 1) (by omega) (by omega)
    rw [h, show Lng M - 1 - 1 = Lng M - 2 from by omega]
  have hslice := admof_slice M 0 (transJ0 M - 1) (Lng M - 2) hM (by omega) (by omega) (by omega)
  rw [Nat.sub_zero, Nat.sub_zero, ← hPredSeg] at hslice
  simp only [transJm1]
  rw [hpredJ0, hslice, hAdmStep]

/-- **fact (c)（`c6nx_t2eq`）を無条件に閉じる**。 -/
theorem c6nx_t2eq_nc : CondVInadm_t2eq_fc := by
  intro M hR hmono hcond hj₁ hnadm
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 2 < Lng M := by omega
  have htj0 : transJ0 M = Lng M - 2 := (condVI_idx_nc hcond).1
  have hna : adm M (transJ0 M) = false := by simpa using hnadm
  have hLP : Lng (Pred M) = Lng M - 1 := Lng_Pred_nc M (by omega)
  have hLPm1 : Lng (Pred M) - 1 = transJ0 M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredmono : monoT (Pred M) = true := monoT_Pred_long M hM hmono (by omega)
  have hpredJ1 : 0 < transJ1 (Pred M) := by simp only [transJ1, lastIdx, hLP]; omega
  have eu : entry (Pred M) 1 (Lng (Pred M) - 1) = entry M 1 (transJ0 M) := by
    rw [hLPm1]; exact entry_Pred_nc M 1 (transJ0 M) (by omega) (by omega)
  by_cases hcorner : transT1 (Pred M) = BZero
  · -- corner: `Lng M = 3`, `j₀ = 1`, `transJm1 M = 0`
    have hPredM_TPS : TPS (Pred M) := Pred_TPS M hM
    have hPPredTPS : TPS (Pred (Pred M)) := Pred_TPS (Pred M) hPredM_TPS
    have hcorner' : Trans (Pred (Pred M)) = BZero := by simpa [transT1] using hcorner
    have hzPP : zeroT (Pred (Pred M)) = true :=
      (Trans_preserves_zeroT (Pred (Pred M)) hPPredTPS).2 hcorner'
    have hLPP1 : Lng (Pred (Pred M)) = 1 := by
      simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzPP; exact hzPP.1
    have hLPP : Lng (Pred (Pred M)) = Lng M - 2 := by
      have h1 : Lng (Pred (Pred M)) = Lng (Pred M) - 1 := Lng_Pred_nc (Pred M) (by rw [hLP]; omega)
      omega
    have hL3 : Lng M = 3 := by omega
    have hLP2 : Lng (Pred M) = 2 := by omega
    have htj01 : transJ0 M = 1 := by omega
    have hjm10 : transJm1 M = 0 := by
      have hAle : Adm M (transJ0 M) ≤ transJ0 M := Adm_le M (transJ0 M)
      have hAadm : adm M (Adm M (transJ0 M)) = true := Adm_adm M (transJ0 M)
      have hne : Adm M (transJ0 M) ≠ transJ0 M := by
        intro h; rw [h, hna] at hAadm; exact Bool.noConfusion hAadm
      simp only [transJm1]; omega
    have hmk := (two_column_Mark (Pred M) hpredR hpredmono hLP2).1
    have c1M0 : transC1 M = Mark (Pred M) 0 := by
      have h : transC1 M = Mark (Pred M) (transJm1 M) := rfl
      rw [h, hjm10]
    have e11 : entry (Pred M) 1 1 = entry M 1 (transJ0 M) := by
      rw [htj01]; exact entry_Pred_nc M 1 1 (by omega) (by omega)
    have h : transT2 M = bpHeadT (transC1 M) := rfl
    rw [h, c1M0, hmk]
    show Dprin (entry (Pred M) 1 1 : ℕ∞) BZero = Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero
    rw [e11]
  · -- main de-adm bridge via `m_7_3_Mark_rightmost2`
    have hpredVI : transCondVI (Pred M) = true := (c6nx_predVI_nc M hR hmono hcond hj₁ hnadm).1
    have hjm1eq : transJm1 M = transJm1 (Pred M) := c6nx_jm1eq_nc M hR hmono hcond hj₁ hnadm
    have rm2 : Mark (Pred M) (transJm1 (Pred M)) = transC2 (Pred M) :=
      m_7_3_Mark_rightmost2 (Pred M) hpredR hpredmono hpredJ1 hcorner
    have c2P : transC2 (Pred M)
        = Dprin (transV (Pred M)) (Dprin (entry (Pred M) 1 (Lng (Pred M) - 1) : ℕ∞) BZero) :=
      condVI_transC2_v6p hpredVI
    have c1M : transC1 M = transC2 (Pred M) := by
      have h : transC1 M = Mark (Pred M) (transJm1 M) := rfl
      rw [h, hjm1eq, rm2]
    have h : transT2 M = bpHeadT (transC1 M) := rfl
    rw [h, c1M, c2P]
    show Dprin (entry (Pred M) 1 (Lng (Pred M) - 1) : ℕ∞) BZero
        = Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero
    rw [eu]

/-- **`CondVIres_nadm_Ltower_v6p` を無条件に閉じる**（`8.6-condVI-props`:421）。 -/
theorem CondVIres_nadm_Ltower_holds_nc : CondVIres_nadm_Ltower_v6p :=
  CondVIres_nadm_Ltower_of_t2eq_nc c6nx_t2eq_nc

#print axioms CondVIres_nadm_Ltower_of_t2eq_nc
#print axioms c6nx_t2eq_nc
#print axioms CondVIres_nadm_Ltower_holds_nc

end PSS

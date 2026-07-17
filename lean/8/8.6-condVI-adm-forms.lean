import «8».«8.6-condVI-close»
import «8».«8.6-condVI-props»
import «8».«8.6-condVI-Ltower-facta»
import «8».«8.6-Trans-Red-funpow-IncrFirst»
import «8».«8.5-exchV-props»

/-!
# §8.6 条件 (VI) 許容枝 L 塔閉形式 — `CondVI_scbdec_adm_forms_v6` の討伐

- 目標: `«8».«8.6-condVI-close»` の `CondVI_scbdec_adm_forms_v6`（同 :244）を
  house pattern で閉じる。`«8».«8.6-condVI-props»` の
  `condVI_scbdec_adm_forms_holds_v6p : CondVIres_adm_Ltower_v6p → CondVI_scbdec_adm_forms_v6`
  へ、本ファイルが証明する `CondVIres_adm_Ltower_v6p`（同 :399）を渡す。
- Isabelle 対応（設計図）:
  * 許容枝塔 = `c613x_condVI_exch_adm`（`layerB/pss_wip.thy`:73312）内の `Ltower`/`flatMn`
  * L 塔閉形式 = `c6zx_L_tower`（同 :72166）＋ 境界 `c6zx_condVI_oper_L`（同 :72257）
    ＋ 底 `c6zx_condVI_baseL_free`（同 :72286）
  * `n = 1` 脚 = `condVI_transC1_adm_v6p`（`«8».«8.6-condVI-props»` 公開）＋ `pred_is_oper1`
- Lean 短縮のかなめ: Isabelle が `m_8_4_oper_props_5`（§8.4 scb 分解転送クラスタ、
  Lean 未移植）で回した塔帰納を、条件 (VI) 崩壊（`w = 1`）下で
  `oper M (n+1) = oper M n ++ [colₙ]`（`Pred (oper M (n+1)) = oper M n`）に還元し、
  `trans_surgery_localized_v6p`（`«8».«8.6-condVI-props»` 公開）を `oper M (n+1)` に
  適用して 1 段ずつ塔を伸ばす。scb 対の同定は `scb_unique_decomp_unconditional`（§7.2）。
- 依存: 上記 5 import に加え、推移的に §5.1（`row0_transitive`/`parent_exists_3`/
  `ancestor_basic_1`）、§6.5（`pred_is_oper1`/`monoT_Pred_long`/`entry_append_*`）、
  §6.6（`oper_tiling_expand`/`length_oper_tiling`/`entry_oper_tiling_*`）、
  §7.3（`Mark_rightmost1_forward`）。
- 状態: 🚧 作成中。private 補助は `_af` 接尾辞。
-/

namespace PSS

/-! ## 条件 (VI) の崩壊事実（`«8».«8.6-condVI-Ltower-facta»` の private を再導出） -/

/-- 条件 (VI) の指標事実（Isabelle `c6gx_condVI_j0`）。 -/
private theorem condVI_idx_af {M : PS} (hcond : transCondVI M = true) :
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
private theorem nextR_of_parent_pos_af (M : PS) (i k : ℕ)
    (hpos : 0 < parent M i k) : nextR M i (parent M i k) k = true := by
  have hmem : parent M i k ∈ parents M i k := by
    have hdef : parent M i k = (parents M i k).headD 0 := rfl
    cases hl : parents M i k with
    | nil => rw [hdef, hl] at hpos; simp at hpos
    | cons x xs => rw [hdef, hl]; simp
  simp only [parents, List.mem_filter] at hmem
  exact hmem.2

/-- 条件 (VI) の橋（Isabelle `c6gx_condVI_bridge`）。 -/
private theorem condVI_bridge_af (M : PS) (hM : TPS M)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    hasParent M 1 (Lng M - 1) = true ∧ parent M 1 (Lng M - 1) = Lng M - 2 := by
  obtain ⟨hp0, he1, hpos1⟩ := condVI_idx_af hcond
  have hpar0pos : 0 < parent M 0 (Lng M - 1) := by rw [hp0]; omega
  have hnext0 : nextR M 0 (Lng M - 2) (Lng M - 1) = true := by
    have h := nextR_of_parent_pos_af M 0 (Lng M - 1) hpar0pos
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
private theorem condVI_tiling_af (M : PS) (hM : TPS M)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    1 < Lng M ∧
    ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) ∧
    idx1 M (Lng M - 1) = 1 ∧
    hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true ∧
    parent M (idx1 M (Lng M - 1)) (Lng M - 1) = Lng M - 2 := by
  obtain ⟨_, _, hpos1⟩ := condVI_idx_af hcond
  obtain ⟨hhp, hjp⟩ := condVI_bridge_af M hM hcond hj₁
  have hi1 : idx1 M (Lng M - 1) = 1 := by simp [idx1, hpos1]
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨_, h2⟩; omega
  refine ⟨hlast, hzero, hi1, ?_, ?_⟩
  · rw [hi1]; exact hhp
  · rw [hi1]; exact hjp

/-- 条件 (VI) 下の `oper` の長さ `Lng (oper M N) = Lng M - 2 + N`。 -/
private theorem oper_len_af (M : PS) (N : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    Lng (oper M N) = Lng M - 2 + N := by
  obtain ⟨hlast, hzero, hi1, hp, hjp⟩ := condVI_tiling_af M hM hcond hj₁
  have h := length_oper_tiling M N hlast hzero hp
  simp only [hjp] at h
  rw [show Lng M - 1 - (Lng M - 2) = 1 by omega] at h
  simpa using h

/-- 条件 (VI) 崩壊（`w = 1`）: `oper M (n+1)` は `oper M n` に 1 列を append したもの。
Isabelle `c6zx_condVI_oper_L` の Lean 版の骨。 -/
private theorem oper_append_block_af (M : PS) (n : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    oper M (n + 1) = oper M n ++
      [(entry M 0 (Lng M - 2) + n * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)),
        entry M 1 (Lng M - 2))] := by
  obtain ⟨hlast, hzero, hi1, hp, hjp⟩ := condVI_tiling_af M hM hcond hj₁
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
  have hp1 : parent M 1 (Lng M - 1) = Lng M - 2 := (condVI_bridge_af M hM hcond hj₁).2
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
private theorem Pred_oper_succ_af (M : PS) (n : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    Pred (oper M (n + 1)) = oper M n := by
  have hc := oper_append_block_af M n hM hcond hj₁
  have hlen : 1 < Lng (oper M (n + 1)) := by
    rw [oper_len_af M (n + 1) hM hcond hj₁]; omega
  have hP : Pred (oper M (n + 1)) = (oper M (n + 1)).dropLast := by
    rw [Pred, if_neg (by omega)]
  rw [hP, hc]
  simp

/-! ## 最終列の行 1 は `u = M_{1,j₀}`、および `monoT (oper M k)` -/

/-- 最終列の行 1 の値はブロック定数 `u = entry M 1 (Lng M - 2)`。 -/
private theorem entry_oper_last_row1_af (M : PS) (k : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hk : 1 ≤ k) :
    entry (oper M k) 1 (Lng (oper M k) - 1) = entry M 1 (Lng M - 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hc := oper_append_block_af M j hM hcond hj₁
  have hlenj : Lng (oper M j) = Lng M - 2 + j := oper_len_af M j hM hcond hj₁
  have hlensj : Lng (oper M (j + 1)) = Lng M - 2 + (j + 1) := oper_len_af M (j + 1) hM hcond hj₁
  have hidx : Lng (oper M (j + 1)) - 1 = Lng (oper M j) := by rw [hlensj, hlenj]; omega
  rw [hidx, hc]
  rw [entry_append_right_mr _ _ 1 (Lng (oper M j)) (le_refl _)]
  simp [entry]

/-- 条件 (VI) 崩壊下、`oper M k` は `monoT`（`leR ... 0 0 last`）。 -/
private theorem le0_oper_full_af (M : PS)
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
        have hlenj : Lng (oper M j) = Lng M - 2 + j := oper_len_af M j hM hcond hj₁
        have hlensj : Lng (oper M (j + 1)) = Lng M - 2 + (j + 1) :=
          oper_len_af M (j + 1) hM hcond hj₁
        have hc := oper_append_block_af M j hM hcond hj₁
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
private theorem monoT_oper_af (M : PS)
    (hM : TPS M) (hmono : monoT M = true) (hcond : transCondVI M = true)
    (hj₁ : 1 < Lng M - 1) (k : ℕ) (hk : 1 ≤ k) :
    monoT (oper M k) = true := by
  have hlen : Lng (oper M k) = Lng M - 2 + k := oper_len_af M k hM hcond hj₁
  have hnz : zeroT (oper M k) = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    left; rw [hlen]; omega
  simp only [monoT, hnz, Bool.not_false, Bool.true_and]
  exact le0_oper_full_af M hM hmono hcond hj₁ k hk

/-! ## `oper M (n+1)` の `transJ0` / `transC1` / `transC2`（塔の 1 段） -/

/-- 行 0 の増分 `d₀ > 0`（Isabelle `s84c1_e0_jm2_lt`）。 -/
private theorem condVI_d0_pos_af (M : PS) (hM : TPS M)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    entry M 0 (Lng M - 2) < entry M 0 (Lng M - 1) := by
  obtain ⟨hhp, hjp⟩ := condVI_bridge_af M hM hcond hj₁
  have hnext1 := hasParent_next_fseq M 1 (Lng M - 1) hhp
  have hleR := (nextR_implies_row0 M 1 (parent M 1 (Lng M - 1)) (Lng M - 1) hnext1).2
  rw [hjp] at hleR
  exact ancestor_basic_1 M (Lng M - 2) (Lng M - 1) (Lng M - 1) hM (by omega) (le_refl _) hleR

/-- 最終列の行 0 の値。 -/
private theorem entry_oper_last_row0_af (M : PS) (k : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hk : 1 ≤ k) :
    entry (oper M k) 0 (Lng (oper M k) - 1)
      = entry M 0 (Lng M - 2)
        + (k - 1) * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hc := oper_append_block_af M j hM hcond hj₁
  have hlenj : Lng (oper M j) = Lng M - 2 + j := oper_len_af M j hM hcond hj₁
  have hlensj : Lng (oper M (j + 1)) = Lng M - 2 + (j + 1) := oper_len_af M (j + 1) hM hcond hj₁
  have hidx : Lng (oper M (j + 1)) - 1 = Lng (oper M j) := by rw [hlensj, hlenj]; omega
  rw [hidx, hc, entry_append_right_mr _ _ 0 (Lng (oper M j)) (le_refl _)]
  simp [entry]

/-- 基点 `ms = Lng (oper M n) - 1` は `oper M (n+1)` で許容的（行 1 が定数 `u` なので
`ms → ms+1` の行 1 辺が立たない）。 -/
private theorem adm_oper_ms_af (M : PS) (n : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hn : 1 ≤ n) :
    adm (oper M (n + 1)) (Lng (oper M n) - 1) = true := by
  have hlenj : Lng (oper M n) = Lng M - 2 + n := oper_len_af M n hM hcond hj₁
  have hlensj : Lng (oper M (n + 1)) = Lng M - 2 + (n + 1) := oper_len_af M (n + 1) hM hcond hj₁
  have hc := oper_append_block_af M n hM hcond hj₁
  set ms := Lng (oper M n) - 1 with hms
  have hms1 : ms + 1 = Lng (oper M (n + 1)) - 1 := by rw [hms, hlensj, hlenj]; omega
  -- 行 1 の値: `ms` と `ms+1` はともに `u`
  have e_ms1 : entry (oper M (n + 1)) 1 (ms + 1) = entry M 1 (Lng M - 2) := by
    rw [hms1]; exact entry_oper_last_row1_af M (n + 1) hM hcond hj₁ (by omega)
  have hmslt : ms < Lng (oper M n) := by rw [hms, hlenj]; omega
  have e_ms : entry (oper M (n + 1)) 1 ms = entry M 1 (Lng M - 2) := by
    rw [hc, entry_append_left_mr (oper M n) _ 1 ms hmslt]
    exact entry_oper_last_row1_af M n hM hcond hj₁ hn
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
private theorem transJ0_oper_succ_af (M : PS) (n : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hn : 1 ≤ n) :
    transJ0 (oper M (n + 1)) = Lng (oper M n) - 1 := by
  have hlenj : Lng (oper M n) = Lng M - 2 + n := oper_len_af M n hM hcond hj₁
  have hlensj : Lng (oper M (n + 1)) = Lng M - 2 + (n + 1) := oper_len_af M (n + 1) hM hcond hj₁
  have hc := oper_append_block_af M n hM hcond hj₁
  have hd0 := condVI_d0_pos_af M hM hcond hj₁
  set ms := Lng (oper M n) - 1 with hms
  have hms1 : ms + 1 = Lng (oper M (n + 1)) - 1 := by rw [hms, hlensj, hlenj]; omega
  have hmslt : ms < Lng (oper M n) := by rw [hms, hlenj]; omega
  -- 行 0 の値
  have e_ms1 : entry (oper M (n + 1)) 0 (ms + 1)
      = entry M 0 (Lng M - 2) + n * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)) := by
    rw [hms1]
    have := entry_oper_last_row0_af M (n + 1) hM hcond hj₁ (by omega)
    simpa using this
  have hmslt2 : ms < Lng (oper M n) := by rw [hms, hlenj]; omega
  have e_ms : entry (oper M (n + 1)) 0 ms
      = entry M 0 (Lng M - 2) + (n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)) := by
    rw [hc, entry_append_left_mr (oper M n) _ 0 ms hmslt2]
    exact entry_oper_last_row0_af M n hM hcond hj₁ hn
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
private theorem transC1_oper_succ_af (M : PS) (n : ℕ)
    (hST : STPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hn : 1 ≤ n) :
    transC1 (oper M (n + 1)) = Dprin (entry M 1 (Lng M - 2) : ℕ∞) BZero := by
  have hM : TPS M := STPS_TPS M hST
  have hRn : RTPS (oper M n) := STPS_RTPS _ (STPS.oper hST n hn)
  have hJ0 : transJ0 (oper M (n + 1)) = Lng (oper M n) - 1 :=
    transJ0_oper_succ_af M n hM hcond hj₁ hn
  have hadm : adm (oper M (n + 1)) (Lng (oper M n) - 1) = true :=
    adm_oper_ms_af M n hM hcond hj₁ hn
  have hJm1 : transJm1 (oper M (n + 1)) = Lng (oper M n) - 1 := by
    rw [transJm1, hJ0, Adm, if_pos hadm]
  have hnz : zeroT (oper M n) = false := by
    have hlen := oper_len_af M n hM hcond hj₁
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    left; rw [hlen]; omega
  rw [transC1, hJm1, Pred_oper_succ_af M n hM hcond hj₁,
    Mark_rightmost1_forward (oper M n) hRn hnz,
    entry_oper_last_row1_af M n hM hcond hj₁ hn]

/-- `transC2 (oper M (n+1)) = D_u(D_u 0)`（`oper M (n+1)` は条件 (I) または (III)）。 -/
private theorem transC2_oper_succ_af (M : PS) (n : ℕ)
    (hST : STPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hn : 1 ≤ n) :
    transC2 (oper M (n + 1))
      = Dprin (entry M 1 (Lng M - 2) : ℕ∞)
          (Dprin (entry M 1 (Lng M - 2) : ℕ∞) BZero) := by
  have hM : TPS M := STPS_TPS M hST
  have hC1 : transC1 (oper M (n + 1)) = Dprin (entry M 1 (Lng M - 2) : ℕ∞) BZero :=
    transC1_oper_succ_af M n hST hcond hj₁ hn
  have hV : transV (oper M (n + 1)) = (entry M 1 (Lng M - 2) : ℕ∞) := by
    rw [transV, hC1]; rfl
  have hT2 : transT2 (oper M (n + 1)) = BZero := by
    rw [transT2, hC1]; rfl
  have hJ0 : transJ0 (oper M (n + 1)) = Lng (oper M n) - 1 :=
    transJ0_oper_succ_af M n hM hcond hj₁ hn
  have hadm : adm (oper M (n + 1)) (Lng (oper M n) - 1) = true :=
    adm_oper_ms_af M n hM hcond hj₁ hn
  have hadmlp : adm (oper M (n + 1)) (lastParent (oper M (n + 1))) = true := by
    rw [show lastParent (oper M (n + 1)) = Lng (oper M n) - 1 from hJ0]; exact hadm
  -- 行 1 の値: 最終列と親（＝ms）はともに `u`
  have hlastu : entry (oper M (n + 1)) 1 (lastIdx (oper M (n + 1)))
      = entry M 1 (Lng M - 2) := entry_oper_last_row1_af M (n + 1) hM hcond hj₁ (by omega)
  have hlpu : entry (oper M (n + 1)) 1 (lastParent (oper M (n + 1)))
      = entry M 1 (Lng M - 2) := by
    have hlenj : Lng (oper M n) = Lng M - 2 + n := oper_len_af M n hM hcond hj₁
    have hc := oper_append_block_af M n hM hcond hj₁
    have hlt : Lng (oper M n) - 1 < Lng (oper M n) := by rw [hlenj]; omega
    rw [show lastParent (oper M (n + 1)) = Lng (oper M n) - 1 from hJ0]
    rw [hc, entry_append_left_mr (oper M n) _ 1 (Lng (oper M n) - 1) hlt]
    exact entry_oper_last_row1_af M n hM hcond hj₁ hn
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
private theorem flat_tower_af (u : ℕ) (m : ℕ) :
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

/-- **削減後の残差 (A′) `CondVIres_adm_Ltower_v6p`（`«8».«8.6-condVI-props»`:399）の証明**。
条件 (VI) 崩壊（`w = 1`）下、`oper M (n+1) = oper M n ++ [colₙ]` に還元し、
`trans_surgery_localized_v6p` を各段の `oper M (n+1)` に適用して塔を 1 段ずつ伸ばす。 -/
theorem CondVIres_adm_Ltower_holds_af : CondVIres_adm_Ltower_v6p := by
  intro M s₁ b₁ hST hmono hcond hj₁ _hadm hbase
  have hM : TPS M := STPS_TPS M hST
  have htj0 : transJ0 M = Lng M - 2 := (condVI_idx_af hcond).1
  set u := entry M 1 (Lng M - 2) with hudef
  -- base scb 分解を `flatBT (D_u 0)` の形に読み替える
  have hbase' : scb_decomp (Trans (oper M 1)) s₁ (flatBT (Dprin (u : ℕ∞) BZero)) b₁ := by
    have h := hbase; rw [htj0] at h; exact h
  have hbrp : ∀ x ∈ b₁, x = Sym.rp := hbase'.2.2
  have hptb : isPTB_str (flatBT (Dprin (u : ℕ∞) BZero)) :=
    ⟨.db (u : ℕ∞) BZero, by simp [dfree_BP, dfree_BT, dfree_BPList, BZero], rfl⟩
  -- 塔の帰納 `Q(k)`: `Trans (oper M (k+1))` は `D_u 0` を core に持つ scb 分解
  have Q : ∀ k, scb_decomp (Trans (oper M (k + 1)))
      (s₁ ++ List.replicate k (Sym.dsym (u : ℕ∞)))
      (flatBT (Dprin (u : ℕ∞) BZero)) b₁ := by
    intro k
    induction k with
    | zero => simpa using hbase'
    | succ k ih =>
        have hRsj : RTPS (oper M (k + 2)) := STPS_RTPS _ (STPS.oper hST (k + 2) (by omega))
        have hmsj : monoT (oper M (k + 2)) = true :=
          monoT_oper_af M hM hmono hcond hj₁ (k + 2) (by omega)
        have hj₁sj : 0 < transJ1 (oper M (k + 2)) := by
          rw [transJ1, lastIdx, oper_len_af M (k + 2) hM hcond hj₁]; omega
        have hpredsj : Pred (oper M (k + 2)) = oper M (k + 1) :=
          Pred_oper_succ_af M (k + 1) hM hcond hj₁
        have ht1sj : transT1 (oper M (k + 2)) ≠ BZero := by
          rw [transT1, hpredsj]
          intro hz
          have hzt : zeroT (oper M (k + 1)) = true :=
            (Trans_preserves_zeroT (oper M (k + 1)) (oper_TPS M (k + 1) hM (by omega))).mpr hz
          have hnz : zeroT (oper M (k + 1)) = false := by
            simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
            left; rw [oper_len_af M (k + 1) hM hcond hj₁]; omega
          rw [hnz] at hzt; exact Bool.noConfusion hzt
        have hC1 : transC1 (oper M (k + 2)) = Dprin (u : ℕ∞) BZero :=
          transC1_oper_succ_af M (k + 1) hST hcond hj₁ (by omega)
        have hC2 : transC2 (oper M (k + 2)) = Dprin (u : ℕ∞) (Dprin (u : ℕ∞) BZero) :=
          transC2_oper_succ_af M (k + 1) hST hcond hj₁ (by omega)
        have hc₂P : ∃ p, transC2 (oper M (k + 2)) = .trm [p] :=
          ⟨.db (u : ℕ∞) (Dprin (u : ℕ∞) BZero), by rw [hC2]; rfl⟩
        obtain ⟨s', b', hd1, hd2⟩ :=
          trans_surgery_localized_v6p (oper M (k + 2)) hRsj hmsj hj₁sj ht1sj hc₂P
        rw [hpredsj, hC1] at hd1
        rw [hC2] at hd2
        obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (oper M (k + 1)))
          s' (s₁ ++ List.replicate k (Sym.dsym (u : ℕ∞))) (flatBT (Dprin (u : ℕ∞) BZero))
          b' b₁ hd1 ih
        rw [hs, hb] at hd2
        refine ⟨?_, fun _ => hptb, hbrp⟩
        rw [hd2.1]
        have hfd : flatBT (Dprin (u : ℕ∞) (Dprin (u : ℕ∞) BZero))
            = Sym.dsym (u : ℕ∞) :: flatBT (Dprin (u : ℕ∞) BZero) := rfl
        rw [hfd, List.replicate_add k 1, List.replicate_one]
        simp [List.append_assoc]
  -- 残差の結論（`n ≥ 2`）
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hqm := Q m
  have hL : (s₁ ++ List.replicate m (Sym.dsym (u : ℕ∞))) ++ flatBT (Dprin (u : ℕ∞) BZero) ++ b₁
      = s₁ ++ (List.replicate (m + 1) (Sym.dsym (u : ℕ∞)) ++ [Sym.zero]) ++ b₁ := by
    have hfz : flatBT (Dprin (u : ℕ∞) BZero) = [Sym.dsym (u : ℕ∞), Sym.zero] := rfl
    rw [hfz, List.replicate_add m 1, List.replicate_one]
    simp [List.append_assoc]
  have hRt : flatBP (BP.db (u : ℕ∞) ((Dprin (u : ℕ∞))^[m] BZero))
      = List.replicate (m + 1) (Sym.dsym (u : ℕ∞)) ++ [Sym.zero] := by
    have hfb : flatBP (BP.db (u : ℕ∞) ((Dprin (u : ℕ∞))^[m] BZero))
        = Sym.dsym (u : ℕ∞) :: flatBT ((Dprin (u : ℕ∞))^[m] BZero) := rfl
    rw [hfb, flat_tower_af, ← List.cons_append, ← List.replicate_succ]
  simp only [Nat.add_sub_cancel]
  rw [htj0, ← hudef, hqm.1, hL, hRt]

/-- **`CondVI_scbdec_adm_forms_v6`（`«8».«8.6-condVI-close»`:244）の討伐**（house pattern）。
`condVI_scbdec_adm_forms_holds_v6p`（`«8».«8.6-condVI-props»`）へ、無条件に証明した
残差 (A′) を渡す。 -/
theorem CondVI_scbdec_adm_forms_v6_holds : CondVI_scbdec_adm_forms_v6 :=
  condVI_scbdec_adm_forms_holds_v6p CondVIres_adm_Ltower_holds_af

#print axioms oper_len_af
#print axioms oper_append_block_af
#print axioms Pred_oper_succ_af
#print axioms entry_oper_last_row1_af
#print axioms monoT_oper_af
#print axioms transJ0_oper_succ_af
#print axioms transC1_oper_succ_af
#print axioms transC2_oper_succ_af
#print axioms CondVIres_adm_Ltower_holds_af
#print axioms CondVI_scbdec_adm_forms_v6_holds

end PSS
